#!/usr/bin/env bash
# Live trust-footprint audit: run `#print axioms` for every declaration listed in
# scripts/print_axioms/*.lean and fail unless each axiom set is a subset of the
# allowlist (the Lean/mathlib kernel trio). Catches `sorryAx`, project axioms and
# other trust escapes (e.g. `Lean.ofReduceBool` from `native_decide`) — including
# transitive ones that the textual guards cannot see.
#
# Requires a completed `lake build` (scripts/check.sh orders this correctly).
# Changing ALLOW is a `needs-decision` change.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
export PATH="$HOME/.elan/bin:$PATH"

ALLOW="propext Classical.choice Quot.sound"
# Library (namespace) name, read from lakefile.toml so scripts/rename-project.sh has one
# less site to patch.
NS="$(sed -n 's/^name = "\(.*\)"$/\1/p' lakefile.toml | head -1)"
PIN_DIR="scripts/print_axioms"

if ! command -v lake >/dev/null 2>&1; then
  echo "ERROR: 'lake' not found (install elan; see scripts/bootstrap.sh)." >&2
  exit 1
fi

# Declarations the audit must cover, taken from every area file.
if [ ! -d "$PIN_DIR" ]; then
  echo "ERROR: missing axiom pin directory $PIN_DIR." >&2
  exit 1
fi
mapfile -d '' SCRIPTS < <(find "$PIN_DIR" -maxdepth 1 -type f -name '*.lean' -print0 | sort -z)
if [ "${#SCRIPTS[@]}" -eq 0 ]; then
  echo "ERROR: $PIN_DIR has no Lean audit files." >&2
  exit 1
fi
expected="$(awk '/^#print axioms /{print $3}' "${SCRIPTS[@]}")"
if [ -z "$expected" ]; then
  echo "ERROR: $PIN_DIR lists no '#print axioms' declarations; the audit must never pass vacuously." >&2
  exit 1
fi

# Capture with errexit disabled so a failing lean run is diagnosed loudly instead of
# aborting before its output is shown.
OUTPUT=""
for SCRIPT in "${SCRIPTS[@]}"; do
  echo "==> lake env lean $SCRIPT"
  set +e
  result="$("$ROOT/scripts/lean.sh" lake env lean "$SCRIPT" 2>&1)"
  STATUS=$?
  set -e
  printf '%s\n' "$result"
  if [ "$STATUS" -ne 0 ]; then
    echo "ERROR: 'lake env lean $SCRIPT' failed with exit $STATUS." >&2
    echo "  Run 'lake build' first; a pinned declaration that no longer exists also fails here." >&2
    exit 1
  fi
  OUTPUT+="$result"$'\n'
done

# `#print axioms` output is one record per declaration, possibly wrapped over
# several lines:  'X' depends on axioms: [a, b, c]   or   'X' does not depend on any axioms
# Join each record into a single line.
records="$(printf '%s\n' "$OUTPUT" | awk '
  /^'"'"'/ { if (rec != "") print rec; rec = $0; next }
  { if (rec != "") rec = rec " " $0 }
  END { if (rec != "") print rec }
')"

FAIL=0
n=0
for decl in $expected; do
  n=$((n + 1))
  # Select the records whose leading token is exactly '<decl>' followed by a space. The
  # comparison is a literal prefix test (no regex), so the pin X never selects X', X'', ...
  prefix="'$decl' "
  rec="$(printf '%s\n' "$records" | PREFIX="$prefix" awk 'index($0, ENVIRON["PREFIX"]) == 1')"
  count=0
  [ -z "$rec" ] || count="$(printf '%s\n' "$rec" | wc -l | tr -d ' ')"
  if [ "$count" -eq 0 ]; then
    echo "ERROR: no '#print axioms' output for $decl (declaration missing or renamed?)." >&2
    FAIL=1
    continue
  fi
  if [ "$count" -ne 1 ]; then
    pins="$(printf '%s\n' "$expected" | grep -cxF -- "$decl" || true)"
    if [ "$pins" -gt 1 ]; then
      echo "ERROR: $decl is pinned $pins times in $PIN_DIR; pin it once." >&2
    else
      echo "ERROR: $count '#print axioms' records for $decl; expected exactly one." >&2
    fi
    FAIL=1
    continue
  fi
  # Parse only the sole record: exactly the no-axioms body, or one non-empty bracketed list of
  # comma-separated names (a wrapped list arrives joined with spaces). Anything else is malformed.
  body="$(printf '%s\n' "${rec#"$prefix"}" | sed 's/[[:space:]]*$//')"
  axioms=""
  case "$body" in
    "does not depend on any axioms")
      echo "OK: $decl — no axioms."
      continue
      ;;
    "depends on axioms: ["*"]")
      list="${body#"depends on axioms: ["}"; list="${list%"]"}"
      list="$(printf '%s\n' "$list" | sed 's/[[:space:]]*$//')"
      case "$list" in
        *,) ;;  # a trailing empty entry, which the command substitution below would drop
        *) axioms="$(printf '%s\n' "$list" | tr ',' '\n' | sed 's/^[[:space:]]*//; s/[[:space:]]*$//')" ;;
      esac
      ;;
  esac
  if [ -z "$axioms" ] || grep -q -e '^$' -e '[][[:space:]]' <<<"$axioms"; then
    echo "ERROR: malformed '#print axioms' record for $decl: $rec" >&2
    FAIL=1
    continue
  fi
  bad=0
  for ax in $axioms; do
    case " $ALLOW " in
      *" $ax "*) ;;
      *)
        if [ "$ax" = "sorryAx" ]; then
          echo "ERROR: $decl is incomplete (depends on sorryAx)." >&2
        elif [ "${ax#"$NS".}" != "$ax" ]; then
          echo "ERROR: $decl depends on project axiom $ax." >&2
        else
          echo "ERROR: $decl depends on unexpected trust $ax." >&2
        fi
        bad=1
        ;;
    esac
  done
  if [ "$bad" -ne 0 ]; then
    FAIL=1
  else
    echo "OK: $decl — axioms ⊆ {$ALLOW}: [$(printf '%s' "$axioms" | tr '\n' ' ' | sed 's/ $//')]"
  fi
done

if [ "$FAIL" -ne 0 ]; then
  echo "AXIOM AUDIT FAILED" >&2
  exit 1
fi
echo "AXIOM AUDIT OK — $n declaration(s) within the allowlist {$ALLOW}."
