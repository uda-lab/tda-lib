#!/usr/bin/env bash
# Live trust-footprint audit: run `#print axioms` for every declaration listed in
# scripts/print_axioms.lean and fail unless each axiom set is a subset of the
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
SCRIPT="scripts/print_axioms.lean"

if ! command -v lake >/dev/null 2>&1; then
  echo "ERROR: 'lake' not found (install elan; see scripts/bootstrap.sh)." >&2
  exit 1
fi

# Declarations the audit must cover, taken from the script itself.
expected="$(awk '/^#print axioms /{print $3}' "$SCRIPT")"
if [ -z "$expected" ]; then
  echo "ERROR: $SCRIPT lists no '#print axioms' declarations; the audit must never pass vacuously." >&2
  exit 1
fi

echo "==> lake env lean $SCRIPT"
# Capture with errexit disabled so a failing lean run is diagnosed loudly instead of
# aborting before its output is shown.
set +e
OUTPUT="$("$ROOT/scripts/lean.sh" lake env lean "$SCRIPT" 2>&1)"
STATUS=$?
set -e
printf '%s\n' "$OUTPUT"
if [ "$STATUS" -ne 0 ]; then
  echo "ERROR: 'lake env lean $SCRIPT' failed with exit $STATUS." >&2
  echo "  Run 'lake build' first; a pinned declaration that no longer exists also fails here." >&2
  exit 1
fi

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
  # The quoted declaration name is followed by a space in each Lean record.
  # Match that complete literal prefix so X cannot select X', and count before
  # parsing so missing or duplicate records fail closed.
  prefix="'$decl' "
  rec=""
  matches=0
  while IFS= read -r candidate; do
    if [[ "$candidate" == "$prefix"* ]]; then
      rec="$candidate"
      matches=$((matches + 1))
    fi
  done <<< "$records"

  if [ "$matches" -eq 0 ]; then
    echo "ERROR: no '#print axioms' output for $decl (declaration missing or renamed?)." >&2
    FAIL=1
    continue
  fi
  if [ "$matches" -ne 1 ]; then
    echo "ERROR: expected exactly one '#print axioms' output for $decl; found $matches records." >&2
    FAIL=1
    continue
  fi

  body="${rec#"$prefix"}"
  if [ "$body" = "does not depend on any axioms" ]; then
    echo "OK: $decl — no axioms."
    continue
  fi
  if [[ "$body" != "depends on axioms: ["*"]" ]]; then
    echo "ERROR: unrecognized '#print axioms' record for $decl: $rec" >&2
    FAIL=1
    continue
  fi
  axiom_list="$(printf '%s\n' "$body" | sed -n 's/^depends on axioms: \[\(.*\)\]$/\1/p')"
  if [ -z "$axiom_list" ] || [[ "$axiom_list" == ,* || "$axiom_list" == *, || "$axiom_list" == *,,* ]]; then
    echo "ERROR: could not parse axiom list for $decl: $rec" >&2
    FAIL=1
    continue
  fi
  IFS=',' read -r -a axiom_names <<< "$axiom_list"
  parse_bad=0
  for i in "${!axiom_names[@]}"; do
    ax="${axiom_names[$i]}"
    ax="${ax#"${ax%%[![:blank:]]*}"}"
    ax="${ax%"${ax##*[![:blank:]]}"}"
    if [ -z "$ax" ] || [[ "$ax" == *[[:blank:]]* ]]; then
      parse_bad=1
      break
    fi
    axiom_names[$i]="$ax"
  done
  if [ "$parse_bad" -ne 0 ]; then
    echo "ERROR: could not parse axiom list for $decl: $rec" >&2
    FAIL=1
    continue
  fi
  bad=0
  for ax in "${axiom_names[@]}"; do
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
    axiom_summary="${axiom_names[*]}"
    echo "OK: $decl — axioms ⊆ {$ALLOW}: [$axiom_summary]"
  fi
done

if [ "$FAIL" -ne 0 ]; then
  echo "AXIOM AUDIT FAILED" >&2
  exit 1
fi
echo "AXIOM AUDIT OK — $n declaration(s) within the allowlist {$ALLOW}."
