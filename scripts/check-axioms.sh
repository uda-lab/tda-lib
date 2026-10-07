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
OUTPUT="$(lake env lean "$SCRIPT" 2>&1)"
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
  rec="$(printf '%s\n' "$records" | grep -F "'$decl'" || true)"
  if [ -z "$rec" ]; then
    echo "ERROR: no '#print axioms' output for $decl (declaration missing or renamed?)." >&2
    FAIL=1
    continue
  fi
  if printf '%s\n' "$rec" | grep -q "does not depend on any axioms"; then
    echo "OK: $decl — no axioms."
    continue
  fi
  axioms="$(printf '%s\n' "$rec" | sed -n 's/.*\[\(.*\)\].*/\1/p' | tr ',' '\n' | tr -d ' ' | sed '/^$/d')"
  if [ -z "$axioms" ]; then
    echo "ERROR: could not parse axiom list for $decl: $rec" >&2
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
