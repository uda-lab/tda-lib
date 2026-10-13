#!/usr/bin/env bash
# Real Lean regressions for #38. Requires the existing built TDA library/cache.
# Unsafe fixture proofs exist only in a cleaned temporary directory, never in TDA/.
# This tests the existing coverage gate; it does not add a separate gate to check.sh.
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
if [ "$#" -ne 0 ]; then
  echo 'usage: scripts/test-private-axioms.sh' >&2
  exit 64
fi
tmp="$(mktemp -d)"
trap 'rm -rf -- "$tmp"' EXIT
mkdir -p "$tmp/TDA" "$tmp/pins"
cp scripts/print_axioms/*.lean "$tmp/pins/"
# Use the production checker unchanged except for an extra imported test module and
# isolated pins. Actual module metadata, theorem kinds, dependency traversal and Lean's
# axiom collector are exercised; neither Lean output nor its exit status is mocked.
python3 - "$tmp" <<'PY'
import json
import pathlib
import sys
root = pathlib.Path(sys.argv[1])
source = pathlib.Path('scripts/check_axiom_coverage.lean').read_text()
source = source.replace('import TDA\n', 'import TDA\nimport TDA.AxiomAuditFixture\n', 1)
source = source.replace('readAllPinnedNames "scripts/print_axioms"',
                        'readAllPinnedNames ' + json.dumps(str(root / 'pins')))
(root / 'coverage.lean').write_text(source)
PY

run_case() {
  local name="$1" expected="$2" pattern="$3" status=0
  { printf '%s\n' 'import TDA' 'namespace AxiomAuditFixture'; cat; printf '%s\n' 'end AxiomAuditFixture'; } > "$tmp/TDA/AxiomAuditFixture.lean"
  "$ROOT/scripts/lean.sh" lake env lean --root="$tmp" \
    -o "$tmp/TDA/AxiomAuditFixture.olean" "$tmp/TDA/AxiomAuditFixture.lean" > "$tmp/compile.log" 2>&1 || {
    cat "$tmp/compile.log" >&2
    echo "FAIL [$name]: fixture did not compile" >&2
    exit 1
  }
  # lake env establishes the pinned package paths; prepend the isolated fixture path
  # inside that environment so the import resolves the freshly compiled module.
  "$ROOT/scripts/lean.sh" lake env bash -c \
    'export LEAN_PATH="$1${LEAN_PATH:+:$LEAN_PATH}"; exec "$2/scripts/lean.sh" lean "$1/coverage.lean"' \
    fixture "$tmp" "$ROOT" > "$tmp/check.log" 2>&1 || status=$?
  if { [ "$expected" = pass ] && [ "$status" -ne 0 ]; } || \
     { [ "$expected" = fail ] && [ "$status" -eq 0 ]; } || \
     ! rg -F -- "$pattern" "$tmp/check.log" >/dev/null; then
    cat "$tmp/check.log" >&2
    echo "FAIL [$name]: expected $expected with diagnostic '$pattern', got exit $status" >&2
    exit 1
  fi
  echo "PASS [$name]"
  if [ "$expected" = fail ]; then
    rg '^PRIVATE AXIOM FAILURE:' "$tmp/check.log"
  fi
}

# Measure current library roots so fixture expectations remain valid as the library grows.
"$ROOT/scripts/lean.sh" lake env lean scripts/check_axiom_coverage.lean > "$tmp/baseline.log" 2>&1 || {
  cat "$tmp/baseline.log" >&2
  echo 'FAIL [baseline]: current library coverage/audit failed' >&2
  exit 1
}
rg '^PRIVATE AUDIT|^COVERAGE OK' "$tmp/baseline.log"
read -r baseline_roots baseline_covered baseline_added < <(
  awk '/^PRIVATE AUDIT / { print $4, $6, $11 }' "$tmp/baseline.log"
)
for count in "$baseline_roots" "$baseline_covered" "$baseline_added"; do
  if [[ ! "$count" =~ ^[0-9]+$ ]]; then
    echo 'FAIL [baseline]: missing numeric private-audit summary' >&2
    exit 1
  fi
done

# The public root reaches one private proof. The others must be independently audited;
# computation, including native execution, is not itself a theorem trust claim.
printf '%s\n' '#print axioms AxiomAuditFixture.publicRoot' > "$tmp/pins/Fixture.lean"
run_case allowed pass 'COVERAGE OK' <<'LEAN'
private theorem reached : True := by trivial
theorem publicRoot : True := reached
private theorem kernelDecide : (2 : Nat) + 2 = 4 := by decide
private theorem ext : True := by trivial
private theorem proof_explicit : True := by trivial
private theorem classicalAllowed (p : Prop) : p ∨ ¬p := Classical.em p
private instance privatePropInstance : Nonempty Unit := ⟨()⟩
#eval (2 : Nat) + 2
LEAN
# Verify the closure split as well as success: six private roots, only reached covered.
expected_split="$((baseline_roots + 6)) roots, $((baseline_covered + 1)) already in pinned closures, $((baseline_added + 5)) additionally checked"
if ! rg -F -- "$expected_split" "$tmp/check.log" >/dev/null; then
  cat "$tmp/check.log" >&2
  echo 'FAIL [allowed]: private classification or pinned dependency closure changed' >&2
  exit 1
fi
rm -- "$tmp/pins/Fixture.lean"

# One failing module contains independent native, generated-looking-name and transitive
# private claims. Require each diagnostic, so one detected failure cannot hide a missed root.
run_case forbidden_private fail 'PRIVATE AXIOM FAILURE: AxiomAuditFixture.nativeClaim' <<'LEAN'
private theorem nativeClaim : (2 : Nat) + 2 = 4 := by native_decide
private theorem proof_bad : (2 : Nat) + 2 = 4 := by native_decide
private axiom forbidden : True
private theorem helper : True := forbidden
private theorem standalone : True := helper
LEAN
for pattern in \
  'PRIVATE AXIOM FAILURE: AxiomAuditFixture.proof_bad' \
  'PRIVATE AXIOM FAILURE: AxiomAuditFixture.helper' \
  'PRIVATE AXIOM FAILURE: AxiomAuditFixture.standalone' \
  'native_decide.ax' \
  'AxiomAuditFixture.forbidden'; do
  if ! rg -F -- "$pattern" "$tmp/check.log" >/dev/null; then
    cat "$tmp/check.log" >&2
    echo "FAIL [forbidden_private]: missing diagnostic '$pattern'" >&2
    exit 1
  fi
done

echo 'PRIVATE AXIOM REGRESSIONS OK — kernel proofs accepted; forbidden private proofs rejected'
