#!/usr/bin/env bash
# Real Lean regressions for #38 using an isolated TDA root and the unchanged checker.
# Unsafe fixture proofs exist only in a cleaned temporary directory, never in TDA/.
# This tests the existing coverage gate; it adds no gate to check.sh and no mathlib build.
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
if [ "$#" -ne 0 ]; then
  echo 'usage: scripts/test-private-axioms.sh' >&2
  exit 64
fi
tmp="$(mktemp -d)"
trap 'rm -rf -- "$tmp"' EXIT
mkdir -p "$tmp/TDA" "$tmp/scripts/print_axioms"
cp scripts/check_axiom_coverage.lean "$tmp/scripts/"
printf '%s\n' 'import TDA.AxiomAuditFixture' > "$tmp/TDA.lean"

# lake env supplies the pinned toolchain paths. Only these child Lean processes see
# the temporary TDA overlay; the real library and its build cache are never overwritten.
fixture_lean() {
  "$ROOT/scripts/lean.sh" lake env bash -c '
    fixture_root=$1; project_root=$2; shift 2
    export LEAN_PATH="$fixture_root${LEAN_PATH:+:$LEAN_PATH}"
    cd "$fixture_root" || exit 1
    exec "$project_root/scripts/lean.sh" lean "$@"
  ' fixture "$tmp" "$ROOT" "$@"
}

run_case() {
  local name="$1" expected="$2" pattern="$3" status=0
  { printf '%s\n' 'import Lean' 'namespace AxiomAuditFixture'; cat; printf '%s\n' 'end AxiomAuditFixture'; } > "$tmp/TDA/AxiomAuditFixture.lean"
  if ! fixture_lean -o TDA/AxiomAuditFixture.olean TDA/AxiomAuditFixture.lean > "$tmp/compile.log" 2>&1 || \
     ! fixture_lean -o TDA.olean TDA.lean >> "$tmp/compile.log" 2>&1; then
    cat "$tmp/compile.log" >&2
    echo "FAIL [$name]: fixture did not compile" >&2
    exit 1
  fi
  # The production checker runs unchanged, including disk/import reachability and pin
  # discovery, against genuine imported module metadata and kernel declarations.
  fixture_lean scripts/check_axiom_coverage.lean > "$tmp/check.log" 2>&1 || status=$?
  if { [ "$expected" = pass ] && [ "$status" -ne 0 ]; } || \
     { [ "$expected" = fail ] && [ "$status" -eq 0 ]; } || \
     ! rg -F -- "$pattern" "$tmp/check.log" >/dev/null; then
    cat "$tmp/check.log" >&2
    echo "FAIL [$name]: expected $expected with diagnostic '$pattern', got exit $status" >&2
    exit 1
  fi
  echo "PASS [$name]"
  rg '^PINNED CLOSURE|^PRIVATE AUDIT|^COVERAGE OK|^PRIVATE AXIOM FAILURE:' "$tmp/check.log"
}

# The public root reaches one private proof. The others must be independently audited;
# computation, including native execution, is not itself a theorem trust claim.
printf '%s\n' 'import TDA' '#print axioms AxiomAuditFixture.publicRoot' > "$tmp/scripts/print_axioms/Fixture.lean"
run_case allowed pass 'COVERAGE OK — 1 public theorems, all pinned' <<'LEAN'
private theorem reached : True := by trivial
theorem publicRoot : True := reached
private theorem kernelDecide : (2 : Nat) + 2 = 4 := by decide
private theorem ext : True := by trivial
private theorem proof_explicit : True := by trivial
private theorem classicalAllowed (p : Prop) : p ∨ ¬p := Classical.em p
private instance privatePropInstance : Nonempty Unit := ⟨()⟩
#eval (2 : Nat) + 2
LEAN
if ! rg -F '6 roots, 1 already in pinned closures, 5 additionally checked' "$tmp/check.log" >/dev/null; then
  cat "$tmp/check.log" >&2
  echo 'FAIL [allowed]: private classification or pinned dependency closure changed' >&2
  exit 1
fi
printf '%s\n' 'import TDA' > "$tmp/scripts/print_axioms/Fixture.lean"

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
