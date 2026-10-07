import Mathlib.Data.Real.Basic

/-!
# TDA.Basic

Scaffold module. `placeholder_add_zero` exists only so that the live axiom audit
(`scripts/print_axioms.lean` → `scripts/check-axioms.sh`) and the coverage guard
(`scripts/check_axiom_coverage.lean`) are exercised end to end from the first commit.
It stays permanently as the audit's smoke test; its line in `scripts/print_axioms.lean`
is not removed. Real development goes into sibling modules imported from the root
aggregator `TDA.lean`.
-/

namespace TDA

/-- Placeholder pinned in `scripts/print_axioms.lean`. Stating it over `ℝ` makes its
axiom closure the kernel trio (`propext`, `Classical.choice`, `Quot.sound`), so the
audit's allowlist path is tested rather than only the "no axioms" path. -/
theorem placeholder_add_zero (x : ℝ) : x + 0 = x := add_zero x

end TDA
