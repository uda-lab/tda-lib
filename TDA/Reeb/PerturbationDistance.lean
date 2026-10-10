import TDA.Reeb.InterleavingDistance
import TDA.Reeb.Perturbation

/-!
# Uniform perturbation bounds the interleaving distance

For continuous `f g : C(X, ℝ)` with `∀ x, |f x - g x| ≤ ε`, the interval restrictions of the
component functors are at interleaving distance at most `ε`
(`interleavingDistance_intervalComponents_le`; de Silva–Munch–Patel, Theorem 4.6(i), in
pointwise form). The witness is the explicit `perturbationInterleaving`. Since smoothing is
nonexpansive, the same bound holds after smoothing both sides by any `δ`
(`interleavingDistance_smoothing_intervalComponents_le`).
See `docs/math/reeb-interleaving-distance.md`.
-/

open Set CategoryTheory
open scoped NNReal ENNReal

universe u

namespace TDA.Reeb

section PerturbationCorollary

variable {X : Type u} [TopologicalSpace X]

/-- DMP Theorem 4.6(i), pointwise form: `d(C_f, C_g) ≤ ε` when `|f x - g x| ≤ ε` for all `x`. -/
theorem interleavingDistance_intervalComponents_le {f g : C(X, ℝ)} {ε : ℝ≥0}
    (hfg : ∀ x, |f x - g x| ≤ ε) :
    interleavingDistance (intervalComponents f) (intervalComponents g) ≤ ε :=
  (perturbationInterleaving hfg).interleavingDistance_le

/-- The same bound after smoothing both sides, by nonexpansiveness. -/
theorem interleavingDistance_smoothing_intervalComponents_le {f g : C(X, ℝ)} {ε : ℝ≥0}
    (hfg : ∀ x, |f x - g x| ≤ ε) (δ : ℝ≥0) :
    interleavingDistance ((smoothing δ).obj (intervalComponents f))
      ((smoothing δ).obj (intervalComponents g)) ≤ ε :=
  (interleavingDistance_smoothing_le δ _ _).trans (interleavingDistance_intervalComponents_le hfg)

end PerturbationCorollary

end TDA.Reeb
