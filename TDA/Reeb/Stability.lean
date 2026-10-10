import TDA.Reeb.PerturbationDistance
import Mathlib.Topology.MetricSpace.UniformConvergence

/-!
# Stability of the component precosheaves in the supremum distance

The supremum distance `‖f − g‖∞ ∈ [0, ∞]` of arbitrary functions `f g : X → ℝ` is mathlib's
extended distance on uniformly converging functions, used literally as
`edist (UniformFun.ofFun f) (UniformFun.ofFun g)`. No new distance, structure, wrapper or
instance is introduced. Its real-valued presentation is `⨆ x, ENNReal.ofReal |f x - g x|`
(`edist_uniformFun_ofFun_eq_iSup`), and it is at most `ε : ℝ≥0` exactly when the pointwise
bound `|f x - g x| ≤ ε` holds everywhere (`edist_uniformFun_ofFun_le_coe_iff`).

For continuous `f g : C(X, ℝ)` on any topological space, the interleaving distance of the
interval restrictions of the component functors is at most this distance
(`interleavingDistance_intervalComponents_le_edist`; de Silva–Munch–Patel, Theorem 4.6(i)).
An infinite distance gives the trivial bound; a finite one reduces to the pointwise theorem
`interleavingDistance_intervalComponents_le`. The same bound holds after smoothing both sides
(`interleavingDistance_smoothing_intervalComponents_le_edist`).
See `docs/math/reeb-interleaving-distance.md`.
-/

open Set CategoryTheory
open scoped NNReal ENNReal UniformConvergence

universe u

namespace TDA.Reeb

section SupDistance

variable {X : Type u}

/-- Real-valued presentation of mathlib's uniform extended distance:
`edist f g = ⨆ x, ENNReal.ofReal |f x - g x|`, possibly `⊤`. -/
theorem edist_uniformFun_ofFun_eq_iSup (f g : X → ℝ) :
    edist (UniformFun.ofFun f) (UniformFun.ofFun g) = ⨆ x, ENNReal.ofReal |f x - g x| := by
  simp only [UniformFun.edist_def, UniformFun.toFun_ofFun, edist_dist, Real.dist_eq]

/-- Finite-bound interface: the uniform extended distance is at most `ε : ℝ≥0` iff the
pointwise bound `|f x - g x| ≤ ε` holds everywhere. -/
theorem edist_uniformFun_ofFun_le_coe_iff {f g : X → ℝ} {ε : ℝ≥0} :
    edist (UniformFun.ofFun f) (UniformFun.ofFun g) ≤ ε ↔ ∀ x, |f x - g x| ≤ ε := by
  simp only [UniformFun.edist_le, UniformFun.toFun_ofFun, edist_le_coe, Real.nndist_eq,
    ← NNReal.coe_le_coe, Real.coe_nnabs]

end SupDistance

section Stability

variable {X : Type u} [TopologicalSpace X]

/-- de Silva–Munch–Patel, Theorem 4.6(i), literal form:
`d(C_f|Int, C_g|Int) ≤ ‖f − g‖∞` with `‖f − g‖∞ ∈ [0, ∞]` mathlib's uniform extended distance.
No compactness, boundedness, finiteness or nonemptiness of `X` is assumed. -/
theorem interleavingDistance_intervalComponents_le_edist (f g : C(X, ℝ)) :
    interleavingDistance (intervalComponents f) (intervalComponents g) ≤
      edist (UniformFun.ofFun ⇑f) (UniformFun.ofFun ⇑g) := by
  by_cases htop : edist (UniformFun.ofFun ⇑f) (UniformFun.ofFun ⇑g) = ⊤
  · rw [htop]
    exact le_top
  · rw [← ENNReal.coe_toNNReal htop]
    exact interleavingDistance_intervalComponents_le
      (edist_uniformFun_ofFun_le_coe_iff.1 (ENNReal.coe_toNNReal htop).ge)

/-- The same literal bound after smoothing both sides by any `δ`. -/
theorem interleavingDistance_smoothing_intervalComponents_le_edist (f g : C(X, ℝ)) (δ : ℝ≥0) :
    interleavingDistance ((smoothing δ).obj (intervalComponents f))
      ((smoothing δ).obj (intervalComponents g)) ≤
      edist (UniformFun.ofFun ⇑f) (UniformFun.ofFun ⇑g) :=
  (interleavingDistance_smoothing_le δ _ _).trans
    (interleavingDistance_intervalComponents_le_edist f g)

end Stability

end TDA.Reeb
