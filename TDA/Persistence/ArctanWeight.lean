import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import TDA.Persistence.WeightedKernelStability

/-!
# The arctan weight and its kernel-stability constant

`arctan` is `1`-Lipschitz by the mean value theorem, since its derivative `1 / (1 + x²)`
lies in `[0, 1]`. For `0 ≤ C` the function `u ↦ arctan (C · max u.2 0)` on
birth–persistence coordinates is a `Weight C (π / 2)`: it is nonnegative, bounded by `π / 2`,
`C`-Lipschitz for the maximum norm, and zero on zero persistence. On every point with
`birth ≤ death` it is the persistence-weighted Gaussian kernel weight
`w_arc = arctan (C · pers)` of Kusano–Fukumizu–Hiraoka, JMLR 18(189), 2018, §3.2, with
`p = 1`. The truncation at `0` is needed only below the diagonal, where the untruncated
formula is negative and is excluded by the nonnegative weight interface.

With `A = C` and `B = π / 2` the weighted-kernel constant `2A + √2·B/|σ|` reads
`2C + √2·π/(2|σ|)`, the KFH18 Corollary 11 `w_arc` constant `π L_k / 2 + 2 B_k C` at
`B_k = 1`, `L_k = √2/|σ|`. The corollaries below are instances of the merged weighted-kernel
stability theorems.
-/

namespace TDA.Persistence.PersistenceImage

open Real

/-- `arctan` is `1`-Lipschitz. -/
theorem lipschitzWith_arctan : LipschitzWith 1 Real.arctan := by
  refine lipschitzWith_of_nnnorm_deriv_le Real.differentiable_arctan fun x => ?_
  rw [Real.deriv_arctan, ← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_one, Real.norm_eq_abs]
  have hpos : (0 : ℝ) < 1 + x ^ 2 := by positivity
  rw [abs_of_nonneg (by positivity), div_le_one₀ hpos]
  nlinarith [sq_nonneg x]

theorem abs_arctan_sub_arctan_le (x y : ℝ) :
    |Real.arctan x - Real.arctan y| ≤ |x - y| := by
  simpa only [NNReal.coe_one, one_mul, Real.dist_eq] using lipschitzWith_arctan.dist_le_mul x y

/-- The persistence-weighted Gaussian kernel weight `arctan (C · pers)`, with persistence
truncated at `0`. -/
noncomputable def arctanWeight (C : ℝ) (hC : 0 ≤ C) : Weight C (π / 2) where
  toFun u := Real.arctan (C * max u.2 0)
  nonneg u := Real.arctan_nonneg.mpr (mul_nonneg hC (le_max_right _ _))
  bounded u := (Real.arctan_lt_pi_div_two _).le
  lipschitz u v := by
    calc
      _ ≤ |C * max u.2 0 - C * max v.2 0| := abs_arctan_sub_arctan_le _ _
      _ = C * |max u.2 0 - max v.2 0| := by rw [← mul_sub, abs_mul, abs_of_nonneg hC]
      _ ≤ C * |u.2 - v.2| := mul_le_mul_of_nonneg_left (abs_max_sub_max_le_abs _ _ _) hC
      _ ≤ C * ‖u - v‖ := by
        refine mul_le_mul_of_nonneg_left ?_ hC
        simpa only [Prod.norm_def, Prod.fst_sub, Prod.snd_sub, Real.norm_eq_abs]
          using le_max_right |u.1 - v.1| |u.2 - v.2|
  zero_persistence b := by simp

@[simp] theorem arctanWeight_apply (C : ℝ) (hC : 0 ≤ C) (u : ℝ × ℝ) :
    arctanWeight C hC u = Real.arctan (C * max u.2 0) := rfl

/-- On the closed upper half-plane the weight is KFH18's `w_arc = arctan (C · pers)`. -/
theorem arctanWeight_birthPersistence (C : ℝ) (hC : 0 ≤ C) {p : ℝ × ℝ} (hp : p.1 ≤ p.2) :
    arctanWeight C hC (birthPersistence p) = Real.arctan (C * (p.2 - p.1)) := by
  rw [arctanWeight_apply, birthPersistence, max_eq_left (sub_nonneg.mpr hp)]

end TDA.Persistence.PersistenceImage

namespace TDA.Persistence.WeightedKernel

open Real
open PersistenceImage (arctanWeight)

variable {C : ℝ}

/-- The weighted-kernel constant of the arctan weight, KFH18 Corollary 11 (`w_arc`, `p = 1`). -/
theorem stabilityConstant_arctan (σ C : ℝ) :
    stabilityConstant σ C (π / 2) = 2 * C + √2 * π / (2 * |σ|) := by
  unfold stabilityConstant
  rw [mul_div_assoc', div_div]

/-- Occurrence-level embedding stability of the arctan weight, the library form of the
KFH18 Corollary 11 `w_arc` line. -/
theorem norm_embedding_sub_le_arctan {I J : Type*} [Fintype I] [Fintype J] (σ : ℝ)
    (hC : 0 ≤ C) (x : I → ℝ × ℝ) (y : J → ℝ × ℝ)
    (hx : ∀ i, (x i).1 < (x i).2) (hy : ∀ j, (y j).1 < (y j).2) :
    ‖embedding σ (arctanWeight C hC) x - embedding σ (arctanWeight C hC) y‖ ≤
      (2 * C + √2 * π / (2 * |σ|)) * finiteFirstOrderMatchingCost x y := by
  simpa only [stabilityConstant_arctan] using
    norm_embedding_sub_le_finiteFirstOrderMatchingCost σ hC Real.pi_div_two_pos.le
      (arctanWeight C hC) x y hx hy

/-- Count-times-bottleneck stability of arctan diagram embeddings. -/
theorem norm_diagramEmbedding_sub_le_arctan (σ : ℝ) (hC : 0 ≤ C) (D E : Diagram ℝ)
    (hD : D.IsPositive) (hE : E.IsPositive) (hfinite : bottleneck D E < ⊤) :
    ‖diagramEmbedding σ (arctanWeight C hC) D - diagramEmbedding σ (arctanWeight C hC) E‖ ≤
      (2 * C + √2 * π / (2 * |σ|)) *
        ((Fintype.card D.finiteOccurrences + Fintype.card E.finiteOccurrences : ℕ) : ℝ) *
          (bottleneck D E).toReal := by
  simpa only [stabilityConstant_arctan] using
    norm_diagramEmbedding_sub_le_card_mul_bottleneck σ hC Real.pi_div_two_pos.le
      (arctanWeight C hC) D E hD hE hfinite

/-- Matching-cost stability of arctan `(k, w)`-Gaussian kernel values. -/
theorem abs_gaussianDiagramKernel_sub_le_arctan (σ τ : ℝ) (hC : 0 ≤ C) (D E E' : Diagram ℝ)
    (hE : E.IsPositive) (hE' : E'.IsPositive) :
    |gaussianDiagramKernel σ τ (arctanWeight C hC) D E -
        gaussianDiagramKernel σ τ (arctanWeight C hC) D E'| ≤
      (2 * C + √2 * π / (2 * |σ|)) / |τ| *
        finiteFirstOrderMatchingCost (fun p : E.finiteOccurrences => p.1)
          (fun p : E'.finiteOccurrences => p.1) := by
  simpa only [stabilityConstant_arctan] using
    abs_gaussianDiagramKernel_sub_le_finiteFirstOrderMatchingCost σ τ hC
      Real.pi_div_two_pos.le (arctanWeight C hC) D E E' hE hE'

/-- Count-times-bottleneck stability of arctan `(k, w)`-Gaussian kernel values. -/
theorem abs_gaussianDiagramKernel_sub_le_arctan_card_mul_bottleneck (σ τ : ℝ) (hC : 0 ≤ C)
    (D E E' : Diagram ℝ) (hE : E.IsPositive) (hE' : E'.IsPositive)
    (hfinite : bottleneck E E' < ⊤) :
    |gaussianDiagramKernel σ τ (arctanWeight C hC) D E -
        gaussianDiagramKernel σ τ (arctanWeight C hC) D E'| ≤
      (2 * C + √2 * π / (2 * |σ|)) / |τ| *
        ((Fintype.card E.finiteOccurrences + Fintype.card E'.finiteOccurrences : ℕ) : ℝ) *
          (bottleneck E E').toReal := by
  simpa only [stabilityConstant_arctan] using
    abs_gaussianDiagramKernel_sub_le_card_mul_bottleneck σ τ hC Real.pi_div_two_pos.le
      (arctanWeight C hC) D E E' hE hE' hfinite

end TDA.Persistence.WeightedKernel
