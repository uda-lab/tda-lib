import TDA.Persistence.ArctanWeight
import TDA.Persistence.WeightedKernelStabilityExamples

/-! # Arctan weight consumers

Weight values on, at and below the diagonal; the negative control showing that the
untruncated formula is not a nonnegative weight; sharpness of the sup bound `π / 2`; the
explicit constant and its `C = 0` boundary; an explicit occurrence-level distance against
its bound; and an explicit `(k, w)`-Gaussian kernel value against its bound. Unless stated
otherwise `σ = τ = C = 1`, so the constant is `2 + √2·π/2`. -/

namespace TDA.Persistence.ArctanWeightExamples

open Real WeightedKernel WeightedKernelExamples WeightedKernelStabilityExamples
open PersistenceImage (Weight arctanWeight arctanWeight_apply arctanWeight_birthPersistence)

/-- The arctan weight at `C = 1`. -/
noncomputable abbrev w : Weight 1 (π / 2) := arctanWeight 1 zero_le_one

/-! ## Weight values -/

/-- On, at and below the diagonal: `π / 4` at `(0, 1)`, zero at the diagonal point `(1, 1)`
with zero weighted feature, and zero at the below-diagonal point `(1, 0)`. -/
theorem weight_values :
    w (birthPersistence (0, 1)) = π / 4 ∧
      w (birthPersistence (1, 1)) = 0 ∧ weightedFeature 1 w (1, 1) = 0 ∧
      w (birthPersistence (1, 0)) = 0 := by
  refine ⟨?_, ?_, weightedFeature_diagonal 1 w 1, ?_⟩
  · rw [arctanWeight_birthPersistence 1 zero_le_one (by norm_num)]
    norm_num [Real.arctan_one]
  · rw [arctanWeight_birthPersistence 1 zero_le_one le_rfl]
    simp
  · simp [birthPersistence]

/-! ## Negative control: the sign -/

/-- The untruncated KFH18 formula `arctan pers` at `C = 1` is not a weight: its value at
`(0, -1)` is `-π/4 < 0`. -/
theorem untruncated_not_weight (A B : ℝ) :
    ¬ ∃ v : Weight A B, v.toFun = fun u => Real.arctan u.2 := by
  rintro ⟨v, hv⟩
  have h := v.nonneg (0, -1)
  rw [hv] at h
  simp only [Real.arctan_neg, Real.arctan_one] at h
  linarith [Real.pi_pos]

/-! ## Boundary: the sup bound `π / 2` is sharp -/

/-- For `0 < C`, no weight with a sup bound below `π / 2` has the arctan weight's function. -/
theorem sup_bound_sharp {C : ℝ} (hC : 0 < C) (A B' : ℝ) (hB' : B' < π / 2) :
    ¬ ∃ v : Weight A B', v.toFun = (arctanWeight C hC.le).toFun := by
  rintro ⟨v, hv⟩
  set y := (max B' 0 + π / 2) / 2 with hy
  have hmax : max B' 0 < π / 2 := max_lt hB' Real.pi_div_two_pos
  have hy0 : 0 < y := by have := le_max_right B' 0; linarith
  have hyπ : y < π / 2 := by linarith
  have hBy : B' < y := by have := le_max_left B' 0; linarith
  have ht : 0 < Real.tan y := Real.tan_pos_of_pos_of_lt_pi_div_two hy0 hyπ
  have h := v.bounded (0, Real.tan y / C)
  rw [hv] at h
  change Real.arctan (C * max (Real.tan y / C) 0) ≤ B' at h
  rw [max_eq_left (div_pos ht hC).le, mul_div_cancel₀ _ hC.ne',
    Real.arctan_tan (by linarith) hyπ] at h
  linarith

/-! ## The constant -/

theorem stabilityConstant_values :
    stabilityConstant 1 1 (π / 2) = 2 + √2 * π / 2 ∧
      stabilityConstant 1 0 (π / 2) = √2 * π / 2 := by
  constructor <;> · rw [stabilityConstant_arctan]; norm_num

/-! ## An explicit occurrence-level bound -/

private theorem w_two : w (birthPersistence (0, 2)) = Real.arctan 2 := by
  rw [arctanWeight_birthPersistence 1 zero_le_one (by norm_num)]
  norm_num

private theorem w_three : w (birthPersistence (0, 3)) = Real.arctan 3 := by
  rw [arctanWeight_birthPersistence 1 zero_le_one (by norm_num)]
  norm_num

private theorem single_sq :
    ‖embedding 1 w (single (0, 2)) - embedding 1 w (single (0, 3))‖ ^ 2 =
      Real.arctan 2 ^ 2 + Real.arctan 3 ^ 2 -
        2 * Real.arctan 2 * Real.arctan 3 * Real.exp (-1 / 2) := by
  rw [norm_embedding_sub_sq]
  simp only [linearKernel, single, Finset.univ_unique, Finset.sum_singleton, w_two, w_three,
    kernel_self, kernel_adjacent]
  ring

/-- The actual squared distance of the one-point embeddings `{(0, 2)}` and `{(0, 3)}`, and
the bound `2 + √2·π/2` from the matching of cost `1`. -/
theorem occurrence_bound :
    ‖embedding 1 w (single (0, 2)) - embedding 1 w (single (0, 3))‖ ^ 2 =
        Real.arctan 2 ^ 2 + Real.arctan 3 ^ 2 -
          2 * Real.arctan 2 * Real.arctan 3 * Real.exp (-1 / 2) ∧
      ‖embedding 1 w (single (0, 2)) - embedding 1 w (single (0, 3))‖ ≤ 2 + √2 * π / 2 := by
  refine ⟨single_sq, ?_⟩
  have h := norm_embedding_sub_le_matching 1 zero_le_one Real.pi_div_two_pos.le w
    pairMatching (single (0, 2)) (single (0, 3)) (fun _ => by norm_num [single])
    (fun _ => by norm_num [single])
  rwa [pairMatching_cost, stabilityConstant_values.1, mul_one] at h

/-! ## An explicit kernel value -/

private theorem diagramEmbedding_singleton (b d : ℝ) (h : b ≠ d) :
    diagramEmbedding 1 w (singletonDiagram b d h) = embedding 1 w (single (b, d)) := by
  rw [diagramEmbedding_eq_sum]
  have hp : finitePart (singletonDiagram b d h).points = {(b, d)} := rfl
  rw [hp, Multiset.map_singleton, Multiset.sum_singleton]
  simp [embedding, finiteFeatureSum, single]

/-- The `(k, w)`-Gaussian kernel value of `{(0, 2)}` and `{(0, 3)}`, and its distance from
the self-value `1` against the matching-cost bound. -/
theorem kernel_value :
    gaussianDiagramKernel 1 1 w diagramTwo diagramThree =
        Real.exp (-(Real.arctan 2 ^ 2 + Real.arctan 3 ^ 2 -
          2 * Real.arctan 2 * Real.arctan 3 * Real.exp (-1 / 2)) / 2) ∧
      |1 - gaussianDiagramKernel 1 1 w diagramTwo diagramThree| ≤
        (2 + √2 * π / 2) *
          finiteFirstOrderMatchingCost (fun p : diagramTwo.finiteOccurrences => p.1)
            (fun p : diagramThree.finiteOccurrences => p.1) := by
  have hself : gaussianDiagramKernel 1 1 w diagramTwo diagramTwo = 1 := by
    simp [gaussianDiagramKernel]
  refine ⟨?_, ?_⟩
  · rw [gaussianDiagramKernel, diagramTwo, diagramThree, diagramEmbedding_singleton,
      diagramEmbedding_singleton, single_sq]
    norm_num
  · have h := abs_gaussianDiagramKernel_sub_le_arctan 1 1 zero_le_one diagramTwo diagramTwo
      diagramThree diagram_stability.1 diagram_stability.2.1
    rw [hself] at h
    convert h using 2
    norm_num

end TDA.Persistence.ArctanWeightExamples
