import TDA.Persistence.WeightedKernelExamples
import TDA.Persistence.WeightedKernelStability

/-! # Stability consumers of the weighted Gaussian kernel embedding

The feature bound against an exact distance, a bandwidth negative control showing that the
factor `1/|σ|` is necessary, the zero-bandwidth boundary, matched, unmatched and diagonal
cases of embedding stability, a diagram-level count-times-bottleneck bound, and the
second-level `(k, w)`-Gaussian kernel. The weight is `clippedWeight` with `A = B = 1`, so at
`σ = 1` the constant is `2 + √2`. -/

namespace TDA.Persistence.WeightedKernelStabilityExamples

open WeightedKernel WeightedKernelExamples
open scoped InnerProductSpace

/-- The squared distance of two kernel functions through the unit-vector identity. -/
private theorem featureAt_sub_sq (σ : ℝ) (p q : ℝ × ℝ) :
    ‖featureAt σ p - featureAt σ q‖ ^ 2 = 2 - 2 * kernel σ p q := by
  rw [norm_sub_sq_eq_of_inner_eq_gaussian (norm_featureAt σ p) (norm_featureAt σ q)
    ((inner_featureAt σ p q).trans (kernel_eq_gaussian σ p q)), kernel_eq_gaussian]

private theorem weight_two : clippedWeight (birthPersistence (0, 2)) = 1 := by
  norm_num [clippedWeight, birthPersistence]

theorem stabilityConstant_one : stabilityConstant 1 1 1 = 2 + √2 := by
  norm_num [stabilityConstant]

/-! ## Feature bounds and bandwidth -/

theorem toLp_distance : ‖WithLp.toLp 2 ((0 : ℝ), (2 : ℝ)) - WithLp.toLp 2 ((0 : ℝ), (3 : ℝ))‖ = 1 := by
  have hsq : ‖WithLp.toLp 2 ((0 : ℝ), (2 : ℝ)) - WithLp.toLp 2 ((0 : ℝ), (3 : ℝ))‖ ^ 2 = 1 := by
    rw [WithLp.prod_norm_sq_eq_of_L2]
    norm_num [Real.norm_eq_abs]
  have h0 := norm_nonneg (WithLp.toLp 2 ((0 : ℝ), (2 : ℝ)) - WithLp.toLp 2 ((0 : ℝ), (3 : ℝ)))
  nlinarith

theorem max_distance : ‖((0 : ℝ), (2 : ℝ)) - (0, 3)‖ = 1 := by
  norm_num [Prod.norm_def]

/-- KFH18 Lemma 16 at `σ = 1` against the exact distance `√(2 - 2e^{-1/2})`. -/
theorem feature_distance :
    ‖featureAt 1 (0, 2) - featureAt 1 (0, 3)‖ ^ 2 = 2 - 2 * Real.exp (-1 / 2) ∧
      ‖featureAt 1 (0, 2) - featureAt 1 (0, 3)‖ ≤ 1 ∧
      ‖featureAt 1 (0, 2) - featureAt 1 (0, 3)‖ ≤ √2 := by
  refine ⟨by rw [featureAt_sub_sq, kernel_adjacent], ?_, ?_⟩
  · simpa [toLp_distance] using norm_featureAt_sub_le_euclidean 1 (0, 2) (0, 3)
  · have h := norm_featureAt_sub_le 1 (0, 2) (0, 3)
    rwa [max_distance, abs_one, div_one, mul_one] at h

private theorem exp_neg_two_lt : Real.exp (-2) < 1 / 2 := by
  have h := Real.add_one_lt_exp (show (2 : ℝ) ≠ 0 by norm_num)
  have h2 : Real.exp (-2) * Real.exp 2 = 1 := by rw [← Real.exp_add]; norm_num
  nlinarith [Real.exp_pos (-2)]

/-- Negative control: at `σ = 1/2` the squared feature distance exceeds the squared
maximum-norm distance, so no bandwidth-independent constant-one bound holds. The
Euclidean bound `‖toLp p - toLp q‖ / |σ| = 2` still holds. -/
theorem bandwidth_negative_control :
    ‖featureAt (1 / 2) (0, 2) - featureAt (1 / 2) (0, 3)‖ ^ 2 = 2 - 2 * Real.exp (-2) ∧
      ‖((0 : ℝ), (2 : ℝ)) - (0, 3)‖ ^ 2 < 2 - 2 * Real.exp (-2) ∧
      ¬ ‖featureAt (1 / 2) (0, 2) - featureAt (1 / 2) (0, 3)‖ ≤ ‖((0 : ℝ), (2 : ℝ)) - (0, 3)‖ ∧
      ‖featureAt (1 / 2) (0, 2) - featureAt (1 / 2) (0, 3)‖ ≤ 2 := by
  have hsq : ‖featureAt (1 / 2) (0, 2) - featureAt (1 / 2) (0, 3)‖ ^ 2 =
      2 - 2 * Real.exp (-2) := by
    rw [featureAt_sub_sq]
    norm_num [kernel]
  have hlt : ‖((0 : ℝ), (2 : ℝ)) - (0, 3)‖ ^ 2 < 2 - 2 * Real.exp (-2) := by
    rw [max_distance]
    linarith [exp_neg_two_lt]
  refine ⟨hsq, hlt, fun h => ?_, ?_⟩
  · have h0 := norm_nonneg (featureAt (1 / 2) (0, 2) - featureAt (1 / 2) (0, 3))
    rw [max_distance] at h hlt
    nlinarith
  · have h := norm_featureAt_sub_le_euclidean (1 / 2) (0, 2) (0, 3)
    rw [toLp_distance] at h
    norm_num at h
    exact h

/-- At `σ = 0` the kernel is identically one, all kernel functions coincide, and the
feature bounds read `0 ≤ 0`. -/
theorem zero_bandwidth :
    featureAt 0 (0, 2) = featureAt 0 (0, 3) ∧
      ‖WithLp.toLp 2 ((0 : ℝ), (2 : ℝ)) - WithLp.toLp 2 ((0 : ℝ), (3 : ℝ))‖ / |(0 : ℝ)| = 0 ∧
      √2 / |(0 : ℝ)| * ‖((0 : ℝ), (2 : ℝ)) - (0, 3)‖ = 0 ∧
      ‖featureAt 0 (0, 2) - featureAt 0 (0, 3)‖ ≤
        ‖WithLp.toLp 2 ((0 : ℝ), (2 : ℝ)) - WithLp.toLp 2 ((0 : ℝ), (3 : ℝ))‖ / |(0 : ℝ)| := by
  have h : ‖featureAt 0 (0, 2) - featureAt 0 (0, 3)‖ ^ 2 = 0 := by
    rw [featureAt_sub_sq]
    simp [kernel]
  refine ⟨sub_eq_zero.mp (norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h)),
    by simp, by simp, norm_featureAt_sub_le_euclidean 0 (0, 2) (0, 3)⟩

/-! ## Embedding stability -/

/-- The one-to-one matching of two singletons. -/
def pairMatching : OccurrenceMatching Unit Unit PEmpty.{1} PEmpty.{1} where
  finite _ := some ()
  finite_injective _ _ _ _ _ := Subsingleton.elim _ _
  essential := Equiv.refl _

/-- The empty matching from a singleton to the empty family. -/
def emptyMatching : OccurrenceMatching Unit (Fin 0) PEmpty.{1} PEmpty.{1} where
  finite _ := none
  finite_injective := by simp
  essential := Equiv.refl _

theorem pairMatching_cost :
    pairMatching.totalFiniteCost (single (0, 2)) (single (0, 3)) = 1 := by
  norm_num [OccurrenceMatching.totalFiniteCost, pairMatching, single, Prod.norm_def]

/-- Matched pair: the bound `2 + √2` against the squared distance `2 - 2e^{-1/2}`. -/
theorem matched_stability :
    ‖embedding 1 clippedWeight (single (0, 2)) - embedding 1 clippedWeight (single (0, 3))‖ ≤
        2 + √2 ∧
      ‖embedding 1 clippedWeight (single (0, 2)) -
          embedding 1 clippedWeight (single (0, 3))‖ ≤
        (2 + √2) * finiteFirstOrderMatchingCost (single (0, 2)) (single (0, 3)) ∧
      ‖embedding 1 clippedWeight (single (0, 2)) -
          embedding 1 clippedWeight (single (0, 3))‖ ^ 2 = 2 - 2 * Real.exp (-1 / 2) := by
  have hx : ∀ i, (single (0, 2) i).1 < (single (0, 2) i).2 := fun _ => by norm_num [single]
  have hy : ∀ j, (single (0, 3) j).1 < (single (0, 3) j).2 := fun _ => by norm_num [single]
  refine ⟨?_, ?_, single_distance.1⟩
  · have h := norm_embedding_sub_le_matching 1 zero_le_one zero_le_one clippedWeight
      pairMatching _ _ hx hy
    rwa [pairMatching_cost, stabilityConstant_one, mul_one] at h
  · have h := norm_embedding_sub_le_finiteFirstOrderMatchingCost 1 zero_le_one zero_le_one
      clippedWeight _ _ hx hy
    rwa [stabilityConstant_one] at h

theorem emptyMatching_cost :
    emptyMatching.totalFiniteCost (single (0, 2)) (Fin.elim0 : Fin 0 → ℝ × ℝ) = 1 := by
  norm_num [OccurrenceMatching.totalFiniteCost, emptyMatching, single]

/-- Unmatched point against the empty family: the bound `2 + √2`, norm `1`. -/
theorem unmatched_stability :
    ‖embedding 1 clippedWeight (single (0, 2))‖ ≤ 2 + √2 ∧
      ‖embedding 1 clippedWeight (single (0, 2))‖ = 1 := by
  have h := norm_embedding_sub_le_matching 1 zero_le_one zero_le_one clippedWeight
    emptyMatching (single (0, 2)) (Fin.elim0 : Fin 0 → ℝ × ℝ)
    (fun _ => by norm_num [single]) (fun j => j.elim0)
  rw [emptyMatching_cost, stabilityConstant_one, mul_one, diagonal_embedding.2,
    sub_zero] at h
  refine ⟨h, ?_⟩
  rw [embedding_eq_finiteFeatureSum]
  simp [finiteFeatureSum, single, weightedFeature, norm_featureAt, weight_two]

/-- A diagonal point has zero feature and the diagonal bound reads `0 ≤ 0`. -/
theorem diagonal_point :
    weightedFeature 1 clippedWeight (1, 1) = 0 ∧
      stabilityConstant 1 1 1 * (diagonalCost (1, 1)).toReal = 0 ∧
      ‖weightedFeature 1 clippedWeight (1, 1)‖ ≤
        stabilityConstant 1 1 1 * (diagonalCost (1, 1)).toReal :=
  ⟨weightedFeature_diagonal 1 clippedWeight 1, by simp,
    norm_weightedFeature_le_diagonalCost 1 zero_le_one clippedWeight (1, 1)⟩

/-! ## Diagram level and the second-level kernel -/

/-- The one-point diagram `{(0, 2)}`. -/
noncomputable def diagramTwo : Diagram ℝ := singletonDiagram 0 2 (by norm_num)

/-- The one-point diagram `{(0, 3)}`. -/
noncomputable def diagramThree : Diagram ℝ := singletonDiagram 0 3 (by norm_num)

private theorem diagramEmbedding_singleton (b d : ℝ) (h : b ≠ d) :
    diagramEmbedding 1 clippedWeight (singletonDiagram b d h) =
      embedding 1 clippedWeight (single (b, d)) := by
  rw [diagramEmbedding_eq_sum]
  have hp : finitePart (singletonDiagram b d h).points = {(b, d)} := rfl
  rw [hp, Multiset.map_singleton, Multiset.sum_singleton]
  simp [embedding, finiteFeatureSum, single]

private theorem card_singleton (b d : ℝ) (h : b ≠ d) :
    Fintype.card (singletonDiagram b d h).finiteOccurrences = 1 := by
  have hp : finitePart (singletonDiagram b d h).points = {(b, d)} := rfl
  classical
  rw [Fintype.card_eq_nat_card]
  change Nat.card (finitePart (singletonDiagram b d h).points) = 1
  rw [hp, Nat.card_eq_fintype_card, Multiset.card_coe, Multiset.card_singleton]

/-- Positivity, finite bottleneck and occurrence count `2`, and the diagram-level bound. -/
theorem diagram_stability :
    diagramTwo.IsPositive ∧ diagramThree.IsPositive ∧ bottleneck diagramTwo diagramThree < ⊤ ∧
      Fintype.card diagramTwo.finiteOccurrences +
        Fintype.card diagramThree.finiteOccurrences = 2 ∧
      ‖diagramEmbedding 1 clippedWeight diagramTwo -
          diagramEmbedding 1 clippedWeight diagramThree‖ ≤
        (2 + √2) * 2 * (bottleneck diagramTwo diagramThree).toReal := by
  have hD : diagramTwo.IsPositive := by
    intro p hp
    simp only [diagramTwo, singletonDiagram, Multiset.mem_singleton] at hp
    subst hp
    norm_num
  have hE : diagramThree.IsPositive := by
    intro p hp
    simp only [diagramThree, singletonDiagram, Multiset.mem_singleton] at hp
    subst hp
    norm_num
  have hfin : bottleneck diagramTwo diagramThree < ⊤ :=
    (bottleneck_lt_top_iff _ _).mpr rfl
  have hcard : Fintype.card diagramTwo.finiteOccurrences +
      Fintype.card diagramThree.finiteOccurrences = 2 := by
    rw [diagramTwo, diagramThree, card_singleton, card_singleton]
  refine ⟨hD, hE, hfin, hcard, ?_⟩
  have h := norm_diagramEmbedding_sub_le_card_mul_bottleneck 1 zero_le_one zero_le_one
    clippedWeight _ _ hD hE hfin
  rwa [hcard, stabilityConstant_one, Nat.cast_ofNat] at h

/-- The `(k, w)`-Gaussian kernel at `σ = τ = 1` on the two one-point diagrams, its Gram
entry, and the second-level kernel-value and feature bounds. -/
theorem second_level :
    gaussianDiagramKernel 1 1 clippedWeight diagramTwo diagramTwo = 1 ∧
      gaussianDiagramKernel 1 1 clippedWeight diagramTwo diagramThree =
        Real.exp (-(2 - 2 * Real.exp (-1 / 2)) / 2) ∧
      |1 - Real.exp (-(2 - 2 * Real.exp (-1 / 2)) / 2)| ≤
        ‖diagramEmbedding 1 clippedWeight diagramTwo -
          diagramEmbedding 1 clippedWeight diagramThree‖ / 1 ∧
      ‖diagramGaussianFeature 1 1 clippedWeight diagramTwo -
          diagramGaussianFeature 1 1 clippedWeight diagramThree‖ ≤
        ‖diagramEmbedding 1 clippedWeight diagramTwo -
          diagramEmbedding 1 clippedWeight diagramThree‖ := by
  have hself : gaussianDiagramKernel 1 1 clippedWeight diagramTwo diagramTwo = 1 := by
    simp [gaussianDiagramKernel]
  have hcross : gaussianDiagramKernel 1 1 clippedWeight diagramTwo diagramThree =
      Real.exp (-(2 - 2 * Real.exp (-1 / 2)) / 2) := by
    have h := gaussianDiagramGram_consumer.2
    rw [gaussianGram_diagramEmbedding_apply] at h
    exact h
  refine ⟨hself, hcross, ?_, ?_⟩
  · have h := abs_gaussianDiagramKernel_sub_le 1 1 clippedWeight diagramTwo diagramTwo
      diagramThree
    rwa [hself, hcross, abs_one] at h
  · simpa using norm_diagramGaussianFeature_sub_le 1 1 clippedWeight diagramTwo diagramThree

end TDA.Persistence.WeightedKernelStabilityExamples
