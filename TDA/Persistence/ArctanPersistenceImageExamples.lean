import TDA.Persistence.ArctanPersistenceImage
import TDA.Persistence.ArctanWeightExamples

/-! # Arctan persistence-image consumers

The explicit image constant and its `C = 0` boundary; the zero weight, whose images and
embeddings vanish while every constant stays positive, so the bounds are not sharp there;
the infinite-bottleneck boundary showing that the diagram-level finiteness hypothesis of the
arctan image bound cannot be dropped; and the arctan Rips image instance for a two-point
perturbation with discrepancy `1`. -/

namespace TDA.Persistence.ArctanPersistenceImageExamples

open TDA.Filtration Real MeasureTheory
open PersistenceImage (Weight arctanWeight arctanWeight_birthPersistence feature
  finiteDiagramImage finiteDiagramImage_eq_sum pixelIntegral pixelIntegral_apply)

/-! ## The constant -/

/-- The image constant at `σ = C = 1` and at the boundary `C = 0`. -/
theorem stabilityConstant_values :
    PersistenceImage.stabilityConstant 1 1 (π / 2) = 2 + 3 * √(π / 2) ∧
      PersistenceImage.stabilityConstant 1 0 (π / 2) = 3 * √(π / 2) := by
  constructor <;> · rw [PersistenceImage.stabilityConstant_arctan]; norm_num

/-! ## The zero weight -/

/-- At `C = 0` every finite-part image vanishes. -/
theorem zero_weight_image {K : Type*} [Fintype K] (σ : ℝ) (P : K → Set (ℝ × ℝ))
    (D : Diagram ℝ) : finiteDiagramImage σ (arctanWeight 0 le_rfl) P D = 0 := by
  rw [finiteDiagramImage_eq_sum]
  refine Multiset.sum_eq_zero fun x hx => ?_
  obtain ⟨u, -, rfl⟩ := Multiset.mem_map.mp hx
  rw [feature, PersistenceImage.arctanWeight_apply, zero_mul, Real.arctan_zero, zero_smul]

/-- At `C = 0` every diagram embedding vanishes. -/
theorem zero_weight_embedding (σ : ℝ) (D : Diagram ℝ) :
    WeightedKernel.diagramEmbedding σ (arctanWeight 0 le_rfl) D = 0 := by
  rw [WeightedKernel.diagramEmbedding_eq_sum]
  refine Multiset.sum_eq_zero fun x hx => ?_
  obtain ⟨u, -, rfl⟩ := Multiset.mem_map.mp hx
  rw [PersistenceImage.arctanWeight_apply, zero_mul, Real.arctan_zero, zero_smul]

/-- At `C = 0` both differences between any two diagrams are zero, while the image constant
`3·√(π/2)` and the kernel constant `√2·π/2` at `σ = 1` are positive: the bounds are not sharp
for the zero weight. -/
theorem zero_weight_not_sharp {K : Type*} [Fintype K] (σ : ℝ) (P : K → Set (ℝ × ℝ))
    (D E : Diagram ℝ) :
    ‖finiteDiagramImage σ (arctanWeight 0 le_rfl) P D -
        finiteDiagramImage σ (arctanWeight 0 le_rfl) P E‖ = 0 ∧
      ‖WeightedKernel.diagramEmbedding σ (arctanWeight 0 le_rfl) D -
        WeightedKernel.diagramEmbedding σ (arctanWeight 0 le_rfl) E‖ = 0 ∧
      0 < PersistenceImage.stabilityConstant 1 0 (π / 2) ∧
      WeightedKernel.stabilityConstant 1 0 (π / 2) = √2 * π / 2 ∧
      0 < WeightedKernel.stabilityConstant 1 0 (π / 2) := by
  have hk : WeightedKernel.stabilityConstant 1 0 (π / 2) = √2 * π / 2 := by
    rw [WeightedKernel.stabilityConstant_arctan]; norm_num
  refine ⟨by simp [zero_weight_image], by simp [zero_weight_embedding], ?_, hk, ?_⟩
  · rw [stabilityConstant_values.2]
    have : 0 < √(π / 2) := Real.sqrt_pos.mpr Real.pi_div_two_pos
    positivity
  · rw [hk]
    have : 0 < √2 := by positivity
    have := Real.pi_pos
    positivity

/-! ## The infinite-bottleneck boundary -/

private noncomputable def emptyDiagram : Diagram ℝ := orderedQ 0 0 (Fin.elim0, Fin.elim0)

private noncomputable def obstructedDiagram : Diagram ℝ :=
  orderedQ 1 1 (fun _ => (0, 2), fun _ => 0)

private theorem obstructed_positive : obstructedDiagram.IsPositive := by
  apply (orderedQ_isPositive_iff _ _ _).mpr
  intro i
  norm_num

private theorem empty_positive : emptyDiagram.IsPositive := by
  apply (orderedQ_isPositive_iff _ _ _).mpr
  intro i
  exact i.elim0

private theorem obstructed_finite :
    finitePart obstructedDiagram.points = {(0, 2)} := by
  simp [obstructedDiagram, finitePart_orderedQ, List.ofFn_succ]

private theorem empty_finite : finitePart emptyDiagram.points = 0 := by
  simp [emptyDiagram, finitePart_orderedQ]

private theorem obstructed_bottleneck : bottleneck obstructedDiagram emptyDiagram = ⊤ := by
  apply (bottleneck_eq_top_iff _ _).mpr
  simp [obstructedDiagram, emptyDiagram, essentialPart_orderedQ, List.ofFn_succ]

/-- The single pixel covering the plane. -/
private def wholePlane : Unit → Set (ℝ × ℝ) := fun _ => Set.univ

private theorem norm_wholePlane (u : ℝ × ℝ) :
    ‖pixelIntegral wholePlane (GaussianKernel.density2D 1 u)‖ = 1 := by
  rw [PiLp.norm_eq_of_L1, Fintype.sum_unique, pixelIntegral_apply, wholePlane,
    setIntegral_univ, GaussianKernel.integral_density2D one_pos, norm_one]

private theorem obstructed_norm :
    ‖finiteDiagramImage 1 (arctanWeight 1 zero_le_one) wholePlane obstructedDiagram -
        finiteDiagramImage 1 (arctanWeight 1 zero_le_one) wholePlane emptyDiagram‖ =
      Real.arctan 2 := by
  rw [finiteDiagramImage_eq_sum, finiteDiagramImage_eq_sum, obstructed_finite, empty_finite,
    Multiset.map_singleton, Multiset.sum_singleton, Multiset.map_zero, Multiset.sum_zero,
    sub_zero, feature, norm_smul, norm_wholePlane, mul_one,
    arctanWeight_birthPersistence 1 zero_le_one (by norm_num)]
  norm_num [abs_of_pos (Real.arctan_pos.mpr two_pos)]

/-- For a finite point `(0, 2)` plus one essential bar against the empty diagram, with one
pixel covering the plane, the bottleneck distance is `⊤`; the arctan image difference has
norm `arctan 2 > 0` but the count-times-`toReal` bound is `0`. The hypothesis
`bottleneck D E < ⊤` of `norm_finiteDiagramImage_sub_le_arctan` cannot be dropped. -/
theorem infinite_bottleneck_boundary :
    obstructedDiagram.IsPositive ∧ emptyDiagram.IsPositive ∧
      bottleneck obstructedDiagram emptyDiagram = ⊤ ∧
      ‖finiteDiagramImage 1 (arctanWeight 1 zero_le_one) wholePlane obstructedDiagram -
          finiteDiagramImage 1 (arctanWeight 1 zero_le_one) wholePlane emptyDiagram‖ =
        Real.arctan 2 ∧
      0 < Real.arctan 2 ∧
      ¬ ‖finiteDiagramImage 1 (arctanWeight 1 zero_le_one) wholePlane obstructedDiagram -
          finiteDiagramImage 1 (arctanWeight 1 zero_le_one) wholePlane emptyDiagram‖ ≤
        (2 * 1 + 3 * √(π / 2) / 1) *
          ((Fintype.card obstructedDiagram.finiteOccurrences +
            Fintype.card emptyDiagram.finiteOccurrences : ℕ) : ℝ) *
            (bottleneck obstructedDiagram emptyDiagram).toReal := by
  have hpos : 0 < Real.arctan 2 := Real.arctan_pos.mpr two_pos
  refine ⟨obstructed_positive, empty_positive, obstructed_bottleneck, obstructed_norm, hpos,
    ?_⟩
  rw [obstructed_norm, obstructed_bottleneck, ENNReal.toReal_top, mul_zero]
  exact not_le.mpr hpos

/-! ## The arctan Rips image instance -/

private abbrev twoPointMetric (c : ℝ) (hc : 0 < c) : MetricSpace (Fin 2) where
  dist i j := if i = j then 0 else c
  dist_self _ := if_pos rfl
  dist_comm i j := by simp only [eq_comm]
  dist_triangle i j k := by
    fin_cases i <;> fin_cases j <;> fin_cases k <;> norm_num <;> linarith
  eq_of_dist_eq_zero := by
    intro i j h
    by_contra hij
    simp only [if_neg hij] at h
    exact hc.ne' h

private abbrev metricOne : MetricSpace (Fin 2) := twoPointMetric 1 (by norm_num)
private abbrev metricTwo : MetricSpace (Fin 2) := twoPointMetric 2 (by norm_num)

private theorem metricOne_dist (i j : Fin 2) :
    metricOne.dist i j = if i = j then 0 else 1 := rfl

private theorem metricTwo_dist (i j : Fin 2) :
    metricTwo.dist i j = if i = j then 0 else 2 := rfl

private theorem nonzero_discrepancy : Rips.pairwiseDiscrepancy metricOne metricTwo = 1 := by
  apply le_antisymm
  · apply (Finset.fold_max_le 1).mpr
    refine ⟨by norm_num, ?_⟩
    rintro ⟨i, j⟩ _
    change |(if i = j then 0 else 1) - (if i = j then 0 else 2)| ≤ 1
    split_ifs <;> norm_num
  · have h := Rips.abs_dist_sub_le_pairwiseDiscrepancy metricOne metricTwo 0 1
    rw [metricOne_dist, metricTwo_dist] at h
    norm_num at h
    exact h

/-- Two-point distances `1` and `2` (discrepancy `1`): the arctan Rips image bound at
`σ = C = 1` for every measurable disjoint pixel family. -/
theorem rips_perturbed_arctan (n : ℕ) {K : Type*} [Fintype K] (P : K → Set (ℝ × ℝ))
    (hm : ∀ j, MeasurableSet (P j)) (hd : Pairwise (fun i j => Disjoint (P i) (P j))) :
    ‖finiteDiagramImage 1 (arctanWeight 1 zero_le_one) P (dgm ℚ (Rips.filter metricOne) n) -
        finiteDiagramImage 1 (arctanWeight 1 zero_le_one) P
          (dgm ℚ (Rips.filter metricTwo) n)‖ ≤
      (2 + 3 * √(π / 2)) *
        ((Fintype.card (dgm ℚ (Rips.filter metricOne) n).finiteOccurrences +
          Fintype.card (dgm ℚ (Rips.filter metricTwo) n).finiteOccurrences : ℕ) : ℝ) := by
  have h := Rips.norm_finiteDiagramImage_sub_le_pairwiseDiscrepancy_arctan ℚ metricOne
    metricTwo n one_pos zero_le_one P hm hd
  rw [nonzero_discrepancy, mul_one] at h
  convert h using 2
  norm_num

end TDA.Persistence.ArctanPersistenceImageExamples
