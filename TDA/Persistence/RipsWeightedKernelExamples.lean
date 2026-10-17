import TDA.Persistence.RipsWeightedKernel
import TDA.Persistence.ArctanWeightExamples

/-! # Rips weighted-kernel consumers

Empty and singleton carriers, where the pairwise discrepancy is zero and the embeddings and
kernel values coincide; a nonzero two-point perturbation with discrepancy `1`, generically
and for the arctan weight at `σ = τ = C = 1`; and the infinite-bottleneck boundary showing
that the diagram-level finiteness hypothesis cannot be dropped. -/

namespace TDA.Persistence.RipsWeightedKernelExamples

open TDA.Filtration Real WeightedKernel
open PersistenceImage (Weight arctanWeight arctanWeight_birthPersistence)

variable {A B : ℝ} (σ τ : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (w : Weight A B)

/-! ## Empty and singleton carriers -/

private theorem empty_discrepancy (d e : MetricSpace (Fin 0)) :
    Rips.pairwiseDiscrepancy d e = 0 := by
  simp [Rips.pairwiseDiscrepancy]

private theorem singleton_discrepancy (d e : MetricSpace Unit) :
    Rips.pairwiseDiscrepancy d e = 0 := by
  apply le_antisymm _ (Rips.pairwiseDiscrepancy_nonneg d e)
  apply (Finset.fold_max_le 0).mpr
  refine ⟨le_rfl, ?_⟩
  rintro ⟨v, z⟩ _
  cases v
  cases z
  rw [d.dist_self, e.dist_self]
  norm_num

include hA hB in
/-- On an empty carrier the embeddings and all kernel values coincide. -/
theorem empty_carrier (d e : MetricSpace (Fin 0)) (n : ℕ) (D : Diagram ℝ) :
    diagramEmbedding σ w (dgm ℚ (Rips.filter d) n) =
        diagramEmbedding σ w (dgm ℚ (Rips.filter e) n) ∧
      gaussianDiagramKernel σ τ w D (dgm ℚ (Rips.filter d) n) =
        gaussianDiagramKernel σ τ w D (dgm ℚ (Rips.filter e) n) := by
  have h₁ := Rips.norm_diagramEmbedding_sub_le_pairwiseDiscrepancy ℚ d e n σ hA hB w
  have h₂ := Rips.abs_gaussianDiagramKernel_sub_le_pairwiseDiscrepancy ℚ d e n σ τ hA hB w D
  rw [empty_discrepancy, mul_zero] at h₁ h₂
  exact ⟨sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm h₁ (norm_nonneg _))),
    sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm h₂ (abs_nonneg _)))⟩

include hA hB in
/-- On a singleton carrier the embeddings and all kernel values coincide. -/
theorem singleton_carrier (d e : MetricSpace Unit) (n : ℕ) (D : Diagram ℝ) :
    diagramEmbedding σ w (dgm ℚ (Rips.filter d) n) =
        diagramEmbedding σ w (dgm ℚ (Rips.filter e) n) ∧
      gaussianDiagramKernel σ τ w D (dgm ℚ (Rips.filter d) n) =
        gaussianDiagramKernel σ τ w D (dgm ℚ (Rips.filter e) n) := by
  have h₁ := Rips.norm_diagramEmbedding_sub_le_pairwiseDiscrepancy ℚ d e n σ hA hB w
  have h₂ := Rips.abs_gaussianDiagramKernel_sub_le_pairwiseDiscrepancy ℚ d e n σ τ hA hB w D
  rw [singleton_discrepancy, mul_zero] at h₁ h₂
  exact ⟨sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm h₁ (norm_nonneg _))),
    sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm h₂ (abs_nonneg _)))⟩

/-! ## A nonzero perturbation -/

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

include hA hB in
/-- Two-point distances `1` and `2` (discrepancy `1`): the embedding and kernel-value
bounds. -/
theorem perturbed_bounds (n : ℕ) (D : Diagram ℝ) :
    ‖diagramEmbedding σ w (dgm ℚ (Rips.filter metricOne) n) -
        diagramEmbedding σ w (dgm ℚ (Rips.filter metricTwo) n)‖ ≤
      stabilityConstant σ A B *
        ((Fintype.card (dgm ℚ (Rips.filter metricOne) n).finiteOccurrences +
          Fintype.card (dgm ℚ (Rips.filter metricTwo) n).finiteOccurrences : ℕ) : ℝ) ∧
    |gaussianDiagramKernel σ τ w D (dgm ℚ (Rips.filter metricOne) n) -
        gaussianDiagramKernel σ τ w D (dgm ℚ (Rips.filter metricTwo) n)| ≤
      stabilityConstant σ A B / |τ| *
        ((Fintype.card (dgm ℚ (Rips.filter metricOne) n).finiteOccurrences +
          Fintype.card (dgm ℚ (Rips.filter metricTwo) n).finiteOccurrences : ℕ) : ℝ) := by
  constructor
  · simpa only [nonzero_discrepancy, mul_one] using
      Rips.norm_diagramEmbedding_sub_le_pairwiseDiscrepancy ℚ metricOne metricTwo n σ hA hB w
  · simpa only [nonzero_discrepancy, mul_one] using
      Rips.abs_gaussianDiagramKernel_sub_le_pairwiseDiscrepancy ℚ metricOne metricTwo n σ τ
        hA hB w D

/-- The arctan instance at `σ = τ = C = 1`. -/
theorem perturbed_arctan (n : ℕ) (D : Diagram ℝ) :
    |gaussianDiagramKernel 1 1 (arctanWeight 1 zero_le_one) D
          (dgm ℚ (Rips.filter metricOne) n) -
        gaussianDiagramKernel 1 1 (arctanWeight 1 zero_le_one) D
          (dgm ℚ (Rips.filter metricTwo) n)| ≤
      (2 + √2 * π / 2) *
        ((Fintype.card (dgm ℚ (Rips.filter metricOne) n).finiteOccurrences +
          Fintype.card (dgm ℚ (Rips.filter metricTwo) n).finiteOccurrences : ℕ) : ℝ) := by
  have h := Rips.abs_gaussianDiagramKernel_sub_le_pairwiseDiscrepancy_arctan ℚ metricOne
    metricTwo n 1 1 zero_le_one D
  rw [nonzero_discrepancy, mul_one] at h
  convert h using 2
  norm_num

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

private theorem obstructed_norm :
    ‖diagramEmbedding 1 (arctanWeight 1 zero_le_one) obstructedDiagram -
        diagramEmbedding 1 (arctanWeight 1 zero_le_one) emptyDiagram‖ = Real.arctan 2 := by
  rw [diagramEmbedding_eq_sum, diagramEmbedding_eq_sum, obstructed_finite, empty_finite,
    Multiset.map_singleton, Multiset.sum_singleton, Multiset.map_zero, Multiset.sum_zero,
    sub_zero, norm_smul, norm_featureAt, mul_one,
    arctanWeight_birthPersistence 1 zero_le_one (by norm_num)]
  norm_num [abs_of_pos (Real.arctan_pos.mpr two_pos)]

/-- For a finite point `(0, 2)` plus one essential bar against the empty diagram, the
bottleneck distance is `⊤`; the arctan embedding difference has norm `arctan 2 > 0` but the
count-times-`toReal` bound is `0`. The hypothesis `bottleneck D E < ⊤` of
`norm_diagramEmbedding_sub_le_arctan` cannot be dropped; the Rips consumers discharge it by
`Rips.bottleneck_dgm_lt_top`. -/
theorem infinite_bottleneck_boundary :
    obstructedDiagram.IsPositive ∧ emptyDiagram.IsPositive ∧
      bottleneck obstructedDiagram emptyDiagram = ⊤ ∧
      ‖diagramEmbedding 1 (arctanWeight 1 zero_le_one) obstructedDiagram -
          diagramEmbedding 1 (arctanWeight 1 zero_le_one) emptyDiagram‖ = Real.arctan 2 ∧
      0 < Real.arctan 2 ∧
      ¬ ‖diagramEmbedding 1 (arctanWeight 1 zero_le_one) obstructedDiagram -
          diagramEmbedding 1 (arctanWeight 1 zero_le_one) emptyDiagram‖ ≤
        (2 * 1 + √2 * π / (2 * |(1 : ℝ)|)) *
          ((Fintype.card obstructedDiagram.finiteOccurrences +
            Fintype.card emptyDiagram.finiteOccurrences : ℕ) : ℝ) *
            (bottleneck obstructedDiagram emptyDiagram).toReal := by
  have hpos : 0 < Real.arctan 2 := Real.arctan_pos.mpr two_pos
  refine ⟨obstructed_positive, empty_positive, obstructed_bottleneck, obstructed_norm, hpos,
    ?_⟩
  rw [obstructed_norm, obstructed_bottleneck, ENNReal.toReal_top, mul_zero]
  exact not_le.mpr hpos

end TDA.Persistence.RipsWeightedKernelExamples
