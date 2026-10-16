import TDA.Persistence.RipsStability

/-! Empty and singleton inputs, and a nonzero perturbation of a two-point metric. -/

namespace TDA.Persistence.Rips.Examples

open TDA.Filtration

private theorem empty_face_excluded :
    (∅ : Finset (Fin 2)) ∉ Rips.fullComplex (Fin 2) := by simp

private theorem empty_carrier_bottleneck (d e : MetricSpace (Fin 0)) (n : ℕ) :
    bottleneck (dgm ℚ (Rips.filter d) n) (dgm ℚ (Rips.filter e) n) = 0 := by
  apply le_antisymm _ bot_le
  simpa using bottleneck_dgm_le_pairwiseDiscrepancy ℚ d e n

private theorem singleton_value (d : MetricSpace Unit) :
    Rips.diameter d {()} = 0 := Rips.diameter_singleton d ()

private theorem singleton_discrepancy (d e : MetricSpace Unit) :
    Rips.pairwiseDiscrepancy d e = 0 := by
  apply le_antisymm _ (Rips.pairwiseDiscrepancy_nonneg d e)
  apply (Finset.fold_max_le 0).mpr
  refine ⟨le_rfl, ?_⟩
  rintro ⟨v, w⟩ _
  cases v
  cases w
  rw [d.dist_self, e.dist_self]
  norm_num

private theorem singleton_bottleneck (d e : MetricSpace Unit) (n : ℕ) :
    bottleneck (dgm ℚ (Rips.filter d) n) (dgm ℚ (Rips.filter e) n) = 0 := by
  apply le_antisymm _ zero_le
  simpa only [singleton_discrepancy, ENNReal.ofReal_zero] using
    bottleneck_dgm_le_pairwiseDiscrepancy ℚ d e n

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

private theorem first_edge_time : Rips.diameter metricOne {0, 1} = 1 := by
  rw [Rips.diameter_pair]
  rw [metricOne_dist]
  norm_num

private theorem perturbed_edge_time : Rips.diameter metricTwo {0, 1} = 2 := by
  rw [Rips.diameter_pair]
  rw [metricTwo_dist]
  norm_num

private theorem perturbation_discrepancy : Rips.pairwiseDiscrepancy metricOne metricTwo = 1 := by
  apply le_antisymm
  · apply (Finset.fold_max_le 1).mpr
    refine ⟨by norm_num, ?_⟩
    rintro ⟨i, j⟩ _
    rw [metricOne_dist, metricTwo_dist]
    split_ifs <;> norm_num
  · have h := Rips.abs_dist_sub_le_pairwiseDiscrepancy metricOne metricTwo 0 1
    rw [metricOne_dist, metricTwo_dist] at h
    norm_num at h
    exact h

private theorem perturbation_actual_diagram_bound (n : ℕ) :
    bottleneck (dgm ℚ (Rips.filter metricOne) n) (dgm ℚ (Rips.filter metricTwo) n) ≤ 1 := by
  simpa only [perturbation_discrepancy, ENNReal.ofReal_one] using
    bottleneck_dgm_le_pairwiseDiscrepancy ℚ metricOne metricTwo n

private theorem negative_stage_empty : (Rips.filter metricOne).sublevel (-1) = ⊥ :=
  Rips.sublevel_eq_bot_of_neg metricOne (by norm_num)

end TDA.Persistence.Rips.Examples
