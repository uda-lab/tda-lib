import TDA.Persistence.RipsPersistenceImage

/-! Count dependence, essential-only images, the infinite-bottleneck conversion
boundary, empty inputs and a nonzero distance-matrix perturbation. -/

namespace TDA.Persistence.Rips.PersistenceImageExamples

open TDA.Filtration MeasureTheory Set PersistenceImage

private theorem repeated_total (m : ℕ) :
    finiteFirstOrderMatchingCost (fun _ : Fin (m + 1) => ((0, 2) : ℝ × ℝ))
      (Fin.elim0 : Fin 0 → ℝ × ℝ) = m + 1 := by
  rw [finiteFirstOrderMatchingCost_of_isEmpty_right]
  simp [diagonalCost]

private theorem repeated_maximum (m : ℕ) :
    presentationBottleneck (fun _ : Fin (m + 1) => ((0, 2) : ℝ × ℝ))
      (Fin.elim0 : Fin 0 → ℝ × ℝ) (Fin.elim0 : Fin 0 → ℝ)
      (Fin.elim0 : Fin 0 → ℝ) = 1 := by
  rw [presentationBottleneck_constant_empty]
  norm_num [diagonalCost]

variable {K : Type*} [Fintype K] {σ A B : ℝ}
variable (w : Weight A B) (P : K → Set (ℝ × ℝ))

private theorem essential_only_image (m : ℕ) (b : Fin m → ℝ) :
    finiteDiagramImage σ w P (orderedQ 0 m (Fin.elim0, b)) = 0 := by
  apply finiteDiagramImage_eq_zero_of_finitePart_eq_zero
  simp [finitePart_orderedQ]

private noncomputable def emptyDiagram : Diagram ℝ := orderedQ 0 0 (Fin.elim0, Fin.elim0)

private noncomputable def obstructedDiagram : Diagram ℝ :=
  orderedQ 1 1 (fun _ => (0, 2), fun _ => 0)

private theorem obstructed_positive : obstructedDiagram.IsPositive := by
  apply (orderedQ_isPositive_iff _ _ _).mpr
  intro i
  norm_num

private theorem obstructed_finite :
    finitePart obstructedDiagram.points = {(0, 2)} := by
  simp [obstructedDiagram, finitePart_orderedQ, List.ofFn_succ]

private theorem empty_finite : finitePart emptyDiagram.points = 0 := by
  simp [emptyDiagram, finitePart_orderedQ]

private theorem obstructed_bottleneck : bottleneck obstructedDiagram emptyDiagram = ⊤ := by
  apply (bottleneck_eq_top_iff _ _).mpr
  simp [obstructedDiagram, emptyDiagram, essentialPart_orderedQ, List.ofFn_succ]

private theorem obstructed_finite_cost :
    finiteFirstOrderMatchingCost (fun p : obstructedDiagram.finiteOccurrences => p.1)
      (fun p : emptyDiagram.finiteOccurrences => p.1) = 1 := by
  have : IsEmpty emptyDiagram.finiteOccurrences := by
    change IsEmpty (finitePart emptyDiagram.points)
    rw [empty_finite]
    infer_instance
  have hv (p : obstructedDiagram.finiteOccurrences) : p.1 = (0, 2) := by
    exact Multiset.mem_singleton.mp (by
      simpa only [obstructed_finite] using (Multiset.coe_mem (x := p)))
  rw [finiteFirstOrderMatchingCost_of_isEmpty_right]
  calc
    _ = ∑ _p : obstructedDiagram.finiteOccurrences, (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro p _
      rw [hv p]
      norm_num [diagonalCost]
    _ = 1 := by simp [Diagram.finiteOccurrences, obstructed_finite]

-- A positive finite cost cannot be bounded using the real conversion of an infinite
-- full bottleneck. The generic bridge must retain its finiteness hypothesis.
private theorem infinite_bottleneck_conversion_fails :
    ¬ finiteFirstOrderMatchingCost (fun p : obstructedDiagram.finiteOccurrences => p.1)
        (fun p : emptyDiagram.finiteOccurrences => p.1) ≤
      ((Fintype.card obstructedDiagram.finiteOccurrences +
        Fintype.card emptyDiagram.finiteOccurrences : ℕ) : ℝ) *
          (bottleneck obstructedDiagram emptyDiagram).toReal := by
  rw [obstructed_finite_cost, obstructed_bottleneck]
  simp

variable (hσ : 0 < σ) (hA : 0 ≤ A) (hB : 0 ≤ B)
variable (hm : ∀ j, MeasurableSet (P j))
variable (hd : Pairwise (fun i j => Disjoint (P i) (P j)))

include hσ hA hB hm hd in
private theorem empty_metric_images (d e : MetricSpace (Fin 0)) (n : ℕ) :
    finiteDiagramImage σ w P (dgm ℚ (Rips.filter d) n) =
      finiteDiagramImage σ w P (dgm ℚ (Rips.filter e) n) := by
  have h := norm_finiteDiagramImage_sub_le_pairwiseDiscrepancy ℚ d e n hσ hA hB w P hm hd
  have hzero : Rips.pairwiseDiscrepancy d e = 0 := by
    simp [Rips.pairwiseDiscrepancy]
  rw [hzero, mul_zero] at h
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm h (norm_nonneg _)))

include hσ hA hB hm hd in
private theorem singleton_metric_images (d e : MetricSpace Unit) (n : ℕ) :
    finiteDiagramImage σ w P (dgm ℚ (Rips.filter d) n) =
      finiteDiagramImage σ w P (dgm ℚ (Rips.filter e) n) := by
  have hzero : Rips.pairwiseDiscrepancy d e = 0 := by
    apply le_antisymm _ (Rips.pairwiseDiscrepancy_nonneg d e)
    apply (Finset.fold_max_le 0).mpr
    refine ⟨le_rfl, ?_⟩
    rintro ⟨v, z⟩ _
    cases v
    cases z
    rw [d.dist_self, e.dist_self]
    norm_num
  have h := norm_finiteDiagramImage_sub_le_pairwiseDiscrepancy ℚ d e n hσ hA hB w P hm hd
  rw [hzero, mul_zero] at h
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm h (norm_nonneg _)))

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

include hσ hA hB hm hd in
private theorem perturbed_metric_image_bound (n : ℕ) :
    ‖finiteDiagramImage σ w P (dgm ℚ (Rips.filter metricOne) n) -
        finiteDiagramImage σ w P (dgm ℚ (Rips.filter metricTwo) n)‖ ≤
      stabilityConstant σ A B *
        ((Fintype.card (dgm ℚ (Rips.filter metricOne) n).finiteOccurrences +
          Fintype.card (dgm ℚ (Rips.filter metricTwo) n).finiteOccurrences : ℕ) : ℝ) := by
  simpa only [nonzero_discrepancy, mul_one] using
    norm_finiteDiagramImage_sub_le_pairwiseDiscrepancy ℚ metricOne metricTwo n
      hσ hA hB w P hm hd

end TDA.Persistence.Rips.PersistenceImageExamples
