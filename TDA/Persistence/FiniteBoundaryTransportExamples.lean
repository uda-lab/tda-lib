import TDA.Persistence.FiniteBoundaryTransport

/-! Real fractional plans, boundary assignments, empty inputs and repeated occurrences. -/

noncomputable section

namespace TDA.Persistence.FiniteBoundaryTransportExamples

open scoped Classical

private def pairSingletons : OccurrenceMatching Unit Unit PEmpty.{1} PEmpty.{1} where
  finite _ := some ()
  finite_injective _ _ _ _ _ := Subsingleton.elim _ _
  essential := Equiv.refl _

private theorem singleton_minimum (p q : ℝ × ℝ) :
    finiteFirstOrderBoundaryTransportCost (fun _ : Unit => p) (fun _ : Unit => q) =
      min (finitePairCost p q).toReal ((diagonalCost p).toReal + (diagonalCost q).toReal) := by
  rw [finiteFirstOrderBoundaryTransportCost_eq_matchingCost]
  apply le_antisymm
  · apply le_min
    · simpa [OccurrenceMatching.totalFiniteCost, pairSingletons] using
        finiteFirstOrderMatchingCost_le_totalFiniteCost
          (fun _ : Unit => p) (fun _ : Unit => q) pairSingletons
    · simpa using finiteFirstOrderMatchingCost_le_diagonalSum
        (fun _ : Unit => p) (fun _ : Unit => q)
  · apply (le_finiteFirstOrderMatchingCost_iff _ _ _).mpr
    intro M
    cases h : M.finite () with
    | none => simp [OccurrenceMatching.totalFiniteCost, h]
    | some j => cases j; simp [OccurrenceMatching.totalFiniteCost, h]

private def halfPlan : FiniteBoundaryPlan Unit Unit where
  mass _ _ := 1 / 2
  nonneg _ _ := by norm_num
  row_le_one _ := by norm_num
  col_le_one _ := by norm_num

/-- Both residual masses are nonzero; this plan is not an incidence matrix. -/
private theorem fractional_cost_and_deficits :
    halfPlan.mass () () = 1 / 2 ∧ halfPlan.deletionMass () = 1 / 2 ∧
    halfPlan.insertionMass () = 1 / 2 ∧
    halfPlan.cost (fun _ => (0, 2)) (fun _ => (0, 4)) = 5 / 2 := by
  norm_num [halfPlan, FiniteBoundaryPlan.deletionMass, FiniteBoundaryPlan.insertionMass,
    FiniteBoundaryPlan.cost, finitePairCost, diagonalCost]

private theorem pairing_preferred :
    finiteFirstOrderBoundaryTransportCost (fun _ : Unit => ((0, 2) : ℝ × ℝ))
      (fun _ : Unit => (0, 4)) = 2 := by
  rw [singleton_minimum]
  norm_num [finitePairCost, diagonalCost]

private theorem deletion_preferred :
    finiteFirstOrderBoundaryTransportCost (fun _ : Unit => ((0, 2) : ℝ × ℝ))
      (fun _ : Unit => (10, 12)) = 2 := by
  rw [singleton_minimum]
  norm_num [finitePairCost, diagonalCost]

/-- The raw collapsed-boundary cost fails the triangle inequality through the boundary. -/
private theorem raw_cost_not_metric :
    (diagonalCost ((0, 2) : ℝ × ℝ)).toReal +
      (diagonalCost ((10, 12) : ℝ × ℝ)).toReal <
      (finitePairCost (0, 2) (10, 12)).toReal := by
  norm_num [finitePairCost, diagonalCost]

private def boundarySwap : (Fin 2 ⊕ Fin 2) ≃ (Fin 2 ⊕ Fin 2) :=
  Equiv.swap (.inl 0) (.inr 1)

private def source : Fin 2 → ℝ × ℝ := ![(0, 2), (4, 8)]
private def target : Fin 2 → ℝ × ℝ := ![(10, 16), (4, 8)]

/-- Deletion and insertion use dummies with different labels; their costs remain 1 and 3. -/
private theorem off_label_dummy_assignment :
    boundaryAssignmentCost source target boundarySwap = 4 := by
  norm_num [boundaryAssignmentCost, boundaryAssignmentEntry, boundarySwap,
    Equiv.swap_apply_def, Fintype.sum_sum_type, Fin.sum_univ_succ,
    source, target, finitePairCost, diagonalCost]
  simp
  norm_num

private theorem restricted_assignment_cost :
    (OccurrenceMatching.ofBoundaryAssignment boundarySwap).totalFiniteCost source target = 4 := by
  rw [OccurrenceMatching.totalFiniteCost_ofBoundaryAssignment, off_label_dummy_assignment]

private theorem completion_section :
    OccurrenceMatching.ofBoundaryAssignment
      (OccurrenceMatching.ofBoundaryAssignment boundarySwap).toBoundaryAssignment =
        OccurrenceMatching.ofBoundaryAssignment boundarySwap :=
  OccurrenceMatching.ofBoundaryAssignment_toBoundaryAssignment _

private def repeatedHalfPlan : FiniteBoundaryPlan (Fin 2) Unit where
  mass _ _ := 1 / 2
  nonneg _ _ := by norm_num
  row_le_one _ := by norm_num
  col_le_one _ := by norm_num [Fin.sum_univ_two]

private def selectFirst : OccurrenceMatching (Fin 2) Unit PEmpty.{1} PEmpty.{1} where
  finite i := if i = 0 then some () else none
  finite_injective := by
    intro i i' j hi hi'
    simp only [ite_eq_left_iff, reduceCtorEq, imp_false, not_not] at hi hi'
    simp_all
  essential := Equiv.refl _

private theorem repeated_minimum :
    finiteFirstOrderBoundaryTransportCost (fun _ : Fin 2 => ((0, 2) : ℝ × ℝ))
      (fun _ : Unit => (0, 2)) = 1 := by
  rw [finiteFirstOrderBoundaryTransportCost_eq_matchingCost]
  apply le_antisymm
  · have h := finiteFirstOrderMatchingCost_le_totalFiniteCost
      (fun _ : Fin 2 => ((0, 2) : ℝ × ℝ)) (fun _ : Unit => (0, 2)) selectFirst
    norm_num [OccurrenceMatching.totalFiniteCost, selectFirst, Fin.sum_univ_two,
      Fin.exists_fin_succ, finitePairCost, diagonalCost] at h ⊢
    exact h
  · apply (le_finiteFirstOrderMatchingCost_iff _ _ _).mpr
    intro M
    cases h0 : M.finite 0 with
    | none =>
      cases h1 : M.finite 1 with
      | none =>
        norm_num [OccurrenceMatching.totalFiniteCost, Fin.sum_univ_two,
          Fin.exists_fin_succ, h0, h1, diagonalCost]
        simp
      | some j => cases j; norm_num [OccurrenceMatching.totalFiniteCost, Fin.sum_univ_two,
          Fin.exists_fin_succ, h0, h1, finitePairCost, diagonalCost]
    | some j =>
      cases j
      cases h1 : M.finite 1 with
      | none => norm_num [OccurrenceMatching.totalFiniteCost, Fin.sum_univ_two,
          Fin.exists_fin_succ, h0, h1, finitePairCost, diagonalCost]
      | some j =>
        cases j
        have h := M.finite_injective 0 1 () h0 h1
        norm_num at h

/-- A fractional optimum coexists with an integral optimum; multiplicity is not deduplicated. -/
private theorem fractional_optimum :
    repeatedHalfPlan.cost (fun _ => (0, 2)) (fun _ => (0, 2)) =
      finiteFirstOrderBoundaryTransportCost (fun _ : Fin 2 => ((0, 2) : ℝ × ℝ))
        (fun _ : Unit => (0, 2)) := by
  rw [repeated_minimum]
  norm_num [FiniteBoundaryPlan.cost, FiniteBoundaryPlan.deletionMass,
    FiniteBoundaryPlan.insertionMass, repeatedHalfPlan, Fin.sum_univ_two,
    finitePairCost, diagonalCost]

private theorem repeated_to_empty :
    finiteFirstOrderBoundaryTransportCost (fun _ : Fin 2 => ((0, 2) : ℝ × ℝ))
      (Fin.elim0 : Fin 0 → ℝ × ℝ) = 2 := by
  rw [finiteFirstOrderBoundaryTransportCost_of_isEmpty_right, Fin.sum_univ_two]
  norm_num [diagonalCost]

private theorem empty_to_repeated :
    finiteFirstOrderBoundaryTransportCost (Fin.elim0 : Fin 0 → ℝ × ℝ)
      (fun _ : Fin 2 => ((0, 2) : ℝ × ℝ)) = 2 := by
  rw [finiteFirstOrderBoundaryTransportCost_of_isEmpty_left, Fin.sum_univ_two]
  norm_num [diagonalCost]

private theorem empty_cost :
    finiteFirstOrderBoundaryTransportCost (Fin.elim0 : Fin 0 → ℝ × ℝ)
      (Fin.elim0 : Fin 0 → ℝ × ℝ) = 0 := by simp

private theorem empty_padding :
    (FiniteBoundaryPlan.zero : FiniteBoundaryPlan (Fin 0) (Fin 0)).paddedMatrix ∈
      doublyStochastic ℝ (Fin 0 ⊕ Fin 0) :=
  FiniteBoundaryPlan.paddedMatrix_doublyStochastic _

private theorem relabelled_transport :
    finiteFirstOrderBoundaryTransportCost (source ∘ Equiv.swap 0 1) target =
      finiteFirstOrderBoundaryTransportCost source target := by
  simpa using finiteFirstOrderBoundaryTransportCost_reindex
    (Equiv.swap 0 1) (Equiv.refl _) source target

end TDA.Persistence.FiniteBoundaryTransportExamples
