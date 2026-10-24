import TDA.Persistence.BoundaryTransportIndexed

/-!
# Repeated weighted occurrences and finite splitting

Two source labels share a point, while a third carries zero mass at a distant
point. Fractional target masses test both finite splitting and geometric powers.
-/

set_option autoImplicit false
noncomputable section

namespace TDA.Persistence.FiniteWeightedCoalescingExamples

open BoundaryTransport MeasureTheory
open scoped Classical NNReal

private theorem third_ne_first : (2 : Fin 3) ≠ 0 := by decide
private theorem third_ne_second : (2 : Fin 3) ≠ 1 := by decide
attribute [local simp] third_ne_first third_ne_second

private def sourcePoint : Interior := ⟨(0, 4), by norm_num⟩
private def targetPoint : Interior := ⟨(1, 5), by norm_num⟩
private def ghostPoint : Interior := ⟨(100, 104), by norm_num⟩

private def sourceWeight (i : Fin 3) : ℝ≥0 :=
  if i.1 = 0 then 1 / 2 else if i.1 = 1 then 3 / 2 else 0

private def targetWeight (j : Fin 2) : ℝ≥0 := if j.1 = 0 then 1 / 4 else 3 / 4

private def sourceCoordinates (i : Fin 3) : Interior :=
  if i.1 = 2 then ghostPoint else sourcePoint

private def targetCoordinates (_ : Fin 2) : Interior := targetPoint

private abbrev sourceDiagram : FiniteWeightedDiagram :=
  FiniteWeightedDiagram.ofIndexed sourceWeight sourceCoordinates

private abbrev targetDiagram : FiniteWeightedDiagram :=
  FiniteWeightedDiagram.ofIndexed targetWeight targetCoordinates

private theorem coalesced_source_mass :
    sourceDiagram sourcePoint = 2 ∧ sourceDiagram ghostPoint = 0 := by
  norm_num [sourceDiagram, FiniteWeightedDiagram.ofIndexed_apply,
    sourceCoordinates, sourceWeight, Fin.sum_univ_three, sourcePoint, ghostPoint]

private theorem coalesced_target_mass : targetDiagram targetPoint = 1 := by
  norm_num [targetDiagram, FiniteWeightedDiagram.ofIndexed_apply,
    targetCoordinates, targetWeight, Fin.sum_univ_two]

private theorem total_source_mass :
    (∑ q : sourceDiagram.supportLabels, (sourceDiagram.weights q : ℝ)) = 2 := by
  rw [FiniteWeightedDiagram.ofIndexed_mass]
  norm_num [sourceWeight, Fin.sum_univ_three]

/-- A feasible allocation deliberately uses only the second repeated source label. -/
private def concentratedPlan : FiniteWeightedBoundaryPlan sourceWeight targetWeight where
  mass i j := if i.1 = 1 then (targetWeight j : ℝ) else 0
  nonneg i j := by split_ifs <;> positivity
  row_le i := by
    fin_cases i <;> norm_num [sourceWeight, targetWeight, Fin.sum_univ_two]
  col_le j := by
    fin_cases j <;> norm_num [sourceWeight, targetWeight, Fin.sum_univ_three]

private theorem concentrated_powered_cost :
    concentratedPlan.powerCost 2 (fun i => (sourceCoordinates i).1)
      (fun j => (targetCoordinates j).1) = 5 := by
  norm_num [FiniteWeightedBoundaryPlan.powerCost, FiniteWeightedBoundaryPlan.linearCost,
    weightedBoundaryLinearObjective, concentratedPlan, sourceWeight, targetWeight,
    sourceCoordinates, targetCoordinates, sourcePoint, targetPoint, ghostPoint,
    Fin.sum_univ_three, Fin.sum_univ_two, finitePairCost, diagonalCost]

private theorem concentrated_first_order_cost :
    concentratedPlan.powerCost 1 (fun i => (sourceCoordinates i).1)
      (fun j => (targetCoordinates j).1) = 3 := by
  norm_num [FiniteWeightedBoundaryPlan.powerCost, FiniteWeightedBoundaryPlan.linearCost,
    weightedBoundaryLinearObjective, concentratedPlan, sourceWeight, targetWeight,
    sourceCoordinates, targetCoordinates, sourcePoint, targetPoint, ghostPoint,
    Fin.sum_univ_three, Fin.sum_univ_two, finitePairCost, diagonalCost]

private theorem every_plan_powered_cost_ge
    (a : FiniteWeightedBoundaryPlan sourceWeight targetWeight) :
    5 ≤ a.powerCost 2 (fun i => (sourceCoordinates i).1)
      (fun j => (targetCoordinates j).1) := by
  have hrow := a.row_le 2
  have h20 := a.nonneg 2 0
  have h21 := a.nonneg 2 1
  norm_num [sourceWeight, Fin.sum_univ_two] at hrow
  have hz20 : a.mass 2 0 = 0 := by linarith
  have hz21 : a.mass 2 1 = 0 := by linarith
  have hc0 := a.col_le 0
  have hc1 := a.col_le 1
  norm_num [targetWeight, Fin.sum_univ_three, hz20, hz21] at hc0 hc1
  norm_num [FiniteWeightedBoundaryPlan.powerCost, FiniteWeightedBoundaryPlan.linearCost,
    weightedBoundaryLinearObjective, sourceWeight, targetWeight,
    sourceCoordinates, targetCoordinates, sourcePoint, targetPoint, ghostPoint,
    Fin.sum_univ_three, Fin.sum_univ_two, finitePairCost, diagonalCost, hz20, hz21]
  linarith

private theorem indexed_powered_optimum :
    weightedPowerBoundaryTransportCost 2 sourceWeight targetWeight
      (fun i => (sourceCoordinates i).1) (fun j => (targetCoordinates j).1) = 5 := by
  apply le_antisymm
  · exact (weightedPowerBoundaryTransportCost_le_plan 2 _ _ _ _ concentratedPlan).trans_eq
      concentrated_powered_cost
  · exact le_ciInf every_plan_powered_cost_ge

private def aggregatePlan :
    FiniteWeightedBoundaryPlan sourceDiagram.weights targetDiagram.weights :=
  concentratedPlan.aggregate sourceCoordinates targetCoordinates

private def recoveredPlan : FiniteWeightedBoundaryPlan sourceWeight targetWeight :=
  FiniteWeightedBoundaryPlan.splitLift sourceCoordinates targetCoordinates aggregatePlan

private theorem aggregate_powered_cost :
    aggregatePlan.powerCost 2 sourceDiagram.coordinates targetDiagram.coordinates = 5 :=
  (FiniteWeightedBoundaryPlan.powerCost_aggregate concentratedPlan 2
    sourceCoordinates targetCoordinates).trans concentrated_powered_cost

private theorem recovered_powered_cost :
    recoveredPlan.powerCost 2 (fun i => (sourceCoordinates i).1)
      (fun j => (targetCoordinates j).1) = 5 :=
  (FiniteWeightedBoundaryPlan.powerCost_splitLift sourceCoordinates targetCoordinates
    aggregatePlan 2).trans aggregate_powered_cost

private theorem aggregate_optimizer :
    aggregatePlan.powerCost 2 sourceDiagram.coordinates targetDiagram.coordinates =
      FiniteWeightedDiagram.powerBoundaryTransportCost 2 sourceDiagram targetDiagram :=
  FiniteWeightedDiagram.aggregate_minimizing_powerPlan 2 sourceWeight targetWeight
    sourceCoordinates targetCoordinates concentratedPlan
    (concentrated_powered_cost.trans indexed_powered_optimum.symm)

private theorem recovered_optimizer :
    recoveredPlan.powerCost 2 (fun i => (sourceCoordinates i).1)
      (fun j => (targetCoordinates j).1) =
      weightedPowerBoundaryTransportCost 2 sourceWeight targetWeight
        (fun i => (sourceCoordinates i).1) (fun j => (targetCoordinates j).1) :=
  FiniteWeightedDiagram.splitLift_minimizing_powerPlan 2 sourceWeight targetWeight
    sourceCoordinates targetCoordinates aggregatePlan aggregate_optimizer

private theorem canonical_cells_recovered
    (q : sourceDiagram.supportLabels) (r : targetDiagram.supportLabels) :
    (recoveredPlan.aggregate sourceCoordinates targetCoordinates).mass q r =
      aggregatePlan.mass q r :=
  FiniteWeightedBoundaryPlan.aggregate_splitLift_mass sourceCoordinates targetCoordinates
    aggregatePlan q r

private theorem sourceDiagram_single : sourceDiagram = Finsupp.single sourcePoint 2 := by
  ext q
  by_cases h : sourcePoint = q <;>
    norm_num [sourceDiagram, FiniteWeightedDiagram.ofIndexed_apply, sourceCoordinates,
      sourceWeight, Fin.sum_univ_three, Finsupp.single_apply, h]

private theorem targetDiagram_single : targetDiagram = Finsupp.single targetPoint 1 := by
  ext q
  by_cases h : targetPoint = q <;>
    norm_num [targetDiagram, FiniteWeightedDiagram.ofIndexed_apply, targetCoordinates,
      targetWeight, Fin.sum_univ_two, Finsupp.single_apply, h]

private def sourceLabel : sourceDiagram.supportLabels :=
  ⟨sourcePoint, by
    apply Finsupp.mem_support_iff.mpr
    rw [coalesced_source_mass.1]
    norm_num⟩

private def targetLabel : targetDiagram.supportLabels :=
  ⟨targetPoint, by
    apply Finsupp.mem_support_iff.mpr
    rw [coalesced_target_mass]
    norm_num⟩

private theorem sourceLabel_unique (q : sourceDiagram.supportLabels) : q = sourceLabel := by
  apply Subtype.ext
  by_contra h
  have hne : sourcePoint ≠ q.1 := fun hq => h hq.symm
  have hq := Finsupp.mem_support_iff.mp q.2
  have heq := congrArg (fun D : FiniteWeightedDiagram => D q.1) sourceDiagram_single
  exact hq (heq.trans (by simp [hne]))

private theorem targetLabel_unique (r : targetDiagram.supportLabels) : r = targetLabel := by
  apply Subtype.ext
  by_contra h
  have hne : targetPoint ≠ r.1 := fun hr => h hr.symm
  have hr := Finsupp.mem_support_iff.mp r.2
  have heq := congrArg (fun D : FiniteWeightedDiagram => D r.1) targetDiagram_single
  exact hr (heq.trans (by simp [hne]))

private theorem proportional_entry : recoveredPlan.mass 0 0 = 1 / 16 := by
  change (FiniteWeightedBoundaryPlan.splitLift sourceCoordinates targetCoordinates
    aggregatePlan).mass 0 0 = 1 / 16
  rw [FiniteWeightedBoundaryPlan.splitLift_mass]
  rw [Finset.sum_eq_single sourceLabel]
  · rw [Finset.sum_eq_single targetLabel]
    · norm_num [FiniteWeightedDiagram.splittingKernel, aggregatePlan,
        FiniteWeightedBoundaryPlan.aggregate_mass, concentratedPlan,
        sourceLabel, targetLabel, FiniteWeightedDiagram.ofIndexed_apply,
        sourceCoordinates, targetCoordinates, sourceWeight, targetWeight,
        Fin.sum_univ_three, Fin.sum_univ_two]
    · intro r _ hne
      exact (hne (targetLabel_unique r)).elim
    · intro h
      exact (h (Finset.mem_univ targetLabel)).elim
  · intro q _ hne
    exact (hne (sourceLabel_unique q)).elim
  · intro h
    exact (h (Finset.mem_univ sourceLabel)).elim

private theorem indexed_allocation_changes : recoveredPlan ≠ concentratedPlan := by
  intro h
  have heq := congrArg (fun a : FiniteWeightedBoundaryPlan sourceWeight targetWeight =>
    a.mass 0 0) h
  rw [proportional_entry] at heq
  norm_num [concentratedPlan] at heq

private theorem zero_label_gets_zero (j : Fin 2) : recoveredPlan.mass 2 j = 0 := by
  simp [recoveredPlan, FiniteWeightedBoundaryPlan.splitLift_mass,
    FiniteWeightedDiagram.splittingKernel, sourceWeight]

private theorem repeated_unit_powered_cost :
    FiniteWeightedDiagram.powerBoundaryTransportCost 2
      (FiniteWeightedDiagram.ofIndexed (fun _ : Fin 2 => 1) (fun _ => sourcePoint)) 0 = 8 := by
  rw [FiniteWeightedDiagram.powerBoundaryTransportCost_zero_right]
  have h := FiniteWeightedDiagram.ofIndexed_weighted_sum
    (fun _ : Fin 2 => 1) (fun _ => sourcePoint)
    (fun q => (diagonalCost q.1).toReal ^ (2 : ℝ))
  exact h.trans (by norm_num [sourcePoint, diagonalCost, Fin.sum_univ_two])

private theorem recovered_rooted_optimizer :
    recoveredPlan.powerCost 2 (fun i => (sourceCoordinates i).1)
      (fun j => (targetCoordinates j).1) ^ (2 : ℝ)⁻¹ =
      weightedPBoundaryTransportCost 2 sourceWeight targetWeight
        (fun i => (sourceCoordinates i).1) (fun j => (targetCoordinates j).1) :=
  FiniteWeightedDiagram.splitLift_minimizing_pPlan 2 sourceWeight targetWeight
    sourceCoordinates targetCoordinates aggregatePlan
    (congrArg (fun t : ℝ => t ^ (2 : ℝ)⁻¹) aggregate_optimizer)

private theorem borel_powered_value :
    boundaryTransportPowerValue 2 (atomicMeasure sourceDiagram)
      (atomicMeasure targetDiagram) = 5 := by
  rw [boundaryTransportPowerValue_ofIndexed 2 (by norm_num), indexed_powered_optimum]
  norm_num

private theorem borel_rooted_value :
    boundaryTransportDistance 2 (atomicMeasure sourceDiagram)
      (atomicMeasure targetDiagram) = ENNReal.ofReal ((5 : ℝ) ^ (2 : ℝ)⁻¹) := by
  rw [boundaryTransportDistance_ofIndexed 2 (by norm_num),
    weightedPBoundaryTransportCost, indexed_powered_optimum]

private theorem indexed_optimizer_constructs_borel :
    IsBoundaryPlan (atomicBoundaryPlan sourceDiagram targetDiagram aggregatePlan)
      (atomicMeasure sourceDiagram) (atomicMeasure targetDiagram) ∧
      (∫⁻ z, planPowerCost 2 z ∂atomicBoundaryPlan sourceDiagram targetDiagram aggregatePlan) =
        5 := by
  have h := atomicBoundaryPlan_ofIndexed_minimizing 2 (by norm_num)
    sourceWeight targetWeight sourceCoordinates targetCoordinates concentratedPlan
    (concentrated_powered_cost.trans indexed_powered_optimum.symm)
  exact ⟨h.1, h.2.trans borel_powered_value⟩

private theorem empty_indexed_diagram :
    FiniteWeightedDiagram.ofIndexed (fun _ : PEmpty.{1} => 1)
      (fun i => PEmpty.elim i) = 0 := by
  simp [FiniteWeightedDiagram.ofIndexed]

private theorem zero_weight_indexed_diagram :
    FiniteWeightedDiagram.ofIndexed (fun _ : Fin 3 => 0) sourceCoordinates = 0 := by
  simp [FiniteWeightedDiagram.ofIndexed]

private theorem repeated_unit_borel_matching_value :
    boundaryTransportPowerValue 2
      (atomicMeasure (FiniteWeightedDiagram.ofIndexed (fun _ : Fin 2 => 1)
        (fun _ => sourcePoint)))
      (atomicMeasure (FiniteWeightedDiagram.ofIndexed (fun _ : PEmpty.{1} => 1)
        (fun i => PEmpty.elim i))) = 8 := by
  rw [boundaryTransportPowerValue_ofIndexed_unit 2 (by norm_num),
    finitePowerMatchingCost_of_isEmpty_right]
  norm_num [sourcePoint, diagonalCost, Fin.sum_univ_two]

end TDA.Persistence.FiniteWeightedCoalescingExamples
