import TDA.Persistence.FiniteWeightedBoundaryTransport

/-!
# Fractional masses and optimized boundary costs

The examples quantify over all feasible plans where an optimum is asserted.
They distinguish real mass splitting from unit-occurrence matching, allow zero
and empty inputs, and instantiate the positive weighted-diagram interface.
-/

noncomputable section

namespace TDA.Persistence.FiniteWeightedBoundaryTransportExamples

open scoped Classical NNReal

/- Unequal fractional masses: every feasible plan is a scalar in [0, 1/2]. -/

private def sourceMass (_ : Unit) : ℝ≥0 := 3 / 2
private def targetMass (_ : Unit) : ℝ≥0 := 1 / 2
private def sourcePoint (_ : Unit) : ℝ × ℝ := (0, 2)
private def targetPoint (_ : Unit) : ℝ × ℝ := (3 / 2, 7 / 2)

private abbrev ScalarPlan := FiniteWeightedBoundaryPlan sourceMass targetMass

private def scalarPlan (t : ℝ) (h0 : 0 ≤ t) (hhalf : t ≤ 1 / 2) : ScalarPlan where
  mass _ _ := t
  nonneg _ _ := h0
  row_le _ := by norm_num [sourceMass]; linarith
  col_le _ := by simpa [targetMass] using hhalf

private def halfPlan : ScalarPlan := scalarPlan (1 / 2) (by norm_num) le_rfl
private def boundaryPlan : ScalarPlan := scalarPlan 0 le_rfl (by norm_num)

private theorem scalar_le_half (a : ScalarPlan) : a.mass () () ≤ 1 / 2 := by
  simpa [targetMass] using a.col_le ()

private theorem scalar_objective (a : ScalarPlan) (p : ℝ) :
    a.powerCost p sourcePoint targetPoint =
      2 + a.mass () () * ((3 / 2 : ℝ) ^ p - 2) := by
  norm_num [FiniteWeightedBoundaryPlan.powerCost, FiniteWeightedBoundaryPlan.linearCost,
    weightedBoundaryLinearObjective, sourceMass, targetMass, sourcePoint, targetPoint,
    finitePairCost, diagonalCost]
  ring

private theorem fractional_power_optimum_one :
    weightedPowerBoundaryTransportCost 1 sourceMass targetMass sourcePoint targetPoint = 7 / 4 := by
  apply le_antisymm
  · exact (weightedPowerBoundaryTransportCost_le_plan 1 _ _ _ _ halfPlan).trans_eq (by
      norm_num [scalar_objective, halfPlan, scalarPlan])
  · apply le_ciInf
    intro a
    rw [scalar_objective]
    norm_num
    have h := scalar_le_half a
    linarith

private theorem fractional_plan_and_residuals :
    halfPlan.mass () () = 1 / 2 ∧ halfPlan.deletionMass () = 1 ∧
      halfPlan.insertionMass () = 0 ∧
      halfPlan.powerCost 1 sourcePoint targetPoint =
        weightedPowerBoundaryTransportCost 1 sourceMass targetMass sourcePoint targetPoint := by
  norm_num [halfPlan, scalarPlan, FiniteWeightedBoundaryPlan.deletionMass,
    FiniteWeightedBoundaryPlan.insertionMass, sourceMass, targetMass,
    scalar_objective, fractional_power_optimum_one]

/- The minimizing plan changes with the exponent. -/

private theorem fractional_power_optimum_two :
    weightedPowerBoundaryTransportCost 2 sourceMass targetMass sourcePoint targetPoint = 2 := by
  apply le_antisymm
  · exact (weightedPowerBoundaryTransportCost_le_plan 2 _ _ _ _ boundaryPlan).trans_eq (by
      norm_num [scalar_objective, boundaryPlan, scalarPlan])
  · apply le_ciInf
    intro a
    rw [scalar_objective]
    norm_num
    have h := a.nonneg () ()
    linarith

private theorem first_order_optimizer_rejected_at_two :
    halfPlan.powerCost 1 sourcePoint targetPoint =
        weightedPowerBoundaryTransportCost 1 sourceMass targetMass sourcePoint targetPoint ∧
      halfPlan.powerCost 2 sourcePoint targetPoint = 17 / 8 ∧
      weightedPowerBoundaryTransportCost 2 sourceMass targetMass sourcePoint targetPoint <
        halfPlan.powerCost 2 sourcePoint targetPoint := by
  norm_num [scalar_objective, halfPlan, scalarPlan,
    fractional_power_optimum_one, fractional_power_optimum_two]

private theorem fractional_rooted_optima :
    weightedPBoundaryTransportCost 1 sourceMass targetMass sourcePoint targetPoint = 7 / 4 ∧
      weightedPBoundaryTransportCost 2 sourceMass targetMass sourcePoint targetPoint =
        (2 : ℝ) ^ (1 / 2 : ℝ) := by
  norm_num [weightedPBoundaryTransportCost, fractional_power_optimum_one,
    fractional_power_optimum_two]

/- A single source really splits to two distinct target points. -/

private def splitSource (_ : Unit) : ℝ≥0 := 1
private def splitTarget (_ : Bool) : ℝ≥0 := 1 / 2
private def splitPlan : FiniteWeightedBoundaryPlan splitSource splitTarget where
  mass _ _ := 1 / 2
  nonneg _ _ := by norm_num
  row_le _ := by norm_num [splitSource, Fintype.sum_bool]
  col_le _ := by norm_num [splitTarget]

private def splitSourcePoint (_ : Unit) : ℝ × ℝ := (0, 4)
private def splitTargetPoint : Bool → ℝ × ℝ
  | false => (0, 4)
  | true => (1, 5)

private theorem split_balances_and_cost :
    splitTargetPoint false ≠ splitTargetPoint true ∧
      splitPlan.mass () false = 1 / 2 ∧ splitPlan.mass () true = 1 / 2 ∧
      splitPlan.deletionMass () = 0 ∧
      (∀ b, splitPlan.insertionMass b = 0) ∧
      splitPlan.powerCost 1 splitSourcePoint splitTargetPoint = 1 / 2 ∧
      weightedPowerBoundaryTransportCost 1 splitSource splitTarget
        splitSourcePoint splitTargetPoint ≤ 1 / 2 := by
  have hc : splitPlan.powerCost 1 splitSourcePoint splitTargetPoint = 1 / 2 := by
    norm_num [splitPlan, FiniteWeightedBoundaryPlan.powerCost,
      FiniteWeightedBoundaryPlan.linearCost, weightedBoundaryLinearObjective,
      splitSource, splitTarget, splitSourcePoint, splitTargetPoint,
      Fintype.sum_bool, finitePairCost, diagonalCost]
  refine ⟨by norm_num [splitTargetPoint], rfl, rfl, ?_, ?_, hc, ?_⟩
  · norm_num [FiniteWeightedBoundaryPlan.deletionMass, splitPlan, splitSource, Fintype.sum_bool]
  · intro b
    norm_num [FiniteWeightedBoundaryPlan.insertionMass, splitPlan, splitTarget]
  · exact (weightedPowerBoundaryTransportCost_le_plan 1 _ _ _ _ splitPlan).trans_eq hc

private theorem split_entries_are_not_incidence :
    ¬ (splitPlan.mass () false = 0 ∨ splitPlan.mass () false = 1) := by
  norm_num [splitPlan]

/- Zero labels contribute nothing, and either side may be empty. -/

private theorem zero_mass_nonempty_labels (p : ℝ) (x : Bool → ℝ × ℝ) (y : Fin 3 → ℝ × ℝ) :
    weightedPowerBoundaryTransportCost p (fun _ => 0) (fun _ => 0) x y = 0 :=
  weightedPowerBoundaryTransportCost_zero p x y

private def ghostMass : Bool → ℝ≥0 | false => 0 | true => 3 / 2
private def ghostPoints (z : ℝ × ℝ) : Bool → ℝ × ℝ | false => z | true => (0, 2)

private theorem empty_target_ignores_zero_label (p : ℝ) (z : ℝ × ℝ) :
    weightedPowerBoundaryTransportCost p ghostMass (fun _ : PEmpty.{1} => 0)
      (ghostPoints z) (fun a => PEmpty.elim a) = 3 / 2 := by
  rw [weightedPowerBoundaryTransportCost_of_isEmpty_right]
  norm_num [Fintype.sum_bool, ghostMass, ghostPoints, diagonalCost]

private theorem empty_source_ignores_zero_label (p : ℝ) (z : ℝ × ℝ) :
    weightedPowerBoundaryTransportCost p (fun _ : PEmpty.{1} => 0) ghostMass
      (fun a => PEmpty.elim a) (ghostPoints z) = 3 / 2 := by
  rw [weightedPowerBoundaryTransportCost_symm]
  exact empty_target_ignores_zero_label p z

private theorem both_empty_rooted {p : ℝ} (hp : 1 ≤ p) :
    weightedPBoundaryTransportCost p (fun _ : PEmpty.{1} => 0) (fun _ : PEmpty.{1} => 0)
      (fun a => PEmpty.elim a) (fun a => PEmpty.elim a) = 0 :=
  weightedPBoundaryTransportCost_zero hp _ _

/- Unit weights keep two repeated occurrences, rather than coalescing them to one. -/

private def repeatedPoints (_ : Fin 2) : ℝ × ℝ := (0, 2)

private theorem repeated_unit_occurrences :
    weightedPowerBoundaryTransportCost 1 (fun _ : Fin 2 => 1) (fun _ : PEmpty.{1} => 1)
      repeatedPoints (fun a => PEmpty.elim a) = 2 ∧
      weightedPowerBoundaryTransportCost 1 (fun _ : Fin 2 => 1) (fun _ : PEmpty.{1} => 1)
        repeatedPoints (fun a => PEmpty.elim a) =
        finitePowerBoundaryTransportCost 1 repeatedPoints (fun a : PEmpty.{1} => PEmpty.elim a) := by
  refine ⟨?_, weightedPowerBoundaryTransportCost_unit 1 _ _⟩
  rw [weightedPowerBoundaryTransportCost_of_isEmpty_right]
  norm_num [repeatedPoints, diagonalCost, Fin.sum_univ_two]

/- positive weighted diagrams use the finite support of their atom masses. -/

private def positivePoint : {z : ℝ × ℝ // z.1 < z.2} := ⟨(0, 2), by norm_num⟩
private def fractionalDiagram : FiniteWeightedDiagram := Finsupp.single positivePoint (1 / 2)

private theorem weighted_diagram_moment :
    FiniteWeightedDiagram.powerBoundaryTransportCost 1 fractionalDiagram 0 = 1 / 2 := by
  rw [FiniteWeightedDiagram.powerBoundaryTransportCost_zero_right]
  change (∑ i : ↥fractionalDiagram.support,
    (fractionalDiagram i.1 : ℝ) * (diagonalCost i.1.1).toReal ^ (1 : ℝ)) = 1 / 2
  calc
    _ = ∑ z ∈ fractionalDiagram.support,
        (fractionalDiagram z : ℝ) * (diagonalCost z.1).toReal ^ (1 : ℝ) :=
      Finset.sum_coe_sort fractionalDiagram.support _
    _ = _ := by norm_num [fractionalDiagram, positivePoint, diagonalCost]

private theorem weighted_diagram_optimizer :
    ∃ a : FiniteWeightedBoundaryPlan fractionalDiagram.weights
        (0 : FiniteWeightedDiagram).weights,
      a.powerCost 1 fractionalDiagram.coordinates (0 : FiniteWeightedDiagram).coordinates = 1 / 2 := by
  obtain ⟨a, ha⟩ := FiniteWeightedDiagram.exists_minimizing_powerPlan 1 fractionalDiagram 0
  exact ⟨a, ha.trans weighted_diagram_moment⟩

private theorem weighted_zero_diagram {p : ℝ} (hp : 1 ≤ p) :
    FiniteWeightedDiagram.pBoundaryTransportCost p 0 0 = 0 :=
  FiniteWeightedDiagram.pBoundaryTransportCost_zero hp

end TDA.Persistence.FiniteWeightedBoundaryTransportExamples
