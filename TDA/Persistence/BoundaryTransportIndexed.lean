import TDA.Persistence.FiniteWeightedCoalescing
import TDA.Persistence.BoundaryTransportAtomic

/-!
# Boundary transport of indexed atomic inputs

The native atomic measure coalesces repeated coordinates. Every indexed finite
matrix and every native finite matrix transfer with the same full powered cost.
The all-Borel value then follows from the native atomic theorem.
-/

set_option autoImplicit false
noncomputable section
namespace TDA.Persistence.BoundaryTransport
open scoped Classical NNReal ENNReal

universe u v
variable {I : Type u} {J : Type v} [Fintype I] [Fintype J]

/-- The atomic measure of a finite indexed family is its occurrence sum. -/
theorem atomicMeasure_ofIndexed (w : I → ℝ≥0) (x : I → Interior) :
    atomicMeasure (FiniteWeightedDiagram.ofIndexed w x) =
      ∑ i, (w i : ℝ≥0∞) • MeasureTheory.Measure.dirac (x i) := by
  apply MeasureTheory.Measure.ext
  intro s hs
  rw [atomicMeasure_apply _ s hs]
  simp only [MeasureTheory.Measure.finsetSum_apply]
  simp only [MeasureTheory.Measure.smul_apply, MeasureTheory.Measure.dirac_apply]
  simpa [Set.indicator, smul_eq_mul] using
    (FiniteWeightedDiagram.ofIndexed_weighted_sum_ennreal w x
      (fun q => if q ∈ s then 1 else 0))

/-- Every all-Borel boundary competitor has the same optimized powered value as the
indexed finite matrix problem. The all-Borel comparison uses `p ≥ 0`. -/
theorem boundaryTransportPowerValue_ofIndexed (p : ℝ) (hp : 0 ≤ p)
    (w : I → ℝ≥0) (v : J → ℝ≥0)
    (x : I → Interior) (y : J → Interior) :
    boundaryTransportPowerValue p
      (atomicMeasure (FiniteWeightedDiagram.ofIndexed w x))
      (atomicMeasure (FiniteWeightedDiagram.ofIndexed v y)) =
      ENNReal.ofReal (weightedPowerBoundaryTransportCost p w v
        (fun i => (x i).1) (fun j => (y j).1)) := by
  rw [boundaryTransportPowerValue_atomic_eq_native p hp]
  rw [FiniteWeightedDiagram.weightedPowerBoundaryTransportCost_ofIndexed]

/-- The all-Borel rooted atomic distance recovers the indexed weighted root for `p ≥ 1`. -/
theorem boundaryTransportDistance_ofIndexed (p : ℝ) (hp : 1 ≤ p)
    (w : I → ℝ≥0) (v : J → ℝ≥0)
    (x : I → Interior) (y : J → Interior) :
    boundaryTransportDistance p
      (atomicMeasure (FiniteWeightedDiagram.ofIndexed w x))
      (atomicMeasure (FiniteWeightedDiagram.ofIndexed v y)) =
      ENNReal.ofReal (weightedPBoundaryTransportCost p w v
        (fun i => (x i).1) (fun j => (y j).1)) := by
  rw [boundaryTransportDistance_atomic_eq_native p hp]
  rw [FiniteWeightedDiagram.weightedPBoundaryTransportCost_ofIndexed]

/-- An indexed optimizer constructs an actual minimizing Borel boundary plan. -/
theorem atomicBoundaryPlan_ofIndexed_minimizing (p : ℝ) (hp : 0 ≤ p)
    (w : I → ℝ≥0) (v : J → ℝ≥0)
    (x : I → Interior) (y : J → Interior)
    (a : FiniteWeightedBoundaryPlan w v)
    (ha : a.powerCost p (fun i => (x i).1) (fun j => (y j).1) =
      weightedPowerBoundaryTransportCost p w v (fun i => (x i).1)
        (fun j => (y j).1)) :
    IsBoundaryPlan
      (atomicBoundaryPlan (FiniteWeightedDiagram.ofIndexed w x)
        (FiniteWeightedDiagram.ofIndexed v y) (a.aggregate x y))
      (atomicMeasure (FiniteWeightedDiagram.ofIndexed w x))
      (atomicMeasure (FiniteWeightedDiagram.ofIndexed v y)) ∧
    (∫⁻ z, planPowerCost p z ∂atomicBoundaryPlan
      (FiniteWeightedDiagram.ofIndexed w x) (FiniteWeightedDiagram.ofIndexed v y)
      (a.aggregate x y)) =
      boundaryTransportPowerValue p
        (atomicMeasure (FiniteWeightedDiagram.ofIndexed w x))
        (atomicMeasure (FiniteWeightedDiagram.ofIndexed v y)) := by
  constructor
  · exact atomicBoundaryPlan_admissible _ _ _
  · rw [atomicBoundaryPlan_cost_native,
      FiniteWeightedDiagram.aggregate_minimizing_powerPlan p w v x y a ha,
      boundaryTransportPowerValue_atomic_eq_native p hp]

/-- A minimizing Borel plan exists for indexed finite data, with no optimizer premise. -/
theorem exists_minimizing_boundaryPlan_ofIndexed (p : ℝ) (hp : 0 ≤ p)
    (w : I → ℝ≥0) (v : J → ℝ≥0)
    (x : I → Interior) (y : J → Interior) :
    ∃ π : MeasureTheory.Measure PlanSpace,
      IsBoundaryPlan π (atomicMeasure (FiniteWeightedDiagram.ofIndexed w x))
        (atomicMeasure (FiniteWeightedDiagram.ofIndexed v y)) ∧
      (∫⁻ z, planPowerCost p z ∂π) =
        boundaryTransportPowerValue p
          (atomicMeasure (FiniteWeightedDiagram.ofIndexed w x))
          (atomicMeasure (FiniteWeightedDiagram.ofIndexed v y)) := by
  obtain ⟨a, ha, _⟩ := FiniteWeightedDiagram.exists_indexed_coalesced_minimizing_powerPlans
    p w v x y
  exact ⟨_, atomicBoundaryPlan_ofIndexed_minimizing p hp w v x y a ha⟩

/-- Unit occurrences recover the existing powered finite assignment quantity. -/
theorem boundaryTransportPowerValue_ofIndexed_unit (p : ℝ) (hp : 0 ≤ p)
    (x : I → Interior) (y : J → Interior) :
    boundaryTransportPowerValue p
      (atomicMeasure (FiniteWeightedDiagram.ofIndexed (fun _ : I => 1) x))
      (atomicMeasure (FiniteWeightedDiagram.ofIndexed (fun _ : J => 1) y)) =
      ENNReal.ofReal (finitePowerMatchingCost p
        (fun i => (x i).1) (fun j => (y j).1)) := by
  rw [boundaryTransportPowerValue_ofIndexed p hp,
    weightedPowerBoundaryTransportCost_unit,
    finitePowerBoundaryTransportCost_eq_matchingCost]

/-- Unit occurrences recover the existing rooted finite assignment quantity. -/
theorem boundaryTransportDistance_ofIndexed_unit (p : ℝ) (hp : 1 ≤ p)
    (x : I → Interior) (y : J → Interior) :
    boundaryTransportDistance p
      (atomicMeasure (FiniteWeightedDiagram.ofIndexed (fun _ : I => 1) x))
      (atomicMeasure (FiniteWeightedDiagram.ofIndexed (fun _ : J => 1) y)) =
      ENNReal.ofReal (finitePMatchingCost p
        (fun i => (x i).1) (fun j => (y j).1)) := by
  rw [boundaryTransportDistance_ofIndexed p hp,
    weightedPBoundaryTransportCost_unit,
    finitePBoundaryTransportCost_eq_matchingCost]

end TDA.Persistence.BoundaryTransport
