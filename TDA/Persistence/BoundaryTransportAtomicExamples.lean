import TDA.Persistence.BoundaryTransportAtomic

/-!
# Atomic boundary transport consumers

Fractional mass stays linear when the geometric distance is squared. Summing
coincident atoms combines their masses, and zero inputs retain zero value.
-/

noncomputable section
set_option autoImplicit false

namespace TDA.Persistence.BoundaryTransport.AtomicExamples

open MeasureTheory
open scoped ENNReal NNReal Classical

private def point : Interior := ⟨(0, 2), by norm_num⟩
private def halfDiagram : FiniteWeightedDiagram := Finsupp.single point (1 / 2)

private theorem single_power_zero (p : ℝ) (w : ℝ≥0) :
    FiniteWeightedDiagram.powerBoundaryTransportCost p (Finsupp.single point w) 0 = w := by
  rw [FiniteWeightedDiagram.powerBoundaryTransportCost_zero_right]
  change (∑ i : ↥(Finsupp.single point w).support,
    ((Finsupp.single point w) i.1 : ℝ) * (diagonalCost i.1.1).toReal ^ p) = w
  calc
    _ = ∑ z ∈ (Finsupp.single point w).support,
        ((Finsupp.single point w) z : ℝ) * (diagonalCost z.1).toReal ^ p :=
      Finset.sum_coe_sort (Finsupp.single point w).support _
    _ = _ := by
      by_cases hw : w = 0
      · simp [hw]
      · rw [Finsupp.support_single point hw, Finset.sum_singleton, Finsupp.single_eq_same]
        norm_num [point, diagonalCost]

private theorem fractional_powered_cost :
    boundaryTransportPowerValue 2 (atomicMeasure halfDiagram) (atomicMeasure 0) = 1 / 2 := by
  rw [boundaryTransportPowerValue_atomic_eq_native 2 (by norm_num)]
  norm_num [halfDiagram, single_power_zero, ENNReal.ofReal_div_of_pos]

private theorem fractional_rooted_cost :
    boundaryTransportDistance 1 (atomicMeasure halfDiagram) (atomicMeasure 0) = 1 / 2 := by
  rw [boundaryTransportDistance_atomic_eq_native 1 (by norm_num)]
  change ENNReal.ofReal
    ((FiniteWeightedDiagram.powerBoundaryTransportCost 1 halfDiagram 0) ^ (1 : ℝ)⁻¹) = 1 / 2
  norm_num [halfDiagram, single_power_zero, ENNReal.ofReal_div_of_pos]

private theorem coincident_half_masses :
    atomicMeasure (halfDiagram + halfDiagram) {point} = 1 := by
  rw [atomicMeasure_singleton]
  norm_num [halfDiagram]

private theorem coalesced_powered_cost :
    boundaryTransportPowerValue 2 (atomicMeasure (halfDiagram + halfDiagram))
      (atomicMeasure 0) = 1 := by
  have hsum : halfDiagram + halfDiagram = Finsupp.single point 1 := by
    unfold halfDiagram
    rw [← Finsupp.single_add, show (1 / 2 : ℝ≥0) + 1 / 2 = 1 by norm_num]
  rw [hsum, boundaryTransportPowerValue_atomic_eq_native 2 (by norm_num)]
  norm_num [single_power_zero]

private theorem zero_powered_cost (p : ℝ) (hp : 0 ≤ p) :
    boundaryTransportPowerValue p (atomicMeasure 0) (atomicMeasure 0) = 0 := by
  rw [boundaryTransportPowerValue_atomic_eq_native p hp]
  simp [FiniteWeightedDiagram.powerBoundaryTransportCost_zero]

private theorem fractional_minimizer :
    ∃ π : Measure PlanSpace,
      IsBoundaryPlan π (atomicMeasure halfDiagram) (atomicMeasure 0) ∧
      (∫⁻ z, planPowerCost 2 z ∂π) = 1 / 2 := by
  obtain ⟨π, hπ, hcost⟩ := exists_atomic_minimizing_boundaryPlan 2 (by norm_num) halfDiagram 0
  exact ⟨π, hπ, hcost.trans fractional_powered_cost⟩

end TDA.Persistence.BoundaryTransport.AtomicExamples
