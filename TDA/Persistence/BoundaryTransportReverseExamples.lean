import TDA.Persistence.BoundaryTransportReverseCore
import TDA.Persistence.BoundaryTransportGeometryExamples

/-!
# Far-atom examples for the reverse boundary plan

The fixed distant pair illustrates direct cost, split cost and the capacity-two reduction.
-/

set_option autoImplicit false
noncomputable section
namespace TDA.Persistence.BoundaryTransport.Reverse
open Set MeasureTheory
open scoped ENNReal

def farSource : Interior := ⟨(0, 2), by norm_num⟩
def farTarget : Interior := ⟨(10, 12), by norm_num⟩

/-- A distant interior pair is actually split: its squared leg cost is two. -/
theorem far_shortcut_reverse_cost :
    (∫⁻ z, planPowerCost 2 z ∂boundaryPlan
      (Measure.dirac (Space.point farSource, Space.point farTarget))) = 2 := by
  rw [boundaryPlan_dirac_points_cost]
  norm_num [farSource, farTarget, depth_eq, Subtype.dist_eq, Prod.dist_eq, Real.dist_eq]

/-- The same collapsed-space competitor pays four, so this comparison is strict. -/
theorem far_shortcut_original_cost :
    (∫⁻ z : Space × Space, ENNReal.ofReal (dist z.1 z.2 ^ (2 : ℝ))
      ∂Measure.dirac (Space.point farSource, Space.point farTarget)) = 4 := by
  rw [lintegral_dirac]
  change ENNReal.ofReal (dist (Space.point farSource) (Space.point farTarget) ^ (2 : ℝ)) = 4
  rw [show dist (Space.point farSource) (Space.point farTarget) = 2 from far_points_shortcut]
  norm_num

/-- The actual capacity-two reservoir competitor exhibits the strict four-to-two reduction. -/
theorem far_reservoir_cost_reduction :
    (∫⁻ z, planPowerCost 2 z ∂boundaryPlan (singlePairReservoirCompetitor farSource farTarget)) = 2 ∧
    (∫⁻ z : Space × Space, ENNReal.ofReal (dist z.1 z.2 ^ (2 : ℝ))
      ∂singlePairReservoirCompetitor farSource farTarget) = 4 := by
  constructor
  · rw [singlePairReservoirCompetitor, boundaryPlan_add, lintegral_add_measure,
      boundaryPlan_boundaryAtom]
    simp only [lintegral_zero_measure, add_zero]
    exact far_shortcut_reverse_cost
  · rw [singlePairReservoirCompetitor, lintegral_add_measure,
      far_shortcut_original_cost, lintegral_dirac]
    norm_num

end TDA.Persistence.BoundaryTransport.Reverse
