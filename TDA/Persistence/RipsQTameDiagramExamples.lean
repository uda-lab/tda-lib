import TDA.Persistence.RipsQTameDiagram
import TDA.Persistence.RipsQTameExamples

/-! An infinite compact Rips space with locally finite diagram and an infinite fiber. -/

namespace TDA.Persistence.RipsQTameDiagramExamples

open Set TDA.Filtration

/-- The compact unit interval's closed Rips `H₀` has an infinite-dimensional
zero fiber, while its extracted finite and essential occurrences are countable
and finite in every separated tail rectangle. -/
theorem unitInterval_infinite_fiber_with_diagram (k : Type*) [Field k] :
    ¬ FiniteDimensional k
        ((sublevelModule k (Rips.filter
          (inferInstance : MetricSpace RipsQTameExamples.UnitInterval)) 0).obj 0) ∧
      Set.Countable {p | 0 < Rips.qTameDiagramMultiplicity k
        (X := RipsQTameExamples.UnitInterval) isCompact_univ.totallyBounded 0 p} ∧
      Set.Finite {p | p ∈ RectangleMeasure.tailRectangleCell (-1) 0 1 ∧
        0 < Rips.qTameDiagramMultiplicity k
          (X := RipsQTameExamples.UnitInterval) isCompact_univ.totallyBounded 0 p} := by
  refine ⟨RipsQTameExamples.unitInterval_zero_not_finiteDimensional k,
    Rips.qTameDiagramMultiplicity_countable_support k isCompact_univ.totallyBounded 0, ?_⟩
  exact Rips.qTameDiagramMultiplicity_tail_locally_finite k
    isCompact_univ.totallyBounded 0 (-1) 0 1 (by norm_num) (by norm_num)

end TDA.Persistence.RipsQTameDiagramExamples
