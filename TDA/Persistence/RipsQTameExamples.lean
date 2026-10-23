import TDA.Persistence.RipsQTame
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Order.Interval.Set.Infinite

/-!
# An infinite compact Rips example

The closed unit interval has q-tame Rips homology in every degree. Its unreduced
degree-zero fiber at time zero is infinite-dimensional. Thus q-tameness controls
strict structure maps without asserting finite-dimensional fibers.
-/

namespace TDA.Persistence.RipsQTameExamples

open Set TDA.Filtration

abbrev UnitInterval := Icc (0 : ℝ) 1

/-- The empty metric space is covered without an inhabitedness assumption. -/
theorem empty_qTame (k : Type*) [Field k] (n : ℕ) :
    (sublevelModule k (Rips.filter (inferInstance : MetricSpace (∅ : Set ℝ))) n).QTame := by
  apply Rips.qTame_of_totallyBounded
  apply Metric.totallyBounded_iff.mpr
  intro ε _
  exact ⟨∅, Set.finite_empty, fun x _ => False.elim x.property⟩

/-- All strict structure maps of the infinite compact interval have finite-dimensional images. -/
theorem unitInterval_qTame (k : Type*) [Field k] (n : ℕ) :
    (sublevelModule k (Rips.filter (inferInstance : MetricSpace UnitInterval)) n).QTame :=
  Rips.qTame_of_totallyBounded k isCompact_univ.totallyBounded n

/-- The same module has an infinite-dimensional degree-zero fiber at time zero. -/
theorem unitInterval_zero_not_finiteDimensional (k : Type*) [Field k] :
    ¬ FiniteDimensional k
      ((sublevelModule k (Rips.filter (inferInstance : MetricSpace UnitInterval)) 0).obj 0) := by
  let : Infinite UnitInterval := Set.Icc.infinite (by norm_num : (0 : ℝ) < 1)
  exact Rips.not_finiteDimensional_zero_homology k

end TDA.Persistence.RipsQTameExamples
