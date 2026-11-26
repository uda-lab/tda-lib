import TDA.Persistence.Reduction.RipsInputBottleneck
import TDA.Persistence.Reduction.RipsInputDiagramExamples

/-!
# Client computations of bottleneck distances between Rips diagrams

Regression fixtures for #1268, family 7 of the downstream-use audit (#1207). The tables are
those of `TDA.Persistence.Reduction.RipsInputExamples`. Each statement runs the certified
reduction on two distance tables and the integer search on the two record lists, and reads
the bottleneck distance between the F₂ Rips diagrams of the two table metrics. The file opens
no scope and declares no instance.

* One point against two points at distance `3`, degree zero: distance `3 / 2`, the cost of
  deleting the bar `[0, 3)`.
* The two-point table against itself, degree zero: distance `0`.
* The empty table against one point, degree zero: infinite distance, since the numbers of
  essential classes differ.
-/

namespace TDA.Persistence.Reduction.RipsInputBottleneckExamples

/-- One point and two points at distance `3` have degree-zero Rips diagrams at bottleneck
distance `3 / 2`. -/
theorem single_pair_bottleneck :
    TDA.Persistence.bottleneck
        (TDA.Persistence.dgm (ZMod 2)
          (TDA.Filtration.Rips.filter
            (TDA.Persistence.Reduction.RipsInputExamples.single.metric
              TDA.Persistence.Reduction.RipsInputDiagramExamples.single_valid)) 0)
        (TDA.Persistence.dgm (ZMod 2)
          (TDA.Filtration.Rips.filter
            (TDA.Persistence.Reduction.RipsInputExamples.pair.metric
              TDA.Persistence.Reduction.RipsInputExamples.pair_valid)) 0) =
      (3 : ENNReal) / 2 := by
  obtain ⟨_, _, h⟩ :=
    TDA.Persistence.Reduction.DistanceTable.bottleneck_rips_dgm_eq_of_twiceDistance
      TDA.Persistence.Reduction.RipsInputExamples.single
      TDA.Persistence.Reduction.RipsInputExamples.pair
      TDA.Persistence.Reduction.RipsInputDiagramExamples.single_ripsRunInDegree_zero
      TDA.Persistence.Reduction.RipsInputDiagramExamples.pair_ripsRunInDegree_zero 3
      (by decide)
  simpa only [Nat.cast_ofNat] using h

/-- A table is at distance zero from itself. -/
theorem pair_pair_bottleneck :
    TDA.Persistence.bottleneck
        (TDA.Persistence.dgm (ZMod 2)
          (TDA.Filtration.Rips.filter
            (TDA.Persistence.Reduction.RipsInputExamples.pair.metric
              TDA.Persistence.Reduction.RipsInputExamples.pair_valid)) 0)
        (TDA.Persistence.dgm (ZMod 2)
          (TDA.Filtration.Rips.filter
            (TDA.Persistence.Reduction.RipsInputExamples.pair.metric
              TDA.Persistence.Reduction.RipsInputExamples.pair_valid)) 0) = 0 := by
  obtain ⟨_, _, h⟩ :=
    TDA.Persistence.Reduction.DistanceTable.bottleneck_rips_dgm_eq_of_twiceDistance
      TDA.Persistence.Reduction.RipsInputExamples.pair
      TDA.Persistence.Reduction.RipsInputExamples.pair
      TDA.Persistence.Reduction.RipsInputDiagramExamples.pair_ripsRunInDegree_zero
      TDA.Persistence.Reduction.RipsInputDiagramExamples.pair_ripsRunInDegree_zero 0
      (by decide)
  simpa using h

/-- The empty table and one point are at infinite distance in degree zero. -/
theorem empty_single_bottleneck :
    TDA.Persistence.bottleneck
        (TDA.Persistence.dgm (ZMod 2)
          (TDA.Filtration.Rips.filter
            (TDA.Persistence.Reduction.RipsInputExamples.empty.metric
              TDA.Persistence.Reduction.RipsInputDiagramExamples.empty_valid)) 0)
        (TDA.Persistence.dgm (ZMod 2)
          (TDA.Filtration.Rips.filter
            (TDA.Persistence.Reduction.RipsInputExamples.single.metric
              TDA.Persistence.Reduction.RipsInputDiagramExamples.single_valid)) 0) = ⊤ := by
  obtain ⟨_, _, h⟩ :=
    TDA.Persistence.Reduction.DistanceTable.bottleneck_rips_dgm_eq_top_of_twiceDistance
      TDA.Persistence.Reduction.RipsInputExamples.empty
      TDA.Persistence.Reduction.RipsInputExamples.single
      (TDA.Persistence.Reduction.RipsInputDiagramExamples.empty_ripsRunInDegree 0)
      TDA.Persistence.Reduction.RipsInputDiagramExamples.single_ripsRunInDegree_zero
      (by decide)
  exact h

end TDA.Persistence.Reduction.RipsInputBottleneckExamples
