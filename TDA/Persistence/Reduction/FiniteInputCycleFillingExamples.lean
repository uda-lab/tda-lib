import TDA.Persistence.Reduction.FiniteInputCycleFillingCorrectness
import TDA.Persistence.Reduction.FiniteInputExamples

/-! Executed fillings and consumers of their actual signed simplicial boundary. -/

set_option maxRecDepth 10000
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 512
set_option backward.defeqAttrib.useBackward true

namespace TDA.Persistence.Reduction.FiniteInput.FillingExamples

open TDA.Simplicial TDA.Filtration

private local instance : NeZero Examples.filled.length := ⟨by decide⟩
private local instance : NeZero Examples.hollow.length := ⟨by decide⟩
private local instance : NeZero Examples.tied.length := ⟨by decide⟩
private local instance : NeZero Examples.negative.length := ⟨by decide⟩
private local instance : NeZero Examples.delayed.length := ⟨by decide⟩

/-- The three supplied triangle edges are filled by the original triangle face. -/
theorem filled_execution :
    runCycleFilling Examples.filled 1 2 (chainVector [3, 4, 5]) = some [6] := by
  have hv : CycleInput Examples.filled 1 2 (chainVector [3, 4, 5]) := by
    refine ⟨by decide +kernel, ?_⟩
    rw [Examples.filled_boundary]
    decide +kernel
  unfold runCycleFilling runCycleCoordinates fillingSupport fillingVector normalCoordinateVector
    activeRepresentatives representedOccurrences pairedRepresentative essentialRepresentative
    pairedVector essentialVector change essentialIndices pivotPairs reduced trace
  simp only [hv, ite_true]
  rw [Examples.filled_boundary]
  decide +kernel

private theorem filled_vertices_admitted (a : ℤ) (ha : 0 ≤ a) :
    CycleInput Examples.filled 0 a (chainVector [0, 2]) := by
  apply cycleInput_mono Examples.filled 0 0 a ha (chainVector [0, 2])
  refine ⟨by decide +kernel, ?_⟩
  rw [Examples.filled_boundary]
  decide +kernel

/-- A supplied pair of vertices can require several edges in the selected filling. -/
theorem multiple_edge_execution :
    runCycleFilling Examples.filled 0 1 (chainVector [0, 2]) = some [3, 4] := by
  have hv := filled_vertices_admitted 1 (by decide)
  unfold runCycleFilling runCycleCoordinates fillingSupport fillingVector normalCoordinateVector
    activeRepresentatives representedOccurrences pairedRepresentative essentialRepresentative
    pairedVector essentialVector change essentialIndices pivotPairs reduced trace
  simp only [hv, ite_true]
  rw [Examples.filled_boundary]
  decide +kernel

/-- A nonempty all-zero coordinate list is accepted. -/
theorem nonempty_zero_coordinates :
    runCycleCoordinates Examples.filled 0 1 (chainVector [0, 1]) = some [0] ∧
    runCycleFilling Examples.filled 0 1 (chainVector [0, 1]) = some [3] := by
  have hv : CycleInput Examples.filled 0 1 (chainVector [0, 1]) := by
    refine ⟨by decide +kernel, ?_⟩
    rw [Examples.filled_boundary]
    decide +kernel
  unfold runCycleFilling runCycleCoordinates fillingSupport fillingVector normalCoordinateVector
    activeRepresentatives representedOccurrences pairedRepresentative essentialRepresentative
    pairedVector essentialVector change essentialIndices pivotPairs reduced trace
  simp only [hv, ite_true]
  rw [Examples.filled_boundary]
  decide +kernel

/-- The equal-grade pivot remains available for filling despite value-barcode omission. -/
theorem tied_execution :
    runCycleFilling Examples.tied 1 1 (chainVector [3, 4, 5]) = some [6] := by
  have hv : CycleInput Examples.tied 1 1 (chainVector [3, 4, 5]) := by
    refine ⟨by decide +kernel, ?_⟩
    rw [Examples.tied_boundary]
    decide +kernel
  unfold runCycleFilling runCycleCoordinates fillingSupport fillingVector normalCoordinateVector
    activeRepresentatives representedOccurrences pairedRepresentative essentialRepresentative
    pairedVector essentialVector change essentialIndices pivotPairs reduced trace
  simp only [hv, ite_true]
  rw [Examples.tied_boundary]
  decide +kernel

/-- A negative-grade boundary is filled only after its edge enters. -/
theorem negative_executions :
    runCycleFilling Examples.negative 0 (-1) (chainVector [0, 1]) = some [2] ∧
    runCycleFilling Examples.negative 0 (-4) (chainVector [0, 1]) = none := by
  have hv1 : CycleInput Examples.negative 0 (-1) (chainVector [0, 1]) := by
    refine ⟨by decide +kernel, ?_⟩
    rw [Examples.negative_boundary]
    decide +kernel
  have hv4 : CycleInput Examples.negative 0 (-4) (chainVector [0, 1]) := by
    refine ⟨by decide +kernel, ?_⟩
    rw [Examples.negative_boundary]
    decide +kernel
  unfold runCycleFilling runCycleCoordinates fillingSupport fillingVector normalCoordinateVector
    activeRepresentatives representedOccurrences pairedRepresentative essentialRepresentative
    pairedVector essentialVector change essentialIndices pivotPairs reduced trace
  simp only [hv1, hv4, ite_true]
  rw [Examples.negative_boundary]
  decide +kernel

private theorem hollow_admitted :
    CycleInput Examples.hollow 1 100 (chainVector [3, 4, 5]) := by
  refine ⟨by decide +kernel, ?_⟩
  rw [Examples.hollow_boundary]
  decide +kernel

/-- The essential hollow-triangle cycle has no filling. -/
theorem hollow_refusal :
    runCycleFilling Examples.hollow 1 100 (chainVector [3, 4, 5]) = none := by
  unfold runCycleFilling runCycleCoordinates fillingSupport fillingVector normalCoordinateVector
    activeRepresentatives representedOccurrences pairedRepresentative essentialRepresentative
    pairedVector essentialVector change essentialIndices pivotPairs reduced trace
  simp only [hollow_admitted, ite_true]
  rw [Examples.hollow_boundary]
  decide +kernel

/-- Execution's refusal detects nonmembership in the actual signed-boundary submodule. -/
theorem hollow_not_boundary :
    vectorSublevelCycle Examples.hollow Examples.hollow_valid 1 100
      (chainVector [3, 4, 5]) hollow_admitted ∉
        simplicialBoundaries ((gradeFilter Examples.hollow Examples.hollow_valid).sublevel 100)
          (ZMod 2) 1 := by
  intro hb
  obtain ⟨b, he⟩ := (runCycleFilling_exists_iff_boundary Examples.hollow Examples.hollow_valid
    1 100 (chainVector [3, 4, 5]) hollow_admitted).mpr hb
  rw [hollow_refusal] at he
  cases he

/-- The public coefficient guarantee proves the boundary of the two-edge output. -/
theorem multiple_edge_boundary :
    (boundary Examples.filled).mulVec (chainVector [3, 4]) = chainVector [0, 2] :=
  (runCycleFilling_data Examples.filled 0 1 (chainVector [0, 2]) [3, 4]
    multiple_edge_execution).2.2.2

/-- The computed two-edge filling has an actual-chain realization with those exact coefficients. -/
theorem multiple_edge_actual_chain :
    ∃ B : Chain ((gradeFilter Examples.filled Examples.filled_valid).sublevel 1) (ZMod 2) 1,
      (letI := faceFintype Examples.filled Examples.filled_valid;
        (prefixChainEquiv (ZMod 2) (compatibleOrder Examples.filled Examples.filled_valid)
          (sublevelStage Examples.filled 1) 1
          (chainIncl (ZMod 2) (sublevel_eq_prefix Examples.filled Examples.filled_valid 1).le 1 B)).1 =
            faceVector Examples.filled Examples.filled_valid (chainVector [3, 4])) ∧
      TDA.Simplicial.boundary _ (ZMod 2) 0 B =
        (vectorSublevelCycle Examples.filled Examples.filled_valid 0 1
          (chainVector [0, 2]) (filled_vertices_admitted 1 (by decide))).1 := by
  obtain ⟨_, _, B, hcoeff, hboundary⟩ := runCycleFilling_correct Examples.filled 0 1
    (chainVector [0, 2]) [3, 4] multiple_edge_execution
  exact ⟨B, hcoeff, hboundary⟩

private theorem triangle_actual_boundary :
    ∃ (h : Valid Examples.filled) (hv : CycleInput Examples.filled 1 2 (chainVector [3, 4, 5])),
      ∃ B : Chain ((gradeFilter Examples.filled h).sublevel 2) (ZMod 2) 2,
        TDA.Simplicial.boundary _ (ZMod 2) 1 B =
          (vectorSublevelCycle Examples.filled h 1 2 (chainVector [3, 4, 5]) hv).1 := by
  obtain ⟨h, hv, B, _, hb⟩ := runCycleFilling_correct Examples.filled 1 2
    (chainVector [3, 4, 5]) [6] filled_execution
  exact ⟨h, hv, B, hb⟩

private theorem zero_empty_rejections :
    runCycleFilling [] 7 (-100) 0 = some [] ∧
    runCycleFilling Examples.delayed 0 6 0 = some [] ∧
    runCycleFilling Examples.delayed 0 100 (Pi.single 0 1) = none ∧
    runCycleFilling Examples.delayed 0 6 (Pi.single 0 1) = none ∧
    runCycleFilling Examples.negative 1 (-1) (Pi.single 0 1) = none ∧
    runCycleFilling Examples.negative 1 (-1) (Pi.single 2 1) = none ∧
    runCycleFilling [({0, 1}, 0)] 0 0 0 = none := by
  refine ⟨runCycleFilling_zero [] (by decide +kernel) 7 (-100),
    runCycleFilling_zero Examples.delayed Examples.delayed_valid 0 6,
    by decide +kernel, by decide +kernel, by decide +kernel, ?_, by decide +kernel⟩
  have hn : runCycleCoordinates Examples.negative 1 (-1) (Pi.single 2 1) = none := by
    apply (runCycleCoordinates_eq_none_iff _ _ _ _).mpr
    intro h
    have he := h.2.2
    rw [Examples.negative_boundary] at he
    have hne : Examples.edgeMatrix.mulVec (Pi.single (2 : Fin Examples.negative.length) 1) ≠ 0 := by
      decide +kernel
    exact hne he
  simp only [runCycleFilling, hn]

end TDA.Persistence.Reduction.FiniteInput.FillingExamples
