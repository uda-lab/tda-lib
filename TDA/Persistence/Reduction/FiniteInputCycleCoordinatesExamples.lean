import TDA.Persistence.Reduction.FiniteInputCycleCoordinatesCorrectness
import TDA.Persistence.Reduction.FiniteInputExamples
import TDA.Persistence.Reduction.FiniteInputSublevelBasisExamples

/-! Public executions and actual homology of supplied, rather than selected, cycles. -/

set_option maxRecDepth 10000
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 512
set_option backward.defeqAttrib.useBackward true

namespace TDA.Persistence.Reduction.FiniteInput.CoordinateExamples

open TDA.Simplicial TDA.Filtration

private local instance : NeZero Examples.filled.length := ⟨by decide⟩
private local instance : NeZero Examples.hollow.length := ⟨by decide⟩
private local instance : NeZero Examples.tied.length := ⟨by decide⟩
private local instance : NeZero Examples.negative.length := ⟨by decide⟩
private local instance : NeZero Examples.delayed.length := ⟨by decide⟩
private local instance : NeZero BasisExamples.mixed.length := ⟨by decide⟩

private def filledLoop : Fin Examples.filled.length → ZMod 2 := chainVector [3, 4, 5]
private def hollowLoop : Fin Examples.hollow.length → ZMod 2 := chainVector [3, 4, 5]
private def tiedLoop : Fin Examples.tied.length → ZMod 2 := chainVector [3, 4, 5]

private theorem filled_cycles :
    (activeRepresentatives Examples.filled 1 1).map Representative.cycle = [[3, 4, 5]] := by
  unfold activeRepresentatives representedOccurrences pairedRepresentative essentialRepresentative
    pairedVector essentialVector change essentialIndices pivotPairs reduced trace
  rw [Examples.filled_boundary]
  decide +kernel

private theorem filled_length : (activeRepresentatives Examples.filled 1 1).length = 1 := by
  simpa only [List.length_map, List.length_cons, List.length_nil] using
    congrArg List.length filled_cycles

private def filledIndex : BasisIndex Examples.filled 1 1 := ⟨0, by rw [filled_length]; decide⟩

private theorem filled_record : (basisRecord Examples.filled 1 1 filledIndex).cycle = [3, 4, 5] := by
  have he := congrArg (fun l => l[0]?) filled_cycles
  rw [List.getElem?_map, List.getElem?_eq_getElem (by rw [filled_length]; decide)] at he
  exact Option.some.inj he

private theorem filled_admitted : CycleInput Examples.filled 1 1 filledLoop := by
  have h := basisRecord_cycleInput Examples.filled Examples.filled_valid 1 1 filledIndex
  simpa only [filled_record, filledLoop] using h

private theorem ofFn_singleton {n : ℕ} (hn : n = 1) (f : Fin n → ZMod 2) :
    List.ofFn f = [f ⟨0, by omega⟩] := by
  subst n
  rfl

private theorem filled_execution : runCycleCoordinates Examples.filled 1 1 filledLoop = some [1] := by
  have h := runCycleCoordinates_basisRecord Examples.filled Examples.filled_valid 1 1 filledIndex
  rw [filled_record, ofFn_singleton filled_length] at h
  simpa [filledLoop, filledIndex] using h

private theorem filled_class_nonzero :
    vectorSublevelClass Examples.filled Examples.filled_valid 1 1 filledLoop filled_admitted ≠ 0 := by
  have hu := rawCycleCoordinates_basisRecord Examples.filled 1 1 filledIndex
  rw [filled_record] at hu
  intro hz
  have hc := (rawCycleCoordinates_eq_zero_iff Examples.filled Examples.filled_valid 1 1
    filledLoop filled_admitted).mpr hz
  have he := congrFun (hu.symm.trans hc) filledIndex
  simp at he

private theorem filled_dead : activeRepresentatives Examples.filled 1 2 = [] := by
  unfold activeRepresentatives representedOccurrences pairedRepresentative essentialRepresentative
    pairedVector essentialVector change essentialIndices pivotPairs reduced trace
  rw [Examples.filled_boundary]
  decide +kernel

private theorem filled_death_execution : runCycleCoordinates Examples.filled 1 2 filledLoop = some [] := by
  rw [runCycleCoordinates_coefficients Examples.filled Examples.filled_valid 1 2 filledLoop
    (cycleInput_mono Examples.filled 1 1 2 (by decide) filledLoop filled_admitted)]
  have hn : (activeRepresentatives Examples.filled 1 2).length = 0 := congrArg List.length filled_dead
  have he : ∀ (n : ℕ) (f : Fin n → ZMod 2), n = 0 → List.ofFn f = [] := by
    intro n f hn
    subst n
    rfl
  rw [he _ _ hn]

private theorem filled_boundary_at_death :
    vectorSublevelCycle Examples.filled Examples.filled_valid 1 2 filledLoop
      (cycleInput_mono Examples.filled 1 1 2 (by decide) filledLoop filled_admitted) ∈
      simplicialBoundaries ((gradeFilter Examples.filled Examples.filled_valid).sublevel 2)
        (ZMod 2) 1 := by
  apply (rawCycleCoordinates_eq_zero_iff_boundary Examples.filled Examples.filled_valid 1 2
    filledLoop _).mp
  funext i
  have hi := i.isLt
  have hn : (activeRepresentatives Examples.filled 1 2).length = 0 := congrArg List.length filled_dead
  omega

private theorem hollow_cycles :
    (activeRepresentatives Examples.hollow 1 100).map Representative.cycle = [[3, 4, 5]] := by
  unfold activeRepresentatives representedOccurrences pairedRepresentative essentialRepresentative
    pairedVector essentialVector change essentialIndices pivotPairs reduced trace
  rw [Examples.hollow_boundary]
  decide +kernel

private theorem hollow_length : (activeRepresentatives Examples.hollow 1 100).length = 1 := by
  simpa only [List.length_map, List.length_cons, List.length_nil] using
    congrArg List.length hollow_cycles

private def hollowIndex : BasisIndex Examples.hollow 1 100 := ⟨0, by rw [hollow_length]; decide⟩

private theorem hollow_record : (basisRecord Examples.hollow 1 100 hollowIndex).cycle = [3, 4, 5] := by
  have he := congrArg (fun l => l[0]?) hollow_cycles
  rw [List.getElem?_map, List.getElem?_eq_getElem (by rw [hollow_length]; decide)] at he
  exact Option.some.inj he

private theorem hollow_admitted : CycleInput Examples.hollow 1 100 hollowLoop := by
  have h := basisRecord_cycleInput Examples.hollow Examples.hollow_valid 1 100 hollowIndex
  simpa only [hollow_record, hollowLoop] using h

private theorem hollow_execution : runCycleCoordinates Examples.hollow 1 100 hollowLoop = some [1] := by
  have h := runCycleCoordinates_basisRecord Examples.hollow Examples.hollow_valid 1 100 hollowIndex
  rw [hollow_record, ofFn_singleton hollow_length] at h
  simpa [hollowLoop, hollowIndex] using h

private theorem hollow_class_nonzero :
    vectorSublevelClass Examples.hollow Examples.hollow_valid 1 100 hollowLoop hollow_admitted ≠ 0 := by
  have hu := rawCycleCoordinates_basisRecord Examples.hollow 1 100 hollowIndex
  rw [hollow_record] at hu
  intro hz
  have hc := (rawCycleCoordinates_eq_zero_iff Examples.hollow Examples.hollow_valid 1 100
    hollowLoop hollow_admitted).mpr hz
  have he := congrFun (hu.symm.trans hc) hollowIndex
  simp at he

private def vertex0 : Fin Examples.negative.length → ZMod 2 := Pi.single 0 1
private def vertex1 : Fin Examples.negative.length → ZMod 2 := Pi.single 1 1
private def edgeBoundary : Fin Examples.negative.length → ZMod 2 := chainVector [0, 1]

private theorem vertex0_admitted : CycleInput Examples.negative 0 (-1) vertex0 := by decide +kernel
private theorem vertex1_admitted : CycleInput Examples.negative 0 (-1) vertex1 := by decide +kernel
private theorem edge_admitted : CycleInput Examples.negative 0 (-1) edgeBoundary := by
  refine ⟨by decide +kernel, ?_⟩
  rw [Examples.negative_boundary]
  decide +kernel

private theorem arbitrary_vertex_executions :
    runCycleCoordinates Examples.negative 0 (-4) vertex0 = some [0, 1] ∧
    runCycleCoordinates Examples.negative 0 (-4) vertex1 = some [1, 1] ∧
    runCycleCoordinates Examples.negative 0 (-1) vertex0 = some [1] ∧
    runCycleCoordinates Examples.negative 0 (-1) vertex1 = some [1] ∧
    runCycleCoordinates Examples.negative 0 (-1) edgeBoundary = some [0] := by
  unfold runCycleCoordinates normalCoordinateVector activeRepresentatives representedOccurrences
    pairedRepresentative essentialRepresentative pairedVector essentialVector change
    essentialIndices pivotPairs reduced trace
  rw [Examples.negative_boundary]
  decide +kernel

private theorem distinct_homologous_vertices : vertex0 ≠ vertex1 ∧
    vectorSublevelClass Examples.negative Examples.negative_valid 0 (-1) vertex0 vertex0_admitted =
      vectorSublevelClass Examples.negative Examples.negative_valid 0 (-1) vertex1 vertex1_admitted := by
  constructor
  · intro he
    have he0 := congrFun he 0
    have hn : (0 : Fin Examples.negative.length) ≠ 1 := by decide +kernel
    simp [vertex0, vertex1, hn] at he0
  · apply (rawCycleCoordinates_eq_iff Examples.negative Examples.negative_valid 0 (-1)
      vertex0 vertex1 vertex0_admitted vertex1_admitted).mp
    apply List.ofFn_injective
    have he0 := Option.some.inj ((runCycleCoordinates_coefficients Examples.negative
      Examples.negative_valid 0 (-1) vertex0 vertex0_admitted).symm.trans
        arbitrary_vertex_executions.2.2.1)
    have he1 := Option.some.inj ((runCycleCoordinates_coefficients Examples.negative
      Examples.negative_valid 0 (-1) vertex1 vertex1_admitted).symm.trans
        arbitrary_vertex_executions.2.2.2.1)
    exact he0.trans he1.symm

private theorem nonzero_boundary : edgeBoundary ≠ 0 ∧
    vectorSublevelCycle Examples.negative Examples.negative_valid 0 (-1) edgeBoundary edge_admitted ∈
      simplicialBoundaries ((gradeFilter Examples.negative Examples.negative_valid).sublevel (-1))
        (ZMod 2) 0 := by
  constructor
  · intro he
    have he0 := congrFun he 0
    simp [edgeBoundary, chainVector] at he0
  · apply (rawCycleCoordinates_eq_zero_iff_boundary Examples.negative Examples.negative_valid 0 (-1)
      edgeBoundary edge_admitted).mp
    apply List.ofFn_injective
    have he := Option.some.inj ((runCycleCoordinates_coefficients Examples.negative
      Examples.negative_valid 0 (-1) edgeBoundary edge_admitted).symm.trans
        arbitrary_vertex_executions.2.2.2.2)
    have hn : (activeRepresentatives Examples.negative 0 (-1)).length = 1 :=
      (runCycleCoordinates_length Examples.negative 0 (-1) edgeBoundary [0]
        arbitrary_vertex_executions.2.2.2.2).symm
    have hz := ofFn_singleton hn (0 : BasisIndex Examples.negative 0 (-1) → ZMod 2)
    exact he.trans hz.symm

private def mixedVertex : Fin BasisExamples.mixed.length → ZMod 2 := Pi.single 1 1

private theorem mixed_executions :
    runCycleCoordinates BasisExamples.mixed 0 0 mixedVertex = some [1, 1] ∧
    runCycleCoordinates BasisExamples.mixed 0 1 mixedVertex = some [1, 0] := by
  unfold runCycleCoordinates normalCoordinateVector activeRepresentatives representedOccurrences
    pairedRepresentative essentialRepresentative pairedVector essentialVector change
    essentialIndices pivotPairs reduced trace
  rw [BasisExamples.mixed_boundary_values]
  decide +kernel

private theorem mixed_transport :
    rawCycleCoordinates BasisExamples.mixed 0 1 mixedVertex =
      (basisTransition BasisExamples.mixed 0 0 1).mulVec
        (rawCycleCoordinates BasisExamples.mixed 0 0 mixedVertex) :=
  rawCycleCoordinates_naturality BasisExamples.mixed BasisExamples.mixed_valid 0 0 1
    (by decide) mixedVertex (by decide +kernel)

private theorem tied_admitted : CycleInput Examples.tied 1 1 tiedLoop := by
  refine ⟨by decide +kernel, ?_⟩
  rw [Examples.tied_boundary]
  decide +kernel

private theorem tied_execution : runCycleCoordinates Examples.tied 1 1 tiedLoop = some [] := by
  apply (runCycleCoordinates_eq_some_iff _ _ _ _ _).mpr
  refine ⟨Examples.tied_valid, tied_admitted, ?_⟩
  have he : activeRepresentatives Examples.tied 1 1 = [] := by
    unfold activeRepresentatives representedOccurrences pairedRepresentative essentialRepresentative
      pairedVector essentialVector change essentialIndices pivotPairs reduced trace
    rw [Examples.tied_boundary]
    decide +kernel
  rw [he]
  rfl

private theorem zero_empty_essential_rejections :
    runCycleCoordinates [] 7 (-100) 0 = some [] ∧
    runCycleCoordinates Examples.delayed 0 100 (Pi.single 0 1) = some [1] ∧
    runCycleCoordinates Examples.delayed 0 6 0 = some [] ∧
    runCycleCoordinates Examples.delayed 0 6 (Pi.single 0 1) = none ∧
    runCycleCoordinates Examples.negative 1 (-1) vertex0 = none ∧
    runCycleCoordinates Examples.negative 1 (-1) (Pi.single 2 1) = none ∧
    runCycleCoordinates [({0, 1}, 0)] 0 0 0 = none := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, ?_, by decide +kernel⟩
  apply (runCycleCoordinates_eq_none_iff _ _ _ _).mpr
  intro h
  have he := h.2.2
  rw [Examples.negative_boundary] at he
  have hn : (Examples.edgeMatrix).mulVec (Pi.single (2 : Fin Examples.negative.length) 1) ≠ 0 := by
    decide +kernel
  exact hn he

end TDA.Persistence.Reduction.FiniteInput.CoordinateExamples
