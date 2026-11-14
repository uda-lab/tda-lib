import TDA.Persistence.Reduction.FiniteInputSublevelBasis
import TDA.Persistence.Reduction.FiniteInputExamples

/-! Executable queries and complete actual-homology consumers. -/

set_option maxRecDepth 10000
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 512
set_option backward.defeqAttrib.useBackward true

namespace TDA.Persistence.Reduction.FiniteInput.BasisExamples

open TDA.Simplicial TDA.Filtration

private local instance : NeZero Examples.filled.length := ⟨by decide⟩
private local instance : NeZero Examples.hollow.length := ⟨by decide⟩

private def summary {n : ℕ} (r : Representative n) :
    ℕ × List ℕ × Option (List ℕ) :=
  (r.birthIndex.val, r.cycle.map Fin.val, r.bounding.map (List.map Fin.val))

private theorem filled_H0_data :
    (activeRepresentatives Examples.filled 0 0).map summary =
      [(1, [0, 1], some [3]), (2, [1, 2], some [4]), (0, [0], none)] := by
  unfold activeRepresentatives representedOccurrences pairedRepresentative essentialRepresentative
    pairedVector essentialVector change essentialIndices pivotPairs reduced trace
  rw [Examples.filled_boundary]
  decide +kernel

private theorem filled_H1_data :
    (activeRepresentatives Examples.filled 1 1).map summary =
      [(5, [3, 4, 5], some [6])] := by
  unfold activeRepresentatives representedOccurrences pairedRepresentative essentialRepresentative
    pairedVector essentialVector change essentialIndices pivotPairs reduced trace
  rw [Examples.filled_boundary]
  decide +kernel

private theorem filled_H1_dead : activeRepresentatives Examples.filled 1 2 = [] := by
  unfold activeRepresentatives representedOccurrences pairedRepresentative essentialRepresentative
    pairedVector essentialVector change essentialIndices pivotPairs reduced trace
  rw [Examples.filled_boundary]
  decide +kernel

private theorem hollow_H1_data :
    (activeRepresentatives Examples.hollow 1 100).map summary = [(5, [3, 4, 5], none)] := by
  unfold activeRepresentatives representedOccurrences pairedRepresentative essentialRepresentative
    pairedVector essentialVector change essentialIndices pivotPairs reduced trace
  rw [Examples.hollow_boundary]
  decide +kernel

private theorem tied_H1_empty : activeRepresentatives Examples.tied 1 1 = [] := by
  unfold activeRepresentatives representedOccurrences pairedRepresentative essentialRepresentative
    pairedVector essentialVector change essentialIndices pivotPairs reduced trace
  rw [Examples.tied_boundary]
  decide +kernel

private theorem filled_H1_length : (activeRepresentatives Examples.filled 1 1).length = 1 := by
  simpa only [List.length_map, List.length_cons, List.length_nil] using
    congrArg List.length filled_H1_data

private def filledH1 : BasisIndex Examples.filled 1 1 := ⟨0, by rw [filled_H1_length]; decide⟩

private theorem filled_H1_cycle :
    (basisRecord Examples.filled 1 1 filledH1).cycle.map Fin.val = [3, 4, 5] ∧
      (basisRecord Examples.filled 1 1 filledH1).bounding.map (List.map Fin.val) = some [6] := by
  have hd := congrArg (fun l => l[0]?) filled_H1_data
  rw [List.getElem?_map, List.getElem?_eq_getElem (by rw [filled_H1_length]; decide)] at hd
  change some (summary (basisRecord Examples.filled 1 1 filledH1)) =
    some (5, [3, 4, 5], some [6]) at hd
  exact ⟨congrArg (fun v => v.2.1) (Option.some.inj hd),
    congrArg (fun v => v.2.2) (Option.some.inj hd)⟩

private theorem filled_H1_basis_nonzero :
    basisClass Examples.filled Examples.filled_valid 1 1 filledH1 ≠ 0 := by
  rw [← sublevelBasis_apply]
  exact (sublevelBasis Examples.filled Examples.filled_valid 1 1).ne_zero filledH1

private theorem filled_complete_dimensions :
    Module.finrank (ZMod 2)
      (simplicialHomology ((gradeFilter Examples.filled Examples.filled_valid).sublevel 0)
        (ZMod 2) 0) = 3 ∧
    Module.finrank (ZMod 2)
      (simplicialHomology ((gradeFilter Examples.filled Examples.filled_valid).sublevel 1)
        (ZMod 2) 1) = 1 := by
  constructor
  · rw [sublevelHomology_finrank]
    simpa only [List.length_map, List.length_cons, List.length_nil] using
      congrArg List.length filled_H0_data
  · rw [sublevelHomology_finrank, filled_H1_length]

private theorem filled_H1_unique_expansion
    (x : simplicialHomology ((gradeFilter Examples.filled Examples.filled_valid).sublevel 1)
      (ZMod 2) 1) :
    ∃! c : BasisIndex Examples.filled 1 1 → ZMod 2,
      ∑ i, c i • basisClass Examples.filled Examples.filled_valid 1 1 i = x :=
  sublevelClass_unique_expansion Examples.filled Examples.filled_valid 1 1 x

private theorem filled_H1_all_die
    (x : simplicialHomology ((gradeFilter Examples.filled Examples.filled_valid).sublevel 1)
      (ZMod 2) 1) :
    (simplicialHomologyIncl (ZMod 2)
      ((gradeFilter Examples.filled Examples.filled_valid).sublevel_mono (by decide : (1 : ℤ) ≤ 2))
      1).hom x = 0 := by
  apply (sublevelCoordinates Examples.filled Examples.filled_valid 1 2).injective
  rw [sublevelCoordinates_naturality Examples.filled Examples.filled_valid 1 1 2 (by decide),
    map_zero]
  funext j
  have hj := j.isLt
  have hn : (activeRepresentatives Examples.filled 1 2).length = 0 :=
    congrArg List.length filled_H1_dead
  omega

private theorem essential_and_tied_dimensions :
    Module.finrank (ZMod 2)
      (simplicialHomology ((gradeFilter Examples.hollow Examples.hollow_valid).sublevel 100)
        (ZMod 2) 1) = 1 ∧
    Module.finrank (ZMod 2)
      (simplicialHomology ((gradeFilter Examples.tied Examples.tied_valid).sublevel 1)
        (ZMod 2) 1) = 0 := by
  constructor
  · rw [sublevelHomology_finrank]
    simpa only [List.length_map, List.length_cons, List.length_nil] using
      congrArg List.length hollow_H1_data
  · rw [sublevelHomology_finrank, tied_H1_empty]
    rfl

private theorem boundary_queries :
    runDegreeAtGrade Examples.delayed 0 6 = some [] ∧
    (runDegreeAtGrade Examples.delayed 0 7).map (List.map summary) =
      some [(0, [0], none)] ∧
    (runDegreeAtGrade Examples.negative 0 (-2)).map (List.map summary) =
      some [(1, [0, 1], some [2]), (0, [0], none)] ∧
    runDegreeAtGrade [] 0 0 = some [] ∧
    runDegreeAtGrade [({0, 1}, 0)] 0 0 = none := by
  refine ⟨by decide +kernel, by decide +kernel, ?_, by decide +kernel, by decide +kernel⟩
  unfold runDegreeAtGrade runAtGrade runWithRepresentatives representedOccurrences
    pairedRepresentative essentialRepresentative pairedVector essentialVector change
    essentialIndices pivotPairs reduced trace
  rw [Examples.negative_boundary]
  decide +kernel

private theorem empty_homology (p : ℕ) (a : ℤ) :
    Module.finrank (ZMod 2)
      (simplicialHomology ((gradeFilter [] (by decide +kernel : Valid [])).sublevel a)
        (ZMod 2) p) = 0 := by
  rw [sublevelHomology_finrank]
  rfl

private theorem negative_dimension :
    Module.finrank (ZMod 2)
      (simplicialHomology ((gradeFilter Examples.negative Examples.negative_valid).sublevel (-2))
        (ZMod 2) 0) = 2 := by
  rw [sublevelHomology_finrank]
  unfold activeRepresentatives representedOccurrences pairedRepresentative essentialRepresentative
    pairedVector essentialVector change essentialIndices pivotPairs reduced trace
  rw [Examples.negative_boundary]
  decide +kernel

private theorem isolated_dimensions :
    Module.finrank (ZMod 2)
      (simplicialHomology ((gradeFilter Examples.delayed Examples.delayed_valid).sublevel 6)
        (ZMod 2) 0) = 0 ∧
    Module.finrank (ZMod 2)
      (simplicialHomology ((gradeFilter Examples.delayed Examples.delayed_valid).sublevel 100)
        (ZMod 2) 0) = 1 := by
  constructor <;> rw [sublevelHomology_finrank] <;> decide +kernel

/-- One inclusion with a death, a survivor and a new birth, all in degree zero. -/
def mixed : Input := [({0}, 0), ({1}, 0), ({0, 1}, 1), ({2}, 1)]

theorem mixed_valid : Valid mixed := (validBool_iff _).mp (by decide +kernel)

private def mixedMatrix : Matrix (Fin 4) (Fin 4) (ZMod 2) := fun r c =>
  if c.val = 2 ∧ (r.val = 0 ∨ r.val = 1) then 1 else 0

private theorem mixed_boundary : boundary mixed = mixedMatrix := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [boundary, mixed, mixedMatrix, Finset.orderEmbOfFin_apply,
      Finset.sort_insert, Finset.sort_singleton] <;> decide +kernel

/-- The mixed birth/death fixture's boundary, available to executable consumers. -/
theorem mixed_boundary_values : boundary mixed =
    fun r c => if c.val = 2 ∧ (r.val = 0 ∨ r.val = 1) then 1 else 0 :=
  mixed_boundary

private theorem mixed_births :
    (activeRepresentatives mixed 0 0).map (fun r => r.birthIndex.val) = [1, 0] ∧
    (activeRepresentatives mixed 0 1).map (fun r => r.birthIndex.val) = [0, 3] := by
  unfold activeRepresentatives representedOccurrences pairedRepresentative essentialRepresentative
    pairedVector essentialVector change essentialIndices pivotPairs reduced trace
  rw [mixed_boundary]
  decide +kernel

private theorem mixed_source_length : (activeRepresentatives mixed 0 0).length = 2 := by
  simpa only [List.length_map, List.length_cons, List.length_nil] using
    congrArg List.length mixed_births.1

private theorem mixed_target_length : (activeRepresentatives mixed 0 1).length = 2 := by
  simpa only [List.length_map, List.length_cons, List.length_nil] using
    congrArg List.length mixed_births.2

private def survivorSource : BasisIndex mixed 0 0 := ⟨1, by rw [mixed_source_length]; decide⟩
private def survivorTarget : BasisIndex mixed 0 1 := ⟨0, by rw [mixed_target_length]; decide⟩
private def newTarget : BasisIndex mixed 0 1 := ⟨1, by rw [mixed_target_length]; decide⟩

private theorem mixed_source_birth (i : BasisIndex mixed 0 0) :
    (basisRecord mixed 0 0 i).birthIndex.val = if i.val = 0 then 1 else 0 := by
  have hi := i.isLt
  have hl := mixed_source_length
  have he := congrArg (fun l => l[i.val]?) mixed_births.1
  rw [List.getElem?_map, List.getElem?_eq_getElem i.isLt] at he
  have hc : i.val = 0 ∨ i.val = 1 := by omega
  rcases hc with hc | hc <;> simpa [basisRecord, List.get_eq_getElem, hc] using he

private theorem mixed_target_birth (j : BasisIndex mixed 0 1) :
    (basisRecord mixed 0 1 j).birthIndex.val = if j.val = 0 then 0 else 3 := by
  have hj := j.isLt
  have hl := mixed_target_length
  have he := congrArg (fun l => l[j.val]?) mixed_births.2
  rw [List.getElem?_map, List.getElem?_eq_getElem j.isLt] at he
  have hc : j.val = 0 ∨ j.val = 1 := by omega
  rcases hc with hc | hc <;> simpa [basisRecord, List.get_eq_getElem, hc] using he

private theorem mixed_transition_apply (j : BasisIndex mixed 0 1) (i : BasisIndex mixed 0 0) :
    basisTransition mixed 0 0 1 j i = if j.val = 0 ∧ i.val = 1 then 1 else 0 := by
  rw [basisTransition_apply]
  simp only [Fin.ext_iff, mixed_source_birth, mixed_target_birth]
  have hi := i.isLt
  have hl := mixed_source_length
  have hc : i.val = 0 ∨ i.val = 1 := by omega
  rcases hc with hc | hc <;> by_cases hj : j.val = 0 <;> simp [hc, hj]

private theorem mixed_mulVec (v : BasisIndex mixed 0 0 → ZMod 2) :
    (basisTransition mixed 0 0 1).mulVec v survivorTarget = v survivorSource ∧
      (basisTransition mixed 0 0 1).mulVec v newTarget = 0 := by
  constructor
  · rw [Matrix.mulVec_apply_eq_sum, Finset.sum_eq_single survivorSource]
    · simp [mixed_transition_apply, survivorSource, survivorTarget]
    · intro i _ hi
      have hn : i.val ≠ 1 := by
        intro he
        exact hi (Fin.ext he)
      simp [mixed_transition_apply, survivorTarget, hn]
    · simp
  · rw [Matrix.mulVec_apply_eq_sum]
    apply Finset.sum_eq_zero
    intro i _
    simp [mixed_transition_apply, newTarget]

private theorem mixed_actual_inclusion
    (x : simplicialHomology ((gradeFilter mixed mixed_valid).sublevel 0) (ZMod 2) 0) :
    let y := (simplicialHomologyIncl (ZMod 2)
      ((gradeFilter mixed mixed_valid).sublevel_mono (by decide : (0 : ℤ) ≤ 1)) 0).hom x
    sublevelCoordinates mixed mixed_valid 0 1 y survivorTarget =
      sublevelCoordinates mixed mixed_valid 0 0 x survivorSource ∧
    sublevelCoordinates mixed mixed_valid 0 1 y newTarget = 0 := by
  dsimp only
  rw [sublevelCoordinates_naturality mixed mixed_valid 0 0 1 (by decide)]
  exact mixed_mulVec _

end TDA.Persistence.Reduction.FiniteInput.BasisExamples
