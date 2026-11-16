import TDA.Persistence.Reduction.FiniteInputExamples
import TDA.Persistence.Reduction.FiniteInputVertexMapChains
import TDA.Persistence.Reduction.FiniteInputHomologyDimensionsExamples

/-! Executable original-position lookups through the finite-input semantic adapters. -/

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 512

namespace TDA.Persistence.Reduction.FiniteInput.IndexExamples

open TDA.Simplicial TDA.Filtration

abbrev Row := ℕ × Finset ℕ × ℤ

/-- Exercise the public forward face map, inverse search and semantic grade together. -/
def listRows (xs : Input) (h : Valid xs) : List Row :=
  (List.finRange xs.length).map fun i =>
    let s := listEquiv xs h i
    (((listEquiv xs h).symm s).val, s.val, (gradeFilter xs h).value s)

/-- Exercise both directions of the cardinality-indexed face equivalence. -/
def positionRows (xs : Input) (h : Valid xs) : List Row :=
  letI := faceFintype xs h
  (List.finRange (faceCount (complex xs h))).map fun i =>
    let s := positionEquiv xs h i
    (((positionEquiv xs h).symm s).val, s.val, (gradeFilter xs h).value s)

/-- The compatible order executes the original list order, including tied faces. -/
def compatibleRows (xs : Input) (h : Valid xs) : List Row :=
  letI := faceFintype xs h
  (List.finRange (faceCount (complex xs h))).map fun i =>
    let s := (compatibleOrder xs h).enum i
    (((compatibleOrder xs h).enum.symm s).val, s.val, (gradeFilter xs h).value s)

/-- Read the actual finite enumeration, sorting only its returned position labels. -/
def enumerationPositions (xs : Input) (h : Valid xs) : List ℕ :=
  ((faceFintype xs h).elems.image fun s => ((listEquiv xs h).symm s).val).sort (· ≤ ·)

/-- All three public presentations must give the same explicit rows. -/
def adapterRows (xs : Input) (h : Valid xs) : List (List Row) :=
  [listRows xs h, positionRows xs h, compatibleRows xs h]

/-- A filled triangle with negative/tied grades and sparse vertex labels. -/
def sparse : Input :=
  [({47}, -4), ({1000003}, -4), ({9000007}, -4),
    ({47, 1000003}, -1), ({1000003, 9000007}, -1), ({47, 9000007}, -1),
    ({47, 1000003, 9000007}, 2)]

/-- A distinct valid ordering of the tied vertices and tied edges. -/
def sparseReordered : Input :=
  [({9000007}, -4), ({47}, -4), ({1000003}, -4),
    ({47, 9000007}, -1), ({47, 1000003}, -1), ({1000003, 9000007}, -1),
    ({47, 1000003, 9000007}, 2)]

theorem sparse_valid : Valid sparse := by decide +kernel
theorem sparseReordered_valid : Valid sparseReordered := by decide +kernel

def sparseExpected : List Row :=
  [(0, {47}, -4), (1, {1000003}, -4), (2, {9000007}, -4),
    (3, {47, 1000003}, -1), (4, {1000003, 9000007}, -1), (5, {47, 9000007}, -1),
    (6, {47, 1000003, 9000007}, 2)]

theorem sparse_adapters : adapterRows sparse sparse_valid =
    List.replicate 3 sparseExpected := by decide +kernel

theorem sparse_reordered_adapters : adapterRows sparseReordered sparseReordered_valid =
    List.replicate 3
      [(0, {9000007}, -4), (1, {47}, -4), (2, {1000003}, -4),
        (3, {47, 9000007}, -1), (4, {47, 1000003}, -1), (5, {1000003, 9000007}, -1),
        (6, {47, 1000003, 9000007}, 2)] := by decide +kernel

theorem filled_adapters : adapterRows Examples.filled Examples.filled_valid =
    List.replicate 3
      [(0, {0}, 0), (1, {1}, 0), (2, {2}, 0), (3, {0, 1}, 1), (4, {1, 2}, 1),
        (5, {0, 2}, 1), (6, {0, 1, 2}, 2)] := by decide +kernel

theorem hollow_adapters : adapterRows Examples.hollow Examples.hollow_valid =
    List.replicate 3
      [(0, {0}, 0), (1, {1}, 0), (2, {2}, 0), (3, {0, 1}, 1), (4, {1, 2}, 1),
        (5, {0, 2}, 1)] := by decide +kernel

theorem tied_adapters : adapterRows Examples.tied Examples.tied_valid =
    List.replicate 3
      [(0, {0}, 0), (1, {1}, 0), (2, {2}, 0), (3, {0, 1}, 1), (4, {1, 2}, 1),
        (5, {0, 2}, 1), (6, {0, 1, 2}, 1)] := by decide +kernel

theorem empty_valid : Valid [] := by decide +kernel

theorem empty_adapters : adapterRows [] empty_valid = [[], [], []] ∧
    enumerationPositions [] empty_valid = [] := by decide +kernel

private theorem enumerationPositions_eq_range (xs : Input) (h : Valid xs) :
    enumerationPositions xs h = List.range xs.length := by
  unfold enumerationPositions
  have he : ((faceFintype xs h).elems.image
      fun s => ((listEquiv xs h).symm s).val) = Finset.range xs.length := by
    ext k
    constructor
    · intro hk
      obtain ⟨s, _, rfl⟩ := Finset.mem_image.mp hk
      exact Finset.mem_range.mpr ((listEquiv xs h).symm s).isLt
    · intro hk
      let i : Fin xs.length := ⟨k, Finset.mem_range.mp hk⟩
      refine Finset.mem_image.mpr ⟨listEquiv xs h i, ?_, ?_⟩
      · exact (faceFintype xs h).complete _
      · exact congrArg Fin.val ((listEquiv xs h).symm_apply_apply i)
  rw [he]
  exact Finset.sort_range xs.length

theorem finite_enumerations : enumerationPositions sparse sparse_valid = [0, 1, 2, 3, 4, 5, 6] ∧
    enumerationPositions sparseReordered sparseReordered_valid = [0, 1, 2, 3, 4, 5, 6] ∧
    enumerationPositions Examples.hollow Examples.hollow_valid = [0, 1, 2, 3, 4, 5] := by
  simp only [enumerationPositions_eq_range]
  decide +kernel

/-- Construct actual sublevel faces and read their original index, grade and degree. -/
def sublevelRows (xs : Input) (h : Valid xs) (p : ℕ) (a : ℤ) :
    List (ℕ × ℤ × ℕ × Bool) :=
  (List.finRange xs.length).filterMap fun i =>
    if ha : (xs.get i).2 ≤ a then
      if hd : (xs.get i).1.card = p + 1 then
        let s : Face ((gradeFilter xs h).sublevel a) p :=
          ⟨(xs.get i).1, (mem_sublevel_iff_list xs h a _).mpr ⟨i, rfl, ha⟩, hd⟩
        let j := sublevelFaceIndex xs h s
        some (j.val, (xs.get j).2, degree xs j, decide ((xs.get j).2 ≤ a))
      else none
    else none

theorem sublevels_before_at_between_after :
    sublevelRows sparse sparse_valid 0 (-5) = [] ∧
    sublevelRows sparse sparse_valid 0 (-4) = [(0, -4, 0, true), (1, -4, 0, true), (2, -4, 0, true)] ∧
    sublevelRows sparse sparse_valid 0 (-2) = [(0, -4, 0, true), (1, -4, 0, true), (2, -4, 0, true)] ∧
    sublevelRows sparse sparse_valid 1 (-2) = [] ∧
    sublevelRows sparse sparse_valid 1 (-1) = [(3, -1, 1, true), (4, -1, 1, true), (5, -1, 1, true)] ∧
    sublevelRows sparse sparse_valid 0 3 = [(0, -4, 0, true), (1, -4, 0, true), (2, -4, 0, true)] ∧
    sublevelRows sparse sparse_valid 1 3 = [(3, -1, 1, true), (4, -1, 1, true), (5, -1, 1, true)] ∧
    sublevelRows sparse sparse_valid 2 3 = [(6, 2, 2, true)] := by decide +kernel

theorem reordered_sublevels :
    sublevelRows sparseReordered sparseReordered_valid 0 (-4) =
      [(0, -4, 0, true), (1, -4, 0, true), (2, -4, 0, true)] ∧
    sublevelRows sparseReordered sparseReordered_valid 1 (-1) =
      [(3, -1, 1, true), (4, -1, 1, true), (5, -1, 1, true)] ∧
    sublevelRows sparseReordered sparseReordered_valid 2 3 = [(6, 2, 2, true)] := by decide +kernel

/-- Both round trips hold for actual faces, independently of their validity witness. -/
theorem roundTrips_and_validity_proofs (h h' : Valid sparse)
    (s : TotalFace (complex sparse h)) (i : Fin sparse.length) :
    listEquiv sparse h ((listEquiv sparse h).symm s) = s ∧
    (listEquiv sparse h).symm (listEquiv sparse h i) = i ∧
    (listEquiv sparse h).symm s = (listEquiv sparse h').symm s ∧
    (gradeFilter sparse h).value s = (gradeFilter sparse h').value s :=
  ⟨(listEquiv sparse h).apply_symm_apply s, (listEquiv sparse h).symm_apply_apply i,
    listEquiv_symm_valid_irrel sparse h h' s, gradeFilter_valid_irrel sparse h h' s⟩

/-- Agreement with the former inverse is a proof-side compatibility result only. -/
theorem former_inverse_agreement (s : TotalFace (complex sparse sparse_valid)) :
    (listEquiv sparse sparse_valid).symm s =
      (Equiv.ofBijective (listFace sparse sparse_valid) (listFace_bijective sparse sparse_valid)).symm s := by
  rw [listEquiv_eq_ofBijective]

end TDA.Persistence.Reduction.FiniteInput.IndexExamples
