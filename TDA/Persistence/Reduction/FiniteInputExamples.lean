import TDA.Persistence.Reduction.FiniteInput
import TDA.Persistence.Morse.MatchingSchedule

/-! End-to-end executions of the public finite-input pipeline. -/

set_option maxRecDepth 10000
set_option maxHeartbeats 800000

namespace TDA.Persistence.Reduction.FiniteInput.Examples

def filled : Input :=
  [({0}, 0), ({1}, 0), ({2}, 0), ({0, 1}, 1), ({1, 2}, 1),
    ({0, 2}, 1), ({0, 1, 2}, 2)]

def hollow : Input := filled.take 6

def tied : Input :=
  [({0}, 0), ({1}, 0), ({2}, 0), ({0, 1}, 1), ({1, 2}, 1),
    ({0, 2}, 1), ({0, 1, 2}, 1)]

theorem filled_valid : Valid filled := (validBool_iff filled).mp (by decide +kernel)
theorem hollow_valid : Valid hollow := (validBool_iff hollow).mp (by decide +kernel)
theorem tied_valid : Valid tied := (validBool_iff tied).mp (by decide +kernel)

def triangleMatrix : Matrix (Fin 7) (Fin 7) (ZMod 2) := fun r c =>
  if c.val = 3 then (if r.val = 0 ∨ r.val = 1 then 1 else 0)
  else if c.val = 4 then (if r.val = 1 ∨ r.val = 2 then 1 else 0)
  else if c.val = 5 then (if r.val = 0 ∨ r.val = 2 then 1 else 0)
  else if c.val = 6 then (if r.val = 3 ∨ r.val = 4 ∨ r.val = 5 then 1 else 0)
  else 0

theorem filled_boundary : boundary filled = triangleMatrix := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [boundary, filled, triangleMatrix, Finset.orderEmbOfFin_apply,
      Finset.sort_insert, Finset.sort_singleton] <;> decide +kernel

theorem filled_pairs_raw : pivotPairs filled =
    [(⟨1, by decide⟩, ⟨3, by decide⟩),
      (⟨2, by decide⟩, ⟨4, by decide⟩),
      (⟨5, by decide⟩, ⟨6, by decide⟩)] := by
  simp only [pivotPairs, reduced, trace]
  rw [filled_boundary]
  decide +kernel

theorem filled_essential_raw : essentialIndices filled = [⟨0, by decide⟩] := by
  simp only [essentialIndices, reduced, trace]
  rw [filled_boundary]
  rw [filled_pairs_raw]
  decide +kernel

theorem filled_pairs : (pivotPairs filled).map (fun q => (q.1.val, q.2.val)) =
    [(1, 3), (2, 4), (5, 6)] := by rw [filled_pairs_raw]; rfl

theorem filled_essential : (essentialIndices filled).map Fin.val = [0] := by
  rw [filled_essential_raw]
  rfl

theorem filled_run : run filled = some
    [⟨0, 0, .finite 1⟩, ⟨0, 0, .finite 1⟩,
      ⟨1, 1, .finite 2⟩, ⟨0, 0, .essential⟩] := by
  simp [run, (validBool_iff filled).mpr filled_valid,
    occurrences, finiteOccurrences, essentialOccurrences,
    filled_pairs_raw, filled_essential_raw, pairOccurrence, degree]
  decide +kernel

def hollowMatrix : Matrix (Fin 6) (Fin 6) (ZMod 2) := fun r c =>
  if c.val = 3 then (if r.val = 0 ∨ r.val = 1 then 1 else 0)
  else if c.val = 4 then (if r.val = 1 ∨ r.val = 2 then 1 else 0)
  else if c.val = 5 then (if r.val = 0 ∨ r.val = 2 then 1 else 0)
  else 0

theorem hollow_boundary : boundary hollow = hollowMatrix := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [boundary, hollow, filled, hollowMatrix, Finset.orderEmbOfFin_apply,
      Finset.sort_insert, Finset.sort_singleton] <;> decide +kernel

theorem hollow_pairs_raw : pivotPairs hollow =
    [(⟨1, by decide⟩, ⟨3, by decide⟩),
      (⟨2, by decide⟩, ⟨4, by decide⟩)] := by
  simp only [pivotPairs, reduced, trace]
  rw [hollow_boundary]
  decide +kernel

theorem hollow_essential_raw : essentialIndices hollow =
    [⟨0, by decide⟩, ⟨5, by decide⟩] := by
  simp only [essentialIndices, reduced, trace]
  rw [hollow_boundary]
  rw [hollow_pairs_raw]
  decide +kernel

theorem hollow_run : run hollow = some
    [⟨0, 0, .finite 1⟩, ⟨0, 0, .finite 1⟩,
      ⟨0, 0, .essential⟩, ⟨1, 1, .essential⟩] := by
  simp [run, (validBool_iff hollow).mpr hollow_valid,
    occurrences, finiteOccurrences, essentialOccurrences,
    hollow_pairs_raw, hollow_essential_raw, pairOccurrence, degree]
  decide +kernel

theorem tied_boundary : boundary tied = triangleMatrix := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [boundary, tied, triangleMatrix, Finset.orderEmbOfFin_apply,
      Finset.sort_insert, Finset.sort_singleton] <;> decide +kernel

theorem tied_run : run tied = some
    [⟨0, 0, .finite 1⟩, ⟨0, 0, .finite 1⟩,
      ⟨0, 0, .essential⟩] := by
  have hp : pivotPairs tied =
      [(⟨1, by decide⟩, ⟨3, by decide⟩),
        (⟨2, by decide⟩, ⟨4, by decide⟩),
        (⟨5, by decide⟩, ⟨6, by decide⟩)] := by
    simp only [pivotPairs, reduced, trace]
    rw [tied_boundary]
    decide +kernel
  have he : essentialIndices tied = [⟨0, by decide⟩] := by
    simp only [essentialIndices, reduced, trace]
    rw [tied_boundary]
    rw [hp]
    decide +kernel
  simp [run, (validBool_iff tied).mpr tied_valid,
    occurrences, finiteOccurrences, essentialOccurrences,
    hp, he, pairOccurrence, degree]
  decide +kernel

theorem empty_run : run [] = some [] := by decide +kernel

def delayed : Input := [({47}, 7)]
theorem delayed_valid : Valid delayed := (validBool_iff delayed).mp (by decide +kernel)
theorem delayed_boundary : boundary delayed = 0 := by
  funext i j
  fin_cases i <;> fin_cases j <;> norm_num [boundary, delayed]
theorem delayed_run : run delayed = some [⟨0, 7, .essential⟩] := by
  have hp : pivotPairs delayed = [] := by
    simp only [pivotPairs, reduced, trace]
    rw [delayed_boundary]
    decide +kernel
  have he : essentialIndices delayed = [⟨0, by decide⟩] := by
    simp only [essentialIndices, reduced, trace]
    rw [delayed_boundary]
    rw [hp]
    decide +kernel
  simp [run, (validBool_iff delayed).mpr delayed_valid,
    occurrences, finiteOccurrences, essentialOccurrences, hp, he, degree]
  decide +kernel

def negative : Input :=
  [({0}, -4), ({1}, -4), ({0, 1}, -1)]
theorem negative_valid : Valid negative := (validBool_iff negative).mp (by decide +kernel)
def edgeMatrix : Matrix (Fin 3) (Fin 3) (ZMod 2) := fun r c =>
  if c.val = 2 then (if r.val = 0 ∨ r.val = 1 then 1 else 0) else 0
theorem negative_boundary : boundary negative = edgeMatrix := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [boundary, negative, edgeMatrix, Finset.orderEmbOfFin_apply,
      Finset.sort_insert, Finset.sort_singleton] <;> decide +kernel
theorem negative_run : run negative = some
    [⟨0, -4, .finite (-1)⟩, ⟨0, -4, .essential⟩] := by
  have hp : pivotPairs negative = [(⟨1, by decide⟩, ⟨2, by decide⟩)] := by
    simp only [pivotPairs, reduced, trace]
    rw [negative_boundary]
    decide +kernel
  have he : essentialIndices negative = [⟨0, by decide⟩] := by
    simp only [essentialIndices, reduced, trace]
    rw [negative_boundary]
    rw [hp]
    decide +kernel
  simp [run, (validBool_iff negative).mpr negative_valid,
    occurrences, finiteOccurrences, essentialOccurrences, hp, he,
    pairOccurrence, degree]
  decide +kernel

def twoEdges : Input :=
  [({0}, 0), ({1}, 0), ({2}, 0), ({3}, 0), ({0, 1}, 1), ({2, 3}, 1)]
theorem twoEdges_valid : Valid twoEdges :=
  (validBool_iff twoEdges).mp (by decide +kernel)
def twoEdgesMatrix : Matrix (Fin 6) (Fin 6) (ZMod 2) := fun r c =>
  if c.val = 4 then (if r.val = 0 ∨ r.val = 1 then 1 else 0)
  else if c.val = 5 then (if r.val = 2 ∨ r.val = 3 then 1 else 0)
  else 0
theorem twoEdges_boundary : boundary twoEdges = twoEdgesMatrix := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [boundary, twoEdges, twoEdgesMatrix, Finset.orderEmbOfFin_apply,
      Finset.sort_insert, Finset.sort_singleton] <;> decide +kernel
theorem twoEdges_run : run twoEdges = some
    [⟨0, 0, .finite 1⟩, ⟨0, 0, .finite 1⟩,
      ⟨0, 0, .essential⟩, ⟨0, 0, .essential⟩] := by
  have hp : pivotPairs twoEdges =
      [(⟨1, by decide⟩, ⟨4, by decide⟩),
        (⟨3, by decide⟩, ⟨5, by decide⟩)] := by
    simp only [pivotPairs, reduced, trace]
    rw [twoEdges_boundary]
    decide +kernel
  have he : essentialIndices twoEdges =
      [⟨0, by decide⟩, ⟨2, by decide⟩] := by
    simp only [essentialIndices, reduced, trace]
    rw [twoEdges_boundary]
    rw [hp]
    decide +kernel
  simp [run, (validBool_iff twoEdges).mpr twoEdges_valid,
    occurrences, finiteOccurrences, essentialOccurrences, hp, he,
    pairOccurrence, degree]
  decide +kernel

def reordered : Input :=
  [({0}, 0), ({1}, 0), ({2}, 0), ({1, 2}, 1), ({0, 1}, 1),
    ({0, 2}, 1), ({0, 1, 2}, 2)]

theorem reordered_valid : Valid reordered :=
  (validBool_iff reordered).mp (by decide +kernel)

def reorderedMatrix : Matrix (Fin 7) (Fin 7) (ZMod 2) := fun r c =>
  if c.val = 3 then (if r.val = 1 ∨ r.val = 2 then 1 else 0)
  else if c.val = 4 then (if r.val = 0 ∨ r.val = 1 then 1 else 0)
  else if c.val = 5 then (if r.val = 0 ∨ r.val = 2 then 1 else 0)
  else if c.val = 6 then (if r.val = 3 ∨ r.val = 4 ∨ r.val = 5 then 1 else 0)
  else 0

theorem reordered_boundary : boundary reordered = reorderedMatrix := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [boundary, reordered, reorderedMatrix, Finset.orderEmbOfFin_apply,
      Finset.sort_insert, Finset.sort_singleton] <;> decide +kernel

theorem reordered_run : run reordered = some
    [⟨0, 0, .finite 1⟩, ⟨0, 0, .finite 1⟩,
      ⟨1, 1, .finite 2⟩, ⟨0, 0, .essential⟩] := by
  have hp : pivotPairs reordered =
      [(⟨2, by decide⟩, ⟨3, by decide⟩),
        (⟨1, by decide⟩, ⟨4, by decide⟩),
        (⟨5, by decide⟩, ⟨6, by decide⟩)] := by
    simp only [pivotPairs, reduced, trace]
    rw [reordered_boundary]
    decide +kernel
  have he : essentialIndices reordered = [⟨0, by decide⟩] := by
    simp only [essentialIndices, reduced, trace]
    rw [reordered_boundary]
    rw [hp]
    decide +kernel
  simp [run, (validBool_iff reordered).mpr reordered_valid,
    occurrences, finiteOccurrences, essentialOccurrences, hp, he,
    pairOccurrence, degree]
  decide +kernel

theorem equal_grade_reordering (p : ℕ) :
    outputDiagram filled p = outputDiagram reordered p := by
  have hsame : occurrences filled = occurrences reordered := by
    have h := filled_run.trans reordered_run.symm
    simpa [run, (validBool_iff filled).mpr filled_valid,
      (validBool_iff reordered).mpr reordered_valid] using h
  simp [outputDiagram, hsame]

def sparse : Input :=
  [({10}, 0), ({40}, 0), ({900}, 0), ({10, 40}, 1), ({40, 900}, 1),
    ({10, 900}, 1), ({10, 40, 900}, 2)]

theorem sparse_valid : Valid sparse :=
  (validBool_iff sparse).mp (by decide +kernel)

theorem sparse_boundary : boundary sparse = triangleMatrix := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [boundary, sparse, triangleMatrix, Finset.orderEmbOfFin_apply,
      Finset.sort_insert, Finset.sort_singleton] <;> decide +kernel

theorem sparse_run : run sparse = some
    [⟨0, 0, .finite 1⟩, ⟨0, 0, .finite 1⟩,
      ⟨1, 1, .finite 2⟩, ⟨0, 0, .essential⟩] := by
  have hp : pivotPairs sparse =
      [(⟨1, by decide⟩, ⟨3, by decide⟩),
        (⟨2, by decide⟩, ⟨4, by decide⟩),
        (⟨5, by decide⟩, ⟨6, by decide⟩)] := by
    simp only [pivotPairs, reduced, trace]
    rw [sparse_boundary]
    decide +kernel
  have he : essentialIndices sparse = [⟨0, by decide⟩] := by
    simp only [essentialIndices, reduced, trace]
    rw [sparse_boundary]
    rw [hp]
    decide +kernel
  simp [run, (validBool_iff sparse).mpr sparse_valid,
    occurrences, finiteOccurrences, essentialOccurrences, hp, he,
    pairOccurrence, degree]
  decide +kernel

theorem sparse_absent_vertex :
    ({11} : Finset ℕ) ∉ complex sparse sparse_valid := by
  simpa only [mem_complex] using
    (show ({11} : Finset ℕ) ∉ faces sparse by decide +kernel)

def emptySimplex : Input := [(∅, 0)]
def duplicate : Input := [({0}, 0), ({0}, 1)]
def missingFace : Input := [({0}, 0), ({0, 1}, 1)]
def cofaceFirst : Input := [({0, 1}, 0), ({0}, 0), ({1}, 0)]
def decreasing : Input := [({0}, 1), ({1}, 0)]

theorem reject_empty_simplex : run emptySimplex = none := by decide +kernel
theorem reject_duplicate : run duplicate = none := by decide +kernel
theorem reject_missing_face : run missingFace = none := by decide +kernel
theorem reject_coface_first : run cofaceFirst = none := by decide +kernel
theorem reject_decreasing : run decreasing = none := by decide +kernel

/-- The rejected examples violate the full predicate, by validator completeness. -/
theorem rejected_invalid :
    ¬ Valid emptySimplex ∧ ¬ Valid duplicate ∧ ¬ Valid missingFace ∧
      ¬ Valid cofaceFirst ∧ ¬ Valid decreasing := by
  exact ⟨(run_eq_none_iff _).mp reject_empty_simplex,
    (run_eq_none_iff _).mp reject_duplicate,
    (run_eq_none_iff _).mp reject_missing_face,
    (run_eq_none_iff _).mp reject_coface_first,
    (run_eq_none_iff _).mp reject_decreasing⟩

/-- The duplicate H₀ finite point remains twice in the interpreted multiset. -/
theorem filled_zero_points : (outputDiagram filled 0).points =
    (([(0, (1 : WithTop ℤ)), (0, 1), (0, ⊤)] :
      List (ℤ × WithTop ℤ)) : Multiset (ℤ × WithTop ℤ)) := by
  have ho : occurrences filled =
      [⟨0, 0, .finite 1⟩, ⟨0, 0, .finite 1⟩,
        ⟨1, 1, .finite 2⟩, ⟨0, 0, .essential⟩] :=
    ((run_eq_some_iff _ _).mp filled_run).2.symm
  simp [outputDiagram, ho, Occurrence.point]

theorem hollow_one_points : (outputDiagram hollow 1).points =
    (([(1, (⊤ : WithTop ℤ))] : List (ℤ × WithTop ℤ)) :
      Multiset (ℤ × WithTop ℤ)) := by
  have ho : occurrences hollow =
      [⟨0, 0, .finite 1⟩, ⟨0, 0, .finite 1⟩,
        ⟨0, 0, .essential⟩, ⟨1, 1, .essential⟩] :=
    ((run_eq_some_iff _ _).mp hollow_run).2.symm
  simp [outputDiagram, ho, Occurrence.point]

theorem tied_one_points : (outputDiagram tied 1).points = 0 := by
  have ho : occurrences tied =
      [⟨0, 0, .finite 1⟩, ⟨0, 0, .finite 1⟩,
        ⟨0, 0, .essential⟩] :=
    ((run_eq_some_iff _ _).mp tied_run).2.symm
  simp [outputDiagram, ho, Occurrence.point]

/-! ## The tetrahedral boundary and its filling -/

open TDA.Persistence.Morse.MatchingInput

/-- All proper nonempty faces of the tetrahedron, graded by dimension. -/
def sphere : Input :=
  [({0}, 0), ({1}, 0), ({2}, 0), ({3}, 0),
   ({0, 1}, 1), ({0, 2}, 1), ({0, 3}, 1), ({1, 2}, 1), ({1, 3}, 1), ({2, 3}, 1),
   ({0, 1, 2}, 2), ({0, 1, 3}, 2), ({0, 2, 3}, 2), ({1, 2, 3}, 2)]

/-- The four triangles acquire a common filling at grade five. -/
def ball : Input := sphere ++ [({0, 1, 2, 3}, 5)]

theorem sphere_valid : Valid sphere := by decide +kernel
theorem ball_valid : Valid ball := by decide +kernel

/-- Bit i of column j records whether face i is a facet of face j in the input order. -/
def tetrahedralBoundary {n : ℕ} (i j : Fin n) : ZMod 2 :=
  let columns := #v[0, 0, 0, 0, 3, 5, 9, 6, 10, 12, 176, 336, 608, 896, 15360]
  if (columns[j.val]?.getD (0 : ℕ)).testBit i.val then 1 else 0

private theorem tetrahedralBoundary_eq (xs : Input)
    (h : (Vector.ofFn fun i : Fin xs.length => Vector.ofFn fun j : Fin xs.length =>
        coverIncidence xs i j) = (Vector.ofFn fun i : Fin xs.length =>
        Vector.ofFn fun j : Fin xs.length => tetrahedralBoundary i j)) :
    boundary xs = @tetrahedralBoundary xs.length := by
  rw [boundary_eq_coverIncidence]
  funext i j
  simpa only [Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta] using
    congrArg (fun rows : Vector (Vector (ZMod 2) xs.length) xs.length => rows[i][j]) h

theorem sphere_boundary : boundary sphere = @tetrahedralBoundary sphere.length :=
  tetrahedralBoundary_eq sphere (by decide +kernel)

theorem ball_boundary : boundary ball = @tetrahedralBoundary ball.length :=
  tetrahedralBoundary_eq ball (by decide +kernel)

theorem sphere_H2_run : (run sphere).map (List.filter fun r => r.degree == 2) =
    some [⟨2, 2, .essential⟩] := by
  simp only [run, (validBool_iff _).mpr sphere_valid, ↓reduceIte, Option.map_some]
  unfold occurrences finiteOccurrences essentialOccurrences essentialIndices pivotPairs reduced trace
  rw [sphere_boundary]
  decide +kernel

theorem ball_H2_run : (run ball).map (List.filter fun r => r.degree == 2) =
    some [⟨2, 2, .finite 5⟩] := by
  simp only [run, (validBool_iff _).mpr ball_valid, ↓reduceIte, Option.map_some]
  unfold occurrences finiteOccurrences essentialOccurrences essentialIndices pivotPairs reduced trace
  rw [ball_boundary]
  decide +kernel

end TDA.Persistence.Reduction.FiniteInput.Examples
