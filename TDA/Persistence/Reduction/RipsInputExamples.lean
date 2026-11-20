import TDA.Persistence.Reduction.RipsInput
import Mathlib.Data.Fin.VecNotation

/-!
# Executed Rips simplex lists from integer distance tables

Each fixture states the complete value of `DistanceTable.ripsInput?`.

* `empty`, `single`, `pair`: no label, one label, two labels at distance `3`. The occurrence
  records of `ripsRun` are checked for all three.
* `tied`: three labels at mutual distance `2`; the four faces of grade `2` are listed by
  cardinality and then lexicographically.
* `line`, `relabelled`: three points on a line, and the same points with two labels exchanged.
  The lists differ in their faces and have the same grades.
* `fourCycle`: the shortest-path metric of the four-cycle, with adjacent distance `1` and
  opposite distance `2`. The edges enter at `1` and both diagonals and all larger faces at `2`.
  The integer grade of a diagonal is transferred to the value of the actual `Rips.filter`.
* `oneWay`, `merged`, `shortcut`, `loop`, `negative`: tables violating symmetry, separation,
  the triangle inequality, the zero diagonal and nonnegativity; each is reported as `none`, by
  `ripsInput?` and by `ripsRun`.
-/

set_option autoImplicit false

namespace TDA.Persistence.Reduction.RipsInputExamples

open DistanceTable FiniteInput TDA.Simplicial TDA.Filtration

/-- No label. -/
def empty : DistanceTable 0 := ⟨fun i _ => i.elim0⟩

theorem empty_ripsInput : empty.ripsInput? = some [] := by decide +kernel

theorem empty_ripsRun : empty.ripsRun = some [] := by decide +kernel

/-- One label. -/
def single : DistanceTable 1 := ⟨![![0]]⟩

theorem single_ripsInput : single.ripsInput? = some [({0}, 0)] := by decide +kernel

theorem single_ripsRun : single.ripsRun = some [⟨0, 0, .essential⟩] := by decide +kernel

/-- Two labels at distance `3`. -/
def pair : DistanceTable 2 := ⟨![![0, 3], ![3, 0]]⟩

/-- The simplex list of `pair`. -/
def pairInput : Input := [({0}, 0), ({1}, 0), ({0, 1}, 3)]

theorem pair_valid : pair.Valid := by decide +kernel

theorem pair_ripsInput_eq : pair.ripsInput = pairInput := by decide +kernel

theorem pair_ripsInput : pair.ripsInput? = some [({0}, 0), ({1}, 0), ({0, 1}, 3)] := by
  decide +kernel

/-- The boundary matrix of one edge on two vertices. -/
def edgeMatrix : Matrix (Fin 3) (Fin 3) (ZMod 2) := fun r c =>
  if c.val = 2 then (if r.val = 0 ∨ r.val = 1 then 1 else 0) else 0

theorem pair_boundary : FiniteInput.boundary pairInput = edgeMatrix := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [FiniteInput.boundary, pairInput, edgeMatrix, Finset.orderEmbOfFin_apply,
      Finset.sort_insert, Finset.sort_singleton] <;> decide +kernel

/-- The two points merge at their distance: one finite and one essential class in degree
zero. -/
theorem pair_ripsRun : pair.ripsRun = some [⟨0, 0, .finite 3⟩, ⟨0, 0, .essential⟩] := by
  rw [ripsRun_eq_some_iff, pair_ripsInput_eq]
  refine ⟨pair_valid, ?_⟩
  have hp : pivotPairs pairInput = [(⟨1, by decide⟩, ⟨2, by decide⟩)] := by
    simp only [pivotPairs, reduced, trace]
    rw [pair_boundary]
    decide +kernel
  have he : essentialIndices pairInput = [⟨0, by decide⟩] := by
    simp only [essentialIndices, reduced, trace]
    rw [pair_boundary]
    rw [hp]
    decide +kernel
  simp [occurrences, finiteOccurrences, essentialOccurrences, hp, he, pairOccurrence, degree]
  decide +kernel

/-- Three labels at mutual distance `2`: all faces of positive dimension are tied. -/
def tied : DistanceTable 3 := ⟨![![0, 2, 2], ![2, 0, 2], ![2, 2, 0]]⟩

theorem tied_ripsInput :
    tied.ripsInput? = some [({0}, 0), ({1}, 0), ({2}, 0),
      ({0, 1}, 2), ({0, 2}, 2), ({1, 2}, 2), ({0, 1, 2}, 2)] := by
  decide +kernel

/-- Three labels on a line at positions `0`, `1`, `3`. -/
def line : DistanceTable 3 := ⟨![![0, 1, 3], ![1, 0, 2], ![3, 2, 0]]⟩

theorem line_ripsInput :
    line.ripsInput? = some [({0}, 0), ({1}, 0), ({2}, 0),
      ({0, 1}, 1), ({1, 2}, 2), ({0, 2}, 3), ({0, 1, 2}, 3)] := by
  decide +kernel

/-- The points of `line` with the labels `0` and `1` exchanged. -/
def relabelled : DistanceTable 3 := ⟨![![0, 1, 2], ![1, 0, 3], ![2, 3, 0]]⟩

theorem relabelled_dist (i j : Fin 3) :
    relabelled.dist i j = line.dist (Equiv.swap 0 1 i) (Equiv.swap 0 1 j) := by
  revert i j
  decide +kernel

theorem relabelled_ripsInput :
    relabelled.ripsInput? = some [({0}, 0), ({1}, 0), ({2}, 0),
      ({0, 1}, 1), ({0, 2}, 2), ({1, 2}, 3), ({0, 1, 2}, 3)] := by
  decide +kernel

/-- Relabelling changes the listed faces and not the grades. -/
theorem relabelled_grades :
    relabelled.ripsInput.map Prod.snd = line.ripsInput.map Prod.snd := by
  decide +kernel

/-- The shortest-path metric of the four-cycle. -/
def fourCycle : DistanceTable 4 :=
  ⟨![![0, 1, 2, 1], ![1, 0, 1, 2], ![2, 1, 0, 1], ![1, 2, 1, 0]]⟩

theorem fourCycle_valid : fourCycle.Valid := by decide +kernel

theorem fourCycle_ripsInput :
    fourCycle.ripsInput? = some [({0}, 0), ({1}, 0), ({2}, 0), ({3}, 0),
      ({0, 1}, 1), ({0, 3}, 1), ({1, 2}, 1), ({2, 3}, 1),
      ({0, 2}, 2), ({1, 3}, 2),
      ({0, 1, 2}, 2), ({0, 1, 3}, 2), ({0, 2, 3}, 2), ({1, 2, 3}, 2),
      ({0, 1, 2, 3}, 2)] := by
  decide +kernel

/-- A diagonal of the four-cycle as a face of the full complex on the labels. -/
def diagonal : TotalFace (Rips.fullComplex (Fin 4)) := ⟨{0, 2}, ⟨0, by decide⟩⟩

/-- The listed grade of the diagonal is the value of the actual Rips filter for the table
metric. -/
theorem fourCycle_diagonal :
    (Rips.filter (fourCycle.metric fourCycle_valid)).value diagonal = 2 := by
  rw [← gradeFilter_ripsFace, gradeFilter_ripsFace_eq_diameter]
  have h : fourCycle.diameter diagonal.1 = 2 := by decide +kernel
  rw [h]
  norm_num

/-- The diagonal is listed with grade `2`. -/
theorem fourCycle_diagonal_mem : (({0, 2} : Finset ℕ), (2 : ℤ)) ∈ fourCycle.ripsInput := by
  decide +kernel

/-- An asymmetric table. -/
def oneWay : DistanceTable 2 := ⟨![![0, 1], ![2, 0]]⟩

theorem oneWay_ripsInput : oneWay.ripsInput? = none := by decide +kernel

theorem oneWay_ripsRun : oneWay.ripsRun = none := by decide +kernel

/-- Two distinct labels at distance `0`. -/
def merged : DistanceTable 2 := ⟨![![0, 0], ![0, 0]]⟩

theorem merged_ripsInput : merged.ripsInput? = none := by decide +kernel

theorem merged_ripsRun : merged.ripsRun = none := by decide +kernel

/-- A table violating the triangle inequality: `3 > 1 + 1`. -/
def shortcut : DistanceTable 3 := ⟨![![0, 1, 3], ![1, 0, 1], ![3, 1, 0]]⟩

theorem shortcut_ripsInput : shortcut.ripsInput? = none := by decide +kernel

theorem shortcut_ripsRun : shortcut.ripsRun = none := by decide +kernel

/-- A nonzero diagonal entry. -/
def loop : DistanceTable 1 := ⟨![![1]]⟩

theorem loop_ripsInput : loop.ripsInput? = none := by decide +kernel

theorem loop_ripsRun : loop.ripsRun = none := by decide +kernel

/-- A negative entry. -/
def negative : DistanceTable 2 := ⟨![![0, -1], ![-1, 0]]⟩

theorem negative_ripsInput : negative.ripsInput? = none := by decide +kernel

theorem negative_ripsRun : negative.ripsRun = none := by decide +kernel

end TDA.Persistence.Reduction.RipsInputExamples
