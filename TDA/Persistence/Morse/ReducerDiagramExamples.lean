import TDA.Persistence.Morse.ReducerDiagram

/-!
# Fixtures for the graded reducer output

Evaluations of `TDA.Persistence.Morse.ReducerDiagram` over `ZMod 2`, on written-out matrices.

* P1. A hollow triangle with staggered edges: vertices `0, 1, 2` at grade 0, edges
  `3 = 01` and `4 = 12` at grade 1 and `5 = 02` at grade 2. The reducer adds columns 4 and 3 to
  column 5, which becomes zero. The pivot pairs are `(1, 3)` and `(2, 4)`, the essential indices
  `0` and `5`; the degree-0 diagram is `{(0, 1), (0, 1), (0, ⊤)}` and the degree-1 diagram
  `{(2, ⊤)}`.
* P2. The Morse complex of the path fixture R2 of `TDA.Persistence.Morse.ReducerOrderExamples`
  in its reducer order A, C, AB, all at grade 0: the matrix with entries in rows 0 and 1 of
  column 2. The pivot pair `(1, 2)` has equal grades and is dropped; the only occurrence is the
  essential `(0, ⊤)` of degree 0.
* P3. The Morse complex of the square fixture R3 of
  `TDA.Persistence.Morse.ReducerOrderExamples` in its reducer order, with degrees and grades
  `0, 1, 2`: the matrix with the single entry in row 1 and column 2. The degree-1 diagram is
  `{(1, 2)}` and the degree-0 diagram `{(0, ⊤)}`.

The pivot pairs, essential indices, occurrences, diagrams and the hypotheses of the rank
theorem are evaluated by kernel `decide`. The rank statements rewrite with
`rankOfStructureMap_eq_countP` and evaluate the slice count by kernel `decide`.
-/

set_option autoImplicit false

namespace TDA.Persistence.Morse.ReducerDiagramExamples

open TDA.Persistence.Reduction TDA.Persistence.Morse.Cancellation
open TDA.Persistence.Morse.ReducerDiagram

/-! ## P1. A hollow triangle with staggered edges -/

/-- The boundary matrix of the hollow triangle with vertices `0, 1, 2` and edges
`3 = 01`, `4 = 12`, `5 = 02`. -/
def triD : Matrix (Fin 6) (Fin 6) (ZMod 2) := Matrix.of fun i j =>
  if (i.val, j.val) ∈ [(0, 3), (1, 3), (1, 4), (2, 4), (0, 5), (2, 5)] then 1 else 0

/-- Vertices have degree 0, edges degree 1. -/
def triDegree (i : Fin 6) : ℕ := if i.val < 3 then 0 else 1

/-- Vertices at grade 0, the edges `01` and `12` at grade 1, the edge `02` at grade 2. -/
def triGrade (i : Fin 6) : ℤ := if i.val < 3 then 0 else if i.val < 5 then 1 else 2

/-- `triD` squares to zero. -/
theorem tri_sq_zero : triD * triD = 0 := by decide +kernel

/-- `triD` is strictly upper triangular. -/
theorem tri_strictBoundary : StrictBoundary triD := by decide +kernel

/-- `triD` lowers `triDegree` by one. -/
theorem tri_lowersDegree : LowersDegree triDegree triD := by decide +kernel

/-- `triGrade` is monotone. -/
theorem tri_monotone : Monotone triGrade := by
  intro i j hij
  simp only [triGrade]
  split_ifs <;> omega

/-- The pivot pairs of `triD` are `(1, 3)` and `(2, 4)`. -/
theorem tri_pivotPairs : pivotPairs triD = [(1, 3), (2, 4)] := by decide +kernel

/-- The essential indices of `triD` are `0` and `5`. -/
theorem tri_essentialIndices : essentialIndices triD = [0, 5] := by decide +kernel

/-- The occurrences of `triD`. -/
theorem tri_occurrences :
    occurrences triDegree triGrade triD =
      [⟨0, 0, .finite 1⟩, ⟨0, 0, .finite 1⟩, ⟨0, 0, .essential⟩, ⟨1, 2, .essential⟩] := by
  decide +kernel

/-- The degree-0 diagram of `triD` is `{(0, 1), (0, 1), (0, ⊤)}`. -/
theorem tri_diagram_zero :
    (diagram triDegree triGrade triD 0).points = {(0, 1), (0, 1), (0, ⊤)} := by
  decide +kernel

/-- The degree-1 diagram of `triD` is `{(2, ⊤)}`. -/
theorem tri_diagram_one : (diagram triDegree triGrade triD 1).points = {(2, ⊤)} := by
  decide +kernel

/-- In degree 0, the structure map `0 ≤ 0` has rank 3 (three components at grade 0) and the
structure map `0 ≤ 1` rank 1 (they merge by grade 1). -/
theorem tri_rank_zero :
    rankOfStructureMap (sublevelHomologyPModule triDegree triGrade triD 0)
        (le_refl (0 : ℤ)) = 3 ∧
      rankOfStructureMap (sublevelHomologyPModule triDegree triGrade triD 0)
        (show (0 : ℤ) ≤ 1 by decide) = 1 := by
  rw [rankOfStructureMap_eq_countP tri_sq_zero tri_strictBoundary tri_lowersDegree tri_monotone,
    rankOfStructureMap_eq_countP tri_sq_zero tri_strictBoundary tri_lowersDegree tri_monotone]
  decide +kernel

/-- In degree 1, the structure map `1 ≤ 2` has rank 0 and the structure map `2 ≤ 5` rank 1: the
cycle is born at grade 2 and never dies. -/
theorem tri_rank_one :
    rankOfStructureMap (sublevelHomologyPModule triDegree triGrade triD 1)
        (show (1 : ℤ) ≤ 2 by decide) = 0 ∧
      rankOfStructureMap (sublevelHomologyPModule triDegree triGrade triD 1)
        (show (2 : ℤ) ≤ 5 by decide) = 1 := by
  rw [rankOfStructureMap_eq_countP tri_sq_zero tri_strictBoundary tri_lowersDegree tri_monotone,
    rankOfStructureMap_eq_countP tri_sq_zero tri_strictBoundary tri_lowersDegree tri_monotone]
  decide +kernel

/-! ## P2. The path in its reducer order -/

/-- The Morse differential of the path fixture R2 in its reducer order A, C, AB:
`d AB = A + C`. -/
def pathD : Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  Matrix.of fun i j => if j.val = 2 ∧ i.val < 2 then 1 else 0

/-- A and C have degree 0, AB degree 1. -/
def pathDegree (i : Fin 3) : ℕ := if i.val = 2 then 1 else 0

/-- All three generators are at grade 0. -/
def pathGrade (_ : Fin 3) : ℤ := 0

/-- The pivot pair of `pathD` is `(1, 2)`, at equal grades. -/
theorem path_pivotPairs : pivotPairs pathD = [(1, 2)] := by decide +kernel

/-- The equal-grade pair is dropped; the only occurrence is the essential `(0, ⊤)` of degree 0. -/
theorem path_occurrences : occurrences pathDegree pathGrade pathD = [⟨0, 0, .essential⟩] := by
  decide +kernel

/-- The degree-0 diagram of `pathD` is `{(0, ⊤)}` and the degree-1 diagram is empty. -/
theorem path_diagram :
    (diagram pathDegree pathGrade pathD 0).points = {(0, ⊤)} ∧
      (diagram pathDegree pathGrade pathD 1).points = 0 := by
  decide +kernel

/-! ## P3. The square in its reducer order -/

/-- The Morse differential of the square fixture R3 in its reducer order: `d 2 = 1`. -/
def sqD : Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  Matrix.of fun i j => if i.val = 1 ∧ j.val = 2 then 1 else 0

/-- The degree of the generator at position `i` is `i`. -/
def sqDegree (i : Fin 3) : ℕ := i.val

/-- The grade of the generator at position `i` is `i`. -/
def sqGrade (i : Fin 3) : ℤ := i.val

/-- The occurrences of `sqD`: the pair `(1, 2)` in degree 1 and the essential `(0, ⊤)` in
degree 0. -/
theorem sq_occurrences :
    occurrences sqDegree sqGrade sqD = [⟨1, 1, .finite 2⟩, ⟨0, 0, .essential⟩] := by
  decide +kernel

/-- The degree-1 diagram of `sqD` is `{(1, 2)}` and the degree-0 diagram `{(0, ⊤)}`. -/
theorem sq_diagram :
    (diagram sqDegree sqGrade sqD 1).points = {(1, 2)} ∧
      (diagram sqDegree sqGrade sqD 0).points = {(0, ⊤)} := by
  decide +kernel

/-- In degree 1, the structure map `1 ≤ 1` has rank 1 and the structure map `1 ≤ 2` rank 0. -/
theorem sq_rank_one :
    rankOfStructureMap (sublevelHomologyPModule sqDegree sqGrade sqD 1) (le_refl (1 : ℤ)) = 1 ∧
      rankOfStructureMap (sublevelHomologyPModule sqDegree sqGrade sqD 1)
        (show (1 : ℤ) ≤ 2 by decide) = 0 := by
  have hD2 : sqD * sqD = 0 := by decide +kernel
  have hs : StrictBoundary sqD := by decide +kernel
  have hd : LowersDegree sqDegree sqD := by decide +kernel
  have hg : Monotone sqGrade := fun _ _ h => Int.ofNat_le.mpr h
  rw [rankOfStructureMap_eq_countP hD2 hs hd hg, rankOfStructureMap_eq_countP hD2 hs hd hg]
  decide +kernel

end TDA.Persistence.Morse.ReducerDiagramExamples
