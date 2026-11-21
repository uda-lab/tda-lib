import TDA.Persistence.F2GridHomologyInput
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Rationally graded triangles

* `triangle`: vertices and edges at the origin, the 2-face at `(2, 2)`; `shiftedTriangle`: the
  same grading translated by `(1/2, 0)`. Both are valid, and their grid values are computed.
* Slices of `triangle`: hollow below the 2-face grade and at an incomparable grade, filled at
  `(2, 2)`, empty below every grade. Slices of `shiftedTriangle`: empty at the origin, hollow at
  `(1/2, 0)`, filled at `(5/2, 2)`. The 2-face is absent from the actual sublevel at `(1, 1)` and
  present at `(2, 2)`.
* The generated representations are valid, with no computation of their matrices.
* Rejected inputs: a non-monotone grading, an edge listed before a vertex, a missing vertex, a
  repeated face and the empty face.
* The empty input is valid and has no grid grades.
-/

set_option autoImplicit false

namespace TDA.Persistence.F2GridHomologyInputExamples

open TDA.Persistence RatGradedInput RatGrid

/-- The triangle on the vertices `0, 1, 2`: vertices and edges at the origin, the 2-face at
`(2, 2)`. -/
def triangle : RatGradedInput 3 2 :=
  [({0}, ![0, 0]), ({1}, ![0, 0]), ({2}, ![0, 0]),
    ({0, 1}, ![0, 0]), ({0, 2}, ![0, 0]), ({1, 2}, ![0, 0]), ({0, 1, 2}, ![2, 2])]

/-- The same complex with every grade translated by `(1/2, 0)`. -/
def shiftedTriangle : RatGradedInput 3 2 :=
  [({0}, ![1 / 2, 0]), ({1}, ![1 / 2, 0]), ({2}, ![1 / 2, 0]),
    ({0, 1}, ![1 / 2, 0]), ({0, 2}, ![1 / 2, 0]), ({1, 2}, ![1 / 2, 0]),
    ({0, 1, 2}, ![5 / 2, 2])]

/-- The triangle is valid input. -/
theorem triangle_valid : Valid triangle := by decide +kernel

/-- The translated triangle is valid input. -/
theorem shiftedTriangle_valid : Valid shiftedTriangle := by decide +kernel

/-- The grid values of `triangle` are `0` and `2` in both coordinates. -/
theorem triangle_gridValues :
    gridValues triangle 0 = [0, 2] ∧ gridValues triangle 1 = [0, 2] := by
  decide +kernel

/-- The translated grid values are `1/2`, `5/2` and `0`, `2`. -/
theorem shiftedTriangle_gridValues :
    gridValues shiftedTriangle 0 = [1 / 2, 5 / 2] ∧ gridValues shiftedTriangle 1 = [0, 2] := by
  decide +kernel

/-- Below the 2-face grade the slice is the hollow triangle, relabelled into `ℕ`. -/
theorem triangle_slice_hollow : slice triangle (![1, 1] : Fin 2 → ℚ) =
    [({0}, 0), ({1}, 0), ({2}, 0), ({0, 1}, 0), ({0, 2}, 0), ({1, 2}, 0)] := by
  decide +kernel

/-- At `(2, 2)` the slice is the filled triangle. -/
theorem triangle_slice_filled : slice triangle (![2, 2] : Fin 2 → ℚ) =
    [({0}, 0), ({1}, 0), ({2}, 0), ({0, 1}, 0), ({0, 2}, 0), ({1, 2}, 0), ({0, 1, 2}, 0)] := by
  decide +kernel

/-- Incomparable with the 2-face grade, the slice stays hollow. -/
theorem triangle_slice_incomparable : slice triangle (![5, 1] : Fin 2 → ℚ) =
    slice triangle (![1, 1] : Fin 2 → ℚ) := by
  decide +kernel

/-- Below every grade the slice is empty. -/
theorem triangle_slice_below : slice triangle (![-1, 5] : Fin 2 → ℚ) = [] := by decide +kernel

/-- At the origin the translated slice is empty, while that of `triangle` is hollow. -/
theorem shiftedTriangle_slice_origin : slice shiftedTriangle (![0, 0] : Fin 2 → ℚ) = [] := by
  decide +kernel

/-- At `(1/2, 0)` the translated slice is the hollow triangle. -/
theorem shiftedTriangle_slice_hollow : slice shiftedTriangle (![1 / 2, 0] : Fin 2 → ℚ) =
    [({0}, 0), ({1}, 0), ({2}, 0), ({0, 1}, 0), ({0, 2}, 0), ({1, 2}, 0)] := by
  decide +kernel

/-- At `(5/2, 2)` the translated slice is the filled triangle. -/
theorem shiftedTriangle_slice_filled : slice shiftedTriangle (![5 / 2, 2] : Fin 2 → ℚ) =
    [({0}, 0), ({1}, 0), ({2}, 0), ({0, 1}, 0), ({0, 2}, 0), ({1, 2}, 0), ({0, 1, 2}, 0)] := by
  decide +kernel

/-- The generated representations are valid, with no computation of their matrices. -/
theorem triangle_toF2GridRep_valid (p : ℕ) : (toF2GridRep triangle p).Valid :=
  toF2GridRep_valid triangle_valid p

/-- The generated representation of the translated triangle is valid. -/
theorem shiftedTriangle_toF2GridRep_valid (p : ℕ) : (toF2GridRep shiftedTriangle p).Valid :=
  toF2GridRep_valid shiftedTriangle_valid p

/-- The 2-face is absent from the actual sublevel at `(1, 1)` and present at `(2, 2)`. -/
theorem triangle_sublevel_face :
    ({0, 1, 2} : Finset (Fin 3)) ∉ (toGraded triangle triangle_valid).sublevel
      (realGrade (![1, 1] : Fin 2 → ℚ)) ∧
      ({0, 1, 2} : Finset (Fin 3)) ∈
        (toGraded triangle triangle_valid).sublevel
          (realGrade (![2, 2] : Fin 2 → ℚ)) := by
  simp only [mem_sublevel_toGraded_iff, realGrade_le_iff]
  decide +kernel

/-- A 2-face graded below one of its edges is rejected. -/
def nonMonotone : RatGradedInput 3 2 :=
  [({0}, ![0, 0]), ({1}, ![0, 0]), ({2}, ![0, 0]),
    ({0, 1}, ![0, 0]), ({0, 2}, ![0, 0]), ({1, 2}, ![1, 0]), ({0, 1, 2}, ![0, 3])]

/-- The non-monotone grading fails validation. -/
theorem nonMonotone_not_valid : ¬ Valid nonMonotone := by decide +kernel

/-- An edge listed before one of its vertices is rejected. -/
def unordered : RatGradedInput 2 1 := [({0}, ![0]), ({0, 1}, ![1]), ({1}, ![0])]

/-- The misordered list fails validation. -/
theorem unordered_not_valid : ¬ Valid unordered := by decide +kernel

/-- An edge without its vertices is rejected. -/
def missingVertex : RatGradedInput 2 1 := [({0, 1}, ![1])]

/-- The list with a missing vertex fails validation. -/
theorem missingVertex_not_valid : ¬ Valid missingVertex := by decide +kernel

/-- A face listed twice is rejected. -/
def duplicateFace : RatGradedInput 1 1 := [({0}, ![0]), ({0}, ![0])]

/-- The list with a repeated face fails validation. -/
theorem duplicateFace_not_valid : ¬ Valid duplicateFace := by decide +kernel

/-- The empty face is rejected. -/
def emptyFace : RatGradedInput 1 1 := [(∅, ![0])]

/-- The list with the empty face fails validation. -/
theorem emptyFace_not_valid : ¬ Valid emptyFace := by decide +kernel

/-- The empty input is valid. -/
theorem empty_valid : Valid ([] : RatGradedInput 0 2) := by decide +kernel

/-- The empty input has no grid grades. -/
theorem empty_points : (gridValues ([] : RatGradedInput 0 2)).points = ∅ := by decide +kernel

end TDA.Persistence.F2GridHomologyInputExamples
