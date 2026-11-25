import TDA.Persistence.F2GridRep
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Executed F₂ grid representations

* `interval`: the interval module `[0, 1)` on the values `0, 1`, with executed ranks inside,
  before and after the interval, at a grid value against a grade just below it, and at a pair
  whose floors differ; one rank is transferred to the actual Kan extension.
* `messy`: the same module from an unsorted list with a repeated value and a different
  off-grid dimension; the executed ranks agree.
* `plane`: a two-parameter representation with a two-dimensional fiber and a rank-one,
  non-identity structure map.
* Two invalid representations, rejected for a composition failure and for a non-identity
  diagonal matrix.
* Degenerate cases: no coordinates, and an empty value list. A zero-dimensional fiber occurs
  in `interval` at the grid value `1`.
-/

set_option autoImplicit false

namespace TDA.Persistence.F2GridRepExamples

open TDA.Persistence.Reduction RatGrid

/-- The interval module `[0, 1)`: one copy of `ZMod 2` at `0`, zero at `1`. -/
def interval : F2GridRep 1 where
  values := fun _ => [0, 1]
  dim := fun a => if a 0 = 0 then 1 else 0
  map := fun _ _ => Matrix.of fun _ _ => 1

theorem interval_valid : interval.Valid := by decide +kernel

/-- Inside the interval the rank is one, also at a grade between the grid values. -/
theorem interval_rank_inside : interval.rankAt ![0] ![1 / 2] = 1 := by decide +kernel

/-- A negative source grade has no lower grid value. -/
theorem interval_rank_before : interval.rankAt ![-1] ![1 / 2] = 0 := by decide +kernel

/-- After the interval the fiber is zero-dimensional. -/
theorem interval_rank_after : interval.rankAt ![1] ![2] = 0 := by decide +kernel

/-- Exactly on the grid value `1` the fiber is zero. -/
theorem interval_rank_at_one : interval.rankAt ![1] ![1] = 0 := by decide +kernel

/-- Just below `1` the floor is still `0`. -/
theorem interval_rank_below_one : interval.rankAt ![999 / 1000] ![999 / 1000] = 1 := by
  decide +kernel

/-- The two floors differ: the map from the fiber at `0` to the fiber at `1` is zero. -/
theorem interval_rank_across : interval.rankAt ![1 / 2] ![1] = 0 := by decide +kernel

theorem interval_inside_le : (![0] : Fin 1 → ℚ) ≤ ![1 / 2] := by decide +kernel

/-- The executed value is the rank of the actual Kan extension from `0` to `1/2`. -/
theorem interval_extension_rank_inside :
    rankOfStructureMap (interval.grid.lan.obj (interval.toModule interval_valid))
      (realGrade_le_iff.mpr interval_inside_le) = 1 := by
  rw [← interval.rankAt_eq interval_valid interval_inside_le]
  exact interval_rank_inside

theorem interval_across_le : (![1 / 2] : Fin 1 → ℚ) ≤ ![1] := by decide +kernel

/-- The actual Kan extension has rank zero from `1/2` to `1`. -/
theorem interval_extension_rank_across :
    rankOfStructureMap (interval.grid.lan.obj (interval.toModule interval_valid))
      (realGrade_le_iff.mpr interval_across_le) = 0 := by
  rw [← interval.rankAt_eq interval_valid interval_across_le]
  exact interval_rank_across

/-- The same module from an unsorted list with a repeated value; off the grid the dimension
is `5`, which no theorem reads. -/
def messy : F2GridRep 1 where
  values := fun _ => [1, 0, 1]
  dim := fun a => if a 0 = 0 then 1 else if a 0 = 1 then 0 else 5
  map := fun _ _ => Matrix.of fun _ _ => 1

theorem messy_valid : messy.Valid := by decide +kernel

theorem messy_rank_inside : messy.rankAt ![0] ![1 / 2] = 1 := by decide +kernel

theorem messy_rank_across : messy.rankAt ![1 / 2] ![1] = 0 := by decide +kernel

/-- Above the grid the floor is the grid value `1`, not the off-grid grade `7`. -/
theorem messy_rank_above : messy.rankAt ![7] ![7] = 0 := by decide +kernel

/-- Fiber dimensions of `plane`: two at the origin, one elsewhere. -/
def planeDim (a : Fin 2 → ℚ) : ℕ := if a 0 = 0 ∧ a 1 = 0 then 2 else 1

/-- A two-parameter representation on the four grades with coordinates `0, 1`: the fiber at
the origin is two-dimensional and maps onto each other fiber by the sum of coordinates; the
other structure maps are identities. -/
def plane : F2GridRep 2 where
  values := fun _ => [0, 1]
  dim := planeDim
  map := fun a b => Matrix.of fun i j =>
    if planeDim a = planeDim b then (if (i : ℕ) = (j : ℕ) then 1 else 0) else 1

theorem plane_valid : plane.Valid := by decide +kernel

/-- The fiber at the origin has dimension two. -/
theorem plane_rank_origin : plane.rankAt ![0, 0] ![0, 0] = 2 := by decide +kernel

/-- The map out of the origin is not an identity and has rank one. -/
theorem plane_rank_out : plane.rankAt ![0, 0] ![1, 0] = 1 := by decide +kernel

/-- The source grade lies between grid values in the first coordinate and has the origin as its
floor; the target grade also lies above the grid values in the second coordinate and has floor
`(0, 1)`. The map between the two floors is the rank-one map out of the origin. -/
theorem plane_rank_between : plane.rankAt ![1 / 2, 0] ![1 / 2, 3] = 1 := by decide +kernel

theorem plane_out_le : (![0, 0] : Fin 2 → ℚ) ≤ ![1, 0] := by decide +kernel

/-- The actual Kan extension has rank one from the origin to `(1, 0)`. -/
theorem plane_extension_rank_out :
    rankOfStructureMap (plane.grid.lan.obj (plane.toModule plane_valid))
      (realGrade_le_iff.mpr plane_out_le) = 1 := by
  rw [← plane.rankAt_eq plane_valid plane_out_le]
  exact plane_rank_out

/-- The composite from `0` to `2` through `1` is not the stored matrix. -/
def badComposition : F2GridRep 1 where
  values := fun _ => [0, 1, 2]
  dim := fun _ => 1
  map := fun a b => Matrix.of fun _ _ => if a 0 = 0 ∧ b 0 = 2 then 0 else 1

theorem badComposition_not_valid : ¬ badComposition.Valid := by decide +kernel

/-- The diagonal matrix is zero, not the identity. -/
def badIdentity : F2GridRep 1 where
  values := fun _ => [0]
  dim := fun _ => 1
  map := fun _ _ => 0

theorem badIdentity_not_valid : ¬ badIdentity.Valid := by decide +kernel

/-- With no coordinates there is one grade; its fiber has dimension three. -/
def noCoordinates : F2GridRep 0 where
  values := fun i => i.elim0
  dim := fun _ => 3
  map := fun _ _ => Matrix.of fun i j => if (i : ℕ) = (j : ℕ) then 1 else 0

theorem noCoordinates_valid : noCoordinates.Valid := by decide +kernel

theorem noCoordinates_rank : noCoordinates.rankAt ![] ![] = 3 := by decide +kernel

/-- An empty value list: there is no grid grade, every representation is valid and every
executed rank is zero. -/
def emptyGrid : F2GridRep 1 where
  values := fun _ => []
  dim := fun _ => 4
  map := fun _ _ => 0

theorem emptyGrid_valid : emptyGrid.Valid := by decide +kernel

theorem emptyGrid_rank : emptyGrid.rankAt ![0] ![5] = 0 := by decide +kernel

end TDA.Persistence.F2GridRepExamples
