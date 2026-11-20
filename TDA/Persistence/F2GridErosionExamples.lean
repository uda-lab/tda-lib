import TDA.Persistence.F2GridErosion
import TDA.Persistence.F2GridRepExamples

/-!
# Executed rank-erosion tests

* The interval module `[0, 1)` against the zero module: at radius `1/4` the test fails at the
  shifted breakpoint `1/4`, which is not a grid value, while every pair of original grid values
  passes; at radius `1/2` it passes. Both outcomes are transferred to `RankErosion` of the actual
  Kan extensions. Swapping the two modules reports the other direction.
* Two rays born at `0` and `1`: a passing comparison of nonzero modules at radius `1`, and a
  failure at radius `1/2`, reported with the other direction when the two modules are exchanged.
* Radius `0`, where the inequalities compare all ranks: a module against a second representation
  of itself on a different list passes, and against the zero module fails on the diagonal.
* An interval with negative grid values against `[0, 1)`, on different grids.
* No coordinates, two-parameter comparisons of a module with itself and with a different
  module, an empty value list, and invalid inputs: an invalid representation and a negative
  radius.
-/

set_option autoImplicit false

namespace TDA.Persistence.F2GridErosionExamples

open TDA.Persistence.Reduction RatGrid F2GridRep F2GridRepExamples

/-- The zero module on the grid `{0}`: every fiber is zero-dimensional. -/
def zero : F2GridRep 1 where
  values := fun _ => [0]
  dim := fun _ => 0
  map := fun _ _ => 0

theorem zero_valid : zero.Valid := by decide +kernel

theorem quarter_nonneg : (0 : ℚ) ≤ 1 / 4 := by norm_num

theorem half_nonneg : (0 : ℚ) ≤ 1 / 2 := by norm_num

/-- At radius `1/4` the test reports the first inequality at the pair `(1/4, 1/4)`: the
interval module has rank one from `0` to `1/2`, the zero module rank zero. -/
theorem interval_zero_quarter :
    runErosion interval zero (1 / 4) = .fail ⟨true, ![1 / 4], ![1 / 4], 1, 0⟩ := by
  decide +kernel

/-- The failing grade `1/4` is not a value of either grid. -/
theorem quarter_not_grid_value : (1 / 4 : ℚ) ∉ interval.values 0 ++ zero.values 0 := by
  decide +kernel

/-- Sampling only the original grid values `0` and `1` finds no failure at radius `1/4`. -/
theorem interval_zero_original_values_pass :
    ∀ p ∈ [![(0 : ℚ)], ![1]], ∀ q ∈ [![(0 : ℚ)], ![1]], p ≤ q →
      erosionFailureAt interval zero (1 / 4) p q = none := by
  decide +kernel

/-- The actual Kan extensions of the interval module and of zero do not satisfy erosion at
radius `1/4`. -/
theorem interval_zero_not_rankErosion :
    ¬ RankErosion (radius (1 / 4) quarter_nonneg)
      (interval.grid.lan.obj (interval.toModule interval_valid))
      (zero.grid.lan.obj (zero.toModule zero_valid)) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, h⟩ := runErosion_eq_fail _ _ _ _ interval_zero_quarter
  exact h

/-- With the modules swapped the second inequality is the one that fails. -/
theorem zero_interval_quarter :
    runErosion zero interval (1 / 4) = .fail ⟨false, ![1 / 4], ![1 / 4], 1, 0⟩ := by
  decide +kernel

theorem interval_zero_half : runErosion interval zero (1 / 2) = .pass := by decide +kernel

/-- At radius `1/2` the actual Kan extensions of the interval module and of zero satisfy
erosion. -/
theorem interval_zero_rankErosion :
    RankErosion (radius (1 / 2) half_nonneg)
      (interval.grid.lan.obj (interval.toModule interval_valid))
      (zero.grid.lan.obj (zero.toModule zero_valid)) := by
  obtain ⟨_, _, _, h⟩ := (runErosion_eq_pass_iff _ _ _).mp interval_zero_half
  exact h

/-- The ray born at `c`: one copy of `ZMod 2` from `c` onwards. -/
def ray (c : ℚ) : F2GridRep 1 where
  values := fun _ => [c]
  dim := fun _ => 1
  map := fun _ _ => Matrix.of fun _ _ => 1

theorem ray_zero_valid : (ray 0).Valid := by decide +kernel

theorem ray_one_valid : (ray 1).Valid := by decide +kernel

/-- Two nonzero modules on different grids pass at radius `1`. -/
theorem rays_one : runErosion (ray 0) (ray 1) 1 = .pass := by decide +kernel

theorem rays_rankErosion :
    RankErosion (radius 1 zero_le_one) ((ray 0).grid.lan.obj ((ray 0).toModule ray_zero_valid))
      ((ray 1).grid.lan.obj ((ray 1).toModule ray_one_valid)) := by
  obtain ⟨_, _, _, h⟩ := (runErosion_eq_pass_iff _ _ _).mp rays_one
  exact h

/-- At radius `1/2` the ray born at `0` already has rank one from `0` to `3/2`, while the ray
born at `1` is zero at `1/2`. -/
theorem rays_half : runErosion (ray 0) (ray 1) (1 / 2) = .fail ⟨true, ![1 / 2], ![1], 1, 0⟩ := by
  decide +kernel

theorem rays_half_swapped :
    runErosion (ray 1) (ray 0) (1 / 2) = .fail ⟨false, ![1 / 2], ![1], 1, 0⟩ := by
  decide +kernel

/-- At radius `0`, two representations of the same module on different lists pass. -/
theorem interval_messy_zero : runErosion interval messy 0 = .pass := by decide +kernel

/-- At radius `0` the diagonal pair `(0, 0)` separates the interval module from zero. -/
theorem interval_zero_zero :
    runErosion interval zero 0 = .fail ⟨true, ![0], ![0], 1, 0⟩ := by
  decide +kernel

/-- The interval module `[-2, -1)`, on negative grid values. -/
def shifted : F2GridRep 1 where
  values := fun _ => [-2, -1]
  dim := fun a => if a 0 = -2 then 1 else 0
  map := fun _ _ => Matrix.of fun _ _ => 1

theorem shifted_valid : shifted.Valid := by decide +kernel

/-- Two unit intervals on different grids pass at radius `1/2`. -/
theorem shifted_interval_half : runErosion shifted interval (1 / 2) = .pass := by decide +kernel

/-- At radius `1/4` they fail at the negative shifted breakpoint `-7/4 = -2 + 1/4`. -/
theorem shifted_interval_quarter :
    runErosion shifted interval (1 / 4) = .fail ⟨true, ![-7 / 4], ![-7 / 4], 1, 0⟩ := by
  decide +kernel

/-- A second module with no coordinates, of dimension two. -/
def noCoordinatesTwo : F2GridRep 0 where
  values := fun i => i.elim0
  dim := fun _ => 2
  map := fun _ _ => Matrix.of fun i j => if (i : ℕ) = (j : ℕ) then 1 else 0

/-- With no coordinates a module passes against itself at any radius. -/
theorem noCoordinates_self : runErosion noCoordinates noCoordinates 3 = .pass := by
  decide +kernel

/-- Fibers of different dimensions fail at the single grade, at any radius. -/
theorem noCoordinates_differ :
    runErosion noCoordinates noCoordinatesTwo 3 = .fail ⟨true, ![], ![], 3, 2⟩ := by
  decide +kernel

/-- A two-parameter module against itself at radius `0`. -/
theorem plane_self_zero : runErosion plane plane 0 = .pass := by decide +kernel

/-- A two-parameter module against itself at radius `1/2`. -/
theorem plane_self_half : runErosion plane plane (1 / 2) = .pass := by decide +kernel

/-- A two-parameter module with one-dimensional fibers and identity maps. -/
def flat : F2GridRep 2 where
  values := fun _ => [0, 1]
  dim := fun _ => 1
  map := fun _ _ => Matrix.of fun _ _ => 1

theorem flat_valid : flat.Valid := by decide +kernel

/-- At radius `0` two different two-parameter modules fail on the diagonal at the origin, where
their fibers have dimensions two and one. -/
theorem plane_flat_zero :
    runErosion plane flat 0 = .fail ⟨true, ![0, 0], ![0, 0], 2, 1⟩ := by
  decide +kernel

/-- At radius `1` the same two modules pass. -/
theorem plane_flat_one : runErosion plane flat 1 = .pass := by decide +kernel

/-- The first representation has an empty value list, hence no grid grade and a zero Kan
extension. The breakpoint grid still has the value of the second grid and its shifts, and the
comparison with the zero module passes there. -/
theorem emptyGrid_zero : runErosion emptyGrid zero 1 = .pass := by decide +kernel

/-- An invalid representation is reported as invalid input, not as failed erosion. -/
theorem badComposition_invalid : runErosion badComposition interval 1 = .invalid := by
  decide +kernel

/-- A negative radius is invalid input. -/
theorem negative_radius_invalid : runErosion interval zero (-1) = .invalid := by decide +kernel

end TDA.Persistence.F2GridErosionExamples
