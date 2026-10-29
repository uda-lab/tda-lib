import TDA.Persistence.RectangleSharpExample
import Mathlib.Data.ZMod.Basic

/-!
# Consumers of the sharp rectangle example

These consumers read the actual component coefficients, instantiate the
distance equalities in characteristic two, and exclude small interleaving
and matching radii through the public obstruction theorems.
-/

set_option autoImplicit false

namespace TDA.Persistence.RectangleSharpExample.Examples

open CategoryTheory CoordinateShift RectangleFamily RectangleHall RectangleMatching
open scoped TDA.Persistence NNReal ENNReal Classical ZeroObject

/-- Both sharp distances hold over the two-element field. -/
theorem characteristic_two_distances :
    coordinateInterleavingDistance (module (k := ZMod 2) source) (module target) = 1 ∧
      bottleneckDistance (k := ZMod 2) source target = 3 :=
  ⟨interleavingDistance_eq_one, bottleneckDistance_eq_three⟩

/-- The negative matrix entry becomes positive in characteristic two,
and still belongs to the verified actual interleaving. -/
theorem characteristic_two_reverse_entry :
    shiftedCoefficient (target 0) (source 0) 1
      (component target source 1 (interleaving (k := ZMod 2)).ψ 0 0) = 1 := by
  rw [reverse_component_coefficient]
  decide

/-- Over the rationals the reverse coefficient has the source's minus sign. -/
theorem rational_signed_entry :
    shiftedCoefficient (target 0) (source 0) 1
      (component target source 1 (interleaving (k := ℚ)).ψ 0 0) = -1 :=
  reverse_component_coefficient 0 0

/-- A zero matrix entry is an actual zero natural transformation. -/
theorem forward_zero_component :
    component source target 1 (interleaving (k := ℚ)).φ 1 2 = 0 := by
  by_contra h
  have hc := (shiftedCoefficient_ne_zero_iff _ _ _ _).mpr h
  exact hc (forward_component_coefficient 1 2)

/-- A nonzero matrix entry is an actual nonzero natural transformation. -/
theorem forward_nonzero_component :
    component source target 1 (interleaving (k := ℚ)).φ 1 0 ≠ 0 := by
  apply (shiftedCoefficient_ne_zero_iff _ _ _ _).mp
  rw [forward_component_coefficient]
  norm_num

/-- There is no radius-zero witness, although a radius-one witness is explicit. -/
theorem zero_excluded_one_attained :
    ¬ Nonempty (CoordinateInterleaving 0 (module (k := ℚ) source) (module target)) ∧
      Nonempty (CoordinateInterleaving 1 (module (k := ℚ) source) (module target)) := by
  refine ⟨?_, ⟨interleaving⟩⟩
  rintro ⟨I⟩
  have h := interleaving_radius_ge_one I
  norm_num at h

/-- Every smaller matching radius is excluded, independently of how pairs
or deletions are chosen. -/
theorem matching_below_three_impossible (ρ : ℝ≥0) (hρ : ρ < 3)
    (M : OccurrenceMatching (Fin 3) (Fin 3) PEmpty.{1} PEmpty.{1}) :
    ¬ IsMatching (k := ℚ) ρ source target M := by
  intro hM
  exact (not_le_of_gt hρ) (matching_radius_ge_three hM)

/-- A coefficient of two already fails over the two-element field. -/
theorem coefficient_two_fails :
    ¬ bottleneckDistance (k := ZMod 2) source target ≤
      2 * coordinateInterleavingDistance (module (k := ZMod 2) source) (module target) :=
  fails_smaller_constant (by norm_num)

/-- The explicit matching retains all three occurrences on both sides. -/
theorem matching_all_occurrences :
    IsMatching (k := ℚ) 3 source target matching ∧
      (∀ i : Fin 3, matching.finite i = some i) ∧
      (∀ j : Fin 3, ∃ i, matching.finite i = some j) :=
  ⟨isMatching_three, fun _ => rfl, fun j => ⟨j, rfl⟩⟩

end TDA.Persistence.RectangleSharpExample.Examples
