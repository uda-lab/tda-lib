import TDA.Persistence.RankResolutionDegreeTwoSimplicialTranslation
import Mathlib.Data.Rat.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Consumers of the simplicial translation distance

These ordinary-import examples use the translated actual degree-one homology,
its inclusion-induced interleavings, and the public obstruction to a
subcritical interleaving. They specialize the arbitrary-field theory to the
rationals and to characteristic two.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence.RankResolutionDegreeTwoSimplicialTranslationExamples

open CategoryTheory CategoryTheory.Limits TDA.Filtration TDA.Simplicial
open TDA.Persistence.RankResolutionDegreeTwoSimplicial
open RankResolutionDegreeTwo
open scoped TDA.Persistence NNReal ENNReal

/-- Positive face translation adds the same delay to each actual face grade. -/
theorem positive_quarter_delays_every_face
    (σ : TotalFace boundaryTetrahedron.toPre) (i : Fin 2) :
    (translatedGrading (1 / 4)).grade σ i =
      boundaryTetrahedronGrading.grade σ i + 1 / 4 := by
  rw [translatedGrading_grade]

/-- The zero translate is the pre-existing, unmodified filtration grading. -/
theorem zero_translate_is_original_grading :
    translatedGrading 0 = boundaryTetrahedronGrading :=
  translatedGrading_zero

/-- The translated comparison commutes with an actual homology structure map. -/
theorem arbitraryField_realIso_respects_structureMaps
    (k : Type u) [Field k] (t : ℝ) {p q : Fin 2 → ℝ} (hpq : p ≤ q) :
    structureMap (translatedHomology k t) hpq ≫
        (translatedRealIso k t).hom.app q =
      (translatedRealIso k t).hom.app p ≫
        structureMap (realModule (k := k))
          ((translationPullback t).monotone' hpq) :=
  translatedRealIso_structureMap k t hpq

/-- Finite presentation follows from the actual finite grading at every delay. -/
theorem arbitraryField_each_translate_is_finitelyPresented
    (k : Type u) [Field k] (t : ℝ) :
    GradedFree.FinitelyPresented.{u,0,0} (R := k) (P := Fin 2 → ℝ)
      (translatedHomology k t) :=
  translatedHomology_finitelyPresented k t

/-- The actual birth map remains nonzero for every subunit displacement. -/
theorem arbitraryField_birth_map_survives
    (k : Type u) [Field k] (t r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    structureMap (translatedHomology k t)
      (show translatedBirth t ≤ (fun i => translatedBirth t i + r) from
        fun _ => le_add_of_nonneg_right hr0) ≠ 0 :=
  translatedHomology_birth_structureMap_ne_zero k t r hr0 hr1

/-- The first birth fiber is nonzero even though the one-unit map vanishes. -/
theorem arbitraryField_birth_is_nonzero
    (k : Type u) [Field k] (t : ℝ) :
    ¬ IsZero ((translatedHomology k t).obj (translatedBirth t)) :=
  translatedHomology_birth_not_isZero k t

/-- Every actual translated module has zero one-unit diagonal transitions. -/
theorem arbitraryField_one_unit_transition_is_zero
    (k : Type u) [Field k] (t : ℝ) (p : Fin 2 → ℝ) :
    structureMap (translatedHomology k t)
      (show p ≤ (fun i => p i + 1) from
        fun _ => le_add_of_nonneg_right (by norm_num)) = 0 :=
  translatedHomology_diagonal_one_zero k t p

/-- The magnitude witness uses the actual forward sublevel inclusion map. -/
theorem rational_quarter_magnitude_forward_is_inclusion (p : Fin 2 → ℝ) :
    (translatedHomologyMagnitudeInterleaving ℚ 0 (1 / 4)).φ.app p =
      simplicialHomologyIncl ℚ
        ((translatedGrading 0).sublevel_le_translation_of_error
          (translatedGrading (1 / 4))
          (translatedGrading_grade_error 0 (1 / 4)) p) 1 :=
  translatedHomologyMagnitudeInterleaving_φ_app ℚ 0 (1 / 4) p

/-- The magnitude witness uses the actual reverse sublevel inclusion map. -/
theorem rational_quarter_magnitude_reverse_is_inclusion (p : Fin 2 → ℝ) :
    (translatedHomologyMagnitudeInterleaving ℚ 0 (1 / 4)).ψ.app p =
      simplicialHomologyIncl ℚ
        ((translatedGrading (1 / 4)).sublevel_le_translation_of_error
          (translatedGrading 0)
          (fun σ i => by
            simpa only [abs_sub_comm] using
              translatedGrading_grade_error 0 (1 / 4) σ i) p) 1 :=
  translatedHomologyMagnitudeInterleaving_ψ_app ℚ 0 (1 / 4) p

/-- At radius one half the explicit interleaving has both natural maps zero. -/
theorem rational_half_interleaving_forward_is_zero :
    (translatedHomologyHalfInterleaving ℚ 0 1).φ = 0 :=
  translatedHomologyHalfInterleaving_φ ℚ 0 1

/-- The half-radius interleaving's reverse natural transformation is zero. -/
theorem rational_half_interleaving_reverse_is_zero :
    (translatedHomologyHalfInterleaving ℚ 0 1).ψ = 0 :=
  translatedHomologyHalfInterleaving_ψ ℚ 0 1

/-- The quarter-gap optimum is attained by an actual coordinate interleaving. -/
theorem rational_quarter_has_optimal_interleaving :
    Nonempty (CoordinateInterleaving (1 / 4 : ℝ≥0)
      (translatedHomology ℚ 0) (translatedHomology ℚ (1 / 4))) := by
  have hr : min ‖(1 / 4 : ℝ) - 0‖₊ (1 / 2 : ℝ≥0) = (1 / 4 : ℝ≥0) := by
    norm_num [coe_nnnorm, Real.norm_eq_abs];
    exact_mod_cast (by norm_num : (1 / 4 : ℝ) ≤ 1 / 2)
  rw [← hr]
  exact ⟨translatedHomologyOptimalInterleaving ℚ 0 (1 / 4)⟩

/-- The critical displacement uses the explicit zero-map half interleaving. -/
theorem rational_critical_gap_has_half_interleaving :
    Nonempty (CoordinateInterleaving (1 / 2 : ℝ≥0)
      (translatedHomology ℚ 0) (translatedHomology ℚ (1 / 2))) :=
  ⟨translatedHomologyHalfInterleaving ℚ 0 (1 / 2)⟩

/-- A unit translation attains the saturated distance by the half witness. -/
theorem rational_saturated_gap_has_half_interleaving :
    Nonempty (CoordinateInterleaving (1 / 2 : ℝ≥0)
      (translatedHomology ℚ 0) (translatedHomology ℚ 1)) :=
  ⟨translatedHomologyHalfInterleaving ℚ 0 1⟩

/-- The actual target fiber in the eighth-radius obstruction is zero. -/
theorem rational_quarter_target_at_eighth_is_zero :
    IsZero ((translatedHomology ℚ (1 / 4)).obj
      (CoordinateShift.translation (1 / 8 : ℝ≥0) (translatedBirth 0))) := by
  apply translatedHomology_isZero_of_first_lt
  simp only [CoordinateShift.translation_apply, translatedBirth_first]
  norm_num

/-- The actual source birth transition in that obstruction survives to radius one quarter. -/
theorem rational_quarter_source_birth_map_survives :
    structureMap (translatedHomology ℚ 0)
      (show translatedBirth 0 ≤ (fun i => translatedBirth 0 i + (1 / 4 : ℝ)) from
        fun _ => le_add_of_nonneg_right (by norm_num)) ≠ 0 := by
  exact translatedHomology_birth_structureMap_ne_zero ℚ 0 (1 / 4)
    (by norm_num) (by norm_num)

/-- No actual one-eighth interleaving joins the zero and quarter translates. -/
theorem rational_zero_quarter_has_no_eighth_interleaving :
    IsEmpty (CoordinateInterleaving (1 / 8 : ℝ≥0)
      (translatedHomology ℚ 0) (translatedHomology ℚ (1 / 4))) :=
  translatedHomology_no_interleaving ℚ 0 (1 / 4) (1 / 8)
    (by norm_num) (by norm_num)

/-- Exact distance examples at zero, quarter, critical, and saturated gaps. -/
theorem rational_distance_zero_gap :
    coordinateInterleavingDistance (translatedHomology ℚ 0)
      (translatedHomology ℚ 0) = 0 := by
  rw [coordinateInterleavingDistance_translatedHomology]
  norm_num

/-- A quarter-unit translation has distance one quarter. -/
theorem rational_distance_quarter_gap :
    coordinateInterleavingDistance (translatedHomology ℚ 0)
      (translatedHomology ℚ (1 / 4)) = ENNReal.ofReal (1 / 4 : ℝ) := by
  rw [coordinateInterleavingDistance_translatedHomology]
  norm_num

theorem rational_distance_critical_gap :
    coordinateInterleavingDistance (translatedHomology ℚ 0)
      (translatedHomology ℚ (1 / 2)) = ENNReal.ofReal (1 / 2 : ℝ) := by
  rw [coordinateInterleavingDistance_translatedHomology]
  norm_num

/-- A one-unit gap has reached the one-half saturation value. -/
theorem rational_distance_saturated_gap :
    coordinateInterleavingDistance (translatedHomology ℚ 0)
      (translatedHomology ℚ 1) = ENNReal.ofReal (1 / 2 : ℝ) := by
  rw [coordinateInterleavingDistance_translatedHomology]
  norm_num

/-- Negative and reversed parameters retain the signed-gap formula. -/
theorem rational_distance_negative_quarter_gap :
    coordinateInterleavingDistance (translatedHomology ℚ 0)
      (translatedHomology ℚ (-1 / 4)) = ENNReal.ofReal (1 / 4 : ℝ) := by
  rw [coordinateInterleavingDistance_translatedHomology]
  norm_num

theorem rational_distance_negative_saturated_gap :
    coordinateInterleavingDistance (translatedHomology ℚ 0)
      (translatedHomology ℚ (-1)) = ENNReal.ofReal (1 / 2 : ℝ) := by
  rw [coordinateInterleavingDistance_translatedHomology]
  norm_num

/-- Two nonzero parameters on opposite sides of zero give the same symmetric distance. -/
theorem rational_distance_straddling_zero :
    coordinateInterleavingDistance (translatedHomology ℚ (-1 / 4))
      (translatedHomology ℚ (1 / 4)) = ENNReal.ofReal (1 / 2 : ℝ) := by
  rw [coordinateInterleavingDistance_translatedHomology]
  norm_num

theorem rational_distance_reversed_straddling_zero :
    coordinateInterleavingDistance (translatedHomology ℚ (1 / 4))
      (translatedHomology ℚ (-1 / 4)) = ENNReal.ofReal (1 / 2 : ℝ) := by
  rw [coordinateInterleavingDistance_translatedHomology]
  norm_num

/-- The same exact formula and lifetime maps hold over a characteristic-two field. -/
theorem characteristicTwo_distance_quarter_gap :
    coordinateInterleavingDistance (translatedHomology (ZMod 2) 0)
      (translatedHomology (ZMod 2) (1 / 4)) = ENNReal.ofReal (1 / 4 : ℝ) := by
  rw [coordinateInterleavingDistance_translatedHomology]
  norm_num

theorem characteristicTwo_distance_negative_saturated_gap :
    coordinateInterleavingDistance (translatedHomology (ZMod 2) 0)
      (translatedHomology (ZMod 2) (-1)) = ENNReal.ofReal (1 / 2 : ℝ) := by
  rw [coordinateInterleavingDistance_translatedHomology]
  norm_num

/-- The early cycle's actual inclusion-induced map survives in characteristic two. -/
theorem characteristicTwo_birth_map_survives_quarter :
    structureMap (translatedHomology (ZMod 2) 0)
      (show translatedBirth 0 ≤ (fun i => translatedBirth 0 i + (1 / 4 : ℝ)) from
        fun _ => le_add_of_nonneg_right (by norm_num)) ≠ 0 := by
  exact translatedHomology_birth_structureMap_ne_zero (ZMod 2) 0 (1 / 4)
    (by norm_num) (by norm_num)

/-- Characteristic two has the same zero one-unit transition. -/
theorem characteristicTwo_one_unit_transition_is_zero (p : Fin 2 → ℝ) :
    structureMap (translatedHomology (ZMod 2) (-1))
      (show p ≤ (fun i => p i + 1) from
        fun _ => le_add_of_nonneg_right (by norm_num)) = 0 :=
  translatedHomology_diagonal_one_zero (ZMod 2) (-1) p

/-- The actual public obstruction also rules out a subcritical characteristic-two interleaving. -/
theorem characteristicTwo_zero_quarter_has_no_eighth_interleaving :
    IsEmpty (CoordinateInterleaving (1 / 8 : ℝ≥0)
      (translatedHomology (ZMod 2) 0) (translatedHomology (ZMod 2) (1 / 4))) :=
  translatedHomology_no_interleaving (ZMod 2) 0 (1 / 4) (1 / 8)
    (by norm_num) (by norm_num)

end TDA.Persistence.RankResolutionDegreeTwoSimplicialTranslationExamples
