import TDA.Persistence.RankResolutionDegreeTwoSimplicialCoordinateTranslation
import Mathlib.Data.Rat.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Ordinary-import consumers of independent simplicial coordinate translations

These clients use actual translated simplicial homology, inclusion maps,
explicit interleavings and the coordinate-specific obstruction over arbitrary
fields, the rationals, and a characteristic-two field.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence.RankResolutionDegreeTwoSimplicialCoordinateTranslationExamples

open CategoryTheory CategoryTheory.Limits TDA.Filtration TDA.Simplicial
open TDA.Persistence.RankResolutionDegreeTwoSimplicial
open RankResolutionDegreeTwo
open scoped TDA.Persistence NNReal ENNReal

def zeroVector : Fin 2 → ℝ := fun _ => 0
noncomputable def secondQuarter : Fin 2 → ℝ := fun i => if i = 0 then 0 else 1 / 4
noncomputable def tiedMixed : Fin 2 → ℝ := fun i => if i = 0 then 1 / 4 else -1 / 4
noncomputable def negativeLargestSecond : Fin 2 → ℝ := fun i => if i = 0 then 1 / 8 else -1 / 4
noncomputable def positiveLargestSecond : Fin 2 → ℝ := fun i => if i = 0 then -1 / 8 else 1 / 4
noncomputable def saturatedMixed : Fin 2 → ℝ := fun i => if i = 0 then 1 / 4 else -1
def negativeOffsetSource : Fin 2 → ℝ := fun i => if i = 0 then -2 else -3
noncomputable def negativeOffsetTarget : Fin 2 → ℝ := fun i => if i = 0 then -15 / 8 else -13 / 4

/-- The actual realization comparison is natural for every field and vector. -/
theorem arbitraryField_vector_realization_naturality
    (k : Type u) [Field k] (v : Fin 2 → ℝ) {p q : Fin 2 → ℝ} (hpq : p ≤ q) :
    structureMap (coordinateTranslatedHomology k v) hpq ≫
        (coordinateTranslatedRealIso k v).hom.app q =
      (coordinateTranslatedRealIso k v).hom.app p ≫
        structureMap (realModule (k := k))
          ((coordinateTranslationPullback v).monotone' hpq) :=
  coordinateTranslatedRealIso_structureMap k v hpq

/-- Each independently translated actual finite homology module is finitely presented. -/
theorem arbitraryField_vector_is_finitelyPresented
    (k : Type u) [Field k] (v : Fin 2 → ℝ) :
    GradedFree.FinitelyPresented.{u,0,0} (R := k) (P := Fin 2 → ℝ)
      (coordinateTranslatedHomology k v) :=
  coordinateTranslatedHomology_finitelyPresented k v

/-- Zero vector translation identifies the actual module with the original grading. -/
theorem rational_zero_vector_is_original :
    coordinateTranslatedHomology ℚ zeroVector =
      finiteSimplicialHomology ℚ boundaryTetrahedronGrading 1 := by
  change coordinateTranslatedHomology ℚ (0 : Fin 2 → ℝ) = _
  exact coordinateTranslatedHomology_zero ℚ

/-- Constant vectors use the established scalar theorem through actual module equalities. -/
theorem rational_constant_vector_compatibility (s t : ℝ) :
    coordinateInterleavingDistance
      (coordinateTranslatedHomology ℚ (fun _ => s))
      (coordinateTranslatedHomology ℚ (fun _ => t)) =
      ENNReal.ofReal (min |t - s| (1 / 2)) :=
  coordinateInterleavingDistance_const_translatedHomology ℚ s t

/-- The selected second arm starts at the actual boundary corner (1,0). -/
theorem rational_second_arm_birth_coordinates :
    coordinateTranslatedBirth 1 zeroVector = fun i => if i = 0 then 1 else 0 := by
  funext i
  fin_cases i <;> simp [coordinateTranslatedBirth_apply, zeroVector]

/-- The radius-one-eighth middle target is the actual point (9/8,1/8). -/
theorem rational_second_quarter_target_coordinates :
    CoordinateShift.translation (1 / 8 : ℝ≥0)
        (coordinateTranslatedBirth 1 zeroVector) =
      fun i => if i = 0 then 9 / 8 else 1 / 8 := by
  funext i
  fin_cases i <;> simp [CoordinateShift.translation_apply,
    coordinateTranslatedBirth_apply, zeroVector] <;> norm_num

/-- The second-coordinate target fiber is actually zero below the quarter birth. -/
theorem rational_second_quarter_target_is_zero :
    IsZero ((coordinateTranslatedHomology ℚ secondQuarter).obj
      (CoordinateShift.translation (1 / 8 : ℝ≥0)
        (coordinateTranslatedBirth 1 zeroVector))) := by
  apply coordinateTranslatedHomology_isZero_of_coordinate_lt ℚ secondQuarter 1
  simp only [CoordinateShift.translation_apply, coordinateTranslatedBirth_selected]
  norm_num [secondQuarter, zeroVector]

/-- The actual source transition from (1,0) to (5/4,1/4) survives. -/
theorem rational_second_quarter_source_map_survives :
    structureMap (coordinateTranslatedHomology ℚ zeroVector)
      (show coordinateTranslatedBirth 1 zeroVector ≤
        (fun i => coordinateTranslatedBirth 1 zeroVector i + (1 / 4 : ℝ)) from
          fun _ => le_add_of_nonneg_right (by norm_num)) ≠ 0 :=
  coordinateTranslatedHomology_birth_structureMap_ne_zero ℚ zeroVector 1
    (1 / 4) (by norm_num) (by norm_num)

/-- The public actual second-arm obstruction excludes an eighth interleaving. -/
theorem rational_zero_second_quarter_has_no_eighth_interleaving :
    IsEmpty (CoordinateInterleaving (1 / 8 : ℝ≥0)
      (coordinateTranslatedHomology ℚ zeroVector)
      (coordinateTranslatedHomology ℚ secondQuarter)) := by
  apply coordinateTranslatedHomology_no_interleaving ℚ zeroVector secondQuarter 1
  · norm_num [zeroVector, secondQuarter]
  · norm_num

/-- Both components of the explicit half-radius witness are zero maps. -/
theorem rational_saturated_half_maps_are_zero :
    (coordinateTranslatedHomologyHalfInterleaving ℚ zeroVector saturatedMixed).φ = 0 ∧
      (coordinateTranslatedHomologyHalfInterleaving ℚ zeroVector saturatedMixed).ψ = 0 :=
  ⟨coordinateTranslatedHomologyHalfInterleaving_φ ℚ zeroVector saturatedMixed,
    coordinateTranslatedHomologyHalfInterleaving_ψ ℚ zeroVector saturatedMixed⟩

/-- The magnitude witness components are the real sublevel inclusions. -/
theorem rational_second_quarter_magnitude_components (p : Fin 2 → ℝ) :
    (coordinateTranslatedHomologyMagnitudeInterleaving ℚ zeroVector secondQuarter).φ.app p =
        simplicialHomologyIncl ℚ
          ((coordinateTranslatedGrading zeroVector).sublevel_le_translation_of_error
            (coordinateTranslatedGrading secondQuarter)
            (coordinateTranslatedGrading_grade_error zeroVector secondQuarter) p) 1 ∧
      (coordinateTranslatedHomologyMagnitudeInterleaving ℚ zeroVector secondQuarter).ψ.app p =
        simplicialHomologyIncl ℚ
          ((coordinateTranslatedGrading secondQuarter).sublevel_le_translation_of_error
            (coordinateTranslatedGrading zeroVector)
            (fun σ i => by
              simpa only [abs_sub_comm] using
                coordinateTranslatedGrading_grade_error zeroVector secondQuarter σ i) p) 1 :=
  ⟨coordinateTranslatedHomologyMagnitudeInterleaving_φ_app ℚ zeroVector secondQuarter p,
    coordinateTranslatedHomologyMagnitudeInterleaving_ψ_app ℚ zeroVector secondQuarter p⟩

/-- The explicit optimal witness has the quarter-radius type. -/
theorem rational_second_quarter_has_optimal_interleaving :
    Nonempty (CoordinateInterleaving (1 / 4 : ℝ≥0)
      (coordinateTranslatedHomology ℚ zeroVector)
      (coordinateTranslatedHomology ℚ secondQuarter)) := by
  have hr : min (coordinateTranslationGap zeroVector secondQuarter) (1 / 2 : ℝ≥0) =
      (1 / 4 : ℝ≥0) := by
    norm_num [coordinateTranslationGap, zeroVector, secondQuarter,
      coe_nnnorm, Real.norm_eq_abs]
    exact_mod_cast (by norm_num : (1 / 4 : ℝ) ≤ 1 / 2)
  rw [← hr]
  exact ⟨coordinateTranslatedHomologyOptimalInterleaving ℚ zeroVector secondQuarter⟩

/-- At the critical pure-second displacement the zero-map constructor is used directly. -/
theorem rational_second_critical_gap_has_half_interleaving :
    Nonempty (CoordinateInterleaving (1 / 2 : ℝ≥0)
      (coordinateTranslatedHomology ℚ zeroVector)
      (coordinateTranslatedHomology ℚ (fun i => if i = 0 then 0 else 1 / 2))) :=
  ⟨coordinateTranslatedHomologyHalfInterleaving ℚ zeroVector
    (fun i => if i = 0 then 0 else 1 / 2)⟩

/-- Exact examples cover pure, tied, sign-selected, saturated, and negative-offset gaps. -/
theorem rational_distance_cases :
    coordinateInterleavingDistance (coordinateTranslatedHomology ℚ zeroVector)
        (coordinateTranslatedHomology ℚ zeroVector) = 0 ∧
    coordinateInterleavingDistance (coordinateTranslatedHomology ℚ zeroVector)
        (coordinateTranslatedHomology ℚ secondQuarter) = ENNReal.ofReal (1 / 4 : ℝ) ∧
    coordinateInterleavingDistance (coordinateTranslatedHomology ℚ zeroVector)
        (coordinateTranslatedHomology ℚ (fun i => if i = 0 then 0 else 1 / 2)) =
          ENNReal.ofReal (1 / 2 : ℝ) ∧
    coordinateInterleavingDistance (coordinateTranslatedHomology ℚ zeroVector)
        (coordinateTranslatedHomology ℚ tiedMixed) = ENNReal.ofReal (1 / 4 : ℝ) ∧
    coordinateInterleavingDistance (coordinateTranslatedHomology ℚ zeroVector)
        (coordinateTranslatedHomology ℚ negativeLargestSecond) = ENNReal.ofReal (1 / 4 : ℝ) ∧
    coordinateInterleavingDistance (coordinateTranslatedHomology ℚ negativeLargestSecond)
        (coordinateTranslatedHomology ℚ zeroVector) = ENNReal.ofReal (1 / 4 : ℝ) ∧
    coordinateInterleavingDistance (coordinateTranslatedHomology ℚ zeroVector)
        (coordinateTranslatedHomology ℚ positiveLargestSecond) = ENNReal.ofReal (1 / 4 : ℝ) ∧
    coordinateInterleavingDistance (coordinateTranslatedHomology ℚ zeroVector)
        (coordinateTranslatedHomology ℚ saturatedMixed) = ENNReal.ofReal (1 / 2 : ℝ) ∧
    coordinateInterleavingDistance (coordinateTranslatedHomology ℚ negativeOffsetSource)
        (coordinateTranslatedHomology ℚ negativeOffsetTarget) = ENNReal.ofReal (1 / 4 : ℝ) := by
  repeat' constructor
  all_goals
    rw [coordinateInterleavingDistance_coordinateTranslatedHomology]
    norm_num [zeroVector, secondQuarter, tiedMixed, negativeLargestSecond,
      positiveLargestSecond, saturatedMixed, negativeOffsetSource, negativeOffsetTarget]

/-- Characteristic two has the same actual arm map, obstruction, and quarter distance. -/
theorem characteristicTwo_second_arm_quarter_clients :
    structureMap (coordinateTranslatedHomology (ZMod 2) zeroVector)
        (show coordinateTranslatedBirth 1 zeroVector ≤
          (fun i => coordinateTranslatedBirth 1 zeroVector i + (1 / 4 : ℝ)) from
            fun _ => le_add_of_nonneg_right (by norm_num)) ≠ 0 ∧
    IsEmpty (CoordinateInterleaving (1 / 8 : ℝ≥0)
      (coordinateTranslatedHomology (ZMod 2) zeroVector)
      (coordinateTranslatedHomology (ZMod 2) secondQuarter)) ∧
    coordinateInterleavingDistance (coordinateTranslatedHomology (ZMod 2) zeroVector)
      (coordinateTranslatedHomology (ZMod 2) secondQuarter) = ENNReal.ofReal (1 / 4 : ℝ) := by
  refine ⟨?_, ?_, ?_⟩
  · exact coordinateTranslatedHomology_birth_structureMap_ne_zero (ZMod 2)
      zeroVector 1 (1 / 4) (by norm_num) (by norm_num)
  · apply coordinateTranslatedHomology_no_interleaving (ZMod 2)
      zeroVector secondQuarter 1
    · norm_num [zeroVector, secondQuarter]
    · norm_num
  · rw [coordinateInterleavingDistance_coordinateTranslatedHomology]
    norm_num [zeroVector, secondQuarter]

end TDA.Persistence.RankResolutionDegreeTwoSimplicialCoordinateTranslationExamples
