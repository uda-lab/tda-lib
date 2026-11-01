import TDA.Persistence.RankResolutionDegreeTwoSimplicialScaledTranslation
import Mathlib.Data.Rat.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Ordinary-import clients for scaled diagonal translations

These clients inspect the actual PH₁ modules, inclusion maps, witnesses and
zero middle fibers for both asymmetric scales. The direct radius-5/8
obstructions use the interleaving equation and a nonzero actual source map.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence.RankResolutionDegreeTwoSimplicialScaledTranslationExamples

open CategoryTheory CategoryTheory.Limits
open TDA.Filtration TDA.Simplicial
open TDA.Persistence.RankResolutionDegreeTwoSimplicial
open RankResolutionDegreeTwo
open scoped TDA.Persistence NNReal ENNReal ZeroObject

private def scale11 : Fin 2 → ℝ := fun _ => 1
private def scale41 : Fin 2 → ℝ := ![(4 : ℝ), 1]
private def scale14 : Fin 2 → ℝ := ![(1 : ℝ), 4]
private noncomputable def scaleQuarterOne : Fin 2 → ℝ := ![(1 / 4 : ℝ), 1]

private theorem scale11_pos : ∀ i, 0 < scale11 i := by
  intro i
  fin_cases i <;> norm_num [scale11]

private theorem scale41_pos : ∀ i, 0 < scale41 i := by
  intro i
  fin_cases i <;> norm_num [scale41]

private theorem scale14_pos : ∀ i, 0 < scale14 i := by
  intro i
  fin_cases i <;> norm_num [scale14]

private theorem scaleQuarterOne_pos : ∀ i, 0 < scaleQuarterOne i := by
  intro i
  fin_cases i <;> norm_num [scaleQuarterOne]

/-- Every field and universe use the literal translated finite PH₁ family. -/
theorem arbitraryField_module_is_finitelyPresented (k : Type u) [Field k]
    (s : Fin 2 → ℝ) (hs : ∀ i, 0 < s i) (t : ℝ) :
    GradedFree.FinitelyPresented.{u,0,0} (R := k) (P := Fin 2 → ℝ)
      (scaledTranslatedHomology k s hs t) :=
  scaledTranslatedHomology_finitelyPresented k s hs t

/-- The original-Lan realization map is natural on every actual inclusion map. -/
theorem arbitraryField_actualRealization_naturality (k : Type u) [Field k]
    (s : Fin 2 → ℝ) (hs : ∀ i, 0 < s i) (t : ℝ)
    {p q : Fin 2 → ℝ} (hpq : p ≤ q) :
    structureMap (scaledTranslatedHomology k s hs t) hpq ≫
        (scaledTranslatedRealIso k s hs t).hom.app q =
      (scaledTranslatedRealIso k s hs t).hom.app p ≫
        structureMap (realModule (k := k))
          ((scaledTranslatedPullback s hs t).monotone' hpq) :=
  scaledTranslatedRealIso_structureMap k s hs t hpq

/-- Zero delay and unit scale recover the established actual inputs and modules. -/
theorem zero_and_unit_actual_module_compatibility (k : Type u) [Field k]
    (s : Fin 2 → ℝ) (hs : ∀ i, 0 < s i) (t : ℝ) :
    scaledTranslatedGrading s hs 0 = scaledGrading s hs ∧
    scaledTranslatedHomology k s hs 0 = scaledHomology k s hs ∧
    scaledTranslatedGrading (fun _ : Fin 2 => (1 : ℝ)) (fun _ => by norm_num) t =
      translatedGrading t ∧
    scaledTranslatedHomology k (fun _ : Fin 2 => (1 : ℝ)) (fun _ => by norm_num) t =
      translatedHomology k t := by
  exact ⟨scaledTranslatedGrading_zero s hs, scaledTranslatedHomology_zero k s hs,
    scaledTranslatedGrading_one t, scaledTranslatedHomology_one k t⟩

/-- At unit scale, the established scalar-translation distance theorem applies. -/
theorem unit_scale_old_distance_compatibility (k : Type u) [Field k] (t u : ℝ) :
    coordinateInterleavingDistance
      (scaledTranslatedHomology k scale11 scale11_pos t)
      (scaledTranslatedHomology k scale11 scale11_pos u) =
        ENNReal.ofReal (min |t - u| (1 / 2 : ℝ)) := by
  have ht : scaledTranslatedHomology k scale11 scale11_pos t = translatedHomology k t := by
    change scaledTranslatedHomology k (fun _ : Fin 2 => (1 : ℝ))
      (fun _ => by norm_num) t = _
    exact scaledTranslatedHomology_one k t
  have hu : scaledTranslatedHomology k scale11 scale11_pos u = translatedHomology k u := by
    change scaledTranslatedHomology k (fun _ : Fin 2 => (1 : ℝ))
      (fun _ => by norm_num) u = _
    exact scaledTranslatedHomology_one k u
  rw [ht, hu]
  simpa [abs_sub_comm] using coordinateInterleavingDistance_translatedHomology k t u

/-- Equal signed delays have zero distance, including at a negative value. -/
theorem equal_negative_delay_has_zero_distance (k : Type u) [Field k] :
    coordinateInterleavingDistance
      (scaledTranslatedHomology k scale41 scale41_pos (-2))
      (scaledTranslatedHomology k scale41 scale41_pos (-2)) = 0 := by
  rw [coordinateInterleavingDistance_scaledTranslatedHomology]
  norm_num [scaledLifetime, scaledArmLifetimeA, scaledArmLifetimeB, scale41]

/-- Signed and reversed shifts have the same exact gap formula. -/
theorem rational_signed_reversed_gap (t u : ℝ) :
    coordinateInterleavingDistance
        (scaledTranslatedHomology ℚ scale41 scale41_pos t)
        (scaledTranslatedHomology ℚ scale41 scale41_pos u) =
          ENNReal.ofReal (min |t - u| (1 : ℝ)) ∧
    coordinateInterleavingDistance
        (scaledTranslatedHomology ℚ scale41 scale41_pos u)
        (scaledTranslatedHomology ℚ scale41 scale41_pos t) =
          ENNReal.ofReal (min |t - u| (1 : ℝ)) := by
  constructor <;> rw [coordinateInterleavingDistance_scaledTranslatedHomology] <;>
    norm_num [scaledLifetime, scaledArmLifetimeA, scaledArmLifetimeB, scale41,
      abs_sub_comm]

/-- The concrete signed pair `(-1/2,1/4)` and its reversal have gap `3/4`. -/
theorem rational_concrete_signed_pair_and_reverse :
    coordinateInterleavingDistance
        (scaledTranslatedHomology ℚ scale41 scale41_pos (-1 / 2))
        (scaledTranslatedHomology ℚ scale41 scale41_pos (1 / 4)) = ENNReal.ofReal (3 / 4 : ℝ) ∧
    coordinateInterleavingDistance
        (scaledTranslatedHomology ℚ scale41 scale41_pos (1 / 4))
        (scaledTranslatedHomology ℚ scale41 scale41_pos (-1 / 2)) = ENNReal.ofReal (3 / 4 : ℝ) := by
  constructor <;> rw [coordinateInterleavingDistance_scaledTranslatedHomology] <;>
    norm_num [scaledLifetime, scaledArmLifetimeA, scaledArmLifetimeB, scale41,
      ENNReal.ofReal, abs_sub_comm]

/-- The quarter-scale lifetime is one half and its saturation radius is one quarter. -/
theorem quarter_scale_distances (k : Type u) [Field k] :
    coordinateInterleavingDistance
      (scaledTranslatedHomology k scaleQuarterOne scaleQuarterOne_pos 0)
      (scaledTranslatedHomology k scaleQuarterOne scaleQuarterOne_pos (1 / 8)) =
        ENNReal.ofReal (1 / 8 : ℝ) ∧
    coordinateInterleavingDistance
      (scaledTranslatedHomology k scaleQuarterOne scaleQuarterOne_pos 0)
      (scaledTranslatedHomology k scaleQuarterOne scaleQuarterOne_pos (1 / 2)) =
        ENNReal.ofReal (1 / 4 : ℝ) := by
  constructor <;> rw [coordinateInterleavingDistance_scaledTranslatedHomology] <;>
    norm_num [scaledLifetime, scaledArmLifetimeA, scaledArmLifetimeB, scaleQuarterOne,
      ENNReal.ofReal]

/-- At both asymmetric scales, gap 3/4 exceeds the old half-unit cap. -/
theorem rational_asymmetric_distance_cases :
    coordinateInterleavingDistance
        (scaledTranslatedHomology ℚ scale41 scale41_pos 0)
        (scaledTranslatedHomology ℚ scale41 scale41_pos (3 / 4)) = ENNReal.ofReal (3 / 4 : ℝ) ∧
    coordinateInterleavingDistance
        (scaledTranslatedHomology ℚ scale41 scale41_pos 0)
        (scaledTranslatedHomology ℚ scale41 scale41_pos 1) = 1 ∧
    coordinateInterleavingDistance
        (scaledTranslatedHomology ℚ scale41 scale41_pos 0)
        (scaledTranslatedHomology ℚ scale41 scale41_pos 2) = 1 ∧
    coordinateInterleavingDistance
        (scaledTranslatedHomology ℚ scale14 scale14_pos 0)
        (scaledTranslatedHomology ℚ scale14 scale14_pos (3 / 4)) = ENNReal.ofReal (3 / 4 : ℝ) ∧
    coordinateInterleavingDistance
        (scaledTranslatedHomology ℚ scale14 scale14_pos 0)
        (scaledTranslatedHomology ℚ scale14 scale14_pos 1) = 1 ∧
    coordinateInterleavingDistance
        (scaledTranslatedHomology ℚ scale14 scale14_pos 0)
        (scaledTranslatedHomology ℚ scale14 scale14_pos 2) = 1 := by
  repeat' constructor
  all_goals
    rw [coordinateInterleavingDistance_scaledTranslatedHomology]
    norm_num [scaledLifetime, scaledArmLifetimeA, scaledArmLifetimeB, scale41, scale14,
      ENNReal.ofReal]

/-- The rational magnitude witness at gap 3/4 has a nonzero long-arm composite at 3/2. -/
theorem rational_scale41_magnitude_long_composite_nonzero :
    let ε : ℝ≥0 := Real.toNNReal |(0 : ℝ) - 3 / 4|
    let I := scaledTranslatedHomologyMagnitudeInterleaving ℚ scale41 scale41_pos 0 (3 / 4)
    let p := scaledTranslatedBirthB scale41 0
    I.φ.app p ≫ I.ψ.app (CoordinateShift.translation ε p) ≠ 0 := by
  dsimp only
  let ε : ℝ≥0 := Real.toNNReal |(0 : ℝ) - 3 / 4|
  let I := scaledTranslatedHomologyMagnitudeInterleaving ℚ scale41 scale41_pos 0 (3 / 4)
  let p := scaledTranslatedBirthB scale41 0
  rw [I.φ_ψ_structureMap p]
  apply (scaledTranslatedHomology_structureMap_ne_zero_iff ℚ scale41 scale41_pos 0
    (CoordinateInterleaving.twice_le ε p)).2
  norm_num [ε, p, CoordinateShift.translation_apply, scaledTranslatedBirthB,
    scaledBirthB, scale41]

/-- Reversing the skew scale uses the other actual long arm at the same gap. -/
theorem rational_scale14_magnitude_long_composite_nonzero :
    let ε : ℝ≥0 := Real.toNNReal |(0 : ℝ) - 3 / 4|
    let I := scaledTranslatedHomologyMagnitudeInterleaving ℚ scale14 scale14_pos 0 (3 / 4)
    let p := scaledTranslatedBirthA scale14 0
    I.φ.app p ≫ I.ψ.app (CoordinateShift.translation ε p) ≠ 0 := by
  dsimp only
  let ε : ℝ≥0 := Real.toNNReal |(0 : ℝ) - 3 / 4|
  let I := scaledTranslatedHomologyMagnitudeInterleaving ℚ scale14 scale14_pos 0 (3 / 4)
  let p := scaledTranslatedBirthA scale14 0
  rw [I.φ_ψ_structureMap p]
  apply (scaledTranslatedHomology_structureMap_ne_zero_iff ℚ scale14 scale14_pos 0
    (CoordinateInterleaving.twice_le ε p)).2
  norm_num [ε, p, CoordinateShift.translation_apply, scaledTranslatedBirthA,
    scaledBirthA, scale14]

private theorem noInterleaving_of_nonzero_double_to_zero_middle
    {k : Type u} [Field k] {M N : PModule.{u,0,u} k (Fin 2 → ℝ)}
    (ε : ℝ≥0) (p : Fin 2 → ℝ)
    (hmap : structureMap M (CoordinateInterleaving.twice_le ε p) ≠ 0)
    (hzero : IsZero (N.obj (CoordinateShift.translation ε p))) :
    IsEmpty (CoordinateInterleaving ε M N) := by
  refine ⟨fun I => ?_⟩
  have hφ : I.φ.app p = 0 := hzero.eq_of_tgt _ _
  have heq := I.φ_ψ_structureMap p
  erw [hφ, zero_comp] at heq
  exact hmap heq.symm

/-- The 5/8 rational obstruction for scale (4,1) uses the actual B-arm map. -/
theorem rational_scale41_gap_three_quarters_no_five_eighth :
    IsEmpty (CoordinateInterleaving (5 / 8 : ℝ≥0)
      (scaledTranslatedHomology ℚ scale41 scale41_pos 0)
      (scaledTranslatedHomology ℚ scale41 scale41_pos (3 / 4))) := by
  let ε : ℝ≥0 := 5 / 8
  let p := scaledTranslatedBirthB scale41 0
  have hmap : structureMap (scaledTranslatedHomology ℚ scale41 scale41_pos 0)
      (CoordinateInterleaving.twice_le ε p) ≠ 0 := by
    apply (scaledTranslatedHomology_structureMap_ne_zero_iff ℚ scale41 scale41_pos 0
      (CoordinateInterleaving.twice_le ε p)).2
    norm_num [ε, p, CoordinateShift.translation_apply, scaledTranslatedBirthB,
      scaledBirthB, scale41]
  have hzero : IsZero ((scaledTranslatedHomology ℚ scale41 scale41_pos (3 / 4)).obj
      (CoordinateShift.translation ε p)) := by
    apply scaledTranslatedHomology_isZero_of_coordinate_lt ℚ scale41 scale41_pos
      (3 / 4) (CoordinateShift.translation ε p) 1
    norm_num [ε, p, CoordinateShift.translation_apply, scaledTranslatedBirthB,
      scaledBirthB, scale41]
  exact noInterleaving_of_nonzero_double_to_zero_middle ε p hmap hzero

/-- Characteristic two has the reversed long-arm 5/8 obstruction by the same mechanism. -/
theorem characteristicTwo_scale14_gap_three_quarters_no_five_eighth :
    IsEmpty (CoordinateInterleaving (5 / 8 : ℝ≥0)
      (scaledTranslatedHomology (ZMod 2) scale14 scale14_pos 0)
      (scaledTranslatedHomology (ZMod 2) scale14 scale14_pos (3 / 4))) := by
  let ε : ℝ≥0 := 5 / 8
  let p := scaledTranslatedBirthA scale14 0
  have hmap : structureMap (scaledTranslatedHomology (ZMod 2) scale14 scale14_pos 0)
      (CoordinateInterleaving.twice_le ε p) ≠ 0 := by
    apply (scaledTranslatedHomology_structureMap_ne_zero_iff (ZMod 2) scale14 scale14_pos 0
      (CoordinateInterleaving.twice_le ε p)).2
    norm_num [ε, p, CoordinateShift.translation_apply, scaledTranslatedBirthA,
      scaledBirthA, scale14]
  have hzero : IsZero ((scaledTranslatedHomology (ZMod 2) scale14 scale14_pos (3 / 4)).obj
      (CoordinateShift.translation ε p)) := by
    apply scaledTranslatedHomology_isZero_of_coordinate_lt (ZMod 2) scale14 scale14_pos
      (3 / 4) (CoordinateShift.translation ε p) 0
    norm_num [ε, p, CoordinateShift.translation_apply, scaledTranslatedBirthA,
      scaledBirthA, scale14]
  exact noInterleaving_of_nonzero_double_to_zero_middle ε p hmap hzero

private theorem not_isZero_of_nonzero_self_map {k : Type u} [Field k]
    (M : PModule.{u,0,u} k (Fin 2 → ℝ)) (p : Fin 2 → ℝ)
    (hne : structureMap M (le_rfl : p ≤ p) ≠ 0) : ¬ IsZero (M.obj p) := by
  intro hz
  exact hne (by simpa [structureMap_self] using (IsZero.iff_id_eq_zero _).mp hz)

/-- At the critical gap, both scale-(4,1) PH₁ fibers are nonzero at one grade. -/
theorem rational_scale41_critical_common_grade_nonzero :
    ¬ IsZero ((scaledTranslatedHomology ℚ scale41 scale41_pos 0).obj
        ![(5 : ℝ), 3 / 2]) ∧
    ¬ IsZero ((scaledTranslatedHomology ℚ scale41 scale41_pos 1).obj
        ![(5 : ℝ), 3 / 2]) := by
  constructor
  · apply not_isZero_of_nonzero_self_map
    apply (scaledTranslatedHomology_structureMap_ne_zero_iff ℚ scale41 scale41_pos 0
      (le_rfl : ![(5 : ℝ), 3 / 2] ≤ ![(5 : ℝ), 3 / 2])).2
    norm_num [scale41]
  · apply not_isZero_of_nonzero_self_map
    apply (scaledTranslatedHomology_structureMap_ne_zero_iff ℚ scale41 scale41_pos 1
      (le_rfl : ![(5 : ℝ), 3 / 2] ≤ ![(5 : ℝ), 3 / 2])).2
    norm_num [scale41]

/-- At the critical gap, both scale-(1,4) PH₁ fibers are nonzero at one grade. -/
theorem rational_scale14_critical_common_grade_nonzero :
    ¬ IsZero ((scaledTranslatedHomology ℚ scale14 scale14_pos 0).obj
        ![(3 / 2 : ℝ), 5]) ∧
    ¬ IsZero ((scaledTranslatedHomology ℚ scale14 scale14_pos 1).obj
        ![(3 / 2 : ℝ), 5]) := by
  constructor
  · apply not_isZero_of_nonzero_self_map
    apply (scaledTranslatedHomology_structureMap_ne_zero_iff ℚ scale14 scale14_pos 0
      (le_rfl : ![(3 / 2 : ℝ), 5] ≤ ![(3 / 2 : ℝ), 5])).2
    norm_num [scale14]
  · apply not_isZero_of_nonzero_self_map
    apply (scaledTranslatedHomology_structureMap_ne_zero_iff ℚ scale14 scale14_pos 1
      (le_rfl : ![(3 / 2 : ℝ), 5] ≤ ![(3 / 2 : ℝ), 5])).2
    norm_num [scale14]

/-- Both zero transformations of the sharp half-lifetime witness satisfy its equations. -/
theorem arbitraryField_lifetime_witness_has_both_actual_equations
    (k : Type u) [Field k] (s : Fin 2 → ℝ) (hs : ∀ i, 0 < s i) (t u : ℝ)
    (p : Fin 2 → ℝ) :
    let ε := Real.toNNReal (scaledLifetime s / 2)
    let I := scaledTranslatedHomologyLifetimeInterleaving k s hs t u
    I.φ.app p ≫ I.ψ.app (CoordinateShift.translation ε p) =
        structureMap (scaledTranslatedHomology k s hs t)
          (CoordinateInterleaving.twice_le ε p) ∧
    I.ψ.app p ≫ I.φ.app (CoordinateShift.translation ε p) =
        structureMap (scaledTranslatedHomology k s hs u)
          (CoordinateInterleaving.twice_le ε p) ∧
    I.φ = 0 ∧ I.ψ = 0 := by
  let ε : ℝ≥0 := Real.toNNReal (scaledLifetime s / 2)
  let I := scaledTranslatedHomologyLifetimeInterleaving k s hs t u
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact I.φ_ψ_structureMap p
  · exact I.symm.φ_ψ_structureMap p
  · exact scaledTranslatedHomologyLifetimeInterleaving_φ k s hs t u
  · exact scaledTranslatedHomologyLifetimeInterleaving_ψ k s hs t u

/-- Magnitude maps in arbitrary characteristic are the existing simplicial inclusions. -/
theorem arbitraryField_magnitude_witness_actual_inclusion_maps
    (k : Type u) [Field k] (s : Fin 2 → ℝ) (hs : ∀ i, 0 < s i) (t u : ℝ)
    (p : Fin 2 → ℝ) :
    (scaledTranslatedHomologyMagnitudeInterleaving k s hs t u).φ.app p =
      simplicialHomologyIncl k
        ((scaledTranslatedGrading s hs t).sublevel_le_translation_of_error
          (scaledTranslatedGrading s hs u) (scaledTranslatedGrading_grade_error s hs t u) p) 1 ∧
    (scaledTranslatedHomologyMagnitudeInterleaving k s hs t u).ψ.app p =
      simplicialHomologyIncl k
        ((scaledTranslatedGrading s hs u).sublevel_le_translation_of_error
          (scaledTranslatedGrading s hs t)
          (fun σ i => by
            simpa only [abs_sub_comm] using scaledTranslatedGrading_grade_error s hs t u σ i) p) 1 := by
  exact ⟨scaledTranslatedHomologyMagnitudeInterleaving_φ_app k s hs t u p,
    scaledTranslatedHomologyMagnitudeInterleaving_ψ_app k s hs t u p⟩

/-- Both magnitude witness equations are the actual double-displacement structure maps. -/
theorem arbitraryField_magnitude_witness_both_actual_equations
    (k : Type u) [Field k] (s : Fin 2 → ℝ) (hs : ∀ i, 0 < s i) (t u : ℝ)
    (p : Fin 2 → ℝ) :
    (scaledTranslatedHomologyMagnitudeInterleaving k s hs t u).φ.app p ≫
        (scaledTranslatedHomologyMagnitudeInterleaving k s hs t u).ψ.app
          (CoordinateShift.translation (Real.toNNReal |t - u|) p) =
      structureMap (scaledTranslatedHomology k s hs t)
        (CoordinateInterleaving.twice_le (Real.toNNReal |t - u|) p) ∧
    (scaledTranslatedHomologyMagnitudeInterleaving k s hs t u).ψ.app p ≫
        (scaledTranslatedHomologyMagnitudeInterleaving k s hs t u).φ.app
          (CoordinateShift.translation (Real.toNNReal |t - u|) p) =
      structureMap (scaledTranslatedHomology k s hs u)
        (CoordinateInterleaving.twice_le (Real.toNNReal |t - u|) p) := by
  exact ⟨(scaledTranslatedHomologyMagnitudeInterleaving k s hs t u).φ_ψ_structureMap p,
    (scaledTranslatedHomologyMagnitudeInterleaving k s hs t u).symm.φ_ψ_structureMap p⟩

end TDA.Persistence.RankResolutionDegreeTwoSimplicialScaledTranslationExamples
