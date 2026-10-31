import TDA.Persistence.RankResolutionDegreeTwoSimplicialScaling
import Mathlib.Data.Rat.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Ordinary-import consumers of positive simplicial scaling

These clients use the actual scaled PH₁ modules, arm maps, finite interleaving
witnesses and the distance-to-zero theorem over arbitrary fields, ℚ and ZMod 2.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence.RankResolutionDegreeTwoSimplicialScalingExamples

open CategoryTheory CategoryTheory.Limits
open TDA.Persistence.RankResolutionDegreeTwoSimplicial
open RankResolutionDegreeTwo
open scoped TDA.Persistence NNReal ENNReal ZeroObject

private def scale11 : Fin 2 → ℝ := fun _ => 1
private def scale22 : Fin 2 → ℝ := ![(2 : ℝ), 2]
private def scale41 : Fin 2 → ℝ := ![(4 : ℝ), 1]
private def scale14 : Fin 2 → ℝ := ![(1 : ℝ), 4]
private noncomputable def scaleThreeHalvesOne : Fin 2 → ℝ := ![(3 / 2 : ℝ), 1]
private def scale21 : Fin 2 → ℝ := ![(2 : ℝ), 1]
private noncomputable def scaleQuarterOne : Fin 2 → ℝ := ![(1 / 4 : ℝ), 1]

private theorem scale11_pos : ∀ i, 0 < scale11 i := by
  intro i
  fin_cases i <;> norm_num [scale11]

private theorem scale22_pos : ∀ i, 0 < scale22 i := by
  intro i
  fin_cases i <;> norm_num [scale22]

private theorem scale41_pos : ∀ i, 0 < scale41 i := by
  intro i
  fin_cases i <;> norm_num [scale41]

private theorem scale14_pos : ∀ i, 0 < scale14 i := by
  intro i
  fin_cases i <;> norm_num [scale14]

private theorem scaleThreeHalvesOne_pos : ∀ i, 0 < scaleThreeHalvesOne i := by
  intro i
  fin_cases i <;> norm_num [scaleThreeHalvesOne]

private theorem scale21_pos : ∀ i, 0 < scale21 i := by
  intro i
  fin_cases i <;> norm_num [scale21]

private theorem scaleQuarterOne_pos : ∀ i, 0 < scaleQuarterOne i := by
  intro i
  fin_cases i <;> norm_num [scaleQuarterOne]

private theorem distance_scale41_anyField (k : Type u) [Field k] :
    coordinateInterleavingDistance (scaledHomology k scale41 scale41_pos)
      (0 : PModule.{u,0,u} k (Fin 2 → ℝ)) = 1 := by
  rw [coordinateInterleavingDistance_scaledHomology_zero]
  norm_num [scaledLifetime, scaledArmLifetimeA, scaledArmLifetimeB, scale41]

private theorem distance_scale14_anyField (k : Type u) [Field k] :
    coordinateInterleavingDistance (scaledHomology k scale14 scale14_pos)
      (0 : PModule.{u,0,u} k (Fin 2 → ℝ)) = 1 := by
  rw [coordinateInterleavingDistance_scaledHomology_zero]
  norm_num [scaledLifetime, scaledArmLifetimeA, scaledArmLifetimeB, scale14]

example (k : Type u) [Field k] :
    coordinateInterleavingDistance (scaledHomology k scale11 scale11_pos)
      (0 : PModule.{u,0,u} k (Fin 2 → ℝ)) = ENNReal.ofReal (1 / 2 : ℝ) := by
  rw [coordinateInterleavingDistance_scaledHomology_zero]
  norm_num [scaledLifetime, scaledArmLifetimeA, scaledArmLifetimeB, scale11, ENNReal.ofReal]

example (k : Type u) [Field k] :
    coordinateInterleavingDistance (scaledHomology k scale22 scale22_pos)
      (0 : PModule.{u,0,u} k (Fin 2 → ℝ)) = 1 := by
  rw [coordinateInterleavingDistance_scaledHomology_zero]
  norm_num [scaledLifetime, scaledArmLifetimeA, scaledArmLifetimeB, scale22]

example (k : Type u) [Field k] := distance_scale41_anyField k

example (k : Type u) [Field k] := distance_scale14_anyField k

example (k : Type u) [Field k] :
    coordinateInterleavingDistance (scaledHomology k scaleThreeHalvesOne scaleThreeHalvesOne_pos)
      (0 : PModule.{u,0,u} k (Fin 2 → ℝ)) = ENNReal.ofReal (3 / 4 : ℝ) := by
  rw [coordinateInterleavingDistance_scaledHomology_zero]
  norm_num [scaledLifetime, scaledArmLifetimeA, scaledArmLifetimeB, scaleThreeHalvesOne,
    ENNReal.ofReal]

example (k : Type u) [Field k] :
    coordinateInterleavingDistance (scaledHomology k scale21 scale21_pos)
      (0 : PModule.{u,0,u} k (Fin 2 → ℝ)) = 1 := by
  rw [coordinateInterleavingDistance_scaledHomology_zero]
  norm_num [scaledLifetime, scaledArmLifetimeA, scaledArmLifetimeB, scale21]

example (k : Type u) [Field k] :
    coordinateInterleavingDistance (scaledHomology k scaleQuarterOne scaleQuarterOne_pos)
      (0 : PModule.{u,0,u} k (Fin 2 → ℝ)) = ENNReal.ofReal (1 / 4 : ℝ) := by
  rw [coordinateInterleavingDistance_scaledHomology_zero]
  norm_num [scaledLifetime, scaledArmLifetimeA, scaledArmLifetimeB, scaleQuarterOne,
    ENNReal.ofReal]

example : scaledGrading scale11 scale11_pos = boundaryTetrahedronGrading := by
  change scaledGrading (fun _ : Fin 2 => (1 : ℝ)) (fun _ => by norm_num) = _
  exact scaledGrading_one

example (k : Type u) [Field k] :
    scaledHomology k scale11 scale11_pos =
      finiteSimplicialHomology k boundaryTetrahedronGrading 1 := by
  change scaledHomology k (fun _ : Fin 2 => (1 : ℝ)) (fun _ => by norm_num) = _
  exact scaledHomology_one k

example {p q : Fin 2 → ℝ} (hpq : p ≤ q) :
    structureMap (scaledHomology ℚ scale41 scale41_pos) hpq ≫
        (scaledRealIso ℚ scale41 scale41_pos).hom.app q =
      (scaledRealIso ℚ scale41 scale41_pos).hom.app p ≫
        structureMap (realModule (k := ℚ))
          ((scalingPullback scale41 scale41_pos).monotone' hpq) :=
  scaledRealIso_structureMap ℚ scale41 scale41_pos hpq

example : (scaledHomologyZeroInterleaving ℚ scale41 scale41_pos).φ = 0 := by simp

example : (scaledHomologyZeroInterleaving ℚ scale41 scale41_pos).ψ = 0 := by simp

example (p : Fin 2 → ℝ) :
    (scaledHomologyZeroInterleaving ℚ scale41 scale41_pos).φ.app p ≫
        (scaledHomologyZeroInterleaving ℚ scale41 scale41_pos).ψ.app
          (CoordinateShift.translation
            (Real.toNNReal (scaledLifetime scale41 / 2)) p) =
      structureMap (scaledHomology ℚ scale41 scale41_pos)
        (CoordinateInterleaving.twice_le
          (Real.toNNReal (scaledLifetime scale41 / 2)) p) :=
  (scaledHomologyZeroInterleaving ℚ scale41 scale41_pos).φ_ψ_structureMap p

example (p : Fin 2 → ℝ) :
    (scaledHomologyZeroInterleaving ℚ scale41 scale41_pos).ψ.app p ≫
        (scaledHomologyZeroInterleaving ℚ scale41 scale41_pos).φ.app
          (CoordinateShift.translation
            (Real.toNNReal (scaledLifetime scale41 / 2)) p) =
      structureMap (0 : PModule ℚ (Fin 2 → ℝ))
        (CoordinateInterleaving.twice_le
          (Real.toNNReal (scaledLifetime scale41 / 2)) p) :=
  (scaledHomologyZeroInterleaving ℚ scale41 scale41_pos).symm.φ_ψ_structureMap p

example : scaledArmLifetimeA scale41 = 1 := by
  norm_num [scaledArmLifetimeA, scale41]

example : scaledArmLifetimeB scale41 = 2 := by
  norm_num [scaledArmLifetimeB, scale41]

example : scaledArmLifetimeA scale14 = 2 := by
  norm_num [scaledArmLifetimeA, scale14]

example : scaledArmLifetimeB scale14 = 1 := by
  norm_num [scaledArmLifetimeB, scale14]

example : scaledArmLifetimeB scale21 = 2 := by
  norm_num [scaledArmLifetimeB, scale21]

example : scaledArmLifetimeB scale21 = min (scale21 0) (2 * scale21 1) := rfl

example : ¬ IsZero ((scaledHomology ℚ scale41 scale41_pos).obj (scaledBirthA scale41)) :=
  scaledHomology_birthA_not_isZero ℚ scale41 scale41_pos

example : ¬ IsZero ((scaledHomology ℚ scale41 scale41_pos).obj (scaledBirthB scale41)) :=
  scaledHomology_birthB_not_isZero ℚ scale41 scale41_pos

example (p : Fin 2 → ℝ) :
    structureMap (scaledHomology ℚ scale41 scale41_pos)
      (show p ≤ (fun i => p i + 2) from fun _ => by norm_num) = 0 :=
  scaledHomology_lifetime_structureMap_zero ℚ scale41 scale41_pos 2
    (by norm_num [scaledLifetime, scaledArmLifetimeA, scaledArmLifetimeB, scale41]) p

example : structureMap (scaledHomology ℚ scale41 scale41_pos)
    (show scaledBirthB scale41 ≤ (fun i => scaledBirthB scale41 i + 3 / 2) from
      fun _ => le_add_of_nonneg_right (by norm_num)) ≠ 0 := by
  apply (scaledHomology_armB_structureMap_ne_zero_iff ℚ scale41 scale41_pos
    (3 / 2) (by norm_num)).2
  norm_num [scaledArmLifetimeB, scale41]

example : structureMap (scaledHomology ℚ scale41 scale41_pos)
    (show scaledBirthA scale41 ≤ (fun i => scaledBirthA scale41 i + 1) from
      fun _ => le_add_of_nonneg_right (by norm_num)) = 0 := by
  simpa using scaledHomology_armA_structureMap_zero_of_ge ℚ scale41 scale41_pos 1
    (by norm_num) (by norm_num [scaledArmLifetimeA, scale41])

example : structureMap (scaledHomology ℚ scale41 scale41_pos)
    (show scaledBirthB scale41 ≤ (fun i => scaledBirthB scale41 i + 2) from
      fun _ => le_add_of_nonneg_right (by norm_num)) = 0 := by
  apply scaledHomology_armB_structureMap_zero_of_ge ℚ scale41 scale41_pos 2
    (by norm_num)
  norm_num [scaledArmLifetimeB, scale41]

example : structureMap (scaledHomology ℚ scale14 scale14_pos)
    (show scaledBirthA scale14 ≤ (fun i => scaledBirthA scale14 i + 3 / 2) from
      fun _ => le_add_of_nonneg_right (by norm_num)) ≠ 0 := by
  apply (scaledHomology_armA_structureMap_ne_zero_iff ℚ scale14 scale14_pos
    (3 / 2) (by norm_num)).2
  norm_num [scaledArmLifetimeA, scale14]

example : structureMap (scaledHomology ℚ scale14 scale14_pos)
    (show scaledBirthA scale14 ≤ (fun i => scaledBirthA scale14 i + 2) from
      fun _ => le_add_of_nonneg_right (by norm_num)) = 0 := by
  apply scaledHomology_armA_structureMap_zero_of_ge ℚ scale14 scale14_pos 2
    (by norm_num)
  norm_num [scaledArmLifetimeA, scale14]

example : structureMap (scaledHomology ℚ scale14 scale14_pos)
    (show scaledBirthB scale14 ≤ (fun i => scaledBirthB scale14 i + 1) from
      fun _ => le_add_of_nonneg_right (by norm_num)) = 0 := by
  apply scaledHomology_armB_structureMap_zero_of_ge ℚ scale14 scale14_pos 1
    (by norm_num)
  norm_num [scaledArmLifetimeB, scale14]

example : structureMap (scaledHomology ℚ scale21 scale21_pos)
    (show scaledBirthB scale21 ≤ (fun i => scaledBirthB scale21 i + 3 / 2) from
      fun _ => le_add_of_nonneg_right (by norm_num)) ≠ 0 := by
  apply (scaledHomology_armB_structureMap_ne_zero_iff ℚ scale21 scale21_pos
    (3 / 2) (by norm_num)).2
  norm_num [scaledArmLifetimeB, scale21]

example : structureMap (scaledHomology ℚ scale21 scale21_pos)
    (show scaledBirthB scale21 ≤ (fun i => scaledBirthB scale21 i + 2) from
      fun _ => le_add_of_nonneg_right (by norm_num)) = 0 := by
  apply scaledHomology_armB_structureMap_zero_of_ge ℚ scale21 scale21_pos 2
    (by norm_num)
  norm_num [scaledArmLifetimeB, scale21]

private noncomputable def scale41LongTarget : Fin 2 → ℝ :=
  fun i => scaledBirthB scale41 i + 3 / 2

private theorem scale41LongTarget_pullback :
    scalingPullback scale41 scale41_pos scale41LongTarget = ![(11 / 8 : ℝ), 3 / 2] := by
  funext i
  fin_cases i <;>
    norm_num [scale41LongTarget, scalingPullback_apply, scaledBirthB, scale41]

private theorem scaleGridCoordinate_cases (q : grid.Point) (i : Fin 2) :
    (q i).val = 0 ∨ (q i).val = 1 ∨ (q i).val = 2 := by
  have h : (q i).val ∈ gridValues := by simp [grid]
  simpa only [gridValues, Finset.mem_insert, Finset.mem_singleton] using h

private theorem scale41LongTargetPullback_hasLowerPoint :
    grid.HasLowerPoint (scalingPullback scale41 scale41_pos scale41LongTarget) := by
  refine ⟨c, ?_⟩
  rw [grid_embedding_c, scale41LongTarget_pullback]
  intro i
  fin_cases i <;> norm_num

private theorem q_le_c_of_le_scale41LongTarget (q : grid.Point)
    (hq : grid.embedding q ≤ scalingPullback scale41 scale41_pos scale41LongTarget) : q ≤ c := by
  have hq0 : (q 0).val ≤ 1 := by
    have hqi : (q 0).val ≤ (11 / 8 : ℝ) := by
      have h := hq 0
      change (q 0).val ≤ scale41LongTarget 0 / scale41 0 at h
      norm_num [scale41LongTarget, scaledBirthB, scale41] at h
      exact h
    rcases scaleGridCoordinate_cases q 0 with h0 | h1 | h2
    · norm_num [h0]
    · norm_num [h1]
    · rw [h2] at hqi
      norm_num at hqi
  have hq1 : (q 1).val ≤ 1 := by
    have hqi : (q 1).val ≤ (3 / 2 : ℝ) := by
      have h := hq 1
      change (q 1).val ≤ scale41LongTarget 1 / scale41 1 at h
      norm_num [scale41LongTarget, scaledBirthB, scale41] at h
      exact h
    rcases scaleGridCoordinate_cases q 1 with h0 | h1 | h2
    · norm_num [h0]
    · norm_num [h1]
    · rw [h2] at hqi
      norm_num at hqi
  intro i
  fin_cases i
  · change (q 0).val ≤ (c 0).val
    rw [show (c 0).val = 1 by
      have h := congrFun grid_embedding_c 0
      simpa only [CoordinateGrid.embedding_apply] using h]
    exact hq0
  · change (q 1).val ≤ (c 1).val
    rw [show (c 1).val = 1 by
      have h := congrFun grid_embedding_c 1
      simpa only [CoordinateGrid.embedding_apply] using h]
    exact hq1

private theorem scale41LongTarget_floor :
    grid.floor (scalingPullback scale41 scale41_pos scale41LongTarget)
      scale41LongTargetPullback_hasLowerPoint = c := by
  apply (grid.floor_eq_iff (scalingPullback scale41 scale41_pos scale41LongTarget)
    scale41LongTargetPullback_hasLowerPoint c).2
  constructor
  · rw [grid_embedding_c, scale41LongTarget_pullback]
    intro i
    fin_cases i <;> norm_num
  · exact q_le_c_of_le_scale41LongTarget

example : grid.floor (scalingPullback scale41 scale41_pos scale41LongTarget)
    scale41LongTargetPullback_hasLowerPoint = c :=
  scale41LongTarget_floor

example : IsEmpty (CoordinateInterleaving (3 / 4)
    (scaledHomology ℚ scale41 scale41_pos) (0 : PModule ℚ (Fin 2 → ℝ))) := by
  exact scaledHomology_no_zero_interleaving ℚ scale41 scale41_pos (3 / 4)
    (by norm_num [scaledLifetime, scaledArmLifetimeA, scaledArmLifetimeB, scale41])

example : IsEmpty (CoordinateInterleaving (3 / 4)
    (scaledHomology ℚ scale14 scale14_pos) (0 : PModule ℚ (Fin 2 → ℝ))) := by
  exact scaledHomology_no_zero_interleaving ℚ scale14 scale14_pos (3 / 4)
    (by norm_num [scaledLifetime, scaledArmLifetimeA, scaledArmLifetimeB, scale14])

example : IsEmpty (CoordinateInterleaving (3 / 4)
    (scaledHomology (ZMod 2) scale41 scale41_pos)
      (0 : PModule (ZMod 2) (Fin 2 → ℝ))) := by
  exact scaledHomology_no_zero_interleaving (ZMod 2) scale41 scale41_pos (3 / 4)
    (by norm_num [scaledLifetime, scaledArmLifetimeA, scaledArmLifetimeB, scale41])

example : IsEmpty (CoordinateInterleaving (3 / 4)
    (scaledHomology (ZMod 2) scale14 scale14_pos)
      (0 : PModule (ZMod 2) (Fin 2 → ℝ))) := by
  exact scaledHomology_no_zero_interleaving (ZMod 2) scale14 scale14_pos (3 / 4)
    (by norm_num [scaledLifetime, scaledArmLifetimeA, scaledArmLifetimeB, scale14])

example :
    coordinateInterleavingDistance (scaledHomology ℚ scale41 scale41_pos)
      (0 : PModule ℚ (Fin 2 → ℝ)) = 1 := distance_scale41_anyField ℚ

example :
    coordinateInterleavingDistance (scaledHomology (ZMod 2) scale41 scale41_pos)
      (0 : PModule (ZMod 2) (Fin 2 → ℝ)) = 1 := distance_scale41_anyField (ZMod 2)

example :
    coordinateInterleavingDistance (scaledHomology ℚ scale14 scale14_pos)
      (0 : PModule ℚ (Fin 2 → ℝ)) = 1 := distance_scale14_anyField ℚ

example :
    coordinateInterleavingDistance (scaledHomology (ZMod 2) scale14 scale14_pos)
      (0 : PModule (ZMod 2) (Fin 2 → ℝ)) = 1 := distance_scale14_anyField (ZMod 2)

end TDA.Persistence.RankResolutionDegreeTwoSimplicialScalingExamples
