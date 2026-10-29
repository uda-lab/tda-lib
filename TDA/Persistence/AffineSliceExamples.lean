import TDA.Persistence.PositiveAffineSlice
import TDA.Persistence.AffineSliceHooks
import TDA.Persistence.AffineSlicePresentation
import Mathlib.Tactic

/-!
# Concrete positive affine slices

The examples use nonunit and unequal slopes, actual hook modules, and occurrence
multiplicities. In particular, a nonzero planar hook can have an empty slice.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence.AffineSliceExamples

open CategoryTheory CategoryTheory.Limits
open scoped TDA.Persistence

private def nonunitLine : PositiveAffineLine 1 where
  offset _ := 3
  slope _ := 2
  slope_pos _ := by norm_num

/-- The grade `7` is reached at time `2` on the line `3 + 2t`. -/
theorem nonunit_slope_entrance : nonunitLine.entrance (fun _ => 7) = 2 := by
  apply le_antisymm
  · apply (nonunitLine.entrance_le_iff _ _).mpr
    intro i
    norm_num [PositiveAffineLine.orderHom_apply, nonunitLine]
  · have h := nonunitLine.normalizedDifference_le_entrance (fun _ => 7) 0
    norm_num [nonunitLine] at h
    exact h

private def tiltedLine : PositiveAffineLine 2 where
  offset i := if i = 0 then 1 else -1
  slope i := if i = 0 then 2 else 1
  slope_pos i := by fin_cases i <;> norm_num

/-- Unequal slopes and offsets place time `2` at coordinate grade `(5,1)`. -/
theorem unequal_slopes_and_offsets :
    tiltedLine.orderHom 2 = fun i => if i = 0 then 5 else 1 := by
  funext i
  fin_cases i <;> norm_num [PositiveAffineLine.orderHom_apply, tiltedLine]

/-- The smaller slope, rather than the larger one, controls diagonal padding. -/
theorem tilted_minimum_slope : tiltedLine.minSlope = 1 := by
  apply le_antisymm
  · exact_mod_cast (show (tiltedLine.minSlope : ℝ) ≤ 1 by
      simpa [tiltedLine] using tiltedLine.minSlope_le_slope 1)
  · apply NNReal.coe_le_coe.mp
    apply (tiltedLine.le_minSlope_iff 1).mpr
    intro i
    fin_cases i <;> norm_num [tiltedLine]

private def collapseBirth : Fin 2 → ℝ := fun i => if i = 0 then 1 else 0
private def collapseDeath : Fin 2 → ℝ := fun i => if i = 0 then 2 else 0

private theorem collapse_lt : collapseBirth < collapseDeath := by
  apply lt_iff_le_not_ge.mpr
  constructor
  · intro i
    fin_cases i <;> norm_num [collapseBirth, collapseDeath]
  · intro h
    have h0 := h 0
    norm_num [collapseBirth, collapseDeath] at h0

private theorem collapse_birth_entrance : tiltedLine.entrance collapseBirth = 1 := by
  apply le_antisymm
  · apply (tiltedLine.entrance_le_iff _ _).mpr
    intro i
    fin_cases i <;> norm_num [PositiveAffineLine.orderHom_apply, tiltedLine, collapseBirth]
  · have h := tiltedLine.normalizedDifference_le_entrance collapseBirth 1
    norm_num [tiltedLine, collapseBirth] at h
    exact h

private theorem collapse_death_entrance : tiltedLine.entrance collapseDeath = 1 := by
  apply le_antisymm
  · apply (tiltedLine.entrance_le_iff _ _).mpr
    intro i
    fin_cases i <;> norm_num [PositiveAffineLine.orderHom_apply, tiltedLine, collapseDeath]
  · have h := tiltedLine.normalizedDifference_le_entrance collapseDeath 1
    norm_num [tiltedLine, collapseDeath] at h
    exact h

/-- The planar hook that disappears on the slice has a nonzero
birth fibre, over every coefficient field. -/
theorem collapse_original_nonzero (k : Type u) [Field k] :
    ∃ x : (Hook.module (k := k) collapseBirth collapseDeath).obj collapseBirth, x ≠ 0 := by
  refine ⟨SupportInterval.one (Hook.support collapseBirth collapseDeath)
    (Hook.birth_mem collapse_lt), ?_⟩
  intro hz
  have hval := congrArg Subtype.val hz
  exact (one_ne_zero : (1 : k) ≠ 0) hval

private def retainedBirth₀ : Fin 2 → ℝ := fun i => if i = 0 then 1 else -1
private def retainedDeath₀ : Fin 2 → ℝ := fun i => if i = 0 then 3 else 1
private def retainedBirth₁ : Fin 2 → ℝ := fun i => if i = 0 then 0 else -1
private def retainedDeath₁ : Fin 2 → ℝ := fun i => if i = 0 then 2 else 1

private theorem retained_lt₀ : retainedBirth₀ < retainedDeath₀ := by
  apply lt_iff_le_not_ge.mpr
  constructor
  · intro i
    fin_cases i <;> norm_num [retainedBirth₀, retainedDeath₀]
  · intro h
    have h0 := h 0
    norm_num [retainedBirth₀, retainedDeath₀] at h0

private theorem retained_lt₁ : retainedBirth₁ < retainedDeath₁ := by
  apply lt_iff_le_not_ge.mpr
  constructor
  · intro i
    fin_cases i <;> norm_num [retainedBirth₁, retainedDeath₁]
  · intro h
    have h0 := h 0
    norm_num [retainedBirth₁, retainedDeath₁] at h0

private theorem retained_birth₀_entrance : tiltedLine.entrance retainedBirth₀ = 0 := by
  apply le_antisymm
  · apply (tiltedLine.entrance_le_iff _ _).mpr
    intro i
    fin_cases i <;> norm_num [PositiveAffineLine.orderHom_apply, tiltedLine, retainedBirth₀]
  · have h := tiltedLine.normalizedDifference_le_entrance retainedBirth₀ 1
    norm_num [tiltedLine, retainedBirth₀] at h
    exact h

private theorem retained_death₀_entrance : tiltedLine.entrance retainedDeath₀ = 2 := by
  apply le_antisymm
  · apply (tiltedLine.entrance_le_iff _ _).mpr
    intro i
    fin_cases i <;> norm_num [PositiveAffineLine.orderHom_apply, tiltedLine, retainedDeath₀]
  · have h := tiltedLine.normalizedDifference_le_entrance retainedDeath₀ 1
    norm_num [tiltedLine, retainedDeath₀] at h
    exact h

private theorem retained_birth₁_entrance : tiltedLine.entrance retainedBirth₁ = 0 := by
  apply le_antisymm
  · apply (tiltedLine.entrance_le_iff _ _).mpr
    intro i
    fin_cases i <;> norm_num [PositiveAffineLine.orderHom_apply, tiltedLine, retainedBirth₁]
  · have h := tiltedLine.normalizedDifference_le_entrance retainedBirth₁ 1
    norm_num [tiltedLine, retainedBirth₁] at h
    exact h

private theorem retained_death₁_entrance : tiltedLine.entrance retainedDeath₁ = 2 := by
  apply le_antisymm
  · apply (tiltedLine.entrance_le_iff _ _).mpr
    intro i
    fin_cases i <;> norm_num [PositiveAffineLine.orderHom_apply, tiltedLine, retainedDeath₁]
  · have h := tiltedLine.normalizedDifference_le_entrance retainedDeath₁ 1
    norm_num [tiltedLine, retainedDeath₁] at h
    exact h

private theorem retained_support (t : ℝ) (ht0 : 0 ≤ t) (ht2 : t < 2) :
    tiltedLine.orderHom t ∈ Hook.support retainedBirth₀ retainedDeath₀ := by
  constructor
  · apply (tiltedLine.entrance_le_iff _ _).mp
    rwa [retained_birth₀_entrance]
  · intro h
    have hd := (tiltedLine.entrance_le_iff _ _).mpr h
    rw [retained_death₀_entrance] at hd
    exact (not_le_of_gt ht2) hd

/-- Inside the retained interval the actual restricted hook has a nonzero
structure map, so this slice contains persistent information. -/
theorem retained_slice_nonzero_transition (k : Type u) [Field k] :
    structureMapLinear (reindex tiltedLine.orderHom
      (Hook.module (k := k) retainedBirth₀ retainedDeath₀))
      (show (0 : ℝ) ≤ 1 by norm_num) ≠ 0 := by
  change structureMapLinear (Hook.module (k := k) retainedBirth₀ retainedDeath₀)
    (tiltedLine.orderHom.monotone' (show (0 : ℝ) ≤ 1 by norm_num)) ≠ 0
  intro hz
  exact ((SupportInterval.structureMap_eq_zero_iff
    (Hook.support retainedBirth₀ retainedDeath₀)
    (Hook.support_ordConnected retainedBirth₀ retainedDeath₀) _).mp hz)
      ⟨retained_support 0 le_rfl (by norm_num),
        retained_support 1 (by norm_num) (by norm_num)⟩

/-- The finite right endpoint is excluded: the actual transition to time `2`
kills the previously surviving class. -/
theorem retained_slice_dies_at_endpoint (k : Type u) [Field k] :
    structureMapLinear (reindex tiltedLine.orderHom
      (Hook.module (k := k) retainedBirth₀ retainedDeath₀))
      (show (1 : ℝ) ≤ 2 by norm_num) = 0 := by
  change structureMapLinear (Hook.module (k := k) retainedBirth₀ retainedDeath₀)
    (tiltedLine.orderHom.monotone' (show (1 : ℝ) ≤ 2 by norm_num)) = 0
  apply SupportInterval.structureMap_eq_zero_of_not_mem
  intro h
  apply h.2.2
  apply (tiltedLine.entrance_le_iff _ _).mp
  rw [retained_death₀_entrance]

/-- A nonunit slope gives the actual half-open slice `[2,4)`, with its original
structure maps, rather than leaving the coordinate endpoints unchanged. -/
theorem nonunit_slope_hook_interval (k : Type u) [Field k] :
    reindex nonunitLine.orderHom (Hook.module (k := k) (fun _ => 7) (fun _ => 11)) =
      RealBarcode.intervalModule (k := k) (2, (4 : WithTop ℝ)) := by
  have hd : nonunitLine.entrance (fun _ => 11) = 4 := by
    apply le_antisymm
    · apply (nonunitLine.entrance_le_iff _ _).mpr
      intro i
      norm_num [PositiveAffineLine.orderHom_apply, nonunitLine]
    · have h := nonunitLine.normalizedDifference_le_entrance (fun _ => 11) 0
      norm_num [nonunitLine] at h
      exact h
  rw [nonunitLine.finiteHook_reindex_eq, nonunit_slope_entrance, hd]
  norm_num

/-- This actual nonzero multidimensional hook becomes the zero module on the
positive slice: both entrance times are `1`. -/
theorem collapse_slice_zero (k : Type u) [Field k] :
    IsZero (reindex tiltedLine.orderHom (Hook.module (k := k) collapseBirth collapseDeath)) :=
  tiltedLine.finiteHook_reindex_isZero_of_entrance_eq _ _
    (collapse_birth_entrance.trans collapse_death_entrance.symm)

/-- The retained hook comparison identifies the actual slice with `[0,2)`. -/
theorem retained_slice_interval (k : Type u) [Field k] :
    reindex tiltedLine.orderHom (Hook.module (k := k) retainedBirth₀ retainedDeath₀) =
      RealBarcode.intervalModule (k := k) (0, (2 : WithTop ℝ)) := by
  rw [tiltedLine.finiteHook_reindex_eq, retained_birth₀_entrance, retained_death₀_entrance]
  norm_num

/-- The principal hook has essential death, with no finite cutoff introduced by
restriction to a line. -/
theorem principal_slice_essential_interval (k : Type u) [Field k] :
    Nonempty (reindex tiltedLine.orderHom (HookInfinity.module (R := k) retainedBirth₀) ≅
      RealBarcode.intervalModule (k := k) (0, (⊤ : WithTop ℝ))) := by
  have e := tiltedLine.principalHook_reindexIso (k := k) retainedBirth₀
  rw [retained_birth₀_entrance] at e
  exact ⟨e⟩

/-- A principal class survives the actual restricted map from birth to time
`10`, beyond the finite hook's death. -/
theorem principal_slice_transition_nonzero (k : Type u) [Field k] :
    structureMapLinear (reindex tiltedLine.orderHom
      (HookInfinity.module (R := k) retainedBirth₀))
      (show (0 : ℝ) ≤ 10 by norm_num) ≠ 0 := by
  let hbirth : retainedBirth₀ ≤ tiltedLine.orderHom 0 :=
    (tiltedLine.entrance_le_iff _ _).mp (by rw [retained_birth₀_entrance])
  let hmap := tiltedLine.orderHom.monotone' (show (0 : ℝ) ≤ 10 by norm_num)
  let x := (HookInfinity.fiberEquivOfLe (R := k) hbirth).symm 1
  have hcoef : HookInfinity.fiberEquivOfLe (R := k) (hbirth.trans hmap)
      (structureMapLinear (HookInfinity.module (R := k) retainedBirth₀) hmap x) = 1 := by
    rw [HookInfinity.fiberEquivOfLe_structureMap]
    exact LinearEquiv.apply_symm_apply _ _
  intro hz
  change structureMapLinear (HookInfinity.module (R := k) retainedBirth₀) hmap = 0 at hz
  rw [hz, LinearMap.zero_apply, map_zero] at hcoef
  exact zero_ne_one hcoef

private def retainedTag₀ : RealHookTag (n := 2) :=
  .inl ⟨(retainedBirth₀, retainedDeath₀), retained_lt₀⟩
private def retainedTag₁ : RealHookTag (n := 2) :=
  .inl ⟨(retainedBirth₁, retainedDeath₁), retained_lt₁⟩
private def collapseTag : RealHookTag (n := 2) :=
  .inl ⟨(collapseBirth, collapseDeath), collapse_lt⟩

private theorem retained_tags_distinct : retainedTag₀ ≠ retainedTag₁ := by
  intro he
  have hv := congrArg (fun tag : RealHookTag (n := 2) => match tag with
    | .inl pq => pq.val.1 0
    | .inr p => p 0) he
  norm_num [retainedTag₀, retainedTag₁, retainedBirth₀, retainedBirth₁] at hv

/-- Distinct planar hooks yield two copies of `[0,2)`; the third
nonzero hook is omitted because its slice is empty. -/
theorem repeated_retained_endpoints :
    retainedTag₀ ≠ retainedTag₁ ∧
      tiltedLine.sliceHookMultiset ({retainedTag₀} + {retainedTag₁} + {collapseTag}) =
        {(0, (2 : WithTop ℝ))} + {(0, (2 : WithTop ℝ))} := by
  classical
  refine ⟨retained_tags_distinct, ?_⟩
  rw [tiltedLine.sliceHookMultiset_add, tiltedLine.sliceHookMultiset_add,
    tiltedLine.sliceHookMultiset_singleton, tiltedLine.sliceHookMultiset_singleton,
    tiltedLine.sliceHookMultiset_singleton]
  norm_num [retainedTag₀, retainedTag₁, collapseTag, retained_birth₀_entrance,
    retained_death₀_entrance, retained_birth₁_entrance, retained_death₁_entrance,
    collapse_birth_entrance, collapse_death_entrance]

/-- Endpoint extraction counts occurrences even when their endpoint values
coincide, rather than deduplicating them. -/
theorem repeated_retained_endpoints_count :
    (tiltedLine.sliceHookMultiset ({retainedTag₀} + {retainedTag₁} + {collapseTag})).count
      (0, (2 : WithTop ℝ)) = 2 := by
  classical
  rw [repeated_retained_endpoints.2]
  simp

/-- A principal occurrence is retained with death exactly infinity. -/
theorem principal_endpoint_infinite :
    tiltedLine.sliceHookMultiset {Sum.inr retainedBirth₀} = {(0, (⊤ : WithTop ℝ))} := by
  simp [retained_birth₀_entrance]

private abbrev noGenerators (n : ℕ) : GradedFree.GradedGenerators.{0,0} (Fin n → ℝ) where
  Carrier := Fin 0
  grade := Fin.elim0

/-- Empty original generator and relation families yield an original finite
presentation of the actual real slice, even over arbitrary coefficient rings. -/
theorem empty_original_presentation_slice (R : Type u) [Ring R] :
    GradedFree.FinitelyPresented.{u,0,0}
      (reindex tiltedLine.orderHom (GradedFree.module (R := R) (noGenerators 2))) :=
  tiltedLine.finitelyPresented_slice (GradedFree.free_finitelyPresented (noGenerators 2))

/-- With no original generators, every actual slice fibre is zero. -/
theorem empty_original_slice_zero (R : Type u) [Ring R] :
    IsZero (reindex tiltedLine.orderHom (GradedFree.module (R := R) (noGenerators 2))) := by
  apply Functor.isZero
  intro t
  have : Subsingleton ((reindex tiltedLine.orderHom
      (GradedFree.module (R := R) (noGenerators 2))).obj t) := by
    constructor
    intro x y
    apply Subtype.ext
    apply Finsupp.ext
    intro i
    exact Fin.elim0 i
  exact ModuleCat.isZero_of_subsingleton _

/-- The same empty original presentation reaches the one-coordinate interface
required by ordinary barcode consumers without a slice presentation premise. -/
theorem empty_original_presentation_fromReal_slice (R : Type u) [Ring R] :
    GradedFree.FinitelyPresented.{u,0,0}
      (CoordinateRealBridge.fromReal
        (reindex tiltedLine.orderHom (GradedFree.module (R := R) (noGenerators 2)))) :=
  tiltedLine.finitelyPresented_fromReal_slice
    (GradedFree.free_finitelyPresented (noGenerators 2))

end TDA.Persistence.AffineSliceExamples
