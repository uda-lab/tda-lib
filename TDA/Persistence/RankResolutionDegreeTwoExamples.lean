import TDA.Persistence.RankResolutionDegreeTwo
import Mathlib.Data.Rat.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Concrete degree-two rank-resolution consumers

These consumers specialize the arbitrary-field construction to the rationals
and characteristic two. They check the actual public finite maps and the real
hook's supported arms and death boundary.
-/

set_option autoImplicit false

namespace TDA.Persistence.RankResolutionDegreeTwo.Examples

open CategoryTheory CategoryTheory.Limits
open TDA.Persistence.RankResolutionDegreeTwo
open scoped TDA.Persistence ZeroObject

/-- The real hook's upper-arm test grade `(1,2)`. -/
abbrev realFGrade : Fin 2 → ℝ := fun i => if i = 0 then 1 else 2

/-- The real hook's right-arm test grade `(2,1)`. -/
abbrev realGGrade : Fin 2 → ℝ := fun i => if i = 0 then 2 else 1

private theorem birth_le_fGrade : realSecondBirth ≤ realFGrade := by
  intro i
  fin_cases i <;> norm_num [realSecondBirth, realFGrade]

private theorem birth_le_gGrade : realSecondBirth ≤ realGGrade := by
  intro i
  fin_cases i <;> norm_num [realSecondBirth, realGGrade]

private theorem death_not_le_fGrade : ¬ realSecondDeath ≤ realFGrade := by
  intro h
  have h0 := h 0
  norm_num [realSecondDeath, realFGrade] at h0

private theorem death_not_le_gGrade : ¬ realSecondDeath ≤ realGGrade := by
  intro h
  have h1 := h 1
  norm_num [realSecondDeath, realGGrade] at h1

private theorem fGrade_mem_hook : realFGrade ∈ Hook.support realSecondBirth realSecondDeath :=
  ⟨birth_le_fGrade, death_not_le_fGrade⟩

private theorem gGrade_mem_hook : realGGrade ∈ Hook.support realSecondBirth realSecondDeath :=
  ⟨birth_le_gGrade, death_not_le_gGrade⟩

private noncomputable def realHookBirthUnit (k : Type) [Field k] :
    (realSecondHook (k := k)).obj realSecondBirth :=
  SupportInterval.one (Hook.support realSecondBirth realSecondDeath)
    (Hook.birth_mem realSecondHook_birth_lt_death)

private theorem realHook_birthToF_nonzero (k : Type) [Field k] :
    structureMapLinear (realSecondHook (k := k)) birth_le_fGrade
      (realHookBirthUnit k) ≠ 0 := by
  intro hz
  have hzero := congrArg Subtype.val hz
  have hval := SupportInterval.structureMap_val
    (Hook.support realSecondBirth realSecondDeath)
    (Hook.support_ordConnected realSecondBirth realSecondDeath)
    birth_le_fGrade (realHookBirthUnit k)
  rw [if_pos fGrade_mem_hook] at hval
  have hone : ((structureMapLinear (realSecondHook (k := k))
      birth_le_fGrade (realHookBirthUnit k) :
        (realSecondHook (k := k)).obj realFGrade) : k) = 1 := by
    simpa [realSecondHook, realHookBirthUnit, SupportInterval.one] using hval
  exact one_ne_zero (hone.symm.trans hzero)

private theorem realHook_birthToG_nonzero (k : Type) [Field k] :
    structureMapLinear (realSecondHook (k := k)) birth_le_gGrade
      (realHookBirthUnit k) ≠ 0 := by
  intro hz
  have hzero := congrArg Subtype.val hz
  have hval := SupportInterval.structureMap_val
    (Hook.support realSecondBirth realSecondDeath)
    (Hook.support_ordConnected realSecondBirth realSecondDeath)
    birth_le_gGrade (realHookBirthUnit k)
  rw [if_pos gGrade_mem_hook] at hval
  have hone : ((structureMapLinear (realSecondHook (k := k))
      birth_le_gGrade (realHookBirthUnit k) :
        (realSecondHook (k := k)).obj realGGrade) : k) = 1 := by
    simpa [realSecondHook, realHookBirthUnit, SupportInterval.one] using hval
  exact one_ne_zero (hone.symm.trans hzero)

/-- The rational finite hook-Hom module has ordinary projective dimension two. -/
theorem rational_finite_hookHom_dimension :
    projectiveDimension
      ((FiniteRankProjectiveHomExact.homFunctor (k := ℚ) (S := grid.Point)).obj
        (finiteModule (k := ℚ))) = 2 :=
  finite_hookHom_projectiveDimension_eq_two (k := ℚ)

/-- The finite augmentation and both differentials are nonzero over `ℚ`. -/
theorem rational_finite_maps_nonzero :
    q0 (k := ℚ) ≠ 0 ∧ d1 (k := ℚ) ≠ 0 ∧ j (k := ℚ) ≠ 0 :=
  ⟨q0_ne_zero (k := ℚ), d1_ne_zero (k := ℚ), j_ne_zero (k := ℚ)⟩

/-- The rational real module retains the original finite-presentation
predicate in the real-coordinate category. -/
theorem rational_real_original_finitelyPresented :
    GradedFree.FinitelyPresented.{0,0,0} (R := ℚ) (P := Fin 2 → ℝ)
      (realModule (k := ℚ)) :=
  realModule_finitelyPresented (k := ℚ)

/-- The rational real witness has an actual second hook identified with
`H((1,1),(2,2))`. -/
theorem rational_real_second_hook_iso :
    Nonempty ((realMinimalResolution (k := ℚ)).termAt 2 ≅ realSecondHook (k := ℚ)) :=
  ⟨realMinimalResolution_termAt_two_iso (k := ℚ)⟩

/-- Every rational certified minimal real resolution has nonzero degree two
and vanishes strictly above it. -/
theorem rational_real_all_minimal_degrees
    (R : MinimalFiniteRankProjectiveResolution (k := ℚ)
      (M := realModule (k := ℚ))) :
    ¬ IsZero (R.termAt 2) ∧ ∀ j, 2 < j → IsZero (R.termAt j) :=
  ⟨realMinimalResolution_second_term_nonzero R,
    fun j hj => realMinimalResolution_terms_vanish_above_two R j hj⟩

/-- The canonical birth vector on the rational real hook survives along its
upper arm to `(1,2)`. -/
theorem rational_real_hook_birth_to_f_nonzero :
    structureMapLinear (realSecondHook (k := ℚ))
      (show realSecondBirth ≤ realFGrade from by
        intro i
        fin_cases i <;> norm_num [realSecondBirth, realFGrade]) ≠ 0 := by
  intro hzero
  apply realHook_birthToF_nonzero ℚ
  have hunit := congrArg (fun f => f
    (SupportInterval.one (Hook.support realSecondBirth realSecondDeath)
      (Hook.birth_mem realSecondHook_birth_lt_death))) hzero
  simpa [realHookBirthUnit] using hunit

/-- The canonical birth vector on the rational real hook survives along its
right arm to `(2,1)`. -/
theorem rational_real_hook_birth_to_g_nonzero :
    structureMapLinear (realSecondHook (k := ℚ))
      (show realSecondBirth ≤ realGGrade from by
        intro i
        fin_cases i <;> norm_num [realSecondBirth, realGGrade]) ≠ 0 := by
  intro hzero
  apply realHook_birthToG_nonzero ℚ
  have hunit := congrArg (fun f => f
    (SupportInterval.one (Hook.support realSecondBirth realSecondDeath)
      (Hook.birth_mem realSecondHook_birth_lt_death))) hzero
  simpa [realHookBirthUnit] using hunit

/-- The rational real hook's birth vector dies at its death grade `(2,2)`. -/
theorem rational_real_hook_dies_at_death :
    structureMapLinear (realSecondHook (k := ℚ))
      realSecondHook_birth_lt_death.le = 0 := by
  change structureMapLinear
    (SupportInterval.module (k := ℚ) (Hook.support realSecondBirth realSecondDeath)
      (Hook.support_ordConnected realSecondBirth realSecondDeath))
    realSecondHook_birth_lt_death.le = 0
  apply SupportInterval.structureMap_eq_zero_of_not_mem
  rintro ⟨_, hq⟩
  exact hq.2 le_rfl

/-- The finite hook-Hom module has ordinary projective dimension two in
characteristic two as well. -/
theorem characteristicTwo_finite_hookHom_dimension :
    projectiveDimension
      ((FiniteRankProjectiveHomExact.homFunctor (k := ZMod 2) (S := grid.Point)).obj
        (finiteModule (k := ZMod 2))) = 2 :=
  finite_hookHom_projectiveDimension_eq_two (k := ZMod 2)

/-- The finite augmentation and both differentials remain nonzero in
characteristic two. -/
theorem characteristicTwo_finite_maps_nonzero :
    q0 (k := ZMod 2) ≠ 0 ∧ d1 (k := ZMod 2) ≠ 0 ∧ j (k := ZMod 2) ≠ 0 :=
  ⟨q0_ne_zero (k := ZMod 2), d1_ne_zero (k := ZMod 2), j_ne_zero (k := ZMod 2)⟩

/-- The characteristic-two real module retains original finite presentation. -/
theorem characteristicTwo_real_original_finitelyPresented :
    GradedFree.FinitelyPresented.{0,0,0} (R := ZMod 2) (P := Fin 2 → ℝ)
      (realModule (k := ZMod 2)) :=
  realModule_finitelyPresented (k := ZMod 2)

/-- The characteristic-two real witness has the actual second hook term. -/
theorem characteristicTwo_real_second_hook_iso :
    Nonempty ((realMinimalResolution (k := ZMod 2)).termAt 2 ≅
      realSecondHook (k := ZMod 2)) :=
  ⟨realMinimalResolution_termAt_two_iso (k := ZMod 2)⟩

/-- Every characteristic-two certified minimal real resolution has nonzero
degree two and vanishes strictly above it. -/
theorem characteristicTwo_real_all_minimal_degrees
    (R : MinimalFiniteRankProjectiveResolution (k := ZMod 2)
      (M := realModule (k := ZMod 2))) :
    ¬ IsZero (R.termAt 2) ∧ ∀ j, 2 < j → IsZero (R.termAt j) :=
  ⟨realMinimalResolution_second_term_nonzero R,
    fun j hj => realMinimalResolution_terms_vanish_above_two R j hj⟩

/-- The characteristic-two real hook's birth survives along its upper arm to `(1,2)`. -/
theorem characteristicTwo_real_hook_birth_to_f_nonzero :
    structureMapLinear (realSecondHook (k := ZMod 2))
      (show realSecondBirth ≤ realFGrade from by
        intro i
        fin_cases i <;> norm_num [realSecondBirth, realFGrade]) ≠ 0 := by
  intro hzero
  apply realHook_birthToF_nonzero (ZMod 2)
  have hunit := congrArg (fun f => f
    (SupportInterval.one (Hook.support realSecondBirth realSecondDeath)
      (Hook.birth_mem realSecondHook_birth_lt_death))) hzero
  simpa [realHookBirthUnit] using hunit

/-- The characteristic-two real hook's birth survives along the right arm. -/
theorem characteristicTwo_real_hook_birth_to_g_nonzero :
    structureMapLinear (realSecondHook (k := ZMod 2))
      (show realSecondBirth ≤ realGGrade from by
        intro i
        fin_cases i <;> norm_num [realSecondBirth, realGGrade]) ≠ 0 := by
  intro hzero
  apply realHook_birthToG_nonzero (ZMod 2)
  have hunit := congrArg (fun f => f
    (SupportInterval.one (Hook.support realSecondBirth realSecondDeath)
      (Hook.birth_mem realSecondHook_birth_lt_death))) hzero
  simpa [realHookBirthUnit] using hunit

/-- The characteristic-two real hook's birth dies at its death grade. -/
theorem characteristicTwo_real_hook_dies_at_death :
    structureMapLinear (realSecondHook (k := ZMod 2))
      realSecondHook_birth_lt_death.le = 0 := by
  change structureMapLinear
    (SupportInterval.module (k := ZMod 2) (Hook.support realSecondBirth realSecondDeath)
      (Hook.support_ordConnected realSecondBirth realSecondDeath))
    realSecondHook_birth_lt_death.le = 0
  apply SupportInterval.structureMap_eq_zero_of_not_mem
  rintro ⟨_, hq⟩
  exact hq.2 le_rfl

end TDA.Persistence.RankResolutionDegreeTwo.Examples
