import TDA.Persistence.HookInfinityProjective

set_option autoImplicit false

namespace TDA.Persistence.HookInfinityProjectiveExamples

open CategoryTheory

structure Grade where
  level : ℕ
  tag : Bool
  deriving DecidableEq

instance gradePreorder : Preorder Grade := Preorder.lift Grade.level

def birthGrade : Grade := ⟨1, false⟩

def equivalentGrade : Grade := ⟨1, true⟩

def laterGrade : Grade := ⟨2, true⟩

def beforeGrade : Grade := ⟨0, false⟩

theorem preorder_not_antisymmetric :
    birthGrade ≤ equivalentGrade ∧ equivalentGrade ≤ birthGrade ∧ birthGrade ≠ equivalentGrade := by
  decide

abbrev source : PModule ℤ Grade := (Functor.const Grade).obj (ModuleCat.of ℤ ℤ)

abbrev target : PModule ℤ Grade := (Functor.const Grade).obj (ModuleCat.of ℤ (ZMod 2))

def quotient : source ⟶ target where
  app _ := ModuleCat.ofHom (Int.castAddHom (ZMod 2)).toIntLinearMap
  naturality _ := by simp

private instance quotient_epi : Epi quotient := by
  apply (NatTrans.epi_iff_epi_app _).mpr
  intro p
  apply (ModuleCat.epi_iff_surjective _).mpr
  change Function.Surjective ((↑) : ℤ → ZMod 2)
  exact ZMod.intCast_surjective

noncomputable def unitMap : HookInfinity.module (R := ℤ) birthGrade ⟶ target :=
  HookInfinity.fromBirth birthGrade target (1 : ZMod 2)

private theorem unit_at_birth :
    unitMap.app birthGrade (HookInfinity.birth (R := ℤ) birthGrade) = (1 : ZMod 2) :=
  HookInfinity.fromBirth_birth _ _ _

theorem unit_transport :
    unitMap.app laterGrade
      (structureMapLinear (HookInfinity.module (R := ℤ) birthGrade)
        (show birthGrade ≤ laterGrade by decide)
        (HookInfinity.birth (R := ℤ) birthGrade)) = (1 : ZMod 2) := by
  have hn := NatTrans.naturality_apply unitMap
    (homOfLE (show birthGrade ≤ laterGrade by decide))
    (HookInfinity.birth (R := ℤ) birthGrade)
  change unitMap.app laterGrade
      (structureMapLinear (HookInfinity.module (R := ℤ) birthGrade)
        (show birthGrade ≤ laterGrade by decide)
        (HookInfinity.birth (R := ℤ) birthGrade)) =
      unitMap.app birthGrade (HookInfinity.birth (R := ℤ) birthGrade) at hn
  exact hn.trans unit_at_birth

theorem unit_nonzero : unitMap ≠ 0 := by
  intro h
  have he := unit_at_birth
  rw [h] at he
  change (0 : ZMod 2) = 1 at he
  exact zero_ne_one he

/-- The integer quotient lifts a unit-born map nontrivially at birth and after transport. -/
theorem integer_quotient_lift :
    ∃ β : HookInfinity.module (R := ℤ) birthGrade ⟶ source,
      β ≫ quotient = unitMap ∧
      β.app birthGrade (HookInfinity.birth (R := ℤ) birthGrade) ≠ 0 ∧
      β.app laterGrade
        (structureMapLinear (HookInfinity.module (R := ℤ) birthGrade)
          (show birthGrade ≤ laterGrade by decide)
          (HookInfinity.birth (R := ℤ) birthGrade)) ≠ 0 := by
  obtain ⟨β, hβ⟩ := Projective.factors unitMap quotient
  refine ⟨β, hβ, ?_, ?_⟩
  · intro hz
    have he := congrArg
      (fun α => α.app birthGrade (HookInfinity.birth (R := ℤ) birthGrade)) hβ
    change quotient.app birthGrade
      (β.app birthGrade (HookInfinity.birth (R := ℤ) birthGrade)) = _ at he
    rw [hz] at he
    have : (0 : ZMod 2) = 1 := he.trans unit_at_birth
    exact zero_ne_one this
  · intro hz
    have he := congrArg (fun α => α.app laterGrade
      (structureMapLinear (HookInfinity.module (R := ℤ) birthGrade)
        (show birthGrade ≤ laterGrade by decide)
        (HookInfinity.birth (R := ℤ) birthGrade))) hβ
    change quotient.app laterGrade (β.app laterGrade
      (structureMapLinear (HookInfinity.module (R := ℤ) birthGrade)
        (show birthGrade ≤ laterGrade by decide)
        (HookInfinity.birth (R := ℤ) birthGrade))) = _ at he
    rw [hz] at he
    have : (0 : ZMod 2) = 1 := he.trans unit_transport
    exact zero_ne_one this

theorem quotient_noninjective : ¬ Function.Injective (quotient.app birthGrade) := by
  intro h
  have hz : quotient.app birthGrade (2 : ℤ) = quotient.app birthGrade 0 := by
    change (2 : ZMod 2) = 0
    decide
  have : (2 : ℤ) = 0 := h hz
  norm_num at this

theorem outside_support_zero
    (x : (HookInfinity.module (R := ℤ) birthGrade).obj beforeGrade) : x = 0 :=
  HookInfinity.fiber_eq_zero_of_not_le (by decide) x

end TDA.Persistence.HookInfinityProjectiveExamples
