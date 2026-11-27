import TDA.Sheaf.BandCompositionUnit
import TDA.Sheaf.BandCompositionExamples

/-!
# Unit laws of the composition isomorphism of the band functors: fixtures

These fixtures consume `TDA.Sheaf.BandCompositionUnit` over `ℚ`, with Mathlib's standard derived
category `HasDerivedCategory.standard` installed as a local instance in this file only. `constOn X`
is the constant sheaf with value `kpt` on `X` (`TDA.Sheaf.IntervalFibrationExamples`). Each fixture
is the general theorem at the stated radii.

* **Unit laws at radius `1`.** `TCompOfEq_zero_left_one` and `TCompOfEq_zero_right_one`; `H⁰` of
  every stalk of the sources `T_1 (T_0 (constOn ℝ))` and `T_0 (T_1 (constOn ℝ))` is nonzero
  (`not_isZero_H0_stalk_TT_zero_one`, `not_isZero_H0_stalk_TT_one_zero`).
* **Augmentation law at `(1, 1)` on the constant sheaf** (`hcomp_aug_TComp_constOn`); the source
  `T_1 (T_1 (constOn ℝ))` has nonzero `H⁰` stalks
  (`TDA.Sheaf.BandCompositionLawsExamples.not_isZero_H0_stalk_TT_one_one`).
* **Bounded derived category.** The left unit law at `b = 1` on `Dᵇ`
  (`compIsoB_TCompOfEq_zero_left_one`).
-/

noncomputable section

open CategoryTheory Limits TopologicalSpace TDA.Sheaf TDA.Sheaf.BandConvolution

namespace TDA.Sheaf.BandCompositionUnitExamples

open TDA.Sheaf.IntervalFibrationExamples (constOn)
open TDA.Sheaf.BandCompositionExamples (not_isZero_H0_stalk_TT)

attribute [local instance] HasDerivedCategory.standard

/-- **The left unit law at `b = 1`** over `ℚ`. -/
theorem TCompOfEq_zero_left_one :
    (TCompOfEq ℚ le_rfl zero_le_one (zero_add (1 : ℝ))).hom =
      Functor.whiskerRight (T0Iso ℚ).hom (T ℚ 1) ≫ (Functor.leftUnitor (T ℚ 1)).hom :=
  TCompOfEq_zero_left_hom ℚ zero_le_one

/-- **The right unit law at `a = 1`** over `ℚ`. -/
theorem TCompOfEq_zero_right_one :
    (TCompOfEq ℚ zero_le_one le_rfl (add_zero (1 : ℝ))).hom =
      Functor.whiskerLeft (T ℚ 1) (T0Iso ℚ).hom ≫ (Functor.rightUnitor (T ℚ 1)).hom :=
  TCompOfEq_zero_right_hom ℚ zero_le_one

/-- The source of `TCompOfEq_zero_left_one`: `H⁰` of every stalk of `T_1 (T_0 (constOn ℝ))` is
nonzero. -/
theorem not_isZero_H0_stalk_TT_zero_one (y : realLine) :
    ¬ IsZero ((DerivedCategory.Plus.homologyFunctor _ 0).obj
      ((pullbackPlus ℚ (ptOf y)).obj ((T ℚ 0 ⋙ T ℚ 1).obj (constOn realLine)))) :=
  not_isZero_H0_stalk_TT le_rfl zero_le_one y

/-- The source of `TCompOfEq_zero_right_one`: `H⁰` of every stalk of `T_0 (T_1 (constOn ℝ))` is
nonzero. -/
theorem not_isZero_H0_stalk_TT_one_zero (y : realLine) :
    ¬ IsZero ((DerivedCategory.Plus.homologyFunctor _ 0).obj
      ((pullbackPlus ℚ (ptOf y)).obj ((T ℚ 1 ⋙ T ℚ 0).obj (constOn realLine)))) :=
  not_isZero_H0_stalk_TT zero_le_one le_rfl y

/-- **The augmentation law at `(1, 1)` on the constant sheaf.** -/
theorem hcomp_aug_TComp_constOn :
    ((aug ℚ zero_le_one ◫ aug ℚ zero_le_one) ≫ (Functor.leftUnitor (𝟭 _)).hom).app
        (constOn realLine) =
      ((TComp ℚ zero_le_one zero_le_one).hom ≫
        aug ℚ (add_nonneg zero_le_one zero_le_one)).app (constOn realLine) :=
  congr_app (hcomp_aug_TComp_hom ℚ zero_le_one zero_le_one) _

/-- **The left unit law at `b = 1` on `Dᵇ`** over `ℚ`. -/
theorem compIsoB_TCompOfEq_zero_left_one :
    (compIsoB ℚ (TCompOfEq ℚ le_rfl zero_le_one (zero_add (1 : ℝ)))).hom =
      Functor.whiskerRight (T0IsoB ℚ).hom (TB ℚ 1) ≫ (Functor.leftUnitor (TB ℚ 1)).hom :=
  compIsoB_TCompOfEq_zero_left_hom ℚ zero_le_one

end TDA.Sheaf.BandCompositionUnitExamples
