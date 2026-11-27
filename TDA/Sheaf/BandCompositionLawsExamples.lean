import TDA.Sheaf.BandCompositionLaws
import TDA.Sheaf.BandCompositionExamples

/-!
# Laws of the composition isomorphism of the band functors: fixtures

These fixtures consume `TDA.Sheaf.BandCompositionLaws` over `ℚ`, with Mathlib's standard derived
category `HasDerivedCategory.standard` installed as a local instance in this file only. `constOn X`
is the constant sheaf with value `kpt` on `X` (`TDA.Sheaf.IntervalFibrationExamples`).

* **Radius maps on the constant sheaf.** For `(1, 1) ≤ (2, 1)`, the radius map `T_2 ⟶ T_1`
  whiskered by `T_1`, followed by `TComp` at `(1, 1)`, agrees at `constOn ℝ` with `TComp` at
  `(2, 1)` followed by the radius map `T_{2+1} ⟶ T_{1+1}` (`whiskerRight_restr_TComp_constOn`);
  `H⁰` of every stalk of the source `T_1 (T_2 (constOn ℝ))` and of the target
  `T_1 (T_1 (constOn ℝ))` is nonzero (`not_isZero_H0_stalk_TT_two_one`,
  `not_isZero_H0_stalk_TT_one_one`). The second radius `(1, 1) ≤ (1, 2)` and both radii
  `(1, 1) ≤ (2, 2)` (`whiskerLeft_restr_TComp_constOn`, `hcomp_restr_TComp_constOn`).
* **Bounded derived category.** `TCompB` at `(1, 1)` (`TCompB_one_one`) and the radius law for
  `(1, 1) ≤ (2, 1)` on `Dᵇ` (`whiskerRight_restrB_TCompB_one`).
-/

noncomputable section

open CategoryTheory Limits TopologicalSpace TDA.Sheaf TDA.Sheaf.BandConvolution

namespace TDA.Sheaf.BandCompositionLawsExamples

open TDA.Sheaf.IntervalFibrationExamples (constOn)
open TDA.Sheaf.BandCompositionExamples (not_isZero_H0_stalk_TT)

attribute [local instance] HasDerivedCategory.standard

/-- `1 ≤ 2` in `ℝ`. -/
theorem one_le_two_real : (1 : ℝ) ≤ 2 := one_le_two

/-- **The first-radius law on the constant sheaf** for `(1, 1) ≤ (2, 1)`. -/
theorem whiskerRight_restr_TComp_constOn :
    (Functor.whiskerRight (restr ℚ one_le_two_real) (T ℚ 1) ≫
        (TComp ℚ zero_le_one zero_le_one).hom).app (constOn realLine) =
      ((TComp ℚ (zero_le_one.trans one_le_two_real) zero_le_one).hom ≫
        restr ℚ (add_le_add one_le_two_real (le_refl 1))).app (constOn realLine) :=
  congr_app (whiskerRight_restr_TComp_hom ℚ zero_le_one zero_le_one one_le_two_real) _

/-- The source of `whiskerRight_restr_TComp_constOn`: `H⁰` of every stalk of
`T_1 (T_2 (constOn ℝ))` is nonzero. -/
theorem not_isZero_H0_stalk_TT_two_one (y : realLine) :
    ¬ IsZero ((DerivedCategory.Plus.homologyFunctor _ 0).obj
      ((pullbackPlus ℚ (ptOf y)).obj ((T ℚ 2 ⋙ T ℚ 1).obj (constOn realLine)))) :=
  not_isZero_H0_stalk_TT zero_le_two zero_le_one y

/-- The target of `whiskerRight_restr_TComp_constOn`: `H⁰` of every stalk of
`T_1 (T_1 (constOn ℝ))` is nonzero. -/
theorem not_isZero_H0_stalk_TT_one_one (y : realLine) :
    ¬ IsZero ((DerivedCategory.Plus.homologyFunctor _ 0).obj
      ((pullbackPlus ℚ (ptOf y)).obj ((T ℚ 1 ⋙ T ℚ 1).obj (constOn realLine)))) :=
  not_isZero_H0_stalk_TT zero_le_one zero_le_one y

/-- **The second-radius law on the constant sheaf** for `(1, 1) ≤ (1, 2)`. -/
theorem whiskerLeft_restr_TComp_constOn :
    (Functor.whiskerLeft (T ℚ 1) (restr ℚ one_le_two_real) ≫
        (TComp ℚ zero_le_one zero_le_one).hom).app (constOn realLine) =
      ((TComp ℚ zero_le_one (zero_le_one.trans one_le_two_real)).hom ≫
        restr ℚ (add_le_add (le_refl 1) one_le_two_real)).app (constOn realLine) :=
  congr_app (whiskerLeft_restr_TComp_hom ℚ zero_le_one zero_le_one one_le_two_real) _

/-- **Both radii on the constant sheaf** for `(1, 1) ≤ (2, 2)`. -/
theorem hcomp_restr_TComp_constOn :
    ((restr ℚ one_le_two_real ◫ restr ℚ one_le_two_real) ≫
        (TComp ℚ zero_le_one zero_le_one).hom).app (constOn realLine) =
      ((TComp ℚ (zero_le_one.trans one_le_two_real) (zero_le_one.trans one_le_two_real)).hom ≫
        restr ℚ (add_le_add one_le_two_real one_le_two_real)).app (constOn realLine) :=
  congr_app (hcomp_restr_TComp_hom ℚ zero_le_one zero_le_one one_le_two_real one_le_two_real) _

/-- The bounded composition isomorphism `TB 1 ⋙ TB 1 ≅ TB (1 + 1)` over `ℚ`. -/
def TCompB_one_one : TB ℚ 1 ⋙ TB ℚ 1 ≅ TB ℚ (1 + 1) :=
  TCompB ℚ zero_le_one zero_le_one

/-- **The first-radius law on `Dᵇ`** for `(1, 1) ≤ (2, 1)`. -/
theorem whiskerRight_restrB_TCompB_one :
    Functor.whiskerRight (restrB ℚ one_le_two_real) (TB ℚ 1) ≫ (TCompB ℚ zero_le_one zero_le_one).hom =
      (TCompB ℚ (zero_le_one.trans one_le_two_real) zero_le_one).hom ≫
        restrB ℚ (add_le_add one_le_two_real (le_refl 1)) :=
  whiskerRight_restrB_TCompB_hom ℚ zero_le_one zero_le_one one_le_two_real

end TDA.Sheaf.BandCompositionLawsExamples
