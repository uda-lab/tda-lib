import TDA.Sheaf.BandBaseChange
import TDA.Sheaf.BandStalksExamples

/-!
# Base change on band fibres and pasting: fixtures

These fixtures consume `TDA.Sheaf.BaseChangePasting` and `TDA.Sheaf.BandBaseChange` over `ℚ`,
with Mathlib's standard derived category `HasDerivedCategory.standard` installed as a local
instance in this file only. `kpt` is the sheaf on the point with value `ℚ` and `kD` the constant
sheaf on the band `D 1` (`TDA.Sheaf.BandStalksExamples`).

* `H0StalkIso`: the canonical stalk formula `stalkFormula ℚ 1 0` at `kD`, read in `H⁰`, gives
  `H⁰((ptAt 0)⁻¹ R(q 1)_* kD) ≅ kpt` without any choice; `nonempty_H0_stalk_kD_of_stalkFormula`
  re-derives `nonempty_H0_stalk_kD` from it and `not_isZero_H0_stalk_kD_of_stalkFormula` the
  nonvanishing.
* `inclSquare`, `fibreSquare`, `pastedSquare`: the square `incl ≫ q 2 = q 1 ≫ 𝟙` of the band
  inclusion `D 1 ⟶ D 2`, the fibre square of `q 1` at `0`, and the composite square
  `(fibreEmb 1 0 ≫ incl) ≫ q 2 = toPt _ ≫ ptAt 0 ≫ 𝟙`; `baseChange_pastedSquare_app` is the
  pasting formula for them.
-/

noncomputable section

open CategoryTheory Limits TDA.Sheaf TDA.Sheaf.BandConvolution

namespace TDA.Sheaf.BandBaseChangeExamples

open TDA.Sheaf.IntervalCohomologyExamples (kpt)
open TDA.Sheaf.BandStalksExamples (kD not_isZero_kpt)

attribute [local instance] HasDerivedCategory.standard

/-- **The canonical stalk formula on a constant sheaf.** `H⁰` of the stalk at `0` of
`R(q 1)_* kD` is `kpt`, through `stalkFormula ℚ 1 0`, the derived unit of `[-1, 1] ⟶ pt` and the
`H⁰` of a sheaf in degree `0`. -/
def H0StalkIso :
    (DerivedCategory.Plus.homologyFunctor _ 0).obj
        ((pullbackPlus ℚ (ptAt 0)).obj ((pushforwardPlus ℚ (q 1)).obj kD)) ≅ kpt :=
  have := isIso_derivedUnit_toPt_Icc (k := ℚ) (u := (0 : ℝ) - 1) (v := 0 + 1) (by norm_num) kpt
  (DerivedCategory.Plus.homologyFunctor _ 0).mapIso ((stalkFormula ℚ 1 0).app kD) ≪≫
    (DerivedCategory.Plus.homologyFunctor _ 0).mapIso
      ((pushforwardPlus ℚ (toPt (TopCat.of (Set.Icc ((0 : ℝ) - 1) (0 + 1))))).mapIso
        ((pullbackPlusCompIso ℚ (fibreEmb 1 0) (toPt (D 1))).app _)) ≪≫
    (DerivedCategory.Plus.homologyFunctor _ 0).mapIso
      (asIso ((derivedUnit ℚ (toPt (TopCat.of (Set.Icc ((0 : ℝ) - 1) (0 + 1))))).app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj kpt))).symm ≪≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app kpt

/-- `nonempty_H0_stalk_kD`, witnessed by the canonical `H0StalkIso`. -/
theorem nonempty_H0_stalk_kD_of_stalkFormula :
    Nonempty ((DerivedCategory.Plus.homologyFunctor _ 0).obj
        ((pullbackPlus ℚ (ptAt 0)).obj ((pushforwardPlus ℚ (q 1)).obj kD)) ≅ kpt) :=
  ⟨H0StalkIso⟩

/-- `H⁰` of the stalk at `0` of `R(q 1)_* kD` is nonzero, through `H0StalkIso`. -/
theorem not_isZero_H0_stalk_kD_of_stalkFormula :
    ¬ IsZero ((DerivedCategory.Plus.homologyFunctor _ 0).obj
      ((pullbackPlus ℚ (ptAt 0)).obj ((pushforwardPlus ℚ (q 1)).obj kD))) :=
  fun h => not_isZero_kpt (h.of_iso H0StalkIso.symm)

/-- The square of the band inclusion: `incl ≫ q 2 = q 1 ≫ 𝟙 ℝ`. -/
theorem inclSquare : incl (show (1 : ℝ) ≤ 2 by norm_num) ≫ q 2 = q 1 ≫ 𝟙 realLine := by
  rw [incl_q, Category.comp_id]

/-- The fibre square of `q 1` at `0`. -/
theorem fibreSquare : fibreEmb 1 0 ≫ q 1 = toPt _ ≫ ptAt 0 := fibreEmb_comp_q 1 0

/-- The composite of the fibre square and the inclusion square. -/
theorem pastedSquare :
    (fibreEmb 1 0 ≫ incl (show (1 : ℝ) ≤ 2 by norm_num)) ≫ q 2 =
      toPt _ ≫ ptAt 0 ≫ 𝟙 realLine := by
  rw [Category.assoc, inclSquare, ← Category.assoc, fibreSquare, Category.assoc]

/-- **Pasting on band squares.** The base change of the composite square is `(ptAt 0)⁻¹` of the
base change of the inclusion square, followed by the base change of the fibre square, conjugated
by `pullbackPlusCompIso`. -/
theorem baseChange_pastedSquare_app (M : DerivedCategory.Plus ((D 2).Sheaf (ModuleCat.{0} ℚ))) :
    (baseChange ℚ pastedSquare).app M =
      (pullbackPlusCompIso ℚ (ptAt 0) (𝟙 realLine)).inv.app ((pushforwardPlus ℚ (q 2)).obj M) ≫
        (pullbackPlus ℚ (ptAt 0)).map ((baseChange ℚ inclSquare).app M) ≫
        (baseChange ℚ fibreSquare).app
          ((pullbackPlus ℚ (incl (show (1 : ℝ) ≤ 2 by norm_num))).obj M) ≫
        (pushforwardPlus ℚ (toPt _)).map
          ((pullbackPlusCompIso ℚ (fibreEmb 1 0) (incl (show (1 : ℝ) ≤ 2 by norm_num))).hom.app
            M) :=
  baseChange_comp_app ℚ inclSquare fibreSquare pastedSquare M

/-- The base change of the fibre square is invertible, at every object. -/
theorem isIso_baseChange_fibreSquare_app
    (M : DerivedCategory.Plus ((D 1).Sheaf (ModuleCat.{0} ℚ))) :
    IsIso ((baseChange ℚ fibreSquare).app M) :=
  inferInstance

end TDA.Sheaf.BandBaseChangeExamples
