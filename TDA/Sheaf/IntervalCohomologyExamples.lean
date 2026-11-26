import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Mathlib.Topology.Sheaves.Skyscraper
import TDA.Sheaf.IntervalCohomology

/-!
# Cohomology of compact intervals: fixtures

These fixtures consume `TDA.Sheaf.IntervalCohomology` over `ℚ`, with Mathlib's standard derived
category `HasDerivedCategory.standard` installed as a local instance in this file only.

* `kpt` is the sheaf on the point with value `ℚ`. On the unit interval `[0, 1]` the derived unit
  `kpt ⟶ RΓ([0, 1]; constSh kpt)` is an isomorphism (`isIso_derivedUnit_kpt`), so
  `H⁰([0, 1]; constSh kpt) ≅ kpt` (`H0_constSh_kpt`); `H¹` vanishes (`isZero_H1_constSh_kpt`).
* The same holds on the one-point interval `[1, 1]` (`isIso_derivedUnit_kpt_singleton`).
* For the skyscraper sheaf `sky` at `1/2` on `[0, 1]`, `H²` vanishes (`isZero_H2_sky`), and so
  does `H²` of any sheaf on the empty interval `[1, 0]` (`isZero_H2_empty`).
* The stalk of `constSh kpt` at `1/2` is `ℚ` (`stalk_constSh_kpt`), through
  `stalkPullbackSheafIso`.
-/

noncomputable section

open CategoryTheory Limits TopologicalSpace Opposite TDA.Sheaf

namespace TDA.Sheaf.IntervalCohomologyExamples

attribute [local instance] HasDerivedCategory.standard Classical.propDecidable

/-- The unit interval `[0, 1]` in `TopCat`. -/
abbrev I01 : TopCat.{0} := TopCat.of (Set.Icc (0 : ℝ) 1)

/-- The midpoint `1/2` of the unit interval. -/
def mid : I01 := ⟨1 / 2, by norm_num, by norm_num⟩

/-- The sheaf on the point with value `ℚ`. -/
abbrev kpt : pt.Sheaf (ModuleCat.{0} ℚ) := skyscraperSheaf PUnit.unit (ModuleCat.of ℚ ℚ)

/-- The skyscraper sheaf at `1/2` on `[0, 1]` with value `ℚ`. -/
abbrev sky : I01.Sheaf (ModuleCat.{0} ℚ) := skyscraperSheaf mid (ModuleCat.of ℚ ℚ)

/-- The derived unit `kpt ⟶ RΓ([0, 1]; constSh kpt)` is an isomorphism. -/
theorem isIso_derivedUnit_kpt :
    IsIso ((derivedUnit ℚ (toPt I01)).app ((DerivedCategory.Plus.singleFunctor _ 0).obj kpt)) :=
  isIso_derivedUnit_toPt_Icc zero_le_one kpt

/-- `H⁰([0, 1]; constSh kpt) ≅ kpt`. -/
def H0_constSh_kpt :
    (DerivedCategory.Plus.homologyFunctor _ 0).obj
        ((pushforwardPlus ℚ (toPt I01)).obj
          ((pullbackPlus ℚ (toPt I01)).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj kpt))) ≅
      kpt :=
  have := isIso_derivedUnit_kpt
  (DerivedCategory.Plus.homologyFunctor _ 0).mapIso
      (asIso ((derivedUnit ℚ (toPt I01)).app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj kpt))).symm ≪≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app kpt

/-- `H¹([0, 1]; constSh kpt) = 0`. -/
theorem isZero_H1_constSh_kpt :
    IsZero ((DerivedCategory.Plus.homologyFunctor _ 1).obj
      ((pushforwardPlus ℚ (toPt I01)).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj (constSh ℚ I01 kpt)))) :=
  isZero_H_constSh_Icc kpt le_rfl

/-- On the one-point interval `[1, 1]` the derived unit at `kpt` is an isomorphism as well. -/
theorem isIso_derivedUnit_kpt_singleton :
    IsIso ((derivedUnit ℚ (toPt (TopCat.of (Set.Icc (1 : ℝ) 1)))).app
      ((DerivedCategory.Plus.singleFunctor _ 0).obj kpt)) :=
  isIso_derivedUnit_toPt_Icc le_rfl kpt

/-- `H²([0, 1]; sky) = 0`. -/
theorem isZero_H2_sky :
    IsZero ((DerivedCategory.Plus.homologyFunctor _ 2).obj
      ((pushforwardPlus ℚ (toPt I01)).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj sky))) :=
  isZero_H_Icc sky le_rfl

/-- `H²` of any sheaf on the empty interval `[1, 0]` vanishes. -/
theorem isZero_H2_empty (G : (TopCat.of (Set.Icc (1 : ℝ) 0)).Sheaf (ModuleCat.{0} ℚ)) :
    IsZero ((DerivedCategory.Plus.homologyFunctor _ 2).obj
      ((pushforwardPlus ℚ (toPt (TopCat.of (Set.Icc (1 : ℝ) 0)))).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj G))) :=
  isZero_H_Icc G le_rfl

/-- The stalk of the constant sheaf `constSh kpt` at `1/2` is `ℚ`. -/
def stalk_constSh_kpt : (constSh ℚ I01 kpt).presheaf.stalk mid ≅ ModuleCat.of ℚ ℚ :=
  (stalkPullbackSheafIso ℚ (toPt I01) kpt mid).symm ≪≫
    skyscraperPresheafStalkOfSpecializes (X := pt) (y := toPt I01 mid) PUnit.unit
      (ModuleCat.of ℚ ℚ) specializes_rfl

end TDA.Sheaf.IntervalCohomologyExamples
