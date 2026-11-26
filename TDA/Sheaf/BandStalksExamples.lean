import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import TDA.Sheaf.BandStalks
import TDA.Sheaf.IntervalCohomologyExamples

/-!
# Acyclic classes and stalks of band projections: fixtures

These fixtures consume `TDA.Sheaf.IntervalAcyclic` and `TDA.Sheaf.BandStalks` over `ℚ`, with
Mathlib's standard derived category `HasDerivedCategory.standard` installed as a local instance in
this file only. `kpt` is the sheaf on the point with value `ℚ` and `I01 = [0, 1]`, both from
`TDA.Sheaf.IntervalCohomologyExamples`.

* The constant sheaf `constSh ℚ I01 kpt` placed in degree `0` is a complex of germ-surjective
  sheaves (`germSurjective_constPlus`), so the acyclic class of germ-surjective sheaves gives that
  its global sections compute `RΓ([0, 1]; -)` (`isIso_unit_constPlus`).
* On the band `D 1` of positive width, the constant sheaf `kD = (toPt (D 1))⁻¹ kpt` in `D⁺` has, by
  the stalk formula, `H⁰` of its stalk at `0` of `R(q 1)_* kD` equal to `H⁰([-1, 1]; constSh kpt)`,
  which is `kpt` (`H0_stalk_kD`); in particular it is nonzero (`not_isZero_H0_stalk_kD`). Its `H²`
  vanishes (`isZero_H2_stalk_constSh`).
-/

noncomputable section

open CategoryTheory Limits TopologicalSpace TDA.Sheaf TDA.Sheaf.BandConvolution

namespace TDA.Sheaf.BandStalksExamples

open TDA.Sheaf.IntervalCohomologyExamples (kpt I01)

attribute [local instance] HasDerivedCategory.standard Classical.propDecidable

/-- The constant sheaf `constSh ℚ I01 kpt` on `[0, 1]` placed in degree `0`. -/
abbrev constPlus : CochainComplex.Plus (I01.Sheaf (ModuleCat.{0} ℚ)) :=
  singlePlus 0 (constSh ℚ I01 kpt)

/-- Every term of `constPlus` is germ-surjective. -/
theorem germSurjective_constPlus (n : ℤ) : GermSurjective ℚ (constPlus.obj.X n) := by
  by_cases hn : n = 0
  · subst hn
    exact germSurjective_of_epi ℚ (HomologicalComplex.singleObjXSelf _ 0 _).inv
      (germSurjective_constSh _ kpt)
  · exact (acyclicClass_germSurjective_Icc (k := ℚ) 0 1).zero _
      (HomologicalComplex.isZero_single_obj_X _ _ _ _ hn)

/-- Global sections of `constPlus` compute `RΓ([0, 1]; constSh kpt)`: the comparison
`Γ([0, 1]; constPlus) ⟶ RΓ([0, 1]; constPlus)` is an isomorphism (acyclic class of
germ-surjective sheaves). -/
theorem isIso_unit_constPlus :
    IsIso ((TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) (toPt I01)).rightDerivedFunctorPlusUnit.app
      constPlus) :=
  isIso_rightDerivedFunctorPlusUnit_app_toPt_Icc_of_germSurjective constPlus
    germSurjective_constPlus

/-- The constant sheaf on the band `D 1` with value `kpt`, in `D⁺`. -/
abbrev kD : DerivedCategory.Plus ((D 1).Sheaf (ModuleCat.{0} ℚ)) :=
  (pullbackPlus ℚ (toPt (D 1))).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj kpt)

/-- **The stalk formula on a constant sheaf.** `H⁰` of the stalk at `0` of `R(q 1)_* kD` is
`H⁰([-1, 1]; constSh kpt) ≅ kpt`. -/
theorem nonempty_H0_stalk_kD :
    Nonempty ((DerivedCategory.Plus.homologyFunctor _ 0).obj
        ((pullbackPlus ℚ (ptAt 0)).obj ((pushforwardPlus ℚ (q 1)).obj kD)) ≅ kpt) :=
  have := isIso_derivedUnit_toPt_Icc (k := ℚ) (u := (0 : ℝ) - 1) (v := 0 + 1) (by norm_num) kpt
  ⟨(nonempty_stalkFormula_homology ℚ 1 0 kD 0).some ≪≫
    (DerivedCategory.Plus.homologyFunctor _ 0).mapIso
      ((pushforwardPlus ℚ (toPt (TopCat.of (Set.Icc ((0 : ℝ) - 1) (0 + 1))))).mapIso
        ((pullbackPlusCompIso ℚ (fibreEmb 1 0) (toPt (D 1))).app _)) ≪≫
    (DerivedCategory.Plus.homologyFunctor _ 0).mapIso
      (asIso ((derivedUnit ℚ (toPt (TopCat.of (Set.Icc ((0 : ℝ) - 1) (0 + 1))))).app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj kpt))).symm ≪≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app kpt⟩

/-- The sheaf `kpt` on the point is nonzero: its stalk is `ℚ`. -/
theorem not_isZero_kpt : ¬ IsZero kpt := by
  intro h
  have hs := Functor.map_isZero
    (TopCat.Sheaf.forget (ModuleCat.{0} ℚ) pt ⋙ TopCat.Presheaf.stalkFunctor _ (PUnit.unit : pt)) h
  have hq := ModuleCat.subsingleton_of_isZero (hs.of_iso
    (skyscraperPresheafStalkOfSpecializes (X := pt) (y := PUnit.unit) PUnit.unit
      (ModuleCat.of ℚ ℚ) specializes_rfl).symm)
  exact one_ne_zero (hq.elim (1 : ℚ) 0)

/-- `H⁰` of the stalk at `0` of `R(q 1)_* kD` is nonzero. -/
theorem not_isZero_H0_stalk_kD :
    ¬ IsZero ((DerivedCategory.Plus.homologyFunctor _ 0).obj
      ((pullbackPlus ℚ (ptAt 0)).obj ((pushforwardPlus ℚ (q 1)).obj kD))) :=
  fun h => not_isZero_kpt (h.of_iso nonempty_H0_stalk_kD.some.symm)

/-- `H²` of the stalk at `0` of `R(q 1)_*` of the constant sheaf vanishes. -/
theorem isZero_H2_stalk_constSh :
    IsZero ((DerivedCategory.Plus.homologyFunctor _ 2).obj
      ((pullbackPlus ℚ (ptAt 0)).obj ((pushforwardPlus ℚ (q 1)).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj (constSh ℚ (D 1) kpt))))) :=
  isZero_H_stalk_pushforwardPlus_q ℚ 1 0 _ le_rfl

end TDA.Sheaf.BandStalksExamples
