import TDA.Sheaf.BandAmplitude
import TDA.Sheaf.BandStalksExamples

/-!
# Amplitude of the band functors and their bounded restriction: fixtures

These fixtures consume `TDA.Sheaf.BandAmplitude` over `ℚ`, with Mathlib's standard derived
category `HasDerivedCategory.standard` installed as a local instance in this file only. `kpt` is the
sheaf on the point with value `ℚ` (`TDA.Sheaf.IntervalCohomologyExamples`) and `kD` the constant
sheaf on the band `D 1` (`TDA.Sheaf.BandStalksExamples`).

* `kR` is the constant sheaf `constSh ℚ ℝ kpt` placed in degree `0`. Its inverse image along `p 1`
  is `kD` (`nonempty_pullbackPlus_p_kR_iso`), so the stalk at `0` of `H⁰(T ℚ 1 kR)` is nonzero by
  the stalk formula (`BandStalksExamples.not_isZero_H0_stalk_kD`); hence `H⁰(T ℚ 1 kR)` is nonzero
  (`not_isZero_H0_T_kR`).
* `kR` lies in degrees `[0, 0]`, and `T ℚ 1 kR` in degrees `[0, 1]` (`isGE_isLE_T_kR`).
* `kRb` is `kR` as an object of `Dᵇ`; `TB ℚ 1 kRb` lies over `T ℚ 1 kR` (`TB_kRb`) and its `H⁰` is
  nonzero (`not_isZero_H0_TB_kRb`). The bounded augmentations are compatible with the bounded
  radius maps along `0 ≤ 1 ≤ 2` (`restrB_comp_augB_kRb`).
-/

noncomputable section

open CategoryTheory Limits TDA.Sheaf TDA.Sheaf.BandConvolution

namespace TDA.Sheaf.BandAmplitudeExamples

open TDA.Sheaf.IntervalCohomologyExamples (kpt)
open TDA.Sheaf.BandStalksExamples (kD not_isZero_H0_stalk_kD)

attribute [local instance] HasDerivedCategory.standard

/-- The constant sheaf on the real line with value `kpt`, placed in degree `0`. -/
abbrev kR : DerivedCategory.Plus (realLine.Sheaf (ModuleCat.{0} ℚ)) :=
  (DerivedCategory.Plus.singleFunctor _ 0).obj (constSh ℚ realLine kpt)

/-- The inverse image of `kR` along `p 1` is the constant sheaf `kD` on the band `D 1`. -/
theorem nonempty_pullbackPlus_p_kR_iso : Nonempty ((pullbackPlus ℚ (p 1)).obj kR ≅ kD) :=
  ⟨rightDerivedFunctorPlusSingleIso (TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) (p 1)) 0
      (constSh ℚ realLine kpt) ≪≫
    (DerivedCategory.Plus.singleFunctor _ 0).mapIso
      ((pullbackCompIso ℚ (p 1) (toPt realLine)).app kpt) ≪≫
    (rightDerivedFunctorPlusSingleIso (TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) (toPt (D 1))) 0
      kpt).symm⟩

/-- **A nonzero `H⁰`.** `H⁰(T ℚ 1 kR)` is a nonzero sheaf on the real line. -/
theorem not_isZero_H0_T_kR :
    ¬ IsZero ((DerivedCategory.Plus.homologyFunctor _ 0).obj ((T ℚ 1).obj kR)) := by
  intro h
  obtain ⟨e₁⟩ := nonempty_homology_rightDerivedFunctorPlus_of_exact
    (TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) (ptAt 0)) ((T ℚ 1).obj kR) 0
  obtain ⟨e₂⟩ := nonempty_pullbackPlus_p_kR_iso
  refine not_isZero_H0_stalk_kD (IsZero.of_iso ?_
    ((DerivedCategory.Plus.homologyFunctor _ 0).mapIso
      ((pullbackPlus ℚ (ptAt 0)).mapIso ((pushforwardPlus ℚ (q 1)).mapIso e₂.symm)) ≪≫ e₁))
  exact Functor.map_isZero _ h

/-- **The bound `[0, 1]`.** `T ℚ 1 kR` lies in degrees `[0, 1]`. -/
theorem isGE_isLE_T_kR : ((T ℚ 1).obj kR).IsGE 0 ∧ ((T ℚ 1).obj kR).IsLE 1 :=
  isGE_isLE_T_obj ℚ 1 kR 0 0

/-- `kR` as an object of the bounded derived category. -/
abbrev kRb : DerivedCategory.Bounded (realLine.Sheaf (ModuleCat.{0} ℚ)) :=
  ⟨kR.obj, kR.property, 0, (DerivedCategory.Plus.isLE_ι_obj_iff kR 0).2 inferInstance⟩

/-- `TB ℚ 1 kRb` lies over `T ℚ 1 kR`. -/
theorem TB_kRb : (boundedToPlus _).obj ((TB ℚ 1).obj kRb) = (T ℚ 1).obj kR :=
  rfl

/-- **The bounded restriction on `kRb`.** `H⁰` of `TB ℚ 1 kRb` is nonzero. -/
theorem not_isZero_H0_TB_kRb :
    ¬ IsZero ((DerivedCategory.homologyFunctor _ 0).obj ((TB ℚ 1).obj kRb).obj) :=
  not_isZero_H0_T_kR

/-- The bounded radius map `TB ℚ 2 ⟶ TB ℚ 1` followed by the bounded augmentation of `TB ℚ 1` is
the bounded augmentation of `TB ℚ 2`, at `kRb`. -/
theorem restrB_comp_augB_kRb :
    (restrB ℚ (by norm_num : (1 : ℝ) ≤ 2)).app kRb ≫ (augB ℚ zero_le_one).app kRb =
      (augB ℚ (zero_le_one.trans (by norm_num : (1 : ℝ) ≤ 2))).app kRb := by
  rw [← NatTrans.comp_app, restrB_comp_augB]

end TDA.Sheaf.BandAmplitudeExamples
