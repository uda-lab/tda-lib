import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Mathlib.Topology.Sheaves.Skyscraper
import TDA.Sheaf.IntervalCohomologyExamples
import TDA.Sheaf.IntervalFibre

/-!
# Fibres of a band projection: fixtures

These fixtures consume `TDA.Sheaf.IntervalFibre` over `ℚ`, with Mathlib's standard derived
category `HasDerivedCategory.standard` installed as a local instance in this file only. `kpt` is
the sheaf on the point with value `ℚ` from `TDA.Sheaf.IntervalCohomologyExamples`.

* The fibre of `q 1` over `0` is the positive-length interval `[-1, 1]`: `fibreHomeo` sends the
  point `half = (1/2, 0)` to `1/2` (`fibreHomeo_half`). The derived unit of the constant sheaf
  `constSh kpt` on it is an isomorphism (`isIso_derivedUnit_kpt_fibre`), so
  `H⁰((q 1)⁻¹ {0}; constSh kpt) ≅ kpt` (`H0_constSh_kpt_fibre`).
* The fibre of `q 0` over `y` is the point `[y, y]`; the derived unit of `constSh kpt` on it is
  an isomorphism (`isIso_derivedUnit_kpt_fibre_zero`). On the singleton interval `[2, 2]` the
  derived unit of `toPt` is an isomorphism at every object (`isIso_derivedUnit_Icc_two`).
* For the skyscraper `skyHalf` at `half` on `(q 1)⁻¹ {0}`, `H²` vanishes (`isZero_H2_skyHalf`),
  and `H¹` is transported to `[-1, 1]` (`H1_skyHalf_iso`).
* For `a < 0` the fibre is empty (`isEmpty_fibre_neg`).
-/

noncomputable section

open CategoryTheory Limits TopologicalSpace TDA.Sheaf TDA.Sheaf.BandConvolution

namespace TDA.Sheaf.IntervalFibreExamples

open TDA.Sheaf.IntervalCohomologyExamples (kpt)

attribute [local instance] HasDerivedCategory.standard Classical.propDecidable

/-- The point `(1/2, 0)` of the fibre of `q 1` over `0`. -/
def half : fibre 1 0 :=
  ⟨⟨(1 / 2, 0), by change dist (1 / 2 : ℝ) 0 ≤ 1; rw [Real.dist_eq]; norm_num⟩, rfl⟩

/-- `fibreHomeo 1 0` sends `(1/2, 0)` to `1/2 ∈ [-1, 1]`. -/
theorem fibreHomeo_half : (fibreHomeo 1 0 half : ℝ) = 1 / 2 := rfl

/-- The fibres of `q a` are empty for `a < 0`. -/
theorem isEmpty_fibre_neg : IsEmpty (fibre (-1) 0) :=
  ⟨fun z => by
    obtain ⟨h₁, h₂⟩ := (fibreHomeo (-1) 0 z).2
    linarith⟩

/-- On the fibre `(q 1)⁻¹ {0} ≅ [-1, 1]`, the derived unit at `kpt` is an isomorphism. -/
theorem isIso_derivedUnit_kpt_fibre :
    IsIso ((derivedUnit ℚ (toPt (fibre 1 0))).app
      ((DerivedCategory.Plus.singleFunctor _ 0).obj kpt)) :=
  isIso_derivedUnit_toPt_fibre zero_le_one 0 kpt

/-- `H⁰((q 1)⁻¹ {0}; constSh kpt) ≅ kpt`. -/
def H0_constSh_kpt_fibre :
    (DerivedCategory.Plus.homologyFunctor _ 0).obj
        ((pushforwardPlus ℚ (toPt (fibre 1 0))).obj
          ((pullbackPlus ℚ (toPt (fibre 1 0))).obj
            ((DerivedCategory.Plus.singleFunctor _ 0).obj kpt))) ≅
      kpt :=
  have := isIso_derivedUnit_kpt_fibre
  (DerivedCategory.Plus.homologyFunctor _ 0).mapIso
      (asIso ((derivedUnit ℚ (toPt (fibre 1 0))).app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj kpt))).symm ≪≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app kpt

/-- On the one-point fibre `(q 0)⁻¹ {y}`, the derived unit at `kpt` is an isomorphism. -/
theorem isIso_derivedUnit_kpt_fibre_zero (y : ℝ) :
    IsIso ((derivedUnit ℚ (toPt (fibre 0 y))).app
      ((DerivedCategory.Plus.singleFunctor _ 0).obj kpt)) :=
  isIso_derivedUnit_toPt_fibre le_rfl y kpt

/-- On the singleton interval `[2, 2]` the derived unit of `toPt` is invertible. -/
theorem isIso_derivedUnit_Icc_two :
    IsIso (derivedUnit ℚ (toPt (TopCat.of (Set.Icc (2 : ℝ) 2)))) :=
  isIso_derivedUnit_toPt_Icc_self 2

/-- The skyscraper sheaf at `half` on `(q 1)⁻¹ {0}` with value `ℚ`. -/
abbrev skyHalf : (fibre 1 0).Sheaf (ModuleCat.{0} ℚ) := skyscraperSheaf half (ModuleCat.of ℚ ℚ)

/-- `H²((q 1)⁻¹ {0}; skyHalf) = 0`. -/
theorem isZero_H2_skyHalf :
    IsZero ((DerivedCategory.Plus.homologyFunctor _ 2).obj
      ((pushforwardPlus ℚ (toPt (fibre 1 0))).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj skyHalf))) :=
  isZero_H_fibre skyHalf le_rfl

/-- A pure transport example: `H¹((q 1)⁻¹ {0}; skyHalf)` is `H¹` on `[-1, 1]` of the transported
skyscraper, by `H_iso_of_homeo`. Both sides vanish (skyscrapers are flasque); the substantive
fibre fixture is `H0_constSh_kpt_fibre`. -/
def H1_skyHalf_iso :
    (DerivedCategory.Plus.homologyFunctor _ 1).obj
        ((pushforwardPlus ℚ (toPt (fibre 1 0))).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj skyHalf)) ≅
      (DerivedCategory.Plus.homologyFunctor _ 1).obj
        ((pushforwardPlus ℚ (toPt (TopCat.of (Set.Icc ((0 : ℝ) - 1) (0 + 1))))).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj
            ((TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) (fibreIso 1 0).hom).obj skyHalf))) :=
  H_iso_of_homeo (fibreIso 1 0).hom skyHalf 1

end TDA.Sheaf.IntervalFibreExamples
