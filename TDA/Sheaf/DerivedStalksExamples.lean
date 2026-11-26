import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Mathlib.Topology.Sheaves.Skyscraper
import TDA.Sheaf.DerivedPlus
import TDA.Sheaf.DerivedStalks
import TDA.Sheaf.RealLine

/-!
# Derived stalks: fixtures on the real line

These fixtures consume `TDA.Sheaf.StalkPullback` and `TDA.Sheaf.DerivedStalks` over `ℚ`, with
Mathlib's standard derived category `HasDerivedCategory.standard` installed as a local instance in
this file only.

* `shift : realLine ⟶ realLine` is the translation `x ↦ x + 1`, a homeomorphism (`isIso_shift`).
* `skyR` is the skyscraper sheaf at `1` with value `ℚ`, and `skyShift` its inverse image along
  `shift`. Its stalk at `0` is `ℚ` (`stalk_skyShift_zero`), since `shift 0 = 1`; its stalk at `5`
  vanishes (`isZero_stalk_skyShift_five`), since `shift 5 = 6`.
* The derived unit of `shift` at `skyR` in degree `0` is an isomorphism, so the stalk maps of
  its homology sheaf maps are isomorphisms (`isIso_stalk_homology_derivedUnit_shift`).
* `stalk_skyShift_naturality`: naturality of the stalk isomorphism at the endomorphism
  `2 • 𝟙 skyR`.
-/

noncomputable section

open CategoryTheory Limits TopologicalSpace TDA.Sheaf

namespace TDA.Sheaf.DerivedStalksExamples

attribute [local instance] HasDerivedCategory.standard Classical.propDecidable

/-- The translation `x ↦ x + 1` of the real line. -/
def shift : realLine ⟶ realLine := TopCat.ofHom ⟨fun x : ℝ => x + 1, by fun_prop⟩

/-- The translation is a homeomorphism. -/
instance isIso_shift : IsIso shift :=
  ⟨⟨TopCat.ofHom ⟨fun x : ℝ => x - 1, by fun_prop⟩,
    TopCat.ext fun x => show (x : ℝ) + 1 - 1 = x by ring,
    TopCat.ext fun x => show (x : ℝ) - 1 + 1 = x by ring⟩⟩

/-- The skyscraper sheaf at `1` on the real line with value `ℚ`. -/
abbrev skyR : realLine.Sheaf (ModuleCat.{0} ℚ) := skyscraperSheaf (1 : ℝ) (ModuleCat.of ℚ ℚ)

/-- The inverse image of `skyR` along the translation. -/
abbrev skyShift : realLine.Sheaf (ModuleCat.{0} ℚ) :=
  (TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) shift).obj skyR

/-- The stalk of `skyShift` at `0` is `ℚ`. -/
def stalk_skyShift_zero : skyShift.presheaf.stalk (0 : ℝ) ≅ ModuleCat.of ℚ ℚ :=
  (stalkPullbackSheafIso ℚ shift skyR (0 : ℝ)).symm ≪≫
    skyscraperPresheafStalkOfSpecializes (X := realLine) (y := shift (0 : ℝ)) (1 : ℝ)
      (ModuleCat.of ℚ ℚ) (specializes_of_eq (show (1 : ℝ) = 0 + 1 by norm_num))

/-- The stalk of `skyShift` at `5` is zero. -/
theorem isZero_stalk_skyShift_five : IsZero (skyShift.presheaf.stalk (5 : ℝ)) := by
  have h : ¬ (1 : realLine) ⤳ shift (5 : ℝ) := by
    rw [specializes_iff_eq]
    change (1 : ℝ) ≠ 5 + 1
    norm_num
  exact (isZero_zero _).of_iso ((stalkPullbackSheafIso ℚ shift skyR (5 : ℝ)).symm ≪≫
    (skyscraperPresheafStalkOfNotSpecializesIsTerminal (1 : realLine) (ModuleCat.of ℚ ℚ)
      h).uniqueUpToIso HasZeroObject.zeroIsTerminal)

/-- Naturality of the stalk isomorphism at `2 • 𝟙 skyR`. -/
theorem stalk_skyShift_naturality :
    (TopCat.Presheaf.stalkFunctor (ModuleCat.{0} ℚ) (shift (0 : ℝ))).map (2 • 𝟙 skyR).hom ≫
        (stalkPullbackSheafIso ℚ shift skyR (0 : ℝ)).hom =
      (stalkPullbackSheafIso ℚ shift skyR (0 : ℝ)).hom ≫
        (TopCat.Presheaf.stalkFunctor (ModuleCat.{0} ℚ) (0 : ℝ)).map
          ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) shift).map (2 • 𝟙 skyR)).hom :=
  stalkPullbackSheafIso_hom_naturality ℚ shift (2 • 𝟙 skyR) (0 : ℝ)

/-- The stalk maps of the homology sheaf maps of the derived unit of `shift` at `skyR` are
isomorphisms. -/
theorem isIso_stalk_homology_derivedUnit_shift (i : ℤ) (x : realLine) :
    IsIso ((TopCat.Presheaf.stalkFunctor (ModuleCat.{0} ℚ) x).map
      ((DerivedCategory.Plus.homologyFunctor _ i).map ((derivedUnit ℚ shift).app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj skyR))).hom) :=
  (isIso_iff_isIso_stalk_homology ((derivedUnit ℚ shift).app
    ((DerivedCategory.Plus.singleFunctor _ 0).obj skyR))).1 inferInstance i x

end TDA.Sheaf.DerivedStalksExamples
