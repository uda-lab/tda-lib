import Mathlib.Algebra.Field.Rat
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Sheaves.Skyscraper
import TDA.Sheaf.FlasqueAcyclic

/-!
# Flasque acyclicity: fixtures

These fixtures consume `TDA.Sheaf.FlasqueAcyclic` over `ℚ` on the unit interval `I01 = [0, 1]`,
with Mathlib's standard derived category `HasDerivedCategory.standard` installed as a local
instance in this file only.

* `embSc` is the short exact sequence `0 ⟶ sky ⟶ I ⟶ I / sky ⟶ 0`, where `sky` is the
  skyscraper sheaf at `1/2` with value `ℚ` (flasque) and `I = Injective.under sky`
  (`embSc_shortExact`). Sections of `I` surject onto sections of the cokernel over every open
  (`surjective_cokernel_π`), the cokernel is flasque (`isFlasque_cokernel`), and the direct
  image to the point keeps the sequence short exact (`shortExact_pushforward_embSc`).
* `skyPlus` is `sky` placed in degree `0`, a one-term complex of flasque sheaves
  (`isFlasque_skyPlus`). The comparison `f_* skyPlus ⟶ Rf_* skyPlus` is an isomorphism for the
  inclusion `ι : [0, 1] ⟶ ℝ` (`isIso_unit_skyPlus_ι`) and for global sections
  (`isIso_unit_skyPlus_toPt`).
-/

noncomputable section

open CategoryTheory Limits TopologicalSpace Opposite TDA.Sheaf

namespace TDA.Sheaf.FlasqueAcyclicExamples

attribute [local instance] HasDerivedCategory.standard Classical.propDecidable

/-- The unit interval `[0, 1]` in `TopCat`. -/
abbrev I01 : TopCat.{0} := TopCat.of (Set.Icc (0 : ℝ) 1)

/-- The midpoint `1/2` of the unit interval. -/
def mid : I01 := ⟨1 / 2, by norm_num, by norm_num⟩

/-- The skyscraper sheaf at `1/2` with value `ℚ`. -/
abbrev sky : I01.Sheaf (ModuleCat.{0} ℚ) := skyscraperSheaf mid (ModuleCat.of ℚ ℚ)

/-- The skyscraper sheaf `sky` is flasque (Mathlib). -/
instance sky_isFlasque : TopCat.Sheaf.IsFlasque sky :=
  isFlasque_skyscraperSheaf_of_hasZeroObject mid _

/-- The sequence `0 ⟶ sky ⟶ I ⟶ I / sky ⟶ 0` for the injective sheaf `I = Injective.under sky`. -/
abbrev embSc : ShortComplex (I01.Sheaf (ModuleCat.{0} ℚ)) :=
  ShortComplex.mk (Injective.ι sky) (cokernel.π (Injective.ι sky)) (cokernel.condition _)

theorem embSc_shortExact : embSc.ShortExact :=
  ShortComplex.ShortExact.mk' (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _))
    inferInstance inferInstance

/-- Sections of `I` surject onto sections of `I / sky` over every open (`epi_of_shortExact`). -/
theorem surjective_cokernel_π (U : Opens I01) :
    Function.Surjective ((cokernel.π (Injective.ι sky)).hom.app (op U)) :=
  (ModuleCat.epi_iff_surjective _).1 (epi_of_shortExact embSc_shortExact U)

/-- The cokernel `I / sky` is flasque (`isFlasque_of_shortExact`). -/
theorem isFlasque_cokernel : TopCat.Sheaf.IsFlasque (cokernel (Injective.ι sky)) :=
  @isFlasque_of_shortExact ℚ _ I01 embSc embSc_shortExact _ (isFlasque_of_injective ℚ _)

/-- Global sections keep `embSc` short exact (`pushforward_shortExact_of_isFlasque`). -/
theorem shortExact_pushforward_embSc :
    (embSc.map (TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) (toPt I01))).ShortExact :=
  pushforward_shortExact_of_isFlasque (toPt I01) embSc_shortExact

/-- `sky` placed in degree `0`. -/
abbrev skyPlus : CochainComplex.Plus (I01.Sheaf (ModuleCat.{0} ℚ)) := singlePlus 0 sky

/-- Every term of `skyPlus` is flasque. -/
instance isFlasque_skyPlus (n : ℤ) : TopCat.Sheaf.IsFlasque (skyPlus.obj.X n) := by
  by_cases hn : n = 0
  · subst hn
    exact isFlasque_of_iso (HomologicalComplex.singleObjXSelf _ 0 sky).symm
  · exact isFlasque_of_isZero (HomologicalComplex.isZero_single_obj_X _ _ _ _ hn)

/-- The inclusion `[0, 1] ⟶ ℝ`. -/
def ι : I01 ⟶ TopCat.of ℝ := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

/-- `ι_* skyPlus ⟶ Rι_* skyPlus` is an isomorphism. -/
theorem isIso_unit_skyPlus_ι :
    IsIso ((TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) ι).rightDerivedFunctorPlusUnit.app
      skyPlus) :=
  isIso_rightDerivedFunctorPlusUnit_app_of_isFlasque ι skyPlus

/-- `Γ skyPlus ⟶ RΓ skyPlus` is an isomorphism. -/
theorem isIso_unit_skyPlus_toPt :
    IsIso ((TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) (toPt I01)).rightDerivedFunctorPlusUnit.app
      skyPlus) :=
  isIso_rightDerivedFunctorPlusUnit_app_toPt_of_isFlasque skyPlus

end TDA.Sheaf.FlasqueAcyclicExamples
