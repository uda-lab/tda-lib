import Mathlib.Algebra.Field.Rat
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Topology.Sheaves.Skyscraper
import TDA.Sheaf.DerivedPlus
import TDA.Sheaf.IntervalSections

/-!
# Flasque sheaves and section lifting on `[0, 1]`: fixtures

These fixtures consume `TDA.Sheaf.SheafFlasque` and `TDA.Sheaf.IntervalSections` over `ℚ` on
the unit interval `I01 = [0, 1]`.

* The skyscraper sheaf `sky` at `1/2` with value `ℚ` is flasque (`sky_isFlasque`, from Mathlib)
  and germ-surjective (`germSurjective_sky`).
* An injective sheaf containing any given sheaf is flasque and germ-surjective, and so is the
  cokernel of the embedding (`germSurjective_cokernel_ι`, through `germSurjective_of_epi`).
* With constant coefficients `K`, the constant sheaf with value `ℚ`: for the complex
  `sky ⟶ sky ⊞ K ⟶ K ⟶ K` (inclusion, projection, zero), exact at `sky ⊞ K` and `K`,
  `sections_exact_Icc` lifts every global section of `K` to `sky ⊞ K`
  (`constant_section_lift`); `exists_section_lift_Icc` does the same from the local lifts
  (`constant_section_lift_of_local`).
* On the empty interval `[1, 0]` the lifting statement holds as well (`empty_section_lift`).
-/

noncomputable section

open CategoryTheory Limits TopologicalSpace Opposite TDA.Sheaf

namespace TDA.Sheaf.IntervalSectionsExamples

attribute [local instance] Classical.propDecidable

/-- The unit interval `[0, 1]` in `TopCat`. -/
abbrev I01 : TopCat.{0} := TopCat.of (Set.Icc (0 : ℝ) 1)

/-- The midpoint `1/2` of the unit interval. -/
def mid : I01 := ⟨1 / 2, by norm_num, by norm_num⟩

/-- The skyscraper sheaf at `1/2` with value `ℚ`. -/
abbrev sky : I01.Sheaf (ModuleCat.{0} ℚ) := skyscraperSheaf mid (ModuleCat.of ℚ ℚ)

/-- The constant sheaf on `[0, 1]` with value `ℚ`. -/
abbrev K : I01.Sheaf (ModuleCat.{0} ℚ) :=
  (constantSheaf (Opens.grothendieckTopology I01) (ModuleCat.{0} ℚ)).obj (ModuleCat.of ℚ ℚ)

theorem sky_isFlasque : TopCat.Sheaf.IsFlasque sky :=
  isFlasque_skyscraperSheaf_of_hasZeroObject mid _

theorem germSurjective_sky : GermSurjective ℚ sky :=
  @germSurjective_of_isFlasque ℚ _ I01 sky sky_isFlasque

/-- An injective sheaf containing `F` is flasque. -/
theorem isFlasque_under (F : I01.Sheaf (ModuleCat.{0} ℚ)) :
    TopCat.Sheaf.IsFlasque (Injective.under F) :=
  isFlasque_of_injective ℚ _

/-- The cokernel of an embedding of `F` into an injective sheaf is germ-surjective. -/
theorem germSurjective_cokernel_ι (F : I01.Sheaf (ModuleCat.{0} ℚ)) :
    GermSurjective ℚ (cokernel (Injective.ι F)) :=
  germSurjective_of_epi ℚ (cokernel.π (Injective.ι F)) (germSurjective_of_injective ℚ _)

/-- Every global section of the constant sheaf `K` comes from `sky ⊞ K`, by exactness of global
sections on `[0, 1]`. -/
theorem constant_section_lift (s : K.presheaf.obj (op ⊤)) :
    ∃ t : (sky ⊞ K).presheaf.obj (op ⊤), (biprod.snd : sky ⊞ K ⟶ K).hom.app _ t = s :=
  sections_exact_Icc ℚ biprod.inl biprod.snd (0 : K ⟶ K) biprod.inl_snd (by simp)
    (ShortComplex.Splitting.ofHasBinaryBiproduct sky K).exact
    ((ShortComplex.exact_iff_epi _ rfl).2 inferInstance) germSurjective_sky s rfl

/-- Every global section of `K` comes from `sky ⊞ K`, from its local lifts along the section
`biprod.inr`. -/
theorem constant_section_lift_of_local (s : K.presheaf.obj (op ⊤)) :
    ∃ t : (sky ⊞ K).presheaf.obj (op ⊤), (biprod.snd : sky ⊞ K ⟶ K).hom.app _ t = s := by
  refine exists_section_lift_Icc ℚ _ (ShortComplex.Splitting.ofHasBinaryBiproduct sky K).exact
    germSurjective_sky s (fun x => ⟨⊤, trivial, (biprod.inr : K ⟶ sky ⊞ K).hom.app _ s, ?_⟩)
  have h := congrArg (fun φ : K ⟶ K => φ.hom.app (op ⊤) s) (biprod.inr_snd (X := sky) (Y := K))
  simp only at h
  rw [← ConcreteCategory.comp_apply, ← NatTrans.comp_app]
  exact h.trans (by rw [presheaf_map_eq _ _ (𝟙 _), CategoryTheory.Functor.map_id]; rfl)

/-- On the empty interval `[1, 0]` every global section lifts (there are no points). -/
theorem empty_section_lift
    (Sc : ShortComplex ((TopCat.of (Set.Icc (1 : ℝ) 0)).Sheaf (ModuleCat.{0} ℚ)))
    (hSc : Sc.Exact) (s : Sc.X₃.presheaf.obj (op ⊤)) :
    ∃ t : Sc.X₂.presheaf.obj (op ⊤), Sc.g.hom.app _ t = s :=
  exists_section_lift_Icc ℚ Sc hSc (fun _ x => absurd (x.2.1.trans x.2.2) (by norm_num)) s
    (fun x => absurd (x.2.1.trans x.2.2) (by norm_num))

end TDA.Sheaf.IntervalSectionsExamples
