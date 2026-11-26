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
* On the open interval `(0, 1)` and on the half-line `[0, ∞)`, with the skyscraper `skyAt` at a
  point and the constant sheaf `KS`, the complex `skyAt ⟶ skyAt ⊞ KS ⟶ KS` lifts every global
  section of `KS` from its local lifts (`exists_section_lift_ordConnected`:
  `section_lift_Ioo`, `section_lift_Ici`), and `sections_exact_ordConnected` gives the same
  lift from exactness (`section_lift_exact_Ioo`, `section_lift_exact_Ici`).
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

/-! ### Open intervals and half-lines -/

section OrdConnected

variable {S : Set ℝ}

/-- The skyscraper sheaf at a point `x` of `S` with value `ℚ`. -/
abbrev skyAt (x : TopCat.of S) : (TopCat.of S).Sheaf (ModuleCat.{0} ℚ) :=
  skyscraperSheaf x (ModuleCat.of ℚ ℚ)

variable (S) in
/-- The constant sheaf on `S` with value `ℚ`. -/
abbrev KS : (TopCat.of S).Sheaf (ModuleCat.{0} ℚ) :=
  (constantSheaf (Opens.grothendieckTopology (TopCat.of S)) (ModuleCat.{0} ℚ)).obj
    (ModuleCat.of ℚ ℚ)

theorem germSurjective_skyAt (x : TopCat.of S) : GermSurjective ℚ (skyAt x) :=
  @germSurjective_of_isFlasque ℚ _ _ (skyAt x) (isFlasque_skyscraperSheaf_of_hasZeroObject x _)

/-- On an order-connected `S`, every global section of `KS S` lifts to `skyAt x ⊞ KS S` from its
local lifts along `biprod.inr` (section lifting with `c = x`). -/
theorem section_lift_of_local (hS : S.OrdConnected) (x : TopCat.of S)
    (s : (KS S).presheaf.obj (op ⊤)) :
    ∃ t : (skyAt x ⊞ KS S).presheaf.obj (op ⊤),
      (biprod.snd : skyAt x ⊞ KS S ⟶ KS S).hom.app _ t = s := by
  refine exists_section_lift_ordConnected ℚ hS (x : ℝ) _
    (ShortComplex.Splitting.ofHasBinaryBiproduct (skyAt x) (KS S)).exact
    (fun V _ => germSurjective_skyAt x V) s
    (fun y => ⟨⊤, trivial, (biprod.inr : KS S ⟶ skyAt x ⊞ KS S).hom.app _ s, ?_⟩)
  have h := congrArg (fun φ : KS S ⟶ KS S => φ.hom.app (op ⊤) s)
    (biprod.inr_snd (X := skyAt x) (Y := KS S))
  simp only at h
  rw [← ConcreteCategory.comp_apply, ← NatTrans.comp_app]
  exact h.trans (by rw [presheaf_map_eq _ _ (𝟙 _), CategoryTheory.Functor.map_id]; rfl)

/-- On an order-connected `S`, every global section of `KS S` lifts to `skyAt x ⊞ KS S`, by
exactness of global sections. -/
theorem section_lift_of_exact (hS : S.OrdConnected) (x : TopCat.of S)
    (s : (KS S).presheaf.obj (op ⊤)) :
    ∃ t : (skyAt x ⊞ KS S).presheaf.obj (op ⊤),
      (biprod.snd : skyAt x ⊞ KS S ⟶ KS S).hom.app _ t = s :=
  sections_exact_ordConnected ℚ hS (x : ℝ) biprod.inl biprod.snd (0 : KS S ⟶ KS S) biprod.inl_snd
    (by simp) (ShortComplex.Splitting.ofHasBinaryBiproduct (skyAt x) (KS S)).exact
    ((ShortComplex.exact_iff_epi _ rfl).2 inferInstance) (fun V _ => germSurjective_skyAt x V) s
    rfl

end OrdConnected

/-- The midpoint `1/2` of the open interval `(0, 1)`. -/
def midIoo : TopCat.of (Set.Ioo (0 : ℝ) 1) := ⟨1 / 2, by norm_num, by norm_num⟩

/-- The end point `0` of the half-line `[0, ∞)`. -/
def zeroIci : TopCat.of (Set.Ici (0 : ℝ)) := ⟨0, Set.mem_Ici.2 (le_refl (0 : ℝ))⟩

/-- **Section lifting on the open interval `(0, 1)`.** -/
theorem section_lift_Ioo (s : (KS (Set.Ioo (0 : ℝ) 1)).presheaf.obj (op ⊤)) :
    ∃ t : (skyAt midIoo ⊞ KS (Set.Ioo (0 : ℝ) 1)).presheaf.obj (op ⊤),
      (biprod.snd : skyAt midIoo ⊞ KS _ ⟶ KS _).hom.app _ t = s :=
  section_lift_of_local Set.ordConnected_Ioo midIoo s

/-- **Section lifting on the half-line `[0, ∞)`.** -/
theorem section_lift_Ici (s : (KS (Set.Ici (0 : ℝ))).presheaf.obj (op ⊤)) :
    ∃ t : (skyAt zeroIci ⊞ KS (Set.Ici (0 : ℝ))).presheaf.obj (op ⊤),
      (biprod.snd : skyAt zeroIci ⊞ KS _ ⟶ KS _).hom.app _ t = s :=
  section_lift_of_local Set.ordConnected_Ici zeroIci s

/-- **Exactness of global sections on the open interval `(0, 1)`.** -/
theorem section_lift_exact_Ioo (s : (KS (Set.Ioo (0 : ℝ) 1)).presheaf.obj (op ⊤)) :
    ∃ t : (skyAt midIoo ⊞ KS (Set.Ioo (0 : ℝ) 1)).presheaf.obj (op ⊤),
      (biprod.snd : skyAt midIoo ⊞ KS _ ⟶ KS _).hom.app _ t = s :=
  section_lift_of_exact Set.ordConnected_Ioo midIoo s

/-- **Exactness of global sections on the half-line `[0, ∞)`.** -/
theorem section_lift_exact_Ici (s : (KS (Set.Ici (0 : ℝ))).presheaf.obj (op ⊤)) :
    ∃ t : (skyAt zeroIci ⊞ KS (Set.Ici (0 : ℝ))).presheaf.obj (op ⊤),
      (biprod.snd : skyAt zeroIci ⊞ KS _ ⟶ KS _).hom.app _ t = s :=
  section_lift_of_exact Set.ordConnected_Ici zeroIci s

end TDA.Sheaf.IntervalSectionsExamples
