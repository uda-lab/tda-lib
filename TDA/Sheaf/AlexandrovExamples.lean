import TDA.Sheaf.Alexandrov
import TDA.Persistence.Basic
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.CategoryTheory.ComposableArrows.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Order.Sum.Order

/-!
# Alexandrov sheaves of persistence modules: fixtures

These fixtures consume `TDA.Sheaf.Alexandrov` through actual Mathlib types.

* A two-point chain `Fin 2` with the module `0 ⟶ ℚ`: the sections over the whole space `↑0`
  are zero, the sections over `↑1` are `ℚ`, and the restriction along `↑1 ⊆ ↑0` is the
  noninvertible zero map. A morphism `0 ⟶ ℚ`, `ℚ ⟶ ℚ` of chains acts on sections as `α`
  does: invertibly over `↑1` and noninvertibly over `↑0`. The sections over `∅` are zero.
* The two-point antichain `Unit ⊕ Unit`: the whole space is not a principal open, and for
  every sheaf its sections over it are the product of the sections over the two points, by
  the restriction limit cone `restrictionConeIsLimit`.
* Real-indexed persistence modules `PModule.{0,0,0} K ℝ` over `K = ℚ` and `K = ZMod 2`:
  the equivalence, the section isomorphisms and their transition maps. The topology of `ℝ`
  itself is unchanged; the upper set topology lives on `WithUpperSet ℝ`.
-/

namespace TDA.Sheaf.AlexandrovExamples

open CategoryTheory Limits Opposite TopologicalSpace Topology TDA.Persistence
open TDA.Sheaf.Alexandrov

/-- A terminal object of `ModuleCat ℚ` has at most one element. -/
private theorem subsingleton_of_isTerminal {T : ModuleCat.{0} ℚ} (hT : IsTerminal T) :
    Subsingleton T :=
  (hT.uniqueUpToIso
    (ModuleCat.isZero_of_subsingleton (ModuleCat.of ℚ PUnit.{1})).isTerminal).toLinearEquiv
      |>.injective.subsingleton

/-! ## The two-point chain `0 ⟶ ℚ` -/

/-- The persistence module on `0 < 1` in `Fin 2` which is zero at `0`, `ℚ` at `1`, with the
zero map. -/
noncomputable abbrev chainModule : PModule.{0,0,0} ℚ (Fin 2) :=
  ComposableArrows.mk₁ (0 : ModuleCat.of ℚ PUnit.{1} ⟶ ModuleCat.of ℚ ℚ)

/-- The constant chain `ℚ ⟶ ℚ` with the identity map. -/
noncomputable abbrev constChain : PModule.{0,0,0} ℚ (Fin 2) :=
  ComposableArrows.mk₁ (𝟙 (ModuleCat.of ℚ ℚ))

/-- The morphism `chainModule ⟶ constChain` which is `0` at `0` and the identity at `1`. -/
noncomputable abbrev chainInclusion : chainModule ⟶ constChain :=
  ComposableArrows.homMk₁ 0 (𝟙 _) (by simp)

/-- The sheaf on the upper Alexandrov space of `Fin 2` attached to `chainModule`. -/
noncomputable abbrev chainSheaf : (upperSpace (Fin 2)).Sheaf (ModuleCat.{0} ℚ) :=
  (upperSetEquivalence (Fin 2) (ModuleCat.{0} ℚ)).functor.obj chainModule

/-- The principal open of `p : Fin 2` in the upper Alexandrov space. -/
abbrev chainOpen (p : Fin 2) : Opens (upperSpace (Fin 2)) :=
  _root_.Alexandrov.principalOpen (X := upperSpace (Fin 2)) (WithUpperSet.toUpperSet p)

/-- The principal open of the lower point is the whole space. -/
example : chainOpen 0 = ⊤ := by
  ext x
  simp only [Opens.coe_top, Set.mem_univ, iff_true]
  exact Fin.zero_le (WithUpperSet.ofUpperSet x)

/-- Sections over the whole space `↑0` are zero, as `M 0 = 0`. -/
example : Subsingleton (chainSheaf.presheaf.obj (op (chainOpen 0))) :=
  haveI : Subsingleton (chainModule.obj 0) := inferInstanceAs (Subsingleton PUnit)
  (upperSetSectionsIso chainModule 0).toLinearEquiv.injective.subsingleton

/-- Sections over `↑1` are `ℚ`. -/
noncomputable example : chainSheaf.presheaf.obj (op (chainOpen 1)) ≅ ModuleCat.of ℚ ℚ :=
  upperSetSectionsIso chainModule 1

example : Nontrivial (chainSheaf.presheaf.obj (op (chainOpen 1))) :=
  haveI : Nontrivial (chainModule.obj 1) := inferInstanceAs (Nontrivial ℚ)
  (upperSetSectionsIso chainModule 1).toLinearEquiv.symm.injective.nontrivial

/-- The restriction along `↑1 ⊆ ↑0`, the transition map of the sheaf from `0` to `1`. -/
noncomputable abbrev chainRestriction :
    chainSheaf.presheaf.obj (op (chainOpen 0)) ⟶ chainSheaf.presheaf.obj (op (chainOpen 1)) :=
  chainSheaf.presheaf.map
    (homOfLE (_root_.Alexandrov.principalOpen_le (X := upperSpace (Fin 2))
      (x := WithUpperSet.toUpperSet (0 : Fin 2)) (y := WithUpperSet.toUpperSet (1 : Fin 2))
      (show (0 : Fin 2) ≤ 1 by decide))).op

/-- The transition is `M.map (0 ≤ 1) = 0` under the section isomorphisms. -/
example : chainRestriction ≫ (upperSetSectionsIso chainModule 1).hom =
    (upperSetSectionsIso chainModule 0).hom ≫ 0 :=
  upperSetSectionsIso_hom_naturality chainModule (show (0 : Fin 2) ≤ 1 by decide)

/-- The transition from `0` to `1` is not invertible: a reversed or identity-like transition
cannot satisfy this fixture. -/
example : ¬ IsIso chainRestriction := by
  intro h
  have key := upperSetSectionsIso_hom_naturality chainModule (show (0 : Fin 2) ≤ 1 by decide)
  have hiso : IsIso (chainModule.map (homOfLE (show (0 : Fin 2) ≤ 1 by decide))) := by
    rw [(Iso.eq_inv_comp _).mpr key.symm]
    infer_instance
  have : Subsingleton (chainModule.obj 0) := inferInstanceAs (Subsingleton PUnit)
  have hsub : Subsingleton (chainModule.obj 1) :=
    (asIso (chainModule.map (homOfLE (show (0 : Fin 2) ≤ 1 by decide)))).toLinearEquiv.symm
      |>.injective.subsingleton
  have hq : Subsingleton ℚ := hsub
  exact one_ne_zero (Subsingleton.elim (1 : ℚ) 0)

/-- On sections over `↑1`, the sheaf morphism attached to `chainInclusion` is invertible,
as `chainInclusion.app 1 = 𝟙`. -/
example : IsIso (((upperSetEquivalence (Fin 2) (ModuleCat.{0} ℚ)).functor.map
    chainInclusion).hom.app (op (chainOpen 1))) := by
  have h := upperSetEquivalence_map_app_sectionsIso chainInclusion 1
  rw [← Iso.eq_comp_inv] at h
  rw [h]
  have : IsIso (chainInclusion.app 1) := inferInstanceAs (IsIso (𝟙 (ModuleCat.of ℚ ℚ)))
  infer_instance

/-- On sections over `↑0`, the same morphism is the zero map `0 ⟶ ℚ`, not invertible. -/
example : ¬ IsIso (((upperSetEquivalence (Fin 2) (ModuleCat.{0} ℚ)).functor.map
    chainInclusion).hom.app (op (chainOpen 0))) := by
  intro h
  have h' := upperSetEquivalence_map_app_sectionsIso chainInclusion 0
  rw [← Iso.eq_comp_inv] at h'
  rw [h'] at h
  have hiso : IsIso ((upperSetSectionsIso chainModule 0).inv ≫
      ((upperSetSectionsIso chainModule 0).hom ≫ chainInclusion.app 0 ≫
        (upperSetSectionsIso constChain 0).inv) ≫ (upperSetSectionsIso constChain 0).hom) :=
    inferInstance
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Iso.inv_hom_id_assoc] at hiso
  have : Subsingleton (chainModule.obj 0) := inferInstanceAs (Subsingleton PUnit)
  have hsub : Subsingleton (constChain.obj 0) :=
    (asIso (chainInclusion.app 0)).toLinearEquiv.symm.injective.subsingleton
  have hq : Subsingleton ℚ := hsub
  exact one_ne_zero (Subsingleton.elim (1 : ℚ) 0)

/-- Sections over the empty open are zero, by the sheaf condition for the empty cover. -/
example : Subsingleton (chainSheaf.presheaf.obj (op ⊥)) :=
  subsingleton_of_isTerminal (TopCat.Sheaf.isTerminalOfEmpty chainSheaf)

/-! ## The two-point antichain -/

/-- The two-point antichain. -/
abbrev Antichain : Type := Unit ⊕ Unit

/-- The left point of the antichain in its upper Alexandrov space. -/
abbrev leftPt : upperSpace Antichain := WithUpperSet.toUpperSet (Sum.inl ())

/-- The right point of the antichain in its upper Alexandrov space. -/
abbrev rightPt : upperSpace Antichain := WithUpperSet.toUpperSet (Sum.inr ())

private theorem antichain_eq_of_le {p q : upperSpace Antichain} (h : p ≤ q) : p = q := by
  rcases p with ⟨⟨⟩⟩ | ⟨⟨⟩⟩ <;> rcases q with ⟨⟨⟩⟩ | ⟨⟨⟩⟩
  · rfl
  · exact absurd h Sum.not_inl_le_inr
  · exact absurd h Sum.not_inr_le_inl
  · rfl

/-- The whole antichain is not a principal open. -/
example (p : upperSpace Antichain) : _root_.Alexandrov.principalOpen p ≠ ⊤ := by
  intro h
  have hl : leftPt ∈ _root_.Alexandrov.principalOpen p := h ▸ trivial
  have hr : rightPt ∈ _root_.Alexandrov.principalOpen p := h ▸ trivial
  exact absurd ((antichain_eq_of_le hl).symm.trans (antichain_eq_of_le hr))
    (WithUpperSet.toUpperSet.injective.ne Sum.inl_ne_inr)

section Antichain

variable {C : Type*} [Category.{0} C] [HasLimits C] (F : (upperSpace Antichain).Sheaf C)

/-- A leg over a principal open of the antichain, from legs over the two points. -/
private noncomputable def antichainLeg {W : C}
    (fa : W ⟶ F.presheaf.obj (op (_root_.Alexandrov.principalOpen leftPt)))
    (fb : W ⟶ F.presheaf.obj (op (_root_.Alexandrov.principalOpen rightPt))) :
    ∀ p : upperSpace Antichain,
      W ⟶ F.presheaf.obj (op (_root_.Alexandrov.principalOpen p))
  | Sum.inl () => fa
  | Sum.inr () => fb

/-- The cone over the principal opens contained in the whole antichain given by two legs. -/
private noncomputable def antichainCone {W : C}
    (fa : W ⟶ F.presheaf.obj (op (_root_.Alexandrov.principalOpen leftPt)))
    (fb : W ⟶ F.presheaf.obj (op (_root_.Alexandrov.principalOpen rightPt))) :
    Cone (StructuredArrow.proj (op ⊤) (_root_.Alexandrov.principals (upperSpace Antichain)) ⋙
      _root_.Alexandrov.principals (upperSpace Antichain) ⋙ F.presheaf) where
  pt := W
  π :=
    { app := fun j => antichainLeg F fa fb j.right
      naturality := by
        rintro ⟨⟨⟩, p, hp⟩ ⟨⟨⟩, q, hq⟩ g
        obtain rfl : p = q := antichain_eq_of_le (leOfHom g.right)
        have hg : g.right = 𝟙 p := Subsingleton.elim _ _
        have hmap : F.presheaf.map
            ((_root_.Alexandrov.principals (upperSpace Antichain)).map g.right) = 𝟙 _ := by
          rw [hg, CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
        change 𝟙 W ≫ antichainLeg F fa fb p = antichainLeg F fa fb p ≫
          F.presheaf.map ((_root_.Alexandrov.principals (upperSpace Antichain)).map g.right)
        rw [Category.id_comp]
        exact (Category.comp_id _).symm.trans (congrArg (antichainLeg F fa fb p ≫ ·) hmap.symm) }

/-- For every sheaf on the antichain, the sections over the whole (non-principal) space are the
product of the sections over the two points, with the restrictions as projections. The proof
uses only the restriction limit cone `restrictionConeIsLimit`. -/
noncomputable def antichainIsProduct :
    IsLimit (BinaryFan.mk
      (F.presheaf.map (homOfLE (le_top : _root_.Alexandrov.principalOpen leftPt ≤ ⊤)).op)
      (F.presheaf.map (homOfLE (le_top : _root_.Alexandrov.principalOpen rightPt ≤ ⊤)).op)) :=
  BinaryFan.IsLimit.mk _
    (fun fa fb => (restrictionConeIsLimit F ⊤).lift (antichainCone F fa fb))
    (fun fa fb => (restrictionConeIsLimit F ⊤).fac (antichainCone F fa fb)
      (StructuredArrow.mk (homOfLE le_top).op))
    (fun fa fb => (restrictionConeIsLimit F ⊤).fac (antichainCone F fa fb)
      (StructuredArrow.mk (homOfLE le_top).op))
    (fun fa fb m h₁ h₂ => (restrictionConeIsLimit F ⊤).uniq (antichainCone F fa fb) m
      (fun j => by
        rcases j with ⟨⟨⟩, p, hp⟩
        rcases p with ⟨⟨⟩⟩ | ⟨⟨⟩⟩
        · obtain rfl : hp = (homOfLE le_top).op := Subsingleton.elim _ _
          exact h₁
        · obtain rfl : hp = (homOfLE le_top).op := Subsingleton.elim _ _
          exact h₂))

end Antichain

/-- The constant module `ℚ` on the antichain. -/
noncomputable abbrev constAntichain : upperSpace Antichain ⥤ ModuleCat.{0} ℚ :=
  (Functor.const _).obj (ModuleCat.of ℚ ℚ)

/-- For the constant module `ℚ` on the antichain, the sections of its sheaf over the whole
space are a product of two copies of `ℚ`, with projections the restrictions followed by the
counit. -/
noncomputable example :
    IsLimit (BinaryFan.mk
      (((kanSheaf (upperSpace Antichain) (ModuleCat.{0} ℚ)).obj constAntichain).presheaf.map
          (homOfLE (le_top : _root_.Alexandrov.principalOpen leftPt ≤ ⊤)).op ≫
        ((counitIso (upperSpace Antichain) (ModuleCat.{0} ℚ)).hom.app constAntichain).app leftPt)
      (((kanSheaf (upperSpace Antichain) (ModuleCat.{0} ℚ)).obj constAntichain).presheaf.map
          (homOfLE (le_top : _root_.Alexandrov.principalOpen rightPt ≤ ⊤)).op ≫
        ((counitIso (upperSpace Antichain) (ModuleCat.{0} ℚ)).hom.app constAntichain).app
          rightPt)) :=
  BinaryFan.isLimitCompRightIso _
    (((counitIso (upperSpace Antichain) (ModuleCat.{0} ℚ)).hom.app constAntichain).app rightPt)
    (BinaryFan.isLimitCompLeftIso _
      (((counitIso (upperSpace Antichain) (ModuleCat.{0} ℚ)).hom.app constAntichain).app leftPt)
      (antichainIsProduct ((kanSheaf (upperSpace Antichain) (ModuleCat.{0} ℚ)).obj
        constAntichain)))

/-! ## Real-indexed persistence modules over `ℚ` and `ZMod 2` -/

/-- The upper set topology lives on `WithUpperSet ℝ`, distinct from the topology of `ℝ`:
`(-∞, 0)` is open in `ℝ` but not in `WithUpperSet ℝ`. -/
example : IsOpen (Set.Iio (0 : ℝ)) ∧
    ¬ IsOpen (WithUpperSet.ofUpperSet ⁻¹' Set.Iio (0 : ℝ) : Set (WithUpperSet ℝ)) := by
  refine ⟨isOpen_Iio, fun h => ?_⟩
  rw [IsUpperSet.isOpen_iff_isUpperSet] at h
  have hmem : WithUpperSet.toUpperSet (-1 : ℝ) ∈
      (WithUpperSet.ofUpperSet ⁻¹' Set.Iio (0 : ℝ) : Set (WithUpperSet ℝ)) := by
    show (-1 : ℝ) < 0
    norm_num
  have := h (show WithUpperSet.toUpperSet (-1 : ℝ) ≤ WithUpperSet.toUpperSet 0 by
    show (-1 : ℝ) ≤ 0
    norm_num) hmem
  exact lt_irrefl (0 : ℝ) this

/-- Real-indexed persistence modules over `ℚ` are sheaves on the upper Alexandrov space of `ℝ`. -/
noncomputable example : PModule.{0,0,0} ℚ ℝ ≌ (upperSpace ℝ).Sheaf (ModuleCat.{0} ℚ) :=
  upperSetEquivalence ℝ (ModuleCat.{0} ℚ)

/-- Real-indexed persistence modules over `ZMod 2` are sheaves on the upper Alexandrov space of
`ℝ`. -/
noncomputable example :
    PModule.{0,0,0} (ZMod 2) ℝ ≌ (upperSpace ℝ).Sheaf (ModuleCat.{0} (ZMod 2)) :=
  upperSetEquivalence ℝ (ModuleCat.{0} (ZMod 2))

/-- For a real-indexed module over `ℚ`, the restriction along `↑t ⊆ ↑s` for `s ≤ t` is the
structure map `M (s ≤ t)`. -/
example (M : PModule.{0,0,0} ℚ ℝ) {s t : ℝ} (h : s ≤ t) :
    ((upperSetEquivalence ℝ (ModuleCat.{0} ℚ)).functor.obj M).presheaf.map
        (homOfLE (_root_.Alexandrov.principalOpen_le (X := upperSpace ℝ)
          (x := WithUpperSet.toUpperSet s) (y := WithUpperSet.toUpperSet t) h)).op ≫
        (upperSetSectionsIso M t).hom =
      (upperSetSectionsIso M s).hom ≫ structureMap M h :=
  upperSetSectionsIso_hom_naturality M h

/-- The same identification over `ZMod 2`. -/
example (M : PModule.{0,0,0} (ZMod 2) ℝ) {s t : ℝ} (h : s ≤ t) :
    ((upperSetEquivalence ℝ (ModuleCat.{0} (ZMod 2))).functor.obj M).presheaf.map
        (homOfLE (_root_.Alexandrov.principalOpen_le (X := upperSpace ℝ)
          (x := WithUpperSet.toUpperSet s) (y := WithUpperSet.toUpperSet t) h)).op ≫
        (upperSetSectionsIso M t).hom =
      (upperSetSectionsIso M s).hom ≫ structureMap M h :=
  upperSetSectionsIso_hom_naturality M h

/-- Every sheaf of `ZMod 2`-modules on the upper Alexandrov space of `ℝ` is recovered from its
principal sections. -/
noncomputable example (F : (upperSpace ℝ).Sheaf (ModuleCat.{0} (ZMod 2))) :
    F ≅ (kanSheaf (upperSpace ℝ) _).obj ((principalSections (upperSpace ℝ) _).obj F) :=
  (unitIso (upperSpace ℝ) (ModuleCat.{0} (ZMod 2))).app F

/-- The constant real-indexed module `ℚ` has sections `ℚ` over every principal open. -/
example (t : ℝ) : Nontrivial
    (((upperSetEquivalence ℝ (ModuleCat.{0} ℚ)).functor.obj
      ((Functor.const ℝ).obj (ModuleCat.of ℚ ℚ))).presheaf.obj
        (op (_root_.Alexandrov.principalOpen (X := upperSpace ℝ) (WithUpperSet.toUpperSet t)))) :=
  haveI : Nontrivial (((Functor.const ℝ).obj (ModuleCat.of ℚ ℚ)).obj t) :=
    inferInstanceAs (Nontrivial ℚ)
  (upperSetSectionsIso _ t).toLinearEquiv.symm.injective.nontrivial

end TDA.Sheaf.AlexandrovExamples
