import TDA.Sheaf.PointSheaf
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Filtered.Connected

/-!
# Constant sheaves of modules

The pullback from a point agrees with Mathlib's sheafification of a constant presheaf.
On a nonempty preconnected open, the unit identifies sections of the pullback with
the value on the point. A sheaf whose global sections map isomorphically to each
stalk is constant, via the constant sheaf adjunction.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits TopologicalSpace Opposite

namespace TDA.Sheaf

variable (k : Type) [Ring k]

/-- The value of `constSh k X N` on a nonempty preconnected open is `N(⊤)`, via the unit
followed by restriction. -/
theorem isIso_constSh_unitRes {X : TopCat.{0}} (N : pt.Sheaf (ModuleCat.{0} k))
    {V : Opens X} (hne : (V : Set X).Nonempty) (hc : IsPreconnected (V : Set X)) :
    IsIso (pullbackUnitRes k (toPt X) N (B := ⊤) (W := V) le_top) := by
  apply isIso_pullbackUnitRes
  · intro y _
    obtain ⟨x, hx⟩ := hne
    exact ⟨x, hx, Subsingleton.elim _ _⟩
  · intro O _
    exact isOpen_discrete _
  · intro y _
    have h : (toPt X) ⁻¹' {y} = Set.univ := Set.eq_univ_of_forall
      fun x => Set.mem_singleton_iff.2 (Subsingleton.elim (toPt X x) y)
    simpa only [h, Set.inter_univ] using hc

/-- Restrictions of `constSh` between nested nonempty preconnected opens are isomorphisms. -/
theorem isIso_restrict_constSh {X : TopCat.{0}} (N : pt.Sheaf (ModuleCat.{0} k))
    {V W : Opens X} (hVW : V ≤ W) (hne : (V : Set X).Nonempty)
    (hV : IsPreconnected (V : Set X)) (hW : IsPreconnected (W : Set X)) :
    IsIso ((constSh k X N).presheaf.map (homOfLE hVW).op) := by
  have := isIso_constSh_unitRes k N (hne.mono hVW) hW
  have := isIso_constSh_unitRes k N hne hV
  suffices IsIso (pullbackUnitRes k (toPt X) N (B := ⊤) (W := W) le_top ≫
      (constSh k X N).presheaf.map (homOfLE hVW).op) from
    IsIso.of_isIso_comp_left (pullbackUnitRes k (toPt X) N (B := ⊤) (W := W) le_top) _
  rw [pullbackUnitRes_map k (toPt X) N le_top le_top hVW le_rfl]
  rw [show (homOfLE (le_rfl : (⊤ : Opens pt) ≤ ⊤)).op = 𝟙 _ from Subsingleton.elim _ _,
    N.presheaf.map_id, Category.id_comp]
  infer_instance

/-- Pullback of a Mathlib constant sheaf gives the constant sheaf with the same value. -/
def pullbackConstantSheafIso {X Y : TopCat.{0}} (f : X ⟶ Y) :
    constantSheaf (Opens.grothendieckTopology Y) (ModuleCat.{0} k) ⋙
        TopCat.Sheaf.pullback (ModuleCat.{0} k) f ≅
      constantSheaf (Opens.grothendieckTopology X) (ModuleCat.{0} k) := by
  let adj := (constantSheafAdj (Opens.grothendieckTopology Y) (ModuleCat.{0} k)
    isTerminalTop).comp (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} k) f)
  exact adj.leftAdjointUniq
    (constantSheafAdj (Opens.grothendieckTopology X) (ModuleCat.{0} k) isTerminalTop)

/-- Restrictions of Mathlib's constant sheaf between nested nonempty preconnected opens are
isomorphisms. -/
theorem isIso_restrict_constantSheaf {X : TopCat.{0}} (M : ModuleCat.{0} k)
    {V W : Opens X} (hVW : V ≤ W) (hne : (V : Set X).Nonempty)
    (hV : IsPreconnected (V : Set X)) (hW : IsPreconnected (W : Set X)) :
    IsIso ((TopCat.Sheaf.presheaf ((constantSheaf (Opens.grothendieckTopology X)
      (ModuleCat.{0} k)).obj M)).map (homOfLE hVW).op) :=
  (NatIso.isIso_map_iff ((TopCat.Sheaf.forget (ModuleCat.{0} k) X).mapIso
    ((pullbackConstantSheafIso k (toPt X)).app M)) _).mp
      (isIso_restrict_constSh k _ hVW hne hV hW)

/-- The counit from the constant sheaf on the global sections is an isomorphism if the
global germ at every point is an isomorphism. -/
theorem isIso_constantSheaf_counit_of_isIso_Γgerm {X : TopCat.{0}}
    (F : X.Sheaf (ModuleCat.{0} k)) (h : ∀ x, IsIso (F.presheaf.Γgerm x)) :
    IsIso ((constantSheafAdj (Opens.grothendieckTopology X) (ModuleCat.{0} k)
      isTerminalTop).counit.app F) := by
  let J := Opens.grothendieckTopology X
  let F' : CategoryTheory.Sheaf J (ModuleCat.{0} k) := F
  let P : X.Presheaf (ModuleCat.{0} k) :=
    (Functor.const (Opens X)ᵒᵖ).obj (F.presheaf.obj (op ⊤))
  let α : P ⟶ F.presheaf := (constantPresheafAdj (ModuleCat.{0} k) isTerminalTop).counit.app
    F.presheaf
  let ε := (constantSheafAdj J (ModuleCat.{0} k) isTerminalTop).counit.app F'
  let εhom : sheafify J P ⟶ F.presheaf := ε.hom
  have hε : toSheafify J P ≫ εhom = α := by
    have he : ε.hom = sheafifyLift J α F'.property := by
      rw [sheafifyLift, Adjunction.homEquiv_counit]
      rfl
    change toSheafify J P ≫ ε.hom = α
    rw [he]
    exact toSheafify_sheafifyLift J α F'.property
  suffices ∀ x, IsIso ((TopCat.Presheaf.stalkFunctor (ModuleCat.{0} k) x).map ε.hom) from
    TopCat.Presheaf.isIso_of_stalkFunctor_map_iso ε
  intro x
  let G := TopCat.Presheaf.stalkFunctor (ModuleCat.{0} k) x
  change IsIso (G.map εhom)
  have hP : IsIso (P.Γgerm x) := by
    have : CategoryTheory.IsConnected (OpenNhds x)ᵒᵖ := IsFiltered.isConnected _
    let c := isColimitConstCocone (OpenNhds x)ᵒᵖ (F.presheaf.obj (op ⊤))
    let e := c.coconePointUniqueUpToIso (colimit.isColimit ((OpenNhds.inclusion x).op ⋙ P))
    have he : e.hom = P.Γgerm x := by
      have he := IsColimit.comp_coconePointUniqueUpToIso_hom c
        (colimit.isColimit ((OpenNhds.inclusion x).op ⋙ P)) (op ⟨⊤, trivial⟩)
      change 𝟙 _ ≫ e.hom = P.Γgerm x at he
      simpa only [Category.id_comp] using he
    exact he ▸ e.isIso_hom
  have hunit : IsIso (G.map (toSheafify J P)) :=
    TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x _ P
  let g : P.obj (op ⊤) ⟶ G.obj P := P.Γgerm x
  have hα : α.app (op ⊤) = 𝟙 (F.presheaf.obj (op ⊤)) := by
    change F.presheaf.map (isTerminalTop.from ⊤).op = _
    rw [Subsingleton.elim (isTerminalTop.from (⊤ : Opens X)) (𝟙 _), op_id, F.presheaf.map_id]
  have eq : g ≫ G.map (toSheafify J P) ≫ G.map εhom = F.presheaf.Γgerm x := by
    have he := congrArg (fun φ : P ⟶ F.presheaf => G.map φ) hε
    rw [G.map_comp] at he
    have hg : g ≫ G.map α = α.app (op ⊤) ≫ F.presheaf.Γgerm x :=
      TopCat.Presheaf.stalkFunctor_map_germ ⊤ x trivial α
    rw [he, hg, hα]
    exact Category.id_comp _
  have hcomp : IsIso (g ≫ G.map (toSheafify J P) ≫ G.map εhom) := eq.symm ▸ h x
  have hg : IsIso g := hP
  have hmap : IsIso (G.map (toSheafify J P) ≫ G.map εhom) := IsIso.of_isIso_comp_left g _
  exact IsIso.of_isIso_comp_left (G.map (toSheafify J P)) (G.map εhom)

/-- The constant sheaf pulled back from a sheaf `N` on the point is Mathlib's constant sheaf
with value `N(⊤)`. -/
def constShIsoConstantSheaf (X : TopCat.{0}) (N : pt.Sheaf (ModuleCat.{0} k)) :
    constSh k X N ≅
      (constantSheaf (Opens.grothendieckTopology X) (ModuleCat.{0} k)).obj
        (N.presheaf.obj (op ⊤)) := by
  let ε := (constantSheafAdj (Opens.grothendieckTopology pt) (ModuleCat.{0} k)
      isTerminalTop).counit.app N
  have : IsIso ε := isIso_constantSheaf_counit_of_isIso_Γgerm k N fun x =>
    (ConcreteCategory.isIso_iff_bijective _).2 (germ_top_bijective N x)
  exact (TopCat.Sheaf.pullback (ModuleCat.{0} k) (toPt X)).mapIso (asIso ε).symm ≪≫
    (pullbackConstantSheafIso k (toPt X)).app _

end TDA.Sheaf
