import Mathlib.Algebra.Category.ModuleCat.Adjunctions
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.Topology.Sheaves.Flasque
import Mathlib.Topology.Sheaves.LocallySurjective

/-!
# Flasque and germ-surjective sheaves of modules

Let `k` be a ring and `X : TopCat`. Mathlib's `TopCat.Sheaf.IsFlasque` (every restriction map
is an epimorphism) is stated for any value category; this file supplies the facts about
flasque sheaves of `k`-modules that the cohomology of compact intervals uses.

* `isFlasque_of_injective`: an injective object of `X.Sheaf (ModuleCat k)` is flasque. The
  underlying presheaf of an injective sheaf is injective, because sheafification preserves
  monomorphisms (`Injective.injective_of_adjoint`). For opens `U ≤ V`, a section over `U` is
  a morphism out of the free presheaf `yoneda.obj U ⋙ ModuleCat.free k`, and the induced map
  of free presheaves for `U ≤ V` is a monomorphism; injectivity extends the morphism to `V`.
  These free presheaves are private helpers: a concrete model, in which the monomorphism is a
  `Finsupp.mapDomain`, of Mathlib's `CategoryTheory.Presheaf.freeYoneda U (ModuleCat.of k k)`.
* `GermSurjective F`: every germ of `F` at `x` is the germ of a section over every open
  neighbourhood of `x`. Flasque sheaves are germ-surjective (`germSurjective_of_isFlasque`,
  hence `germSurjective_of_injective`), and germ-surjectivity passes to quotients
  (`germSurjective_of_epi`).
* `exists_local_preimage_of_exact`: for an exact complex `X₁ ⟶ X₂ ⟶ X₃` of sheaves, a section
  of `X₂` killed by `X₂ ⟶ X₃` comes from `X₁` on a neighbourhood of each point.

The epimorphism criterion `TopCat.Sheaf.IsFlasque.epi_of_shortExact` and its corollaries are
stated for abelian groups only at the pinned Mathlib; they are not needed here.
-/

noncomputable section
open CategoryTheory Limits TopologicalSpace Opposite

namespace TDA.Sheaf

variable (k : Type) [Ring k]

section FreeYoneda

variable {X : TopCat.{0}}

/-- The free presheaf of `k`-modules on the open `U`: its module of sections over `W` is free on
the inclusions `W ⟶ U`, so it is `k` when `W ≤ U` and zero otherwise. -/
private abbrev freeYonedaPresheaf (U : Opens X) : X.Presheaf (ModuleCat.{0} k) :=
  yoneda.obj U ⋙ ModuleCat.free k

/-- The morphism of free presheaves induced by an inclusion of opens. -/
private abbrev freeYonedaMap {U V : Opens X} (h : U ≤ V) :
    freeYonedaPresheaf k U ⟶ freeYonedaPresheaf k V :=
  Functor.whiskerRight (yoneda.map (homOfLE h)) (ModuleCat.free k)

/-- The morphism of free presheaves induced by an inclusion of opens is a monomorphism. -/
private instance mono_freeYonedaMap {U V : Opens X} (h : U ≤ V) : Mono (freeYonedaMap k h) := by
  have (W : (Opens X)ᵒᵖ) : Mono ((freeYonedaMap k h).app W) := by
    rw [ModuleCat.mono_iff_injective]
    exact Finsupp.mapDomain_injective (fun _ _ _ => Subsingleton.elim (α := unop W ⟶ U) _ _)
  exact NatTrans.mono_of_mono_app _

/-- The morphism out of the free presheaf on `U` that classifies a section `a` over `U`. -/
private def freeYonedaDesc (F : X.Presheaf (ModuleCat.{0} k)) {U : Opens X}
    (a : F.obj (op U)) : freeYonedaPresheaf k U ⟶ F where
  app W := ModuleCat.freeDesc (TypeCat.ofHom fun f : unop W ⟶ U => F.map f.op a)
  naturality W W' g := by
    refine ModuleCat.free_hom_ext (fun f => ?_)
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, Functor.comp_map,
      ModuleCat.free_map_apply, ModuleCat.freeDesc_apply, ModuleCat.freeDesc_apply]
    change F.map (g.unop ≫ f).op a = F.map g (F.map f.op a)
    rw [op_comp, F.map_comp, ConcreteCategory.comp_apply]
    rfl

@[simp]
private theorem freeYonedaDesc_app_freeMk (F : X.Presheaf (ModuleCat.{0} k)) {U W : Opens X}
    (a : F.obj (op U)) (f : W ⟶ U) :
    (freeYonedaDesc k F a).app (op W) (ModuleCat.freeMk f) = F.map f.op a :=
  ModuleCat.freeDesc_apply _ _

end FreeYoneda

variable {X : TopCat.{0}}

/-- An injective presheaf of `k`-modules has surjective restriction maps. -/
theorem presheaf_isFlasque_of_injective (P : X.Presheaf (ModuleCat.{0} k)) [Injective P] :
    TopCat.Presheaf.IsFlasque P where
  epi {U' V'} i := by
    induction U' with | op V => ?_
    induction V' with | op U => ?_
    have h : U ≤ V := leOfHom i.unop
    rw [ModuleCat.epi_iff_surjective]
    intro a
    let ψ := Injective.factorThru (freeYonedaDesc k P a) (freeYonedaMap k h)
    have hψ : freeYonedaMap k h ≫ ψ = freeYonedaDesc k P a := Injective.comp_factorThru _ _
    have e : (freeYonedaPresheaf k V).map i (ModuleCat.freeMk (𝟙 V)) =
        (freeYonedaMap k h).app (op U) (ModuleCat.freeMk (𝟙 U)) := by
      rw [Functor.comp_map, Functor.whiskerRight_app, ModuleCat.free_map_apply,
        ModuleCat.free_map_apply]
      exact congrArg ModuleCat.freeMk (Subsingleton.elim (α := U ⟶ V) _ _)
    refine ⟨ψ.app (op V) (ModuleCat.freeMk (𝟙 V)), ?_⟩
    rw [← NatTrans.naturality_apply, e, ← ConcreteCategory.comp_apply, ← NatTrans.comp_app, hψ,
      freeYonedaDesc_app_freeMk, op_id, P.map_id, ConcreteCategory.id_apply]

/-- **Injective sheaves of `k`-modules are flasque.** -/
theorem isFlasque_of_injective (I : X.Sheaf (ModuleCat.{0} k)) [Injective I] :
    TopCat.Sheaf.IsFlasque I := by
  have hmono :
      (presheafToSheaf (Opens.grothendieckTopology X) (ModuleCat.{0} k)).PreservesMonomorphisms :=
    inferInstance
  have : Injective ((sheafToPresheaf _ _).obj I) :=
    @Injective.injective_of_adjoint _ _ _ _ _ _ hmono (sheafificationAdjunction _ _) I ‹_›
  exact @presheaf_isFlasque_of_injective k _ X I.obj this

/-- A sheaf is germ-surjective if every germ at `x` is the germ of a section over every open
neighbourhood `V` of `x`. -/
def GermSurjective (F : X.Sheaf (ModuleCat.{0} k)) : Prop :=
  ∀ (V : Opens X) (x : X) (hx : x ∈ V), Function.Surjective (F.presheaf.germ V x hx)

/-- Flasque sheaves are germ-surjective. -/
theorem germSurjective_of_isFlasque (F : X.Sheaf (ModuleCat.{0} k))
    [TopCat.Sheaf.IsFlasque F] : GermSurjective k F := by
  intro V x hx g
  obtain ⟨U, hxU, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq F.presheaf g
  have hepi : Epi (F.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op) := inferInstance
  obtain ⟨t, ht⟩ := (ModuleCat.epi_iff_surjective _).1 hepi
    (F.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op s)
  refine ⟨t, ?_⟩
  have h1 := TopCat.Presheaf.germ_res_apply F.presheaf (homOfLE (inf_le_right : U ⊓ V ≤ V)) x
    ⟨hxU, hx⟩ t
  have h2 := TopCat.Presheaf.germ_res_apply F.presheaf (homOfLE (inf_le_left : U ⊓ V ≤ U)) x
    ⟨hxU, hx⟩ s
  rw [ht] at h1
  exact h1.symm.trans h2

/-- Injective sheaves of `k`-modules are germ-surjective. -/
theorem germSurjective_of_injective (I : X.Sheaf (ModuleCat.{0} k)) [Injective I] :
    GermSurjective k I :=
  @germSurjective_of_isFlasque k _ X I (isFlasque_of_injective k I)

/-- Germ-surjectivity passes to quotients: if `π : F ⟶ G` is an epimorphism of sheaves and `F`
is germ-surjective, so is `G`. -/
theorem germSurjective_of_epi {F G : X.Sheaf (ModuleCat.{0} k)} (π : F ⟶ G) [Epi π]
    (hF : GermSurjective k F) : GermSurjective k G := by
  intro V x hx g
  have hloc := (TopCat.Sheaf.isLocallySurjective_iff_epi π).2 inferInstance
  obtain ⟨h, rfl⟩ :=
    (TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks π.hom).1 hloc x g
  obtain ⟨t, rfl⟩ := hF V x hx h
  exact ⟨π.hom.app (op V) t, (TopCat.Presheaf.stalkFunctor_map_germ_apply V x hx π.hom t).symm⟩

/-- **Local preimages along an exact complex.** If `X₁ ⟶ X₂ ⟶ X₃` is exact and a section `s` of
`X₂` over `U` maps to zero in `X₃`, then near every point of `U` the section `s` is the image of a
section of `X₁`. -/
theorem exists_local_preimage_of_exact (S : ShortComplex (X.Sheaf (ModuleCat.{0} k)))
    (hS : S.Exact) {U : Opens X} (s : S.X₂.presheaf.obj (op U)) (hs : S.g.hom.app _ s = 0)
    (x : X) (hx : x ∈ U) :
    ∃ (W : Opens X) (_ : x ∈ W) (hWU : W ≤ U) (t : S.X₁.presheaf.obj (op W)),
      S.f.hom.app _ t = S.X₂.presheaf.map (homOfLE hWU).op s := by
  have hx' := (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact S).1 hS x
  rw [ShortComplex.moduleCat_exact_iff] at hx'
  obtain ⟨y, hy⟩ := hx' (S.X₂.presheaf.germ U x hx s) (by
    change (TopCat.Presheaf.stalkFunctor _ x).map S.g.hom (S.X₂.presheaf.germ U x hx s) = 0
    rw [TopCat.Presheaf.stalkFunctor_map_germ_apply, hs]
    exact map_zero _)
  obtain ⟨W₀, hxW₀, t₀, rfl⟩ := TopCat.Presheaf.exists_germ_eq S.X₁.presheaf y
  change (TopCat.Presheaf.stalkFunctor _ x).map S.f.hom (S.X₁.presheaf.germ W₀ x hxW₀ t₀) = _
    at hy
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply] at hy
  obtain ⟨W, hxW, iW₀, iU, he⟩ := TopCat.Presheaf.germ_eq S.X₂.presheaf x hxW₀ hx _ _ hy
  refine ⟨W, hxW, leOfHom iU, S.X₁.presheaf.map iW₀.op t₀, ?_⟩
  rw [← ConcreteCategory.comp_apply, S.f.hom.naturality, ConcreteCategory.comp_apply]
  exact he

end TDA.Sheaf
