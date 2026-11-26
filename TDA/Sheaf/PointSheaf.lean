import TDA.Sheaf.SheafFlasque
import TDA.Sheaf.StalkPullback

/-!
# Sheaves on the point and constant sheaves

Let `k` be a ring. `pt` is the one-point space and `toPt X : X ⟶ pt` the unique map. Derived
global sections of a sheaf on `X` are its derived direct image along `toPt X`, valued in sheaves
of `k`-modules on `pt`.

* A sheaf of `k`-modules on `pt` is determined by its module of global sections: the germ map
  from global sections to the stalk is bijective (`germ_top_bijective`). Hence a complex of such
  sheaves is exact when its global sections are (`exact_of_sections_top`), and a morphism is an
  isomorphism when it is bijective on global sections (`isIso_of_bijective_app_top`).
* `constSh k X N := (toPt X)⁻¹ N` is the constant sheaf on `X` with value `N`, a sheaf on the
  point. Every germ of `constSh k X N` is the germ of a global section, so it is
  germ-surjective (`germSurjective_constSh`).
-/

noncomputable section
open CategoryTheory Limits TopologicalSpace Opposite

namespace TDA.Sheaf

/-- The one-point space. -/
abbrev pt : TopCat.{0} := TopCat.of PUnit.{1}

/-- The unique map to the point. -/
def toPt (X : TopCat.{0}) : X ⟶ pt := TopCat.ofHom (ContinuousMap.const X PUnit.unit)

/-- An open subset of the point that contains a point is everything. -/
theorem eq_top_of_mem_pt {U : Opens pt} {p : pt} (h : p ∈ U) : U = ⊤ :=
  eq_top_iff.2 fun q _ => Subsingleton.elim p q ▸ h

variable {k : Type} [Ring k]

/-- On the point, the germ map from global sections to the stalk is bijective. -/
theorem germ_top_bijective (F : pt.Sheaf (ModuleCat.{0} k)) (p : pt) :
    Function.Bijective (F.presheaf.germ ⊤ p trivial) := by
  constructor
  · intro a b hab
    obtain ⟨W, hW, i₁, i₂, he⟩ :=
      TopCat.Presheaf.germ_eq F.presheaf (U := ⊤) (V := ⊤) p trivial trivial a b hab
    obtain rfl := eq_top_of_mem_pt hW
    rwa [Subsingleton.elim i₁ (𝟙 _), Subsingleton.elim i₂ (𝟙 _), op_id, F.presheaf.map_id,
      ConcreteCategory.id_apply, ConcreteCategory.id_apply] at he
  · intro g
    obtain ⟨U, hU, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq F.presheaf g
    obtain rfl := eq_top_of_mem_pt hU
    exact ⟨s, rfl⟩

/-- A complex of sheaves of `k`-modules on the point is exact if its global sections are exact
at the middle term. -/
theorem exact_of_sections_top (S : ShortComplex (pt.Sheaf (ModuleCat.{0} k)))
    (h : ∀ s : S.X₂.presheaf.obj (op ⊤), S.g.hom.app _ s = 0 →
      ∃ t : S.X₁.presheaf.obj (op ⊤), S.f.hom.app _ t = s) : S.Exact := by
  rw [TopCat.Sheaf.exact_iff_stalkFunctor_map_exact]
  intro p
  rw [ShortComplex.moduleCat_exact_iff]
  intro y hy
  obtain ⟨s, rfl⟩ := (germ_top_bijective S.X₂ p).2 y
  have hy' : S.X₃.presheaf.germ ⊤ p trivial (S.g.hom.app _ s) = 0 :=
    (TopCat.Presheaf.stalkFunctor_map_germ_apply ⊤ p trivial S.g.hom s).symm.trans hy
  obtain ⟨t, rfl⟩ := h s ((germ_top_bijective S.X₃ p).1 (by rw [hy', map_zero]))
  exact ⟨S.X₁.presheaf.germ ⊤ p trivial t,
    TopCat.Presheaf.stalkFunctor_map_germ_apply ⊤ p trivial S.f.hom t⟩

/-- A morphism of sheaves of `k`-modules on the point that is bijective on global sections is an
isomorphism. -/
theorem isIso_of_bijective_app_top {F G : pt.Sheaf (ModuleCat.{0} k)} (φ : F ⟶ G)
    (h : Function.Bijective (φ.hom.app (op ⊤))) : IsIso φ := by
  have (p : pt) : IsIso ((TopCat.Presheaf.stalkFunctor _ p).map φ.hom) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    have e : (TopCat.Presheaf.stalkFunctor _ p).map φ.hom ∘ F.presheaf.germ ⊤ p trivial =
        G.presheaf.germ ⊤ p trivial ∘ φ.hom.app (op ⊤) :=
      funext fun s => TopCat.Presheaf.stalkFunctor_map_germ_apply _ _ _ _ s
    have hb := (germ_top_bijective G p).comp h
    rw [← e] at hb
    exact (Function.Bijective.of_comp_iff _ (germ_top_bijective F p)).1 hb
  exact TopCat.Presheaf.isIso_of_stalkFunctor_map_iso φ

variable (k) in
/-- The constant sheaf on `X` with value `N`, a sheaf on the point: the inverse image
`(toPt X)⁻¹ N`. -/
abbrev constSh (X : TopCat.{0}) (N : pt.Sheaf (ModuleCat.{0} k)) : X.Sheaf (ModuleCat.{0} k) :=
  (TopCat.Sheaf.pullback (ModuleCat.{0} k) (toPt X)).obj N

/-- **Constant sheaves are germ-surjective.** Every germ of `constSh k X N` is the germ of the
image of a global section of `N` under the adjunction unit `N ⟶ (toPt X)_* (toPt X)⁻¹ N`. -/
theorem germSurjective_constSh (X : TopCat.{0}) (N : pt.Sheaf (ModuleCat.{0} k)) :
    GermSurjective k (constSh k X N) := by
  intro V x hx g
  obtain ⟨n, hn⟩ :=
    (germ_top_bijective N (toPt X x)).2 ((stalkPullbackSheafIso k (toPt X) N x).inv g)
  refine ⟨(constSh k X N).presheaf.map (homOfLE (fun y _ => trivial :
    V ≤ (Opens.map (toPt X)).obj ⊤)).op
    (((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} k) (toPt X)).unit.app N).hom.app
      (op ⊤) n), ?_⟩
  refine (TopCat.Presheaf.germ_res_apply _ _ x hx _).trans ?_
  refine (stalkPullbackSheafIso_unit k (toPt X) N ⊤ x trivial n).symm.trans ?_
  rw [hn]
  exact Iso.inv_hom_id_apply _ _

end TDA.Sheaf
