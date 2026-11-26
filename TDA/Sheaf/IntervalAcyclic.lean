import TDA.Sheaf.FlasqueAcyclic
import TDA.Sheaf.IntervalCohomology

/-!
# Germ-surjective sheaves are acyclic for global sections on a compact interval

Let `k` be a ring.

* `germ_pullback_surjective`: if the germs of `G` at `i x` are germs of sections over an open
  `W ⊇ i(V)`, the germs of `i⁻¹ G` at `x` are germs of sections over `V`. A germ of `i⁻¹ G` at
  `x` is a germ of `G` at `i x` (`stalkPullbackSheafIso`), hence the germ of a section of `G`
  over `W`, whose image under the adjunction unit is a section of `i⁻¹ G` over `i⁻¹ W`.
* `germSurjective_pullback`: the inverse image `i⁻¹ G` of a germ-surjective sheaf `G` along any
  continuous map `i` is germ-surjective (the case `W = X`). In particular inverse images of
  flasque (for instance injective) sheaves are germ-surjective
  (`germSurjective_pullback_of_isFlasque`).
* `germSurjective_of_id_eq_add`: a sheaf `Z` with `𝟙 Z = p₁ ≫ i₁ + p₂ ≫ i₂` for maps through
  germ-surjective sheaves is germ-surjective.
* `pushforward_toPt_shortExact_Icc`: on `[u, v]`, global sections keep a short exact sequence
  with germ-surjective first term short exact (`exists_section_lift_Icc`).
* `acyclicClass_germSurjective_Icc`: germ-surjective sheaves form an acyclic class
  (`TDA.Sheaf.AcyclicClass`) for global sections `(toPt [u, v])_*`. Hence a bounded below complex
  of germ-surjective sheaves computes `RΓ([u, v]; -)`
  (`isIso_rightDerivedFunctorPlusUnit_app_toPt_Icc_of_germSurjective`).
* `isZero_H_Icc_pullback_of_isFlasque`: `Hⁱ([u, v]; ι⁻¹ I) = 0` for `1 ≤ i`, a flasque sheaf
  `I` on any space and any continuous `ι` from `[u, v]`.
* `isIso_derivedUnit_Icc`: for `u ≤ v`, the derived unit `𝟭 ⟶ (toPt [u, v])⁻¹ ⋙ RΓ([u, v]; -)`
  of `D⁺(Sh pt)` is an isomorphism. On a complex `K` the unit is termwise the isomorphism
  `Kⁿ ⟶ Γ([u, v]; constSh Kⁿ)` (`isIso_unit_constSh_Icc`), and the constant terms are
  germ-surjective, so they compute `RΓ([u, v]; -)`.
-/

noncomputable section
open CategoryTheory Limits TopologicalSpace Opposite

namespace TDA.Sheaf

variable {k : Type} [Ring k]

section germ

/-- **Germs of an inverse image from germs downstairs.** Let `i : K ⟶ X` be continuous, `G` a
sheaf of `k`-modules on `X`, `V` an open of `K` containing `x`, and `W` an open of `X` with
`i(V) ⊆ W`. If every germ of `G` at `i x` is the germ of a section over `W`, then every germ of
`i⁻¹ G` at `x` is the germ of a section over `V`: a germ of `i⁻¹ G` at `x` is a germ of `G` at
`i x` (`stalkPullbackSheafIso`), and the adjunction unit carries a section over `W` to a section
of `i⁻¹ G` over `i⁻¹ W ⊇ V`. -/
theorem germ_pullback_surjective {K X : TopCat.{0}} (i : K ⟶ X) (G : X.Sheaf (ModuleCat.{0} k))
    {V : Opens K} {x : K} (hx : x ∈ V) {W : Opens X} (hVW : V ≤ (Opens.map i).obj W)
    (hW : Function.Surjective (G.presheaf.germ W (i x) (hVW hx))) :
    Function.Surjective
      (((TopCat.Sheaf.pullback (ModuleCat.{0} k) i).obj G).presheaf.germ V x hx) := by
  intro g
  obtain ⟨g₀, rfl⟩ : ∃ g₀, (stalkPullbackSheafIso k i G x).hom g₀ = g :=
    ⟨(stalkPullbackSheafIso k i G x).inv g, by
      rw [← ConcreteCategory.comp_apply, Iso.inv_hom_id, ConcreteCategory.id_apply]⟩
  obtain ⟨t, rfl⟩ := hW g₀
  refine ⟨((TopCat.Sheaf.pullback (ModuleCat.{0} k) i).obj G).presheaf.map (homOfLE hVW).op
    (((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} k) i).unit.app G).hom.app
      (op W) t), ?_⟩
  rw [stalkPullbackSheafIso_unit k i G W x (hVW hx) t]
  exact TopCat.Presheaf.germ_res_apply _ (homOfLE hVW) x hx _

/-- **Inverse images of germ-surjective sheaves are germ-surjective.** For any continuous
`i : K ⟶ X` and a germ-surjective sheaf `G` of `k`-modules on `X`, the inverse image `i⁻¹ G` is
germ-surjective. -/
theorem germSurjective_pullback {K X : TopCat.{0}} (i : K ⟶ X) {G : X.Sheaf (ModuleCat.{0} k)}
    (hG : GermSurjective k G) :
    GermSurjective k ((TopCat.Sheaf.pullback (ModuleCat.{0} k) i).obj G) :=
  fun _ x hx => germ_pullback_surjective i G hx (W := ⊤) (fun _ _ => trivial) (hG ⊤ (i x) trivial)

/-- **Inverse images of flasque sheaves are germ-surjective.** For any continuous `i : K ⟶ X` and
a flasque sheaf `I` of `k`-modules on `X`, the inverse image `i⁻¹ I` is germ-surjective. -/
theorem germSurjective_pullback_of_isFlasque {K X : TopCat.{0}} (i : K ⟶ X)
    (I : X.Sheaf (ModuleCat.{0} k)) [TopCat.Sheaf.IsFlasque I] :
    GermSurjective k ((TopCat.Sheaf.pullback (ModuleCat.{0} k) i).obj I) :=
  germSurjective_pullback i (germSurjective_of_isFlasque k I)

/-- A sheaf `Z` with `𝟙 Z = p₁ ≫ i₁ + p₂ ≫ i₂` for maps through germ-surjective sheaves `A₁` and
`A₂` is germ-surjective. -/
theorem germSurjective_of_id_eq_add {X : TopCat.{0}} {Z A₁ A₂ : X.Sheaf (ModuleCat.{0} k)}
    (p₁ : Z ⟶ A₁) (i₁ : A₁ ⟶ Z) (p₂ : Z ⟶ A₂) (i₂ : A₂ ⟶ Z) (h₁ : GermSurjective k A₁)
    (h₂ : GermSurjective k A₂) (h : p₁ ≫ i₁ + p₂ ≫ i₂ = 𝟙 Z) : GermSurjective k Z := by
  intro V x hx g
  obtain ⟨W, hxW, z, rfl⟩ := TopCat.Presheaf.exists_germ_eq Z.presheaf g
  obtain ⟨a₁, ha₁⟩ := h₁ V x hx (A₁.presheaf.germ W x hxW (p₁.hom.app _ z))
  obtain ⟨a₂, ha₂⟩ := h₂ V x hx (A₂.presheaf.germ W x hxW (p₂.hom.app _ z))
  have hz : i₁.hom.app _ (p₁.hom.app _ z) + i₂.hom.app _ (p₂.hom.app _ z) = z := by
    have h' := congrArg (fun φ : Z ⟶ Z => φ.hom.app (op W) z) h
    simp at h'
    exact h'
  refine ⟨i₁.hom.app _ a₁ + i₂.hom.app _ a₂, ?_⟩
  rw [map_add, ← TopCat.Presheaf.stalkFunctor_map_germ_apply V x hx i₁.hom a₁,
    ← TopCat.Presheaf.stalkFunctor_map_germ_apply V x hx i₂.hom a₂, ha₁, ha₂,
    TopCat.Presheaf.stalkFunctor_map_germ_apply, TopCat.Presheaf.stalkFunctor_map_germ_apply,
    ← map_add, hz]

end germ

section Icc

variable {u v : ℝ}

/-- **Global sections on a compact interval, germ-surjective kernel.** On `[u, v]`, the direct
image to the point keeps a short exact sequence of sheaves of `k`-modules with germ-surjective
first term short exact. -/
theorem pushforward_toPt_shortExact_Icc
    {S : ShortComplex ((TopCat.of (Set.Icc u v)).Sheaf (ModuleCat.{0} k))} (hS : S.ShortExact)
    (h₁ : GermSurjective k S.X₁) :
    (S.map (TopCat.Sheaf.pushforward (ModuleCat.{0} k)
      (toPt (TopCat.of (Set.Icc u v))))).ShortExact := by
  let F := TopCat.Sheaf.pushforward (ModuleCat.{0} k) (toPt (TopCat.of (Set.Icc u v)))
  have key : PreservesFiniteLimits F → ∀ S : ShortComplex
      ((TopCat.of (Set.Icc u v)).Sheaf (ModuleCat.{0} k)),
      S.ShortExact → (S.map F).Exact ∧ Mono (F.map S.f) :=
    ((Functor.preservesFiniteLimits_tfae F).out 4 1).1
  have h := key (preservesFiniteLimits_pushforward _) S hS
  refine ShortComplex.ShortExact.mk' h.1 h.2 ?_
  -- Global sections of `S.X₃` lift: `S.g` is locally surjective.
  have hloc := (TopCat.Sheaf.isLocallySurjective_iff_epi S.g).2 hS.epi_g
  have hsurj (s : S.X₃.presheaf.obj (op ⊤)) : ∃ t : S.X₂.presheaf.obj (op ⊤),
      S.g.hom.app _ t = s :=
    exists_section_lift_Icc k S hS.exact h₁ s (fun x => by
      obtain ⟨W, hWU, ⟨t, ht⟩, hxW⟩ :=
        (TopCat.Presheaf.isLocallySurjective_iff S.g.hom).1 hloc ⊤ s x trivial
      exact ⟨W, hxW, t, ht⟩)
  rw [← TopCat.Sheaf.isLocallySurjective_iff_epi, TopCat.Presheaf.isLocallySurjective_iff]
  intro U s p hp
  obtain rfl := eq_top_of_mem_pt hp
  obtain ⟨t, ht⟩ := hsurj s
  exact ⟨⊤, le_rfl, ⟨t, ht.trans (TopCat.Presheaf.restrict_self s).symm⟩, hp⟩

/-- **Germ-surjective sheaves form an acyclic class on a compact interval.** Germ-surjective
sheaves of `k`-modules on `[u, v]` form an acyclic class (`AcyclicClass`) for global sections,
the direct image `(toPt [u, v])_*` to the point. -/
theorem acyclicClass_germSurjective_Icc (u v : ℝ) :
    AcyclicClass (TopCat.Sheaf.pushforward (ModuleCat.{0} k) (toPt (TopCat.of (Set.Icc u v))))
      (GermSurjective k) where
  zero G hG := @germSurjective_of_isFlasque k _ _ G (isFlasque_of_isZero hG)
  quot S hS _ h₂ := have := hS.epi_g; germSurjective_of_epi k S.g h₂
  retract p₁ i₁ p₂ i₂ h₁ h₂ h := germSurjective_of_id_eq_add p₁ i₁ p₂ i₂ h₁ h₂ h
  shortExact _ hS h₁ := pushforward_toPt_shortExact_Icc hS h₁
  injective I _ := germSurjective_of_injective k I

/-- **Germ-surjective complexes compute cohomology on a compact interval.** For a bounded below
complex `K` of germ-surjective sheaves of `k`-modules on `[u, v]`, the comparison
`Γ([u, v]; K) ⟶ RΓ([u, v]; K)` in `D⁺(Sh pt)` is an isomorphism. -/
theorem isIso_rightDerivedFunctorPlusUnit_app_toPt_Icc_of_germSurjective
    [HasDerivedCategory ((TopCat.of (Set.Icc u v)).Sheaf (ModuleCat.{0} k))]
    [HasDerivedCategory (pt.Sheaf (ModuleCat.{0} k))]
    (K : CochainComplex.Plus ((TopCat.of (Set.Icc u v)).Sheaf (ModuleCat.{0} k)))
    (hK : ∀ n, GermSurjective k (K.obj.X n)) :
    IsIso ((TopCat.Sheaf.pushforward (ModuleCat.{0} k)
      (toPt (TopCat.of (Set.Icc u v)))).rightDerivedFunctorPlusUnit.app K) :=
  have := preservesFiniteLimits_pushforward (k := k) (toPt (TopCat.of (Set.Icc u v)))
  isIso_rightDerivedFunctorPlusUnit_app_of_acyclicClass (acyclicClass_germSurjective_Icc u v) K hK

/-- **Inverse images of flasque sheaves are acyclic on a compact interval.** For a flasque (for
instance injective) sheaf `I` of `k`-modules on any `X` and a continuous `ι : [u, v] ⟶ X`,
`Hⁱ([u, v]; ι⁻¹ I) = 0` for `1 ≤ i`. -/
theorem isZero_H_Icc_pullback_of_isFlasque {X : TopCat.{0}}
    [HasDerivedCategory ((TopCat.of (Set.Icc u v)).Sheaf (ModuleCat.{0} k))]
    [HasDerivedCategory (pt.Sheaf (ModuleCat.{0} k))]
    (ι : TopCat.of (Set.Icc u v) ⟶ X) (I : X.Sheaf (ModuleCat.{0} k))
    [TopCat.Sheaf.IsFlasque I] {i : ℤ} (hi : 1 ≤ i) :
    IsZero ((DerivedCategory.Plus.homologyFunctor _ i).obj
      ((pushforwardPlus k (toPt (TopCat.of (Set.Icc u v)))).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((TopCat.Sheaf.pullback (ModuleCat.{0} k) ι).obj I)))) :=
  isZero_H_Icc_of_germSurjective _ (germSurjective_pullback_of_isFlasque ι I) hi

/-- **The derived unit of a nonempty compact interval is an isomorphism.** For `u ≤ v`, the
derived unit `𝟭 ⟶ (toPt [u, v])⁻¹ ⋙ RΓ([u, v]; -)` of `D⁺(Sh pt)` is an isomorphism: every
`M ∈ D⁺(Sh pt)` is `RΓ([u, v]; -)` of the constant complex `(toPt [u, v])⁻¹ M`. On a complex `K`,
the unit `K ⟶ Γ([u, v]; constSh K)` is a termwise isomorphism (`isIso_unit_constSh_Icc`), and the
constant terms are germ-surjective, so they compute `RΓ([u, v]; -)`. -/
theorem isIso_derivedUnit_Icc
    [HasDerivedCategory ((TopCat.of (Set.Icc u v)).Sheaf (ModuleCat.{0} k))]
    [HasDerivedCategory (pt.Sheaf (ModuleCat.{0} k))] (huv : u ≤ v) :
    IsIso (derivedUnit k (toPt (TopCat.of (Set.Icc u v)))) := by
  let f := toPt (TopCat.of (Set.Icc u v))
  have := Localization.essSurj (DerivedCategory.Plus.Q (C := pt.Sheaf (ModuleCat.{0} k)))
    (CochainComplex.Plus.quasiIso _)
  have : IsIso (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} k) f).unit :=
    have := fun N => isIso_unit_constSh_Icc (k := k) huv N
    NatIso.isIso_of_isIso_app _
  have : IsIso (unitCochain k f) := by
    unfold unitCochain
    infer_instance
  rw [NatTrans.isIso_iff_isIso_app]
  intro M
  rw [← NatTrans.isIso_app_iff_of_iso _ (DerivedCategory.Plus.Q.objObjPreimageIso M),
    derivedUnit_app_Q]
  have := isIso_rightDerivedFunctorPlusUnit_app_toPt_Icc_of_germSurjective
    ((TopCat.Sheaf.pullback (ModuleCat.{0} k) f).mapCochainComplexPlus.obj
      (DerivedCategory.Plus.Q.objPreimage M))
    (fun n => germSurjective_constSh _ ((DerivedCategory.Plus.Q.objPreimage M).obj.X n))
  infer_instance

end Icc

end TDA.Sheaf
