import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.Order.IntermediateValue
import TDA.Sheaf.IntervalSections
import TDA.Sheaf.PointSheaf
import TDA.Sheaf.RightDerivedHomology

/-!
# Cohomology of compact intervals

Let `k` be a ring and `[u, v]` the compact interval `TopCat.of (Set.Icc u v)`. Its cohomology
with coefficients in a sheaf `G` of `k`-modules is read through the derived direct image
`pushforwardPlus k (toPt _)` to the point: `Hⁱ([u, v]; G)` is the `i`-th homology, a sheaf of
`k`-modules on `pt`, of `pushforwardPlus` applied to `G` placed in degree `0`.

* `isZero_H_Icc`: `Hⁱ([u, v]; G) = 0` for `2 ≤ i`, every sheaf `G` and all `u`, `v`.
* `isIso_unit_constSh_Icc`: for `u ≤ v`, the adjunction unit `N ⟶ (toPt _)_* constSh N` is an
  isomorphism; this is the underived `H⁰` of a constant sheaf on a connected space.
* `isZero_H_constSh_Icc`: `Hⁱ([u, v]; constSh N) = 0` for `1 ≤ i`.
* `isIso_derivedUnit_toPt_Icc`: for `u ≤ v`, the derived unit `N ⟶ RΓ([u, v]; constSh N)` is an
  isomorphism in `D⁺(Sh pt)`, for every sheaf `N` of `k`-modules on the point.

The proofs read `Hⁱ` off an injective resolution `G ⟶ J` (`homologyRightDerivedIsoOfQuasiIso`).
Global sections of `J` on `[u, v]` are exact in degree `n ≥ 1` (`sections_exact_Icc`): `J` is
exact there, and the sheaf mapping onto the kernel of `Jⁿ⁻¹ ⟶ Jⁿ` is germ-surjective. For
`n ≥ 2` it is `Jⁿ⁻²`, which is injective (`germSurjective_of_injective`); for `n = 1` it is `G`
itself, which is germ-surjective when `G` is constant (`germSurjective_constSh`). Exactness on the point is read on global sections
(`exact_of_sections_top`). For `H⁰`, a global section of `constSh N` has locally constant, hence
constant, germs on the connected interval.
-/

noncomputable section
open CategoryTheory Limits TopologicalSpace Opposite

namespace TDA.Sheaf

variable {k : Type} [Ring k]

/-- **`H⁰` of a constant sheaf, underived.** On a nonempty compact interval, the unit
`N ⟶ (toPt _)_* (toPt _)⁻¹ N` of the inverse and direct image adjunction is an isomorphism. -/
theorem isIso_unit_constSh_Icc {u v : ℝ} (huv : u ≤ v) (N : pt.Sheaf (ModuleCat.{0} k)) :
    IsIso ((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} k)
      (toPt (TopCat.of (Set.Icc u v)))).unit.app N) := by
  let I := TopCat.of (Set.Icc u v)
  let η := (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} k) (toPt I)).unit.app N
  let e := fun x : I => stalkPullbackSheafIso k (toPt I) N x
  have inj (x : I) : Function.Injective (e x).hom := fun a b h => by
    rw [← Iso.hom_inv_id_apply (e x) a, h, Iso.hom_inv_id_apply]
  have key (x : I) (n : N.presheaf.obj (op ⊤)) :
      (constSh k I N).presheaf.germ ((Opens.map (toPt I)).obj ⊤) x trivial
          (η.hom.app (op ⊤) n) =
        (e x).hom (N.presheaf.germ ⊤ (toPt I x) trivial n) :=
    (stalkPullbackSheafIso_unit k (toPt I) N ⊤ x trivial n).symm
  let x₀ : I := ⟨u, le_rfl, huv⟩
  apply isIso_of_bijective_app_top
  constructor
  · intro a b hab
    exact (germ_top_bijective N (toPt I x₀)).1
      (inj x₀ ((key x₀ a).symm.trans ((congrArg _ hab).trans (key x₀ b))))
  · intro σ
    have hc (x : I) : ∃ n : N.presheaf.obj (op ⊤),
        (constSh k I N).presheaf.germ ((Opens.map (toPt I)).obj ⊤) x trivial σ =
          (e x).hom (N.presheaf.germ ⊤ (toPt I x) trivial n) := by
      obtain ⟨n, hn⟩ := (germ_top_bijective N (toPt I x)).2
        ((e x).inv ((constSh k I N).presheaf.germ ((Opens.map (toPt I)).obj ⊤) x trivial σ))
      exact ⟨n, by rw [hn, Iso.inv_hom_id_apply]⟩
    choose c hc using hc
    -- The germs of `σ`, read in `N(⊤)`, are locally constant.
    have hloc : IsLocallyConstant c := by
      rw [IsLocallyConstant.iff_eventually_eq]
      intro x
      obtain ⟨W, hxW, i₁, i₂, he⟩ := TopCat.Presheaf.germ_eq (constSh k I N).presheaf
        (U := (Opens.map (toPt I)).obj ⊤) (V := (Opens.map (toPt I)).obj ⊤) x trivial trivial
        σ (η.hom.app (op ⊤) (c x)) ((hc x).trans (key x (c x)).symm)
      filter_upwards [W.isOpen.mem_nhds hxW] with y hy
      have h2 := (TopCat.Presheaf.germ_res_apply _ i₁ y hy σ).symm.trans
        ((congrArg _ he).trans (TopCat.Presheaf.germ_res_apply _ i₂ y hy _))
      exact (germ_top_bijective N (toPt I y)).1
        (inj y ((hc y).symm.trans (h2.trans (key y (c x)))))
    have : PreconnectedSpace I := Subtype.preconnectedSpace isPreconnected_Icc
    refine ⟨c x₀, TopCat.Presheaf.section_ext (constSh k I N) _ _ _ (fun x _ => ?_)⟩
    rw [hloc.apply_eq_of_preconnectedSpace x₀ x]
    exact (key x (c x)).trans (hc x).symm

/-- A left exact additive functor keeps a quasi-isomorphism in degree `0` from a complex
concentrated in degree `0` to a complex vanishing in degree `-1`. -/
private theorem quasiIsoAt_zero_map {C D : Type*} [Category* C] [Category* D] [Abelian C]
    [Abelian D] (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] {A B : CochainComplex C ℤ}
    (j : A ⟶ B) [QuasiIsoAt j 0] (hA₀ : IsZero (A.X (-1))) (hA₁ : IsZero (A.X 1))
    (hB : IsZero (B.X (-1))) : QuasiIsoAt ((F.mapHomologicalComplex _).map j) 0 := by
  have hq := (quasiIsoAt_iff' j (-1) 0 1 ((ComplexShape.up ℤ).prev_eq' (by norm_num))
    ((ComplexShape.up ℤ).next_eq' (by norm_num))).1 inferInstance
  rw [ShortComplex.quasiIso_iff_of_zeros _ (hA₀.eq_of_src _ _) (hA₁.eq_of_tgt _ _)
    (hB.eq_of_src _ _)] at hq
  rw [quasiIsoAt_iff' _ (-1) 0 1 ((ComplexShape.up ℤ).prev_eq' (by norm_num))
      ((ComplexShape.up ℤ).next_eq' (by norm_num)),
    ShortComplex.quasiIso_iff_of_zeros _ ((F.map_isZero hA₀).eq_of_src _ _)
      ((F.map_isZero hA₁).eq_of_tgt _ _) ((F.map_isZero hB).eq_of_src _ _)]
  have : Mono (j.f 0) := hq.2
  exact ⟨hq.1.map_of_mono_of_preservesKernel F hq.2 inferInstance, F.map_mono _⟩

/-- On `[u, v]`, a complex `J` exact at `n`, together with a germ-surjective `L₀ ⟶ Jᵐ` making
`L₀ ⟶ Jᵐ ⟶ Jⁿ` exact, has exact global sections at `n`. -/
private theorem exactAt_pushforward_toPt {u v : ℝ}
    (J : CochainComplex ((TopCat.of (Set.Icc u v)).Sheaf (ModuleCat.{0} k)) ℤ) {m n p : ℤ}
    (hmn : m + 1 = n) (hnp : n + 1 = p)
    {L₀ : (TopCat.of (Set.Icc u v)).Sheaf (ModuleCat.{0} k)} (d₀ : L₀ ⟶ J.X m)
    (w : d₀ ≫ J.d m n = 0) (h₀ : (ShortComplex.mk d₀ (J.d m n) w).Exact)
    (hL₀ : GermSurjective k L₀) (hJ : J.ExactAt n) :
    (((TopCat.Sheaf.pushforward (ModuleCat.{0} k)
      (toPt (TopCat.of (Set.Icc u v)))).mapHomologicalComplex _).obj J).ExactAt n := by
  rw [HomologicalComplex.exactAt_iff' _ m n p ((ComplexShape.up ℤ).prev_eq' hmn)
    ((ComplexShape.up ℤ).next_eq' hnp)] at hJ ⊢
  apply exact_of_sections_top
  intro s hs
  exact sections_exact_Icc k d₀ (J.d m n) (J.d n p) w (J.d_comp_d _ _ _) h₀ hJ hL₀ s hs

/-- Global sections on `[u, v]` of an injective resolution `j : A ⟶ J` of a complex `A`
concentrated in degree `0` are exact in degree `n ≥ 1`, provided `A⁰` is germ-surjective when
`n = 1`. -/
private theorem exactAt_pushforward_of_quasiIso {u v : ℝ}
    {A J : CochainComplex ((TopCat.of (Set.Icc u v)).Sheaf (ModuleCat.{0} k)) ℤ}
    (hA : ∀ m, m ≠ 0 → IsZero (A.X m)) [J.IsStrictlyGE 0] [∀ m, Injective (J.X m)]
    (j : A ⟶ J) [QuasiIso j] {n : ℤ} (hn : 1 ≤ n) (hg : n = 1 → GermSurjective k (A.X 0)) :
    (((TopCat.Sheaf.pushforward (ModuleCat.{0} k)
      (toPt (TopCat.of (Set.Icc u v)))).mapHomologicalComplex _).obj J).ExactAt n := by
  have hJ (m : ℤ) (hm : m ≠ 0) : J.ExactAt m :=
    (quasiIsoAt_iff_exactAt j m ((HomologicalComplex.exactAt_iff _ _).2
      (ShortComplex.exact_of_isZero_X₂ _ (hA m hm)))).1 inferInstance
  rcases eq_or_lt_of_le hn with rfl | hn2
  · have hq := (quasiIsoAt_iff' j (-1) 0 1
      ((ComplexShape.up ℤ).prev_eq' (by norm_num)) ((ComplexShape.up ℤ).next_eq' (by norm_num))).1
      inferInstance
    rw [ShortComplex.quasiIso_iff_of_zeros _ ((hA (-1) (by norm_num)).eq_of_src _ _)
      ((hA 1 one_ne_zero).eq_of_tgt _ _) ((J.isZero_of_isStrictlyGE 0 (-1)).eq_of_src _ _)] at hq
    exact exactAt_pushforward_toPt J (by norm_num) rfl (j.f 0)
      (by rw [j.comm, (hA 1 one_ne_zero).eq_of_tgt (A.d 0 1) 0, zero_comp]) hq.1 (hg rfl)
      (hJ 1 one_ne_zero)
  · have h₀ := (HomologicalComplex.exactAt_iff' J (n - 2) (n - 1) n
      ((ComplexShape.up ℤ).prev_eq' (show n - 2 + 1 = n - 1 by omega))
      ((ComplexShape.up ℤ).next_eq' (show n - 1 + 1 = n by omega))).1 (hJ (n - 1) (by omega))
    exact exactAt_pushforward_toPt J (m := n - 1) (by omega) rfl (J.d (n - 2) (n - 1))
      (J.d_comp_d _ _ _) h₀ (germSurjective_of_injective k _) (hJ n (by omega))

/-- Let `j : A ⟶ B` be a quasi-isomorphism to a bounded below complex of injective objects. A
morphism `u : X ⟶ F A` followed by the derived-functor comparison of `F` at `A` is invertible
in `D⁺` when `u ≫ F j` is a quasi-isomorphism. -/
private theorem isIso_Q_map_comp_rightDerivedFunctorPlusUnit {C D : Type*} [Category* C]
    [Category* D] [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D]
    [EnoughInjectives C] (F : C ⥤ D) [F.Additive] {X : CochainComplex.Plus D}
    {A B : CochainComplex.Plus C} (u : X ⟶ F.mapCochainComplexPlus.obj A) (j : A ⟶ B)
    (hj : CochainComplex.Plus.quasiIso C j) [∀ n, Injective (B.obj.X n)]
    (hψ : CochainComplex.Plus.quasiIso D (u ≫ F.mapCochainComplexPlus.map j)) :
    IsIso (DerivedCategory.Plus.Q.map u ≫ F.rightDerivedFunctorPlusUnit.app A) := by
  have : IsIso (DerivedCategory.Plus.Q.map j) :=
    Localization.inverts _ (CochainComplex.Plus.quasiIso _) j hj
  have : IsIso (DerivedCategory.Plus.Q.map (u ≫ F.mapCochainComplexPlus.map j)) :=
    Localization.inverts _ (CochainComplex.Plus.quasiIso _) _ hψ
  have := isIso_rightDerivedFunctorPlusUnit_app_of_injective F B
  have nat : DerivedCategory.Plus.Q.map (F.mapCochainComplexPlus.map j) ≫
      F.rightDerivedFunctorPlusUnit.app B =
      F.rightDerivedFunctorPlusUnit.app A ≫
        F.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map j) :=
    F.rightDerivedFunctorPlusUnit.naturality j
  have eq : DerivedCategory.Plus.Q.map u ≫ F.rightDerivedFunctorPlusUnit.app A =
      (DerivedCategory.Plus.Q.map (u ≫ F.mapCochainComplexPlus.map j) ≫
        F.rightDerivedFunctorPlusUnit.app B) ≫
          inv (F.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map j)) := by
    rw [IsIso.eq_comp_inv, Functor.map_comp, Category.assoc, Category.assoc, nat]
  rw [eq]
  infer_instance

section derived

variable [HasDerivedCategory (pt.Sheaf (ModuleCat.{0} k))]

/-- `Hⁱ([u, v]; G) = 0` for `1 ≤ i`, provided `G` is germ-surjective when `i = 1`. -/
private theorem isZero_H_Icc_aux {u v : ℝ}
    [HasDerivedCategory ((TopCat.of (Set.Icc u v)).Sheaf (ModuleCat.{0} k))]
    (G : (TopCat.of (Set.Icc u v)).Sheaf (ModuleCat.{0} k)) {i : ℤ} (hi : 1 ≤ i)
    (hg : i = 1 → GermSurjective k G) :
    IsZero ((DerivedCategory.Plus.homologyFunctor _ i).obj
      ((pushforwardPlus k (toPt (TopCat.of (Set.Icc u v)))).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj G))) := by
  obtain ⟨L, _, j, hj⟩ := CochainComplex.Plus.exists_quasiIso_injective (singlePlus 0 G) 0
  have : QuasiIso j.hom := hj
  have (m : ℤ) : Injective (((InjectiveObject.ι _).mapCochainComplexPlus.obj L).obj.X m) :=
    (L.obj.X m).property
  have : CochainComplex.IsStrictlyGE
      (((InjectiveObject.ι _).mapCochainComplexPlus.obj L).obj) 0 :=
    inferInstanceAs (CochainComplex.IsStrictlyGE
      (((InjectiveObject.ι _).mapHomologicalComplex _).obj L.obj) 0)
  refine IsZero.of_iso ?_ ((DerivedCategory.Plus.homologyFunctor _ i).mapIso
    ((pushforwardPlus k _).mapIso (singleFunctorIsoQ 0 G)) ≪≫
      homologyRightDerivedIsoOfQuasiIso _ j hj i)
  refine HomologicalComplex.ExactAt.isZero_homology ?_
  exact exactAt_pushforward_of_quasiIso
    (fun m hm => HomologicalComplex.isZero_single_obj_X _ _ _ _ hm) j.hom hi
    (fun h => germSurjective_of_epi k (HomologicalComplex.singleObjXSelf _ 0 G).inv (hg h))

/-- **Cohomological dimension of a compact interval.** For every sheaf `G` of `k`-modules on
`[u, v]`, `Hⁱ([u, v]; G) = 0` for `2 ≤ i`. No `u ≤ v` is needed. -/
theorem isZero_H_Icc {u v : ℝ}
    [HasDerivedCategory ((TopCat.of (Set.Icc u v)).Sheaf (ModuleCat.{0} k))]
    (G : (TopCat.of (Set.Icc u v)).Sheaf (ModuleCat.{0} k)) {i : ℤ} (hi : 2 ≤ i) :
    IsZero ((DerivedCategory.Plus.homologyFunctor _ i).obj
      ((pushforwardPlus k (toPt (TopCat.of (Set.Icc u v)))).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj G))) :=
  isZero_H_Icc_aux G (by omega) (fun h => absurd h (by omega))

/-- **Constant coefficients, vanishing.** `Hⁱ([u, v]; constSh N) = 0` for `1 ≤ i`, for all `u`,
`v`. -/
theorem isZero_H_constSh_Icc {u v : ℝ}
    [HasDerivedCategory ((TopCat.of (Set.Icc u v)).Sheaf (ModuleCat.{0} k))]
    (N : pt.Sheaf (ModuleCat.{0} k)) {i : ℤ} (hi : 1 ≤ i) :
    IsZero ((DerivedCategory.Plus.homologyFunctor _ i).obj
      ((pushforwardPlus k (toPt (TopCat.of (Set.Icc u v)))).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj (constSh k (TopCat.of (Set.Icc u v)) N)))) :=
  isZero_H_Icc_aux _ hi (fun _ => germSurjective_constSh _ N)

/-- **Constant coefficients, derived unit.** On a nonempty compact interval, the derived unit
`N ⟶ R(toPt _)_* (toPt _)⁻¹ N` is an isomorphism for every sheaf `N` of `k`-modules on the
point: `H⁰([u, v]; constSh N) = N` and `Hⁱ([u, v]; constSh N) = 0` for `i ≠ 0`. -/
theorem isIso_derivedUnit_toPt_Icc {u v : ℝ}
    [HasDerivedCategory ((TopCat.of (Set.Icc u v)).Sheaf (ModuleCat.{0} k))]
    (huv : u ≤ v) (N : pt.Sheaf (ModuleCat.{0} k)) :
    IsIso ((derivedUnit k (toPt (TopCat.of (Set.Icc u v)))).app
      ((DerivedCategory.Plus.singleFunctor _ 0).obj N)) := by
  let f := toPt (TopCat.of (Set.Icc u v))
  let F := TopCat.Sheaf.pushforward (ModuleCat.{0} k) f
  let K₀ : CochainComplex.Plus (pt.Sheaf (ModuleCat.{0} k)) := singlePlus 0 N
  let A := (TopCat.Sheaf.pullback (ModuleCat.{0} k) f).mapCochainComplexPlus.obj K₀
  let adj := TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} k) f
  rw [NatTrans.isIso_app_iff_of_iso _ (singleFunctorIsoQ 0 N), derivedUnit_app_Q]
  suffices h : IsIso (DerivedCategory.Plus.Q.map ((unitCochain k f).app K₀) ≫
      F.rightDerivedFunctorPlusUnit.app A) by
    rw [← Category.assoc]
    infer_instance
  have : CochainComplex.IsStrictlyGE A.obj 0 := inferInstanceAs (CochainComplex.IsStrictlyGE
    (((TopCat.Sheaf.pullback (ModuleCat.{0} k) f).mapHomologicalComplex _).obj K₀.obj) 0)
  obtain ⟨L, _, j, hj⟩ := CochainComplex.Plus.exists_quasiIso_injective A 0
  have : QuasiIso j.hom := hj
  let B := (InjectiveObject.ι _).mapCochainComplexPlus.obj L
  have : CochainComplex.IsStrictlyGE B.obj 0 := inferInstanceAs (CochainComplex.IsStrictlyGE
    (((InjectiveObject.ι _).mapHomologicalComplex _).obj L.obj) 0)
  have (m : ℤ) : Injective (B.obj.X m) := (L.obj.X m).property
  have := adj.rightAdjoint_preservesLimits
  -- `A` is `(toPt _)⁻¹ N` in degree `0`.
  have hA (m : ℤ) (hm : m ≠ 0) : IsZero (A.obj.X m) :=
    Functor.map_isZero _ (HomologicalComplex.isZero_single_obj_X _ _ _ _ hm)
  -- The unit `K₀ ⟶ f_* f⁻¹ K₀` is an isomorphism of complexes.
  have hu : CochainComplex.Plus.quasiIso _ ((unitCochain k f).app K₀) := by
    rw [CochainComplex.Plus.quasiIso_iff]
    have : IsIso ((unitCochain k f).app K₀).hom := by
      have (m : ℤ) : IsIso (((unitCochain k f).app K₀).hom.f m) := by
        rw [unitCochain_app_hom_f]
        by_cases hm : m = 0
        · subst hm
          exact (NatTrans.isIso_app_iff_of_iso _ (HomologicalComplex.singleObjXSelf _ 0 N)).2
            (isIso_unit_constSh_Icc huv N)
        · exact isIso_of_source_target_iso_zero _
            (HomologicalComplex.isZero_single_obj_X _ _ _ _ hm).isoZero
            ((Functor.map_isZero F (hA m hm)).isoZero)
      exact HomologicalComplex.Hom.isIso_of_components _
    infer_instance
  -- `f_* j : f_* f⁻¹ K₀ ⟶ f_* B` is a quasi-isomorphism.
  have hFj : CochainComplex.Plus.quasiIso _ (F.mapCochainComplexPlus.map j) := by
    rw [CochainComplex.Plus.quasiIso_iff, quasiIso_iff]
    intro n
    have hFA (m : ℤ) (hm : m ≠ 0) : ((F.mapCochainComplexPlus.obj A).obj).ExactAt m :=
      (HomologicalComplex.exactAt_iff _ _).2
        (ShortComplex.exact_of_isZero_X₂ _ (Functor.map_isZero F (hA m hm)))
    rcases lt_trichotomy n 0 with hn | rfl | hn
    · rw [quasiIsoAt_iff_exactAt _ n (hFA n hn.ne)]
      exact (HomologicalComplex.exactAt_iff _ _).2 (ShortComplex.exact_of_isZero_X₂ _
        (Functor.map_isZero F (B.obj.isZero_of_isStrictlyGE 0 n)))
    · exact quasiIsoAt_zero_map F j.hom (hA (-1) (by norm_num)) (hA 1 one_ne_zero)
        (B.obj.isZero_of_isStrictlyGE 0 (-1))
    · rw [quasiIsoAt_iff_exactAt _ n (hFA n hn.ne')]
      exact exactAt_pushforward_of_quasiIso hA j.hom (by omega) (fun _ =>
        germSurjective_of_epi k ((TopCat.Sheaf.pullback (ModuleCat.{0} k) f).map
          (HomologicalComplex.singleObjXSelf _ 0 N).inv) (germSurjective_constSh _ N))
  -- The composite `K₀ ⟶ f_* f⁻¹ K₀ ⟶ f_* B` is a quasi-isomorphism.
  have hψ := (CochainComplex.Plus.quasiIso _).comp_mem _ _ hu hFj
  exact isIso_Q_map_comp_rightDerivedFunctorPlusUnit F ((unitCochain k f).app K₀) j hj hψ

end derived

end TDA.Sheaf
