import TDA.Reeb.QuotientThickeningAbsorption

/-!
# Absorption on all constructible ℝ-spaces

This module begins the point-set part of the absorption argument.  A closed window is detected
inside a slightly larger open window by the interval-component comparison and the clamp on a
cylinder presentation.  The level sets of a geometric thickening are precisely closed windows of
the original space.  Later blocks of this file package these facts into point-bijectivity of
`ℛ (T_ε q_X)`, the compact-to-Hausdorff homeomorphism, (H2) by transport, the functor
`thickeningQuotient`, and the isomorphisms `thickeningQuotientAbsorptionIso` and
`thickeningQuotientCompIso`.

The route bypasses DMP15-v1 Theorem 4.27, which asserts constructibility of `T_ε X` beyond graph
input; no such assertion is claimed here.  The statements in this file are library statements,
not attributions to that source.  See `docs/math/reeb-quotient-thickening-absorption.md`.
-/

open Set Topology CategoryTheory
open scoped NNReal

universe u

namespace TDA.Reeb

noncomputable section

open OpenInterval

namespace CriticalValues

/-- A closed interval has clamp data in a sufficiently small enlarged open interval. -/
theorem exists_clampData_Icc {n : ℕ} (S : CriticalValues n) {a b : ℝ} (hab : a ≤ b) :
    ∃ δ > 0, ∃ c : S.ClampData (ioo (a - δ) (b + δ)), c.lo = a ∧ c.hi = b := by
  have h : ∀ k : Fin (n + 1),
      ∀ᶠ δ in 𝓝[>] (0 : ℝ), S.value k ∈ Ioo (a - δ) (b + δ) →
        S.value k ∈ Icc a b := by
    intro k
    by_cases hka : S.value k < a
    · have hg : 0 < a - S.value k := sub_pos.mpr hka
      filter_upwards [Ioo_mem_nhdsGT hg] with δ hδ
      intro hmem
      exfalso
      linarith [hmem.1, hδ.2]
    · by_cases hkb : b < S.value k
      · have hg : 0 < S.value k - b := sub_pos.mpr hkb
        filter_upwards [Ioo_mem_nhdsGT hg] with δ hδ
        intro hmem
        exfalso
        linarith [hmem.2, hδ.2]
      · exact Filter.Eventually.of_forall (fun _ _ =>
          ⟨le_of_not_gt hka, le_of_not_gt hkb⟩)
  obtain ⟨δ, hδ, hpos⟩ := ((Filter.eventually_all.2 h).and self_mem_nhdsWithin).exists
  refine ⟨δ, hpos, ⟨a, b, hab, ?_, ?_⟩, rfl, rfl⟩
  · intro t ht
    constructor <;> linarith [hpos, ht.1, ht.2]
  · intro k hk
    exact hδ k hk

end CriticalValues

namespace CylinderPresentation

/-- Joining in an enlarged window implies joining in the closed clamped window for points already
in that closed window. -/
theorem joinedIn_Icc_of_joinedIn {n : ℕ} (S : CriticalValues n)
    (P : CylinderPresentation.{u} n) {a b δ : ℝ} (c : S.ClampData (ioo (a - δ) (b + δ)))
    (hlo : c.lo = a) (hhi : c.hi = b) {x x' : P.Realization S}
    (hx : P.height S x ∈ Icc a b) (hx' : P.height S x' ∈ Icc a b)
    (h : JoinedIn (P.height S ⁻¹' (ioo (a - δ) (b + δ) : Set ℝ)) x x') :
    JoinedIn (P.height S ⁻¹' Icc a b) x x' := by
  let γ : Path x x' :=
    { toFun := fun t => P.clampFamily c ⟨h.somePath t, h.somePath_mem t⟩ 1
      continuous_toFun := (P.continuous_clampFamily_one c).comp
        (h.somePath.continuous.subtype_mk _)
      source' := by
        simp only [Path.source]
        exact P.clampFamily_of_mem c _ (by rw [hlo, hhi]; exact hx) 1
      target' := by
        simp only [Path.target]
        exact P.clampFamily_of_mem c _ (by rw [hlo, hhi]; exact hx') 1 }
  refine ⟨γ, fun t => ?_⟩
  have hm := P.clampFamily_one_mem_Icc c ⟨h.somePath t, h.somePath_mem t⟩
  rw [hlo, hhi] at hm
  exact hm

end CylinderPresentation

namespace GeometricThickening

/-- Reeb-related points in a thickening have equal thickened height and their base points are
joined in the corresponding closed window. -/
theorem reebRel_height_iff {X : Type*} [TopologicalSpace X] (f : C(X, ℝ))
    (ε : ℝ≥0) (z z' : X × Band ε) :
    ReebRel (height f ε) z z' ↔ height f ε z' = height f ε z ∧
      JoinedIn (f ⁻¹' Icc (height f ε z - ε) (height f ε z + ε)) z.1 z'.1 := by
  constructor
  · rintro ⟨γ, hγ⟩
    refine ⟨by simpa using hγ 1, ⟨γ.map continuous_fst, ?_⟩⟩
    intro t
    have hb : height f ε (γ t) - ε ≤ f (γ t).1 ∧
        f (γ t).1 ≤ height f ε (γ t) + ε := band_bounds f (γ t).1 (γ t).2
    rw [hγ t] at hb
    exact hb
  · rintro ⟨hz', hjoin⟩
    let t : ℝ := height f ε z
    let γ : Path z.1 z'.1 := hjoin.somePath
    have hmem : ∀ s : unitInterval, f (γ s) ∈ Icc (t - ε) (t + ε) := by
      intro s
      exact hjoin.somePath_mem s
    let γ' : Path z z' := {
      toFun := fun s =>
        (γ s, ⟨t - f (γ s), sub_mem_band f (hmem s)⟩)
      continuous_toFun := γ.continuous.prodMk
        ((continuous_const.sub (f.continuous.comp γ.continuous)).subtype_mk _)
      source' := by
        apply Prod.ext
        · exact γ.source
        · apply Subtype.ext
          dsimp only [Prod.snd, Subtype.coe_mk]
          rw [γ.source]
          dsimp [t]
          ring
      target' := by
        apply Prod.ext
        · exact γ.target
        · apply Subtype.ext
          dsimp only [Prod.snd, Subtype.coe_mk]
          rw [γ.target]
          dsimp [t]
          have e : f z'.1 + (z'.2 : ℝ) = f z.1 + z.2 := hz'
          linarith }
    refine ⟨γ', ?_⟩
    intro s
    change f (γ s) + (t - f (γ s)) = height f ε z
    dsimp [t]
    ring

end GeometricThickening

namespace RGraph

open OpenInterval

local notation "ℛ" => ReebQuotient.quotientFunctor ℝ

/-- On a constructible space, joining in a closed window of its Reeb quotient lifts to joining in
the same closed window of the original space. -/
theorem joinedIn_Icc_of_isConstructibleSpace {X : Over (TopCat.of ℝ)}
    (hX : IsConstructibleSpace X) {a b : ℝ} (hab : a ≤ b) {x x' : X.left}
    (hx : overBaseMap X x ∈ Icc a b) (hx' : overBaseMap X x' ∈ Icc a b)
    (h : JoinedIn (overBaseMap ((ℛ).obj X) ⁻¹' Icc a b)
      (ReebQuotient.mk (overBaseMap X) x) (ReebQuotient.mk (overBaseMap X) x')) :
    JoinedIn (overBaseMap X ⁻¹' Icc a b) x x' := by
  obtain ⟨n, S, P, h1, h2, h3, h4, ⟨i⟩⟩ := hX
  have := h1
  have := h2
  have := h3
  have := h4
  obtain ⟨δ, hδ, c, hlo, hhi⟩ := S.exists_clampData_Icc hab
  let J : OpenInterval := ioo (a - δ) (b + δ)
  have hxP : P.height S (i.hom.left.hom x) ∈ Icc a b := by
    have e : P.height S (i.hom.left.hom x) = overBaseMap X x :=
      overBaseMap_comm i.hom x
    exact e.symm ▸ hx
  have hxP' : P.height S (i.hom.left.hom x') ∈ Icc a b := by
    have e : P.height S (i.hom.left.hom x') = overBaseMap X x' :=
      overBaseMap_comm i.hom x'
    exact e.symm ▸ hx'
  have hmap := h.map (((ℛ).map i.hom).left.hom.continuous)
  have hP : JoinedIn
      (overBaseMap ((ℛ).obj (Over.mk (TopCat.ofHom (P.height S)))) ⁻¹' Icc a b)
      (ReebQuotient.mk (P.height S) (i.hom.left.hom x))
      (ReebQuotient.mk (P.height S) (i.hom.left.hom x')) := by
    apply (hmap.mono ?_)
    rintro q ⟨q₀, hq₀, rfl⟩
    change overBaseMap ((ℛ).obj (Over.mk (TopCat.ofHom (P.height S))))
      (((ℛ).map i.hom).left.hom q₀) ∈ Icc a b
    rw [overBaseMap_comm ((ℛ).map i.hom) q₀]
    exact hq₀
  have hJ : JoinedIn
      (overBaseMap ((ℛ).obj (Over.mk (TopCat.ofHom (P.height S)))) ⁻¹' (J : Set ℝ))
      (ReebQuotient.mk (P.height S) (i.hom.left.hom x))
      (ReebQuotient.mk (P.height S) (i.hom.left.hom x')) := by
    have hsub : Icc a b ⊆ (J : Set ℝ) := by
      intro t ht
      constructor <;> linarith [hδ, ht.1, ht.2]
    exact hP.mono (fun q hq => hsub hq)
  have hxJ : P.height S (i.hom.left.hom x) ∈ (J : Set ℝ) := by
    have hsub : Icc a b ⊆ (J : Set ℝ) := by
      intro t ht
      constructor <;> linarith [hδ, ht.1, ht.2]
    exact hsub hxP
  have hxJ' : P.height S (i.hom.left.hom x') ∈ (J : Set ℝ) := by
    have hsub : Icc a b ⊆ (J : Set ℝ) := by
      intro t ht
      constructor <;> linarith [hδ, ht.1, ht.2]
    exact hsub hxP'
  have hQcomp :
      ZerothHomotopy.mk
          (⟨ReebQuotient.mk (P.height S) (i.hom.left.hom x), hJ.source_mem⟩ :
            {q : ReebQuotient (P.height S) //
              ReebQuotient.height (P.height S) q ∈ OpenInterval.toOpens J}) =
        ZerothHomotopy.mk
          (⟨ReebQuotient.mk (P.height S) (i.hom.left.hom x'), hJ.target_mem⟩ :
            {q : ReebQuotient (P.height S) //
              ReebQuotient.height (P.height S) q ∈ OpenInterval.toOpens J}) :=
    ZerothHomotopy.sound hJ.joined_subtype.somePath
  have hPconstructible : IsConstructibleSpace (Over.mk (TopCat.ofHom (P.height S))) :=
    ⟨n, S, P, h1, h2, h3, h4, ⟨Iso.refl _⟩⟩
  have hκinj :=
    (bijective_intervalComponentComparison_app_of_constructible hPconstructible J).1
  have hPcomp :
      ZerothHomotopy.mk
          (⟨i.hom.left.hom x, hxJ⟩ :
            {y : P.Realization S //
              overBaseMap (Over.mk (TopCat.ofHom (P.height S))) y ∈
                OpenInterval.toOpens J}) =
        ZerothHomotopy.mk
          (⟨i.hom.left.hom x', hxJ'⟩ :
            {y : P.Realization S //
              overBaseMap (Over.mk (TopCat.ofHom (P.height S))) y ∈
                OpenInterval.toOpens J}) := by
    apply hκinj
    exact
      (ReebQuotient.intervalComponentComparison_app_mk
        (overBaseMap (Over.mk (TopCat.ofHom (P.height S)))) J
        ⟨i.hom.left.hom x, hxJ⟩).trans
        (hQcomp.trans
          (ReebQuotient.intervalComponentComparison_app_mk
            (overBaseMap (Over.mk (TopCat.ofHom (P.height S)))) J
            ⟨i.hom.left.hom x', hxJ'⟩).symm)
  have hJ' : JoinedIn (P.height S ⁻¹' (J : Set ℝ))
      (i.hom.left.hom x) (i.hom.left.hom x') :=
    (joinedIn_iff_joined (F := P.height S ⁻¹' (J : Set ℝ)) hxJ hxJ').2
      (Quotient.exact hPcomp)
  have hPclosed := CylinderPresentation.joinedIn_Icc_of_joinedIn S P c hlo hhi
    hxP hxP' hJ'
  have hback := hPclosed.map i.inv.left.hom.continuous
  have hback' : JoinedIn (overBaseMap X ⁻¹' Icc a b)
      (i.inv.left.hom (i.hom.left.hom x))
      (i.inv.left.hom (i.hom.left.hom x')) := by
    apply hback.mono
    rintro y ⟨y₀, hy₀, rfl⟩
    change overBaseMap X (i.inv.left.hom y₀) ∈ Icc a b
    have e : overBaseMap X (i.inv.left.hom y₀) = P.height S y₀ :=
      overBaseMap_comm i.inv y₀
    exact e.symm ▸ hy₀
  have hinv (y : X.left) : i.inv.left.hom (i.hom.left.hom y) = y :=
    congrArg (fun φ => φ.left.hom y) i.hom_inv_id
  rw [hinv x, hinv x'] at hback'
  exact hback'

/-! ### Point bijectivity and the homeomorphism -/

/-- The Reeb quotient of a thickened projection is bijective on points for a constructible space. -/
theorem bijective_quotientFunctor_map_functor_map_projNatTrans_app {X : Over (TopCat.of ℝ)}
    (hX : IsConstructibleSpace X) (ε : ℝ≥0) :
    Function.Bijective (((ℛ).map ((GeometricThickening.functor ε).map
      ((ReebQuotient.projNatTrans ℝ).app X))).left.hom) := by
  constructor
  · intro q q' h
    induction q using ReebQuotient.ind with
    | h z =>
      induction q' using ReebQuotient.ind with
      | h z' =>
        rcases z with ⟨x, t⟩
        rcases z' with ⟨x', t'⟩
        change ReebQuotient.mk _ (ReebQuotient.mk _ x, t) =
          ReebQuotient.mk _ (ReebQuotient.mk _ x', t') at h
        have hrelQ :
            ReebRel (GeometricThickening.height (overBaseMap ((ℛ).obj X)) ε)
              (ReebQuotient.mk (overBaseMap X) x, t)
              (ReebQuotient.mk (overBaseMap X) x', t') :=
          (ReebQuotient.mk_eq_mk_iff _).1 h
        have hheight := (GeometricThickening.reebRel_height_iff
          (overBaseMap ((ℛ).obj X)) ε
          (ReebQuotient.mk (overBaseMap X) x, t)
          (ReebQuotient.mk (overBaseMap X) x', t')).1 hrelQ
        have hx : overBaseMap X x ∈ Icc
            (GeometricThickening.height (overBaseMap ((ℛ).obj X)) ε
              (ReebQuotient.mk (overBaseMap X) x, t) - ε)
            (GeometricThickening.height (overBaseMap ((ℛ).obj X)) ε
              (ReebQuotient.mk (overBaseMap X) x, t) + ε) := by
          change (overBaseMap X x + t) - ε ≤ overBaseMap X x ∧
            overBaseMap X x ≤ (overBaseMap X x + t) + ε
          exact GeometricThickening.band_bounds (overBaseMap X) x t
        have hx' : overBaseMap X x' ∈ Icc
            (GeometricThickening.height (overBaseMap ((ℛ).obj X)) ε
              (ReebQuotient.mk (overBaseMap X) x, t) - ε)
            (GeometricThickening.height (overBaseMap ((ℛ).obj X)) ε
              (ReebQuotient.mk (overBaseMap X) x, t) + ε) := by
          have heq : overBaseMap X x' + t' = overBaseMap X x + t := by
            exact hheight.1
          change (overBaseMap X x + t) - ε ≤ overBaseMap X x' ∧
            overBaseMap X x' ≤ (overBaseMap X x + t) + ε
          rw [← heq]
          exact GeometricThickening.band_bounds (overBaseMap X) x' t'
        have hab :
            GeometricThickening.height (overBaseMap ((ℛ).obj X)) ε
                (ReebQuotient.mk (overBaseMap X) x, t) - ε ≤
              GeometricThickening.height (overBaseMap ((ℛ).obj X)) ε
                (ReebQuotient.mk (overBaseMap X) x, t) + ε := by
          linarith [ε.coe_nonneg]
        have hjoinX := joinedIn_Icc_of_isConstructibleSpace hX hab hx hx' hheight.2
        have hrelX : ReebRel (GeometricThickening.height (overBaseMap X) ε) (x, t) (x', t') := by
          apply (GeometricThickening.reebRel_height_iff (overBaseMap X) ε (x, t) (x', t')).2
          exact ⟨by
            exact hheight.1,
            by
              exact hjoinX⟩
        change ReebQuotient.mk (GeometricThickening.height (overBaseMap X) ε) (x, t) =
          ReebQuotient.mk (GeometricThickening.height (overBaseMap X) ε) (x', t')
        exact (ReebQuotient.mk_eq_mk_iff _).2 hrelX
  · intro q
    obtain ⟨⟨p, s⟩, rfl⟩ := ReebQuotient.mk_surjective _ q
    obtain ⟨x, rfl⟩ := ReebQuotient.mk_surjective (overBaseMap X) p
    exact ⟨ReebQuotient.mk _ (x, s), rfl⟩

/-! ### Compactness and separation for the homeomorphism -/

/-- The Reeb quotient of a thickening of a constructible space is compact. -/
theorem compactSpace_quotient_thickening {X : Over (TopCat.of ℝ)}
    (hX : IsConstructibleSpace X) (ε : ℝ≥0) :
    CompactSpace (ReebQuotient (GeometricThickening.height (overBaseMap X) ε)) := by
  obtain ⟨n, S, P, h1, h2, h3, h4, ⟨i⟩⟩ := hX
  have := h1
  have := h3
  have : CompactSpace (P.Realization S) := P.compactSpace S
  let e : X.left ≃ₜ P.Realization S := TopCat.homeoOfIso ((Over.forget _).mapIso i)
  have : CompactSpace X.left := e.symm.compactSpace
  have : CompactSpace (X.left × GeometricThickening.Band ε) := inferInstance
  exact (ReebQuotient.mk_surjective _).compactSpace (ReebQuotient.continuous_mk _)

/-- The Reeb quotient of the thickening of a constructible quotient is Hausdorff. -/
theorem t2Space_quotient_thickening_quotient {X : Over (TopCat.of ℝ)}
    (hX : IsConstructibleSpace X) (ε : ℝ≥0) :
    T2Space (ReebQuotient
      (GeometricThickening.height (overBaseMap ((ℛ).obj X)) ε)) := by
  obtain ⟨m, T, D, ⟨i⟩⟩ :=
    isRGraph_quotient_of_isConstructibleSpace
      (isConstructibleSpace_thickening (isRGraph_quotient_of_isConstructibleSpace hX) ε)
  have : T2Space ((CylinderPresentation.ofFiniteData D).Realization T) :=
    CylinderPresentation.finiteData_t2Space T D
  let e : ReebQuotient
      (GeometricThickening.height (overBaseMap ((ℛ).obj X)) ε) ≃ₜ
      (CylinderPresentation.ofFiniteData D).Realization T :=
    TopCat.homeoOfIso ((Over.forget _).mapIso i)
  exact e.isEmbedding.t2Space

/-- The absorption map is a homeomorphism of the underlying spaces. -/
noncomputable def absorptionHomeomorph {X : Over (TopCat.of ℝ)}
    (hX : IsConstructibleSpace X) (ε : ℝ≥0) :
    ReebQuotient (GeometricThickening.height (overBaseMap X) ε) ≃ₜ
      ReebQuotient (GeometricThickening.height (overBaseMap ((ℛ).obj X)) ε) :=
  haveI := compactSpace_quotient_thickening hX ε
  haveI := t2Space_quotient_thickening_quotient hX ε
  (((ℛ).map ((GeometricThickening.functor ε).map
      ((ReebQuotient.projNatTrans ℝ).app X))).left.hom.continuous).homeoOfEquivCompactToT2
    (f := Equiv.ofBijective _
      (bijective_quotientFunctor_map_functor_map_projNatTrans_app hX ε))

theorem absorptionHomeomorph_apply {X : Over (TopCat.of ℝ)}
    (hX : IsConstructibleSpace X) (ε : ℝ≥0)
    (q : ReebQuotient (GeometricThickening.height (overBaseMap X) ε)) :
    absorptionHomeomorph hX ε q =
      ((ℛ).map ((GeometricThickening.functor ε).map
        ((ReebQuotient.projNatTrans ℝ).app X))).left.hom q := rfl

/-- The absorption map is a homeomorphism of the underlying spaces, packaged over `ℝ`. -/
noncomputable def absorptionOverIso {X : Over (TopCat.of ℝ)}
    (hX : IsConstructibleSpace X) (ε : ℝ≥0) :
    (ℛ).obj ((GeometricThickening.functor ε).obj X) ≅
      (ℛ).obj ((GeometricThickening.functor ε).obj ((ℛ).obj X)) :=
  haveI := compactSpace_quotient_thickening hX ε
  haveI := t2Space_quotient_thickening_quotient hX ε
  Over.isoMk (TopCat.isoOfHomeo (absorptionHomeomorph hX ε))
    (by
      ext q
      exact overBaseMap_comm
        ((ℛ).map ((GeometricThickening.functor ε).map
          ((ReebQuotient.projNatTrans ℝ).app X))) q)

/-- The forward map of `absorptionOverIso` is the Reeb-quotient of the thickened projection. -/
theorem absorptionOverIso_hom {X : Over (TopCat.of ℝ)} (hX : IsConstructibleSpace X)
    (ε : ℝ≥0) :
    (absorptionOverIso hX ε).hom =
      (ℛ).map ((GeometricThickening.functor ε).map
        ((ReebQuotient.projNatTrans ℝ).app X)) := by
  exact Over.OverMorphism.ext (by
    ext q
    rfl)

/-- The absorption map sends `[(x, t)]` to `[([x], t)]`. -/
theorem absorptionOverIso_hom_left_mk {X : Over (TopCat.of ℝ)}
    (hX : IsConstructibleSpace X) (ε : ℝ≥0) (x : X.left)
    (t : GeometricThickening.Band ε) :
    (absorptionOverIso hX ε).hom.left.hom
        (ReebQuotient.mk _ (x, t)) =
      ReebQuotient.mk _ (ReebQuotient.mk (overBaseMap X) x, t) := by
  rfl

/-- The Reeb quotient of a thickening of a constructible space is a graph object. -/
theorem isRGraph_quotient_thickening_of_isConstructibleSpace {X : Over (TopCat.of ℝ)}
    (hX : IsConstructibleSpace X) (ε : ℝ≥0) :
    IsRGraph ((ℛ).obj ((GeometricThickening.functor ε).obj X)) := by
  obtain ⟨m, T, D, ⟨i⟩⟩ :=
    isRGraph_quotient_of_isConstructibleSpace
      (isConstructibleSpace_thickening (isRGraph_quotient_of_isConstructibleSpace hX) ε)
  exact ⟨m, T, D, ⟨absorptionOverIso hX ε ≪≫ i⟩⟩

/-! ### Absorption on constructible ℝ-spaces -/

/-- The absorption map is an isomorphism for every constructible input. -/
instance isIso_quotientFunctor_map_functor_map_projNatTrans_app_constructible
    (X : ConstructibleSpaceCat) (ε : ℝ≥0) :
    IsIso ((ℛ).map ((GeometricThickening.functor ε).map
      ((ReebQuotient.projNatTrans ℝ).app X.obj))) := by
  rw [← absorptionOverIso_hom X.property ε]
  infer_instance

/-- The thickening-then-quotient functor on constructible ℝ-spaces. -/
def thickeningQuotient (ε : ℝ≥0) : ConstructibleSpaceCat ⥤ RGraphCat :=
  IsRGraph.lift (IsConstructibleSpace.ι ⋙ GeometricThickening.functor ε ⋙ ℛ)
    fun X => isRGraph_quotient_thickening_of_isConstructibleSpace X.property ε

/-- The inclusion of `thickeningQuotient` is the actual thickening followed by the Reeb quotient. -/
theorem thickeningQuotient_comp_ι (ε : ℝ≥0) :
    thickeningQuotient ε ⋙ IsRGraph.ι =
      IsConstructibleSpace.ι ⋙ GeometricThickening.functor ε ⋙ ℛ :=
  rfl

/-- `ℛ T_ε ≅ U_ε ℛ` on constructible ℝ-spaces; components `ℛ (T_ε q_X)`. -/
def thickeningQuotientAbsorptionIso (ε : ℝ≥0) :
    thickeningQuotient ε ≅ quotientRGraphFunctor ⋙ geometricSmoothing ε :=
  NatIso.ofComponents
    (fun X => ObjectProperty.isoMk _ (absorptionOverIso X.property ε))
    (fun φ => by
      ext1
      change (ℛ).map ((GeometricThickening.functor ε).map φ.hom) ≫
          (absorptionOverIso _ ε).hom =
        (absorptionOverIso _ ε).hom ≫
          (ℛ).map ((GeometricThickening.functor ε).map ((ℛ).map φ.hom))
      rw [absorptionOverIso_hom, absorptionOverIso_hom]
      exact (Functor.whiskerRight (Functor.whiskerRight (ReebQuotient.projNatTrans ℝ)
        (GeometricThickening.functor ε)) ℛ).naturality φ.hom)

/-- The component of the constructible absorption is the pointwise absorption map. -/
theorem thickeningQuotientAbsorptionIso_hom_app_hom (ε : ℝ≥0) (X : ConstructibleSpaceCat) :
    ((thickeningQuotientAbsorptionIso ε).hom.app X).hom =
      (ℛ).map ((GeometricThickening.functor ε).map
        ((ReebQuotient.projNatTrans ℝ).app X.obj)) :=
  absorptionOverIso_hom X.property ε

/-! ### The composite law -/

/-- `U_ε (ℛ T_δ X) ≅ ℛ T_(ε+δ) X` on constructible ℝ-spaces. -/
def thickeningQuotientCompIso (ε δ : ℝ≥0) :
    thickeningQuotient δ ⋙ geometricSmoothing ε ≅ thickeningQuotient (ε + δ) :=
  Functor.isoWhiskerRight (thickeningQuotientAbsorptionIso δ) (geometricSmoothing ε) ≪≫
    Functor.associator quotientRGraphFunctor (geometricSmoothing δ)
      (geometricSmoothing ε) ≪≫
    Functor.isoWhiskerLeft quotientRGraphFunctor (geometricSmoothingCompIso ε δ) ≪≫
    (thickeningQuotientAbsorptionIso (ε + δ)).symm

end RGraph

end
end TDA.Reeb
