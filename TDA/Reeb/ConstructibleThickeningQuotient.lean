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

end RGraph

end
end TDA.Reeb
