import TDA.Reeb.ComponentsHomotopy
import TDA.Reeb.IntervalComponents
import TDA.Reeb.Smoothing
import TDA.Reeb.RGraphCosheafEquivalence
import TDA.Reeb.ConstructibleComparison
import Mathlib.Topology.Order.ProjIcc

/-!
# Geometric thickening and its component comparison

The thickening `T_ε` of a space over `ℝ`, and the canonical comparison between the path
components of the thickening and the smoothing of the path components (de Silva–Munch–Patel,
*Categorified Reeb Graphs*, Definition 4.22, Observation 4.23, Theorem 4.24 and Lemma 4.25).

## The thickened space

For `f : C(X, ℝ)` and `ε : ℝ≥0`, the thickening is `X × Band ε` with `Band ε = [-ε, ε]` and height
`height f ε (x, t) = f x + t`.

* `map g ε (x, t) = (g x, t)` for every continuous `g`; it preserves height when `h ∘ g = f`
  (`height_map`), and `map_id`, `map_comp` hold by `rfl`.
* `zeroSection X ε : x ↦ (x, 0)` preserves height (`height_zeroSection`) and is natural
  (`map_comp_zeroSection`). Band enlargement `bandInclusion X hεδ` for `ε ≤ δ` preserves height.
* `bandHomeomorph f ε` identifies `X × Band ε` with `{(x, u) | u - ε ≤ f x ≤ u + ε}` by
  `(x, t) ↦ (x, f x + t)`, with inverse `(x, u) ↦ (x, u - f x)`; the thickened height becomes the
  second coordinate (`snd_bandHomeomorph`).

## Inverse images

For an open interval `I`, `preimageProjection f ε I : f_ε⁻¹ I → f⁻¹ (thicken ε I)` is the first
projection `(x, t) ↦ x`. It is a homotopy equivalence for every `I`, including `⊥`, rays and `⊤`,
and every `ε`, including `0`, with no hypothesis on `X` (`preimageHomotopyEquiv`); its forward map
is the projection by `rfl`. The homotopy inverse `x ↦ (x, clamp ε c (f x))` uses the clamp
`max (-ε) (min ε (c - s))` at a point `c ∈ I` (`add_clamp_mem`) and a straight-line homotopy in the
band coordinate. The point `c` is a choice (`intervalCenter`), and the inverse is not part of the
interface. The projection commutes on points with interval inclusions and with height-preserving
maps (`preimageProjection_comp_inclusion`, `preimageProjection_comp_restrict`). For `ε > 0` it
does not preserve height in general; only at `ε = 0` is the first projection height-preserving
(`zeroHomeomorph`).

## The comparison

```
componentComparison f ε : intervalComponents (height f ε) ⟶ (smoothing ε).obj (intervalComponents f)
```

is `π₀` of the projection at every `I`, `[(x, t)] ↦ [x]` (`componentComparison_app_mk`). Its
component at `I` is the forward map of the merged `componentEquivOfHomotopyEquiv` applied to
`preimageHomotopyEquiv f ε I`, so it is bijective, and `componentComparisonIso f ε` has the
comparison itself as hom.

With `π₀` of a height-preserving map written as `intervalComponentNatTrans`:

* the comparison is natural in height-preserving maps (`componentComparison_natural`);
* `π₀` of the zero section followed by the comparison is the smoothing unit
  `(smoothingUnit ε).app (intervalComponents f)` (`zeroSection_comp_componentComparison`, and
  `componentComparison_app_zeroSection_mk` on representatives);
* band enlargement corresponds to `smoothingMap` (`bandInclusion_comp_componentComparison`).

## The real slice

`functor ε` is `T_ε` on `Over (TopCat.of ℝ)`, with `zeroSectionNatTrans ε : 𝟭 ⟶ functor ε`.
`zeroIso : functor 0 ≅ 𝟭` has the projections `zeroHomeomorph` as components
(`zeroIso_hom_app_left_hom`) and the zero section as inverse (`zeroIso_inv`).
`componentComparisonNatIso ε` is a natural isomorphism
`functor ε ⋙ intervalComponentsOver ≅ intervalComponentsOver ⋙ smoothing ε`, with component
`componentComparison` of the structure map. The unit equation holds objectwise
(`map_zeroSectionNatTrans_comp_componentComparisonNatIso`) and as an equation of natural
transformations (`whiskerRight_zeroSectionNatTrans_comp_componentComparisonNatIso`).

`height`, `map`, `map_id`, `map_comp`, `componentComparison`, `componentComparison_app_mk`,
`componentComparison_natural` and `componentComparison_naturality` share their short names with
declarations in `ReebQuotient` or `CylinderPresentation`; refer to them by qualified name when one
of those namespaces is also open.

See `docs/math/reeb-geometric-thickening.md`.
-/

open Set Topology CategoryTheory
open scoped NNReal

universe u v w

namespace TDA.Reeb

namespace GeometricThickening

noncomputable section

open OpenInterval

/-! ### The band -/

section Band

/-- The closed band `[-ε, ε]` of DMP Definition 4.22, with the subspace topology of `ℝ`. -/
abbrev Band (ε : ℝ≥0) : Set ℝ := Icc (-(ε : ℝ)) ε

theorem neg_le_band (ε : ℝ≥0) : -(ε : ℝ) ≤ ε := neg_le_self ε.coe_nonneg

theorem zero_mem_band (ε : ℝ≥0) : (0 : ℝ) ∈ Band ε :=
  ⟨neg_nonpos.2 ε.coe_nonneg, ε.coe_nonneg⟩

/-- At `ε = 0` the band is `{0}`. -/
theorem eq_zero_of_mem_band_zero {t : ℝ} (ht : t ∈ Band 0) : t = 0 := by
  have h₁ : (0 : ℝ) ≤ t := by simpa using ht.1
  have h₂ : t ≤ (0 : ℝ) := by simpa using ht.2
  exact le_antisymm h₂ h₁

/-- The band is convex: the straight-line interpolation of two band points stays in it. -/
theorem interp_mem_band {ε : ℝ≥0} (a b : Band ε) (r : unitInterval) :
    (1 - (r : ℝ)) * a + r * b ∈ Band ε := by
  simpa only [smul_eq_mul] using
    convex_Icc (-(ε : ℝ)) ε a.2 b.2 (sub_nonneg.2 r.2.2) r.2.1 (sub_add_cancel 1 (r : ℝ))

/-- An open interval is convex: the straight-line interpolation of two of its points stays in
it. -/
theorem interp_mem {I : OpenInterval} {a b : ℝ} (ha : a ∈ I) (hb : b ∈ I) (r : unitInterval) :
    (1 - (r : ℝ)) * a + r * b ∈ I := by
  have h := (convex_iff_ordConnected.2 I.ordConnected) ha hb (sub_nonneg.2 r.2.2) r.2.1
    (sub_add_cancel 1 (r : ℝ))
  rw [smul_eq_mul, smul_eq_mul] at h
  exact h

end Band

/-! ### The clamp: DMP's auxiliary function `λ` in the proof of Lemma 4.25 -/

section Clamp

/-- The clamp `λ_c(s) = max (-ε) (min ε (c - s))` into the band: mathlib's `Set.projIcc`. -/
def clamp (ε : ℝ≥0) (c s : ℝ) : Band ε :=
  projIcc (-(ε : ℝ)) ε (neg_le_band ε) (c - s)

theorem coe_clamp (ε : ℝ≥0) (c s : ℝ) :
    (clamp ε c s : ℝ) = max (-(ε : ℝ)) (min (ε : ℝ) (c - s)) :=
  coe_projIcc _ _ _ _

theorem continuous_clamp (ε : ℝ≥0) (c : ℝ) : Continuous (clamp ε c) :=
  continuous_projIcc.comp (continuous_const.sub continuous_id)

theorem nonempty_of_mem_thicken {ε : ℝ≥0} {I : OpenInterval} {s : ℝ} (hs : s ∈ thicken ε I) :
    (I : Set ℝ).Nonempty :=
  let ⟨y, hy, _⟩ := mem_thicken.1 hs
  ⟨y, hy⟩

/-- **Clamp membership.** For `c ∈ I` and `s ∈ I^ε`, `s + λ_c(s) ∈ I`. It holds for every open
interval, including rays and `ℝ`, and for `ε = 0`; no positive radius and no finite endpoint
is used. -/
theorem add_clamp_mem {ε : ℝ≥0} {I : OpenInterval} {c s : ℝ} (hc : c ∈ I)
    (hs : s ∈ thicken ε I) : s + (clamp ε c s : ℝ) ∈ I := by
  obtain ⟨y, hy, hsy⟩ := mem_thicken.1 hs
  rw [abs_le] at hsy
  have hε := ε.coe_nonneg
  refine I.ordConnected.uIcc_subset hc hy ?_
  rw [coe_clamp, mem_uIcc]
  have hm1 : min (ε : ℝ) (c - s) ≤ ε := min_le_left _ _
  have hm2 : min (ε : ℝ) (c - s) ≤ c - s := min_le_right _ _
  have hm3 := min_choice (ε : ℝ) (c - s)
  have hv1 : -(ε : ℝ) ≤ max (-(ε : ℝ)) (min (ε : ℝ) (c - s)) := le_max_left _ _
  have hv2 : min (ε : ℝ) (c - s) ≤ max (-(ε : ℝ)) (min (ε : ℝ) (c - s)) := le_max_right _ _
  have hv3 := max_choice (-(ε : ℝ)) (min (ε : ℝ) (c - s))
  rcases hm3 with hm3 | hm3 <;> rcases hv3 with hv3 | hv3 <;> rcases le_total c y with hcy | hcy <;>
    first
    | (left; constructor <;> linarith)
    | (right; constructor <;> linarith)

end Clamp

/-! ### The thickened space (DMP Definition 4.22 and Observation 4.23) -/

section Space

variable {X : Type u} {Y : Type v} {Z : Type w}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- The thickened height `f_ε (x, t) = f x + t` on `X × [-ε, ε]` (DMP Definition 4.22). -/
def height (f : C(X, ℝ)) (ε : ℝ≥0) : C(X × Band ε, ℝ) where
  toFun z := f z.1 + z.2
  continuous_toFun := (f.continuous.comp continuous_fst).add (continuous_subtype_val.comp continuous_snd)

@[simp] theorem height_apply (f : C(X, ℝ)) (ε : ℝ≥0) (z : X × Band ε) :
    height f ε z = f z.1 + z.2 := rfl

/-- `T_ε[g] (x, t) = (g x, t)` (DMP Definition 4.22). It is defined for every continuous `g`;
height preservation needs `h ∘ g = f` (`height_map`). -/
def map (g : C(X, Y)) (ε : ℝ≥0) : C(X × Band ε, Y × Band ε) where
  toFun z := (g z.1, z.2)
  continuous_toFun := (g.continuous.comp continuous_fst).prodMk continuous_snd

@[simp] theorem map_apply (g : C(X, Y)) (ε : ℝ≥0) (z : X × Band ε) :
    map g ε z = (g z.1, z.2) := rfl

theorem height_map {f : C(X, ℝ)} {h : C(Y, ℝ)} (g : C(X, Y)) (comm : ∀ x, h (g x) = f x)
    (ε : ℝ≥0) (z : X × Band ε) : height h ε (map g ε z) = height f ε z := by
  simp [comm]

theorem map_id (ε : ℝ≥0) : map (ContinuousMap.id X) ε = ContinuousMap.id (X × Band ε) := rfl

theorem map_comp (k : C(Y, Z)) (g : C(X, Y)) (ε : ℝ≥0) :
    map (k.comp g) ε = (map k ε).comp (map g ε) := rfl

/-- The zero section `τ^ε : x ↦ (x, 0)` (DMP Observation 4.23). It does not depend on a
height function. -/
def zeroSection (X : Type u) [TopologicalSpace X] (ε : ℝ≥0) : C(X, X × Band ε) where
  toFun x := (x, ⟨0, zero_mem_band ε⟩)
  continuous_toFun := continuous_id.prodMk continuous_const

@[simp] theorem zeroSection_apply (ε : ℝ≥0) (x : X) :
    zeroSection X ε x = (x, ⟨0, zero_mem_band ε⟩) := rfl

/-- The zero section preserves height. -/
theorem height_zeroSection (f : C(X, ℝ)) (ε : ℝ≥0) (x : X) :
    height f ε (zeroSection X ε x) = f x := by
  simp

/-- Naturality of `τ^ε` on points. -/
theorem map_comp_zeroSection (g : C(X, Y)) (ε : ℝ≥0) :
    (map g ε).comp (zeroSection X ε) = (zeroSection Y ε).comp g := rfl

/-- Band enlargement `X × [-ε, ε] → X × [-δ, δ]` for `ε ≤ δ`. -/
def bandInclusion (X : Type u) [TopologicalSpace X] {ε δ : ℝ≥0} (hεδ : ε ≤ δ) :
    C(X × Band ε, X × Band δ) where
  toFun z := (z.1, ⟨z.2, Icc_subset_Icc (neg_le_neg (NNReal.coe_le_coe.2 hεδ))
    (NNReal.coe_le_coe.2 hεδ) z.2.2⟩)
  continuous_toFun := continuous_fst.prodMk
    ((continuous_subtype_val.comp continuous_snd).subtype_mk _)

theorem height_bandInclusion (f : C(X, ℝ)) {ε δ : ℝ≥0} (hεδ : ε ≤ δ) (z : X × Band ε) :
    height f δ (bandInclusion X hεδ z) = height f ε z := rfl

theorem band_bounds (f : C(X, ℝ)) {ε : ℝ≥0} (x : X) (t : Band ε) :
    (f x + t) - ε ≤ f x ∧ f x ≤ (f x + t) + ε :=
  ⟨by linarith [t.2.2], by linarith [t.2.1]⟩

theorem sub_mem_band (f : C(X, ℝ)) {ε : ℝ≥0} {x : X} {s : ℝ}
    (h : s - ε ≤ f x ∧ f x ≤ s + ε) : s - f x ∈ Band ε :=
  ⟨by linarith [h.2], by linarith [h.1]⟩

/-- The reparametrization in the proof of DMP Theorem 4.27 (Figure 8): `(x, t) ↦ (x, f x + t)`
identifies `X × [-ε, ε]` with the band `{(x, u) | u - ε ≤ f x ≤ u + ε} ⊆ X × ℝ`, with inverse
`(x, u) ↦ (x, u - f x)`; the thickened height becomes the second coordinate. -/
def bandHomeomorph (f : C(X, ℝ)) (ε : ℝ≥0) :
    X × Band ε ≃ₜ {p : X × ℝ // p.2 - ε ≤ f p.1 ∧ f p.1 ≤ p.2 + ε} where
  toFun z := ⟨(z.1, f z.1 + z.2), band_bounds f z.1 z.2⟩
  invFun p := (p.1.1, ⟨p.1.2 - f p.1.1, sub_mem_band f p.2⟩)
  left_inv z := Prod.ext rfl (Subtype.ext (show f z.1 + (z.2 : ℝ) - f z.1 = z.2 by ring))
  right_inv p := Subtype.ext (Prod.ext rfl (show f p.1.1 + (p.1.2 - f p.1.1) = p.1.2 by ring))
  continuous_toFun := (continuous_fst.prodMk (height f ε).continuous).subtype_mk _
  continuous_invFun := (continuous_fst.comp continuous_subtype_val).prodMk
    (((continuous_snd.comp continuous_subtype_val).sub
      (f.continuous.comp (continuous_fst.comp continuous_subtype_val))).subtype_mk _)

@[simp] theorem coe_bandHomeomorph_apply (f : C(X, ℝ)) (ε : ℝ≥0) (z : X × Band ε) :
    (bandHomeomorph f ε z : X × ℝ) = (z.1, f z.1 + z.2) := rfl

@[simp] theorem bandHomeomorph_symm_apply (f : C(X, ℝ)) (ε : ℝ≥0)
    (p : {p : X × ℝ // p.2 - ε ≤ f p.1 ∧ f p.1 ≤ p.2 + ε}) :
    (bandHomeomorph f ε).symm p =
      (p.1.1, ⟨p.1.2 - f p.1.1, sub_mem_band f p.2⟩) := rfl

/-- The reparametrization carries the thickened height to the second coordinate. -/
theorem snd_bandHomeomorph (f : C(X, ℝ)) (ε : ℝ≥0) (z : X × Band ε) :
    (bandHomeomorph f ε z : X × ℝ).2 = height f ε z := rfl

end Space

/-! ### Inverse images (DMP Lemma 4.25) -/

section Preimage

variable {X : Type u} {Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

/-- `f (x) + t ∈ I` implies `f (x) ∈ I^ε`. -/
theorem fst_mem_thicken {f : C(X, ℝ)} {ε : ℝ≥0} {I : OpenInterval} {z : X × Band ε}
    (hz : height f ε z ∈ I) : f z.1 ∈ thicken ε I :=
  mem_thicken.2 ⟨height f ε z, hz, abs_le.2 ⟨by rw [height_apply]; linarith [z.2.2.2],
    by rw [height_apply]; linarith [z.2.2.1]⟩⟩

/-- The first projection `p_I : f_ε⁻¹ I → f⁻¹ I^ε`, literally `(x, t) ↦ x`. It is not a map over
`ℝ`. -/
def preimageProjection (f : C(X, ℝ)) (ε : ℝ≥0) (I : OpenInterval) :
    C({z : X × Band ε // height f ε z ∈ I}, {x : X // f x ∈ thicken ε I}) where
  toFun z := ⟨z.1.1, fst_mem_thicken z.2⟩
  continuous_toFun := (continuous_fst.comp continuous_subtype_val).subtype_mk _

@[simp] theorem coe_preimageProjection_apply (f : C(X, ℝ)) (ε : ℝ≥0) (I : OpenInterval)
    (z : {z : X × Band ε // height f ε z ∈ I}) :
    (preimageProjection f ε I z : X) = z.1.1 := rfl

/-- The section `q_I (x) = (x, λ_c (f x))` for a center `c`, which must lie in `I` whenever `I`
is nonempty. It is a chosen homotopy inverse, not part of the interface. -/
def preimageSectionAt (f : C(X, ℝ)) (ε : ℝ≥0) (I : OpenInterval) {c : ℝ}
    (hc : (I : Set ℝ).Nonempty → c ∈ I) :
    C({x : X // f x ∈ thicken ε I}, {z : X × Band ε // height f ε z ∈ I}) where
  toFun x := ⟨(x.1, clamp ε c (f x.1)), add_clamp_mem (hc (nonempty_of_mem_thicken x.2)) x.2⟩
  continuous_toFun := (continuous_subtype_val.prodMk
    ((continuous_clamp ε c).comp (f.continuous.comp continuous_subtype_val))).subtype_mk _

/-- `p_I ∘ q_I = id` exactly. -/
theorem preimageProjection_comp_preimageSectionAt (f : C(X, ℝ)) (ε : ℝ≥0) (I : OpenInterval)
    {c : ℝ} (hc : (I : Set ℝ).Nonempty → c ∈ I) :
    (preimageProjection f ε I).comp (preimageSectionAt f ε I hc) = ContinuousMap.id _ :=
  ContinuousMap.ext fun _ => rfl

/-- The straight-line homotopy `(x, t, r) ↦ (x, (1 - r) λ_c (f x) + r t)` from `q_I ∘ p_I` to the
identity of `f_ε⁻¹ I`. -/
def preimageHomotopyAt (f : C(X, ℝ)) (ε : ℝ≥0) (I : OpenInterval) {c : ℝ}
    (hc : (I : Set ℝ).Nonempty → c ∈ I) :
    ContinuousMap.Homotopy ((preimageSectionAt f ε I hc).comp (preimageProjection f ε I))
      (ContinuousMap.id _) where
  toFun p := ⟨(p.2.1.1, ⟨(1 - (p.1 : ℝ)) * clamp ε c (f p.2.1.1) + p.1 * p.2.1.2,
      interp_mem_band _ _ p.1⟩), by
    have hx := fst_mem_thicken p.2.2
    have h := interp_mem (add_clamp_mem (hc (nonempty_of_mem_thicken hx)) hx) p.2.2 p.1
    show f p.2.1.1 + ((1 - (p.1 : ℝ)) * clamp ε c (f p.2.1.1) + p.1 * p.2.1.2) ∈ I
    convert h using 1
    show _ = (1 - (p.1 : ℝ)) * (f p.2.1.1 + clamp ε c (f p.2.1.1)) + p.1 * (f p.2.1.1 + p.2.1.2)
    ring⟩
  continuous_toFun := by
    have hx : Continuous fun p : unitInterval × {z : X × Band ε // height f ε z ∈ I} =>
        p.2.1.1 := continuous_fst.comp (continuous_subtype_val.comp continuous_snd)
    have hr : Continuous fun p : unitInterval × {z : X × Band ε // height f ε z ∈ I} =>
        (p.1 : ℝ) := continuous_subtype_val.comp continuous_fst
    have ht : Continuous fun p : unitInterval × {z : X × Band ε // height f ε z ∈ I} =>
        (p.2.1.2 : ℝ) :=
      continuous_subtype_val.comp (continuous_snd.comp (continuous_subtype_val.comp continuous_snd))
    have hl : Continuous fun p : unitInterval × {z : X × Band ε // height f ε z ∈ I} =>
        (clamp ε c (f p.2.1.1) : ℝ) :=
      continuous_subtype_val.comp ((continuous_clamp ε c).comp (f.continuous.comp hx))
    exact (hx.prodMk ((((continuous_const.sub hr).mul hl).add (hr.mul ht)).subtype_mk _)).subtype_mk _
  map_zero_left z := Subtype.ext (Prod.ext rfl (Subtype.ext (by
    show (1 - ((0 : unitInterval) : ℝ)) * (clamp ε c (f z.1.1) : ℝ) +
        ((0 : unitInterval) : ℝ) * z.1.2 = clamp ε c (f z.1.1)
    simp)))
  map_one_left z := Subtype.ext (Prod.ext rfl (Subtype.ext (by
    show (1 - ((1 : unitInterval) : ℝ)) * (clamp ε c (f z.1.1) : ℝ) +
        ((1 : unitInterval) : ℝ) * z.1.2 = z.1.2
    simp)))

/-- **DMP Lemma 4.25 at a center.** `p_I` is a homotopy equivalence with forward map exactly
`preimageProjection`. -/
def preimageHomotopyEquivAt (f : C(X, ℝ)) (ε : ℝ≥0) (I : OpenInterval) {c : ℝ}
    (hc : (I : Set ℝ).Nonempty → c ∈ I) :
    ContinuousMap.HomotopyEquiv {z : X × Band ε // height f ε z ∈ I}
      {x : X // f x ∈ thicken ε I} where
  toFun := preimageProjection f ε I
  invFun := preimageSectionAt f ε I hc
  left_inv := ⟨preimageHomotopyAt f ε I hc⟩
  right_inv := by
    rw [preimageProjection_comp_preimageSectionAt]

/-- A chosen center of `I`, a point of `I` whenever `I` is nonempty. -/
def intervalCenter (I : OpenInterval) : ℝ := Classical.epsilon fun c => c ∈ I

theorem intervalCenter_mem {I : OpenInterval} (hI : (I : Set ℝ).Nonempty) : intervalCenter I ∈ I :=
  Classical.epsilon_spec hI

/-- **DMP Lemma 4.25.** For every open interval `I`, including `∅`, rays and `ℝ`, and every
`ε ≥ 0`, `p_I : f_ε⁻¹ I → f⁻¹ I^ε` is a homotopy equivalence. No hypothesis on `X` is used, and
`X` may be empty. -/
def preimageHomotopyEquiv (f : C(X, ℝ)) (ε : ℝ≥0) (I : OpenInterval) :
    ContinuousMap.HomotopyEquiv {z : X × Band ε // height f ε z ∈ I}
      {x : X // f x ∈ thicken ε I} :=
  preimageHomotopyEquivAt f ε I (c := intervalCenter I) intervalCenter_mem

/-- The forward map is exactly the first projection. -/
theorem preimageHomotopyEquiv_toFun (f : C(X, ℝ)) (ε : ℝ≥0) (I : OpenInterval) :
    (preimageHomotopyEquiv f ε I).toFun = preimageProjection f ε I := rfl

theorem coe_preimageHomotopyEquiv_apply (f : C(X, ℝ)) (ε : ℝ≥0) (I : OpenInterval)
    (z : {z : X × Band ε // height f ε z ∈ I}) :
    (preimageHomotopyEquiv f ε I z : X) = z.1.1 := rfl

/-- DMP's left square in the proof of Theorem 4.24, on points: projection commutes with the
inclusions for `I ⊆ J`. -/
theorem preimageProjection_comp_inclusion (f : C(X, ℝ)) (ε : ℝ≥0) {I J : OpenInterval}
    (hIJ : I ≤ J) :
    (preimageInclusion f (toOpens_monotone (thicken_mono (ε := ε) hIJ))).comp
        (preimageProjection f ε I) =
      (preimageProjection f ε J).comp (preimageInclusion (height f ε) (toOpens_monotone hIJ)) :=
  rfl

/-- DMP's square for a morphism `g` in the proof of Theorem 4.24, on points. -/
theorem preimageProjection_comp_restrict {f : C(X, ℝ)} {h : C(Y, ℝ)} (g : C(X, Y))
    (comm : ∀ x, h (g x) = f x) (ε : ℝ≥0) (I : OpenInterval) :
    (preimageRestrict g comm (toOpens (thicken ε I))).comp (preimageProjection f ε I) =
      (preimageProjection h ε I).comp
        (preimageRestrict (map g ε) (height_map g comm ε) (toOpens I)) :=
  rfl

end Preimage

/-! ### The canonical component comparison (DMP Theorem 4.24) -/

section Comparison

variable {X : Type u} {Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

/-- `ρ_f : C(T_ε f) ⟶ S_ε C(f)` with `(ρ_f)_I = π₀[p_I]` (DMP proof of Theorem 4.24), into the
smoothing of the interval components. -/
def componentComparison (f : C(X, ℝ)) (ε : ℝ≥0) :
    intervalComponents (height f ε) ⟶ (smoothing ε).obj (intervalComponents f) where
  app I := TypeCat.ofHom (componentMap (preimageProjection f ε I))
  naturality I J i := by
    ext c
    induction c using ZerothHomotopy.rec with
    | mk z => rfl

theorem componentComparison_app (f : C(X, ℝ)) (ε : ℝ≥0) (I : OpenInterval) :
    (componentComparison f ε).app I = TypeCat.ofHom (componentMap (preimageProjection f ε I)) :=
  rfl

/-- Representative formula: `[(x, t)] ↦ [x]`. -/
@[simp] theorem componentComparison_app_mk (f : C(X, ℝ)) (ε : ℝ≥0) (I : OpenInterval)
    (z : {z : X × Band ε // height f ε z ∈ I}) :
    (componentComparison f ε).app I (ZerothHomotopy.mk z) =
      ZerothHomotopy.mk (⟨z.1.1, fst_mem_thicken z.2⟩ : {x : X // f x ∈ thicken ε I}) :=
  rfl

/-- The component at `I` is the forward map of the path-component bijection of the homotopy
equivalence of Lemma 4.25. -/
theorem componentComparison_app_eq_componentEquiv (f : C(X, ℝ)) (ε : ℝ≥0) (I : OpenInterval) :
    ⇑((componentComparison f ε).app I) =
      ⇑(componentEquivOfHomotopyEquiv (preimageHomotopyEquiv f ε I)) := by
  funext c
  induction c using ZerothHomotopy.rec with
  | mk z => rfl

theorem componentComparison_app_bijective (f : C(X, ℝ)) (ε : ℝ≥0) (I : OpenInterval) :
    Function.Bijective ((componentComparison f ε).app I) := by
  rw [componentComparison_app_eq_componentEquiv]
  exact Equiv.bijective _

instance isIso_componentComparison (f : C(X, ℝ)) (ε : ℝ≥0) :
    IsIso (componentComparison f ε) := by
  have : ∀ I, IsIso ((componentComparison f ε).app I) := fun I =>
    (isIso_iff_bijective _).2 (componentComparison_app_bijective f ε I)
  exact NatIso.isIso_of_isIso_app _

/-- **DMP Theorem 4.24, objectwise.** `C(T_ε f) ≅ S_ε C(f)`, with hom the comparison itself. -/
def componentComparisonIso (f : C(X, ℝ)) (ε : ℝ≥0) :
    intervalComponents (height f ε) ≅ (smoothing ε).obj (intervalComponents f) :=
  asIso (componentComparison f ε)

@[simp] theorem componentComparisonIso_hom (f : C(X, ℝ)) (ε : ℝ≥0) :
    (componentComparisonIso f ε).hom = componentComparison f ε := rfl

/-- Naturality in the interval (the `NatTrans` field). -/
theorem componentComparison_naturality (f : C(X, ℝ)) (ε : ℝ≥0) {I J : OpenInterval}
    (i : I ⟶ J) :
    (intervalComponents (height f ε)).map i ≫ (componentComparison f ε).app J =
      (componentComparison f ε).app I ≫ ((smoothing ε).obj (intervalComponents f)).map i :=
  (componentComparison f ε).naturality i

/-- Naturality in a height-preserving map `g` with `h ∘ g = f`: the comparison commutes with
`π₀` of `T_ε[g]` and the smoothing of `π₀` of `g`. -/
theorem componentComparison_natural {f : C(X, ℝ)} {h : C(Y, ℝ)} (g : C(X, Y))
    (comm : ∀ x, h (g x) = f x) (ε : ℝ≥0) :
    intervalComponentNatTrans (map g ε) (height_map g comm ε) ≫ componentComparison h ε =
      componentComparison f ε ≫ (smoothing ε).map (intervalComponentNatTrans g comm) := by
  ext I c
  induction c using ZerothHomotopy.rec with
  | mk z => rfl

/-- **Unit compatibility.** `π₀` of the zero section followed by the comparison is the smoothing unit `σ^ε`, as an equation of natural transformations at arbitrary carrier universe. It
holds on representatives because `p ∘ τ^ε` is the inclusion `f⁻¹ I ⊆ f⁻¹ I^ε`; DMP
Proposition 4.35 states the same square through the homotopy inverse, up to homotopy. -/
theorem zeroSection_comp_componentComparison (f : C(X, ℝ)) (ε : ℝ≥0) :
    intervalComponentNatTrans (zeroSection X ε) (height_zeroSection f ε) ≫
        componentComparison f ε =
      (smoothingUnit ε).app (intervalComponents f) := by
  ext I c
  induction c using ZerothHomotopy.rec with
  | mk x => rfl

/-- Unit compatibility on representatives: the zero-section class of `x` goes to the class of
`x` in `f⁻¹ I^ε`, which is the smoothing unit of the class of `x`. -/
theorem componentComparison_app_zeroSection_mk (f : C(X, ℝ)) (ε : ℝ≥0) (I : OpenInterval)
    (x : {x : X // f x ∈ I}) :
    (componentComparison f ε).app I
        (ZerothHomotopy.mk (⟨zeroSection X ε x.1, by rw [height_zeroSection]; exact x.2⟩ :
          {z : X × Band ε // height f ε z ∈ I})) =
      ((smoothingUnit ε).app (intervalComponents f)).app I (ZerothHomotopy.mk x) :=
  rfl

/-- Band enlargement is compatible with `smoothingMap` (an additive convenience). -/
theorem bandInclusion_comp_componentComparison (f : C(X, ℝ)) {ε δ : ℝ≥0} (hεδ : ε ≤ δ) :
    intervalComponentNatTrans (bandInclusion X hεδ) (height_bandInclusion f hεδ) ≫
        componentComparison f δ =
      componentComparison f ε ≫ (smoothingMap hεδ).app (intervalComponents f) := by
  ext I c
  induction c using ZerothHomotopy.rec with
  | mk z => rfl

end Comparison

/-! ### Packaging on the real slice (universe `0`) -/

section Over

/-- `T_ε` on the real slice `Over (TopCat.of ℝ)` (DMP Definition 4.22). -/
def functor (ε : ℝ≥0) : Over (TopCat.of ℝ) ⥤ Over (TopCat.of ℝ) where
  obj A := Over.mk (TopCat.ofHom (height (overBaseMap A) ε))
  map {A B} φ := Over.homMk (TopCat.ofHom (map φ.left.hom ε))
    (by ext z; exact height_map φ.left.hom (overBaseMap_comm φ) ε z)
  map_id A := by ext z; rfl
  map_comp φ ψ := by ext z; rfl

theorem overBaseMap_functor_obj (ε : ℝ≥0) (A : Over (TopCat.of ℝ)) :
    overBaseMap ((functor ε).obj A) = height (overBaseMap A) ε := rfl

theorem functor_map_left_hom (ε : ℝ≥0) {A B : Over (TopCat.of ℝ)} (φ : A ⟶ B) :
    ((functor ε).map φ).left.hom = map φ.left.hom ε := rfl

/-- `τ^ε : 𝟭 ⟶ T_ε` (DMP Observation 4.23). -/
def zeroSectionNatTrans (ε : ℝ≥0) : 𝟭 (Over (TopCat.of ℝ)) ⟶ functor ε where
  app A := Over.homMk (TopCat.ofHom (zeroSection A.left ε))
    (by ext x; exact height_zeroSection (overBaseMap A) ε x)
  naturality A B φ := by ext x; rfl

theorem zeroSectionNatTrans_app_left_hom (ε : ℝ≥0) (A : Over (TopCat.of ℝ)) :
    ((zeroSectionNatTrans ε).app A).left.hom = zeroSection A.left ε := rfl

/-- At `ε = 0`, `X × [0, 0] ≃ₜ X` by the first projection, with inverse the zero section. -/
def zeroHomeomorph (X : Type u) [TopologicalSpace X] : X × Band 0 ≃ₜ X where
  toFun z := z.1
  invFun x := zeroSection X 0 x
  left_inv z := Prod.ext rfl (Subtype.ext (eq_zero_of_mem_band_zero z.2.2).symm)
  right_inv _ := rfl
  continuous_toFun := continuous_fst
  continuous_invFun := (zeroSection X 0).continuous

/-- The zero homeomorphism is the first projection. -/
@[simp] theorem zeroHomeomorph_apply {X : Type u} [TopologicalSpace X] (z : X × Band 0) :
    zeroHomeomorph X z = z.1 := rfl

/-- The inverse of the zero homeomorphism is the zero section. -/
@[simp] theorem zeroHomeomorph_symm_apply {X : Type u} [TopologicalSpace X] (x : X) :
    (zeroHomeomorph X).symm x = zeroSection X 0 x := rfl

/-- The zero homeomorphism preserves height: `f` of the first projection is the thickened height
at `ε = 0`. -/
theorem apply_zeroHomeomorph {X : Type u} [TopologicalSpace X] (f : C(X, ℝ)) (z : X × Band 0) :
    f (zeroHomeomorph X z) = height f 0 z := by
  rw [zeroHomeomorph_apply, height_apply, eq_zero_of_mem_band_zero z.2.2, add_zero]

/-- `T_0 ≅ 𝟭` over `ℝ`: the projection is height-preserving at `ε = 0`. -/
def zeroIso : functor 0 ≅ 𝟭 (Over (TopCat.of ℝ)) :=
  NatIso.ofComponents
    (fun A => Over.isoMk (TopCat.isoOfHomeo (X := ((functor 0).obj A).left) (Y := A.left)
      (zeroHomeomorph A.left)) (by
        ext z
        change overBaseMap A z.1 = overBaseMap A z.1 + (z.2 : ℝ)
        rw [eq_zero_of_mem_band_zero z.2.2, add_zero]))
    (fun φ => by ext z; rfl)

/-- The inverse of `zeroIso` is the zero section. -/
theorem zeroIso_inv : zeroIso.inv = zeroSectionNatTrans 0 := by
  ext A x
  rfl

/-- The components of `zeroIso` are the zero homeomorphisms, the first projections
`A × [0, 0] → A`. -/
theorem zeroIso_hom_app_left_hom (A : Over (TopCat.of ℝ)) :
    (zeroIso.hom.app A).left.hom = (zeroHomeomorph A.left : C(A.left × Band 0, A.left)) := rfl

/-- The components of the inverse of `zeroIso` are the zero sections. -/
theorem zeroIso_inv_app_left_hom (A : Over (TopCat.of ℝ)) :
    (zeroIso.inv.app A).left.hom = zeroSection A.left 0 := rfl

/-- **DMP Theorem 4.24 on the real slice.** `T_ε ⋙ 𝒞 ≅ 𝒞 ⋙ S_ε`, using the merged
`intervalComponentsOver`. Its component at `A` is `componentComparisonIso` of the structure map. -/
def componentComparisonNatIso (ε : ℝ≥0) :
    functor ε ⋙ intervalComponentsOver ≅ intervalComponentsOver ⋙ smoothing ε :=
  NatIso.ofComponents (fun A => componentComparisonIso (overBaseMap A) ε) (fun {A B} φ => by
    ext I c
    induction c using ZerothHomotopy.rec with
    | mk z => rfl)

@[simp] theorem componentComparisonNatIso_hom_app (ε : ℝ≥0) (A : Over (TopCat.of ℝ)) :
    (componentComparisonNatIso ε).hom.app A = componentComparison (overBaseMap A) ε := rfl

/-- At `ε = 0`, `π₀` of `zeroIso` is the comparison followed by the merged `smoothingZeroIso`
(an additive coherence check). -/
theorem map_zeroIso_hom_app (A : Over (TopCat.of ℝ)) :
    intervalComponentsOver.map (zeroIso.hom.app A) =
      (componentComparisonNatIso 0).hom.app A ≫
        smoothingZeroIso.hom.app (intervalComponentsOver.obj A) := by
  ext I c
  induction c using ZerothHomotopy.rec with
  | mk z => rfl

/-- Unit compatibility on the slice, objectwise. -/
theorem map_zeroSectionNatTrans_comp_componentComparisonNatIso (ε : ℝ≥0)
    (A : Over (TopCat.of ℝ)) :
    intervalComponentsOver.map ((zeroSectionNatTrans ε).app A) ≫
        (componentComparisonNatIso ε).hom.app A =
      (smoothingUnit ε).app (intervalComponentsOver.obj A) := by
  ext I c
  induction c using ZerothHomotopy.rec with
  | mk x => rfl

/-- Unit compatibility on the slice, as an equation of natural transformations
`𝒞 ⟶ 𝒞 ⋙ S_ε`. -/
theorem whiskerRight_zeroSectionNatTrans_comp_componentComparisonNatIso (ε : ℝ≥0) :
    Functor.whiskerRight (zeroSectionNatTrans ε) intervalComponentsOver ≫
        (componentComparisonNatIso ε).hom =
      Functor.whiskerLeft intervalComponentsOver (smoothingUnit ε) := by
  ext A I c
  induction c using ZerothHomotopy.rec with
  | mk x => rfl

end Over

end

end GeometricThickening

end TDA.Reeb
