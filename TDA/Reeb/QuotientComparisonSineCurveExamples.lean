/-
Copyright (c) 2025 Daniele Bolla. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniele Bolla, David Loeffler

The definitions `S`, `Z`, `T`, `w` and the proof of `not_joinedIn_T` are adapted from
Counterexamples/TopologistsSineCurve.lean in mathlib at
0df444a360eaa60ab8c11dca51a86af692955474. The adaptation restricts the graph to `0 < x ≤ 1`,
renames the namespace and makes the helpers private, drops the module-system syntax and the
closure and connectedness results, and states the contradiction step of `not_isPathConnected_T`
as the pointwise `¬ JoinedIn T (0, 0) w`.
-/
import TDA.Reeb.ConstructibleComparison
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-!
# The quotient-to-component comparison is not injective on the topologist's sine curve

`T ⊆ ℝ × ℝ` is the graph `S` of `x ↦ sin x⁻¹` over `0 < x ≤ 1` together with the vertical
segment `Z = {0} × [-1, 1]`, the space `𝕊` of the source. Mathlib's counterexample takes the graph
over all `0 < x`; the truncation at `x = 1` changes none of the arguments used here. The height
is the first coordinate, `fstHeight : C(T, ℝ)`. Then:

* `not_joinedIn_T`: no path in `T` joins `(0, 0)` to `w = (1, sin 1⁻¹)`;
* `joined_mk_zero_mk_w`: their classes in the Reeb quotient `Q` of `fstHeight` are joined by a
  path. The segment `Z` is the fibre over `0` and is one Reeb class, so every neighbourhood of
  that class in `Q` pulls back to a neighbourhood of `Z` in `T`; by the tube lemma it contains the
  graph over some `(0, δ)`. Hence `t ↦ q (t, sin t⁻¹)`, extended by the class of `Z` at `t = 0`,
  is continuous on `[0, 1]`;
* `componentComparison_not_injective`: `η = componentComparison fstHeight` is not injective at
  `U = ⊤`, and `intervalComponentComparison_not_injective` is the same statement at the open
  interval `ℝ`.

The statements carry no hypotheses. Connectedness of `T` is not used. Only failure of injectivity
of `η` is proved. Non-isomorphism of the two cosheaves is not claimed.

Source: de Silva, Munch and Patel, *Categorified Reeb Graphs*, Example 3.21; the sine-curve
facts follow mathlib's `Counterexamples/TopologistsSineCurve.lean`. See
`docs/math/reeb-quotient-comparison.md`.
-/

open Topology Filter Set Real

namespace TDA.Reeb.Examples.TopologistsSineCurve

open ReebQuotient

/-- The graph of `y = sin x⁻¹` over `0 < x ≤ 1`. -/
noncomputable def S : Set (ℝ × ℝ) := (fun x ↦ (x, sin x⁻¹)) '' Ioc 0 1

/-- The vertical segment `{0} × [-1, 1]`. -/
def Z : Set (ℝ × ℝ) := (fun y ↦ (0, y)) '' Icc (-1) 1

/-- The closed topologist's sine curve `S ∪ Z`. -/
noncomputable def T : Set (ℝ × ℝ) := S ∪ Z

/-- A point of the graph part. -/
noncomputable def w : ℝ × ℝ := (1, sin 1⁻¹)

theorem zero_mem_T : ((0, 0) : ℝ × ℝ) ∈ T :=
  .inr ⟨0, ⟨by norm_num, by norm_num⟩, rfl⟩

theorem w_mem_T : w ∈ T := .inl ⟨1, ⟨zero_lt_one' ℝ, le_rfl⟩, rfl⟩

/-! ## No path in `T` from the segment to the graph -/

/-- `x`-values tending to `0` at which `sin x⁻¹ = y`. -/
private noncomputable def xSeq (y : ℝ) (k : ℕ) := 1 / (arcsin y + (k + 1) * (2 * π))

private lemma xSeq_pos (y : ℝ) (k : ℕ) : 0 < xSeq y k := by
  rw [xSeq, one_div_pos]
  nlinarith [pi_pos, neg_pi_div_two_le_arcsin y]

private lemma sin_inv_xSeq {y : ℝ} (hy : y ∈ Icc (-1) 1) (k : ℕ) : sin (xSeq y k)⁻¹ = y := by
  simpa [xSeq, -Nat.cast_add, ← Nat.cast_succ] using sin_arcsin' hy

private lemma xSeq_tendsto (y : ℝ) : Tendsto (xSeq y) atTop (𝓝 0) := by
  refine .comp (g := fun k : ℝ ↦ 1 / (arcsin y + (k + 1) * (2 * π))) ?_ tendsto_natCast_atTop_atTop
  simp only [div_eq_mul_inv, show 𝓝 0 = 𝓝 (1 * (0 : ℝ)) by simp]
  refine (tendsto_inv_atTop_zero.comp <| tendsto_atTop_add_const_left _ _ ?_).const_mul _
  exact (tendsto_atTop_add_const_right _ _ tendsto_id).atTop_mul_const (by positivity)

private lemma norm_ge_abs_snd {a b : ℝ} : |b| ≤ ‖(a, b)‖ := by simp

private lemma exists_unitInterval_gt {t₀ : unitInterval} (ht₀ : t₀ < 1) {δ : ℝ} (hδ : 0 < δ) :
    ∃ t₁, t₀ < t₁ ∧ dist t₀ t₁ < δ := by
  let s₀ := (t₀ : ℝ)
  let s₁ := min (s₀ + δ / 2) 1
  have h_s₀_delta_pos : 0 ≤ s₀ + δ / 2 := add_nonneg t₀.2.1 (by positivity)
  have hs₁ : 0 ≤ s₁ := le_min h_s₀_delta_pos zero_le_one
  have hs₁' : s₁ ≤ 1 := min_le_right ..
  refine ⟨⟨s₁, hs₁, hs₁'⟩, lt_min ((lt_add_iff_pos_right _).mpr (half_pos hδ)) ht₀, ?_⟩
  have h_le : s₁ ≤ s₀ + δ / 2 := min_le_left _ _
  have h_ge : s₀ ≤ s₁ := le_min (by linarith) t₀.2.2
  rw [Subtype.dist_eq, dist_comm, dist_eq, abs_of_nonneg (by linarith)]
  linarith

private lemma mem_S_of_x_pos {p : ℝ × ℝ} (hx : 0 < p.1) (hT : p ∈ T) : p.2 = sin (p.1)⁻¹ := by
  obtain ⟨x, -, hx⟩ : p ∈ S := by
    cases hT with
    | inl hT => trivial
    | inr hZ => obtain ⟨y, ⟨-, rfl⟩⟩ := hZ; exact (lt_irrefl _ hx).elim
  simp [← hx]

private lemma exists_mem_Ioc_of_y {y : ℝ} (hy : y ∈ Icc (-1) 1) {a : ℝ} (ha : 0 < a) :
    ∃ x ∈ Ioc 0 a, sin x⁻¹ = y := by
  obtain ⟨N, h_dist⟩ := (Metric.tendsto_nhds.mp (xSeq_tendsto y) (a / 2) (by positivity)).exists
  refine ⟨xSeq y N, ⟨xSeq_pos y N, ?_⟩, sin_inv_xSeq hy _⟩
  rw [dist_eq, sub_zero, abs_of_pos (xSeq_pos _ N)] at h_dist
  linarith

/-- `T` has no path from `(0, 0)` to `w`. Let `t₀` be the last time the path meets the segment
and take `t₁ > t₀` close to `t₀`; the first coordinate sweeps `[0, a]` with `a > 0` on
`[t₀, t₁]`, so the second coordinate takes both values `±1` near `t₀`, contradicting continuity
at `t₀`. -/
theorem not_joinedIn_T : ¬ JoinedIn T (0, 0) w := by
  intro h_pathConn
  let p := h_pathConn.somePath
  have xcoord_pathContinuous : Continuous fun t ↦ (p t).1 := continuous_fst.comp p.continuous
  let t₀ : unitInterval := sSup {t | (p t).1 = 0}
  have h_pt₀_x : (p t₀).1 = 0 :=
    (isClosed_singleton.preimage xcoord_pathContinuous).sSup_mem ⟨0, by aesop⟩
  obtain ⟨δ, hδ, ht⟩ : ∃ δ, 0 < δ ∧ ∀ t, dist t t₀ < δ → dist (p t) (p t₀) < 1 :=
    Metric.eventually_nhds_iff.mp <| Metric.tendsto_nhds.mp (p.continuousAt t₀) _ one_pos
  obtain ⟨t₁, ht₁⟩ : ∃ t₁, t₀ < t₁ ∧ dist t₀ t₁ < δ := by
    refine exists_unitInterval_gt (lt_of_le_of_ne (unitInterval.le_one t₀) fun ht₀' ↦ ?_) hδ
    have w_x_path : (p 1).1 = 1 := by rw [Path.target p, w]
    have x_eq_zero : (p 1).1 = 0 := by rwa [ht₀'] at h_pt₀_x
    linarith
  let a := (p t₁).1
  have ha : 0 < a := by
    obtain ⟨x, hxI, hx_eq⟩ : p t₁ ∈ S := by
      refine (h_pathConn.somePath_mem t₁).elim id fun ⟨y, hy⟩ ↦ ?_
      have : (p t₁).1 = 0 := by simp only [p, ← hy.2]
      exact ((show t₁ ≤ t₀ from le_sSup this).not_gt ht₁.1).elim
    simpa only [a, ← hx_eq] using! hxI.1
  have intervalAZeroSubOfT₀T₁Xcoord : Icc 0 a ⊆ (fun t ↦ (p t).1) '' Icc t₀ t₁ :=
    (isPreconnected_Icc.image _ <| xcoord_pathContinuous.continuousOn).Icc_subset
      (show 0 ∈ (fun t ↦ (p t).1) '' Icc t₀ t₁ from ⟨t₀, ⟨le_rfl, ht₁.1.le⟩, ‹_›⟩)
      (show a ∈ (fun t ↦ (p t).1) '' Icc t₀ t₁ from ⟨t₁, ⟨ht₁.1.le, le_rfl⟩, rfl⟩)
  have exists_close {y : ℝ} (hy : y ∈ Icc (-1) 1) : ∃ t, dist t t₀ < δ ∧ (p t).2 = y := by
    obtain ⟨x, hx, hx'⟩ := exists_mem_Ioc_of_y hy ha
    obtain ⟨t, ht⟩ : ∃ t ∈ Icc t₀ t₁, (p t).1 = x := intervalAZeroSubOfT₀T₁Xcoord ⟨hx.1.le, hx.2⟩
    have hp : (p t).2 = sin (p t).1⁻¹ := mem_S_of_x_pos (ht.2 ▸ hx.1) (h_pathConn.somePath_mem t)
    refine ⟨t, ?_, by rw [← hx', hp, ht.2]⟩
    calc
    dist t t₀ ≤ dist t₁ t₀ := dist_right_le_of_mem_uIcc (Icc_subset_uIcc' ht.1)
    _ = dist t₀ t₁ := by rw [dist_comm]
    _ < δ := ht₁.2
  obtain ⟨x₁, hx₁, h_pathx₁⟩ : ∃ x₁, dist x₁ t₀ < δ ∧ (p x₁).2 = 1 := exists_close (by simp)
  obtain ⟨x₂, hx₂, h_pathx₂⟩ : ∃ x₂, dist x₂ t₀ < δ ∧ (p x₂).2 = -1 := exists_close (by simp)
  have : dist (p x₁) (p x₂) < 2 := by
    refine (dist_triangle_right _ _ (p t₀)).trans_lt ?_
    exact (add_lt_add (ht _ hx₁) (ht _ hx₂)).trans_eq (by norm_num)
  have := norm_ge_abs_snd.trans_lt this
  rw [h_pathx₁, h_pathx₂, abs_of_nonneg (by norm_num)] at this
  linarith

/-! ## The Reeb quotient of the first coordinate -/

/-- The height of `T`: the first coordinate. -/
def fstHeight : C(T, ℝ) := ⟨fun p => (p : ℝ × ℝ).1, continuous_fst.comp continuous_subtype_val⟩

/-- The segment `Z` is one Reeb class of `fstHeight`: `(0, y)` is joined to `(0, 0)` along the
segment, at height `0`. -/
private lemma mk_segment {y : ℝ} (hy : y ∈ Icc (-1) 1) :
    mk fstHeight ⟨(0, 0), zero_mem_T⟩ = mk fstHeight ⟨(0, y), .inr ⟨y, hy, rfl⟩⟩ := by
  have mem (s : unitInterval) : ((0 : ℝ), (s : ℝ) * y) ∈ T :=
    .inr ⟨(s : ℝ) * y, ⟨by nlinarith [s.2.1, s.2.2, hy.1, hy.2],
      by nlinarith [s.2.1, s.2.2, hy.1, hy.2]⟩, rfl⟩
  let γ : Path (⟨(0, 0), zero_mem_T⟩ : T) ⟨(0, y), .inr ⟨y, hy, rfl⟩⟩ :=
    { toFun := fun s => ⟨(0, (s : ℝ) * y), mem s⟩
      continuous_toFun := by fun_prop
      source' := by ext <;> simp
      target' := by ext <;> simp }
  exact mk_eq_mk_of_path fstHeight γ fun _ => rfl

/-- The curve `t ↦ (t, sin t⁻¹)` on `[0, 1]`, with value `(0, sin 0⁻¹) = (0, 0)` at `t = 0`. -/
private noncomputable def curve : unitInterval → T :=
  Set.codRestrict (fun s : unitInterval => ((s : ℝ), sin (s : ℝ)⁻¹)) T fun s => by
    rcases s.2.1.eq_or_lt with h | h
    · exact .inr ⟨0, ⟨by norm_num, by norm_num⟩, by simp [← h]⟩
    · exact .inl ⟨s, ⟨h, s.2.2⟩, rfl⟩

private lemma continuous_mk_curve : Continuous fun s => mk fstHeight (curve s) := by
  refine continuous_iff_continuousAt.2 fun t => ?_
  rcases t.2.1.eq_or_lt with h | h
  · rw [ContinuousAt, (nhds_basis_opens _).tendsto_right_iff]
    rintro V ⟨hVt, hV⟩
    obtain ⟨N, hN, hNV⟩ := isOpen_induced_iff.1 (hV.preimage (continuous_mk fstHeight))
    have hcurve : curve t = ⟨(0, 0), zero_mem_T⟩ := Subtype.ext (by simp [curve, ← h])
    have hseg : {(0 : ℝ)} ×ˢ Icc (-1 : ℝ) 1 ⊆ N := by
      rintro ⟨x, y⟩ ⟨rfl, hy⟩
      have : (⟨(0, y), .inr ⟨y, hy, rfl⟩⟩ : T) ∈ Subtype.val ⁻¹' N := by
        rw [hNV]
        show mk fstHeight _ ∈ V
        rw [← mk_segment hy, ← hcurve]
        exact hVt
      exact this
    obtain ⟨u, v, hu, -, hu0, hv, huv⟩ :=
      generalized_tube_lemma isCompact_singleton isCompact_Icc hN hseg
    have hut : Subtype.val ⁻¹' u ∈ 𝓝 t :=
      continuous_subtype_val.continuousAt.preimage_mem_nhds
        (hu.mem_nhds (by rw [← h]; exact hu0 rfl))
    filter_upwards [hut] with s hs
    have : curve s ∈ Subtype.val ⁻¹' N :=
      huv ⟨hs, hv ⟨neg_one_le_sin _, sin_le_one _⟩⟩
    rw [hNV] at this
    exact this
  · refine (continuous_mk fstHeight).continuousAt.comp ?_
    refine (continuousAt_codRestrict_iff _).2 ?_
    exact continuous_subtype_val.continuousAt.prodMk
      (continuous_sin.continuousAt.comp
        ((continuousAt_inv₀ h.ne').comp continuous_subtype_val.continuousAt))

/-- In the Reeb quotient of `fstHeight`, the classes of `(0, 0)` and `w` are joined by a path:
`t ↦ q (t, sin t⁻¹)` on `(0, 1]`, extended by the class of the segment at `t = 0`. -/
theorem joined_mk_zero_mk_w :
    Joined (mk fstHeight ⟨(0, 0), zero_mem_T⟩) (mk fstHeight ⟨w, w_mem_T⟩) :=
  ⟨{ toFun := fun s => mk fstHeight (curve s)
     continuous_toFun := continuous_mk_curve
     source' := congrArg (mk fstHeight) (Subtype.ext (by simp [curve]))
     target' := congrArg (mk fstHeight) (Subtype.ext (by simp [curve, w])) }⟩

/-- `η` is not injective at any open set containing all heights. -/
private lemma componentComparison_not_injective_of_forall_mem {U : TopologicalSpace.Opens ℝ}
    (hU : ∀ t : ℝ, t ∈ U) : ¬ Function.Injective ((componentComparison fstHeight).app U) := by
  intro hinj
  have hne : ZerothHomotopy.mk (⟨⟨(0, 0), zero_mem_T⟩, hU _⟩ : {x : T // fstHeight x ∈ U}) ≠
      ZerothHomotopy.mk ⟨⟨w, w_mem_T⟩, hU _⟩ := by
    intro h
    obtain ⟨γ⟩ : Joined _ _ := Quotient.exact h
    exact not_joinedIn_T
      ⟨γ.map (continuous_subtype_val.comp continuous_subtype_val), fun t => (γ t).1.2⟩
  refine hne (hinj ?_)
  rw [componentComparison_app_mk, componentComparison_app_mk]
  have hV (q : ReebQuotient fstHeight) :
      q ∈ {q : ReebQuotient fstHeight | height fstHeight q ∈ U} := hU _
  exact Quotient.sound <| (joinedIn_iff_joined (hV _) (hV _)).1 <|
    (joinedIn_univ.2 joined_mk_zero_mk_w).mono fun q _ => hV q

/-- de Silva–Munch–Patel, Example 3.21: `η_f = componentComparison f` is not injective at
`U = ⊤` for the first coordinate `f` of the topologist's sine curve. The path components of
`(0, 0)` and `w` in `T` are distinct (`not_joinedIn_T`) and have the same image
(`joined_mk_zero_mk_w`). -/
theorem componentComparison_not_injective :
    ¬ Function.Injective ((componentComparison fstHeight).app ⊤) :=
  componentComparison_not_injective_of_forall_mem fun _ => by simp

/-- The same failure on open intervals, at the interval `ℝ`. -/
theorem intervalComponentComparison_not_injective :
    ¬ Function.Injective ((intervalComponentComparison fstHeight).app ⊤) := by
  rw [intervalComponentComparison_app]
  exact componentComparison_not_injective_of_forall_mem fun _ => trivial

end TDA.Reeb.Examples.TopologistsSineCurve
