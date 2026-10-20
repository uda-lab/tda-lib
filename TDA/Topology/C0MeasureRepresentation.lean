/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors

The internal signed C_c decomposition is adapted from
TauCeti/MeasureTheory/Integral/RieszMarkovKakutani/Signed.lean and its three
CompactlySupportedContinuousMap.toReal helpers, revision
b971ef7017efd17b28899a41289f2f11cdced2a2.
Adaptation: keep the decomposition private, use the pinned mathlib imports,
and add the bounded C₀ finite-measure representation bridge below.
-/
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.Topology.UrysohnsLemma
import Mathlib.Topology.ContinuousMap.ZeroAtInfty

/-!
# Finite-measure representation of bounded functionals on C₀

A bounded real-linear functional on continuous functions vanishing at infinity
is a difference of integration against two finite regular measures. The internal
order-bounded C_c decomposition is a compatibility adaptation of the cited
Apache-2.0 Tau Ceti source. The operator-norm bound supplies finite total mass;
uniform cutoff approximation extends its identity to C₀.
-/

noncomputable section

open scoped NNReal CompactlySupported

namespace CompactlySupportedContinuousMap

variable {X : Type*} [TopologicalSpace X]

/-- `toReal` sends the zero function to the zero function. -/
@[simp]
private lemma toReal_zero : (0 : C_c(X, ℝ≥0)).toReal = 0 := by
  ext x
  simp

/-- `toReal` is an order embedding. -/
@[simp]
private lemma toReal_le_toReal_iff {f g : C_c(X, ℝ≥0)} : f.toReal ≤ g.toReal ↔ f ≤ g := by
  simp [le_def]

/-- On a nonnegative function, `toReal` is a left inverse of `nnrealPart`; compare
`nnrealPart_toReal_eq`. -/
private lemma toReal_nnrealPart_of_nonneg {f : C_c(X, ℝ)} (hf : 0 ≤ f) :
    f.nnrealPart.toReal = f := by
  ext x
  simpa using le_def.1 hf x

end CompactlySupportedContinuousMap

open CompactlySupportedContinuousMap MeasureTheory Set
open scoped NNReal CompactlySupported

namespace TDA.Topology.C0MeasureRepresentation.Internal

variable {X : Type*} [TopologicalSpace X] {Λ : C_c(X, ℝ) →ₗ[ℝ] ℝ}

section Construction

/-- The positive part of `Λ` on a nonnegative function `f`, the supremum of `Λ` over the
functions between `0` and `f`. -/
private def posPartAux (Λ : C_c(X, ℝ) →ₗ[ℝ] ℝ) (f : C_c(X, ℝ≥0)) : ℝ :=
  ⨆ g : Iic f, Λ (g : C_c(X, ℝ≥0)).toReal

variable (hΛ : ∀ f : C_c(X, ℝ), BddAbove (Λ '' Icc 0 f))
include hΛ

private lemma bddAbove_range_posPartAux (f : C_c(X, ℝ≥0)) :
    BddAbove (range fun g : Iic f => Λ (g : C_c(X, ℝ≥0)).toReal) :=
  (hΛ f.toReal).mono <| by
    rintro _ ⟨⟨g, hg⟩, rfl⟩
    exact ⟨g.toReal, ⟨toReal_nonneg, toReal_le_toReal_iff.2 hg⟩, rfl⟩

private lemma apply_le_posPartAux {f g : C_c(X, ℝ≥0)} (hg : g ≤ f) :
    Λ g.toReal ≤ posPartAux Λ f :=
  le_ciSup (f := fun g : Iic f => Λ (g : C_c(X, ℝ≥0)).toReal) (bddAbove_range_posPartAux hΛ f)
    ⟨g, hg⟩

omit hΛ in
private lemma posPartAux_le {f : C_c(X, ℝ≥0)} {c : ℝ} (h : ∀ g ≤ f, Λ g.toReal ≤ c) :
    posPartAux Λ f ≤ c :=
  have : Nonempty (Iic f) := ⟨⟨f, mem_Iic.2 le_rfl⟩⟩
  ciSup_le fun g => h g g.2

private lemma posPartAux_nonneg (f : C_c(X, ℝ≥0)) : 0 ≤ posPartAux Λ f := by
  simpa using apply_le_posPartAux hΛ (le_def.2 fun x => by simp : 0 ≤ f)

private lemma posPartAux_add (f₁ f₂ : C_c(X, ℝ≥0)) :
    posPartAux Λ (f₁ + f₂) = posPartAux Λ f₁ + posPartAux Λ f₂ := by
  refine le_antisymm (posPartAux_le fun g hg => ?_) ?_
  · -- Riesz decomposition: `g = g ⊓ f₁ + g₂` with `g₂ ≤ f₂`.
    obtain ⟨g₂, hg₂⟩ := CompactlySupportedContinuousMap.exists_add_of_le (inf_le_left : g ⊓ f₁ ≤ g)
    have hg₂f₂ : g₂ ≤ f₂ := le_def.2 fun x => by
      have hx : min (g x) (f₁ x) + g₂ x = g x := by simpa using congr($hg₂ x)
      have hgx : g x ≤ f₁ x + f₂ x := by simpa using le_def.1 hg x
      rcases le_total (g x) (f₁ x) with h | h
      · rw [min_eq_left h, add_eq_left] at hx
        simp [hx]
      · rw [min_eq_right h] at hx
        exact le_of_add_le_add_left (hx ▸ hgx)
    rw [← hg₂, toReal_add, map_add]
    exact add_le_add (apply_le_posPartAux hΛ inf_le_right) (apply_le_posPartAux hΛ hg₂f₂)
  · rw [← le_sub_iff_add_le]
    refine posPartAux_le fun g₁ hg₁ => ?_
    rw [le_sub_comm]
    refine posPartAux_le fun g₂ hg₂ => ?_
    rw [le_sub_iff_add_le', ← map_add, ← toReal_add]
    exact apply_le_posPartAux hΛ (add_le_add hg₁ hg₂)

omit hΛ in
private lemma apply_toReal_smul (c : ℝ≥0) (g : C_c(X, ℝ≥0)) :
    Λ (c • g).toReal = c * Λ g.toReal := by
  rw [toReal_smul, NNReal.smul_def, map_smul, smul_eq_mul]

private lemma posPartAux_smul (c : ℝ≥0) (f : C_c(X, ℝ≥0)) :
    posPartAux Λ (c • f) = c * posPartAux Λ f := by
  rcases eq_or_ne c 0 with rfl | hc
  · refine le_antisymm (posPartAux_le fun g hg => ?_) (by simpa using posPartAux_nonneg hΛ 0)
    have hg0 : g = 0 := le_antisymm (by simpa using hg) (le_def.2 fun x => by simp)
    simp [hg0]
  have hc₀ : (0 : ℝ) < c := by positivity
  refine le_antisymm (posPartAux_le fun g hg => ?_) ?_
  · -- `g = c • (c⁻¹ • g)` with `c⁻¹ • g ≤ f`.
    have hle : c⁻¹ • g ≤ f := le_def.2 fun x => by
      have hx : g x ≤ c * f x := by simpa using le_def.1 hg x
      simpa [inv_mul_le_iff₀ (pos_iff_ne_zero.2 hc)] using hx
    have hg' : g = c • c⁻¹ • g := by rw [smul_smul, mul_inv_cancel₀ hc, one_smul]
    rw [hg', apply_toReal_smul]
    exact mul_le_mul_of_nonneg_left (apply_le_posPartAux hΛ hle) hc₀.le
  · rw [← le_div_iff₀' hc₀]
    refine posPartAux_le fun g hg => ?_
    rw [le_div_iff₀' hc₀, ← apply_toReal_smul]
    refine apply_le_posPartAux hΛ (le_def.2 fun x => ?_)
    simpa using mul_le_mul_of_nonneg_left (le_def.1 hg x) c.2

/-- The positive part of `Λ` as an `ℝ≥0`-linear functional on `C_c(X, ℝ≥0)`. -/
private def posPartNNReal : C_c(X, ℝ≥0) →ₗ[ℝ≥0] ℝ≥0 where
  toFun f := ⟨posPartAux Λ f, posPartAux_nonneg hΛ f⟩
  map_add' f₁ f₂ := NNReal.eq (posPartAux_add hΛ f₁ f₂)
  map_smul' c f := NNReal.eq (posPartAux_smul hΛ c f)

private lemma coe_posPartNNReal_apply (f : C_c(X, ℝ≥0)) :
    (posPartNNReal hΛ f : ℝ) = posPartAux Λ f :=
  (rfl)

end Construction

variable (Λ) (hΛ : ∀ f : C_c(X, ℝ), BddAbove (Λ '' Icc 0 f))

/-- The **positive part** of an order-bounded linear functional `Λ` on `C_c(X, ℝ)`: the positive
linear functional which on a nonnegative `f` is the supremum of `Λ g` over `0 ≤ g ≤ f`
(`TauCeti.RealRMK.posPart_apply_of_nonneg`). It is the least positive functional dominating `Λ`
on nonnegative functions (`TauCeti.RealRMK.posPart_apply_le_of_le`). -/
private def posPart : C_c(X, ℝ) →ₚ[ℝ] ℝ :=
  toRealPositiveLinear (posPartNNReal hΛ)

variable {Λ}

private lemma posPart_apply_eq_posPartAux {f : C_c(X, ℝ)} (hf : 0 ≤ f) :
    posPart Λ hΛ f = posPartAux Λ f.nnrealPart := by
  simp [posPart, toRealPositiveLinear_apply, nnrealPart_neg_eq_zero_of_nonneg hf,
    coe_posPartNNReal_apply]

/-- Every `Λ g` with `0 ≤ g ≤ f` is bounded by the positive part of `Λ` at `f`. -/
private theorem apply_le_posPart_apply {f g : C_c(X, ℝ)} (hg : 0 ≤ g) (hgf : g ≤ f) :
    Λ g ≤ posPart Λ hΛ f := by
  rw [posPart_apply_eq_posPartAux hΛ (hg.trans hgf)]
  have h := apply_le_posPartAux hΛ (f := f.nnrealPart) (g := g.nnrealPart) <|
    toReal_le_toReal_iff.1 <| by
      rwa [toReal_nnrealPart_of_nonneg hg, toReal_nnrealPart_of_nonneg (hg.trans hgf)]
  rwa [toReal_nnrealPart_of_nonneg hg] at h

/-- On a nonnegative `f`, the positive part of `Λ` is at most every upper bound of `Λ` on
`[0, f]`. -/
private theorem posPart_apply_le {f : C_c(X, ℝ)} (hf : 0 ≤ f) {c : ℝ}
    (h : ∀ g : C_c(X, ℝ), 0 ≤ g → g ≤ f → Λ g ≤ c) : posPart Λ hΛ f ≤ c := by
  rw [posPart_apply_eq_posPartAux hΛ hf]
  exact posPartAux_le fun g hg => h _ toReal_nonneg
    ((toReal_le_toReal_iff.2 hg).trans_eq (toReal_nnrealPart_of_nonneg hf))

variable (Λ) in
/-- The **negative part** `posPart Λ hΛ - Λ` of an order-bounded linear functional `Λ` on
`C_c(X, ℝ)`, a positive linear functional.  -/
private def negPart : C_c(X, ℝ) →ₚ[ℝ] ℝ :=
  PositiveLinearMap.mk₀ ((posPart Λ hΛ).toLinearMap - Λ) fun f hf => by
    simpa using apply_le_posPart_apply hΛ hf le_rfl

/-- The negative part of `Λ` is its positive part minus `Λ`. -/
@[simp]
private theorem negPart_apply (f : C_c(X, ℝ)) : negPart Λ hΛ f = posPart Λ hΛ f - Λ f :=
  (rfl)

/-- The **Jordan decomposition** `Λ = posPart Λ hΛ - negPart Λ hΛ`. -/
private theorem posPart_sub_negPart_apply (f : C_c(X, ℝ)) :
    posPart Λ hΛ f - negPart Λ hΛ f = Λ f := by
  simp

/-- On a nonnegative `f`, the negative part of `Λ` is at most every upper bound of `-Λ` on
`[0, f]`. -/
private theorem negPart_apply_le {f : C_c(X, ℝ)} (hf : 0 ≤ f) {c : ℝ}
    (h : ∀ g : C_c(X, ℝ), 0 ≤ g → g ≤ f → -Λ g ≤ c) : negPart Λ hΛ f ≤ c := by
  rw [negPart_apply, sub_le_iff_le_add]
  refine posPart_apply_le hΛ hf fun g hg hgf => ?_
  have := h (f - g) (sub_nonneg.2 hgf) (sub_le_self f hg)
  rw [map_sub] at this
  linarith

section Measure

variable [T2Space X] [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]

/-- The **Riesz–Markov–Kakutani representation theorem** for an order-bounded linear functional
`Λ` on `C_c(X, ℝ)`: `Λ` is integration against the Riesz measure of its positive part minus
integration against the Riesz measure of its negative part. -/
private theorem integral_rieszMeasure_posPart_sub_integral_rieszMeasure_negPart (f : C_c(X, ℝ)) :
    ∫ x, f x ∂(_root_.RealRMK.rieszMeasure (posPart Λ hΛ)) -
      ∫ x, f x ∂(_root_.RealRMK.rieszMeasure (negPart Λ hΛ)) = Λ f := by
  rw [_root_.RealRMK.integral_rieszMeasure, _root_.RealRMK.integral_rieszMeasure,
    posPart_sub_negPart_apply]

end Measure

end TDA.Topology.C0MeasureRepresentation.Internal

namespace TDA.Topology.C0MeasureRepresentation

open MeasureTheory Set Filter _root_.Topology
open scoped CompactlySupported ZeroAtInfty

variable {X : Type*} [TopologicalSpace X]

private def ccInclusion : C_c(X, ℝ) →ₗ[ℝ] C₀(X, ℝ) where
  toFun f := f
  map_add' f g := by ext x; rfl
  map_smul' c f := by ext x; rfl

private theorem cc_norm_le {f : C_c(X, ℝ)} {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ x, ‖f x‖ ≤ C) : ‖(f : C₀(X, ℝ))‖ ≤ C :=
  (BoundedContinuousFunction.norm_le hC).2 hf

private def restrictFunctional (L : C₀(X, ℝ) →L[ℝ] ℝ) : C_c(X, ℝ) →ₗ[ℝ] ℝ :=
  L.toLinearMap.comp ccInclusion

private theorem restrictFunctional_orderBounded (L : C₀(X, ℝ) →L[ℝ] ℝ)
    (f : C_c(X, ℝ)) : BddAbove (restrictFunctional L '' Icc 0 f) := by
  refine ⟨‖L‖ * ‖(f : C₀(X, ℝ))‖, ?_⟩
  rintro _ ⟨g, ⟨hg, hgf⟩, rfl⟩
  have hgn : ‖(g : C₀(X, ℝ))‖ ≤ ‖(f : C₀(X, ℝ))‖ := by
    apply cc_norm_le (norm_nonneg _)
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (hg x)]
    exact (hgf x).trans ((f : C₀(X, ℝ)).toBCF.apply_le_norm x)
  exact (le_abs_self (L (g : C₀(X, ℝ)))).trans <|
    (L.le_opNorm (g : C₀(X, ℝ))).trans <|
      mul_le_mul_of_nonneg_left hgn (norm_nonneg _)

variable [T2Space X] [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]

private theorem finite_rieszMeasure_of_cutoff_bound (P : C_c(X, ℝ) →ₚ[ℝ] ℝ)
    {C : ℝ} (_hC : 0 ≤ C)
    (hP : ∀ f : C_c(X, ℝ), (∀ x, f x ∈ Icc (0 : ℝ) 1) → P f ≤ C) :
    IsFiniteMeasure (_root_.RealRMK.rieszMeasure P) := by
  have hcompact (K : Set X) (hK : IsCompact K) :
      _root_.RealRMK.rieszMeasure P K ≤ ENNReal.ofReal C := by
    obtain ⟨f, hfK, hfc, _, hf01⟩ :=
      exists_continuousMap_one_of_isCompact_subset_isOpen hK isOpen_univ (subset_univ K)
    let g : C_c(X, ℝ) := ⟨f, hfc⟩
    exact (_root_.RealRMK.rieszMeasure_le_of_eq_one P (f := g)
      (fun x => (hf01 x).1) hK hfK).trans (ENNReal.ofReal_le_ofReal (hP g hf01))
  have hmass : _root_.RealRMK.rieszMeasure P univ ≤ ENNReal.ofReal C := by
    rw [isOpen_univ.measure_eq_iSup_isCompact]
    exact iSup_le fun K => iSup_le fun _ => iSup_le fun hK => hcompact K hK
  exact ⟨hmass.trans_lt ENNReal.ofReal_lt_top⟩

private theorem finite_posPart_measure (L : C₀(X, ℝ) →L[ℝ] ℝ) :
    IsFiniteMeasure (_root_.RealRMK.rieszMeasure
      (Internal.posPart (restrictFunctional L) (restrictFunctional_orderBounded L))) := by
  apply finite_rieszMeasure_of_cutoff_bound _ (norm_nonneg L)
  intro f hf
  apply Internal.posPart_apply_le (restrictFunctional_orderBounded L)
    (fun x => (hf x).1)
  intro g hg hgf
  have hgn : ‖(g : C₀(X, ℝ))‖ ≤ 1 := by
    apply cc_norm_le zero_le_one
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (hg x)]
    exact (hgf x).trans (hf x).2
  exact (le_abs_self (L (g : C₀(X, ℝ)))).trans <|
    (L.le_opNorm (g : C₀(X, ℝ))).trans <| by nlinarith [norm_nonneg L]

private theorem finite_negPart_measure (L : C₀(X, ℝ) →L[ℝ] ℝ) :
    IsFiniteMeasure (_root_.RealRMK.rieszMeasure
      (Internal.negPart (restrictFunctional L) (restrictFunctional_orderBounded L))) := by
  apply finite_rieszMeasure_of_cutoff_bound _ (norm_nonneg L)
  intro f hf
  apply Internal.negPart_apply_le (restrictFunctional_orderBounded L)
    (fun x => (hf x).1)
  intro g hg hgf
  have hgn : ‖(g : C₀(X, ℝ))‖ ≤ 1 := by
    apply cc_norm_le zero_le_one
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (hg x)]
    exact (hgf x).trans (hf x).2
  exact (neg_le_abs (L (g : C₀(X, ℝ)))).trans <|
    (L.le_opNorm (g : C₀(X, ℝ))).trans <| by nlinarith [norm_nonneg L]

omit [MeasurableSpace X] [BorelSpace X] in
/-- Compactly supported continuous functions are uniformly dense in C₀. -/
theorem denseRange_compactlySupported :
    DenseRange (fun f : C_c(X, ℝ) => (f : C₀(X, ℝ))) := by
  intro f
  apply Metric.mem_closure_iff.2
  intro ε hε
  obtain ⟨K, hK, htail⟩ := Filter.mem_cocompact.1 <|
    (zero_at_infty f) (Metric.ball_mem_nhds (0 : ℝ) (half_pos hε))
  obtain ⟨χ, hχK, hχc, _, hχ01⟩ :=
    exists_continuousMap_one_of_isCompact_subset_isOpen hK isOpen_univ (subset_univ K)
  have hχsupport : HasCompactSupport (χ : X → ℝ) := hχc
  let g : C_c(X, ℝ) := ⟨χ * f.toContinuousMap, hχsupport.mul_right⟩
  refine ⟨ccInclusion g, ⟨g, rfl⟩, ?_⟩
  apply lt_of_le_of_lt ?_ (half_lt_self hε)
  rw [dist_comm, dist_eq_norm]
  apply (BoundedContinuousFunction.norm_le (le_of_lt (half_pos hε))).2
  intro x
  change ‖χ x * f x - f x‖ ≤ ε / 2
  by_cases hx : x ∈ K
  · simpa [hχK hx] using (le_of_lt (half_pos hε))
  · have ht := htail hx
    have hfx : |f x| < ε / 2 := by simpa [Real.dist_eq] using ht
    have hχ : |χ x - 1| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith [(hχ01 x).1, (hχ01 x).2]
    calc
      _ = |χ x - 1| * |f x| := by rw [← sub_one_mul, Real.norm_eq_abs, abs_mul]
      _ ≤ 1 * |f x| := mul_le_mul_of_nonneg_right hχ (abs_nonneg _)
      _ ≤ ε / 2 := by linarith

/-- Every bounded real functional on C₀ is represented by a difference of finite regular
measures. In particular the representing measures have finite mass on the whole space,
not only on compact subsets. -/
theorem exists_finite_regular_measure_sub (L : C₀(X, ℝ) →L[ℝ] ℝ) :
    ∃ μ ν : Measure X, IsFiniteMeasure μ ∧ IsFiniteMeasure ν ∧ μ.Regular ∧ ν.Regular ∧
      ∀ f : C₀(X, ℝ), L f = (∫ x, f x ∂μ) - ∫ x, f x ∂ν := by
  let Λ := restrictFunctional L
  let P := Internal.posPart Λ (restrictFunctional_orderBounded L)
  let N := Internal.negPart Λ (restrictFunctional_orderBounded L)
  let μ := _root_.RealRMK.rieszMeasure P
  let ν := _root_.RealRMK.rieszMeasure N
  have hμ : IsFiniteMeasure μ := finite_posPart_measure L
  have hν : IsFiniteMeasure ν := finite_negPart_measure L
  let := hμ
  let := hν
  refine ⟨μ, ν, hμ, hν, inferInstance, inferInstance, ?_⟩
  have hcont (ρ : Measure X) [IsFiniteMeasure ρ] :
      Continuous (fun f : C₀(X, ℝ) => ∫ x, f x ∂ρ) := by
    apply continuous_iff_continuousAt.2
    intro f
    apply Metric.continuousAt_iff.2
    intro ε hε
    refine ⟨ε / (ρ.real univ + 1), by positivity, ?_⟩
    intro g hg
    rw [dist_eq_norm]
    have hgint : Integrable (fun x => g x) ρ := g.toBCF.integrable ρ
    have hfint : Integrable (fun x => f x) ρ := f.toBCF.integrable ρ
    rw [← integral_sub hgint hfint]
    have hbound := (g - f).toBCF.norm_integral_le_mul_norm ρ
    rw [ZeroAtInftyContinuousMap.norm_toBCF_eq_norm] at hbound
    change ‖∫ x, g x - f x ∂ρ‖ ≤ ρ.real univ * ‖g - f‖ at hbound
    have hdist : ‖g - f‖ < ε / (ρ.real univ + 1) := by simpa [dist_eq_norm] using hg
    have := (lt_div_iff₀ (by positivity : 0 < ρ.real univ + 1)).1 hdist
    nlinarith [norm_nonneg (g - f), measureReal_nonneg (μ := ρ) (s := univ)]
  have heq : (fun f : C₀(X, ℝ) => L f) = fun f => (∫ x, f x ∂μ) - ∫ x, f x ∂ν := by
    apply denseRange_compactlySupported.equalizer L.continuous ((hcont μ).sub (hcont ν))
    funext f
    change Λ f = (∫ x, f x ∂μ) - ∫ x, f x ∂ν
    exact (Internal.integral_rieszMeasure_posPart_sub_integral_rieszMeasure_negPart
      (restrictFunctional_orderBounded L) f).symm
  exact congrFun heq

end TDA.Topology.C0MeasureRepresentation
