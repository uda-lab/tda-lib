import TDA.Persistence.GaussianMeasureEmbedding
import TDA.Topology.C0MeasureRepresentation

/-!
# C₀ universality of the full-plane Gaussian

At nonzero bandwidth Gaussian sections vanish at infinity. The actual RKHS
embeds continuously into C₀, and the span of its sections is uniformly dense
there. Density follows by bounded-functional separation and finite-measure
representation, using Gaussian measure separation.
-/

noncomputable section

namespace TDA.Persistence.WeightedKernel

open MeasureTheory Filter Set _root_.Topology
open scoped InnerProductSpace ZeroAtInfty BoundedContinuousFunction

private def rkhsToBCF (σ : ℝ) : Space σ →ₗ[ℝ] ((ℝ × ℝ) →ᵇ ℝ) where
  toFun f := ⟨⟨f, continuous_rkhsFunction σ f⟩,
    ⟨2 * ‖f‖, fun p q => (dist_le_norm_add_norm _ _).trans <| by
      nlinarith [norm_rkhsFunction_apply_le σ f p, norm_rkhsFunction_apply_le σ f q]⟩⟩
  map_add' f g := by ext p; exact congrFun (RKHS.coe_add f g) p
  map_smul' c f := by ext p; exact congrFun (RKHS.coe_smul f c) p

private def rkhsToBCFCLM (σ : ℝ) : Space σ →L[ℝ] ((ℝ × ℝ) →ᵇ ℝ) :=
  (rkhsToBCF σ).mkContinuous 1 fun f => by
    simpa only [one_mul] using
      (BoundedContinuousFunction.norm_le (norm_nonneg f)).2
        (norm_rkhsFunction_apply_le σ f)

private theorem gaussian_zero_at_infty {σ : ℝ} (hσ : σ ≠ 0) (q : ℝ × ℝ) :
    Tendsto (fun p => kernel σ p q) (cocompact (ℝ × ℝ)) (𝓝 0) := by
  let e := (WithLp.homeomorphProd 2 ℝ ℝ).symm
  have he : Tendsto e (cocompact (ℝ × ℝ)) (cocompact GaussianSpectral.Plane) :=
    e.isClosedEmbedding.tendsto_cocompact
  have ht : Tendsto (fun p => e p - e q) (cocompact (ℝ × ℝ))
      (cocompact GaussianSpectral.Plane) :=
    (Homeomorph.subRight (e q)).isClosedEmbedding.tendsto_cocompact.comp he
  have hn := tendsto_norm_cocompact_atTop.comp ht
  have hp := (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp hn
  have hd := hp.atTop_div_const (by positivity : 0 < 2 * σ ^ 2)
  have hz := Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hd)
  have hker (p : ℝ × ℝ) : kernel σ p q =
      Real.exp (-‖e p - e q‖ ^ 2 / (2 * σ ^ 2)) := by
    rw [kernel_eq_gaussian]
    rfl
  simpa only [hker, Function.comp_def, neg_div] using hz

/-- A full-plane Gaussian section as a continuous function vanishing at infinity. -/
def gaussianSection {σ : ℝ} (hσ : σ ≠ 0) (q : ℝ × ℝ) : C₀(ℝ × ℝ, ℝ) where
  toFun p := kernel σ p q
  continuous_toFun := by unfold kernel; fun_prop
  zero_at_infty' := gaussian_zero_at_infty hσ q

@[simp] theorem gaussianSection_apply {σ : ℝ} (hσ : σ ≠ 0) (p q : ℝ × ℝ) :
    gaussianSection hσ q p = kernel σ p q := rfl

/-- Every actual Gaussian RKHS function vanishes at infinity at nonzero bandwidth. -/
theorem rkhsFunction_zero_at_infty {σ : ℝ} (hσ : σ ≠ 0) (f : Space σ) :
    Tendsto f (cocompact (ℝ × ℝ)) (𝓝 0) := by
  let S : Submodule ℝ (Space σ) :=
    { carrier := {g | ∃ h : C₀(ℝ × ℝ, ℝ), ∀ p, h p = g p}
      zero_mem' := ⟨0, fun p => by simp [RKHS.coe_zero]⟩
      add_mem' := by
        rintro g h ⟨g₀, hg⟩ ⟨h₀, hh⟩
        exact ⟨g₀ + h₀, fun p => by simp [hg p, hh p, RKHS.coe_add]⟩
      smul_mem' := by
        rintro c g ⟨g₀, hg⟩
        exact ⟨c • g₀, fun p => by simp [hg p, RKHS.coe_smul]⟩ }
  have hclosed : IsClosed (S : Set (Space σ)) := by
    have hpre := ZeroAtInftyContinuousMap.isClosed_range_toBCF.preimage
      (rkhsToBCFCLM σ).continuous
    convert hpre using 1
    ext g
    constructor
    · rintro ⟨g₀, hg⟩
      exact ⟨g₀, by ext p; exact hg p⟩
    · rintro ⟨g₀, hg⟩
      exact ⟨g₀, fun p => congrArg (fun g : (ℝ × ℝ) →ᵇ ℝ => g p) hg⟩
  have hspan : Submodule.span ℝ {RKHS.kerFun (Space σ) p c | (p) (c)} ≤ S := by
    apply Submodule.span_le.2
    rintro _ ⟨p, c, rfl⟩
    refine ⟨c • gaussianSection hσ p, ?_⟩
    intro q
    simp [gaussianSection, RKHS.kerFun_apply, RKHS.OfKernel.kernel_ofKernel,
      kernelOp_apply, mul_comm]
  have htop : S = ⊤ := by
    apply top_le_iff.1
    rw [← RKHS.kerFun_dense (𝕜 := ℝ) (H := Space σ)]
    exact Submodule.topologicalClosure_minimal _ hspan hclosed
  obtain ⟨g, hg⟩ := show f ∈ S by rw [htop]; trivial
  have heq : (g : (ℝ × ℝ) → ℝ) = f := funext hg
  rw [← heq]
  exact zero_at_infty g

/-- The actual Gaussian RKHS function, regarded as a C₀ function. -/
def rkhsToC0 {σ : ℝ} (hσ : σ ≠ 0) (f : Space σ) : C₀(ℝ × ℝ, ℝ) where
  toFun := f
  continuous_toFun := continuous_rkhsFunction σ f
  zero_at_infty' := rkhsFunction_zero_at_infty hσ f

@[simp] theorem rkhsToC0_apply {σ : ℝ} (hσ : σ ≠ 0) (f : Space σ) (p : ℝ × ℝ) :
    rkhsToC0 hσ f p = f p := rfl

/-- The RKHS-to-C₀ inclusion has operator bound one. -/
theorem norm_rkhsToC0_le {σ : ℝ} (hσ : σ ≠ 0) (f : Space σ) :
    ‖rkhsToC0 hσ f‖ ≤ ‖f‖ :=
  (BoundedContinuousFunction.norm_le (norm_nonneg f)).2
    (norm_rkhsFunction_apply_le σ f)

/-- The actual Gaussian RKHS includes continuously and linearly in C₀. -/
def rkhsToC0CLM {σ : ℝ} (hσ : σ ≠ 0) : Space σ →L[ℝ] C₀(ℝ × ℝ, ℝ) :=
  ({ toFun := rkhsToC0 hσ
     map_add' := fun f g => by ext p; simp [rkhsToC0_apply, RKHS.coe_add]
     map_smul' := fun c f => by ext p; simp [rkhsToC0_apply, RKHS.coe_smul] } :
    Space σ →ₗ[ℝ] C₀(ℝ × ℝ, ℝ)).mkContinuous 1 fun f => by
      change ‖rkhsToC0 hσ f‖ ≤ 1 * ‖f‖
      simpa only [one_mul] using norm_rkhsToC0_le hσ f

@[simp] theorem rkhsToC0CLM_apply {σ : ℝ} (hσ : σ ≠ 0) (f : Space σ) :
    rkhsToC0CLM hσ f = rkhsToC0 hσ f := rfl

theorem norm_rkhsToC0CLM_le {σ : ℝ} (hσ : σ ≠ 0) : ‖rkhsToC0CLM hσ‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  simpa only [rkhsToC0CLM_apply, one_mul] using norm_rkhsToC0_le hσ f

@[simp] theorem rkhsToC0_featureAt {σ : ℝ} (hσ : σ ≠ 0) (p : ℝ × ℝ) :
    rkhsToC0 hσ (featureAt σ p) = gaussianSection hσ p := by
  ext q
  simp only [rkhsToC0_apply, featureAt_apply, gaussianSection_apply]

/-- Gaussian sections span a uniformly dense subspace of C₀ on the full plane. -/
theorem gaussian_sections_dense {σ : ℝ} (hσ : σ ≠ 0) :
    Dense (Submodule.span ℝ (range (gaussianSection hσ)) : Set C₀(ℝ × ℝ, ℝ)) := by
  let S := (Submodule.span ℝ (range (gaussianSection hσ))).topologicalClosure
  suffices htop : S = ⊤ by
    apply dense_iff_closure_eq.2
    exact congrArg (fun T : Submodule ℝ C₀(ℝ × ℝ, ℝ) => (T : Set C₀(ℝ × ℝ, ℝ))) htop
  by_contra hne
  obtain ⟨f, hf⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.2 hne)
  have hSclosed : IsClosed (S : Set C₀(ℝ × ℝ, ℝ)) :=
    Submodule.isClosed_topologicalClosure _
  obtain ⟨L, u, hLu, huf⟩ := geometric_hahn_banach_closed_point S.convex
    hSclosed hf.2
  have hvanish (g : C₀(ℝ × ℝ, ℝ)) (hg : g ∈ S) : L g = 0 := by
    by_contra hLg
    have hu := hLu (((u + 1) / L g) • g) (S.smul_mem _ hg)
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hLg] at hu
    linarith
  obtain ⟨μ, ν, hμ, hν, _, _, hrepr⟩ :=
    TDA.Topology.C0MeasureRepresentation.exists_finite_regular_measure_sub L
  let := hμ
  let := hν
  have hembed : positiveEmbedding σ μ = positiveEmbedding σ ν := by
    apply DFunLike.ext
    intro p
    rw [positiveEmbedding_apply, positiveEmbedding_apply]
    have hp := hvanish (gaussianSection hσ p)
      (Submodule.le_topologicalClosure _ (Submodule.subset_span (mem_range_self p)))
    rw [hrepr] at hp
    simpa only [gaussianSection_apply, kernel_symm, sub_eq_zero] using hp
  have hμν := positiveEmbedding_injective hσ μ ν hembed
  have hLzero : L = 0 := by
    ext g
    simp [hrepr, hμν]
  have hu := hLu 0 S.zero_mem
  simp only [hLzero, zero_apply] at hu huf
  linarith

/-- Uniform Gaussian approximation in a form usable without unfolding density. -/
theorem exists_gaussian_span_approx {σ : ℝ} (hσ : σ ≠ 0) (f : C₀(ℝ × ℝ, ℝ))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g ∈ Submodule.span ℝ (range (gaussianSection hσ)), ‖g - f‖ < ε := by
  obtain ⟨g, hg, hdist⟩ := Metric.mem_closure_iff.1 (gaussian_sections_dense hσ f) ε hε
  exact ⟨g, hg, by simpa [dist_eq_norm, norm_sub_rev] using hdist⟩

/-- C₀ universality for the actual Gaussian RKHS, with its genuine uniform inclusion. -/
theorem denseRange_rkhsToC0 {σ : ℝ} (hσ : σ ≠ 0) : DenseRange (rkhsToC0CLM hσ) := by
  have hsub : Submodule.span ℝ (range (gaussianSection hσ)) ≤
      (rkhsToC0CLM hσ).range := by
    apply Submodule.span_le.2
    rintro _ ⟨p, rfl⟩
    exact ⟨featureAt σ p, by simp⟩
  intro f
  exact closure_mono hsub (gaussian_sections_dense hσ f)

end TDA.Persistence.WeightedKernel
