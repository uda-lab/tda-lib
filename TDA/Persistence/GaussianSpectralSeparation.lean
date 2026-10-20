import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Tactic

/-!
# Spectral separation by the planar Gaussian

The spectral law is the standard Gaussian on the Euclidean plane. The phase
uses inverse bandwidth; this keeps the full-support argument independent of a
change of spectral measure. All measures in the separation result are finite.
-/

noncomputable section

namespace TDA.Persistence.WeightedKernel.GaussianSpectral

open MeasureTheory ProbabilityTheory Complex Set
open scoped InnerProductSpace ComplexConjugate

abbrev Plane := WithLp 2 (ℝ × ℝ)

instance instMeasurableSpacePlane : MeasurableSpace Plane := borel Plane
instance instBorelSpacePlane : BorelSpace Plane := ⟨rfl⟩

private def phase (σ : ℝ) (p ω : Plane) : ℂ :=
  Complex.exp ((⟪p, ω⟫_ℝ / σ : ℝ) * Complex.I)

private theorem norm_phase (σ : ℝ) (p ω : Plane) : ‖phase σ p ω‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

private theorem phase_mul_conj (σ : ℝ) (p q ω : Plane) :
    phase σ p ω * conj (phase σ q ω) = phase σ (p - q) ω := by
  rw [phase, phase, ← Complex.exp_conj, ← Complex.exp_add, phase]
  congr 1
  simp only [map_mul, map_div₀, conj_ofReal, conj_I, inner_sub_left,
    Complex.ofReal_div, Complex.ofReal_sub]
  ring

/-- The standard spectral Gaussian gives positive mass to every nonempty open subset of
the Euclidean plane. -/
private theorem fullSupport : (stdGaussian Plane).IsOpenPosMeasure := by
  have : (gaussianReal 0 1).IsOpenPosMeasure :=
    (gaussianReal_absolutelyContinuous' 0 one_ne_zero).isOpenPosMeasure
  unfold stdGaussian
  apply Continuous.isOpenPosMeasure_map (by fun_prop)
  intro p
  refine ⟨fun i => (stdOrthonormalBasis ℝ Plane).repr p i, ?_⟩
  exact (stdOrthonormalBasis ℝ Plane).sum_repr p

/-- The Gaussian spectral identity with exponent `-‖p‖² / (2σ²)`. -/
private theorem integral_phase (σ : ℝ) (p : Plane) :
    (∫ ω, phase σ p ω ∂stdGaussian Plane) =
      (Real.exp (-‖p‖ ^ 2 / (2 * σ ^ 2)) : ℂ) := by
  have h := charFun_stdGaussian (σ⁻¹ • p)
  rw [charFun_apply] at h
  have hphase : (fun ω : Plane => phase σ p ω) =
      fun ω => Complex.exp (⟪ω, σ⁻¹ • p⟫_ℝ * Complex.I) := by
    funext ω
    simp [phase, inner_smul_right, div_eq_mul_inv]
    congr 1
    ring
  rw [hphase, h]
  norm_cast
  congr 1
  rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, inv_pow]
  by_cases hσ : σ = 0
  · simp [hσ]
  · field_simp [hσ]

private theorem phase_mean (σ : ℝ) (μ : Measure Plane) (ω : Plane) :
    (∫ p, phase σ p ω ∂μ) = charFun μ (σ⁻¹ • ω) := by
  rw [charFun_apply]
  congr 1
  ext p
  simp [phase, inner_smul_right, div_eq_mul_inv]
  congr 1
  ring

private theorem bounded_continuous_integrable {A : Type*} [TopologicalSpace A]
    [MeasurableSpace A] [BorelSpace A] [SecondCountableTopology A]
    (μ : Measure A) [IsFiniteMeasure μ] {f : A → ℂ} (hf : Continuous f)
    (C : ℝ) (hC : ∀ x, ‖f x‖ ≤ C) : Integrable f μ :=
  (integrable_const C).mono' hf.stronglyMeasurable.aestronglyMeasurable
    (Filter.Eventually.of_forall hC)

/-- Integrating Gaussian sections against two finite measures is the spectral product of
their characteristic functions. All interchanges involve bounded continuous integrands. -/
private theorem spectral_cross (σ : ℝ) (μ ν : Measure Plane)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    (∫ p, ∫ q, (Real.exp (-‖p - q‖ ^ 2 / (2 * σ ^ 2)) : ℂ) ∂ν ∂μ) =
      ∫ ω, charFun μ (σ⁻¹ • ω) * conj (charFun ν (σ⁻¹ • ω)) ∂stdGaussian Plane := by
  have hswap (p : Plane) :
      (∫ q, ∫ ω, phase σ p ω * conj (phase σ q ω) ∂stdGaussian Plane ∂ν) =
        ∫ ω, ∫ q, phase σ p ω * conj (phase σ q ω) ∂ν ∂stdGaussian Plane := by
    apply integral_integral_swap
    apply bounded_continuous_integrable _ (by unfold phase; fun_prop) 1
    intro x
    change ‖phase σ p x.2 * conj (phase σ x.1 x.2)‖ ≤ 1
    simp [norm_phase]
  have hinner (p ω : Plane) :
      (∫ q, phase σ p ω * conj (phase σ q ω) ∂ν) =
        phase σ p ω * conj (charFun ν (σ⁻¹ • ω)) := by
    rw [integral_const_mul, integral_conj, phase_mean]
  calc
    _ = ∫ p, ∫ q, ∫ ω, phase σ p ω * conj (phase σ q ω) ∂stdGaussian Plane ∂ν ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with p
      apply integral_congr_ae
      filter_upwards [] with q
      simp_rw [phase_mul_conj, integral_phase]
    _ = ∫ p, ∫ ω, phase σ p ω * conj (charFun ν (σ⁻¹ • ω)) ∂stdGaussian Plane ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with p
      rw [hswap]
      simp_rw [hinner]
    _ = ∫ ω, ∫ p, phase σ p ω * conj (charFun ν (σ⁻¹ • ω)) ∂μ ∂stdGaussian Plane := by
      apply integral_integral_swap
      apply bounded_continuous_integrable _
        (by unfold phase; fun_prop) (ν.real univ)
      intro x
      change ‖phase σ x.1 x.2 * conj (charFun ν (σ⁻¹ • x.2))‖ ≤ ν.real univ
      simpa only [norm_mul, norm_phase, one_mul, norm_conj] using
        norm_charFun_le (μ := ν) (σ⁻¹ • x.2)
    _ = _ := by simp_rw [integral_mul_const, phase_mean]

/-- Finite positive measures on the Euclidean plane are determined by all Gaussian
section integrals at any nonzero bandwidth. -/
theorem eq_of_gaussian_integrals {σ : ℝ} (hσ : σ ≠ 0) (μ ν : Measure Plane)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ p : Plane,
      (∫ q, Real.exp (-‖p - q‖ ^ 2 / (2 * σ ^ 2)) ∂μ) =
        ∫ q, Real.exp (-‖p - q‖ ^ 2 / (2 * σ ^ 2)) ∂ν) : μ = ν := by
  let a : Plane → ℂ := fun ω => charFun μ (σ⁻¹ • ω)
  let b : Plane → ℂ := fun ω => charFun ν (σ⁻¹ • ω)
  let γ := stdGaussian Plane
  have ha : Continuous a := (continuous_charFun (μ := μ)).comp (by fun_prop)
  have hb : Continuous b := (continuous_charFun (μ := ν)).comp (by fun_prop)
  have hprod (ξ ζ : Measure Plane) [IsFiniteMeasure ξ] [IsFiniteMeasure ζ] :
      Integrable (fun ω => charFun ξ (σ⁻¹ • ω) * conj (charFun ζ (σ⁻¹ • ω))) γ := by
    apply bounded_continuous_integrable _ (by fun_prop) (ξ.real univ * ζ.real univ)
    intro ω
    rw [norm_mul, norm_conj]
    exact mul_le_mul (norm_charFun_le _) (norm_charFun_le _) (norm_nonneg _)
      (measureReal_nonneg (μ := ξ))
  have hcross (ξ : Measure Plane) [IsFiniteMeasure ξ] :
      (∫ ω, charFun ξ (σ⁻¹ • ω) * conj (a ω) ∂γ) =
        ∫ ω, charFun ξ (σ⁻¹ • ω) * conj (b ω) ∂γ := by
    rw [← spectral_cross, ← spectral_cross]
    apply integral_congr_ae
    filter_upwards [] with p
    simpa only [← integral_complex_ofReal] using congrArg Complex.ofReal (h p)
  have hzero : (∫ ω, (a ω - b ω) * conj (a ω - b ω) ∂γ) = 0 := by
    have hexpand : (fun ω => (a ω - b ω) * conj (a ω - b ω)) =
        fun ω => (a ω * conj (a ω) - a ω * conj (b ω)) -
          (b ω * conj (a ω) - b ω * conj (b ω)) := by
      funext ω
      rw [map_sub]
      ring
    rw [hexpand]
    dsimp only [a, b]
    simp only [a, b] at hcross
    have hout := integral_sub ((hprod μ μ).sub (hprod μ ν))
      ((hprod ν μ).sub (hprod ν ν))
    have hleft := integral_sub (hprod μ μ) (hprod μ ν)
    have hright := integral_sub (hprod ν μ) (hprod ν ν)
    simp only [Pi.sub_apply] at hout hleft hright
    rw [hout, hleft, hright, hcross μ, hcross ν]
    simp
  have hi : Integrable (fun ω => ‖a ω - b ω‖ ^ 2) γ := by
    apply (integrable_const ((μ.real univ + ν.real univ) ^ 2)).mono'
      ((ha.sub hb).norm.pow 2).stronglyMeasurable.aestronglyMeasurable
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    apply pow_le_pow_left₀ (norm_nonneg _) _ 2
    exact (norm_sub_le _ _).trans (add_le_add (norm_charFun_le _) (norm_charFun_le _))
  have hreal : (∫ ω, ‖a ω - b ω‖ ^ 2 ∂γ) = 0 := by
    have hcast : (fun ω => (a ω - b ω) * conj (a ω - b ω)) =
        fun ω => ((‖a ω - b ω‖ ^ 2 : ℝ) : ℂ) := by
      funext ω
      simpa only [Complex.ofReal_pow] using Complex.mul_conj' (a ω - b ω)
    rw [hcast, integral_complex_ofReal] at hzero
    exact_mod_cast hzero
  have hae : a =ᵐ[γ] b := by
    have hz := (integral_eq_zero_iff_of_nonneg_ae
      (Filter.Eventually.of_forall fun ω => sq_nonneg ‖a ω - b ω‖) hi).1 hreal
    filter_upwards [hz] with ω hω
    exact sub_eq_zero.1 (norm_eq_zero.1 (eq_zero_of_pow_eq_zero hω))
  have : γ.IsOpenPosMeasure := fullSupport
  have hab : a = b := Measure.eq_of_ae_eq hae ha hb
  apply Measure.ext_of_charFun
  funext t
  have ht := congrFun hab (σ • t)
  simpa [a, b, smul_smul, hσ] using ht

end TDA.Persistence.WeightedKernel.GaussianSpectral
