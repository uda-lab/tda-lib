import TDA.Probability.FiniteTotalVariation
import TDA.Probability.GromovWasserstein

/-!
# Finite total variation controls distortion Gromov–Wasserstein

For two probability laws on one finite metric carrier of diameter at most `D`,
the maximal coupling has a nonzero distortion only when at least one of its
independent draws mismatches. Its probability is bounded by twice total
variation. The Gromov–Wasserstein convention includes a factor one half.
-/

noncomputable section

universe u
namespace TDA.Probability

open scoped ENNReal NNReal Classical

variable {X : Type u} [Fintype X] [MetricSpace X]

omit [Fintype X] in
private theorem distortion_le_diameter (D : ℝ≥0)
    (hD : ∀ x y : X, dist x y ≤ (D : ℝ)) (a b : X × X) :
    distortion a b ≤ (D : ℝ≥0∞) := by
  have h : |dist a.1 b.1 - dist a.2 b.2| ≤ (D : ℝ) := by
    apply abs_le.mpr
    constructor
    · linarith [dist_nonneg (x := a.1) (y := b.1), hD a.2 b.2]
    · linarith [dist_nonneg (x := a.2) (y := b.2), hD a.1 b.1]
  exact (ENNReal.ofReal_le_ofReal h).trans_eq (by simp)

omit [Fintype X] in
private theorem distortion_rpow_le_mismatch (D : ℝ≥0)
    (hD : ∀ x y : X, dist x y ≤ (D : ℝ)) {p : ℝ} (hp : 0 < p)
    (a b : X × X) :
    distortion a b ^ p ≤ (D : ℝ≥0∞) ^ p *
      ((if a.1 = a.2 then 0 else 1) + (if b.1 = b.2 then 0 else 1)) := by
  have h := ENNReal.rpow_le_rpow (distortion_le_diameter D hD a b) hp.le
  by_cases ha : a.1 = a.2
  · by_cases hb : b.1 = b.2
    · simp [distortion, ha, hb, ENNReal.zero_rpow_of_pos hp]
    · simpa [ha, hb] using h
  · by_cases hb : b.1 = b.2
    · simpa [ha, hb] using h
    · simp only [ha, hb, if_false]
      exact h.trans (le_mul_of_one_le_right' (by norm_num))

omit [Fintype X] [MetricSpace X] in
private theorem expectation_const_mul (ρ : PMF (X × X)) (c : ℝ≥0∞)
    (f : X × X → ℝ≥0∞) :
    expectation ρ (fun x => c * f x) = c * expectation ρ f := by
  simp only [expectation, mul_left_comm (ρ _) c, ENNReal.tsum_mul_left]

/-- The explicit maximal coupling has distortion moment at most the diameter
power times twice the mismatch probability. -/
theorem maximalCoupling_distortionMoment_le (μ ν : PMF X) (D : ℝ≥0)
    (hD : ∀ x y : X, dist x y ≤ (D : ℝ)) {p : ℝ} (hp : 0 < p) :
    (maximalCoupling μ ν).distortionMoment p ≤
      (D : ℝ≥0∞) ^ p * (2 * finiteTotalVariation μ ν) := by
  let π := maximalCoupling μ ν
  let e : X × X → ℝ≥0∞ := fun a => if a.1 = a.2 then 0 else 1
  have he : expectation π.joint e = finiteTotalVariation μ ν :=
    maximalCoupling_mismatch μ ν
  calc
    π.distortionMoment p ≤ expectation π.joint (fun a =>
        expectation π.joint (fun b => (D : ℝ≥0∞) ^ p * (e a + e b))) := by
      apply expectation_mono
      intro a
      apply expectation_mono
      exact distortion_rpow_le_mismatch D hD hp a
    _ = (D : ℝ≥0∞) ^ p * (2 * finiteTotalVariation μ ν) := by
      simp only [expectation_const_mul, expectation_add, expectation_const]
      rw [he]
      simp only [← two_mul]

/-- Total variation bounds finite-p distortion GW on a finite metric carrier.
No atom is required to have positive mass, and no optimizer is assumed. -/
theorem two_mul_gromovWasserstein_le_finiteTotalVariation (μ ν : PMF X) (D : ℝ≥0)
    (hD : ∀ x y : X, dist x y ≤ (D : ℝ)) {p : ℝ} (hp : 0 < p) :
    2 * gromovWasserstein p μ ν ≤
      (D : ℝ≥0∞) * (2 * finiteTotalVariation μ ν) ^ p⁻¹ := by
  have hGW : 2 * gromovWasserstein p μ ν =
      ⨅ π : Coupling μ ν, π.distortionMoment p ^ p⁻¹ := by
    simp only [gromovWasserstein, ← mul_assoc]
    rw [ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
  rw [hGW]
  calc
    (⨅ π : Coupling μ ν, π.distortionMoment p ^ p⁻¹) ≤
        (maximalCoupling μ ν).distortionMoment p ^ p⁻¹ :=
      iInf_le (fun π : Coupling μ ν => π.distortionMoment p ^ p⁻¹) (maximalCoupling μ ν)
    _ ≤ ((D : ℝ≥0∞) ^ p * (2 * finiteTotalVariation μ ν)) ^ p⁻¹ :=
      ENNReal.rpow_le_rpow (maximalCoupling_distortionMoment_le μ ν D hD hp)
        (inv_nonneg.mpr hp.le)
    _ = (D : ℝ≥0∞) * (2 * finiteTotalVariation μ ν) ^ p⁻¹ := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (inv_nonneg.mpr hp.le),
        ← ENNReal.rpow_mul, mul_inv_cancel₀ hp.ne', ENNReal.rpow_one]

end TDA.Probability
