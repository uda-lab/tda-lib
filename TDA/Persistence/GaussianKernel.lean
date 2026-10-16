import TDA.Persistence.AdditiveFeatures

/-!
# Gaussian densities for persistence images

The one-dimensional density is mathlib's Gaussian density at variance `σ²`.
Translation is bounded in L¹ by splitting at the midpoint of the centers and
integrating the density over the interval between the shifted cutoffs. This proves
the analytic estimate rather than assuming it as a feature-map hypothesis.
-/

namespace TDA.Persistence.GaussianKernel

open MeasureTheory Set

/-- Normalized one-dimensional Gaussian with bandwidth `σ` and center `u`. -/
noncomputable def density1D (σ u x : ℝ) : ℝ :=
  ProbabilityTheory.gaussianPDFReal u ⟨σ ^ 2, sq_nonneg σ⟩ x

/-- Maximum value of the one-dimensional density. -/
noncomputable def peak (σ : ℝ) : ℝ := (Real.sqrt (2 * Real.pi * σ ^ 2))⁻¹

theorem density1D_nonneg (σ u x : ℝ) : 0 ≤ density1D σ u x :=
  ProbabilityTheory.gaussianPDFReal_nonneg _ _ _

theorem density1D_formula {σ : ℝ} (hσ : 0 < σ) (u x : ℝ) :
    density1D σ u x = (σ * Real.sqrt (2 * Real.pi))⁻¹ *
      Real.exp (-(x - u) ^ 2 / (2 * σ ^ 2)) := by
  change (Real.sqrt (2 * Real.pi * σ ^ 2))⁻¹ *
    Real.exp (-(x - u) ^ 2 / (2 * σ ^ 2)) = _
  rw [Real.sqrt_mul (show 0 ≤ 2 * Real.pi by positivity),
    Real.sqrt_sq_eq_abs, abs_of_pos hσ, mul_comm (Real.sqrt (2 * Real.pi)) σ]

theorem integrable_density1D (σ u : ℝ) : Integrable (density1D σ u) :=
  ProbabilityTheory.integrable_gaussianPDFReal _ _

theorem integral_density1D {σ : ℝ} (hσ : 0 < σ) (u : ℝ) :
    ∫ x, density1D σ u x = 1 := by
  apply ProbabilityTheory.integral_gaussianPDFReal_eq_one
  have h : (0 : NNReal) < ⟨σ ^ 2, sq_nonneg σ⟩ := by
    exact_mod_cast sq_pos_of_pos hσ
  exact ne_of_gt h

theorem peak_nonneg (σ : ℝ) : 0 ≤ peak σ := by unfold peak; positivity

theorem density1D_le_peak (σ u x : ℝ) : density1D σ u x ≤ peak σ := by
  change peak σ * Real.exp (-(x - u) ^ 2 / (2 * σ ^ 2)) ≤ peak σ
  have he : Real.exp (-(x - u) ^ 2 / (2 * σ ^ 2)) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (by positivity)
  simpa using mul_le_mul_of_nonneg_left he (peak_nonneg σ)

private theorem density1D_le_of_sq {σ u v x : ℝ} (hσ : 0 < σ)
    (h : (x - v) ^ 2 ≤ (x - u) ^ 2) : density1D σ u x ≤ density1D σ v x := by
  change peak σ * Real.exp (-(x - u) ^ 2 / (2 * σ ^ 2)) ≤
    peak σ * Real.exp (-(x - v) ^ 2 / (2 * σ ^ 2))
  apply mul_le_mul_of_nonneg_left _ (peak_nonneg σ)
  apply Real.exp_le_exp.mpr
  apply (div_le_div_iff_of_pos_right (by positivity : 0 < 2 * σ ^ 2)).2
  linarith

private theorem integral_Iic_comp_sub (f : ℝ → ℝ) (a u : ℝ) :
    (∫ x in Iic a, f (x - u)) = ∫ x in Iic (a - u), f x := by
  calc
    _ = ∫ x, (Iic a).indicator (fun x => f (x - u)) x :=
      (integral_indicator measurableSet_Iic).symm
    _ = ∫ x, (Iic a).indicator (fun x => f (x - u)) (x + u) :=
      (integral_add_right_eq_self _ u).symm
    _ = ∫ x, (Iic (a - u)).indicator f x := by
      apply integral_congr_ae
      filter_upwards [] with x
      have h : x + u ≤ a ↔ x ≤ a - u := by constructor <;> intro h <;> linarith
      simp only [indicator_apply, mem_Iic, h, add_sub_cancel_right]
    _ = _ := integral_indicator measurableSet_Iic

private theorem integral_Iic_density1D (σ u a : ℝ) :
    (∫ x in Iic a, density1D σ u x) = ∫ x in Iic (a - u), density1D σ 0 x := by
  have h : density1D σ u = fun x => density1D σ 0 (x - u) := by
    funext x
    simp [density1D, ProbabilityTheory.gaussianPDFReal]
  rw [h]
  exact integral_Iic_comp_sub _ _ _

private theorem integral_abs_sub_of_le {σ u v : ℝ} (hσ : 0 < σ) (huv : u ≤ v) :
    (∫ x, |density1D σ u x - density1D σ v x|) ≤ 2 * peak σ * (v - u) := by
  let m := (u + v) / 2
  have hu := integrable_density1D σ u
  have hv := integrable_density1D σ v
  have hd : Integrable (fun x => density1D σ u x - density1D σ v x) := hu.sub hv
  have habs : Integrable (fun x => |density1D σ u x - density1D σ v x|) := hd.abs
  have hleft (x : ℝ) (hx : x ∈ Iic m) : density1D σ v x ≤ density1D σ u x := by
    apply density1D_le_of_sq hσ
    have hm : 0 ≤ u + v - 2 * x := by
      change x ≤ (u + v) / 2 at hx
      linarith
    nlinarith [mul_nonneg (sub_nonneg.mpr huv) hm]
  have hright (x : ℝ) (hx : x ∈ Ioi m) : density1D σ u x ≤ density1D σ v x := by
    apply density1D_le_of_sq hσ
    have hm : 0 ≤ 2 * x - u - v := by
      change (u + v) / 2 < x at hx
      linarith
    nlinarith [mul_nonneg (sub_nonneg.mpr huv) hm]
  have hl : (∫ x in Iic m, |density1D σ u x - density1D σ v x|) =
      ∫ x in Iic m, density1D σ u x - density1D σ v x := by
    apply setIntegral_congr_fun measurableSet_Iic
    intro x hx
    exact abs_of_nonneg (sub_nonneg.mpr (hleft x hx))
  have hr : (∫ x in Ioi m, |density1D σ u x - density1D σ v x|) =
      -(∫ x in Ioi m, density1D σ u x - density1D σ v x) := by
    rw [← integral_neg]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    exact abs_of_nonpos (sub_nonpos.mpr (hright x hx))
  have hz : (∫ x in Iic m, density1D σ u x - density1D σ v x) +
      (∫ x in Ioi m, density1D σ u x - density1D σ v x) = 0 := by
    rw [intervalIntegral.integral_Iic_add_Ioi hd.integrableOn hd.integrableOn,
      integral_sub hu hv, integral_density1D hσ, integral_density1D hσ, sub_self]
  have hsplit : (∫ x, |density1D σ u x - density1D σ v x|) =
      2 * (∫ x in Iic m, density1D σ u x - density1D σ v x) := by
    rw [← intervalIntegral.integral_Iic_add_Ioi habs.integrableOn habs.integrableOn,
      hl, hr]
    linarith
  have hinterval : (∫ x in Iic m, density1D σ u x - density1D σ v x) =
      ∫ x in (m - v)..(m - u), density1D σ 0 x := by
    rw [integral_sub hu.integrableOn hv.integrableOn,
      integral_Iic_density1D σ u m, integral_Iic_density1D σ v m]
    exact intervalIntegral.integral_Iic_sub_Iic
      (integrable_density1D σ 0).integrableOn (integrable_density1D σ 0).integrableOn
  have hb : (∫ x in (m - v)..(m - u), density1D σ 0 x) ≤ peak σ * (v - u) := by
    have h := intervalIntegral.integral_mono_on (show m - v ≤ m - u by linarith)
      (integrable_density1D σ 0).intervalIntegrable (intervalIntegrable_const)
      (fun x _ => density1D_le_peak σ 0 x)
    simpa [intervalIntegral.integral_const, smul_eq_mul, mul_comm] using h
  rw [hsplit, hinterval]
  linarith

/-- Translation in one dimension, with twice the density maximum as constant. -/
theorem integral_abs_density1D_sub_le {σ : ℝ} (hσ : 0 < σ) (u v : ℝ) :
    (∫ x, |density1D σ u x - density1D σ v x|) ≤ 2 * peak σ * |u - v| := by
  rcases le_total u v with huv | hvu
  · simpa [abs_of_nonpos (sub_nonpos.mpr huv)] using integral_abs_sub_of_le hσ huv
  · have h := integral_abs_sub_of_le hσ hvu
    simpa only [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hvu)] using h

/-- The translation coefficient in terms of bandwidth, rather than variance. -/
noncomputable def translationConstant (σ : ℝ) : ℝ := Real.sqrt (2 / Real.pi) / σ

theorem translationConstant_nonneg {σ : ℝ} (hσ : 0 < σ) :
    0 ≤ translationConstant σ := by unfold translationConstant; positivity

theorem two_mul_peak {σ : ℝ} (hσ : 0 < σ) :
    2 * peak σ = translationConstant σ := by
  unfold peak translationConstant
  rw [Real.sqrt_mul (show 0 ≤ 2 * Real.pi by positivity),
    Real.sqrt_sq_eq_abs, abs_of_pos hσ,
    Real.sqrt_mul (show (0 : ℝ) ≤ 2 by norm_num),
    Real.sqrt_div (show (0 : ℝ) ≤ 2 by norm_num)]
  have h₂ : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  have hπ : Real.sqrt Real.pi ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr Real.pi_pos)
  field_simp
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

/-- Normalized isotropic product Gaussian on the Lebesgue plane. -/
noncomputable def density2D (σ : ℝ) (u z : ℝ × ℝ) : ℝ :=
  density1D σ u.1 z.1 * density1D σ u.2 z.2

theorem density2D_nonneg (σ : ℝ) (u z : ℝ × ℝ) : 0 ≤ density2D σ u z :=
  mul_nonneg (density1D_nonneg _ _ _) (density1D_nonneg _ _ _)

theorem integrable_density2D (σ : ℝ) (u : ℝ × ℝ) : Integrable (density2D σ u) :=
  (integrable_density1D σ u.1).mul_prod (integrable_density1D σ u.2)

theorem integral_density2D {σ : ℝ} (hσ : 0 < σ) (u : ℝ × ℝ) :
    ∫ z, density2D σ u z = 1 := by
  change (∫ z, density1D σ u.1 z.1 * density1D σ u.2 z.2
    ∂(volume.prod volume)) = 1
  rw [integral_prod_mul, integral_density1D hσ, integral_density1D hσ, one_mul]

/-- L¹ translation is controlled by coordinate ℓ¹ displacement of the centers.
This does not use the default maximum norm on the real product. -/
theorem integral_abs_density2D_sub_le {σ : ℝ} (hσ : 0 < σ) (u v : ℝ × ℝ) :
    (∫ z, |density2D σ u z - density2D σ v z|) ≤
      translationConstant σ * (|u.1 - v.1| + |u.2 - v.2|) := by
  have h₁ := (integrable_density1D σ u.1).sub (integrable_density1D σ v.1)
  have h₂ := (integrable_density1D σ u.2).sub (integrable_density1D σ v.2)
  have ha : Integrable (fun z : ℝ × ℝ =>
      |density1D σ u.1 z.1 - density1D σ v.1 z.1| * density1D σ u.2 z.2) :=
    h₁.abs.mul_prod (integrable_density1D σ u.2)
  have hb : Integrable (fun z : ℝ × ℝ =>
      density1D σ v.1 z.1 * |density1D σ u.2 z.2 - density1D σ v.2 z.2|) :=
    (integrable_density1D σ v.1).mul_prod h₂.abs
  have hd : Integrable (fun z => density2D σ u z - density2D σ v z) :=
    (integrable_density2D σ u).sub (integrable_density2D σ v)
  have hp (z : ℝ × ℝ) : |density2D σ u z - density2D σ v z| ≤
      |density1D σ u.1 z.1 - density1D σ v.1 z.1| * density1D σ u.2 z.2 +
      density1D σ v.1 z.1 * |density1D σ u.2 z.2 - density1D σ v.2 z.2| := by
    have he : density2D σ u z - density2D σ v z =
        (density1D σ u.1 z.1 - density1D σ v.1 z.1) * density1D σ u.2 z.2 +
        density1D σ v.1 z.1 * (density1D σ u.2 z.2 - density1D σ v.2 z.2) := by
      unfold density2D
      ring
    rw [he]
    simpa only [abs_mul, abs_of_nonneg (density1D_nonneg σ u.2 z.2),
      abs_of_nonneg (density1D_nonneg σ v.1 z.1)] using abs_add_le
      ((density1D σ u.1 z.1 - density1D σ v.1 z.1) * density1D σ u.2 z.2)
      (density1D σ v.1 z.1 * (density1D σ u.2 z.2 - density1D σ v.2 z.2))
  have hi := integral_mono hd.abs (ha.add hb) hp
  simp only [Pi.add_apply] at hi
  rw [integral_add ha hb] at hi
  simp only [Measure.volume_eq_prod] at hi
  rw [integral_prod_mul (fun x => |density1D σ u.1 x - density1D σ v.1 x|)
      (density1D σ u.2),
    integral_prod_mul (density1D σ v.1)
      (fun x => |density1D σ u.2 x - density1D σ v.2 x|),
    integral_density1D hσ, integral_density1D hσ, mul_one, one_mul] at hi
  calc
    _ ≤ (∫ x, |density1D σ u.1 x - density1D σ v.1 x|) +
        (∫ x, |density1D σ u.2 x - density1D σ v.2 x|) := hi
    _ ≤ 2 * peak σ * |u.1 - v.1| + 2 * peak σ * |u.2 - v.2| :=
      add_le_add (integral_abs_density1D_sub_le hσ _ _)
        (integral_abs_density1D_sub_le hσ _ _)
    _ = _ := by rw [two_mul_peak hσ]; ring

end TDA.Persistence.GaussianKernel
