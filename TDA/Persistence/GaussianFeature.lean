import TDA.Persistence.GaussianGram

/-!
# Gaussian kernel functions and their distance bound

Two unit vectors whose inner product is `exp (-r² / (2s²))` are at distance at most
`|r| / |s|`. This is the abstract content of Kusano–Fukumizu–Hiraoka, JMLR 18(189), 2018,
Appendix C, Lemma 16, eq. (25): it uses only `1 - e^{-t} ≤ t`. Both the birth–death
feature bound and the second-level bound for the Gaussian kernel on an RKHS are instances.

The Gaussian kernel of an arbitrary real inner product space `E` generates mathlib's RKHS
`RKHS.OfKernel`. Its kernel functions have unit norm and Gaussian inner products. With
Lean's division the bandwidth needs no sign hypothesis; at bandwidth zero all kernel
functions coincide and every bound reads `0 ≤ 0`.
-/

namespace TDA.Persistence.WeightedKernel

open Matrix
open scoped InnerProductSpace

/-! ## The scalar inequality and the unit-vector lemma -/

/-- `2 - 2 exp (-r² / (2s²)) ≤ r² / s²`, from `1 - t ≤ exp (-t)`. Both sides vanish at
`s = 0`. -/
theorem two_sub_two_mul_exp_le (r s : ℝ) :
    2 - 2 * Real.exp (-r ^ 2 / (2 * s ^ 2)) ≤ r ^ 2 / s ^ 2 := by
  rcases eq_or_ne s 0 with rfl | _
  · norm_num
  · have h := Real.add_one_le_exp (-(r ^ 2 / s ^ 2) / 2)
    have he : -r ^ 2 / (2 * s ^ 2) = -(r ^ 2 / s ^ 2) / 2 := by ring
    rw [he]
    linarith

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The squared distance of two unit vectors with a Gaussian inner product. -/
theorem norm_sub_sq_eq_of_inner_eq_gaussian {u v : H} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    {r s : ℝ} (huv : ⟪u, v⟫_ℝ = Real.exp (-r ^ 2 / (2 * s ^ 2))) :
    ‖u - v‖ ^ 2 = 2 - 2 * Real.exp (-r ^ 2 / (2 * s ^ 2)) := by
  rw [norm_sub_sq_real, hu, hv, huv]
  ring

/-- Gaussian unit-vector lemma, KFH18 Lemma 16, eq. (25), in an arbitrary real inner
product space. -/
theorem norm_sub_le_of_inner_eq_gaussian {u v : H} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    {r s : ℝ} (huv : ⟪u, v⟫_ℝ = Real.exp (-r ^ 2 / (2 * s ^ 2))) :
    ‖u - v‖ ≤ |r| / |s| := by
  have hsq : (|r| / |s|) ^ 2 = r ^ 2 / s ^ 2 := by rw [div_pow, sq_abs, sq_abs]
  have hle : ‖u - v‖ ^ 2 ≤ (|r| / |s|) ^ 2 := by
    rw [norm_sub_sq_eq_of_inner_eq_gaussian hu hv huv, hsq]
    exact two_sub_two_mul_exp_le r s
  exact (sq_le_sq₀ (norm_nonneg _) (div_nonneg (abs_nonneg _) (abs_nonneg _))).mp hle

/-! ## Scalar kernels as operator-valued kernels -/

/-- A positive semidefinite scalar kernel on an arbitrary type, times the identity, is a
positive semidefinite operator-valued kernel in the sense of mathlib's RKHS API. -/
theorem posSemidef_scalarOp {X : Type*} {k : Matrix X X ℝ} (hk : k.PosSemidef) :
    (Matrix.of fun x y => k x y • ContinuousLinearMap.id ℝ ℝ).PosSemidef := by
  have hsymm (x y : X) : k x y = k y x := by
    simpa using hk.isHermitian.apply y x
  have hH : (Matrix.of fun x y => k x y • ContinuousLinearMap.id ℝ ℝ).IsHermitian := by
    refine Matrix.IsHermitian.ext fun x y => ?_
    ext
    simp [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_id, hsymm x y]
  have h3 : (Matrix.of fun x y => k x y • ContinuousLinearMap.id ℝ ℝ).IsHermitian ∧
      ∀ vv : X →₀ ℝ, 0 ≤ RCLike.re (vv.sum fun x t => vv.sum fun x' t' =>
        ⟪(Matrix.of fun x y => k x y • ContinuousLinearMap.id ℝ ℝ) x' x t, t'⟫_ℝ) := by
    refine ⟨hH, fun vv => ?_⟩
    have h := hk.2 vv
    simp only [Matrix.of_apply, _root_.smul_apply, ContinuousLinearMap.id_apply,
      smul_eq_mul, RCLike.re_to_real, Real.inner_apply]
    refine h.trans_eq ?_
    simp only [Finsupp.sum, star_trivial]
    exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by
      rw [hsymm q p]
      ring
  exact (RKHS.posSemidef_tfae.out 2 0).mp h3

/-! ## The Gaussian RKHS of a real inner product space -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The Gaussian kernel `exp (-‖a - b‖² / (2τ²))` on all of `E`, operator-valued. -/
noncomputable def gaussianKernelOp (τ : ℝ) : Matrix E E (ℝ →L[ℝ] ℝ) :=
  Matrix.of fun a b => gaussianGram τ (id : E → E) a b • ContinuousLinearMap.id ℝ ℝ

omit [InnerProductSpace ℝ E] in
theorem gaussianKernelOp_apply (τ : ℝ) (a b : E) (t : ℝ) :
    gaussianKernelOp τ a b t = Real.exp (-‖a - b‖ ^ 2 / (2 * τ ^ 2)) * t := rfl

theorem posSemidef_gaussianKernelOp (τ : ℝ) : (gaussianKernelOp (E := E) τ).PosSemidef :=
  posSemidef_scalarOp (posSemidef_gaussianGram τ id)

instance fact_posSemidef_gaussianKernelOp (τ : ℝ) :
    Fact (gaussianKernelOp (E := E) τ).PosSemidef :=
  ⟨posSemidef_gaussianKernelOp τ⟩

/-- Mathlib's reproducing kernel Hilbert space of the Gaussian kernel on `E`. -/
abbrev GaussianSpace (τ : ℝ) (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] :=
  RKHS.OfKernel (gaussianKernelOp (E := E) τ)

/-- The Gaussian kernel function `ψ_τ(a) = exp (-‖· - a‖² / (2τ²))`. -/
noncomputable def gaussianFeature (τ : ℝ) (a : E) : GaussianSpace τ E :=
  RKHS.kerFun (GaussianSpace τ E) a 1

theorem gaussianFeature_apply (τ : ℝ) (a z : E) :
    gaussianFeature τ a z = Real.exp (-‖z - a‖ ^ 2 / (2 * τ ^ 2)) := by
  rw [gaussianFeature, RKHS.kerFun_apply, RKHS.OfKernel.kernel_ofKernel,
    gaussianKernelOp_apply, mul_one]

theorem inner_gaussianFeature (τ : ℝ) (a b : E) :
    ⟪gaussianFeature τ a, gaussianFeature τ b⟫_ℝ = Real.exp (-‖a - b‖ ^ 2 / (2 * τ ^ 2)) := by
  change ⟪RKHS.kerFun (GaussianSpace τ E) a 1, gaussianFeature τ b⟫_ℝ = _
  rw [RKHS.kerFun_inner, gaussianFeature_apply, Real.inner_apply, one_mul]

theorem norm_gaussianFeature (τ : ℝ) (a : E) : ‖gaussianFeature τ a‖ = 1 := by
  have h := inner_gaussianFeature τ a a
  rw [real_inner_self_eq_norm_sq, sub_self, norm_zero] at h
  norm_num at h
  rcases h with h | h
  · exact h
  · linarith [norm_nonneg (gaussianFeature τ a)]

/-- Distance of Gaussian kernel functions: `‖ψ_τ(a) - ψ_τ(b)‖ ≤ ‖a - b‖ / |τ|`. -/
theorem norm_gaussianFeature_sub_le (τ : ℝ) (a b : E) :
    ‖gaussianFeature τ a - gaussianFeature τ b‖ ≤ ‖a - b‖ / |τ| := by
  have h := norm_sub_le_of_inner_eq_gaussian (norm_gaussianFeature τ a)
    (norm_gaussianFeature τ b) (inner_gaussianFeature τ a b)
  rwa [abs_of_nonneg (norm_nonneg _)] at h

end TDA.Persistence.WeightedKernel
