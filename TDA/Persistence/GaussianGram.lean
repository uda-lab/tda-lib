import Mathlib

/-!
# Positive semidefinite Gaussian Gram matrices over arbitrary index types

Positive semidefiniteness is mathlib's `Matrix.PosSemidef`, tested against finitely
supported coefficient vectors, so every statement holds for an arbitrary index type.
Entrywise powers follow from the Schur product theorem, the entrywise exponential from
its power series, and the Gaussian kernel from the factorization
`exp (-‖a - b‖² / (2σ²)) = exp (-‖a‖² / (2σ²)) exp (⟪a, b⟫ / σ²) exp (-‖b‖² / (2σ²))`.

The birth–death kernel uses the Euclidean squared distance of `WithLp 2 (ℝ × ℝ)`, not the
maximum norm carried by `ℝ × ℝ`. No hypothesis on the bandwidth `σ` is needed: at `σ = 0`
Lean's division gives the all-ones kernel, which is still positive semidefinite.
Kusano–Fukumizu–Hiraoka, JMLR 18(189), 2018, §2.3 and footnote 10.
-/

namespace TDA.Persistence.WeightedKernel

open Matrix
open scoped InnerProductSpace Nat

variable {ι : Type*}

/-- Real matrices: symmetry and the finitely supported quadratic form suffice. -/
private theorem posSemidef_of_real {M : Matrix ι ι ℝ} (hs : ∀ i j, M j i = M i j)
    (hq : ∀ x : ι →₀ ℝ, 0 ≤ x.sum fun i a => x.sum fun j b => a * M i j * b) :
    M.PosSemidef :=
  ⟨IsHermitian.ext fun i j => by simpa using hs i j, fun x => by simpa using hq x⟩

private theorem PosSemidef.real_symm {M : Matrix ι ι ℝ} (hM : M.PosSemidef) (i j : ι) :
    M j i = M i j := by
  simpa using hM.isHermitian.apply i j

private theorem PosSemidef.real_quad {M : Matrix ι ι ℝ} (hM : M.PosSemidef) (x : ι →₀ ℝ) :
    0 ≤ x.sum fun i a => x.sum fun j b => a * M i j * b := by
  simpa using hM.2 x

/-- The real inner-product kernel of any family is positive semidefinite, for an arbitrary
index type; mathlib's `Matrix.posSemidef_gram` is the finite-index case. -/
theorem posSemidef_innerKernel {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v : ι → E) : (Matrix.of fun i j => ⟪v i, v j⟫_ℝ).PosSemidef := by
  refine posSemidef_of_real (fun i j => by simp [real_inner_comm]) fun x => ?_
  have h : (x.sum fun i a => x.sum fun j b => a * (Matrix.of fun i j => ⟪v i, v j⟫_ℝ) i j * b) =
      ⟪x.sum fun i a => a • v i, x.sum fun j b => b • v j⟫_ℝ := by
    simp only [Finsupp.sum, sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right,
      Matrix.of_apply]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
      rw [real_inner_comm (v j) (v i)]
      ring
  rw [h]
  exact real_inner_self_nonneg

/-- Hadamard powers of a positive semidefinite real matrix; the zeroth power is the
all-ones matrix. -/
theorem posSemidef_map_pow {M : Matrix ι ι ℝ} (hM : M.PosSemidef) :
    ∀ n : ℕ, (M.map (· ^ n)).PosSemidef
  | 0 => by
    have h : M.map (· ^ 0) = Matrix.of fun (_ _ : ι) => ⟪(1 : ℝ), (1 : ℝ)⟫_ℝ := by
      ext i j
      simp
    rw [h]
    exact posSemidef_innerKernel fun _ => (1 : ℝ)
  | n + 1 => by
    have h : M.map (· ^ (n + 1)) = Matrix.hadamard (M.map (· ^ n)) M := by
      ext i j
      simp [pow_succ]
    rw [h]
    exact (posSemidef_map_pow hM n).hadamard hM

/-- The entrywise exponential of a positive semidefinite real matrix is positive
semidefinite. Each quadratic form is the sum of the exponential series of quadratic forms
of Hadamard powers. -/
theorem posSemidef_map_exp {M : Matrix ι ι ℝ} (hM : M.PosSemidef) :
    (M.map Real.exp).PosSemidef := by
  refine posSemidef_of_real (fun i j => by simp [PosSemidef.real_symm hM i j]) fun x => ?_
  have hterm : ∀ i j, HasSum (fun n : ℕ => x i * (M i j ^ n / n !) * x j)
      (x i * Real.exp (M i j) * x j) := by
    intro i j
    have h := NormedSpace.expSeries_div_hasSum_exp (M i j)
    rw [← congrFun Real.exp_eq_exp_ℝ] at h
    exact (h.mul_left (x i)).mul_right (x j)
  have hsum : HasSum
      (fun n : ℕ => x.sum fun i a => x.sum fun j b => a * (M i j ^ n / n !) * b)
      (x.sum fun i a => x.sum fun j b => a * M.map Real.exp i j * b) := by
    simp only [Finsupp.sum, Matrix.map_apply]
    exact hasSum_sum fun i _ => hasSum_sum fun j _ => hterm i j
  refine hsum.nonneg fun n => ?_
  have hn := PosSemidef.real_quad
    ((posSemidef_map_pow hM n).smul (a := ((n ! : ℝ)⁻¹)) (by positivity)) x
  refine hn.trans_eq ?_
  simp only [Finsupp.sum, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- Rescaling rows and columns by the same real vector preserves positive semidefiniteness.
The rescaled matrix is the Hadamard product with the rank-one kernel of `d`. -/
theorem posSemidef_diag_mul_mul_diag {M : Matrix ι ι ℝ} (hM : M.PosSemidef) (d : ι → ℝ) :
    (Matrix.of fun i j => d i * M i j * d j).PosSemidef := by
  have heq : (Matrix.of fun i j => d i * M i j * d j) =
      Matrix.hadamard (Matrix.of fun i j => ⟪d i, d j⟫_ℝ) M := by
    ext i j
    simp only [Matrix.of_apply, Matrix.hadamard_apply, Real.inner_apply]
    ring
  rw [heq]
  exact (posSemidef_innerKernel d).hadamard hM

section Gaussian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Gaussian Gram matrix `exp (-‖v i - v j‖² / (2σ²))` of a family in a real inner
product space. -/
noncomputable def gaussianGram (σ : ℝ) (v : ι → E) : Matrix ι ι ℝ :=
  Matrix.of fun i j => Real.exp (-‖v i - v j‖ ^ 2 / (2 * σ ^ 2))

/-- The Gaussian Gram matrix is positive semidefinite for every real bandwidth. -/
theorem posSemidef_gaussianGram (σ : ℝ) (v : ι → E) : (gaussianGram σ v).PosSemidef := by
  have hc : (0 : ℝ) ≤ 2 * (2 * σ ^ 2)⁻¹ := by positivity
  have h := posSemidef_diag_mul_mul_diag
    (posSemidef_map_exp ((posSemidef_innerKernel v).smul hc))
    (fun i => Real.exp (-(2 * σ ^ 2)⁻¹ * ‖v i‖ ^ 2))
  convert h using 1
  ext i j
  simp only [gaussianGram, Matrix.of_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul,
    ← Real.exp_add]
  congr 1
  rw [norm_sub_sq_real]
  ring

end Gaussian

/-! ## The birth–death Gaussian kernel -/

/-- Gaussian kernel on birth–death points with the Euclidean squared distance. -/
noncomputable def kernel (σ : ℝ) (p q : ℝ × ℝ) : ℝ :=
  Real.exp (-((p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2) / (2 * σ ^ 2))

/-- The kernel is the Gaussian of the Euclidean norm on `WithLp 2 (ℝ × ℝ)`. -/
theorem kernel_eq_gaussian (σ : ℝ) (p q : ℝ × ℝ) :
    kernel σ p q =
      Real.exp (-‖WithLp.toLp 2 p - WithLp.toLp 2 q‖ ^ 2 / (2 * σ ^ 2)) := by
  rw [kernel, WithLp.prod_norm_sq_eq_of_L2]
  simp [Real.norm_eq_abs, sq_abs]

theorem kernel_symm (σ : ℝ) (p q : ℝ × ℝ) : kernel σ p q = kernel σ q p := by
  simp only [kernel]
  congr 1
  ring

@[simp] theorem kernel_self (σ : ℝ) (p : ℝ × ℝ) : kernel σ p p = 1 := by
  simp [kernel]

theorem kernel_pos (σ : ℝ) (p q : ℝ × ℝ) : 0 < kernel σ p q := Real.exp_pos _

theorem kernel_le_one (σ : ℝ) (p q : ℝ × ℝ) : kernel σ p q ≤ 1 := by
  refine Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg ?_ (by positivity))
  exact neg_nonpos.mpr (by positivity)

/-- The birth–death Gaussian kernel is positive semidefinite on the whole plane. -/
theorem posSemidef_kernel (σ : ℝ) :
    (Matrix.of (kernel σ) : Matrix (ℝ × ℝ) (ℝ × ℝ) ℝ).PosSemidef := by
  have h := posSemidef_gaussianGram σ (WithLp.toLp 2 : ℝ × ℝ → WithLp 2 (ℝ × ℝ))
  convert h using 1
  ext p q
  simp only [Matrix.of_apply, gaussianGram, kernel_eq_gaussian]

/-- The kernel matrix of every occurrence family is positive semidefinite; equal points
at distinct labels are kept. -/
theorem posSemidef_kernel_family {I : Type*} (σ : ℝ) (x : I → ℝ × ℝ) :
    (Matrix.of fun i j => kernel σ (x i) (x j)).PosSemidef :=
  (posSemidef_kernel σ).submatrix x

end TDA.Persistence.WeightedKernel
