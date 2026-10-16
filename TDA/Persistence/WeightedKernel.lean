import TDA.Persistence.GaussianGram
import TDA.Persistence.PersistenceImage

/-!
# The weighted Gaussian kernel embedding of finite persistence diagrams

The birth–death Gaussian kernel generates a reproducing kernel Hilbert space through
mathlib's Moore construction `RKHS.OfKernel`. A finite occurrence family `x` with weight
`w` embeds as `Σ i, w (x i) • k_σ(·, x i)`. Inner products, norms and distances below
are those of `RKHS.OfKernel`; they are not defined by the Gram formula. The weight is the
persistence-image `Weight`, read in birth–persistence coordinates, so diagonal points
contribute nothing. Equal point values at distinct labels are summed repeatedly. The
finite part of a diagram is embedded and essential bars are omitted.

This RKHS norm is not the `PiLp 1` pixel norm of `PersistenceImage` and not an `L²`
persistence-surface norm; no identification between them is claimed.
Kusano–Fukumizu–Hiraoka, JMLR 18(189), 2018, §3.1 eq. (3), §3.3 eqs. (12), (13),
§4.1.3 and footnote 15.
-/

namespace TDA.Persistence.WeightedKernel

open Matrix
open scoped InnerProductSpace

/-! ## The scalar kernel as an operator-valued kernel -/

/-- The scalar kernel as an operator-valued matrix, as required by mathlib's RKHS API. -/
noncomputable def kernelOp (σ : ℝ) : Matrix (ℝ × ℝ) (ℝ × ℝ) (ℝ →L[ℝ] ℝ) :=
  Matrix.of fun p q => kernel σ p q • ContinuousLinearMap.id ℝ ℝ

theorem kernelOp_apply (σ : ℝ) (p q : ℝ × ℝ) (t : ℝ) :
    kernelOp σ p q t = kernel σ p q * t := rfl

theorem posSemidef_kernelOp (σ : ℝ) : (kernelOp σ).PosSemidef := by
  have hH : (kernelOp σ).IsHermitian := by
    refine Matrix.IsHermitian.ext fun p q => ?_
    ext
    simp [kernelOp, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_id,
      kernel_symm σ p q]
  have h3 : (kernelOp σ).IsHermitian ∧ ∀ vv : (ℝ × ℝ) →₀ ℝ,
      0 ≤ RCLike.re (vv.sum fun x t => vv.sum fun x' t' => ⟪kernelOp σ x' x t, t'⟫_ℝ) := by
    refine ⟨hH, fun vv => ?_⟩
    have h := (posSemidef_kernel σ).2 vv
    simp only [kernelOp_apply, RCLike.re_to_real, Real.inner_apply]
    refine h.trans_eq ?_
    simp only [Finsupp.sum, Matrix.of_apply, star_trivial]
    exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by
      rw [kernel_symm σ q p]
      ring
  exact (RKHS.posSemidef_tfae.out 2 0).mp h3

instance (σ : ℝ) : Fact (kernelOp σ).PosSemidef := ⟨posSemidef_kernelOp σ⟩

/-! ## The reproducing kernel Hilbert space and its kernel functions -/

/-- Mathlib's reproducing kernel Hilbert space of the birth–death Gaussian kernel. -/
abbrev Space (σ : ℝ) := RKHS.OfKernel (kernelOp σ)

/-- The kernel function `k_σ(·, p)`. -/
noncomputable def featureAt (σ : ℝ) (p : ℝ × ℝ) : Space σ := RKHS.kerFun (Space σ) p 1

theorem featureAt_apply (σ : ℝ) (p z : ℝ × ℝ) : featureAt σ p z = kernel σ z p := by
  rw [featureAt, RKHS.kerFun_apply, RKHS.OfKernel.kernel_ofKernel, kernelOp_apply, mul_one]

theorem inner_featureAt (σ : ℝ) (p q : ℝ × ℝ) :
    ⟪featureAt σ p, featureAt σ q⟫_ℝ = kernel σ p q := by
  change ⟪RKHS.kerFun (Space σ) p 1, featureAt σ q⟫_ℝ = _
  rw [RKHS.kerFun_inner, featureAt_apply, Real.inner_apply, one_mul]

theorem norm_featureAt (σ : ℝ) (p : ℝ × ℝ) : ‖featureAt σ p‖ = 1 := by
  have h := inner_featureAt σ p p
  rw [real_inner_self_eq_norm_sq, kernel_self] at h
  have h0 := norm_nonneg (featureAt σ p)
  nlinarith

/-! ## Weighted embeddings of occurrence families and diagrams -/

variable {I J : Type*} [Fintype I] [Fintype J] {A B : ℝ}

/-- Weighted kernel embedding `Σ i, w (x i) • k_σ(·, x i)` of an occurrence family. -/
noncomputable def embedding (σ : ℝ) (w : PersistenceImage.Weight A B) (x : I → ℝ × ℝ) :
    Space σ :=
  finiteFeatureSum (fun p => w (birthPersistence p) • featureAt σ p) x

/-- Embedding of the finite occurrences of a diagram; essential bars are omitted. -/
noncomputable def diagramEmbedding (σ : ℝ) (w : PersistenceImage.Weight A B)
    (D : Diagram ℝ) : Space σ :=
  embedding σ w (fun p : D.finiteOccurrences => p.1)

/-- Evaluation of the embedding, KFH18 eq. (3). -/
theorem embedding_apply (σ : ℝ) (w : PersistenceImage.Weight A B) (x : I → ℝ × ℝ)
    (z : ℝ × ℝ) :
    embedding σ w x z = ∑ i, w (birthPersistence (x i)) * kernel σ z (x i) := by
  rw [embedding, finiteFeatureSum, ← RKHS.coeCLM_apply (𝕜 := ℝ), map_sum,
    Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [RKHS.coeCLM_apply, RKHS.coe_smul, Pi.smul_apply, featureAt_apply, smul_eq_mul]

/-- The diagram embedding is the sum over the multiset of finite points. -/
theorem diagramEmbedding_eq_sum (σ : ℝ) (w : PersistenceImage.Weight A B) (D : Diagram ℝ) :
    diagramEmbedding σ w D =
      ((finitePart D.points).map fun p => w (birthPersistence p) • featureAt σ p).sum := by
  rw [diagramEmbedding, embedding, finiteFeatureSum, Finset.sum_eq_multiset_sum]
  exact congrArg Multiset.sum
    (Multiset.map_univ (finitePart D.points) fun p => w (birthPersistence p) • featureAt σ p)

/-- The linear kernel `Σ i, Σ j, w (x i) w (y j) k_σ(x i, y j)` of KFH18 eq. (12). -/
noncomputable def linearKernel (σ : ℝ) (w : PersistenceImage.Weight A B)
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) : ℝ :=
  ∑ i, ∑ j, w (birthPersistence (x i)) * w (birthPersistence (y j)) * kernel σ (x i) (y j)

/-- The RKHS inner product of two embeddings is the linear kernel, KFH18 eq. (12). -/
theorem inner_embedding (σ : ℝ) (w : PersistenceImage.Weight A B) (x : I → ℝ × ℝ)
    (y : J → ℝ × ℝ) :
    ⟪embedding σ w x, embedding σ w y⟫_ℝ = linearKernel σ w x y := by
  simp only [embedding, finiteFeatureSum, linearKernel, sum_inner, inner_sum,
    real_inner_smul_left, real_inner_smul_right, inner_featureAt]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- The squared RKHS distance of two embeddings, KFH18 §3.3. -/
theorem norm_embedding_sub_sq (σ : ℝ) (w : PersistenceImage.Weight A B) (x : I → ℝ × ℝ)
    (y : J → ℝ × ℝ) :
    ‖embedding σ w x - embedding σ w y‖ ^ 2 =
      linearKernel σ w x x + linearKernel σ w y y - 2 * linearKernel σ w x y := by
  rw [norm_sub_sq_real, ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
    inner_embedding, inner_embedding, inner_embedding]
  ring

theorem linearKernel_self_nonneg (σ : ℝ) (w : PersistenceImage.Weight A B)
    (x : I → ℝ × ℝ) : 0 ≤ linearKernel σ w x x := by
  rw [← inner_embedding]
  exact real_inner_self_nonneg

/-- The RKHS inner product of two diagram embeddings is the linear kernel of their finite
occurrences. -/
theorem inner_diagramEmbedding (σ : ℝ) (w : PersistenceImage.Weight A B) (D E : Diagram ℝ) :
    ⟪diagramEmbedding σ w D, diagramEmbedding σ w E⟫_ℝ =
      linearKernel σ w (fun p : D.finiteOccurrences => p.1)
        (fun p : E.finiteOccurrences => p.1) :=
  inner_embedding σ w _ _

/-! ## Diagram Gram matrices -/

/-- The linear diagram Gram matrix of any family of diagrams is positive semidefinite. -/
theorem posSemidef_linearDiagramGram {κ : Type*} (σ : ℝ) (w : PersistenceImage.Weight A B)
    (D : κ → Diagram ℝ) :
    (Matrix.of fun a b =>
      ⟪diagramEmbedding σ w (D a), diagramEmbedding σ w (D b)⟫_ℝ).PosSemidef :=
  posSemidef_innerKernel _

/-- The same matrix, with entries written as linear kernels of finite occurrences. -/
theorem posSemidef_linearKernelDiagramGram {κ : Type*} (σ : ℝ)
    (w : PersistenceImage.Weight A B) (D : κ → Diagram ℝ) :
    (Matrix.of fun a b => linearKernel σ w (fun p : (D a).finiteOccurrences => p.1)
      (fun p : (D b).finiteOccurrences => p.1)).PosSemidef := by
  simpa only [inner_diagramEmbedding] using posSemidef_linearDiagramGram σ w D

/-- The `(k, w)`-Gaussian diagram Gram matrix `exp (-‖E(D a) - E(D b)‖² / (2τ²))` of
KFH18 eq. (13) is positive semidefinite for every pair of real bandwidths. -/
theorem posSemidef_gaussianDiagramGram {κ : Type*} (σ τ : ℝ)
    (w : PersistenceImage.Weight A B) (D : κ → Diagram ℝ) :
    (gaussianGram τ fun a => diagramEmbedding σ w (D a)).PosSemidef :=
  posSemidef_gaussianGram τ _

end TDA.Persistence.WeightedKernel
