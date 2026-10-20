import TDA.Persistence.WeightedKernelStability
import TDA.Persistence.WeightedKernelInjectivity
import TDA.Persistence.GaussianSpectralSeparation
import Mathlib.MeasureTheory.VectorMeasure.Integral
import Mathlib.MeasureTheory.VectorMeasure.Variation.SignedMeasure
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Gaussian embeddings of finite signed measures

The embedding uses the vector-measure integral of the existing Gaussian RKHS
feature. Its integrability follows from continuity and the feature's unit norm.
The Jordan formula is a theorem about this integral, rather than its definition.
-/

noncomputable section

namespace TDA.Persistence.WeightedKernel

open MeasureTheory
open scoped InnerProductSpace

/-- The actual Gaussian feature map is continuous, including the library's zero-bandwidth
convention. -/
theorem continuous_featureAt (σ : ℝ) : Continuous (featureAt σ) := by
  apply (LipschitzWith.of_dist_le' (K := Real.sqrt 2 / |σ|) ?_).continuous
  intro p q
  simpa only [dist_eq_norm] using norm_featureAt_sub_le σ p q

private theorem inner_featureAt_left (σ : ℝ) (f : Space σ) (p : ℝ × ℝ) :
    ⟪featureAt σ p, f⟫_ℝ = f p := by
  simp [featureAt, RKHS.kerFun_inner]

/-- Every actual Gaussian RKHS function is continuous on the plane. -/
theorem continuous_rkhsFunction (σ : ℝ) (f : Space σ) : Continuous f := by
  have h : Continuous (fun p => ⟪featureAt σ p, f⟫_ℝ) :=
    (continuous_featureAt σ).inner continuous_const
  simpa only [inner_featureAt_left] using h

/-- Unit diagonal gives a uniform bound by the actual Hilbert norm. -/
theorem norm_rkhsFunction_apply_le (σ : ℝ) (f : Space σ) (p : ℝ × ℝ) :
    ‖f p‖ ≤ ‖f‖ := by
  rw [← inner_featureAt_left σ f p]
  simpa only [norm_featureAt, one_mul] using norm_inner_le_norm (featureAt σ p) f

/-- Unit-norm Gaussian features are Bochner integrable against every finite positive measure. -/
theorem integrable_featureAt (σ : ℝ) (μ : Measure (ℝ × ℝ)) [IsFiniteMeasure μ] :
    Integrable (featureAt σ) μ := by
  exact (integrable_const (1 : ℝ)).mono'
    (continuous_featureAt σ).stronglyMeasurable.aestronglyMeasurable
    (Filter.Eventually.of_forall fun p => le_of_eq (norm_featureAt σ p))

/-- Gaussian features are integrable against the variation of every finite signed measure. -/
theorem signed_integrable_featureAt (σ : ℝ) (μ : SignedMeasure (ℝ × ℝ)) :
    μ.Integrable (featureAt σ) := by
  have : IsFiniteMeasure μ.variation := by
    rw [← SignedMeasure.totalVariation_eq_variation]
    infer_instance
  exact integrable_featureAt σ μ.variation

/-- Actual RKHS functions are integrable against every finite positive measure. -/
theorem integrable_rkhsFunction (σ : ℝ) (f : Space σ) (μ : Measure (ℝ × ℝ))
    [IsFiniteMeasure μ] : Integrable f μ := by
  exact (integrable_const ‖f‖).mono'
    (continuous_rkhsFunction σ f).stronglyMeasurable.aestronglyMeasurable
    (Filter.Eventually.of_forall fun p => norm_rkhsFunction_apply_le σ f p)

/-- The Gaussian RKHS embedding of a finite signed measure, defined by the actual
Banach-valued vector-measure integral. -/
def signedEmbedding (σ : ℝ) (μ : SignedMeasure (ℝ × ℝ)) : Space σ :=
  ∫ᵛ p, featureAt σ p ∂<•μ

/-- The ordinary Bochner mean of the actual feature for a finite positive measure. -/
def positiveEmbedding (σ : ℝ) (μ : Measure (ℝ × ℝ)) : Space σ :=
  ∫ p, featureAt σ p ∂μ

/-- The unit diagonal bounds every finite positive mean by its mass. -/
theorem norm_positiveEmbedding_le_mass (σ : ℝ) (μ : Measure (ℝ × ℝ)) [IsFiniteMeasure μ] :
    ‖positiveEmbedding σ μ‖ ≤ μ.real Set.univ := by
  simpa only [positiveEmbedding, one_mul] using
    (MeasureTheory.norm_integral_le_of_norm_le_const (μ := μ) (f := featureAt σ) (C := 1)
      (Filter.Eventually.of_forall fun p => le_of_eq (norm_featureAt σ p)))

@[simp] theorem positiveEmbedding_zero (σ : ℝ) : positiveEmbedding σ 0 = 0 := by
  simp [positiveEmbedding]

@[simp] theorem positiveEmbedding_dirac (σ : ℝ) (p : ℝ × ℝ) :
    positiveEmbedding σ (Measure.dirac p) = featureAt σ p := by
  simp [positiveEmbedding]

theorem positiveEmbedding_add (σ : ℝ) (μ ν : Measure (ℝ × ℝ))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    positiveEmbedding σ (μ + ν) = positiveEmbedding σ μ + positiveEmbedding σ ν :=
  integral_add_measure (integrable_featureAt σ μ) (integrable_featureAt σ ν)

/-- Evaluation of the positive mean is the integral of Gaussian kernel sections. -/
theorem positiveEmbedding_apply (σ : ℝ) (μ : Measure (ℝ × ℝ)) [IsFiniteMeasure μ]
    (z : ℝ × ℝ) : positiveEmbedding σ μ z = ∫ p, kernel σ z p ∂μ := by
  have h := integral_inner (𝕜 := ℝ) (integrable_featureAt σ μ) (featureAt σ z)
  simpa only [inner_featureAt, inner_featureAt_left, featureAt_apply, positiveEmbedding] using h.symm

/-- Pairing a positive mean with any actual RKHS function integrates that function. -/
theorem inner_positiveEmbedding (σ : ℝ) (μ : Measure (ℝ × ℝ)) [IsFiniteMeasure μ]
    (f : Space σ) : ⟪f, positiveEmbedding σ μ⟫_ℝ = ∫ p, f p ∂μ := by
  have h := integral_inner (𝕜 := ℝ) (integrable_featureAt σ μ) f
  simpa only [featureAt, RKHS.inner_kerFun, Real.inner_apply, mul_one,
    positiveEmbedding] using h.symm

/-- The signed integral is a linear map on all finite signed measures. -/
def signedEmbeddingLinear (σ : ℝ) : SignedMeasure (ℝ × ℝ) →ₗ[ℝ] Space σ where
  toFun := signedEmbedding σ
  map_add' μ ν := VectorMeasure.integral_add_vectorMeasure
    (signed_integrable_featureAt σ μ) (signed_integrable_featureAt σ ν)
  map_smul' _c _μ := VectorMeasure.integral_smul_vectorMeasure _ _

@[simp] theorem signedEmbedding_zero (σ : ℝ) : signedEmbedding σ 0 = 0 := by
  simp [signedEmbedding]

theorem signedEmbedding_add (σ : ℝ) (μ ν : SignedMeasure (ℝ × ℝ)) :
    signedEmbedding σ (μ + ν) = signedEmbedding σ μ + signedEmbedding σ ν := by
  exact VectorMeasure.integral_add_vectorMeasure
    (signed_integrable_featureAt σ μ) (signed_integrable_featureAt σ ν)

theorem signedEmbedding_sub (σ : ℝ) (μ ν : SignedMeasure (ℝ × ℝ)) :
    signedEmbedding σ (μ - ν) = signedEmbedding σ μ - signedEmbedding σ ν := by
  exact VectorMeasure.integral_sub_vectorMeasure
    (signed_integrable_featureAt σ μ) (signed_integrable_featureAt σ ν)

@[simp] theorem signedEmbedding_smul (σ c : ℝ) (μ : SignedMeasure (ℝ × ℝ)) :
    signedEmbedding σ (c • μ) = c • signedEmbedding σ μ := by
  exact VectorMeasure.integral_smul_vectorMeasure _ _

@[simp] theorem signedEmbedding_toSignedMeasure (σ : ℝ) (μ : Measure (ℝ × ℝ))
    [IsFiniteMeasure μ] : signedEmbedding σ μ.toSignedMeasure = positiveEmbedding σ μ := by
  exact VectorMeasure.integral_toSignedMeasure

/-- The actual signed integral agrees with the difference of its two Jordan means. -/
theorem signedEmbedding_eq_jordan (σ : ℝ) (μ : SignedMeasure (ℝ × ℝ)) :
    signedEmbedding σ μ = positiveEmbedding σ μ.toJordanDecomposition.posPart -
      positiveEmbedding σ μ.toJordanDecomposition.negPart := by
  conv_lhs => rw [← SignedMeasure.toSignedMeasure_toJordanDecomposition μ]
  rw [JordanDecomposition.toSignedMeasure, signedEmbedding_sub,
    signedEmbedding_toSignedMeasure, signedEmbedding_toSignedMeasure]

/-- Unit feature norm controls the actual signed mean by total variation. This follows
through the proved Jordan bridge and the ordinary Bochner norm estimate. -/
theorem norm_signedEmbedding_le_totalVariation (σ : ℝ) (μ : SignedMeasure (ℝ × ℝ)) :
    ‖signedEmbedding σ μ‖ ≤ μ.totalVariation.real Set.univ := by
  rw [signedEmbedding_eq_jordan]
  calc
    _ ≤ ‖positiveEmbedding σ μ.toJordanDecomposition.posPart‖ +
        ‖positiveEmbedding σ μ.toJordanDecomposition.negPart‖ := norm_sub_le _ _
    _ ≤ μ.toJordanDecomposition.posPart.real Set.univ +
        μ.toJordanDecomposition.negPart.real Set.univ :=
      add_le_add (norm_positiveEmbedding_le_mass σ _) (norm_positiveEmbedding_le_mass σ _)
    _ = μ.totalVariation.real Set.univ := by
      rw [SignedMeasure.totalVariation, measureReal_add_apply]

/-- Pairing with any actual RKHS function is the actual scalar signed integral of that
function. The proof reduces the existing vector integral through its Jordan parts. -/
theorem inner_signedEmbedding (σ : ℝ) (μ : SignedMeasure (ℝ × ℝ)) (f : Space σ) :
    ⟪f, signedEmbedding σ μ⟫_ℝ = ∫ᵛ p, f p ∂<•μ := by
  have hp : μ.toJordanDecomposition.posPart.toSignedMeasure.Integrable f := by
    simpa [VectorMeasure.Integrable] using
      integrable_rkhsFunction σ f μ.toJordanDecomposition.posPart
  have hn : μ.toJordanDecomposition.negPart.toSignedMeasure.Integrable f := by
    simpa [VectorMeasure.Integrable] using
      integrable_rkhsFunction σ f μ.toJordanDecomposition.negPart
  rw [signedEmbedding_eq_jordan, inner_sub_right, inner_positiveEmbedding,
    inner_positiveEmbedding]
  conv_rhs => rw [← SignedMeasure.toSignedMeasure_toJordanDecomposition μ]
  rw [JordanDecomposition.toSignedMeasure, VectorMeasure.integral_sub_vectorMeasure hp hn,
    VectorMeasure.integral_toSignedMeasure, VectorMeasure.integral_toSignedMeasure]

/-- Evaluation of the actual signed mean is the actual signed integral of the section. -/
theorem signedEmbedding_apply (σ : ℝ) (μ : SignedMeasure (ℝ × ℝ)) (z : ℝ × ℝ) :
    signedEmbedding σ μ z = ∫ᵛ p, kernel σ z p ∂<•μ := by
  simpa only [inner_featureAt_left, featureAt_apply, kernel_symm] using
    inner_signedEmbedding σ μ (featureAt σ z)

/-- The genuine RKHS squared norm is the iterated actual signed kernel integral. -/
theorem norm_signedEmbedding_sq (σ : ℝ) (μ : SignedMeasure (ℝ × ℝ)) :
    ‖signedEmbedding σ μ‖ ^ 2 =
      ∫ᵛ p, (∫ᵛ q, kernel σ p q ∂<•μ) ∂<•μ := by
  rw [← real_inner_self_eq_norm_sq, inner_signedEmbedding]
  simp_rw [signedEmbedding_apply]

/-- Squared Hilbert distance is the signed kernel energy of the difference measure. -/
theorem norm_signedEmbedding_sub_sq (σ : ℝ) (μ ν : SignedMeasure (ℝ × ℝ)) :
    ‖signedEmbedding σ μ - signedEmbedding σ ν‖ ^ 2 =
      ∫ᵛ p, (∫ᵛ q, kernel σ p q ∂<•(μ - ν)) ∂<•(μ - ν) := by
  rw [← signedEmbedding_sub, norm_signedEmbedding_sq]

/-- An atom contributes its signed coefficient times the actual feature. -/
@[simp] theorem signedEmbedding_dirac (σ : ℝ) (p : ℝ × ℝ) (c : ℝ) :
    signedEmbedding σ (VectorMeasure.dirac p c) = c • featureAt σ p := by
  simp [signedEmbedding]

/-- Finite signed atomic measures preserve each occurrence and its coefficient. -/
theorem signedEmbedding_finset_atoms {I : Type*} (σ : ℝ) (s : Finset I)
    (p : I → ℝ × ℝ) (c : I → ℝ) :
    signedEmbedding σ (∑ i ∈ s, VectorMeasure.dirac (p i) (c i)) =
      ∑ i ∈ s, c i • featureAt σ (p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => simp [hi, signedEmbedding_add, ih]

/-- The finite-support signed-measure representation, with coincident occurrences already
combined by the finsupp coefficients. -/
def atomicSignedMeasure (m : ℝ × ℝ →₀ ℝ) : SignedMeasure (ℝ × ℝ) :=
  m.sum fun p c => VectorMeasure.dirac p c

/-- The genuine signed integral extends the existing finite-support Gaussian embedding. -/
theorem signedEmbedding_atomicSignedMeasure (σ : ℝ) (m : ℝ × ℝ →₀ ℝ) :
    signedEmbedding σ (atomicSignedMeasure m) = measureEmbedding σ m := by
  classical
  rw [atomicSignedMeasure, Finsupp.sum, signedEmbedding_finset_atoms]
  rfl

/-- Finite persistence diagrams retain the existing weighted embedding, including its
occurrence multiplicities and separate treatment of essential bars. -/
theorem signedEmbedding_weightedDiagram {A B : ℝ} (σ : ℝ)
    (w : PersistenceImage.Weight A B) (D : Diagram ℝ) :
    signedEmbedding σ (atomicSignedMeasure (weightedMeasure w D)) =
      diagramEmbedding σ w D := by
  rw [signedEmbedding_atomicSignedMeasure, diagramEmbedding_eq_measureEmbedding]

/-- Finite positive Borel measures on the full plane are separated by their Gaussian means. -/
theorem positiveEmbedding_injective {σ : ℝ} (hσ : σ ≠ 0)
    (μ ν : Measure (ℝ × ℝ)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : positiveEmbedding σ μ = positiveEmbedding σ ν) : μ = ν := by
  let e := (WithLp.homeomorphProd 2 ℝ ℝ).symm
  apply e.measurableEmbedding.map_injective
  apply GaussianSpectral.eq_of_gaussian_integrals hσ
  intro p
  rw [integral_map e.measurable.aemeasurable (by fun_prop),
    integral_map e.measurable.aemeasurable (by fun_prop)]
  have hp := congrArg (fun f : Space σ => f (e.symm p)) h
  rw [positiveEmbedding_apply, positiveEmbedding_apply] at hp
  have hker (x : ℝ × ℝ) : kernel σ (e.symm p) x =
      Real.exp (-‖p - e x‖ ^ 2 / (2 * σ ^ 2)) := by
    rw [kernel_eq_gaussian]
    rfl
  simpa only [hker] using hp

/-- The actual Gaussian RKHS embedding is injective on all finite signed Borel measures
on the full plane when bandwidth is nonzero. -/
theorem signedEmbedding_injective {σ : ℝ} (hσ : σ ≠ 0) :
    Function.Injective (signedEmbedding σ) := by
  intro μ ν h
  have hz : signedEmbedding σ (μ - ν) = 0 := by rw [signedEmbedding_sub, h, sub_self]
  rw [signedEmbedding_eq_jordan, sub_eq_zero] at hz
  have hj := positiveEmbedding_injective hσ _ _ hz
  have hdiff : μ - ν = 0 := by
    rw [← SignedMeasure.toSignedMeasure_toJordanDecomposition (μ - ν),
      JordanDecomposition.toSignedMeasure]
    simp only [hj, sub_self]
  exact sub_eq_zero.1 hdiff

/-- Vanishing signed Gaussian mean characterizes the zero signed measure. -/
theorem signedEmbedding_eq_zero_iff {σ : ℝ} (hσ : σ ≠ 0)
    (μ : SignedMeasure (ℝ × ℝ)) : signedEmbedding σ μ = 0 ↔ μ = 0 := by
  rw [← signedEmbedding_zero σ, (signedEmbedding_injective hσ).eq_iff]

/-- The actual Hilbert distance separates arbitrary finite signed measures. -/
theorem norm_signedEmbedding_sub_eq_zero_iff {σ : ℝ} (hσ : σ ≠ 0)
    (μ ν : SignedMeasure (ℝ × ℝ)) :
    ‖signedEmbedding σ μ - signedEmbedding σ ν‖ = 0 ↔ μ = ν :=
  norm_sub_eq_zero_iff.trans (signedEmbedding_injective hσ).eq_iff

/-- The Gaussian is characteristic on probability measures on the full plane. -/
theorem probabilityEmbedding_injective {σ : ℝ} (hσ : σ ≠ 0)
    (μ ν : Measure (ℝ × ℝ)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : positiveEmbedding σ μ = positiveEmbedding σ ν) : μ = ν := by
  have hsigned : μ.toSignedMeasure = ν.toSignedMeasure :=
    signedEmbedding_injective hσ (by simpa only [signedEmbedding_toSignedMeasure] using h)
  simpa only [Measure.variation_toSignedMeasure] using
    congrArg VectorMeasure.variation hsigned

end TDA.Persistence.WeightedKernel
