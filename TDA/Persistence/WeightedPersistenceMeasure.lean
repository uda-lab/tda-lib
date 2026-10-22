import TDA.Persistence.GaussianMeasureEmbedding
import TDA.Persistence.WeightedKernelIsometry

/-!
# Weighted positive persistence measures

Positive measures on finite birth–death points may have infinite total mass.
A strictly positive measurable weight with finite weighted mass first produces
a finite measure on the full plane. Its Gaussian mean determines the original
measure, because inverse weighting recovers it. No lower bound on the weight
away from zero is required, and essential bars are separate data.
-/

noncomputable section

namespace TDA.Persistence.WeightedKernel

open MeasureTheory Set
open scoped ENNReal

instance upperPoint_locallyCompact : LocallyCompactSpace UpperPoint :=
  (isOpen_lt continuous_fst continuous_snd).locallyCompactSpace

private theorem upperPoint_measurable : MeasurableSet {p : ℝ × ℝ | p.1 < p.2} :=
  isOpen_lt continuous_fst continuous_snd |>.measurableSet

/-- Weight a positive persistence measure and include it in the full plane. -/
def weightedPlaneMeasure (w : UpperPoint → ℝ) (μ : Measure UpperPoint) : Measure (ℝ × ℝ) :=
  (μ.withDensity fun p => ENNReal.ofReal (w p)).map Subtype.val

/-- Finite weighted mass, rather than finite original mass, suffices. -/
theorem finite_weightedPlaneMeasure (w : UpperPoint → ℝ) (μ : Measure UpperPoint)
    (hμ : (∫⁻ p, ENNReal.ofReal (w p) ∂μ) < ∞) :
    IsFiniteMeasure (weightedPlaneMeasure w μ) := by
  have := isFiniteMeasure_withDensity hμ.ne
  exact Measure.isFiniteMeasure_map _ _

/-- The finite weighted measure is Radon on the full plane. -/
theorem regular_weightedPlaneMeasure (w : UpperPoint → ℝ) (μ : Measure UpperPoint)
    (hμ : (∫⁻ p, ENNReal.ofReal (w p) ∂μ) < ∞) :
    (weightedPlaneMeasure w μ).Regular := by
  have := finite_weightedPlaneMeasure w μ hμ
  infer_instance

/-- Finite weighted mass also gives a Radon measure before the ambient inclusion. -/
theorem regular_withDensity_weight (w : UpperPoint → ℝ) (μ : Measure UpperPoint)
    (hμ : (∫⁻ p, ENNReal.ofReal (w p) ∂μ) < ∞) :
    (μ.withDensity fun p => ENNReal.ofReal (w p)).Regular := by
  have := isFiniteMeasure_withDensity hμ.ne
  infer_instance

/-- The weighted Gaussian embedding uses the full-plane RKHS mean. -/
def weightedPersistenceEmbedding (σ : ℝ) (w : UpperPoint → ℝ)
    (μ : Measure UpperPoint) : Space σ := positiveEmbedding σ (weightedPlaneMeasure w μ)

/-- Weighting an occurrence measure preserves every indexed atom, including coincidences. -/
theorem weightedPlaneMeasure_atoms {I : Type*} (w : UpperPoint → ℝ) (x : I → UpperPoint) :
    weightedPlaneMeasure w (Measure.sum fun i => Measure.dirac (x i)) =
      Measure.sum fun i => ENNReal.ofReal (w (x i)) • Measure.dirac (x i).1 := by
  rw [weightedPlaneMeasure, withDensity_sum,
    Measure.map_sum measurable_subtype_coe.aemeasurable]
  simp only [dirac_withDensity, Measure.map_smul,
    Measure.map_dirac' measurable_subtype_coe]

/-- The finite weighted positive-measure mean is the occurrence sum.
Only the sampled weights must be nonnegative. -/
theorem weightedPersistenceEmbedding_finite {I : Type*} [Fintype I] (σ : ℝ)
    (w : UpperPoint → ℝ) (x : I → UpperPoint) (hw : ∀ i, 0 ≤ w (x i)) :
    weightedPersistenceEmbedding σ w (Measure.sum fun i => Measure.dirac (x i)) =
      ∑ i, w (x i) • featureAt σ (x i).1 := by
  classical
  rw [weightedPersistenceEmbedding, weightedPlaneMeasure_atoms, positiveEmbedding,
    Measure.sum_fintype]
  rw [integral_finsetSum_measure (fun i _ =>
    (integrable_featureAt σ (Measure.dirac (x i).1)).smul_measure ENNReal.ofReal_ne_top)]
  simp_rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (hw _)]

/-- Persistence-image birth–persistence weights reproduce the existing finite full-plane
embedding, with one contribution from each occurrence. -/
theorem weightedPersistenceEmbedding_finite_occurrences {I : Type*} [Fintype I]
    {A B : ℝ} (σ : ℝ) (w : PersistenceImage.Weight A B) (x : I → UpperPoint) :
    weightedPersistenceEmbedding σ (upperWeight w)
        (Measure.sum fun i => Measure.dirac (x i)) =
      embedding σ w (fun i => (x i).1) := by
  rw [weightedPersistenceEmbedding_finite σ (upperWeight w) x
    (fun i => w.nonneg (birthPersistence (x i).1))]
  rfl

/-- Finite weighted mass makes the weighted feature genuinely Bochner integrable. -/
theorem integrable_weightedFeature (σ : ℝ) (w : UpperPoint → ℝ) (hw : Measurable w)
    (hpos : ∀ p, 0 ≤ w p) (μ : Measure UpperPoint)
    (hμ : (∫⁻ p, ENNReal.ofReal (w p) ∂μ) < ∞) :
    Integrable (fun p => w p • featureAt σ p.1) μ := by
  have hwint : Integrable w μ :=
    ⟨hw.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal
      (Filter.Eventually.of_forall hpos)).2 hμ⟩
  apply hwint.mono'
    (hw.stronglyMeasurable.smul
      ((continuous_featureAt σ).comp continuous_subtype_val).stronglyMeasurable).aestronglyMeasurable
  filter_upwards [] with p
  simp [norm_smul, norm_featureAt, Real.norm_eq_abs, abs_of_nonneg (hpos p)]

/-- The weighted measure construction agrees with integrating the weighted feature
against the original, possibly infinite, positive measure. -/
theorem weightedPersistenceEmbedding_eq_integral (σ : ℝ) (w : UpperPoint → ℝ)
    (hw : Measurable w) (hpos : ∀ p, 0 ≤ w p) (μ : Measure UpperPoint) :
    weightedPersistenceEmbedding σ w μ = ∫ p, w p • featureAt σ p.1 ∂μ := by
  rw [weightedPersistenceEmbedding, positiveEmbedding, weightedPlaneMeasure,
    integral_map measurable_subtype_coe.aemeasurable
      (continuous_featureAt σ).stronglyMeasurable.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul hw.ennreal_ofReal
      (Filter.Eventually.of_forall fun p => ENNReal.ofReal_lt_top) ]
  apply integral_congr_ae
  filter_upwards [] with p
  rw [ENNReal.toReal_ofReal (hpos p)]

/-- Strictly positive finite weights lose no measure information, including when the original
positive measures have infinite total mass. -/
theorem weightedPlaneMeasure_injective (w : UpperPoint → ℝ) (hw : Measurable w)
    (hpos : ∀ p, 0 < w p) : Function.Injective (weightedPlaneMeasure w) := by
  intro μ ν h
  have hd : μ.withDensity (fun p => ENNReal.ofReal (w p)) =
      ν.withDensity (fun p => ENNReal.ofReal (w p)) :=
    (MeasurableEmbedding.subtype_coe upperPoint_measurable).map_injective h
  have hrecover (ρ : Measure UpperPoint) :
      (ρ.withDensity (fun p => ENNReal.ofReal (w p))).withDensity
          (fun p => (ENNReal.ofReal (w p))⁻¹) = ρ := by
    apply withDensity_inv_same (hw.ennreal_ofReal)
    · exact Filter.Eventually.of_forall fun p => ENNReal.ofReal_ne_zero_iff.2 (hpos p)
    · exact Filter.Eventually.of_forall fun p => ENNReal.ofReal_ne_top
  have hback := congrArg (fun ρ : Measure UpperPoint =>
    ρ.withDensity (fun p => (ENNReal.ofReal (w p))⁻¹)) hd
  simpa only [hrecover] using hback

/-- Gaussian recovery for positive persistence measures of finite weighted mass. The measures
need not be finite and the weight need not be bounded below. -/
theorem weightedPersistenceEmbedding_eq_iff {σ : ℝ} (hσ : σ ≠ 0)
    (w : UpperPoint → ℝ) (hw : Measurable w) (hpos : ∀ p, 0 < w p)
    (μ ν : Measure UpperPoint)
    (hμ : (∫⁻ p, ENNReal.ofReal (w p) ∂μ) < ∞)
    (hν : (∫⁻ p, ENNReal.ofReal (w p) ∂ν) < ∞) :
    weightedPersistenceEmbedding σ w μ = weightedPersistenceEmbedding σ w ν ↔ μ = ν := by
  constructor
  · intro h
    have := finite_weightedPlaneMeasure w μ hμ
    have := finite_weightedPlaneMeasure w ν hν
    exact weightedPlaneMeasure_injective w hw hpos
      (positiveEmbedding_injective hσ _ _ h)
  · rintro rfl
    rfl

/-- Continuous positive weights recover positive Radon persistence measures, allowing
infinite unweighted total mass. -/
theorem weightedPersistenceEmbedding_eq_iff_continuous {σ : ℝ} (hσ : σ ≠ 0)
    (w : C(UpperPoint, ℝ)) (hpos : ∀ p, 0 < w p)
    (μ ν : Measure UpperPoint) [μ.Regular] [ν.Regular]
    (hμ : (∫⁻ p, ENNReal.ofReal (w p) ∂μ) < ∞)
    (hν : (∫⁻ p, ENNReal.ofReal (w p) ∂ν) < ∞) :
    weightedPersistenceEmbedding σ w μ = weightedPersistenceEmbedding σ w ν ↔ μ = ν :=
  weightedPersistenceEmbedding_eq_iff hσ w w.continuous.measurable hpos μ ν hμ hν

/-- The positive counting measure of countably many finite-bar occurrences. Repeated
points contribute repeatedly. -/
def countableDiagramMeasure (x : ℕ → UpperPoint) : Measure UpperPoint :=
  Measure.sum fun n => Measure.dirac (x n)

/-- Summability of occurrence weights is exactly the weighted-mass condition used by
the Gaussian consumer. -/
theorem countableDiagramMeasure_weighted_mass (w : UpperPoint → ℝ) (x : ℕ → UpperPoint) :
    (∫⁻ p, ENNReal.ofReal (w p) ∂countableDiagramMeasure x) =
      ∑' n, ENNReal.ofReal (w (x n)) := by
  rw [countableDiagramMeasure, lintegral_sum_measure]
  simp only [lintegral_dirac]

/-- Countable locally finite diagrams are recovered as counting measures under summable
strictly positive occurrence weights, so point multiplicities are retained. -/
theorem countableDiagramEmbedding_eq_iff {σ : ℝ} (hσ : σ ≠ 0)
    (w : C(UpperPoint, ℝ)) (hpos : ∀ p, 0 < w p) (x y : ℕ → UpperPoint)
    [IsLocallyFiniteMeasure (countableDiagramMeasure x)]
    [IsLocallyFiniteMeasure (countableDiagramMeasure y)]
    (hx : Summable fun n => w (x n)) (hy : Summable fun n => w (y n)) :
    weightedPersistenceEmbedding σ w (countableDiagramMeasure x) =
      weightedPersistenceEmbedding σ w (countableDiagramMeasure y) ↔
        countableDiagramMeasure x = countableDiagramMeasure y := by
  apply weightedPersistenceEmbedding_eq_iff_continuous hσ w hpos
  · rw [countableDiagramMeasure_weighted_mass]
    exact hx.tsum_ofReal_lt_top
  · rw [countableDiagramMeasure_weighted_mass]
    exact hy.tsum_ofReal_lt_top

end TDA.Persistence.WeightedKernel
