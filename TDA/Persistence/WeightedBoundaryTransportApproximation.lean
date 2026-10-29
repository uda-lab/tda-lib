import TDA.Persistence.BoundaryTransportApproximation
import TDA.Persistence.WeightedBoundaryTransportStability

/-!
# Weighted Gaussian consumers of native boundary transport

Finite real masses give the actual weighted Gaussian sum, including zero masses
and coincident points. Native finite diagrams inherit the measure stability
bound, and the same-mass quantizations converge in the Gaussian RKHS norm.
-/

set_option autoImplicit false
noncomputable section

namespace TDA.Persistence.WeightedKernel

open MeasureTheory BoundaryTransport Filter Topology
open scoped ENNReal NNReal Classical

variable {A B : ℝ}

/-- A finite positive real-mass atomic measure embeds as the corresponding real
weighted feature sum. Zero masses and coincident coordinates are permitted. -/
theorem weightedPersistenceEmbedding_finite_masses {I : Type*} [Fintype I]
    (σ : ℝ) (w : PersistenceImage.Weight A B) (m : I → ℝ)
    (x : I → UpperPoint) (hm : ∀ i, 0 ≤ m i) :
    weightedPersistenceEmbedding σ (upperWeight w)
        (∑ i, ENNReal.ofReal (m i) • Measure.dirac (x i)) =
      ∑ i, m i • weightedFeature σ w (x i).1 := by
  have hplane : weightedPlaneMeasure (upperWeight w)
      (∑ i, ENNReal.ofReal (m i) • Measure.dirac (x i)) =
      ∑ i, (ENNReal.ofReal (m i) * ENNReal.ofReal (upperWeight w (x i))) •
        Measure.dirac (x i).1 := by
    rw [weightedPlaneMeasure, ← Measure.sum_fintype, withDensity_sum,
      Measure.map_sum measurable_subtype_coe.aemeasurable, Measure.sum_fintype]
    simp only [withDensity_smul_measure, dirac_withDensity, Measure.map_smul,
      Measure.map_dirac' measurable_subtype_coe, smul_smul]
  rw [weightedPersistenceEmbedding, hplane, positiveEmbedding]
  rw [integral_finsetSum_measure (fun i _ =>
    (integrable_featureAt σ (Measure.dirac (x i).1)).smul_measure
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top))]
  simp only [integral_smul_measure, integral_dirac,
    ENNReal.toReal_ofReal (hm _), ENNReal.toReal_ofReal (w.nonneg _),
    mul_smul, weightedFeature, upperWeight]

/-- The exact embedding of a native finite weighted diagram is its finite real-mass
support sum. Native masses may be fractional. -/
theorem weightedPersistenceEmbedding_atomicMeasure (σ : ℝ)
    (w : PersistenceImage.Weight A B) (D : FiniteWeightedDiagram) :
    weightedPersistenceEmbedding σ (upperWeight w) (atomicMeasure D) =
      ∑ i : D.supportLabels, (D.weights i : ℝ) •
        weightedFeature σ w (D.coordinates i) := by
  simpa only [atomicMeasure, ENNReal.ofReal_coe_nnreal,
    FiniteWeightedDiagram.coordinates] using
    weightedPersistenceEmbedding_finite_masses σ w
      (fun i : D.supportLabels => (D.weights i : ℝ)) (fun i => i.1)
      (fun i => (D.weights i).coe_nonneg)

/-- Indexed native diagrams retain every real-mass contribution before coalescing
coincident coordinates, including indices of zero mass. -/
theorem weightedPersistenceEmbedding_ofIndexed {I : Type*} [Fintype I]
    (σ : ℝ) (w : PersistenceImage.Weight A B) (m : I → ℝ≥0)
    (x : I → Interior) :
    weightedPersistenceEmbedding σ (upperWeight w)
        (atomicMeasure (FiniteWeightedDiagram.ofIndexed m x)) =
      ∑ i, (m i : ℝ) • weightedFeature σ w (x i).1 := by
  rw [atomicMeasure_ofIndexed]
  simpa only [ENNReal.ofReal_coe_nnreal] using
    weightedPersistenceEmbedding_finite_masses σ w (fun i => (m i : ℝ)) x
      (fun i => (m i).coe_nonneg)

/-- Native finite weighted diagrams satisfy the real RKHS estimate with their
own optimized first-order boundary transport cost, without a mass-balance condition. -/
theorem norm_weightedPersistenceEmbedding_atomicMeasure_sub_le (σ : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (w : PersistenceImage.Weight A B)
    (D E : FiniteWeightedDiagram) :
    ‖weightedPersistenceEmbedding σ (upperWeight w) (atomicMeasure D) -
      weightedPersistenceEmbedding σ (upperWeight w) (atomicMeasure E)‖ ≤
        stabilityConstant σ A B * FiniteWeightedDiagram.pBoundaryTransportCost 1 D E := by
  have := atomicMeasure_isFinite D
  have := atomicMeasure_isFinite E
  have h := enorm_weightedPersistenceEmbedding_sub_le_boundaryTransportDistance
    σ hA hB w (atomicMeasure D) (atomicMeasure E)
  rw [boundaryTransportDistance_atomic_eq_native 1 le_rfl] at h
  have hc := stabilityConstant_nonneg σ hA hB
  have hd : 0 ≤ FiniteWeightedDiagram.pBoundaryTransportCost 1 D E :=
    weightedPBoundaryTransportCost_nonneg 1 D.weights E.weights D.coordinates E.coordinates
  rw [← ENNReal.ofReal_mul hc] at h
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hc hd)).mp h

/-- The existing native same-mass quantizations converge in the actual full-plane
Gaussian RKHS whenever the original finite measure has finite first diagonal moment. -/
theorem weightedPersistenceEmbedding_quantizedDiagram_tendsto (σ : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (w : PersistenceImage.Weight A B)
    (μ : Measure Interior) [IsFiniteMeasure μ]
    (hmoment : (∫⁻ x, ENNReal.ofReal (depth x) ∂μ) < ∞) :
    Tendsto (fun n => weightedPersistenceEmbedding σ (upperWeight w)
      (atomicMeasure (quantizedDiagram μ n))) atTop
        (𝓝 (weightedPersistenceEmbedding σ (upperWeight w) μ)) := by
  have htransport := boundaryTransportDistance_quantizedDiagram_tendsto 1 le_rfl μ
    (by simpa only [Real.rpow_one] using hmoment)
  have hbound : Tendsto (fun n => ENNReal.ofReal (stabilityConstant σ A B) *
      boundaryTransportDistance 1 μ (atomicMeasure (quantizedDiagram μ n)))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, mul_zero] using
      ((ENNReal.continuous_const_mul ENNReal.ofReal_ne_top).tendsto 0).comp htransport
  apply tendsto_iff_edist_tendsto_0.mpr
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hbound
  · intro n
    exact bot_le
  · intro n
    have := atomicMeasure_isFinite (quantizedDiagram μ n)
    simpa only [edist_dist, dist_eq_norm, norm_sub_rev] using
      enorm_weightedPersistenceEmbedding_sub_le_boundaryTransportDistance
        σ hA hB w μ (atomicMeasure (quantizedDiagram μ n))

end TDA.Persistence.WeightedKernel
