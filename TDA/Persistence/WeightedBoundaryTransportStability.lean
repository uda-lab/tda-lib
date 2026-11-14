import TDA.Persistence.BoundaryPlanLaws
import TDA.Persistence.WeightedBoundaryTransportFeature

/-!
# Native boundary transport stability of the weighted Gaussian embedding

The weighted feature is zero on the diagonal. Its two endpoint integrals against
each admissible boundary plan are therefore the original weighted embeddings.
The pointwise maximum-coordinate estimate integrates and passes to the native
infimum, including zero constants and infinite transport cost. Only the real
corollary requires finite first diagonal moments.
-/

noncomputable section

namespace TDA.Persistence.WeightedKernel

open MeasureTheory BoundaryTransport
open scoped ENNReal

variable {A B : ℝ}

private theorem le_mul_boundaryTransportDistance_of_plan_bounds
    (μ ν : Measure Interior) (a c : ℝ≥0∞) (hc : c ≠ ∞)
    (h : ∀ (π : Measure PlanSpace), IsBoundaryPlan π μ ν →
      a ≤ c * ∫⁻ z, planPowerCost 1 z ∂π) :
    a ≤ c * boundaryTransportDistance 1 μ ν := by
  by_cases hc0 : c = 0
  · simpa only [hc0, zero_mul] using
      h (diagonalBoundaryPlan μ ν) (diagonalBoundaryPlan_admissible μ ν)
  · simp only [boundaryTransportDistance, div_one, ENNReal.rpow_one,
      boundaryTransportPowerValue]
    rw [ENNReal.mul_iInf_of_ne hc0 hc]
    apply le_iInf
    intro π
    rw [ENNReal.mul_iInf_of_ne hc0 hc]
    exact le_iInf (h π)

/-- The weighted Gaussian embedding difference is bounded by each genuine
boundary plan, including competitors with infinite first transport cost. -/
theorem enorm_weightedPersistenceEmbedding_sub_le_plan
    (σ : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (w : PersistenceImage.Weight A B)
    {μ ν : Measure Interior} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {π : Measure PlanSpace} (hπ : IsBoundaryPlan π μ ν) :
    ENNReal.ofReal ‖weightedPersistenceEmbedding σ (upperWeight w) μ -
      weightedPersistenceEmbedding σ (upperWeight w) ν‖ ≤
        ENNReal.ofReal (stabilityConstant σ A B) * ∫⁻ z, planPowerCost 1 z ∂π := by
  let := boundaryPlan_isFiniteMeasure hπ
  rw [← integral_planFirst_weightedFeature σ hA hB w hπ,
    ← integral_planSecond_weightedFeature σ hA hB w hπ,
    ← integral_sub (integrable_planFirst_weightedFeature σ hA hB w π)
      (integrable_planSecond_weightedFeature σ hA hB w π)]
  calc
    _ ≤ ∫⁻ z, ENNReal.ofReal
        ‖weightedFeature σ w z.1.1.1 - weightedFeature σ w z.1.2.1‖ ∂π := by
      simpa only [ofReal_norm] using
        (enorm_integral_le_lintegral_enorm
          (fun z : PlanSpace => weightedFeature σ w z.1.1.1 -
            weightedFeature σ w z.1.2.1) (μ := π))
    _ ≤ ∫⁻ z, ENNReal.ofReal (stabilityConstant σ A B) * planPowerCost 1 z ∂π := by
      apply lintegral_mono
      intro z
      have h := ENNReal.ofReal_le_ofReal
        (norm_weightedFeature_sub_le σ hB w z.1.1.1 z.1.2.1)
      simpa only [ENNReal.ofReal_mul (stabilityConstant_nonneg σ hA hB),
        planPowerCost, Real.rpow_one, Subtype.dist_eq, dist_eq_norm] using h
    _ = _ := lintegral_const_mul _ (measurable_planPowerCost 1)

/-- Native first-order boundary transport controls the actual full-plane RKHS
embedding for arbitrary finite original measures. No moment, equal-mass, support,
or optimizer hypothesis is required. The estimate includes zero constants and
infinite transport distance. -/
theorem enorm_weightedPersistenceEmbedding_sub_le_boundaryTransportDistance
    (σ : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (w : PersistenceImage.Weight A B)
    (μ ν : Measure Interior) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    ENNReal.ofReal ‖weightedPersistenceEmbedding σ (upperWeight w) μ -
      weightedPersistenceEmbedding σ (upperWeight w) ν‖ ≤
        ENNReal.ofReal (stabilityConstant σ A B) * boundaryTransportDistance 1 μ ν := by
  apply le_mul_boundaryTransportDistance_of_plan_bounds μ ν _ _ ENNReal.ofReal_ne_top
  intro π hπ
  exact enorm_weightedPersistenceEmbedding_sub_le_plan σ hA hB w hπ

/-- Finite first diagonal moments make the native distance finite, so the
extended estimate yields a real RKHS bound. No ambient first moment is assumed. -/
theorem norm_weightedPersistenceEmbedding_sub_le_boundaryTransportDistance
    (σ : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (w : PersistenceImage.Weight A B)
    (μ ν : Measure Interior) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : (∫⁻ x, ENNReal.ofReal (depth x) ∂μ) < ∞)
    (hν : (∫⁻ x, ENNReal.ofReal (depth x) ∂ν) < ∞) :
    ‖weightedPersistenceEmbedding σ (upperWeight w) μ -
      weightedPersistenceEmbedding σ (upperWeight w) ν‖ ≤
        stabilityConstant σ A B * (boundaryTransportDistance 1 μ ν).toReal := by
  have hfinite : boundaryTransportDistance 1 μ ν < ∞ :=
    boundaryTransportDistance_lt_top 1 (by norm_num) μ ν
      (by simpa only [Real.rpow_one] using hμ)
      (by simpa only [Real.rpow_one] using hν)
  have h := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfinite.ne)
    (enorm_weightedPersistenceEmbedding_sub_le_boundaryTransportDistance σ hA hB w μ ν)
  simpa only [ENNReal.toReal_ofReal (norm_nonneg _), ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (stabilityConstant_nonneg σ hA hB)] using h

end TDA.Persistence.WeightedKernel
