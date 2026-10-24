import TDA.Persistence.BoundaryTransportAttainment
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.Probability.Kernel.Disintegration.StandardBorel

/-! Fixed-space `Lᵖ` notation for reservoir transport. -/

noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped ENNReal
namespace TDA.Persistence.BoundaryTransport

/-- The literal metric `Lᵖ` norm is the rooted powered integral, including infinite values. -/
theorem eLpNorm_dist_eq_collapsedPowerCost (p : ℝ) (hp : 0 < p)
    (γ : Measure (Space × Space)) :
    eLpNorm (fun z : Space × Space => dist z.1 z.2) (ENNReal.ofReal p) γ =
      (∫⁻ z, collapsedPowerCost p z ∂γ) ^ (1 / p) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
    (ENNReal.ofReal_ne_zero_iff.mpr hp) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hp.le]
  congr 1
  apply lintegral_congr
  intro z
  simp only [collapsedPowerCost]
  rw [Real.enorm_eq_ofReal (dist_nonneg : 0 ≤ dist z.1 z.2),
    ENNReal.ofReal_rpow_of_nonneg dist_nonneg hp.le]

private theorem iInf_rpow {ι : Sort*} (f : ι → ℝ≥0∞) {a : ℝ} (ha : 0 < a) :
    (⨅ i, f i) ^ a = ⨅ i, (f i) ^ a := by
  exact (ENNReal.orderIsoRpow a ha).map_iInf f

/-- On the collapsed metric space, the extended metric and real metric give the same
coupling `Lᵖ` norm. -/
theorem eLpNorm_edist_eq_dist (q : ℝ≥0∞) (γ : Measure (Space × Space)) :
    eLpNorm (fun z : Space × Space => edist z.1 z.2) q γ =
      eLpNorm (fun z : Space × Space => dist z.1 z.2) q γ := by
  apply eLpNorm_congr_enorm_ae
  exact Filter.Eventually.of_forall fun z => by
    rw [enorm_eq_self, edist_dist, Real.enorm_eq_ofReal dist_nonneg]

/-- Ordinary unnormalized coupling `Lᵖ` infimum at the full reservoir capacity. -/
theorem reservoirDistance_eq_iInf_eLpNorm (p : ℝ) (hp : 0 < p)
    (μ ν : Measure Interior) (R : ℝ≥0∞) :
    reservoirDistance p μ ν R =
      ⨅ γ : Measure (Space × Space),
        ⨅ (_ : γ.map Prod.fst = reservoirMeasure μ R ∧
          γ.map Prod.snd = reservoirMeasure ν R),
          eLpNorm (fun z : Space × Space => edist z.1 z.2) (ENNReal.ofReal p) γ := by
  unfold reservoirDistance reservoirPowerValue
  have ha : 0 < 1 / p := one_div_pos.mpr hp
  rw [iInf_rpow (a := 1 / p) (fun γ : Measure (Space × Space) =>
    ⨅ (_ : γ.map Prod.fst = reservoirMeasure μ R ∧
      γ.map Prod.snd = reservoirMeasure ν R),
      ∫⁻ z, collapsedPowerCost p z ∂γ) ha]
  simp_rw [iInf_rpow (a := 1 / p) (ha := ha),
    ← eLpNorm_dist_eq_collapsedPowerCost p hp, ← eLpNorm_edist_eq_dist]

/-- Native boundary transport equals the literal coupling `Lᵖ` infimum. -/
theorem boundaryTransportDistance_eq_iInf_eLpNorm (p : ℝ) (hp : 1 ≤ p)
    (μ ν : Measure Interior) (R : ℝ≥0∞) (hRtop : R < ∞)
    (htotal : μ univ + ν univ ≤ R) :
    boundaryTransportDistance p μ ν =
      ⨅ γ : Measure (Space × Space),
        ⨅ (_ : γ.map Prod.fst = reservoirMeasure μ R ∧
          γ.map Prod.snd = reservoirMeasure ν R),
          eLpNorm (fun z : Space × Space => edist z.1 z.2) (ENNReal.ofReal p) γ := by
  rw [boundaryTransportDistance_eq_reservoirDistance p hp μ ν R hRtop htotal]
  exact reservoirDistance_eq_iInf_eLpNorm p (by linarith) μ ν R

/-- The probability-reservoir form uses the actual normalized measures. -/
theorem boundaryTransportDistance_eq_normalized_iInf_eLpNorm
    (p : ℝ) (hp : 1 ≤ p) (μ ν : Measure Interior) (R : ℝ≥0∞)
    (hRtop : R < ∞) (hRpos : 0 < R)
    (htotal : μ univ + ν univ ≤ R) :
    boundaryTransportDistance p μ ν = R ^ (1 / p) *
      (⨅ γ : Measure (Space × Space),
        ⨅ (_ : γ.map Prod.fst = normalizedReservoirMeasure μ R ∧
          γ.map Prod.snd = normalizedReservoirMeasure ν R),
          eLpNorm (fun z : Space × Space => edist z.1 z.2) (ENNReal.ofReal p) γ) := by
  rw [boundaryTransportDistance_eq_normalizedReservoirDistance p hp μ ν R hRtop hRpos htotal,
    reservoirDistance_eq_iInf_eLpNorm p (by linarith)]
  rw [normalizedReservoirMeasure_eq_reservoirMeasure_inv μ R hRtop hRpos,
    normalizedReservoirMeasure_eq_reservoirMeasure_inv ν R hRtop hRpos]

end TDA.Persistence.BoundaryTransport
