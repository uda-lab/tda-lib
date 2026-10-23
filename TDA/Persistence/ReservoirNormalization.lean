import TDA.Persistence.BoundaryTransportComparison

/-!
# Probability normalization of reservoir transport

Scaling every competitor in both directions identifies the unnormalized
reservoir value with the capacity-one value of the scaled input measures.
Finite positive capacity is enough for the algebraic identities. The full
sum-of-masses bound ensures that both normalized reservoirs are probabilities.
-/

noncomputable section

set_option autoImplicit false

open Set MeasureTheory
open scoped ENNReal

namespace TDA.Persistence.BoundaryTransport

private theorem inv_mul_sub_eq_one_sub_inv_mul (R m : ℝ≥0∞)
    (hRtop : R < ∞) (hRpos : 0 < R) :
    R⁻¹ * (R - m) = 1 - R⁻¹ * m := by
  have hinvtop : R⁻¹ ≠ ∞ := ENNReal.inv_ne_top.mpr hRpos.ne'
  rw [ENNReal.mul_sub (fun _ _ => hinvtop), ENNReal.inv_mul_cancel hRpos.ne' hRtop.ne]

/-- Normalizing a capacity-`R` reservoir is literally the capacity-one reservoir of the scaled
interior measure. The identity is algebraic and holds even without the mass-bound premise; when
that premise holds, both sides are probability measures. -/
theorem normalizedReservoirMeasure_eq_reservoirMeasure_inv
    (μ : Measure Interior) (R : ℝ≥0∞) (hRtop : R < ∞) (hRpos : 0 < R) :
    normalizedReservoirMeasure μ R = reservoirMeasure (R⁻¹ • μ) 1 := by
  have hcoef := inv_mul_sub_eq_one_sub_inv_mul R (μ Set.univ) hRtop hRpos
  apply Measure.ext
  intro s hs
  simp only [normalizedReservoirMeasure, Measure.smul_apply, smul_eq_mul,
    reservoirMeasure, Measure.add_apply, Measure.map_smul]
  rw [mul_add]
  congr 1
  rw [← mul_assoc, hcoef]

/-- A common full sum-capacity remains sufficient after probability normalization. -/
theorem scaledReservoirPair_originalMass_le_one (μ ν : Measure Interior) (R : ℝ≥0∞)
    (hRtop : R < ∞) (hRpos : 0 < R)
    (htotal : μ Set.univ + ν Set.univ ≤ R) :
    (R⁻¹ • μ) Set.univ + (R⁻¹ • ν) Set.univ ≤ 1 := by
  rw [Measure.smul_apply, smul_eq_mul, Measure.smul_apply, smul_eq_mul]
  calc
    R⁻¹ * μ Set.univ + R⁻¹ * ν Set.univ = R⁻¹ * (μ Set.univ + ν Set.univ) := by
      rw [mul_add]
    _ ≤ R⁻¹ * R := by
      simpa only [mul_comm R⁻¹] using mul_le_mul_left htotal R⁻¹
    _ = 1 := ENNReal.inv_mul_cancel hRpos.ne' hRtop.ne

/-- The common capacity-one reservoirs obtained by normalization are probability measures. -/
theorem scaledReservoirPair_isProbability (μ ν : Measure Interior) (R : ℝ≥0∞)
    (hRtop : R < ∞) (hRpos : 0 < R)
    (htotal : μ Set.univ + ν Set.univ ≤ R) :
    IsProbabilityMeasure (reservoirMeasure (R⁻¹ • μ) 1) ∧
      IsProbabilityMeasure (reservoirMeasure (R⁻¹ • ν) 1) := by
  rcases normalizedReservoirPair_isProbability μ ν R hRtop hRpos htotal with ⟨hμ, hν⟩
  exact ⟨by
      rw [← normalizedReservoirMeasure_eq_reservoirMeasure_inv μ R hRtop hRpos]
      exact hμ,
    by
      rw [← normalizedReservoirMeasure_eq_reservoirMeasure_inv ν R hRtop hRpos]
      exact hν⟩

private theorem reservoirMeasure_scale_back (μ : Measure Interior) (R : ℝ≥0∞)
    (hRtop : R < ∞) (hRpos : 0 < R) :
    R • reservoirMeasure (R⁻¹ • μ) 1 = reservoirMeasure μ R := by
  rw [← normalizedReservoirMeasure_eq_reservoirMeasure_inv μ R hRtop hRpos,
    normalizedReservoirMeasure, smul_smul, mul_comm R R⁻¹,
    ENNReal.inv_mul_cancel hRpos.ne' hRtop.ne, one_smul]

private theorem reservoirCompetitor_scale_down (μ ν : Measure Interior) (R : ℝ≥0∞)
    (hRtop : R < ∞) (hRpos : 0 < R) (γ : Measure (Space × Space))
    (hγ : γ.map Prod.fst = reservoirMeasure μ R ∧
      γ.map Prod.snd = reservoirMeasure ν R) :
    (R⁻¹ • γ).map Prod.fst = reservoirMeasure (R⁻¹ • μ) 1 ∧
      (R⁻¹ • γ).map Prod.snd = reservoirMeasure (R⁻¹ • ν) 1 := by
  constructor
  · rw [Measure.map_smul, hγ.1]
    simpa only [normalizedReservoirMeasure] using
      normalizedReservoirMeasure_eq_reservoirMeasure_inv μ R hRtop hRpos
  · rw [Measure.map_smul, hγ.2]
    simpa only [normalizedReservoirMeasure] using
      normalizedReservoirMeasure_eq_reservoirMeasure_inv ν R hRtop hRpos

private theorem reservoirCompetitor_scale_up (μ ν : Measure Interior) (R : ℝ≥0∞)
    (hRtop : R < ∞) (hRpos : 0 < R) (η : Measure (Space × Space))
    (hη : η.map Prod.fst = reservoirMeasure (R⁻¹ • μ) 1 ∧
      η.map Prod.snd = reservoirMeasure (R⁻¹ • ν) 1) :
    (R • η).map Prod.fst = reservoirMeasure μ R ∧
      (R • η).map Prod.snd = reservoirMeasure ν R := by
  constructor
  · rw [Measure.map_smul, hη.1]
    exact reservoirMeasure_scale_back μ R hRtop hRpos
  · rw [Measure.map_smul, hη.2]
    exact reservoirMeasure_scale_back ν R hRtop hRpos

/-- Scaling every reservoir competitor by `R⁻¹` and back by `R` identifies the two
all-competitor powered values. The identity uses no exponent or capacity-mass hypothesis and
retains extended-valued costs, including `∞`. -/
theorem reservoirPowerValue_normalization (p : ℝ) (μ ν : Measure Interior)
    (R : ℝ≥0∞) (hRtop : R < ∞) (hRpos : 0 < R) :
    reservoirPowerValue p μ ν R =
      R * reservoirPowerValue p (R⁻¹ • μ) (R⁻¹ • ν) 1 := by
  change (⨅ γ : Measure (Space × Space),
      ⨅ (_ : γ.map Prod.fst = reservoirMeasure μ R ∧
        γ.map Prod.snd = reservoirMeasure ν R),
        ∫⁻ z, collapsedPowerCost p z ∂γ) =
    R * (⨅ η : Measure (Space × Space),
      ⨅ (_ : η.map Prod.fst = reservoirMeasure (R⁻¹ • μ) 1 ∧
        η.map Prod.snd = reservoirMeasure (R⁻¹ • ν) 1),
        ∫⁻ z, collapsedPowerCost p z ∂η)
  apply le_antisymm
  · simp_rw [ENNReal.mul_iInf_of_ne hRpos.ne' hRtop.ne]
    refine le_iInf fun η => le_iInf fun hη => ?_
    have hγ := reservoirCompetitor_scale_up μ ν R hRtop hRpos η hη
    calc
      (⨅ γ : Measure (Space × Space),
          ⨅ (_ : γ.map Prod.fst = reservoirMeasure μ R ∧
            γ.map Prod.snd = reservoirMeasure ν R),
            ∫⁻ z, collapsedPowerCost p z ∂γ) ≤
          ∫⁻ z, collapsedPowerCost p z ∂(R • η) := by
        exact (iInf_le _ (R • η)).trans (iInf_le _ hγ)
      _ = R * ∫⁻ z, collapsedPowerCost p z ∂η := by
        rw [lintegral_smul_measure, smul_eq_mul]
  · simp_rw [ENNReal.mul_iInf_of_ne hRpos.ne' hRtop.ne]
    refine le_iInf fun γ => le_iInf fun hγ => ?_
    have hη := reservoirCompetitor_scale_down μ ν R hRtop hRpos γ hγ
    calc
      (⨅ η : Measure (Space × Space),
          ⨅ (_ : η.map Prod.fst = reservoirMeasure (R⁻¹ • μ) 1 ∧
            η.map Prod.snd = reservoirMeasure (R⁻¹ • ν) 1),
            R * ∫⁻ z, collapsedPowerCost p z ∂η) ≤
          R * ∫⁻ z, collapsedPowerCost p z ∂(R⁻¹ • γ) := by
        exact (iInf_le _ (R⁻¹ • γ)).trans (iInf_le _ hη)
      _ = ∫⁻ z, collapsedPowerCost p z ∂γ := by
        rw [lintegral_smul_measure, smul_eq_mul, ← mul_assoc,
          ENNReal.mul_inv_cancel hRpos.ne' hRtop.ne, one_mul]

/-- The reciprocal-`p` root obeys the corresponding reservoir scaling law whenever `p` is
positive. -/
theorem reservoirDistance_normalization (p : ℝ) (hp : 0 < p)
    (μ ν : Measure Interior) (R : ℝ≥0∞) (hRtop : R < ∞) (hRpos : 0 < R) :
    reservoirDistance p μ ν R =
      R ^ (1 / p) * reservoirDistance p (R⁻¹ • μ) (R⁻¹ • ν) 1 := by
  unfold reservoirDistance
  rw [reservoirPowerValue_normalization p μ ν R hRtop hRpos,
    ENNReal.mul_rpow_of_nonneg _ _ (one_div_nonneg.mpr hp.le)]

/-- Boundary transport equals the scaled probability-reservoir value for every
admissible positive finite common capacity. -/
theorem boundaryTransportDistance_eq_normalizedReservoirDistance
    (p : ℝ) (hp : 1 ≤ p) (μ ν : Measure Interior)
    (R : ℝ≥0∞) (hRtop : R < ∞) (hRpos : 0 < R)
    (htotal : μ Set.univ + ν Set.univ ≤ R) :
    boundaryTransportDistance p μ ν =
      R ^ (1 / p) * reservoirDistance p (R⁻¹ • μ) (R⁻¹ • ν) 1 :=
  (boundaryTransportDistance_eq_reservoirDistance p hp μ ν R hRtop htotal).trans
    (reservoirDistance_normalization p (lt_of_lt_of_le zero_lt_one hp)
      μ ν R hRtop hRpos)

end TDA.Persistence.BoundaryTransport
