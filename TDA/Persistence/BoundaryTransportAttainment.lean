/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

The fixed-marginal closed/tight-plan argument is adapted from
TauCeti/MeasureTheory/OptimalTransport/Compactness.lean at
575dbdfaf4ae0df6e5bb35bb39e16458f028c91f. Modifications specialize it to
BoundaryTransport.Space and the pinned mathlib probability-map interface.
The powered-cost truncation, native reservoir rescaling and reverse-plan
consumers below use the library's existing boundary-transport definitions.
-/
import TDA.Persistence.ReservoirNormalization
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-!
# Minimizing plans for finite boundary measures

The normalized reservoir competitors form a nonempty weakly compact set.
Bounded continuous truncations make the full powered metric integral lower
semicontinuous, including infinite values. A minimum therefore exists.
Rescaling and the proved reverse comparison give a genuine boundary optimizer
for arbitrary finite Borel inputs. Finite diagonal moments ensure finite cost.
-/

noncomputable section
set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal NNReal Topology BoundedContinuousFunction
namespace TDA.Persistence.BoundaryTransport

private def plans (μ ν : ProbabilityMeasure Space) : Set (ProbabilityMeasure (Space × Space)) :=
  {γ | γ.map measurable_fst.aemeasurable = μ ∧ γ.map measurable_snd.aemeasurable = ν}

private theorem compact_plans (μ ν : ProbabilityMeasure Space) : IsCompact (plans μ ν) := by
  have hclosed : IsClosed (plans μ ν) :=
    (isClosed_eq (ProbabilityMeasure.continuous_map continuous_fst) continuous_const).inter
      (isClosed_eq (ProbabilityMeasure.continuous_map continuous_snd) continuous_const)
  have htight : IsTightMeasureSet {(γ : ProbabilityMeasure (Space × Space)).toMeasure |
      γ ∈ plans μ ν} := by
    apply IsTightMeasureSet.prodMk
    · apply (isTightMeasureSet_singleton (μ := μ.toMeasure)).subset
      rintro _ ⟨_, ⟨γ, hγ, rfl⟩, rfl⟩
      exact congrArg ProbabilityMeasure.toMeasure hγ.1
    · apply (isTightMeasureSet_singleton (μ := ν.toMeasure)).subset
      rintro _ ⟨_, ⟨γ, hγ, rfl⟩, rfl⟩
      exact congrArg ProbabilityMeasure.toMeasure hγ.2
  simpa only [hclosed.closure_eq] using isCompact_closure_of_isTightMeasureSet htight

private def truncation (p : ℝ) (hp : 0 ≤ p) (n : ℕ) : (Space × Space) →ᵇ ℝ≥0 :=
  (BoundedContinuousFunction.ofNormedAddCommGroup
    (fun z : Space × Space => min (dist z.1 z.2 ^ p) (n : ℝ))
    (((Real.continuous_rpow_const hp).comp continuous_dist).min continuous_const)
    n (by
      intro z
      rw [Real.norm_eq_abs, abs_of_nonneg (le_min (Real.rpow_nonneg dist_nonneg _) (by positivity))]
      exact min_le_right _ _)).nnrealPart

private theorem truncation_coe (p : ℝ) (hp : 0 ≤ p) (n : ℕ) (z : Space × Space) :
    (truncation p hp n z : ℝ≥0∞) = min (collapsedPowerCost p z) (n : ℝ≥0∞) := by
  change ENNReal.ofReal (min (dist z.1 z.2 ^ p) (n : ℝ)) = _
  simp [collapsedPowerCost, ENNReal.ofReal_min]

private theorem cost_lsc (p : ℝ) (hp : 0 ≤ p) :
    LowerSemicontinuous (fun γ : ProbabilityMeasure (Space × Space) =>
      ∫⁻ z, collapsedPowerCost p z ∂γ.toMeasure) := by
  have heq (γ : ProbabilityMeasure (Space × Space)) :
      (∫⁻ z, collapsedPowerCost p z ∂γ.toMeasure) =
        ⨆ n : ℕ, ∫⁻ z, (truncation p hp n z : ℝ≥0∞) ∂γ.toMeasure := by
    rw [← lintegral_iSup (fun n => (truncation p hp n).continuous.measurable.coe_nnreal_ennreal)
      (by intro i j hij z; simpa only [truncation_coe] using
        min_le_min_left (collapsedPowerCost p z) (show (i : ℝ≥0∞) ≤ j from Nat.cast_le.mpr hij))]
    apply lintegral_congr
    intro z
    simp_rw [truncation_coe]
    rw [← inf_iSup_eq, ENNReal.iSup_natCast, inf_top_eq]
  simp_rw [heq]
  apply lowerSemicontinuous_iSup
  intro n
  exact ((FiniteMeasure.continuous_lintegral_boundedContinuousFunction (truncation p hp n)).comp
    ProbabilityMeasure.toFiniteMeasure_continuous).lowerSemicontinuous

private theorem probability_minimizer (p : ℝ) (hp : 0 ≤ p) (μ ν : ProbabilityMeasure Space) :
    ∃ γ : ProbabilityMeasure (Space × Space), γ ∈ plans μ ν ∧
      IsMinOn (fun τ : ProbabilityMeasure (Space × Space) =>
        ∫⁻ z, collapsedPowerCost p z ∂τ.toMeasure) (plans μ ν) γ := by
  have hne : (plans μ ν).Nonempty := ⟨μ.prod ν, by simp [plans]⟩
  exact ((cost_lsc p hp).lowerSemicontinuousOn _).exists_isMinOn hne (compact_plans μ ν)


private theorem reservoir_minimizer (p : ℝ) (hp : 0 ≤ p)
    (μ ν : Measure Interior) (R : ℝ≥0∞) (hRtop : R < ∞) (hRpos : 0 < R)
    (hμR : μ univ ≤ R) (hνR : ν univ ≤ R) :
    ∃ γ : Measure (Space × Space),
      γ.map Prod.fst = reservoirMeasure μ R ∧
      γ.map Prod.snd = reservoirMeasure ν R ∧
      (∫⁻ z, collapsedPowerCost p z ∂γ) = reservoirPowerValue p μ ν R := by
  let A := normalizedReservoirProbability μ R hRtop hRpos hμR
  let B := normalizedReservoirProbability ν R hRtop hRpos hνR
  obtain ⟨η, hη, hmin⟩ := probability_minimizer p hp A B
  have scale_back (ξ : Measure Interior) :
      R • normalizedReservoirMeasure ξ R = reservoirMeasure ξ R := by
    rw [normalizedReservoirMeasure, smul_smul,
      ENNReal.mul_inv_cancel hRpos.ne' hRtop.ne, one_smul]
  let γ := R • η.toMeasure
  have hη₁ : η.toMeasure.map Prod.fst = normalizedReservoirMeasure μ R :=
    congrArg ProbabilityMeasure.toMeasure hη.1
  have hη₂ : η.toMeasure.map Prod.snd = normalizedReservoirMeasure ν R :=
    congrArg ProbabilityMeasure.toMeasure hη.2
  have hγ₁ : γ.map Prod.fst = reservoirMeasure μ R := by
    rw [Measure.map_smul, hη₁]
    exact scale_back μ
  have hγ₂ : γ.map Prod.snd = reservoirMeasure ν R := by
    rw [Measure.map_smul, hη₂]
    exact scale_back ν
  refine ⟨γ, hγ₁, hγ₂, le_antisymm ?_
    (reservoirPowerValue_le_plan p μ ν R γ hγ₁ hγ₂)⟩
  unfold reservoirPowerValue
  refine le_iInf fun σ => le_iInf fun hσ => ?_
  have hσmass : σ univ = R := by
    have h := congrArg (fun m : Measure Space => m univ) hσ.1
    simpa [Measure.map_apply measurable_fst MeasurableSet.univ,
      reservoirMeasure_mass μ R hμR] using h
  have hprob : IsProbabilityMeasure (R⁻¹ • σ) := ⟨by
    simp only [Measure.smul_apply, smul_eq_mul, hσmass,
      ENNReal.inv_mul_cancel hRpos.ne' hRtop.ne]⟩
  let τ : ProbabilityMeasure (Space × Space) := ⟨R⁻¹ • σ, hprob⟩
  have hτ : τ ∈ plans A B := by
    constructor
    · apply Subtype.ext
      change (R⁻¹ • σ).map Prod.fst = normalizedReservoirMeasure μ R
      rw [Measure.map_smul, hσ.1]
      rfl
    · apply Subtype.ext
      change (R⁻¹ • σ).map Prod.snd = normalizedReservoirMeasure ν R
      rw [Measure.map_smul, hσ.2]
      rfl
  have hcost : R * (∫⁻ z, collapsedPowerCost p z ∂η.toMeasure) ≤
      R * (∫⁻ z, collapsedPowerCost p z ∂τ.toMeasure) := by
    exact mul_le_mul' le_rfl (hmin hτ)
  change R * (∫⁻ z, collapsedPowerCost p z ∂η.toMeasure) ≤
    R * (∫⁻ z, collapsedPowerCost p z ∂(R⁻¹ • σ)) at hcost
  simpa only [γ, lintegral_smul_measure, smul_eq_mul, ← mul_assoc,
    ENNReal.mul_inv_cancel hRpos.ne' hRtop.ne, one_mul] using hcost

/-- Every finite positive full sum-capacity reservoir admits a genuine minimizing plan.
The continuous powered metric objective may have value infinity. -/
theorem exists_minimizing_reservoirPlan (p : ℝ) (hp : 0 ≤ p)
    (μ ν : Measure Interior) (R : ℝ≥0∞) (hRtop : R < ∞) (hRpos : 0 < R)
    (htotal : μ univ + ν univ ≤ R) :
    ∃ γ : Measure (Space × Space),
      γ.map Prod.fst = reservoirMeasure μ R ∧
      γ.map Prod.snd = reservoirMeasure ν R ∧
      (∫⁻ z, collapsedPowerCost p z ∂γ) = reservoirPowerValue p μ ν R :=
  reservoir_minimizer p hp μ ν R hRtop hRpos
    (le_self_add.trans htotal) (le_add_self.trans htotal)

/-- Every pair of finite Borel inputs admits a genuine minimizing boundary plan,
including when its optimal cost is infinite. No moment or support condition is needed. -/
theorem exists_minimizing_boundaryPlan (p : ℝ) (hp : 1 ≤ p)
    (μ ν : Measure Interior) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    ∃ π : Measure PlanSpace, IsBoundaryPlan π μ ν ∧
      (∫⁻ z, planPowerCost p z ∂π) = boundaryTransportPowerValue p μ ν := by
  let R := μ univ + ν univ + 1
  have hRtop : R < ∞ := ENNReal.add_lt_top.mpr
    ⟨ENNReal.add_lt_top.mpr ⟨measure_lt_top μ _, measure_lt_top ν _⟩, by simp⟩
  have hRpos : 0 < R := (zero_lt_one : (0 : ℝ≥0∞) < 1).trans_le le_add_self
  have htotal : μ univ + ν univ ≤ R := le_self_add
  obtain ⟨γ, hγ₁, hγ₂, hγcost⟩ := exists_minimizing_reservoirPlan p (by linarith) μ ν R hRtop hRpos htotal
  obtain ⟨π, hπ, hcost⟩ := Reverse.exists_boundaryPlan_cost_le p hp γ μ ν R hγ₁ hγ₂
  refine ⟨π, hπ, le_antisymm ?_ (boundaryTransportPowerValue_le_plan p hπ)⟩
  exact hcost.trans_eq (hγcost.trans
    (boundaryTransportPowerValue_eq_reservoirPowerValue p hp μ ν R hRtop htotal).symm)


/-- Finite diagonal persistence moments give a minimizing plan of finite powered cost. -/
theorem exists_finite_cost_minimizing_boundaryPlan (p : ℝ) (hp : 1 ≤ p)
    (μ ν : Measure Interior) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : (∫⁻ x, ENNReal.ofReal (depth x ^ p) ∂μ) < ∞)
    (hν : (∫⁻ x, ENNReal.ofReal (depth x ^ p) ∂ν) < ∞) :
    ∃ π : Measure PlanSpace, IsBoundaryPlan π μ ν ∧
      (∫⁻ z, planPowerCost p z ∂π) = boundaryTransportPowerValue p μ ν ∧
      (∫⁻ z, planPowerCost p z ∂π) < ∞ := by
  obtain ⟨π, hπ, hcost⟩ := exists_minimizing_boundaryPlan p hp μ ν
  exact ⟨π, hπ, hcost, hcost ▸ boundaryTransportPowerValue_lt_top p μ ν hμ hν⟩


/-- The same minimizing measure realizes both the powered and rooted boundary values. -/
theorem exists_minimizing_boundaryPlan_rooted (p : ℝ) (hp : 1 ≤ p)
    (μ ν : Measure Interior) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    ∃ π : Measure PlanSpace, IsBoundaryPlan π μ ν ∧
      (∫⁻ z, planPowerCost p z ∂π) = boundaryTransportPowerValue p μ ν ∧
      (∫⁻ z, planPowerCost p z ∂π) ^ (1 / p) = boundaryTransportDistance p μ ν := by
  obtain ⟨π, hπ, hcost⟩ := exists_minimizing_boundaryPlan p hp μ ν
  exact ⟨π, hπ, hcost, congrArg (fun a : ℝ≥0∞ => a ^ (1 / p)) hcost⟩

end TDA.Persistence.BoundaryTransport
