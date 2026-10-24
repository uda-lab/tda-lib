import TDA.Persistence.BoundaryTransportMetric
import TDA.Persistence.BoundaryTransportIndexed
import TDA.Persistence.BoundaryTransportApproximation
import TDA.Persistence.BoundaryTransportZero

/-!
# Metric and normalization consumers

Far unit atoms distinguish the full sum-of-masses reservoir condition from a
maximum-only bound. Native atomic formulas evaluate the true boundary optimum.
The metric laws also transfer same-mass approximation errors to distances.
-/

set_option autoImplicit false
noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace TDA.Persistence.BoundaryTransport.MetricExamples

private theorem reservoirMeasure_dirac_one (x : Interior) :
    reservoirMeasure (Measure.dirac x) (1 : ℝ≥0∞) = Measure.dirac (Space.point x) := by
  rw [reservoirMeasure, Measure.map_dirac' continuous_point.measurable]
  simp

private theorem unit_reservoir_marginal_forces_cost_four
    (γ : Measure (Space × Space))
    (hγ : γ.map Prod.fst = reservoirMeasure (Measure.dirac Reverse.farSource) 1 ∧
      γ.map Prod.snd = reservoirMeasure (Measure.dirac Reverse.farTarget) 1) :
    (∫⁻ z, collapsedPowerCost 2 z ∂γ) = 4 := by
  have hfirst : γ.map Prod.fst = Measure.dirac (Space.point Reverse.farSource) :=
    hγ.1.trans (reservoirMeasure_dirac_one Reverse.farSource)
  have hsecond : γ.map Prod.snd = Measure.dirac (Space.point Reverse.farTarget) :=
    hγ.2.trans (reservoirMeasure_dirac_one Reverse.farTarget)
  have hfirst_map : ∀ᵐ y ∂γ.map Prod.fst, y = Space.point Reverse.farSource := by
    rw [hfirst]
    simp
  have hsecond_map : ∀ᵐ y ∂γ.map Prod.snd, y = Space.point Reverse.farTarget := by
    rw [hsecond]
    simp
  have hfirst_ae : ∀ᵐ z ∂γ, z.1 = Space.point Reverse.farSource :=
    (ae_map_iff (by fun_prop : AEMeasurable Prod.fst γ)
      (by measurability : MeasurableSet {y : Space | y = Space.point Reverse.farSource})).1
      hfirst_map
  have hsecond_ae : ∀ᵐ z ∂γ, z.2 = Space.point Reverse.farTarget :=
    (ae_map_iff (by fun_prop : AEMeasurable Prod.snd γ)
      (by measurability : MeasurableSet {y : Space | y = Space.point Reverse.farTarget})).1
      hsecond_map
  have hmass : γ Set.univ = 1 := by
    have hmap := congrArg (fun η : Measure Space => η Set.univ) hfirst
    rw [Measure.map_apply measurable_fst MeasurableSet.univ] at hmap
    simpa using hmap
  have hcost_ae : ∀ᵐ z ∂γ, collapsedPowerCost 2 z = 4 := by
    filter_upwards [hfirst_ae, hsecond_ae] with z hfst hsnd
    rw [collapsedPowerCost, hfst, hsnd]
    rw [show dist (Space.point Reverse.farSource) (Space.point Reverse.farTarget) = 2
      from far_points_shortcut]
    norm_num
  calc
    (∫⁻ z, collapsedPowerCost 2 z ∂γ) = ∫⁻ z, (4 : ℝ≥0∞) ∂γ :=
      lintegral_congr_ae hcost_ae
    _ = 4 := by rw [lintegral_const, hmass]; norm_num

/-- At unit capacity every feasible coupling is concentrated on the far point pair,
so its squared collapsed cost is four. -/
private theorem far_atoms_unit_capacity_value :
    reservoirPowerValue 2 (Measure.dirac Reverse.farSource)
      (Measure.dirac Reverse.farTarget) (1 : ℝ≥0∞) = 4 := by
  apply le_antisymm
  · let γ : Measure (Space × Space) :=
      Measure.dirac (Space.point Reverse.farSource, Space.point Reverse.farTarget)
    have hfirst : γ.map Prod.fst =
        reservoirMeasure (Measure.dirac Reverse.farSource) (1 : ℝ≥0∞) := by
      dsimp [γ]
      rw [Measure.map_dirac' measurable_fst, reservoirMeasure_dirac_one]
    have hsecond : γ.map Prod.snd =
        reservoirMeasure (Measure.dirac Reverse.farTarget) (1 : ℝ≥0∞) := by
      dsimp [γ]
      rw [Measure.map_dirac' measurable_snd, reservoirMeasure_dirac_one]
    calc
      reservoirPowerValue 2 (Measure.dirac Reverse.farSource)
          (Measure.dirac Reverse.farTarget) (1 : ℝ≥0∞) ≤
          ∫⁻ z, collapsedPowerCost 2 z ∂γ :=
        reservoirPowerValue_le_plan 2 _ _ 1 γ hfirst hsecond
      _ = 4 := by
        simpa [γ, collapsedPowerCost] using Reverse.far_shortcut_original_cost
  · unfold reservoirPowerValue
    refine le_iInf fun γ => le_iInf fun hγ => ?_
    exact (unit_reservoir_marginal_forces_cost_four γ hγ).symm.le

/-- The capacity-one fixture violates the required sum-of-masses capacity bound. -/
private theorem far_atoms_exceed_unit_capacity :
    (Measure.dirac Reverse.farSource : Measure Interior) Set.univ +
      (Measure.dirac Reverse.farTarget : Measure Interior) Set.univ = 2 := by
  norm_num


private theorem indexed_unit_dirac (x : Interior) :
    atomicMeasure (FiniteWeightedDiagram.ofIndexed (fun _ : Fin 1 => 1) (fun _ => x)) =
      Measure.dirac x := by
  rw [atomicMeasure_ofIndexed]
  simp

private theorem far_atoms_boundary_value :
    boundaryTransportPowerValue 2 (Measure.dirac Reverse.farSource)
      (Measure.dirac Reverse.farTarget) = 2 := by
  rw [← indexed_unit_dirac Reverse.farSource, ← indexed_unit_dirac Reverse.farTarget,
    boundaryTransportPowerValue_ofIndexed_unit 2 (by norm_num),
    finitePowerMatchingCost_singleton]
  norm_num [Reverse.farSource, Reverse.farTarget, finitePairCost, diagonalCost]

private theorem full_capacity_countercontrol :
    reservoirPowerValue 2 (Measure.dirac Reverse.farSource)
        (Measure.dirac Reverse.farTarget) 1 = 4 ∧
      boundaryTransportPowerValue 2 (Measure.dirac Reverse.farSource)
        (Measure.dirac Reverse.farTarget) = 2 ∧
      reservoirPowerValue 2 (Measure.dirac Reverse.farSource)
        (Measure.dirac Reverse.farTarget) 2 = 2 := by
  refine ⟨far_atoms_unit_capacity_value, far_atoms_boundary_value, ?_⟩
  rw [← boundaryTransportPowerValue_eq_reservoirPowerValue 2 (by norm_num)
    (Measure.dirac Reverse.farSource) (Measure.dirac Reverse.farTarget) 2
    (by norm_num) (by norm_num)]
  exact far_atoms_boundary_value

private def translatedPoint (t : ℝ) : Interior := ⟨(t, t + 10), by linarith⟩

private theorem translated_powered_values :
    boundaryTransportPowerValue 1 (Measure.dirac (translatedPoint 0))
        (Measure.dirac (translatedPoint 1)) = 1 ∧
      boundaryTransportPowerValue 1 (Measure.dirac (translatedPoint 1))
        (Measure.dirac (translatedPoint 2)) = 1 ∧
      boundaryTransportPowerValue 1 (Measure.dirac (translatedPoint 0))
        (Measure.dirac (translatedPoint 2)) = 2 := by
  have h (a b : ℝ) :
      boundaryTransportPowerValue 1 (Measure.dirac (translatedPoint a))
        (Measure.dirac (translatedPoint b)) =
      ENNReal.ofReal (min ((finitePairCost (translatedPoint a).1
        (translatedPoint b).1).toReal ^ (1 : ℝ))
        ((diagonalCost (translatedPoint a).1).toReal ^ (1 : ℝ) +
          (diagonalCost (translatedPoint b).1).toReal ^ (1 : ℝ))) := by
    rw [← indexed_unit_dirac (translatedPoint a), ← indexed_unit_dirac (translatedPoint b),
      boundaryTransportPowerValue_ofIndexed_unit 1 (by norm_num),
      finitePowerMatchingCost_singleton]
  simp only [h]
  norm_num [translatedPoint, finitePairCost, diagonalCost]

private theorem sharp_atomic_triangle :
    boundaryTransportDistance 1 (Measure.dirac (translatedPoint 0))
        (Measure.dirac (translatedPoint 2)) =
      boundaryTransportDistance 1 (Measure.dirac (translatedPoint 0))
        (Measure.dirac (translatedPoint 1)) +
      boundaryTransportDistance 1 (Measure.dirac (translatedPoint 1))
        (Measure.dirac (translatedPoint 2)) := by
  rcases translated_powered_values with ⟨h01, h12, h02⟩
  norm_num [boundaryTransportDistance, h01, h12, h02]

private theorem approximation_distance_bounds (p : ℝ) (hp : 1 ≤ p)
    (μ ν : Measure Interior) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : (∫⁻ x, ENNReal.ofReal (depth x ^ p) ∂μ) < ∞)
    (hν : (∫⁻ x, ENNReal.ofReal (depth x ^ p) ∂ν) < ∞)
    (ε : ℝ≥0∞) (hε : 0 < ε) :
    ∃ D E : FiniteWeightedDiagram,
      atomicMeasure D univ = μ univ ∧ atomicMeasure E univ = ν univ ∧
      boundaryTransportDistance p μ ν ≤
        boundaryTransportDistance p (atomicMeasure D) (atomicMeasure E) + (ε + ε) ∧
      boundaryTransportDistance p (atomicMeasure D) (atomicMeasure E) ≤
        boundaryTransportDistance p μ ν + (ε + ε) := by
  obtain ⟨D, hD, hnearD⟩ := exists_atomicMeasure_approx_same_mass p hp μ hμ ε hε
  obtain ⟨E, hE, hnearE⟩ := exists_atomicMeasure_approx_same_mass p hp ν hν ε hε
  have : IsFiniteMeasure (atomicMeasure D) := atomicMeasure_isFinite D
  have : IsFiniteMeasure (atomicMeasure E) := atomicMeasure_isFinite E
  have hDrev : boundaryTransportDistance p (atomicMeasure D) μ ≤ ε := by
    rw [boundaryTransportDistance_symm]
    exact hnearD.le
  have hErev : boundaryTransportDistance p (atomicMeasure E) ν ≤ ε := by
    rw [boundaryTransportDistance_symm]
    exact hnearE.le
  refine ⟨D, E, hD, hE, ?_, ?_⟩
  · calc
      boundaryTransportDistance p μ ν ≤ boundaryTransportDistance p μ (atomicMeasure D) +
          boundaryTransportDistance p (atomicMeasure D) ν :=
        boundaryTransportDistance_triangle p hp μ (atomicMeasure D) ν
      _ ≤ boundaryTransportDistance p μ (atomicMeasure D) +
          (boundaryTransportDistance p (atomicMeasure D) (atomicMeasure E) +
            boundaryTransportDistance p (atomicMeasure E) ν) :=
        add_le_add le_rfl (boundaryTransportDistance_triangle p hp (atomicMeasure D)
          (atomicMeasure E) ν)
      _ ≤ ε + (boundaryTransportDistance p (atomicMeasure D) (atomicMeasure E) + ε) :=
        add_le_add hnearD.le (add_le_add le_rfl hErev)
      _ = boundaryTransportDistance p (atomicMeasure D) (atomicMeasure E) + (ε + ε) := by
        ac_rfl
  · calc
      boundaryTransportDistance p (atomicMeasure D) (atomicMeasure E) ≤
          boundaryTransportDistance p (atomicMeasure D) μ +
            boundaryTransportDistance p μ (atomicMeasure E) :=
        boundaryTransportDistance_triangle p hp (atomicMeasure D) μ (atomicMeasure E)
      _ ≤ boundaryTransportDistance p (atomicMeasure D) μ +
          (boundaryTransportDistance p μ ν + boundaryTransportDistance p ν (atomicMeasure E)) :=
        add_le_add le_rfl (boundaryTransportDistance_triangle p hp μ ν (atomicMeasure E))
      _ ≤ ε + (boundaryTransportDistance p μ ν + ε) :=
        add_le_add hDrev (add_le_add le_rfl hnearE.le)
      _ = boundaryTransportDistance p μ ν + (ε + ε) := by ac_rfl

private def fractionalLaw : Measure Interior :=
  (3 / 2 : ℝ≥0∞) • Measure.dirac Reverse.farSource

private theorem fractionalLaw_mass : fractionalLaw univ = 3 / 2 := by
  simp [fractionalLaw, Measure.smul_apply, smul_eq_mul]

private theorem fractional_probability_norm :
    IsProbabilityMeasure (normalizedReservoirMeasure fractionalLaw 2) ∧
      IsProbabilityMeasure (normalizedReservoirMeasure 0 2) ∧
      (2 : ℝ≥0∞) *
        (⨅ γ : Measure (Space × Space),
          ⨅ (_ : γ.map Prod.fst = normalizedReservoirMeasure fractionalLaw 2 ∧
            γ.map Prod.snd = normalizedReservoirMeasure 0 2),
            eLpNorm (fun z : Space × Space => edist z.1 z.2) 1 γ) = 3 / 2 := by
  have htotal : fractionalLaw univ + (0 : Measure Interior) univ ≤ (2 : ℝ≥0∞) := by
    rw [fractionalLaw_mass]
    simpa using ((ENNReal.div_le_iff (by norm_num) (by norm_num)).2
      (by norm_num : (3 : ℝ≥0∞) ≤ 2 * 2) : (3 / 2 : ℝ≥0∞) ≤ 2)
  rcases normalizedReservoirPair_isProbability fractionalLaw 0 2
    (by norm_num) (by norm_num) htotal with ⟨hμ, hν⟩
  refine ⟨hμ, hν, ?_⟩
  have hnorm := boundaryTransportDistance_eq_normalized_iInf_eLpNorm 1 (by norm_num)
    fractionalLaw 0 2 (by norm_num) (by norm_num) htotal
  norm_num at hnorm
  rw [← hnorm, boundaryTransportDistance_zero_target 1 (by norm_num) fractionalLaw
    (by rw [fractionalLaw_mass]; finiteness)]
  norm_num [fractionalLaw, lintegral_smul_measure, depth_eq, Reverse.farSource]

end TDA.Persistence.BoundaryTransport.MetricExamples
