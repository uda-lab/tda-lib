import TDA.Persistence.BoundaryTransportApproximation
import TDA.Persistence.BoundaryTransportAttainment
import Mathlib.Probability.Distributions.Geometric
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Same-mass approximation consumers

The nonatomic band and the countable noncompact family used in the attainment
examples both have diagonal moment one. Their approximants must preserve that
original mass, and their native boundary-transport error can be arbitrarily small.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Set
open scoped ENNReal NNReal

namespace TDA.Persistence.BoundaryTransport.ApproximationExamples

private def bandPoint (t : ℝ) : Interior := ⟨(t, t + 2), by linarith⟩

private theorem continuous_bandPoint : Continuous bandPoint := by
  exact (continuous_id.prodMk (continuous_id.add continuous_const)).subtype_mk _

private def bandLaw : Measure Interior := (volume.restrict (Icc (0 : ℝ) 1)).map bandPoint

private instance : IsFiniteMeasure (volume.restrict (Icc (0 : ℝ) 1)) :=
  isFiniteMeasure_restrict.mpr (by simp)

private instance : IsFiniteMeasure bandLaw := Measure.isFiniteMeasure_map _ _

private theorem bandLaw_mass : bandLaw univ = 1 := by
  rw [bandLaw, Measure.map_apply continuous_bandPoint.measurable MeasurableSet.univ]
  simp

private theorem bandLaw_moment (p : ℝ) :
    (∫⁻ x, ENNReal.ofReal (depth x ^ p) ∂bandLaw) = 1 := by
  rw [bandLaw, lintegral_map (by simp_rw [depth_eq]; fun_prop) continuous_bandPoint.measurable]
  have hdepth (t : ℝ) : depth (bandPoint t) = 1 := by simp [depth_eq, bandPoint]
  simp only [hdepth, Real.one_rpow, ENNReal.ofReal_one, lintegral_one]
  simp

private def scaledBandLaw : Measure Interior := (3 / 2 : ℝ≥0∞) • bandLaw

private theorem scaledBandLaw_mass : scaledBandLaw univ = 3 / 2 := by
  simp [scaledBandLaw, Measure.smul_apply, smul_eq_mul, bandLaw_mass]

private instance : IsFiniteMeasure scaledBandLaw := ⟨by rw [scaledBandLaw_mass]; finiteness⟩

private theorem scaledBandLaw_moment (p : ℝ) :
    (∫⁻ x, ENNReal.ofReal (depth x ^ p) ∂scaledBandLaw) = 3 / 2 := by
  rw [scaledBandLaw, lintegral_smul_measure, bandLaw_moment]
  simp

private def half : unitInterval := ⟨1 / 2, by constructor <;> norm_num⟩

private def rayPoint (n : ℕ) : Interior :=
  ⟨((2 : ℝ) ^ (n + 2), (2 : ℝ) ^ (n + 2) + 2), by linarith⟩

private def rayLaw : Measure Interior := (ProbabilityTheory.geometricMeasure half).map rayPoint

private instance : IsProbabilityMeasure rayLaw :=
  Measure.isProbabilityMeasure_map (measurable_of_countable rayPoint).aemeasurable

private theorem rayLaw_moment (p : ℝ) :
    (∫⁻ x, ENNReal.ofReal (depth x ^ p) ∂rayLaw) = 1 := by
  rw [rayLaw, lintegral_map (by simp_rw [depth_eq]; fun_prop) (measurable_of_countable rayPoint)]
  have hdepth (n : ℕ) : depth (rayPoint n) = 1 := by simp [depth_eq, rayPoint]
  simp only [hdepth, Real.one_rpow, ENNReal.ofReal_one, lintegral_one]
  simp

private theorem scaled_nonatomic_approximation (p : ℝ) (hp : 1 ≤ p)
    (ε : ℝ≥0∞) (hε : 0 < ε) :
    ∃ D : FiniteWeightedDiagram, atomicMeasure D univ = 3 / 2 ∧
      boundaryTransportDistance p scaledBandLaw (atomicMeasure D) < ε := by
  obtain ⟨D, hmass, hnear⟩ := exists_atomicMeasure_approx_same_mass p hp scaledBandLaw
    (by rw [scaledBandLaw_moment]; finiteness) ε hε
  exact ⟨D, hmass.trans scaledBandLaw_mass, hnear⟩

private theorem noncompact_approximation_with_optimizer (p : ℝ) (hp : 1 ≤ p)
    (ε : ℝ≥0∞) (hε : 0 < ε) :
    ∃ (D : FiniteWeightedDiagram) (π : Measure PlanSpace),
      atomicMeasure D univ = 1 ∧ IsBoundaryPlan π rayLaw (atomicMeasure D) ∧
      (∫⁻ z, planPowerCost p z ∂π) ^ (1 / p) =
        boundaryTransportDistance p rayLaw (atomicMeasure D) ∧
      (∫⁻ z, planPowerCost p z ∂π) ^ (1 / p) < ε := by
  obtain ⟨D, hmass, hnear⟩ := exists_atomicMeasure_approx_same_mass p hp rayLaw
    (by rw [rayLaw_moment]; simp) ε hε
  have : IsFiniteMeasure (atomicMeasure D) := atomicMeasure_isFinite D
  obtain ⟨π, hπ, _, hroot⟩ := exists_minimizing_boundaryPlan_rooted p hp rayLaw (atomicMeasure D)
  exact ⟨D, π, by simpa using hmass, hπ, hroot, hroot.trans_lt hnear⟩

private theorem zero_approximation (p : ℝ) (hp : 1 ≤ p)
    (ε : ℝ≥0∞) (hε : 0 < ε) :
    ∃ D : FiniteWeightedDiagram, atomicMeasure D = 0 ∧
      boundaryTransportDistance p 0 (atomicMeasure D) < ε := by
  obtain ⟨D, hmass, hnear⟩ := exists_atomicMeasure_approx_same_mass p hp 0 (by simp) ε hε
  exact ⟨D, Measure.measure_univ_eq_zero.mp (by simpa using hmass), hnear⟩

end TDA.Persistence.BoundaryTransport.ApproximationExamples
