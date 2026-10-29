import TDA.Persistence.BoundaryTransportIndexed
import TDA.Persistence.BoundaryTransportComparison
import Mathlib.MeasureTheory.Function.SimpleFuncDense
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

/-!
# Finite diagrams from simple interior quantizers

A simple function assigns finitely many interior targets to a finite measure.
Its fiber masses give a native coalesced weighted diagram whose atomic measure
is exactly the pushforward of the original measure.
-/

set_option autoImplicit false
noncomputable section

namespace TDA.Persistence.BoundaryTransport

open Set MeasureTheory Filter Topology
open scoped Classical ENNReal NNReal
local infixr:25 " →ₛ " => SimpleFunc

/-- The native diagram of a finite-measure simple interior quantizer. -/
def simpleFuncDiagram (μ : Measure Interior) [IsFiniteMeasure μ]
    (T : Interior →ₛ Interior) : FiniteWeightedDiagram :=
  FiniteWeightedDiagram.ofIndexed
    (fun q : T.range => (μ (T ⁻¹' {q.1})).toNNReal) (fun q => q.1)

/-- The diagram records the exact pushforward, including zero-weight fibers. -/
theorem atomicMeasure_simpleFuncDiagram (μ : Measure Interior) [IsFiniteMeasure μ]
    (T : Interior →ₛ Interior) :
    atomicMeasure (simpleFuncDiagram μ T) = μ.map T := by
  classical
  rw [simpleFuncDiagram, atomicMeasure_ofIndexed]
  simp_rw [ENNReal.coe_toNNReal (ne_top_of_le_ne_top (measure_ne_top μ Set.univ)
    (measure_mono (subset_univ _)))]
  exact (Finset.sum_coe_sort T.range
    (fun q => μ (T ⁻¹' {q}) • Measure.dirac q)).trans
    (((Measure.ae_mem_finset_iff_map_eq_sum_dirac
    (f := T) (μ := μ) (s := T.range) T.measurable.aemeasurable).mp
    (Filter.Eventually.of_forall T.mem_range_self)).symm)

/-- Finite quantization preserves the original, unnormalized mass. -/
theorem simpleFuncDiagram_mass (μ : Measure Interior) [IsFiniteMeasure μ]
    (T : Interior →ₛ Interior) :
    atomicMeasure (simpleFuncDiagram μ T) Set.univ = μ Set.univ := by
  rw [atomicMeasure_simpleFuncDiagram, Measure.map_apply T.measurable MeasurableSet.univ]
  rfl

@[simp] theorem simpleFuncDiagram_zero (T : Interior →ₛ Interior) :
    simpleFuncDiagram 0 T = 0 := by
  simp [simpleFuncDiagram, FiniteWeightedDiagram.ofIndexed]

/-- A reservoir capacity for an equal-mass quantizer, exceeding the sum of its masses. -/
def quantizerCapacity (μ : Measure Interior) : ℝ≥0∞ :=
  μ Set.univ + μ Set.univ + 1

private theorem quantizerCapacity_finite (μ : Measure Interior) [IsFiniteMeasure μ] :
    quantizerCapacity μ < ∞ := by
  unfold quantizerCapacity
  finiteness

private theorem quantizerCapacity_le (μ : Measure Interior) :
    μ Set.univ + μ Set.univ ≤ quantizerCapacity μ := by
  unfold quantizerCapacity
  exact le_add_of_nonneg_right bot_le

/-- The graph of a quantizer, padded by a zero-cost boundary–boundary atom. -/
def simpleFuncReservoirPlan (μ : Measure Interior) (T : Interior →ₛ Interior) :
    Measure (Space × Space) :=
  μ.map (fun x => (Space.point x, Space.point (T x))) +
    (quantizerCapacity μ - μ Set.univ) •
      Measure.dirac (Space.boundary, Space.boundary)

theorem simpleFuncReservoirPlan_first (μ : Measure Interior) [IsFiniteMeasure μ]
    (T : Interior →ₛ Interior) :
    (simpleFuncReservoirPlan μ T).map Prod.fst =
      reservoirMeasure μ (quantizerCapacity μ) := by
  unfold simpleFuncReservoirPlan reservoirMeasure
  have hpair : Measurable (fun x => (Space.point x, Space.point (T x))) :=
    continuous_point.measurable.prodMk (continuous_point.measurable.comp T.measurable)
  rw [Measure.map_add _ _ measurable_fst, Measure.map_smul,
    Measure.map_map measurable_fst hpair]
  simp only [Function.comp_def, Measure.map_dirac]

theorem simpleFuncReservoirPlan_second (μ : Measure Interior) [IsFiniteMeasure μ]
    (T : Interior →ₛ Interior) :
    (simpleFuncReservoirPlan μ T).map Prod.snd =
      reservoirMeasure (atomicMeasure (simpleFuncDiagram μ T)) (quantizerCapacity μ) := by
  rw [atomicMeasure_simpleFuncDiagram]
  unfold simpleFuncReservoirPlan reservoirMeasure
  have hpair : Measurable (fun x => (Space.point x, Space.point (T x))) :=
    continuous_point.measurable.prodMk (continuous_point.measurable.comp T.measurable)
  rw [Measure.map_add _ _ measurable_snd, Measure.map_smul,
    Measure.map_map measurable_snd hpair]
  · simp only [Function.comp_def, Measure.map_dirac]
    congr 1
    · rw [Measure.map_map]
      · rfl
      · exact continuous_point.measurable
      · exact T.measurable
    · rw [Measure.map_apply T.measurable MeasurableSet.univ]
      rfl

/-- Graph coupling gives a direct bound on powered boundary transport. -/
theorem boundaryTransportPowerValue_simpleFuncDiagram_le
    (p : ℝ) (hp : 1 ≤ p) (μ : Measure Interior) [IsFiniteMeasure μ]
    (T : Interior →ₛ Interior) :
    boundaryTransportPowerValue p μ (atomicMeasure (simpleFuncDiagram μ T)) ≤
      ∫⁻ x, ENNReal.ofReal ((dist (Space.point x) (Space.point (T x))) ^ p) ∂μ := by
  let R := quantizerCapacity μ
  have hmass : μ Set.univ + atomicMeasure (simpleFuncDiagram μ T) Set.univ ≤ R := by
    rw [simpleFuncDiagram_mass]
    exact quantizerCapacity_le μ
  rw [boundaryTransportPowerValue_eq_reservoirPowerValue p hp μ
    (atomicMeasure (simpleFuncDiagram μ T)) R (quantizerCapacity_finite μ) hmass]
  apply (reservoirPowerValue_le_plan p μ _ R (simpleFuncReservoirPlan μ T)
    (simpleFuncReservoirPlan_first μ T) (simpleFuncReservoirPlan_second μ T)).trans
  unfold simpleFuncReservoirPlan
  have hpair : Measurable (fun x => (Space.point x, Space.point (T x))) :=
    continuous_point.measurable.prodMk (continuous_point.measurable.comp T.measurable)
  rw [lintegral_add_measure, lintegral_smul_measure]
  rw [lintegral_map (measurable_collapsedPowerCost p) hpair]
  simp [collapsedPowerCost, Real.zero_rpow (by linarith : p ≠ 0)]

/-- The same graph competitor also bounds the rooted distance. -/
theorem boundaryTransportDistance_simpleFuncDiagram_le
    (p : ℝ) (hp : 1 ≤ p) (μ : Measure Interior) [IsFiniteMeasure μ]
    (T : Interior →ₛ Interior) :
    boundaryTransportDistance p μ (atomicMeasure (simpleFuncDiagram μ T)) ≤
      (∫⁻ x, ENNReal.ofReal
        ((dist (Space.point x) (Space.point (T x))) ^ p) ∂μ) ^ (1 / p) := by
  unfold boundaryTransportDistance
  exact ENNReal.rpow_le_rpow
    (boundaryTransportPowerValue_simpleFuncDiagram_le p hp μ T)
    (one_div_nonneg.mpr (by linarith))

end TDA.Persistence.BoundaryTransport
