import TDA.Persistence.BoundaryTransportGeometry
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

/-!
# Reservoir measures at the collapsed boundary

An interior measure is augmented by a boundary atom to reach a chosen finite
capacity. Its interior restriction is preserved, and its distance-to-boundary
moment is exactly the input diagonal persistence moment, including infinite
values. Normalization gives a probability measure. Paired capacities explicitly
dominate the sum of the two original masses.
-/

noncomputable section

set_option autoImplicit false

open Set MeasureTheory
open scoped ENNReal

namespace TDA.Persistence.BoundaryTransport

/-- The p-th power of distance to the collapsed boundary, as an extended nonnegative
integrand. -/
def boundaryMomentIntegrand (p : ℝ) (x : Space) : ℝ≥0∞ :=
  ENNReal.ofReal (dist x Space.boundary ^ p)

/-- Add exactly enough mass at the collapsed boundary to reach reservoir capacity `R`. -/
def reservoirMeasure (μ : Measure Interior) (R : ℝ≥0∞) : Measure Space :=
  μ.map Space.point + (R - μ Set.univ) • Measure.dirac Space.boundary

theorem reservoirMeasure_apply_interior (μ : Measure Interior) (R : ℝ≥0∞)
    {s : Set Space} (hs : MeasurableSet s) (hb : Space.boundary ∉ s) :
    reservoirMeasure μ R s = μ (Space.point ⁻¹' s) := by
  rw [reservoirMeasure, Measure.add_apply, Measure.map_apply continuous_point.measurable hs,
    Measure.smul_apply]
  simp [Measure.dirac_apply, hb]

theorem reservoirMeasure_mass (μ : Measure Interior) (R : ℝ≥0∞)
    (hmass : μ Set.univ ≤ R) :
    reservoirMeasure μ R Set.univ = R := by
  rw [reservoirMeasure, Measure.add_apply, Measure.map_apply continuous_point.measurable
    MeasurableSet.univ, Measure.smul_apply, smul_eq_mul]
  simp only [preimage_univ, Measure.dirac_apply' Space.boundary MeasurableSet.univ]
  simp only [Set.indicator_univ, Pi.one_apply, mul_one]
  simpa only [add_comm] using (add_tsub_cancel_of_le hmass)

/-- A common reservoir capacity for a pair dominates each original mass, while retaining the
sum-capacity condition explicitly. -/
theorem reservoirMeasure_pair_mass (μ ν : Measure Interior) (R : ℝ≥0∞)
    (hmass : μ Set.univ + ν Set.univ ≤ R) :
    reservoirMeasure μ R Set.univ = R ∧ reservoirMeasure ν R Set.univ = R := by
  have hμ : μ Set.univ ≤ R :=
    (show μ Set.univ ≤ μ Set.univ + ν Set.univ from le_self_add).trans hmass
  have hν : ν Set.univ ≤ R :=
    (show ν Set.univ ≤ ν Set.univ + μ Set.univ from le_self_add).trans
      (by simpa [add_comm] using hmass)
  exact ⟨reservoirMeasure_mass μ R hμ, reservoirMeasure_mass ν R hν⟩

theorem reservoirMeasure_isFinite (μ : Measure Interior) (R : ℝ≥0∞)
    (hR : R < ∞) (hmass : μ Set.univ ≤ R) :
    IsFiniteMeasure (reservoirMeasure μ R) := by
  refine ⟨?_⟩
  rw [reservoirMeasure_mass μ R hmass]
  exact hR

/-- Finite reservoir measures are regular Borel measures on the collapsed Polish space. -/
theorem reservoirMeasure_regular (μ : Measure Interior) (R : ℝ≥0∞)
    (hR : R < ∞) (hmass : μ Set.univ ≤ R) :
    (reservoirMeasure μ R).Regular := by
  let := reservoirMeasure_isFinite μ R hR hmass
  infer_instance

theorem reservoirMeasure_isFinite_iff (μ : Measure Interior) (R : ℝ≥0∞)
    (hmass : μ Set.univ ≤ R) :
    IsFiniteMeasure (reservoirMeasure μ R) ↔ R < ∞ := by
  constructor
  · intro hμR
    simpa only [reservoirMeasure_mass μ R hmass] using hμR.measure_univ_lt_top
  · exact fun hR => reservoirMeasure_isFinite μ R hR hmass

theorem reservoirMeasure_restrict_interior (μ : Measure Interior) (R : ℝ≥0∞) :
    (reservoirMeasure μ R).restrict (Set.range Space.point) = μ.map Space.point := by
  apply Measure.ext
  intro s hs
  rw [Measure.restrict_apply hs]
  have hb : Space.boundary ∉ s ∩ Set.range Space.point := by
    rintro ⟨_, x, hx⟩
    cases hx
  rw [reservoirMeasure_apply_interior μ R
    (hs.inter measurableEmbedding_point.measurableSet_range) hb,
    Measure.map_apply continuous_point.measurable hs]
  simp [preimage_inter, preimage_range]

theorem reservoirMeasure_boundary_moment (μ : Measure Interior) (R : ℝ≥0∞)
    (p : ℝ) (hp : 0 < p) :
    ∫⁻ x, boundaryMomentIntegrand p x ∂reservoirMeasure μ R =
      ∫⁻ x, ENNReal.ofReal (depth x ^ p) ∂μ := by
  have hp0 : 0 ≤ p := hp.le
  have hdist : Continuous (fun x : Space => dist x Space.boundary) := by
    exact continuous_dist.comp (continuous_id.prodMk continuous_const)
  have hf : Measurable (boundaryMomentIntegrand p) :=
    ENNReal.measurable_ofReal.comp ((Real.continuous_rpow_const hp0).comp hdist).measurable
  rw [reservoirMeasure, lintegral_add_measure, lintegral_smul_measure,
    lintegral_map hf continuous_point.measurable]
  simp [boundaryMomentIntegrand, dist_point_boundary,
    Real.zero_rpow hp.ne']

@[simp] theorem reservoirMeasure_zero (R : ℝ≥0∞) :
    reservoirMeasure (0 : Measure Interior) R = R • Measure.dirac Space.boundary := by
  simp [reservoirMeasure]

theorem reservoirMeasure_zero_boundary_moment (R : ℝ≥0∞) (p : ℝ) (hp : 0 < p) :
    ∫⁻ x, boundaryMomentIntegrand p x ∂reservoirMeasure (0 : Measure Interior) R = 0 := by
  rw [reservoirMeasure_boundary_moment (0 : Measure Interior) R p hp]
  simp

/-- Normalize a finite positive reservoir into a probability measure. -/
def normalizedReservoirMeasure (μ : Measure Interior) (R : ℝ≥0∞) : Measure Space :=
  R⁻¹ • reservoirMeasure μ R

theorem normalizedReservoirMeasure_zero (R : ℝ≥0∞) (hRtop : R < ∞) (hRpos : 0 < R) :
    normalizedReservoirMeasure (0 : Measure Interior) R = Measure.dirac Space.boundary := by
  rw [normalizedReservoirMeasure, reservoirMeasure_zero, smul_smul,
    ENNReal.inv_mul_cancel hRpos.ne' hRtop.ne, one_smul]

theorem normalizedReservoirMeasure_mass (μ : Measure Interior) (R : ℝ≥0∞)
    (hRtop : R < ∞) (hRpos : 0 < R)
    (hmass : μ Set.univ ≤ R) :
    normalizedReservoirMeasure μ R Set.univ = 1 := by
  rw [normalizedReservoirMeasure, Measure.smul_apply, smul_eq_mul,
    reservoirMeasure_mass μ R hmass]
  exact ENNReal.inv_mul_cancel hRpos.ne' hRtop.ne

theorem normalizedReservoirMeasure_isProbability (μ : Measure Interior) (R : ℝ≥0∞)
    (hRtop : R < ∞) (hRpos : 0 < R)
    (hmass : μ Set.univ ≤ R) :
    IsProbabilityMeasure (normalizedReservoirMeasure μ R) :=
  ⟨normalizedReservoirMeasure_mass μ R hRtop hRpos hmass⟩

theorem normalizedReservoirPair_isProbability (μ ν : Measure Interior) (R : ℝ≥0∞)
    (hRtop : R < ∞) (hRpos : 0 < R)
    (htotal : μ Set.univ + ν Set.univ ≤ R) :
    IsProbabilityMeasure (normalizedReservoirMeasure μ R) ∧
      IsProbabilityMeasure (normalizedReservoirMeasure ν R) := by
  have hμ : μ Set.univ ≤ R :=
    (show μ Set.univ ≤ μ Set.univ + ν Set.univ from le_self_add).trans htotal
  have hν : ν Set.univ ≤ R :=
    (show ν Set.univ ≤ ν Set.univ + μ Set.univ from le_self_add).trans
      (by simpa [add_comm] using htotal)
  exact ⟨normalizedReservoirMeasure_isProbability μ R hRtop hRpos hμ,
    normalizedReservoirMeasure_isProbability ν R hRtop hRpos hν⟩

theorem normalizedReservoirMeasure_restrict_interior (μ : Measure Interior)
    (R : ℝ≥0∞) :
    (normalizedReservoirMeasure μ R).restrict (Set.range Space.point) =
      R⁻¹ • μ.map Space.point := by
  rw [normalizedReservoirMeasure, Measure.restrict_smul,
    reservoirMeasure_restrict_interior]

theorem normalizedReservoirMeasure_boundary_moment (μ : Measure Interior)
    (R : ℝ≥0∞) (p : ℝ) (hp : 0 < p) :
    ∫⁻ x, boundaryMomentIntegrand p x ∂normalizedReservoirMeasure μ R =
      R⁻¹ * ∫⁻ x, ENNReal.ofReal (depth x ^ p) ∂μ := by
  rw [normalizedReservoirMeasure, lintegral_smul_measure,
    reservoirMeasure_boundary_moment μ R p hp,
    smul_eq_mul]

def normalizedReservoirProbability (μ : Measure Interior) (R : ℝ≥0∞)
    (hRtop : R < ∞) (hRpos : 0 < R) (hmass : μ Set.univ ≤ R) : ProbabilityMeasure Space :=
  ⟨normalizedReservoirMeasure μ R,
    normalizedReservoirMeasure_isProbability μ R hRtop hRpos hmass⟩

@[simp] theorem coe_normalizedReservoirProbability (μ : Measure Interior) (R : ℝ≥0∞)
    (hRtop : R < ∞) (hRpos : 0 < R) (hmass : μ Set.univ ≤ R) :
    (normalizedReservoirProbability μ R hRtop hRpos hmass : Measure Space) =
      normalizedReservoirMeasure μ R := rfl

theorem reservoirMeasure_dirac_mass (x : Interior) (R : ℝ≥0∞) (hR : 1 ≤ R) :
    reservoirMeasure (Measure.dirac x) R Set.univ = R := by
  apply reservoirMeasure_mass
  simpa using hR

theorem reservoirMeasure_dirac_boundary_moment (x : Interior) (R : ℝ≥0∞) (p : ℝ) (hp : 1 ≤ p) :
    ∫⁻ y, boundaryMomentIntegrand p y ∂reservoirMeasure (Measure.dirac x) R =
      ENNReal.ofReal (depth x ^ p) := by
  rw [reservoirMeasure_boundary_moment (μ := Measure.dirac x) (R := R) p (by linarith)]
  simp

end TDA.Persistence.BoundaryTransport
