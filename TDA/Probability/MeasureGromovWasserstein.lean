import TDA.Probability.GromovWasserstein
import TDA.Probability.MeasureCoupling

/-!
# Distortion Gromov–Wasserstein costs for probability inputs

The convention is one half of the infimum of rooted distortion moments under
arbitrary probability couplings. The two copies of a sample pair are
independently drawn from the same coupling.
-/

noncomputable section

universe u v

namespace TDA.Probability

open MeasureTheory
open scoped ENNReal

variable {X : Type u} {Y : Type v} [MeasurableSpace X] [MeasurableSpace Y]
  [MetricSpace X] [MetricSpace Y]

/-- The metric distortion between two points of the coupling space. -/
def measureDistortion (a b : X × Y) : ℝ≥0∞ :=
  distortion a b

omit [MeasurableSpace X] [MeasurableSpace Y] in
@[simp] theorem measureDistortion_self (a : X × Y) : measureDistortion a a = 0 := by
  exact distortion_self a

omit [MeasurableSpace X] [MeasurableSpace Y] in
theorem measureDistortion_comm (a b : X × Y) :
    measureDistortion a b = measureDistortion b a := by
  exact distortion_comm a b

/-- The unrooted p-th distortion moment of a probability coupling, integrated
against two independent copies of its joint law. -/
def MeasureCoupling.distortionMoment {μ : ProbabilityMeasure X} {ν : ProbabilityMeasure Y}
    (π : MeasureCoupling μ ν) (p : ℝ) : ℝ≥0∞ :=
  ∫⁻ ab, measureDistortion ab.1 ab.2 ^ p ∂((π.joint : Measure (X × Y)).prod π.joint)

/-- Distortion Gromov–Wasserstein distance with the standard factor one half. -/
def measureGromovWasserstein (p : ℝ) (μ : ProbabilityMeasure X) (ν : ProbabilityMeasure Y) :
    ℝ≥0∞ :=
  (2 : ℝ≥0∞)⁻¹ * ⨅ π : MeasureCoupling μ ν, π.distortionMoment p ^ p⁻¹

/-- Essential-supremum distortion of two independent draws from a coupling. -/
def MeasureCoupling.distortionInfinity {μ : ProbabilityMeasure X} {ν : ProbabilityMeasure Y}
    (π : MeasureCoupling μ ν) : ℝ≥0∞ :=
  essSup (fun ab => measureDistortion ab.1 ab.2)
    ((π.joint : Measure (X × Y)).prod π.joint)

/-- Infinity distortion GW uses the essential supremum convention. -/
def measureGromovWassersteinInfinity (μ : ProbabilityMeasure X) (ν : ProbabilityMeasure Y) :
    ℝ≥0∞ :=
  (2 : ℝ≥0∞)⁻¹ * ⨅ π : MeasureCoupling μ ν, π.distortionInfinity

end TDA.Probability
