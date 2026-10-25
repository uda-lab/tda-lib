import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Couplings and transport costs for probability measures

A coupling is a probability measure with the prescribed two marginals. Costs
are integrated against the whole joint law, so the outer mass is always one.
-/

noncomputable section

universe u v w z

namespace TDA.Probability

open MeasureTheory
open scoped ENNReal

variable {X : Type u} {Y : Type v} {Z : Type w} {W : Type z}
variable [MeasurableSpace X] [MeasurableSpace Y]

/-- A probability coupling with exact first and second marginals. -/
structure MeasureCoupling (μ : ProbabilityMeasure X) (ν : ProbabilityMeasure Y) where
  joint : ProbabilityMeasure (X × Y)
  fst_map : joint.map measurable_fst.aemeasurable = μ
  snd_map : joint.map measurable_snd.aemeasurable = ν

namespace MeasureCoupling

variable {μ : ProbabilityMeasure X} {ν : ProbabilityMeasure Y}

/-- Independent probability measures give a feasible coupling. -/
def independent (μ : ProbabilityMeasure X) (ν : ProbabilityMeasure Y) :
    MeasureCoupling μ ν where
  joint := μ.prod ν
  fst_map := ProbabilityMeasure.map_fst_prod μ ν
  snd_map := ProbabilityMeasure.map_snd_prod μ ν

instance : Nonempty (MeasureCoupling μ ν) := ⟨independent μ ν⟩

/-- Push forward a coupling by measurable maps on both coordinates. -/
def map (π : MeasureCoupling μ ν) (f : X → Z) (g : Y → W)
    [MeasurableSpace Z] [MeasurableSpace W] (hf : Measurable f) (hg : Measurable g) :
    MeasureCoupling (μ.map hf.aemeasurable) (ν.map hg.aemeasurable) where
  joint := π.joint.map (hf.prodMap hg).aemeasurable
  fst_map := by
    apply ProbabilityMeasure.toMeasure_injective
    simp only [ProbabilityMeasure.toMeasure_map]
    rw [Measure.map_map measurable_fst (hf.prodMap hg)]
    change Measure.map (f ∘ Prod.fst) (π.joint : Measure (X × Y)) = _
    rw [← Measure.map_map hf measurable_fst]
    have hfst : Measure.map Prod.fst (π.joint : Measure (X × Y)) = μ := by
      simpa using congrArg ProbabilityMeasure.toMeasure π.fst_map
    rw [hfst]
  snd_map := by
    apply ProbabilityMeasure.toMeasure_injective
    simp only [ProbabilityMeasure.toMeasure_map]
    rw [Measure.map_map measurable_snd (hf.prodMap hg)]
    change Measure.map (g ∘ Prod.snd) (π.joint : Measure (X × Y)) = _
    rw [← Measure.map_map hg measurable_snd]
    have hsnd : Measure.map Prod.snd (π.joint : Measure (X × Y)) = ν := by
      simpa using congrArg ProbabilityMeasure.toMeasure π.snd_map
    rw [hsnd]

/-- Integral cost of a probability coupling. -/
def cost (π : MeasureCoupling μ ν) (c : X → Y → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ xy, c xy.1 xy.2 ∂(π.joint : Measure (X × Y))

@[simp] theorem cost_map (π : MeasureCoupling μ ν) (f : X → Z) (g : Y → W)
    [MeasurableSpace Z] [MeasurableSpace W] (hf : Measurable f) (hg : Measurable g)
    (c : Z → W → ℝ≥0∞) (hc : Measurable (fun xy : Z × W => c xy.1 xy.2)) :
    (π.map f g hf hg).cost c = π.cost (fun x y => c (f x) (g y)) := by
  change ∫⁻ xy : Z × W, c xy.1 xy.2 ∂Measure.map (Prod.map f g)
      (π.joint : Measure (X × Y)) = _
  rw [lintegral_map hc (hf.prodMap hg)]
  rfl

end MeasureCoupling

/-- Optimal transport cost between two probability measures for a supplied
extended nonnegative ground cost. -/
def measureTransportCost (c : X → Y → ℝ≥0∞) (μ : ProbabilityMeasure X)
    (ν : ProbabilityMeasure Y) : ℝ≥0∞ := ⨅ π : MeasureCoupling μ ν, π.cost c

theorem measureTransportCost_le_coupling (c : X → Y → ℝ≥0∞)
    (μ : ProbabilityMeasure X) (ν : ProbabilityMeasure Y) (π : MeasureCoupling μ ν) :
    measureTransportCost c μ ν ≤ π.cost c := iInf_le _ π

/-- The rooted finite-p transport cost between probability laws. -/
def measureWasserstein (p : ℝ) (c : X → Y → ℝ≥0∞) (μ : ProbabilityMeasure X)
    (ν : ProbabilityMeasure Y) : ℝ≥0∞ :=
  measureTransportCost (fun x y => c x y ^ p) μ ν ^ p⁻¹

/-- Rooting after the infimum is the infimum of rooted coupling costs. -/
theorem measureWasserstein_eq_iInf {p : ℝ} (hp : 0 < p) (c : X → Y → ℝ≥0∞)
    (μ : ProbabilityMeasure X) (ν : ProbabilityMeasure Y) :
    measureWasserstein p c μ ν =
      ⨅ π : MeasureCoupling μ ν, π.cost (fun x y => c x y ^ p) ^ p⁻¹ := by
  exact (ENNReal.orderIsoRpow p⁻¹ (inv_pos.mpr hp)).map_iInf _

/-- Essential-supremum transport on probability couplings ignores only
zero-measure sets of pairs. -/
def measureWassersteinInfinity (c : X → Y → ℝ≥0∞) (μ : ProbabilityMeasure X)
    (ν : ProbabilityMeasure Y) : ℝ≥0∞ :=
  ⨅ π : MeasureCoupling μ ν, essSup (fun xy => c xy.1 xy.2) (π.joint : Measure (X × Y))

end TDA.Probability
