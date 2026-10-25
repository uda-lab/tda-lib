import TDA.Persistence.RipsSamplingMeasure
import TDA.Probability.MeasureGromovWasserstein
import TDA.Probability.MeasureSampling
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Finite-p stability of compact sampled Rips diagram laws

The output Wasserstein distance is on probability measures over whole diagrams,
with the bottleneck metric as ground cost. The proof couples iid tuples by
sampling pairs from an arbitrary input coupling and then takes its infimum.
-/

noncomputable section

universe u v w

namespace TDA.Persistence.Rips

open MeasureTheory
open TDA.Probability
open scoped ENNReal

variable {X : Type u} {Y : Type v}
  [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSpace Y]
  [BorelSpace X] [BorelSpace Y]
  [CompactSpace X] [CompactSpace Y]

/-- Push an input probability coupling through the two actual iid Rips sample
maps to obtain a coupling of their diagram laws. -/
def sampleLawMeasureCoupling (k : Type w) [Field k]
    {μ : ProbabilityMeasure X} {ν : ProbabilityMeasure Y}
    (π : MeasureCoupling μ ν) (n degree : ℕ) :
    MeasureCoupling (sampleLawMeasure k μ n degree) (sampleLawMeasure k ν n degree) := by
  change MeasureCoupling
    ((iidMeasure μ n).map ((continuous_sampleDiagram (X := X) k degree).measurable.aemeasurable))
    ((iidMeasure ν n).map ((continuous_sampleDiagram (X := Y) k degree).measurable.aemeasurable))
  exact π.sampleLaw n (fun t => sampleDiagram k t degree) (fun s => sampleDiagram k s degree)
    (continuous_sampleDiagram k degree).measurable
    (continuous_sampleDiagram k degree).measurable

/-- The finite-p bottleneck cost between two sampled diagrams. -/
def sampleDiagramBottleneckCost (k : Type w) [Field k] (n degree : ℕ) (p : ℝ)
    (t : Fin n → X) (s : Fin n → Y) : ℝ≥0∞ :=
  bottleneck (sampleDiagram k t degree) (sampleDiagram k s degree) ^ p

/-- The pair cost of the iid tuple coupling is the expected pairwise diagram
cost under independent draws from the input coupling. -/
theorem sampleDiagramPairCost_eq_integral (k : Type w) [Field k]
    {μ : ProbabilityMeasure X} {ν : ProbabilityMeasure Y}
    (π : MeasureCoupling μ ν) (p : ℝ) (n degree : ℕ) :
    (π.tuples n).cost (sampleDiagramBottleneckCost k n degree p) =
      ∫⁻ t, bottleneck (sampleDiagram k (fun i => (t i).1) degree)
        (sampleDiagram k (fun i => (t i).2) degree) ^ p
        ∂(ProbabilityMeasure.pi (fun _ : Fin n => π.joint) : Measure (Fin n → X × Y)) := by
  let f : (Fin n → X) → Diagram ℝ := fun t => sampleDiagram k t degree
  let g : (Fin n → Y) → Diagram ℝ := fun t => sampleDiagram k t degree
  have hf : Measurable f := (continuous_sampleDiagram k degree).measurable
  have hg : Measurable g := (continuous_sampleDiagram k degree).measurable
  have hground : Measurable (fun de : Diagram ℝ × Diagram ℝ => bottleneck de.1 de.2 ^ p) := by
    exact ENNReal.continuous_rpow_const.measurable.comp measurable_bottleneck
  have htupleCost : Measurable
      (fun ts : (Fin n → X) × (Fin n → Y) => bottleneck (f ts.1) (g ts.2) ^ p) :=
    hground.comp (f := Prod.map f g) (hf.prodMap hg)
  exact MeasureCoupling.cost_tuples π n (sampleDiagramBottleneckCost k n degree p)
    htupleCost

/-- The pair cost is pointwise controlled by the maximum input distortion. -/
theorem sampleDiagramPairCost_le_pairMaximum (k : Type w) [Field k]
    {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    {n : ℕ} (p : ℝ) (hp : 0 < p) (degree : ℕ) :
    ∀ t : Fin n → X × Y,
      bottleneck (sampleDiagram k (fun i => (t i).1) degree)
        (sampleDiagram k (fun i => (t i).2) degree) ^ p ≤ pairMaximum distortion t ^ p := by
  intro t
  exact ENNReal.rpow_le_rpow (bottleneck_sampleDiagram_le_pairMaximum k t degree) hp.le

/-- The bottleneck pair cost of the coupled Rips sample diagrams is bounded by
the iid pair distortion energy. -/
theorem sampleDiagramPairCost_le (k : Type w) [Field k]
    {μ : ProbabilityMeasure X} {ν : ProbabilityMeasure Y}
    (π : MeasureCoupling μ ν) {p : ℝ} (hp : 0 < p) (n degree : ℕ) :
    (π.tuples n).cost (sampleDiagramBottleneckCost k n degree p) ≤
      (n.choose 2 : ℝ≥0∞) * π.distortionMoment p := by
  rw [sampleDiagramPairCost_eq_integral]
  calc
    _ ≤ ∫⁻ t, pairMaximum distortion t ^ p
          ∂(ProbabilityMeasure.pi (fun _ : Fin n => π.joint) : Measure (Fin n → X × Y)) := by
      apply lintegral_mono
      exact sampleDiagramPairCost_le_pairMaximum k p hp degree
    _ ≤ (n.choose 2 : ℝ≥0∞) * π.distortionMoment p := by
      have hdist : Measurable
          (fun ab : (X × Y) × (X × Y) => distortion ab.1 ab.2) := by
        apply Continuous.measurable
        unfold distortion
        exact ENNReal.continuous_ofReal.comp
          (((continuous_fst.fst.dist continuous_snd.fst).sub
            (continuous_fst.snd.dist continuous_snd.snd)).abs)
      have hmoment := lintegral_iid_pairMaximum_rpow_le
        (μ := π.joint) n distortion distortion_self distortion_comm hp
        hdist
      simpa [iidMeasure, ProbabilityMeasure.toMeasure_pi, MeasureCoupling.distortionMoment,
        measureDistortion] using hmoment

/-- Every input coupling gives the sharp finite-p moment bound for the entire
diagram laws. -/
theorem measureTransportCost_sampleLawMeasure_le (k : Type w) [Field k]
    {μ : ProbabilityMeasure X} {ν : ProbabilityMeasure Y}
    (π : MeasureCoupling μ ν) {p : ℝ} (hp : 0 < p) (n degree : ℕ) :
    measureTransportCost (fun D E => bottleneck D E ^ p)
      (sampleLawMeasure k μ n degree) (sampleLawMeasure k ν n degree) ≤
        (n.choose 2 : ℝ≥0∞) * π.distortionMoment p := by
  have hground : Measurable
      (fun de : Diagram ℝ × Diagram ℝ => bottleneck de.1 de.2 ^ p) := by
    exact ENNReal.continuous_rpow_const.measurable.comp measurable_bottleneck
  calc
    _ ≤ (π.sampleLaw n (fun t => sampleDiagram k t degree)
        (fun t => sampleDiagram k t degree)
        (continuous_sampleDiagram k degree).measurable
        (continuous_sampleDiagram k degree).measurable).cost
          (fun D E => bottleneck D E ^ p) :=
      measureTransportCost_le_coupling _ _ _ _
    _ = (π.tuples n).cost (sampleDiagramBottleneckCost k n degree p) :=
      MeasureCoupling.cost_map _ _ _ _ _ _ hground
    _ ≤ (n.choose 2 : ℝ≥0∞) * π.distortionMoment p :=
      sampleDiagramPairCost_le k π hp n degree

/-- Finite-p stability of the actual compact-input iid Rips diagram laws for
diameter-time Vietoris–Rips filtrations and the standard half-distortion GW
normalization. -/
theorem wasserstein_sampleLawMeasure_le_measureGromovWasserstein
    (k : Type w) [Field k] (μ : ProbabilityMeasure X) (ν : ProbabilityMeasure Y)
    {p : ℝ} (hp : 1 ≤ p) (n degree : ℕ) (hn : 2 ≤ n) :
    measureWasserstein p bottleneck (sampleLawMeasure k μ n (degree + 1))
      (sampleLawMeasure k ν n (degree + 1)) ≤
        (2 : ℝ≥0∞) * (n.choose 2 : ℝ≥0∞) ^ p⁻¹ *
          measureGromovWasserstein p μ ν := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hC0 : (n.choose 2 : ℝ≥0∞) ^ p⁻¹ ≠ 0 := by
    apply ne_of_gt
    apply ENNReal.rpow_pos
    · exact_mod_cast Nat.choose_pos hn
    · exact ENNReal.natCast_ne_top _
  have hCtop : (n.choose 2 : ℝ≥0∞) ^ p⁻¹ ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (inv_nonneg.mpr hp0.le) (ENNReal.natCast_ne_top _)
  have hGW : 2 * measureGromovWasserstein p μ ν =
      ⨅ π : MeasureCoupling μ ν, π.distortionMoment p ^ p⁻¹ := by
    simp only [measureGromovWasserstein, ← mul_assoc]
    rw [ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
  have hbound :
      measureWasserstein p bottleneck (sampleLawMeasure k μ n (degree + 1))
        (sampleLawMeasure k ν n (degree + 1)) ≤
        (n.choose 2 : ℝ≥0∞) ^ p⁻¹ * (2 * measureGromovWasserstein p μ ν) := by
    rw [hGW, ENNReal.mul_iInf_of_ne hC0 hCtop]
    apply le_iInf
    intro π
    exact (ENNReal.rpow_le_rpow
        (measureTransportCost_sampleLawMeasure_le k π hp0 n (degree + 1))
        (inv_nonneg.mpr hp0.le)).trans_eq
      (ENNReal.mul_rpow_of_nonneg _ _ (inv_nonneg.mpr hp0.le))
  calc
    _ ≤ (n.choose 2 : ℝ≥0∞) ^ p⁻¹ * (2 * measureGromovWasserstein p μ ν) := hbound
    _ = 2 * (n.choose 2 : ℝ≥0∞) ^ p⁻¹ * measureGromovWasserstein p μ ν := by ring

end TDA.Persistence.Rips
