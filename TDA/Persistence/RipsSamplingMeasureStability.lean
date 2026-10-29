import TDA.Persistence.RipsSamplingMeasure
import TDA.Probability.MeasureGromovWasserstein
import TDA.Probability.MeasureSampling
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Wasserstein stability of compact sampled Rips diagram laws

The output Wasserstein distance is on probability measures over whole diagrams,
with the bottleneck metric as ground cost. Finite-p and essential-supremum bounds
couple iid tuples by sampling pairs from an arbitrary input coupling and then
take its infimum.
-/

noncomputable section

universe u v w

namespace TDA.Persistence.Rips

open MeasureTheory
open TDA.Probability
open ProbabilityTheory
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

/-- Finite-p stability of the actual compact-input iid Rips diagram laws in
every homological degree, including degree zero, for diameter-time
Vietoris–Rips filtrations and the standard half-distortion GW normalization.
At degree zero, the diagrams are the full ordinary H₀ diagrams. -/
theorem wasserstein_sampleLawMeasure_le_measureGromovWasserstein_allDegrees
    (k : Type w) [Field k] (μ : ProbabilityMeasure X) (ν : ProbabilityMeasure Y)
    {p : ℝ} (hp : 1 ≤ p) (n q : ℕ) (hn : 2 ≤ n) :
    measureWasserstein p bottleneck (sampleLawMeasure k μ n q)
      (sampleLawMeasure k ν n q) ≤
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
      measureWasserstein p bottleneck (sampleLawMeasure k μ n q)
        (sampleLawMeasure k ν n q) ≤
        (n.choose 2 : ℝ≥0∞) ^ p⁻¹ * (2 * measureGromovWasserstein p μ ν) := by
    rw [hGW, ENNReal.mul_iInf_of_ne hC0 hCtop]
    apply le_iInf
    intro π
    exact (ENNReal.rpow_le_rpow
        (measureTransportCost_sampleLawMeasure_le k π hp0 n q)
        (inv_nonneg.mpr hp0.le)).trans_eq
      (ENNReal.mul_rpow_of_nonneg _ _ (inv_nonneg.mpr hp0.le))
  calc
    _ ≤ (n.choose 2 : ℝ≥0∞) ^ p⁻¹ * (2 * measureGromovWasserstein p μ ν) := hbound
    _ = 2 * (n.choose 2 : ℝ≥0∞) ^ p⁻¹ * measureGromovWasserstein p μ ν := by ring

/-- Positive-degree specialization of
`wasserstein_sampleLawMeasure_le_measureGromovWasserstein_allDegrees`. -/
theorem wasserstein_sampleLawMeasure_le_measureGromovWasserstein
    (k : Type w) [Field k] (μ : ProbabilityMeasure X) (ν : ProbabilityMeasure Y)
    {p : ℝ} (hp : 1 ≤ p) (n degree : ℕ) (hn : 2 ≤ n) :
    measureWasserstein p bottleneck (sampleLawMeasure k μ n (degree + 1))
      (sampleLawMeasure k ν n (degree + 1)) ≤
        (2 : ℝ≥0∞) * (n.choose 2 : ℝ≥0∞) ^ p⁻¹ *
          measureGromovWasserstein p μ ν := by
  simpa using wasserstein_sampleLawMeasure_le_measureGromovWasserstein_allDegrees
    k μ ν hp n (degree + 1) hn

private theorem essSup_pairMaximum_iidMeasure_le {Z : Type*} [MeasurableSpace Z]
    (ρ : ProbabilityMeasure Z) (n : ℕ) (c : Z → Z → ℝ≥0∞)
    (hc : ∀ z, c z z = 0) :
    essSup (pairMaximum c) (iidMeasure ρ n : Measure (Fin n → Z)) ≤
      essSup (fun ab : Z × Z => c ab.1 ab.2) ((ρ : Measure Z).prod ρ) := by
  classical
  let ν : Fin n → Measure Z := fun _ => (ρ : Measure Z)
  let μn : Measure (Fin n → Z) := Measure.pi ν
  let B : ℝ≥0∞ := essSup (fun ab : Z × Z => c ab.1 ab.2)
    ((ρ : Measure Z).prod ρ)
  have hpair (i j : Fin n) :
      ∀ᵐ t ∂μn, c (t i) (t j) ≤ B := by
    by_cases hij : i = j
    · subst j
      filter_upwards with t
      rw [hc]
      exact bot_le
    · let proj : (Fin n → Z) → Z × Z := fun t => (t i, t j)
      have hproj : AEMeasurable proj μn := by fun_prop
      have hind : iIndepFun (fun (i : Fin n) (t : Fin n → Z) => t i)
          (Measure.pi ν) :=
        iIndepFun_pi (X := fun _ : Fin n => id) (fun _ => aemeasurable_id)
      have hmap0 := (hind.indepFun hij).map_prod_eq_prod_map_map
        (measurable_pi_apply i).aemeasurable (measurable_pi_apply j).aemeasurable
      have hi : Measure.map (fun t : Fin n → Z => t i) (Measure.pi ν) = ρ := by
        exact (measurePreserving_eval ν i).map_eq
      have hj : Measure.map (fun t : Fin n → Z => t j) (Measure.pi ν) = ρ := by
        exact (measurePreserving_eval ν j).map_eq
      have hmap : Measure.map proj μn = (ρ : Measure Z).prod ρ := by
        simpa [proj, μn, ν, hi, hj] using hmap0
      have hsup : essSup (fun t => c (t i) (t j)) μn ≤ B := by
        calc
          essSup (fun t => c (t i) (t j)) μn ≤
              essSup (fun ab : Z × Z => c ab.1 ab.2) (Measure.map proj μn) := by
            simpa [proj, Function.comp_def] using
              (essSup_comp_le_essSup_map_measure (f := proj)
                (g := fun ab : Z × Z => c ab.1 ab.2) hproj)
          _ = B := by rw [hmap]
      filter_upwards [ae_le_essSup (f := fun t => c (t i) (t j))] with t ht
      exact ht.trans hsup
  have hforall : ∀ᵐ t ∂μn, ∀ ij : Fin n × Fin n, c (t ij.1) (t ij.2) ≤ B := by
    rw [ae_all_iff]
    intro ij
    exact hpair ij.1 ij.2
  have hmax : ∀ᵐ t ∂μn, pairMaximum c t ≤ B := by
    filter_upwards [hforall] with t ht
    exact Finset.sup_le fun ij _ => ht ij
  have hmain : essSup (pairMaximum c) μn ≤ B := essSup_le_of_ae_le B hmax
  have hμn : (iidMeasure ρ n : Measure (Fin n → Z)) = μn := by
    simp only [iidMeasure, ProbabilityMeasure.toMeasure_pi]
    rfl
  rw [hμn]
  exact hmain

private theorem sampleLawMeasureCoupling_essSup_le_distortionInfinity
    (k : Type w) [Field k] (μ : ProbabilityMeasure X) (ν : ProbabilityMeasure Y)
    (π : MeasureCoupling μ ν) (n q : ℕ) :
    essSup (fun de : Diagram ℝ × Diagram ℝ => bottleneck de.1 de.2)
      ((sampleLawMeasureCoupling k π n q).joint : Measure
        (Diagram ℝ × Diagram ℝ)) ≤
        π.distortionInfinity := by
  let f : (Fin n → X) → Diagram ℝ := fun t => sampleDiagram k t q
  let g : (Fin n → Y) → Diagram ℝ := fun t => sampleDiagram k t q
  let pairTuple : (Fin n → X × Y) → (Fin n → X) × (Fin n → Y) :=
    fun t => (fun i => (t i).1, fun i => (t i).2)
  have hf : Measurable f := (continuous_sampleDiagram k q).measurable
  have hg : Measurable g := (continuous_sampleDiagram k q).measurable
  have hpairTuple : Measurable pairTuple := by
    apply Measurable.prodMk
    · apply measurable_pi_lambda
      intro i
      exact measurable_fst.comp (measurable_pi_apply i)
    · apply measurable_pi_lambda
      intro i
      exact measurable_snd.comp (measurable_pi_apply i)
  have hpairMap : Measurable (Prod.map f g) := hf.prodMap hg
  have htupleCost : Measurable
      (fun ts : (Fin n → X) × (Fin n → Y) => bottleneck (f ts.1) (g ts.2)) :=
    measurable_bottleneck.comp (f := Prod.map f g) hpairMap
  have htupleCostSet : MeasurableSet
      {ts : (Fin n → X) × (Fin n → Y) |
        bottleneck (f ts.1) (g ts.2) ≤ π.distortionInfinity} :=
    measurableSet_le htupleCost measurable_const
  have hpairMax := essSup_pairMaximum_iidMeasure_le π.joint n distortion distortion_self
  have hsource : ∀ᵐ t ∂(iidMeasure π.joint n : Measure (Fin n → X × Y)),
      bottleneck (sampleDiagram k (fun i => (t i).1) q)
        (sampleDiagram k (fun i => (t i).2) q) ≤ π.distortionInfinity := by
    filter_upwards [ae_le_essSup (f := pairMaximum distortion)] with t ht
    exact (bottleneck_sampleDiagram_le_pairMaximum k t q).trans
      (ht.trans hpairMax)
  have htuple : ∀ᵐ ts ∂((π.tuples n).joint : Measure
      ((Fin n → X) × (Fin n → Y))),
      bottleneck (f ts.1) (g ts.2) ≤ π.distortionInfinity := by
    rw [MeasureCoupling.tuples, ProbabilityMeasure.toMeasure_map]
    rw [ae_map_iff (by
      change AEMeasurable pairTuple _
      exact hpairTuple.aemeasurable) htupleCostSet]
    change ∀ᵐ t ∂(ProbabilityMeasure.pi (fun _ : Fin n => π.joint) : Measure
      (Fin n → X × Y)),
      bottleneck (f (pairTuple t).1) (g (pairTuple t).2) ≤ π.distortionInfinity
    simpa [f, g, pairTuple, iidMeasure, ProbabilityMeasure.toMeasure_pi] using hsource
  have hdiagram : ∀ᵐ de ∂((sampleLawMeasureCoupling k π n q).joint :
      Measure (Diagram ℝ × Diagram ℝ)),
      bottleneck de.1 de.2 ≤ π.distortionInfinity := by
    have hsampleLaw : sampleLawMeasureCoupling k π n q =
        MeasureCoupling.map (π.tuples n) f g hf hg := by
      rfl
    rw [hsampleLaw]
    have hdiagramSet : MeasurableSet
        {de : Diagram ℝ × Diagram ℝ | bottleneck de.1 de.2 ≤ π.distortionInfinity} :=
      measurableSet_le measurable_bottleneck measurable_const
    rw [MeasureCoupling.map, ProbabilityMeasure.toMeasure_map]
    rw [ae_map_iff hpairMap.aemeasurable hdiagramSet]
    simpa only [Prod.map_fst, Prod.map_snd] using htuple
  exact essSup_le_of_ae_le _ hdiagram

private theorem measureWassersteinInfinity_sampleLawMeasure_le_coupling
    (k : Type w) [Field k] (μ : ProbabilityMeasure X) (ν : ProbabilityMeasure Y)
    (π : MeasureCoupling μ ν) (n q : ℕ) :
    measureWassersteinInfinity bottleneck (sampleLawMeasure k μ n q)
      (sampleLawMeasure k ν n q) ≤ π.distortionInfinity := by
  change (⨅ γ : MeasureCoupling (sampleLawMeasure k μ n q)
      (sampleLawMeasure k ν n q),
      essSup (fun de : Diagram ℝ × Diagram ℝ => bottleneck de.1 de.2)
        (γ.joint : Measure (Diagram ℝ × Diagram ℝ))) ≤ π.distortionInfinity
  exact (iInf_le _ (sampleLawMeasureCoupling k π n q)).trans
    (sampleLawMeasureCoupling_essSup_le_distortionInfinity k μ ν π n q)

/-- Infinity stability of the actual compact-input iid Rips diagram laws in
every homological degree, including degree zero, for diameter-time
Vietoris–Rips filtrations and the standard half-distortion GW normalization.
At degree zero, the diagrams are the full ordinary H₀ diagrams. The proof
pushes any input probability coupling through the iid sample maps, bounds its
essential-supremum cost by the input distortion, and then takes the infimum;
no optimal coupling is assumed. -/
theorem wassersteinInfinity_sampleLawMeasure_le_measureGromovWassersteinInfinity_allDegrees
    (k : Type w) [Field k] (μ : ProbabilityMeasure X) (ν : ProbabilityMeasure Y)
    (n q : ℕ) :
    measureWassersteinInfinity bottleneck (sampleLawMeasure k μ n q)
      (sampleLawMeasure k ν n q) ≤
        (2 : ℝ≥0∞) * measureGromovWassersteinInfinity μ ν := by
  have hGW : (2 : ℝ≥0∞) * measureGromovWassersteinInfinity μ ν =
      ⨅ π : MeasureCoupling μ ν, π.distortionInfinity := by
    simp only [measureGromovWassersteinInfinity, ← mul_assoc]
    rw [ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
  rw [hGW]
  apply le_iInf
  intro π
  exact measureWassersteinInfinity_sampleLawMeasure_le_coupling k μ ν π n q

/-- Positive-degree specialization of
`wassersteinInfinity_sampleLawMeasure_le_measureGromovWassersteinInfinity_allDegrees`. -/
theorem wassersteinInfinity_sampleLawMeasure_le_measureGromovWassersteinInfinity
    (k : Type w) [Field k] (μ : ProbabilityMeasure X) (ν : ProbabilityMeasure Y)
    (n degree : ℕ) :
    measureWassersteinInfinity bottleneck (sampleLawMeasure k μ n (degree + 1))
      (sampleLawMeasure k ν n (degree + 1)) ≤
        (2 : ℝ≥0∞) * measureGromovWassersteinInfinity μ ν := by
  simpa using wassersteinInfinity_sampleLawMeasure_le_measureGromovWassersteinInfinity_allDegrees
    k μ ν n (degree + 1)

end TDA.Persistence.Rips
