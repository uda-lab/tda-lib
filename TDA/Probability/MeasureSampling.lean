import TDA.Probability.SamplingMoments
import TDA.Probability.MeasureCoupling
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.FiniteMeasurePi
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Data.Finset.Prod

/-!
# Independent sampling and pairwise moment estimates for probability measures

Sampling uses the finite product probability law and permits repeated values.
The maximum over the sample distance matrix is bounded using the unordered
pair-energy, so only distinct draw indices contribute to the finite-p moment.
-/

noncomputable section

universe u v w z

namespace TDA.Probability

open MeasureTheory
open ProbabilityTheory
open scoped ENNReal

variable {X : Type u} {Y : Type v} {Z : Type w} {W : Type z}
variable [MeasurableSpace X] [MeasurableSpace Y]
variable {n : ℕ}

/-- The law of an ordered iid tuple drawn with replacement. -/
def iidMeasure (μ : ProbabilityMeasure X) (n : ℕ) : ProbabilityMeasure (Fin n → X) :=
  ProbabilityMeasure.pi (fun _ : Fin n => μ)

private def tuplePairMap (t : Fin n → X × Y) : (Fin n → X) × (Fin n → Y) :=
  (fun i => (t i).1, fun i => (t i).2)

private theorem measurable_tuplePairMap : Measurable (tuplePairMap (X := X) (Y := Y) (n := n)) := by
  apply Measurable.prodMk
  · apply measurable_pi_lambda
    intro i
    exact measurable_fst.comp (measurable_pi_apply i)
  · apply measurable_pi_lambda
    intro i
    exact measurable_snd.comp (measurable_pi_apply i)

namespace MeasureCoupling

variable {μ : ProbabilityMeasure X} {ν : ProbabilityMeasure Y}

/-- Iid tuple coupling obtained by sampling independent pairs from one input
coupling and then projecting the tuple coordinates. -/
def tuples (π : MeasureCoupling μ ν) (n : ℕ) :
    MeasureCoupling (iidMeasure μ n) (iidMeasure ν n) where
  joint :=
    (ProbabilityMeasure.pi (fun _ : Fin n => π.joint)).map
      (measurable_tuplePairMap (X := X) (Y := Y) (n := n)).aemeasurable
  fst_map := by
    apply ProbabilityMeasure.toMeasure_injective
    change Measure.map Prod.fst
        (Measure.map (tuplePairMap (X := X) (Y := Y) (n := n))
          (ProbabilityMeasure.pi (fun _ : Fin n => π.joint) : Measure (Fin n → X × Y))) = _
    rw [Measure.map_map measurable_fst
      (measurable_tuplePairMap (X := X) (Y := Y) (n := n))]
    change Measure.map (fun t i => (t i).1)
      (Measure.pi (fun _ : Fin n => (π.joint : Measure (X × Y)))) = _
    rw [Measure.pi_map_pi (f := fun _ : Fin n => Prod.fst)
      (fun _ => measurable_fst.aemeasurable)]
    have hfst : Measure.map Prod.fst (π.joint : Measure (X × Y)) = μ := by
      simpa using congrArg ProbabilityMeasure.toMeasure π.fst_map
    simpa [iidMeasure, ProbabilityMeasure.toMeasure_pi] using
      congrArg (fun ρ : Measure X => Measure.pi (fun _ : Fin n => ρ)) hfst
  snd_map := by
    apply ProbabilityMeasure.toMeasure_injective
    change Measure.map Prod.snd
        (Measure.map (tuplePairMap (X := X) (Y := Y) (n := n))
          (ProbabilityMeasure.pi (fun _ : Fin n => π.joint) : Measure (Fin n → X × Y))) = _
    rw [Measure.map_map measurable_snd
      (measurable_tuplePairMap (X := X) (Y := Y) (n := n))]
    change Measure.map (fun t i => (t i).2)
      (Measure.pi (fun _ : Fin n => (π.joint : Measure (X × Y)))) = _
    rw [Measure.pi_map_pi (f := fun _ : Fin n => Prod.snd)
      (fun _ => measurable_snd.aemeasurable)]
    have hsnd : Measure.map Prod.snd (π.joint : Measure (X × Y)) = ν := by
      simpa using congrArg ProbabilityMeasure.toMeasure π.snd_map
    simpa [iidMeasure, ProbabilityMeasure.toMeasure_pi] using
      congrArg (fun ρ : Measure Y => Measure.pi (fun _ : Fin n => ρ)) hsnd

/-- Integrating a cost after the iid pair coupling is the product-sample
integral of that cost on the two coordinate tuples. -/
theorem cost_tuples (π : MeasureCoupling μ ν) (n : ℕ)
    (c : (Fin n → X) → (Fin n → Y) → ℝ≥0∞)
    (hc : Measurable (fun ts : (Fin n → X) × (Fin n → Y) => c ts.1 ts.2)) :
    (π.tuples n).cost c =
      ∫⁻ t, c (fun i => (t i).1) (fun i => (t i).2)
        ∂(ProbabilityMeasure.pi (fun _ : Fin n => π.joint) : Measure (Fin n → X × Y)) := by
  change ∫⁻ ts, c ts.1 ts.2 ∂Measure.map
      (tuplePairMap (X := X) (Y := Y) (n := n))
      (ProbabilityMeasure.pi (fun _ : Fin n => π.joint) : Measure (Fin n → X × Y)) = _
  rw [lintegral_map hc (measurable_tuplePairMap (X := X) (Y := Y) (n := n))]
  rfl

/-- Any measurable sample statistics inherit a coupling from the iid input
coupling. -/
def sampleLaw {μ : ProbabilityMeasure X} {ν : ProbabilityMeasure Y}
    (π : MeasureCoupling μ ν) (n : ℕ) (f : (Fin n → X) → Z) (g : (Fin n → Y) → W)
    [MeasurableSpace Z] [MeasurableSpace W] (hf : Measurable f) (hg : Measurable g) :
    MeasureCoupling ((iidMeasure μ n).map hf.aemeasurable)
      ((iidMeasure ν n).map hg.aemeasurable) :=
  (π.tuples n).map f g hf hg

end MeasureCoupling

private def pairIndices (n : ℕ) : Finset (Fin n × Fin n) :=
  (Finset.univ.product Finset.univ).filter fun ij => ij.1 < ij.2

private def pairEnergyNested (c : X → X → ℝ≥0∞) {n : ℕ} (t : Fin n → X) : ℝ≥0∞ :=
  ∑ i : Fin n, ∑ j : Fin n, if i < j then c (t i) (t j) else 0

private def pairEnergySum (c : X → X → ℝ≥0∞) {n : ℕ} (t : Fin n → X) : ℝ≥0∞ :=
  ∑ ij : Fin n × Fin n, if ij.1 < ij.2 then c (t ij.1) (t ij.2) else 0

omit [MeasurableSpace X] in
private theorem pairEnergy_eq_pairEnergyNested (c : X → X → ℝ≥0∞) {n : ℕ}
    (t : Fin n → X) : pairEnergy c t = pairEnergyNested c t := by
  induction n with
  | zero => simp [pairEnergy, pairEnergyNested]
  | succ n ih =>
    simp [pairEnergy_succ, pairEnergyNested, Fin.sum_univ_succ, ih, add_comm]

omit [MeasurableSpace X] in
private theorem pairEnergyNested_eq_pairEnergySum (c : X → X → ℝ≥0∞) {n : ℕ}
    (t : Fin n → X) : pairEnergyNested c t = pairEnergySum c t := by
  change (∑ i : Fin n, ∑ j : Fin n, if i < j then c (t i) (t j) else 0) = _
  exact (Fintype.sum_prod_type' (fun i j => if i < j then c (t i) (t j) else 0)).symm

omit [MeasurableSpace X] in
private theorem pairEnergySum_eq_pairIndicesSum (c : X → X → ℝ≥0∞) {n : ℕ}
    (t : Fin n → X) : pairEnergySum c t =
      ∑ ij ∈ pairIndices n, c (t ij.1) (t ij.2) := by
  simp [pairEnergySum, pairIndices, Finset.sum_filter]

omit [MeasurableSpace X] in
private theorem pairEnergy_eq_pairEnergySum (c : X → X → ℝ≥0∞) {n : ℕ}
    (t : Fin n → X) : pairEnergy c t = pairEnergySum c t := by
  rw [pairEnergy_eq_pairEnergyNested, pairEnergyNested_eq_pairEnergySum]

private theorem pairIndices_card (n : ℕ) : (pairIndices n).card = n.choose 2 := by
  simpa [pairIndices, Fintype.card_fin] using
    (Finset.card_product_filter_lt (s := (Finset.univ : Finset (Fin n))))

private theorem iid_pair_map (μ : ProbabilityMeasure X) (n : ℕ)
    (i j : Fin n) (hij : i ≠ j) :
    Measure.map (fun t : Fin n → X => (t i, t j))
      (Measure.pi (fun _ : Fin n => (μ : Measure X))) =
        (μ : Measure X).prod μ := by
  let ν : Fin n → Measure X := fun _ => (μ : Measure X)
  have hind : iIndepFun (fun (i : Fin n) (t : Fin n → X) => t i) (Measure.pi ν) :=
    iIndepFun_pi (X := fun _ : Fin n => id) (fun _ => aemeasurable_id)
  have hmap := (hind.indepFun hij).map_prod_eq_prod_map_map
    (measurable_pi_apply i).aemeasurable (measurable_pi_apply j).aemeasurable
  have hi : Measure.map (fun t : Fin n → X => t i) (Measure.pi ν) = μ := by
    exact (measurePreserving_eval ν i).map_eq
  have hj : Measure.map (fun t : Fin n → X => t j) (Measure.pi ν) = μ := by
    exact (measurePreserving_eval ν j).map_eq
  simpa [ν, hi, hj] using hmap

private theorem lintegral_iid_pair (μ : ProbabilityMeasure X) (n : ℕ)
    (c : X → X → ℝ≥0∞) (hc : Measurable (fun xy : X × X => c xy.1 xy.2))
    (i j : Fin n) (hij : i ≠ j) :
    ∫⁻ t, c (t i) (t j) ∂(iidMeasure μ n : Measure (Fin n → X)) =
      ∫⁻ xy, c xy.1 xy.2 ∂(μ : Measure X).prod μ := by
  calc
    _ = ∫⁻ xy, c xy.1 xy.2 ∂Measure.map (fun t : Fin n → X => (t i, t j))
        (iidMeasure μ n : Measure (Fin n → X)) := by
      symm
      rw [iidMeasure, ProbabilityMeasure.toMeasure_pi]
      exact lintegral_map hc (by fun_prop)
    _ = _ := by
      rw [iidMeasure, ProbabilityMeasure.toMeasure_pi]
      rw [iid_pair_map μ n i j hij]

/-- The unordered pair energy has the exact iid expectation. -/
theorem lintegral_iid_pairEnergy (μ : ProbabilityMeasure X) (n : ℕ)
    (c : X → X → ℝ≥0∞) (hc : Measurable (fun xy : X × X => c xy.1 xy.2)) :
    ∫⁻ t, pairEnergy c t ∂(iidMeasure μ n : Measure (Fin n → X)) =
      (n.choose 2 : ℝ≥0∞) * ∫⁻ xy, c xy.1 xy.2 ∂(μ : Measure X).prod μ := by
  classical
  simp_rw [pairEnergy_eq_pairEnergySum, pairEnergySum_eq_pairIndicesSum]
  rw [lintegral_finsetSum (s := pairIndices n)]
  · calc
      _ = ∑ ij ∈ pairIndices n,
          ∫⁻ t, c (t ij.1) (t ij.2) ∂(iidMeasure μ n : Measure (Fin n → X)) := by
        apply Finset.sum_congr rfl
        intro ij hij
        rfl
      _ = ∑ ij ∈ pairIndices n,
          ∫⁻ xy, c xy.1 xy.2 ∂(μ : Measure X).prod μ := by
        apply Finset.sum_congr rfl
        intro ij hij
        exact lintegral_iid_pair μ n c hc ij.1 ij.2
          (ne_of_lt (Finset.mem_filter.mp hij).2)
      _ = (n.choose 2 : ℝ≥0∞) *
          ∫⁻ xy, c xy.1 xy.2 ∂(μ : Measure X).prod μ := by
        rw [Finset.sum_const, nsmul_eq_mul, pairIndices_card]
  · intro ij hij
    fun_prop

/-- Sharp finite-p bound for the maximum of a distance matrix from an iid
sample. The diagonal-zero condition is essential for nonatomic laws. -/
theorem lintegral_iid_pairMaximum_rpow_le (μ : ProbabilityMeasure X) (n : ℕ)
    (c : X → X → ℝ≥0∞) (hc : ∀ x, c x x = 0)
    (hs : ∀ x y, c x y = c y x) {p : ℝ} (hp : 0 < p)
    (hcm : Measurable (fun xy : X × X => c xy.1 xy.2)) :
    ∫⁻ t, pairMaximum c t ^ p ∂(iidMeasure μ n : Measure (Fin n → X)) ≤
      (n.choose 2 : ℝ≥0∞) * ∫⁻ xy, c xy.1 xy.2 ^ p ∂(μ : Measure X).prod μ := by
  calc
    _ ≤ ∫⁻ t, pairEnergy (fun x y => c x y ^ p) t
        ∂(iidMeasure μ n : Measure (Fin n → X)) := by
      apply lintegral_mono
      intro t
      exact pairMaximum_rpow_le_pairEnergy c hc hs hp t
    _ = (n.choose 2 : ℝ≥0∞) *
        ∫⁻ xy, c xy.1 xy.2 ^ p ∂(μ : Measure X).prod μ :=
      lintegral_iid_pairEnergy μ n (fun x y => c x y ^ p) (by fun_prop)

end TDA.Probability
