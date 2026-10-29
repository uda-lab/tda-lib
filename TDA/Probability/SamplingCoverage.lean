import TDA.Probability.MeasureSampling
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Topology.MetricSpace.Pseudo.Basic

/-!
# Finite iid coverage bounds and probability measures on their support

A tuple misses a finite cover if one member contains none of its coordinates.
The product law gives its exact avoidance probability, and a finite union bound
gives both a sum estimate and a common-mass estimate. Subtraction takes place in
`ℝ≥0∞`, so `1 - β` is truncated subtraction. The finite nonempty minimum of the
cover masses is positive whenever every member has positive mass, and is at most one.

The support construction uses second countability to establish full measure;
compactness of the support alone is not used to justify that assertion.
-/

noncomputable section

universe u v

namespace TDA.Probability

open MeasureTheory Set
open scoped ENNReal

variable {X : Type u} {C : Type v} [MeasurableSpace X]

/-- Ordered samples that fail to hit at least one member of an indexed cover. -/
def missedCover (n : ℕ) (A : C → Set X) : Set (Fin n → X) :=
  {t | ∃ c, ∀ i, t i ∉ A c}

omit [MeasurableSpace X] in
@[simp]
theorem mem_missedCover {n : ℕ} {A : C → Set X} {t : Fin n → X} :
    t ∈ missedCover n A ↔ ∃ c, ∀ i, t i ∉ A c := Iff.rfl

omit [MeasurableSpace X] in
/-- Hitting every cover member is exactly the complement of the missed-cover event. -/
theorem not_mem_missedCover_iff {n : ℕ} {A : C → Set X} {t : Fin n → X} :
    t ∉ missedCover n A ↔ ∀ c, ∃ i, t i ∈ A c := by
  classical
  simp [missedCover]

/-- A finite measurable cover has a measurable missed-cover event. -/
theorem measurableSet_missedCover [Fintype C] (n : ℕ) (A : C → Set X)
    (hA : ∀ c, MeasurableSet (A c)) : MeasurableSet (missedCover n A) := by
  have heq : missedCover n A =
      ⋃ c, ⋂ i, (fun t : Fin n → X => t i) ⁻¹' (A c)ᶜ := by
    ext t
    simp [missedCover]
  rw [heq]
  exact MeasurableSet.iUnion fun c => MeasurableSet.iInter fun i =>
    (hA c).compl.preimage (measurable_pi_apply i)

/-- The exact probability that all iid coordinates avoid a measurable set. -/
theorem measure_iid_no_hit (μ : ProbabilityMeasure X) (n : ℕ) (A : Set X)
    (hA : MeasurableSet A) :
    (iidMeasure μ n : Measure (Fin n → X)) {t | ∀ i, t i ∉ A} =
      (1 - (μ : Measure X) A)^n := by
  have heq : {t : Fin n → X | ∀ i, t i ∉ A} = Set.pi Set.univ (fun _ => Aᶜ) := by
    ext t
    simp
  rw [heq, iidMeasure, ProbabilityMeasure.toMeasure_pi, Measure.pi_pi]
  simp [prob_compl_eq_one_sub hA]

/-- A finite union bound by the exact probabilities of missing individual members. -/
theorem measure_missedCover_le_sum [Fintype C] (μ : ProbabilityMeasure X)
    (n : ℕ) (A : C → Set X) (hA : ∀ c, MeasurableSet (A c)) :
    (iidMeasure μ n : Measure (Fin n → X)) (missedCover n A) ≤
      ∑ c, (1 - (μ : Measure X) (A c))^n := by
  classical
  have heq : missedCover n A = ⋃ c, {t : Fin n → X | ∀ i, t i ∉ A c} := by
    ext t
    simp [missedCover]
  rw [heq]
  calc
    _ ≤ ∑ c, (iidMeasure μ n : Measure (Fin n → X))
        {t | ∀ i, t i ∉ A c} := measure_iUnion_fintype_le _ _
    _ = _ := by simp_rw [measure_iid_no_hit μ n _ (hA _)]

/-- A common lower mass gives the cardinality form of the finite iid coverage bound. -/
theorem measure_missedCover_le_card_mul [Fintype C] (μ : ProbabilityMeasure X)
    (n : ℕ) (A : C → Set X) (hA : ∀ c, MeasurableSet (A c)) (β : ℝ≥0∞)
    (hβ : ∀ c, β ≤ (μ : Measure X) (A c)) :
    (iidMeasure μ n : Measure (Fin n → X)) (missedCover n A) ≤
      (Fintype.card C : ℝ≥0∞) * (1 - β)^n := by
  classical
  refine (measure_missedCover_le_sum μ n A hA).trans ?_
  calc
    _ ≤ ∑ _ : C, (1 - β)^n := by
      apply Finset.sum_le_sum
      intro c _
      exact pow_le_pow_left' (tsub_le_tsub_left (hβ c) 1) n
    _ = _ := by simp [nsmul_eq_mul]

section Minimum

variable [Fintype C] [Nonempty C]

/-- The minimum mass of a finite nonempty family of sets. -/
def finiteCoverMass (μ : ProbabilityMeasure X) (A : C → Set X) : ℝ≥0∞ :=
  Finset.univ.inf' Finset.univ_nonempty (fun c => (μ : Measure X) (A c))

/-- The minimum cover mass bounds every cover member's mass from below. -/
theorem finiteCoverMass_le (μ : ProbabilityMeasure X) (A : C → Set X) (c : C) :
    finiteCoverMass μ A ≤ (μ : Measure X) (A c) := by
  classical
  exact Finset.inf'_le _ (Finset.mem_univ c)

/-- Every finite cover mass is at most one. -/
theorem finiteCoverMass_le_one (μ : ProbabilityMeasure X) (A : C → Set X) :
    finiteCoverMass μ A ≤ 1 :=
  (finiteCoverMass_le μ A (Classical.arbitrary C)).trans prob_le_one

/-- A finite nonempty family of positive-mass sets has positive minimum mass. -/
theorem finiteCoverMass_pos (μ : ProbabilityMeasure X) (A : C → Set X)
    (hA : ∀ c, 0 < (μ : Measure X) (A c)) : 0 < finiteCoverMass μ A := by
  classical
  exact (Finset.lt_inf'_iff _).mpr (by simpa using hA)

/-- The coverage estimate using the actual minimum of the cover masses. -/
theorem measure_missedCover_le_finiteCoverMass (μ : ProbabilityMeasure X)
    (n : ℕ) (A : C → Set X) (hA : ∀ c, MeasurableSet (A c)) :
    (iidMeasure μ n : Measure (Fin n → X)) (missedCover n A) ≤
      (Fintype.card C : ℝ≥0∞) * (1 - finiteCoverMass μ A)^n :=
  measure_missedCover_le_card_mul μ n A hA _ (finiteCoverMass_le μ A)

end Minimum

section Carrier

/-- The probability law on a measurable carrier of full measure, pulled back along inclusion. -/
def carrierProbability (μ : ProbabilityMeasure X) (K : Set X) (hK : MeasurableSet K)
    (hfull : (μ : Measure X) K = 1) : ProbabilityMeasure K := by
  have hae : ∀ᵐ x ∂(μ : Measure X), x ∈ Set.range (Subtype.val : K → X) := by
    filter_upwards [(mem_ae_iff_prob_eq_one hK).mpr hfull] with x hx
    exact ⟨⟨x, hx⟩, rfl⟩
  exact ⟨(μ : Measure X).comap Subtype.val,
    (MeasurableEmbedding.subtype_coe hK).isProbabilityMeasure_comap hae⟩

/-- Inclusion transports the full-measure carrier probability back to its ambient law. -/
theorem map_carrierProbability_val (μ : ProbabilityMeasure X) (K : Set X)
    (hK : MeasurableSet K) (hfull : (μ : Measure X) K = 1) :
    (carrierProbability μ K hK hfull).map measurable_subtype_coe.aemeasurable = μ := by
  apply ProbabilityMeasure.toMeasure_injective
  change Measure.map Subtype.val ((μ : Measure X).comap Subtype.val) = _
  rw [(MeasurableEmbedding.subtype_coe hK).map_comap, Subtype.range_coe]
  exact Measure.restrict_eq_self_of_ae_mem ((mem_ae_iff_prob_eq_one hK).mpr hfull)

/-- Ambient measurable sets have unchanged probability after restriction to a full-measure carrier. -/
theorem carrierProbability_preimage (μ : ProbabilityMeasure X) (K : Set X)
    (hK : MeasurableSet K) (hfull : (μ : Measure X) K = 1) (A : Set X)
    (hA : MeasurableSet A) :
    (carrierProbability μ K hK hfull : Measure K) (Subtype.val ⁻¹' A) =
      (μ : Measure X) A := by
  have hmap := congrArg ProbabilityMeasure.toMeasure (map_carrierProbability_val μ K hK hfull)
  rw [ProbabilityMeasure.toMeasure_map] at hmap
  rw [← hmap, Measure.map_apply measurable_subtype_coe hA]

end Carrier

section Support

variable [PseudoMetricSpace X]

/-- Every positive-radius ball about a support point has positive probability. -/
theorem measure_ball_pos_of_mem_support (μ : ProbabilityMeasure X) {x : X}
    (hx : x ∈ (μ : Measure X).support) {r : ℝ} (hr : 0 < r) :
    0 < (μ : Measure X) (Metric.ball x r) :=
  (Measure.mem_support_iff_forall x).mp hx _ (Metric.ball_mem_nhds x hr)

variable [SecondCountableTopology X] [OpensMeasurableSpace X]

/-- A Borel probability on a second countable metric space gives its support full measure. -/
theorem measure_support_eq_one (μ : ProbabilityMeasure X) :
    (μ : Measure X) (μ : Measure X).support = 1 :=
  (mem_ae_iff_prob_eq_one Measure.isClosed_support.measurableSet).mp Measure.support_mem_ae

/-- The ambient probability pulled back to its support carrier. -/
def supportProbability (μ : ProbabilityMeasure X) :
    ProbabilityMeasure (μ : Measure X).support :=
  carrierProbability μ _ Measure.isClosed_support.measurableSet (measure_support_eq_one μ)

/-- Inclusion of the support preserves its probability law. -/
theorem map_supportProbability_val (μ : ProbabilityMeasure X) :
    (supportProbability μ).map measurable_subtype_coe.aemeasurable = μ :=
  map_carrierProbability_val μ _ _ _

/-- A ball in the support carrier has the mass of the corresponding ambient ball. -/
theorem supportProbability_ball (μ : ProbabilityMeasure X)
    (x : (μ : Measure X).support) (r : ℝ) :
    (supportProbability μ : Measure (μ : Measure X).support) (Metric.ball x r) =
      (μ : Measure X) (Metric.ball (x : X) r) :=
  carrierProbability_preimage μ _ _ _ _ measurableSet_ball

/-- Positive-radius balls retain positive mass on the support carrier. -/
theorem supportProbability_ball_pos (μ : ProbabilityMeasure X)
    (x : (μ : Measure X).support) {r : ℝ} (hr : 0 < r) :
    0 < (supportProbability μ : Measure (μ : Measure X).support) (Metric.ball x r) := by
  rw [supportProbability_ball]
  exact measure_ball_pos_of_mem_support μ x.property hr

/-- The probability on the support is positive on every nonempty relative open set. -/
instance supportProbability_isOpenPosMeasure (μ : ProbabilityMeasure X) :
    (supportProbability μ : Measure (μ : Measure X).support).IsOpenPosMeasure where
  open_pos U hU hne := by
    obtain ⟨x, hx⟩ := hne
    obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp hU x hx
    exact ne_of_gt ((supportProbability_ball_pos μ x hr).trans_le (measure_mono hsub))

end Support

end TDA.Probability
