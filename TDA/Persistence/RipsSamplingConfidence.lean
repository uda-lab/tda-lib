import TDA.Probability.SamplingCoverage
import TDA.Persistence.RipsSampling
import TDA.Persistence.RipsQTameInfiniteMetricStability
import TDA.Persistence.LocallyFiniteDiagramBottleneckLaws

/-!
# Finite iid confidence bounds for canonical q-tame Rips diagrams

A sample is the finite range of a tuple, so draws with equal values give one
vertex. The canonical locally finite diagram retains essential bars and uses
closed diameter time. Its factor-two Hausdorff stability gives continuity of the
sample diagram and finite-net confidence bounds in every homological degree.
-/

noncomputable section

universe u v

namespace TDA.Persistence.Rips

open MeasureTheory Metric Set TDA.Probability
open scoped ENNReal NNReal Topology

variable {X : Type u} [MetricSpace X] [LinearOrder X] {n : ℕ}

/-- The actual canonical locally finite q-tame diagram of a finite tuple range. -/
def qTameSampleDiagram (k : Type v) [Field k] (t : Fin n → X) (degree : ℕ) :
    LocallyFiniteDecoratedDiagram :=
  qTameLocallyFiniteDiagram (X := Sample t) k
    (Set.finite_univ.totallyBounded : TotallyBounded (Set.univ : Set (Sample t))) degree

/-- Equal sampled ranges have identical canonical q-tame diagrams, including
when one tuple repeats values more often than the other. -/
theorem qTameSampleDiagram_eq_of_range_eq (k : Type v) [Field k]
    {m : ℕ} (t : Fin n → X) (s : Fin m → X) (h : Set.range t = Set.range s)
    (degree : ℕ) : qTameSampleDiagram k t degree = qTameSampleDiagram k s degree := by
  let e : Sample t ≃ᵢ Sample s :=
    { Equiv.setCongr h with isometry_toFun := fun _ _ => rfl }
  exact qTameLocallyFiniteDiagram_eq_of_isometryEquiv k e _ _ degree

omit [LinearOrder X] in
/-- Pairing draws with the same index bounds the Hausdorff distance between
ranges by the product metric on tuples. No injectivity assumption is needed. -/
theorem hausdorffDist_range_le_dist (t s : Fin n → X) :
    hausdorffDist (Set.range t) (Set.range s) ≤ dist t s := by
  apply hausdorffDist_le_of_mem_dist dist_nonneg
  · rintro x ⟨i, rfl⟩
    exact ⟨s i, ⟨i, rfl⟩, dist_le_pi_dist t s i⟩
  · rintro y ⟨i, rfl⟩
    exact ⟨t i, ⟨i, rfl⟩, by simpa [dist_comm] using dist_le_pi_dist t s i⟩

/-- The canonical q-tame sample diagram obeys the sharp factor-two tuple bound. -/
theorem bottleneck_qTameSampleDiagram_le (k : Type v) [Field k]
    (hn : 0 < n) (t s : Fin n → X) (degree : ℕ) :
    (qTameSampleDiagram k t degree).bottleneck (qTameSampleDiagram k s degree) ≤
      ENNReal.ofReal (2 * dist t s) := by
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let : Nonempty (Sample t) := ⟨sampleProjection t (Classical.choice inferInstance)⟩
  let : Nonempty (Sample s) := ⟨sampleProjection s (Classical.choice inferInstance)⟩
  have h := qTameLocallyFiniteDiagram_bottleneck_le_of_hausdorffDist
    (X := Sample t) (Y := Sample s)
    (isometry_subtype_coe : Isometry (Subtype.val : Sample t → X))
    (isometry_subtype_coe : Isometry (Subtype.val : Sample s → X))
    (Set.finite_univ.totallyBounded : TotallyBounded (Set.univ : Set (Sample t)))
    (Set.finite_univ.totallyBounded : TotallyBounded (Set.univ : Set (Sample s))) k degree
  apply h.trans
  apply ENNReal.ofReal_le_ofReal
  simpa only [Subtype.range_val] using
    mul_le_mul_of_nonneg_left (hausdorffDist_range_le_dist t s) (by norm_num : (0 : ℝ) ≤ 2)

/-- The genuine canonical diagram statistic is two-Lipschitz. -/
theorem lipschitzWith_qTameSampleDiagram (k : Type v) [Field k]
    (hn : 0 < n) (degree : ℕ) :
    LipschitzWith 2 (fun t : Fin n → X => qTameSampleDiagram k t degree) := by
  intro t s
  simpa only [LocallyFiniteDecoratedDiagram.edist_eq_bottleneck, edist_dist,
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat,
    ENNReal.coe_ofNat] using bottleneck_qTameSampleDiagram_le k hn t s degree

/-- Distance from the canonical sample diagram to any fixed locally finite
diagram is continuous, including when this extended distance is infinite. -/
theorem continuous_bottleneck_qTameSampleDiagram (k : Type v) [Field k]
    (hn : 0 < n) (degree : ℕ) (D : LocallyFiniteDecoratedDiagram) :
    Continuous (fun t : Fin n → X => (qTameSampleDiagram k t degree).bottleneck D) := by
  exact (lipschitzWith_qTameSampleDiagram k hn degree).continuous.edist continuous_const

/-- Measurability is obtained from stability of the actual diagram statistic. -/
theorem measurable_bottleneck_qTameSampleDiagram [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    (k : Type v) [Field k] (hn : 0 < n) (degree : ℕ)
    (D : LocallyFiniteDecoratedDiagram) :
    Measurable (fun t : Fin n → X => (qTameSampleDiagram k t degree).bottleneck D) :=
  (continuous_bottleneck_qTameSampleDiagram k hn degree D).measurable

/-- The actual diagram distance exceedance event is measurable. -/
theorem measurableSet_bottleneck_qTameSampleDiagram_gt
    [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    (k : Type v) [Field k] (hn : 0 < n) (degree : ℕ)
    (D : LocallyFiniteDecoratedDiagram) (a : ℝ≥0∞) :
    MeasurableSet {t : Fin n → X | a < (qTameSampleDiagram k t degree).bottleneck D} :=
  measurableSet_lt measurable_const (measurable_bottleneck_qTameSampleDiagram k hn degree D)

omit [LinearOrder X] in
/-- Hitting each radius-`r/2` net ball puts the sampled range within Hausdorff
radius `r` of its carrier. -/
theorem hausdorffDist_range_univ_le_of_hits_net {C : Type*}
    (t : Fin n → X) (c : C → X) {r : ℝ} (hr : 0 ≤ r)
    (hnet : ∀ x, ∃ j, dist x (c j) < r / 2)
    (hhit : ∀ j, ∃ i, t i ∈ ball (c j) (r / 2)) :
    hausdorffDist (Set.range t) Set.univ ≤ r := by
  apply hausdorffDist_le_of_mem_dist hr
  · rintro x hx
    exact ⟨x, Set.mem_univ x, by simpa using hr⟩
  · intro x _
    obtain ⟨j, hj⟩ := hnet x
    obtain ⟨i, hi⟩ := hhit j
    refine ⟨t i, ⟨i, rfl⟩, ?_⟩
    have hi' : dist (c j) (t i) < r / 2 := by simpa [dist_comm] using hi
    exact (dist_triangle x (c j) (t i)).trans (by linarith)

/-- Finite-net coverage controls the actual canonical diagram, using diameter
Rips time and preserving every essential occurrence. -/
theorem bottleneck_qTameSampleDiagram_le_of_hits_net
    (k : Type v) [Field k] [Nonempty X] (hX : TotallyBounded (Set.univ : Set X))
    (hn : 0 < n) (t : Fin n → X) (degree : ℕ) {C : Type*}
    (c : C → X) {r : ℝ} (hr : 0 ≤ r)
    (hnet : ∀ x, ∃ j, dist x (c j) < r / 2)
    (hhit : ∀ j, ∃ i, t i ∈ ball (c j) (r / 2)) :
    (qTameSampleDiagram k t degree).bottleneck
      (qTameLocallyFiniteDiagram (X := X) k hX degree) ≤ ENNReal.ofReal (2 * r) := by
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let : Nonempty (Sample t) := ⟨sampleProjection t (Classical.choice inferInstance)⟩
  have h := qTameLocallyFiniteDiagram_bottleneck_le_of_hausdorffDist
    (X := Sample t) (Y := X)
    (isometry_subtype_coe : Isometry (Subtype.val : Sample t → X))
    (isometry_id : Isometry (id : X → X))
    (Set.finite_univ.totallyBounded : TotallyBounded (Set.univ : Set (Sample t))) hX k degree
  apply h.trans
  apply ENNReal.ofReal_le_ofReal
  simpa only [Subtype.range_val, Set.range_id] using mul_le_mul_of_nonneg_left
    (hausdorffDist_range_univ_le_of_hits_net t c hr hnet hhit) (by norm_num : (0 : ℝ) ≤ 2)

omit [LinearOrder X] in
/-- The minimum mass of positive-radius balls in a full-support probability
carrier is strictly positive. Its upper bound by one is `finiteCoverMass_le_one`. -/
theorem finiteCoverMass_ball_pos [MeasurableSpace X]
    (μ : ProbabilityMeasure X) [(μ : Measure X).IsOpenPosMeasure]
    {C : Type*} [Fintype C] [Nonempty C] (c : C → X) {r : ℝ} (hr : 0 < r) :
    0 < finiteCoverMass μ (fun j => ball (c j) (r / 2)) := by
  apply finiteCoverMass_pos
  intro j
  exact Metric.measure_ball_pos (μ : Measure X) (c j) (by linarith)

/-- A finite iid confidence bound for the genuine canonical locally finite Rips
diagram. The finite minimum and subtraction are in `ℝ≥0∞`; hence subtraction
is truncated and the minimum is explicitly bounded by one. -/
theorem measure_bottleneck_qTameSampleDiagram_gt_le
    [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] [Nonempty X]
    (μ : ProbabilityMeasure X) (k : Type v) [Field k]
    (hX : TotallyBounded (Set.univ : Set X)) (hn : 0 < n) (degree : ℕ)
    {C : Type*} [Fintype C] [Nonempty C] (c : C → X) {r : ℝ} (hr : 0 < r)
    (hnet : ∀ x, ∃ j, dist x (c j) < r / 2) :
    (iidMeasure μ n : Measure (Fin n → X))
      {t | ENNReal.ofReal (2 * r) < (qTameSampleDiagram k t degree).bottleneck
        (qTameLocallyFiniteDiagram (X := X) k hX degree)} ≤
      (Fintype.card C : ℝ≥0∞) *
        (1 - finiteCoverMass μ (fun j => ball (c j) (r / 2))) ^ n := by
  apply le_trans (measure_mono (t := missedCover n (fun j => ball (c j) (r / 2))) ?_)
    (measure_missedCover_le_finiteCoverMass μ n _ (fun _ => measurableSet_ball))
  intro t ht
  by_contra hh
  exact not_lt_of_ge (bottleneck_qTameSampleDiagram_le_of_hits_net k hX hn t degree c hr.le
    hnet (not_mem_missedCover_iff.mp hh)) ht

/-- Coverage bounds the sample-to-carrier diagram distance when every sampled
coordinate lies in the carrier. -/
theorem bottleneck_qTameSampleDiagram_carrier_le_of_hits_net
    (k : Type v) [Field k] {K : Set X} [Nonempty K]
    (hK : TotallyBounded (Set.univ : Set K)) (hn : 0 < n)
    (t : Fin n → X) (ht : ∀ i, t i ∈ K) (degree : ℕ) {C : Type*}
    (c : C → K) {r : ℝ} (hr : 0 ≤ r)
    (hnet : ∀ x : K, ∃ j, dist x (c j) < r / 2)
    (hhit : ∀ j, ∃ i, t i ∈ ball (c j : X) (r / 2)) :
    (qTameSampleDiagram k t degree).bottleneck
      (qTameLocallyFiniteDiagram (X := K) k hK degree) ≤ ENNReal.ofReal (2 * r) := by
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let : Nonempty (Sample t) := ⟨sampleProjection t (Classical.choice inferInstance)⟩
  have hhaus : hausdorffDist (Set.range t) K ≤ r := by
    apply hausdorffDist_le_of_mem_dist hr
    · rintro x ⟨i, rfl⟩
      exact ⟨t i, ht i, by simpa using hr⟩
    · intro x hx
      obtain ⟨j, hj⟩ := hnet ⟨x, hx⟩
      obtain ⟨i, hi⟩ := hhit j
      refine ⟨t i, ⟨i, rfl⟩, ?_⟩
      have hi' : dist (c j : X) (t i) < r / 2 := by simpa [dist_comm] using hi
      have hj' : dist x (c j : X) < r / 2 := hj
      exact (dist_triangle x (c j) (t i)).trans (by linarith)
  have h := qTameLocallyFiniteDiagram_bottleneck_le_of_hausdorffDist
    (X := Sample t) (Y := K)
    (isometry_subtype_coe : Isometry (Subtype.val : Sample t → X))
    (isometry_subtype_coe : Isometry (Subtype.val : K → X))
    (Set.finite_univ.totallyBounded : TotallyBounded (Set.univ : Set (Sample t))) hK k degree
  apply h.trans
  apply ENNReal.ofReal_le_ofReal
  simpa only [Subtype.range_val] using
    mul_le_mul_of_nonneg_left hhaus (by norm_num : (0 : ℝ) ≤ 2)

/-- Ambient iid draws from a full-measure totally bounded carrier satisfy the
same confidence bound. The diagram event is measurable on the entire ambient
tuple space by `measurableSet_bottleneck_qTameSampleDiagram_gt`. -/
theorem measure_bottleneck_qTameSampleDiagram_carrier_gt_le
    [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    (μ : ProbabilityMeasure X) (k : Type v) [Field k]
    {K : Set X} [Nonempty K] (hK : TotallyBounded (Set.univ : Set K))
    (hKm : MeasurableSet K) (hfull : (μ : Measure X) K = 1)
    (hn : 0 < n) (degree : ℕ) {C : Type*} [Fintype C] [Nonempty C]
    (c : C → K) {r : ℝ} (hr : 0 < r)
    (hnet : ∀ x : K, ∃ j, dist x (c j) < r / 2) :
    (iidMeasure μ n : Measure (Fin n → X))
      {t | ENNReal.ofReal (2 * r) < (qTameSampleDiagram k t degree).bottleneck
        (qTameLocallyFiniteDiagram (X := K) k hK degree)} ≤
      (Fintype.card C : ℝ≥0∞) *
        (1 - finiteCoverMass μ (fun j => ball (c j : X) (r / 2))) ^ n := by
  have hmem : ∀ᵐ x ∂(μ : Measure X), x ∈ K := (mem_ae_iff_prob_eq_one hKm).mpr hfull
  have hcoord : ∀ i : Fin n, ∀ᵐ t ∂(iidMeasure μ n : Measure (Fin n → X)), t i ∈ K := by
    intro i
    change ∀ᵐ t ∂(Measure.pi (fun _ : Fin n => (μ : Measure X))), t i ∈ K
    exact (measurePreserving_eval (fun _ : Fin n => (μ : Measure X)) i).quasiMeasurePreserving.ae hmem
  have hall : ∀ᵐ t ∂(iidMeasure μ n : Measure (Fin n → X)), ∀ i, t i ∈ K :=
    ae_all_iff.mpr hcoord
  apply le_trans (measure_mono_ae (t := missedCover n (fun j => ball (c j : X) (r / 2))) ?_)
    (measure_missedCover_le_finiteCoverMass μ n _ (fun _ => measurableSet_ball))
  filter_upwards [hall] with t ht hbad
  by_contra hh
  exact not_lt_of_ge (bottleneck_qTameSampleDiagram_carrier_le_of_hits_net k hK hn t ht degree
    c hr.le hnet (not_mem_missedCover_iff.mp hh)) hbad

/-- The canonical q-tame Rips diagram of a compact ambient carrier. The auxiliary
linear order is inherited from the ambient space and carries no metric assumption. -/
def qTameCompactCarrierDiagram (k : Type v) [Field k] (K : Set X)
    (hK : IsCompact K) (degree : ℕ) : LocallyFiniteDecoratedDiagram := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  exact qTameLocallyFiniteDiagram (X := K) k isCompact_univ.totallyBounded degree

/-- A compactly supported Borel probability on a second countable metric space
satisfies the finite-net confidence bound on the ambient tuple space. The support
is conull by second countability, and all coordinates lie in it almost surely. -/
theorem measure_bottleneck_qTameSampleDiagram_support_gt_le
    [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    (μ : ProbabilityMeasure X) (k : Type v) [Field k]
    (hK : IsCompact (μ : Measure X).support) (hn : 0 < n) (degree : ℕ)
    {C : Type*} [Fintype C] [Nonempty C] (c : C → (μ : Measure X).support)
    {r : ℝ} (hr : 0 < r)
    (hnet : ∀ x : (μ : Measure X).support, ∃ j, dist x (c j) < r / 2) :
    (iidMeasure μ n : Measure (Fin n → X))
      {t | ENNReal.ofReal (2 * r) < (qTameSampleDiagram k t degree).bottleneck
        (qTameCompactCarrierDiagram k (μ : Measure X).support hK degree)} ≤
      (Fintype.card C : ℝ≥0∞) *
        (1 - finiteCoverMass μ (fun j => ball (c j : X) (r / 2))) ^ n := by
  let : Nonempty (μ : Measure X).support := ⟨c (Classical.arbitrary C)⟩
  let : CompactSpace (μ : Measure X).support := isCompact_iff_compactSpace.mp hK
  exact measure_bottleneck_qTameSampleDiagram_carrier_gt_le μ k
    isCompact_univ.totallyBounded Measure.isClosed_support.measurableSet
    (measure_support_eq_one μ) hn degree c hr hnet

/-- The compact-support confidence event is measurable on ambient tuples. -/
theorem measurableSet_bottleneck_qTameSampleDiagram_support_gt
    [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    (μ : ProbabilityMeasure X) (k : Type v) [Field k]
    (hK : IsCompact (μ : Measure X).support) (hn : 0 < n) (degree : ℕ) (a : ℝ≥0∞) :
    MeasurableSet {t : Fin n → X | a < (qTameSampleDiagram k t degree).bottleneck
      (qTameCompactCarrierDiagram k (μ : Measure X).support hK degree)} :=
  measurableSet_bottleneck_qTameSampleDiagram_gt k hn degree _ a

omit [LinearOrder X] in
/-- The finite minimum appearing in the ambient support estimate is positive. -/
theorem finiteCoverMass_support_ball_pos [MeasurableSpace X]
    (μ : ProbabilityMeasure X) {C : Type*} [Fintype C] [Nonempty C]
    (c : C → (μ : Measure X).support) {r : ℝ} (hr : 0 < r) :
    0 < finiteCoverMass μ (fun j => ball (c j : X) (r / 2)) := by
  apply finiteCoverMass_pos
  intro j
  exact measure_ball_pos_of_mem_support μ (c j).property (by linarith)

end TDA.Persistence.Rips
