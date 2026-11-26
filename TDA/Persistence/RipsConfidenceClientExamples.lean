import TDA.Persistence.RipsSamplingConfidence
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace

/-!
# Client statements of the Rips sampling confidence bounds

Regression fixtures for #1266, family 6 of the downstream-use audit (#1207). Each statement is
written as a downstream client writes it: the file opens no scope and declares no instance, and
the ambient metric space carries no order.

* A compactly supported Borel probability on a Euclidean space: the probability that the Rips
  diagram of `n` iid draws is farther than `2 * r` from the diagram of the support, bounded
  through a finite `r / 2`-net of the support, and measurability of that event.
* A compact metric space: the same bound against the diagram of the whole space.
-/

namespace TDA.Persistence.RipsConfidenceClientExamples

/-- The compact-support confidence bound on a Euclidean space. -/
theorem euclidean_support_confidence {d n : ℕ}
    (μ : MeasureTheory.ProbabilityMeasure (EuclideanSpace ℝ (Fin d))) (k : Type) [Field k]
    (hK : IsCompact (μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))).support)
    (hn : 0 < n) (degree : ℕ) {C : Type} [Fintype C] [Nonempty C]
    (c : C → (μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))).support) {r : ℝ}
    (hr : 0 < r)
    (hnet : ∀ x : (μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))).support,
      ∃ j, dist x (c j) < r / 2) :
    (TDA.Probability.iidMeasure μ n :
        MeasureTheory.Measure (Fin n → EuclideanSpace ℝ (Fin d)))
      {t | ENNReal.ofReal (2 * r) <
        (TDA.Persistence.Rips.qTameSampleDiagramOrderFree k t degree).bottleneck
          (TDA.Persistence.Rips.qTameCompactCarrierDiagramOrderFree k
            (μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))).support hK degree)} ≤
      (Fintype.card C : ENNReal) *
        (1 - TDA.Probability.finiteCoverMass μ
          (fun j => Metric.ball (c j : EuclideanSpace ℝ (Fin d)) (r / 2))) ^ n :=
  TDA.Persistence.Rips.measure_bottleneck_qTameSampleDiagramOrderFree_support_gt_le
    μ k hK hn degree c hr hnet

/-- The event of the bound is measurable. -/
theorem euclidean_support_event_measurable {d n : ℕ}
    (μ : MeasureTheory.ProbabilityMeasure (EuclideanSpace ℝ (Fin d))) (k : Type) [Field k]
    (hK : IsCompact (μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))).support)
    (hn : 0 < n) (degree : ℕ) (a : ENNReal) :
    MeasurableSet {t : Fin n → EuclideanSpace ℝ (Fin d) |
      a < (TDA.Persistence.Rips.qTameSampleDiagramOrderFree k t degree).bottleneck
        (TDA.Persistence.Rips.qTameCompactCarrierDiagramOrderFree k
          (μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))).support hK degree)} :=
  TDA.Persistence.Rips.measurableSet_bottleneck_qTameSampleDiagramOrderFree_support_gt
    μ k hK hn degree a

/-- The confidence bound on a compact metric space, against the diagram of the space. -/
theorem compact_space_confidence {X : Type} [MetricSpace X] [CompactSpace X] [Nonempty X]
    [MeasurableSpace X] [BorelSpace X] {n : ℕ}
    (μ : MeasureTheory.ProbabilityMeasure X) (k : Type) [Field k] (hn : 0 < n) (degree : ℕ)
    {C : Type} [Fintype C] [Nonempty C] (c : C → X) {r : ℝ} (hr : 0 < r)
    (hnet : ∀ x, ∃ j, dist x (c j) < r / 2) :
    (TDA.Probability.iidMeasure μ n : MeasureTheory.Measure (Fin n → X))
      {t | ENNReal.ofReal (2 * r) <
        (TDA.Persistence.Rips.qTameSampleDiagramOrderFree k t degree).bottleneck
          (TDA.Persistence.Rips.qTameLocallyFiniteDiagramOrderFree X k
            isCompact_univ.totallyBounded degree)} ≤
      (Fintype.card C : ENNReal) *
        (1 - TDA.Probability.finiteCoverMass μ (fun j => Metric.ball (c j) (r / 2))) ^ n :=
  TDA.Persistence.Rips.measure_bottleneck_qTameSampleDiagramOrderFree_gt_le
    μ k isCompact_univ.totallyBounded hn degree c hr hnet

/-- With an order on the ambient space, the order-free sample diagram is the ordered one. -/
theorem sampleDiagram_orderFree_eq {X : Type} [MetricSpace X] [LinearOrder X] {n : ℕ}
    (k : Type) [Field k] (t : Fin n → X) (degree : ℕ) :
    TDA.Persistence.Rips.qTameSampleDiagramOrderFree k t degree =
      TDA.Persistence.Rips.qTameSampleDiagram k t degree :=
  TDA.Persistence.Rips.qTameSampleDiagramOrderFree_eq k t degree

end TDA.Persistence.RipsConfidenceClientExamples
