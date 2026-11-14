import Mathlib.MeasureTheory.Measure.FiniteMeasurePi

/-!
# Frozen Comparator reference for the bounded pilot (Issue #855)

Independently restates, under the same fully qualified names and the same literal universe
names as the production module `TDA.Probability.SamplingCoverage`, the full statement closure
of the one frozen target `TDA.Probability.measure_missedCover_le_card_mul`: the `missedCover`
event, the `iidMeasure` iid product law, and the theorem itself. Written from the source digest
`docs/math/rips-sampling-confidence.md` ([Fasy et al., Lemma 4](https://arxiv.org/html/1303.7117v3))
and PR #766's independent source ↔ Lean review of the production statement — never regenerated
from the candidate solution module. This module imports mathlib only; it must never import
`TDA` (enforced by `scripts/check-comparator.sh`'s import-boundary check).

The reference proof is a single `sorry`, never relied upon: Comparator judges the production
solution's proof against `scripts/check.sh`'s existing gates, not this reference's.
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

/-- The law of an ordered iid tuple drawn with replacement. -/
def iidMeasure (μ : ProbabilityMeasure X) (n : ℕ) : ProbabilityMeasure (Fin n → X) :=
  ProbabilityMeasure.pi (fun _ : Fin n => μ)

/-- A common lower mass gives the cardinality form of the finite iid coverage bound: the
probability that an `n`-sample iid tuple fails to hit at least one member of a finite cover
(the `missedCover` event) is at most the number of cover members times `(1 - β)^n`, for any
common lower bound `β` on their masses. Truncated subtraction is in `ℝ≥0∞`. -/
theorem measure_missedCover_le_card_mul [Fintype C] (μ : ProbabilityMeasure X)
    (n : ℕ) (A : C → Set X) (hA : ∀ c, MeasurableSet (A c)) (β : ℝ≥0∞)
    (hβ : ∀ c, β ≤ (μ : Measure X) (A c)) :
    (iidMeasure μ n : Measure (Fin n → X)) (missedCover n A) ≤
      (Fintype.card C : ℝ≥0∞) * (1 - β)^n := by
  sorry -- ALLOW_SORRY: #855

end TDA.Probability
