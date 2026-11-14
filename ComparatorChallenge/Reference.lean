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

The reference carries its own proof (same argument as the production module: exact avoidance
probability of one measurable set under the iid product law, a finite union bound, then the
common-mass bound) so that it contains no `sorry`; what is frozen and independently reviewed
is the statement and the two definitions, not the proof. Comparator judges only the production
solution's proof against `scripts/check.sh`'s existing gates, never this reference's. The two
intermediate steps (`measure_iid_no_hit`, `measure_missedCover_le_sum`) are `private`: Lean
mangles a private declaration's name with its declaring module's path, so they never surface
as `TDA.Probability.*` names and never enter the target's statement closure.
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

/-- The exact probability that all iid coordinates avoid a measurable set. -/
private theorem measure_iid_no_hit (μ : ProbabilityMeasure X) (n : ℕ) (A : Set X)
    (hA : MeasurableSet A) :
    (iidMeasure μ n : Measure (Fin n → X)) {t | ∀ i, t i ∉ A} =
      (1 - (μ : Measure X) A)^n := by
  have heq : {t : Fin n → X | ∀ i, t i ∉ A} = Set.pi Set.univ (fun _ => Aᶜ) := by
    ext t
    simp
  rw [heq, iidMeasure, ProbabilityMeasure.toMeasure_pi, Measure.pi_pi]
  simp [prob_compl_eq_one_sub hA]

/-- A finite union bound by the exact probabilities of missing individual members. -/
private theorem measure_missedCover_le_sum [Fintype C] (μ : ProbabilityMeasure X)
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

/-- A common lower mass gives the cardinality form of the finite iid coverage bound: the
probability that an `n`-sample iid tuple fails to hit at least one member of a finite cover
(the `missedCover` event) is at most the number of cover members times `(1 - β)^n`, for any
common lower bound `β` on their masses. Truncated subtraction is in `ℝ≥0∞`. -/
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

end TDA.Probability
