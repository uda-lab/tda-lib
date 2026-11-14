import TDA.Persistence.RipsSamplingConfidence
import Mathlib.MeasureTheory.Constructions.UnitInterval
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Order.Interval.Set.Infinite

/-!
# Examples of Rips sampling confidence

The unit interval carries its ordinary Lebesgue probability measure. In
particular, the confidence examples include an infinite compact carrier.
-/

noncomputable section

universe w

namespace TDA.Persistence.Rips.ConfidenceExamples

open MeasureTheory TDA.Probability
open scoped unitInterval ENNReal

/-- Uniform probability on the infinite compact unit interval. -/
def unitIntervalLaw : ProbabilityMeasure I := ⟨volume, inferInstance⟩

/-- Every relatively open nonempty subset of the unit interval has positive
Lebesgue mass, including neighborhoods of its endpoints. -/
theorem unitIntervalLaw_isOpenPosMeasure :
    (unitIntervalLaw : Measure I).IsOpenPosMeasure := by
  constructor
  intro U hU hne
  obtain ⟨a, b, hab, hsub⟩ := hU.exists_Ioo_subset hne
  apply ne_of_gt
  calc
    0 < volume (Set.Ioo a b) := by
      rw [unitInterval.volume_Ioo]
      exact ENNReal.ofReal_pos.mpr (sub_pos.mpr hab)
    _ ≤ (unitIntervalLaw : Measure I) U := measure_mono hsub

/-- The uniform interval law has full support. -/
theorem unitIntervalLaw_support :
    (unitIntervalLaw : Measure I).support = Set.univ := by
  let := unitIntervalLaw_isOpenPosMeasure
  exact Measure.support_eq_univ

/-- The example's carrier has infinitely many points. -/
theorem unitInterval_infinite : Infinite I :=
  Set.Icc.infinite (by norm_num : (0 : ℝ) < 1)

/-- Nine equally spaced centers in the unit interval. -/
def intervalGrid (i : Fin 9) : I :=
  ⟨(i : ℝ) / 8, by
    constructor
    · positivity
    · have hi : (i : ℝ) ≤ 8 := by exact_mod_cast (by omega : (i : ℕ) ≤ 8)
      linarith⟩

private theorem intervalGrid_net (x : I) :
    ∃ i, dist x (intervalGrid i) < (3 / 16 : ℝ) / 2 := by
  have hx0 := x.property.1
  have hx1 := x.property.2
  by_cases h1 : (x : ℝ) < 1 / 16
  · refine ⟨0, ?_⟩
    simp only [Subtype.dist_eq, Real.dist_eq, intervalGrid, Fin.val_zero, Nat.cast_zero]
    change |(x : ℝ) - 0 / 8| < (3 / 16 : ℝ) / 2
    rw [abs_lt]
    constructor <;> linarith
  by_cases h2 : (x : ℝ) < 3 / 16
  · refine ⟨1, ?_⟩
    simp only [Subtype.dist_eq, Real.dist_eq, intervalGrid, Fin.val_one, Nat.cast_one]
    change |(x : ℝ) - 1 / 8| < (3 / 16 : ℝ) / 2
    rw [abs_lt]
    constructor <;> linarith
  by_cases h3 : (x : ℝ) < 5 / 16
  · refine ⟨2, ?_⟩
    change |(x : ℝ) - 2 / 8| < (3 / 16 : ℝ) / 2
    rw [abs_lt]
    constructor <;> linarith
  by_cases h4 : (x : ℝ) < 7 / 16
  · refine ⟨3, ?_⟩
    change |(x : ℝ) - 3 / 8| < (3 / 16 : ℝ) / 2
    rw [abs_lt]
    constructor <;> linarith
  by_cases h5 : (x : ℝ) < 9 / 16
  · refine ⟨4, ?_⟩
    change |(x : ℝ) - 4 / 8| < (3 / 16 : ℝ) / 2
    rw [abs_lt]
    constructor <;> linarith
  by_cases h6 : (x : ℝ) < 11 / 16
  · refine ⟨5, ?_⟩
    change |(x : ℝ) - 5 / 8| < (3 / 16 : ℝ) / 2
    rw [abs_lt]
    constructor <;> linarith
  by_cases h7 : (x : ℝ) < 13 / 16
  · refine ⟨6, ?_⟩
    change |(x : ℝ) - 6 / 8| < (3 / 16 : ℝ) / 2
    rw [abs_lt]
    constructor <;> linarith
  by_cases h8 : (x : ℝ) < 15 / 16
  · refine ⟨7, ?_⟩
    change |(x : ℝ) - 7 / 8| < (3 / 16 : ℝ) / 2
    rw [abs_lt]
    constructor <;> linarith
  · refine ⟨8, ?_⟩
    change |(x : ℝ) - 8 / 8| < (3 / 16 : ℝ) / 2
    rw [abs_lt]
    constructor <;> linarith

/-- The actual minimum mass of the nine radius-`3/32` net balls. -/
def intervalGridMass : ℝ≥0∞ :=
  finiteCoverMass unitIntervalLaw (fun i => Metric.ball (intervalGrid i) ((3 / 16 : ℝ) / 2))

/-- The explicit interval net has a strictly positive minimum ball mass. -/
theorem intervalGridMass_pos : 0 < intervalGridMass := by
  let := unitIntervalLaw_isOpenPosMeasure
  exact finiteCoverMass_ball_pos unitIntervalLaw intervalGrid (by norm_num : (0 : ℝ) < 3 / 16)

/-- The minimum ball mass is a probability, bounded above by one. -/
theorem intervalGridMass_le_one : intervalGridMass ≤ 1 :=
  finiteCoverMass_le_one unitIntervalLaw _

/-- A concrete infinite compact probability carrier satisfies the actual
canonical q-tame diagram confidence bound in every degree and coefficient field. -/
theorem unitInterval_confidence (k : Type w) [Field k] {n : ℕ} (hn : 0 < n)
    (degree : ℕ) :
    (iidMeasure unitIntervalLaw n : Measure (Fin n → I))
      {t | (3 / 8 : ℝ≥0∞) < (qTameSampleDiagram k t degree).bottleneck
        (qTameLocallyFiniteDiagram (X := I) k isCompact_univ.totallyBounded degree)} ≤
      9 * (1 - intervalGridMass)^n := by
  simpa only [Fintype.card_fin, Nat.cast_ofNat, intervalGridMass,
      show ENNReal.ofReal (2 * (3 / 16 : ℝ)) =
      (3 / 8 : ℝ≥0∞) by norm_num [ENNReal.ofReal_div_of_pos]] using
    measure_bottleneck_qTameSampleDiagram_gt_le unitIntervalLaw k
      isCompact_univ.totallyBounded hn degree intervalGrid
      (by norm_num : (0 : ℝ) < 3 / 16) intervalGrid_net

/-- One draw is permitted by the genuine diagram confidence theorem. -/
theorem unitInterval_one_draw_confidence (k : Type w) [Field k] (degree : ℕ) :
    (iidMeasure unitIntervalLaw 1 : Measure (Fin 1 → I))
      {t | (3 / 8 : ℝ≥0∞) < (qTameSampleDiagram k t degree).bottleneck
        (qTameLocallyFiniteDiagram (X := I) k isCompact_univ.totallyBounded degree)} ≤
      9 * (1 - intervalGridMass) := by
  simpa using unitInterval_confidence k (by decide : 0 < 1) degree

/-- Three duplicate draws have exactly the one-draw canonical diagram. -/
theorem repeatedDraws_qTameSampleDiagram (k : Type w) [Field k] (x : I) (degree : ℕ) :
    qTameSampleDiagram k (fun _ : Fin 3 => x) degree =
      qTameSampleDiagram k (fun _ : Fin 1 => x) degree := by
  apply qTameSampleDiagram_eq_of_range_eq
  simp

/-- Probability concentrated on the singleton metric carrier. -/
def singletonLaw : ProbabilityMeasure PUnit.{1} := ⟨Measure.dirac PUnit.unit, inferInstance⟩

/-- In a singleton carrier every positive-radius net ball has mass `β = 1`. -/
theorem singleton_finiteCoverMass_eq_one {r : ℝ} (hr : 0 < r) :
    finiteCoverMass singletonLaw (fun _ : Fin 1 => Metric.ball PUnit.unit (r / 2)) = 1 := by
  have hball : Metric.ball PUnit.unit (r / 2) = (Set.univ : Set PUnit.{1}) := by
    ext x
    simp only [Metric.mem_ball, dist_self, Set.mem_univ, iff_true]
    linarith
  simp only [hball]
  simp [finiteCoverMass]

/-- The `β = 1` boundary gives zero actual diagram failure probability for
every nonempty sample, including one draw and tuples of repeated draws. -/
theorem singleton_confidence_zero (k : Type w) [Field k] {n : ℕ} (hn : 0 < n)
    (degree : ℕ) {r : ℝ} (hr : 0 < r) :
    (iidMeasure singletonLaw n : Measure (Fin n → PUnit.{1}))
      {t | ENNReal.ofReal (2 * r) < (qTameSampleDiagram k t degree).bottleneck
        (qTameLocallyFiniteDiagram (X := PUnit.{1}) k
          isCompact_univ.totallyBounded degree)} = 0 := by
  apply le_antisymm _ bot_le
  have h := measure_bottleneck_qTameSampleDiagram_gt_le singletonLaw k
    isCompact_univ.totallyBounded hn degree (fun _ : Fin 1 => PUnit.unit) hr
    (fun x => ⟨0, by simpa using (half_pos hr)⟩)
  simpa [singleton_finiteCoverMass_eq_one hr, Nat.ne_of_gt hn] using h

end TDA.Persistence.Rips.ConfidenceExamples
