import TDA.Persistence.FinitePCostContinuity

/-!
# Joint continuity of finite matching costs

The exponent and both labelled coordinate families vary in the ordinary product
and function-space topologies. Geometric coefficients are continuous real
functions. Joint continuity of real powers at positive exponents includes zero
coefficients, so every fixed matching has a continuous powered cost. The optimum is its finite nonempty minimum, even when the minimizing matching changes.

Positive reciprocal powers include zero minima. The existing assignment
equalities transfer both conclusions to the infimum over every feasible real
reservoir matrix. Public statements use p ≥ 1, fixed maximum ground norm and unit
occurrences. Label types stay fixed; raw diagonal crossings are included in the
algebra, while the persistence-diagram interpretation requires positive lifetimes.
-/

noncomputable section
namespace TDA.Persistence
open scoped Classical

private abbrev JointCostInput (I J : Type*) := ℝ × ((I → ℝ × ℝ) × (J → ℝ × ℝ))

-- Rewrite the finite geometric coefficients to real formulas, avoiding toReal at infinity.
private theorem pairCoefficient_continuous {α : Type*} [TopologicalSpace α]
    {f g : α → ℝ × ℝ} (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun a => (finitePairCost (f a) (g a)).toReal) := by
  have he (x y : ℝ × ℝ) : (finitePairCost x y).toReal =
      max |x.1 - y.1| |x.2 - y.2| :=
    ENNReal.toReal_ofReal ((abs_nonneg _).trans (le_max_left _ _))
  simpa only [he, Pi.sub_apply] using (hf.fst.sub hg.fst).abs.max (hf.snd.sub hg.snd).abs

private theorem diagonalCoefficient_continuous {α : Type*} [TopologicalSpace α]
    {f : α → ℝ × ℝ} (hf : Continuous f) :
    Continuous (fun a => (diagonalCost (f a)).toReal) := by
  have he (x : ℝ × ℝ) : (diagonalCost x).toReal = |x.2 - x.1| / 2 :=
    ENNReal.toReal_ofReal (div_nonneg (abs_nonneg _) (by norm_num))
  simpa only [he, Pi.sub_apply] using (hf.snd.sub hf.fst).abs.div_const (2 : ℝ)

namespace OccurrenceMatching
variable {I J : Type*} [Fintype I] [Fintype J]

private theorem totalFinitePowerCost_joint_continuousAt_pos
    (M : OccurrenceMatching I J PEmpty.{1} PEmpty.{1}) {z : JointCostInput I J}
    (hp : 0 < z.1) :
    ContinuousAt (fun w : JointCostInput I J =>
      M.totalFinitePowerCost w.1 w.2.1 w.2.2) z := by
  unfold totalFinitePowerCost totalBoundaryCost
  apply ContinuousAt.add
  · apply tendsto_finsetSum
    intro i _
    have hx : Continuous (fun w : JointCostInput I J => w.2.1 i) :=
      (continuous_apply i).comp continuous_snd.fst
    cases M.finite i with
    | none =>
      exact (diagonalCoefficient_continuous hx).continuousAt.rpow
        continuous_fst.continuousAt (Or.inr hp)
    | some j =>
      have hy : Continuous (fun w : JointCostInput I J => w.2.2 j) :=
        (continuous_apply j).comp continuous_snd.snd
      exact (pairCoefficient_continuous hx hy).continuousAt.rpow
        continuous_fst.continuousAt (Or.inr hp)
  · apply tendsto_finsetSum
    intro j _
    by_cases hj : ∃ i, M.finite i = some j
    · simpa only [if_pos hj] using
        (continuousAt_const : ContinuousAt (fun _ : JointCostInput I J => (0 : ℝ)) z).tendsto
    · have hy : Continuous (fun w : JointCostInput I J => w.2.2 j) :=
        (continuous_apply j).comp continuous_snd.snd
      simpa only [if_neg hj] using
        ((diagonalCoefficient_continuous hy).continuousAt.rpow
          continuous_fst.continuousAt (Or.inr hp)).tendsto

end OccurrenceMatching
variable {I J : Type*} [Fintype I] [Fintype J]

-- The matching family is fixed and finite while coordinates and the exponent move together.
private theorem finitePowerMatchingCost_joint_continuousAt_pos
    {z : JointCostInput I J} (hp : 0 < z.1) :
    ContinuousAt (fun w : JointCostInput I J =>
      finitePowerMatchingCost w.1 w.2.1 w.2.2) z := by
  let : Nonempty (OccurrenceMatching I J PEmpty.{1} PEmpty.{1}) :=
    occurrenceMatching_nonempty_iff.mpr (by simp)
  have h : ContinuousAt (fun w : JointCostInput I J =>
      Finset.univ.inf' Finset.univ_nonempty
        (fun M : OccurrenceMatching I J PEmpty.{1} PEmpty.{1} =>
          M.totalFinitePowerCost w.1 w.2.1 w.2.2)) z :=
    ContinuousAt.finset_inf'_apply Finset.univ_nonempty
      (fun M _ => M.totalFinitePowerCost_joint_continuousAt_pos hp)
  simpa only [Finset.inf'_univ_eq_ciInf, finitePowerMatchingCost] using h

private theorem finitePMatchingCost_joint_continuousAt_pos
    {z : JointCostInput I J} (hp : 0 < z.1) :
    ContinuousAt (fun w : JointCostInput I J =>
      finitePMatchingCost w.1 w.2.1 w.2.2) z := by
  exact (finitePowerMatchingCost_joint_continuousAt_pos hp).rpow
    (continuous_fst.continuousAt.inv₀ hp.ne') (Or.inr (inv_pos.mpr hp))

/-- Joint continuity in the exponent and both finite coordinate families on p ≥ 1. -/
theorem finitePowerMatchingCost_joint_continuousOn :
    ContinuousOn (fun z : ℝ × ((I → ℝ × ℝ) × (J → ℝ × ℝ)) =>
      finitePowerMatchingCost z.1 z.2.1 z.2.2) {z | 1 ≤ z.1} := by
  intro z hz
  exact (finitePowerMatchingCost_joint_continuousAt_pos
    (lt_of_lt_of_le zero_lt_one hz)).continuousWithinAt

/-- Joint continuity of the rooted optimum, including nonempty zero-cost inputs. -/
theorem finitePMatchingCost_joint_continuousOn :
    ContinuousOn (fun z : ℝ × ((I → ℝ × ℝ) × (J → ℝ × ℝ)) =>
      finitePMatchingCost z.1 z.2.1 z.2.2) {z | 1 ≤ z.1} := by
  intro z hz
  exact (finitePMatchingCost_joint_continuousAt_pos
    (lt_of_lt_of_le zero_lt_one hz)).continuousWithinAt

/-- Joint continuity of the powered infimum over all feasible real reservoir plans. -/
theorem finitePowerBoundaryTransportCost_joint_continuousOn :
    ContinuousOn (fun z : ℝ × ((I → ℝ × ℝ) × (J → ℝ × ℝ)) =>
      finitePowerBoundaryTransportCost z.1 z.2.1 z.2.2) {z | 1 ≤ z.1} := by
  simpa only [finitePowerBoundaryTransportCost_eq_matchingCost] using
    (finitePowerMatchingCost_joint_continuousOn (I := I) (J := J))

/-- Joint continuity of the rooted real-plan optimum on the PH exponent domain. -/
theorem finitePBoundaryTransportCost_joint_continuousOn :
    ContinuousOn (fun z : ℝ × ((I → ℝ × ℝ) × (J → ℝ × ℝ)) =>
      finitePBoundaryTransportCost z.1 z.2.1 z.2.2) {z | 1 ≤ z.1} := by
  simpa only [finitePBoundaryTransportCost_eq_matchingCost] using
    (finitePMatchingCost_joint_continuousOn (I := I) (J := J))

end TDA.Persistence
