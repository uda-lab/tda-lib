import TDA.Persistence.FinitePBoundaryTransport
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.Topology.Order.Lattice

/-!
# Continuity in the finite matching exponent

The actual powered matching optimum is a minimum over a finite nonempty family.
Each candidate is continuous at positive exponents, including zero charges, so
the minimum stays continuous when its optimizer changes. Taking the reciprocal
power preserves continuity even at a zero minimum, since the exponent is positive.
The proved assignment equalities transfer both results to the actual real-plan
optima, whose transported and residual masses remain linear.

The public domain is `p ≥ 1`, with fixed maximum ground norm and labelled unit
occurrences. Empty families and zero distances are included. The supporting
raw-pair algebra is not a weighted, essential or all-Radon transport theorem.
-/

noncomputable section
namespace TDA.Persistence
open scoped Classical

namespace OccurrenceMatching
variable {I J : Type*} [Fintype I] [Fintype J]

-- Branch choices depend on the matching, while only the geometric powers vary.
private theorem totalFinitePowerCost_continuousAt_pos
    (M : OccurrenceMatching I J PEmpty.{1} PEmpty.{1}) {p : ℝ} (hp : 0 < p)
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    ContinuousAt (fun q : ℝ => M.totalFinitePowerCost q x y) p := by
  unfold totalFinitePowerCost totalBoundaryCost
  apply ContinuousAt.add
  · apply tendsto_finsetSum
    intro i _
    cases M.finite i <;> exact Real.continuousAt_const_rpow' hp.ne'
  · apply tendsto_finsetSum
    intro j _
    by_cases hj : ∃ i, M.finite i = some j
    · simpa only [if_pos hj] using
        (continuousAt_const : ContinuousAt (fun _ : ℝ => (0 : ℝ)) p).tendsto
    · simpa only [if_neg hj] using
        (Real.continuousAt_const_rpow' hp.ne' :
          ContinuousAt (fun q : ℝ => (diagonalCost (y j)).toReal ^ q) p).tendsto

end OccurrenceMatching
variable {I J : Type*} [Fintype I] [Fintype J]

-- Finiteness is essential: arbitrary infima of continuous functions need not be continuous.
private theorem finitePowerMatchingCost_continuousAt_pos {p : ℝ} (hp : 0 < p)
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    ContinuousAt (fun q : ℝ => finitePowerMatchingCost q x y) p := by
  let : Nonempty (OccurrenceMatching I J PEmpty.{1} PEmpty.{1}) :=
    occurrenceMatching_nonempty_iff.mpr (by simp)
  have h : ContinuousAt (fun q : ℝ => Finset.univ.inf' Finset.univ_nonempty
      (fun M : OccurrenceMatching I J PEmpty.{1} PEmpty.{1} =>
        M.totalFinitePowerCost q x y)) p :=
    ContinuousAt.finset_inf'_apply Finset.univ_nonempty
      (fun M _ => M.totalFinitePowerCost_continuousAt_pos hp x y)
  simpa only [Finset.inf'_univ_eq_ciInf, finitePowerMatchingCost] using h

private theorem finitePMatchingCost_continuousAt_pos {p : ℝ} (hp : 0 < p)
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    ContinuousAt (fun q : ℝ => finitePMatchingCost q x y) p := by
  exact (finitePowerMatchingCost_continuousAt_pos hp x y).rpow
    (continuousAt_id.inv₀ hp.ne') (Or.inr (inv_pos.mpr hp))

/-- The finite powered minimum is continuous in the real exponent on the PD domain. -/
theorem finitePowerMatchingCost_continuousOn (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    ContinuousOn (fun p : ℝ => finitePowerMatchingCost p x y) (Set.Ici 1) := by
  intro p hp
  exact (finitePowerMatchingCost_continuousAt_pos
    (lt_of_lt_of_le zero_lt_one hp) x y).continuousWithinAt

/-- Rooting preserves exponent continuity even when the optimized cost is zero. -/
theorem finitePMatchingCost_continuousOn (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    ContinuousOn (fun p : ℝ => finitePMatchingCost p x y) (Set.Ici 1) := by
  intro p hp
  exact (finitePMatchingCost_continuousAt_pos
    (lt_of_lt_of_le zero_lt_one hp) x y).continuousWithinAt

/-- Continuity of the powered infimum over all feasible real reservoir matrices. -/
theorem finitePowerBoundaryTransportCost_continuousOn
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    ContinuousOn (fun p : ℝ => finitePowerBoundaryTransportCost p x y) (Set.Ici 1) := by
  simpa only [finitePowerBoundaryTransportCost_eq_matchingCost] using
    finitePowerMatchingCost_continuousOn x y

/-- Continuity of the actual rooted real-plan optimum, including empty and zero-cost inputs. -/
theorem finitePBoundaryTransportCost_continuousOn
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    ContinuousOn (fun p : ℝ => finitePBoundaryTransportCost p x y) (Set.Ici 1) := by
  simpa only [finitePBoundaryTransportCost_eq_matchingCost] using
    finitePMatchingCost_continuousOn x y

end TDA.Persistence
