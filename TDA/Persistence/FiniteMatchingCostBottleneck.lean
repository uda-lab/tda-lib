import TDA.Persistence.FiniteMatchingCost
import TDA.Persistence.DiagramBottleneckLaws

/-!
# Finite matching sums bounded by bottleneck maxima

Each finite source and unmatched target contributes at most the full matching's
maximum cost. There are at most the sum of the two finite occurrence counts such
charges. Essential occurrences remain separate in the original matching; its finite
restriction preserves every finite charge and makes no finite/essential cross-match.
-/

namespace TDA.Persistence

namespace OccurrenceMatching

variable {I J E F : Type*} [Fintype I] [Fintype J] [Fintype E] [Fintype F]

/-- Retain the finite partial injection and discard the separate essential bijection.
The matching type already excludes finite/essential cross-matches. -/
def finiteRestriction (M : OccurrenceMatching I J E F) :
    OccurrenceMatching I J PEmpty.{1} PEmpty.{1} where
  finite := M.finite
  finite_injective := M.finite_injective
  essential := Equiv.refl _

/-- A finite sum of matching charges is bounded by their number times the full maximum.
The full cost is finite by `occurrenceMatching_cost_lt_top`, even with essential bars. -/
theorem totalFiniteCost_finiteRestriction_le_card_mul_cost
    (M : OccurrenceMatching I J E F) (x : I → ℝ × ℝ) (y : J → ℝ × ℝ)
    (b : E → ℝ) (c : F → ℝ) :
    M.finiteRestriction.totalFiniteCost x y ≤
      ((Fintype.card I + Fintype.card J : ℕ) : ℝ) * (M.cost x y b c).toReal := by
  classical
  have hfinite := (occurrenceMatching_cost_lt_top x y b c M).ne
  have hs (i : I) :
      (match M.finite i with
        | some j => (finitePairCost (x i) (y j)).toReal
        | none => (diagonalCost (x i)).toReal) ≤ (M.cost x y b c).toReal := by
    have h := ENNReal.toReal_mono hfinite (M.source_le_cost x y b c i)
    cases hi : M.finite i <;> simpa only [hi] using h
  have ht (j : J) :
      (if ∃ i, M.finite i = some j then 0 else (diagonalCost (y j)).toReal) ≤
        (M.cost x y b c).toReal := by
    have h := ENNReal.toReal_mono hfinite (M.target_le_cost x y b c j)
    split_ifs with hj <;> simpa only [hj, if_true, if_false, ENNReal.toReal_zero] using h
  unfold totalFiniteCost
  change (∑ i, _) + (∑ j, _) ≤ _
  calc
    _ ≤ (∑ _i : I, (M.cost x y b c).toReal) +
        ∑ _j : J, (M.cost x y b c).toReal :=
      add_le_add (Finset.sum_le_sum (fun i _ => hs i))
        (Finset.sum_le_sum (fun j _ => ht j))
    _ = _ := by simp [Nat.cast_add, add_mul]

end OccurrenceMatching

/-- Compare the finite first-order minimum with a finite full bottleneck distance.
Essential counts may be nonzero; finiteness supplies the optimal full matching.
The hypothesis prevents the invalid conversion `ENNReal.toReal ⊤ = 0`. -/
theorem finiteFirstOrderMatchingCost_le_card_mul_bottleneck
    (D E : Diagram ℝ) (hfinite : bottleneck D E < ⊤) :
    finiteFirstOrderMatchingCost (fun p : D.finiteOccurrences => p.1)
        (fun p : E.finiteOccurrences => p.1) ≤
      ((Fintype.card D.finiteOccurrences + Fintype.card E.finiteOccurrences : ℕ) : ℝ) *
        (bottleneck D E).toReal := by
  obtain ⟨M, hM⟩ := (bottleneck_optimal_iff D E).mpr
    ((bottleneck_lt_top_iff D E).mp hfinite)
  calc
    _ ≤ M.finiteRestriction.totalFiniteCost _ _ :=
      finiteFirstOrderMatchingCost_le_totalFiniteCost _ _ M.finiteRestriction
    _ ≤ _ := by
      simpa only [hM] using M.totalFiniteCost_finiteRestriction_le_card_mul_cost
        (fun p => p.1) (fun p => p.1) (fun b => b.1) (fun b => b.1)

end TDA.Persistence
