import TDA.Persistence.DiagramBottleneckLaws
import TDA.Persistence.RipsSampleQuotient

/-!
# Client statements of the matching cost bounds and the tuple filtration

Regression fixtures for #1286, family 12 of the downstream-use audit (#1207). Each statement is
written as a downstream client writes it: the file opens no scope and declares no instance, and
the conditions `if ∃ i, M.finite i = some j` and the finite images `Finset.image` are elaborated
with the decidability of the client's own types; every proof is a direct application of a library
theorem.

* A matching between index types `Fin 2`: an unmatched target costs at most the matching cost,
  and the matching cost is at most `r` once the matched, unmatched and essential costs are.
* The faces of the Rips filtration of a tuple of points: a face of the tuple-index complex
  exists exactly when its image in the metric sample is a face of the Rips filtration, for a
  decidable equality on the sample.
-/

namespace TDA.Persistence.OccurrenceMatchingClientExamples

open scoped ENNReal

section Matching

variable (M : OccurrenceMatching (Fin 2) (Fin 2) (Fin 2) (Fin 2))
  (x y : Fin 2 → ℝ × ℝ) (b c : Fin 2 → ℝ)

/-- An unmatched target costs at most the matching cost. -/
theorem fin_two_target_le_cost (j : Fin 2) :
    (if ∃ i, M.finite i = some j then 0 else diagonalCost (y j)) ≤ M.cost x y b c :=
  OccurrenceMatching.target_le_cost_decidable M x y b c j

/-- The matching cost is at most `r` once every matched, unmatched and essential cost is. -/
theorem fin_two_cost_le_of (r : ℝ≥0∞)
    (hm : ∀ i j, M.finite i = some j → finitePairCost (x i) (y j) ≤ r)
    (hn : ∀ i, M.finite i = none → diagonalCost (x i) ≤ r)
    (ht : ∀ j, (if ∃ i, M.finite i = some j then 0 else diagonalCost (y j)) ≤ r)
    (he : ∀ k, essentialPairCost (b k) (c (M.essential k)) ≤ r) :
    M.cost x y b c ≤ r :=
  OccurrenceMatching.cost_le_of_decidable M x y b c r
    (fun i => by
      cases h : M.finite i with
      | none => exact hn i h
      | some j => exact hm i j h)
    ht he

end Matching

section Rips

variable {X : Type*} [MetricSpace X] {n : ℕ} (t : Fin n → X)
  [DecidableEq (TDA.Persistence.Rips.Sample t)]

/-- A tuple-index face and its image in the metric sample. -/
theorem mem_tupleFilter_iff (r : ℝ) (σ : Finset (TDA.Persistence.Rips.TupleVertex t)) :
    σ ∈ (TDA.Persistence.Rips.tupleFilter t).sublevel r ↔
      σ.Nonempty ∧ σ.image (TDA.Persistence.Rips.tupleProjection t) ∈
        (TDA.Filtration.Rips.filter
          (inferInstance : MetricSpace (TDA.Persistence.Rips.Sample t))).sublevel r :=
  TDA.Persistence.Rips.mem_tupleFilter_iff t r σ

end Rips

end TDA.Persistence.OccurrenceMatchingClientExamples
