import TDA.Persistence.Morse.FiniteInputMatchingGeneration
import TDA.Persistence.Morse.FiniteInputMatchingExamples

/-!
# Fixtures for the greedy matching generator

Outputs of `TDA.Persistence.Morse.MatchingInput.generate` on the inputs `empty`, `path`,
`pathStep`, `circle`, `filled` and `square` of `FiniteInputMatchingExamples`. Vertices `{0}`,
`{1}`, … are written A, B, …. Every closed computation is a kernel `decide`; the two
rejection fixtures that quantify over all ranks reuse `cyclic_no_certificate` or combine six
`decide` steps with `omega`.

Inside `TDA.Persistence.Morse`, the bare name `IsMatching` denotes the semantic predicate, so
the list-level one is written `MatchingInput.IsMatching`.

The rejection fixtures concern specific candidates only; no general claim that a rejected
candidate reuses a face or closes a cycle is made.
-/

set_option autoImplicit false

namespace TDA.Persistence.Morse.FiniteInputMatchingGenerationExamples

open TDA.Simplicial TDA.Filtration TDA.Persistence.Reduction FiniteInput
open TDA.Persistence.Morse.MatchingInput
open TDA.Persistence.Morse.FiniteInputMatchingExamples (empty path pathStep circle filled square)

/-- A position pair whose bounds are discharged by `decide`. -/
private def pr {xs : Input} (i j : ℕ) (hi : i < xs.length := by decide)
    (hj : j < xs.length := by decide) : Fin xs.length × Fin xs.length := (⟨i, hi⟩, ⟨j, hj⟩)

/-! ## Generated matchings and their critical reports -/

/-- On the empty input, nothing is generated and nothing is critical. -/
theorem empty_generate :
    (generate empty).pairs = [] ∧ (generate empty).criticalReport = [] := by
  decide +kernel

/-- On the path, the pass matches (A, AB) and (B, BC). -/
theorem path_generate_pairs : (generate path).pairs = [pr 0 3, pr 1 4] := by decide +kernel

/-- On the path, only C remains critical: the tree reduces to one vertex. -/
theorem path_generate_report :
    (generate path).criticalReport = [(⟨2, by decide⟩, 0, 0)] := by
  decide +kernel

/-- On `pathStep`, the pass matches (A, AB) only. -/
theorem pathStep_generate_pairs : (generate pathStep).pairs = [pr 0 3] := by decide +kernel

/-- On `pathStep`, B, C and BC remain critical. -/
theorem pathStep_generate_report :
    (generate pathStep).criticalReport =
      [(⟨1, by decide⟩, 0, 0), (⟨2, by decide⟩, 0, 0), (⟨4, by decide⟩, 1, 1)] := by
  decide +kernel

/-- The filtration barrier: (B, BC) is a cover pair matched on the constant-grade path, but on
`pathStep` its grades differ and it is not a candidate. -/
theorem pathStep_barrier :
    IsCover pathStep ⟨1, by decide⟩ ⟨4, by decide⟩ ∧
      (pathStep.get ⟨1, by decide⟩).2 ≠ (pathStep.get ⟨4, by decide⟩).2 ∧
      pr 1 4 ∉ candidates pathStep ∧ pr 1 4 ∈ (generate path).pairs := by
  decide +kernel

/-- On the hollow triangle, the pass matches (A, AB) and (B, BC). -/
theorem circle_generate_pairs : (generate circle).pairs = [pr 0 3, pr 1 4] := by
  decide +kernel

/-- On the hollow triangle, exactly one vertex, C, and one edge, AC, remain critical. -/
theorem circle_generate_report :
    (generate circle).criticalReport = [(⟨2, by decide⟩, 0, 0), (⟨5, by decide⟩, 1, 0)] := by
  decide +kernel

/-- The rejected candidate (C, AC) on the hollow triangle is a candidate, and adding it to the
generated pairs still gives a list-level matching. -/
theorem circle_rejected_conditions :
    pr 2 5 ∈ candidates circle ∧
      MatchingInput.IsMatching circle ((generate circle).pairs ++ [pr 2 5]) := by
  decide +kernel

/-- No rank is accepted for the generated pairs of the hollow triangle extended by (C, AC). -/
theorem circle_rejected_no_certificate :
    ∀ rank, check circle ((generate circle).pairs ++ [pr 2 5]) rank = false := by
  rw [circle_generate_pairs]
  exact TDA.Persistence.Morse.FiniteInputMatchingExamples.cyclic_no_certificate

/-- The candidate (C, AC), reached with state (A, AB), (B, BC), closes a cycle on `filled`. -/
theorem filled_rejected_no_certificate :
    ∀ rank, check filled [pr 0 3, pr 1 4, pr 2 5] rank = false := by
  intro rank
  rw [Bool.eq_false_iff, ne_eq, check_eq_true_iff]
  rintro ⟨-, h⟩
  have h1 := h ⟨2, by decide⟩ ⟨5, by decide⟩ (by decide +kernel)
  have h2 := h ⟨5, by decide⟩ ⟨0, by decide⟩ (by decide +kernel)
  have h3 := h ⟨0, by decide⟩ ⟨3, by decide⟩ (by decide +kernel)
  have h4 := h ⟨3, by decide⟩ ⟨1, by decide⟩ (by decide +kernel)
  have h5 := h ⟨1, by decide⟩ ⟨4, by decide⟩ (by decide +kernel)
  have h6 := h ⟨4, by decide⟩ ⟨2, by decide⟩ (by decide +kernel)
  omega

/-- On the filled triangle, the pass matches (A, AB), (B, BC) and (AC, ABC). -/
theorem filled_generate_pairs : (generate filled).pairs = [pr 0 3, pr 1 4, pr 5 6] := by
  decide +kernel

/-- On the filled triangle, only C remains critical: it reduces to one vertex. -/
theorem filled_generate_report :
    (generate filled).criticalReport = [(⟨2, by decide⟩, 0, 0)] := by
  decide +kernel

/-- On the square, the pass matches (A, AB), (B, BC), (C, CD) and (AC, ABC). -/
theorem square_generate_pairs :
    (generate square).pairs = [pr 0 4, pr 1 5, pr 2 6, pr 8 9] := by
  decide +kernel

/-- On the square, D, AD and ACD remain critical, one face per grade 0, 1, 2. -/
theorem square_generate_report :
    (generate square).criticalReport =
      [(⟨3, by decide⟩, 0, 0), (⟨7, by decide⟩, 1, 1), (⟨10, by decide⟩, 2, 2)] := by
  decide +kernel

end TDA.Persistence.Morse.FiniteInputMatchingGenerationExamples
