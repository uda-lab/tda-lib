import TDA.Persistence.Morse.FiniteInputMatching

/-!
# Fixtures for the finite-input matching checker

Small inputs with accepted and rejected matchings for
`TDA.Persistence.Morse.MatchingInput.check`. Vertices `{0}`, `{1}`, … are written A, B, ….
Every closed computation is a kernel `decide`; fixtures that quantify over all ranks or state
a semantic fact go through the general theorems of `FiniteInputMatching`.

Inside `TDA.Persistence.Morse`, the bare names `IsMatching`, `arrow` and `IsTopologicalRank`
denote the semantic predicates, so the list-level ones are written `MatchingInput.IsMatching`,
`MatchingInput.arrow` and `MatchingInput.IsTopologicalRank`.

The negative fixtures name the matching conditions (N) distinct endpoints, (C) every pair is
a cover and (G) equal grades. Each matching-level negative fixture violates exactly one of
them, and no rank is accepted for it. The cyclic circle satisfies all three and admits no
topological rank.
-/

set_option autoImplicit false

namespace TDA.Persistence.Morse.FiniteInputMatchingExamples

open TDA.Simplicial TDA.Filtration TDA.Persistence.Reduction FiniteInput
open TDA.Persistence.Morse.MatchingInput

/-- A position pair whose bounds are discharged by `decide`. -/
def pr {xs : Input} (i j : ℕ) (hi : i < xs.length := by decide)
    (hj : j < xs.length := by decide) : Fin xs.length × Fin xs.length := (⟨i, hi⟩, ⟨j, hj⟩)

/-- A rank given by a list of naturals, indexed by position. -/
def rankOf {n : ℕ} (l : List ℕ) : Fin n → ℕ := fun i => l.getD i.val 0

/-! ## Inputs -/

/-- The empty input. -/
def empty : Input := []

/-- The path A–B–C, all grade 0. -/
def path : Input := [({0}, 0), ({1}, 0), ({2}, 0), ({0, 1}, 0), ({1, 2}, 0)]

/-- The path A–B–C with BC at grade 1. -/
def pathStep : Input := [({0}, 0), ({1}, 0), ({2}, 0), ({0, 1}, 0), ({1, 2}, 1)]

/-- The hollow triangle A, B, C, AB, BC, AC, all grade 0. -/
def circle : Input := [({0}, 0), ({1}, 0), ({2}, 0), ({0, 1}, 0), ({1, 2}, 0), ({0, 2}, 0)]

/-- The filled triangle: `circle` followed by ABC, all grade 0. -/
def filled : Input :=
  [({0}, 0), ({1}, 0), ({2}, 0), ({0, 1}, 0), ({1, 2}, 0), ({0, 2}, 0), ({0, 1, 2}, 0)]

/-- The multi-grade square: A, B, C, D, AB, BC, CD at 0; AD at 1; AC, ABC, ACD at 2. -/
def square : Input := [({0}, 0), ({1}, 0), ({2}, 0), ({3}, 0), ({0, 1}, 0), ({1, 2}, 0),
  ({2, 3}, 0), ({0, 3}, 1), ({0, 2}, 2), ({0, 1, 2}, 2), ({0, 2, 3}, 2)]

/-- `empty` is a valid input. -/
theorem empty_valid : Valid empty := (validBool_iff _).mp (by decide +kernel)
/-- `path` is a valid input. -/
theorem path_valid : Valid path := (validBool_iff _).mp (by decide +kernel)
/-- `pathStep` is a valid input. -/
theorem pathStep_valid : Valid pathStep := (validBool_iff _).mp (by decide +kernel)
/-- `circle` is a valid input. -/
theorem circle_valid : Valid circle := (validBool_iff _).mp (by decide +kernel)
/-- `filled` is a valid input. -/
theorem filled_valid : Valid filled := (validBool_iff _).mp (by decide +kernel)
/-- `square` is a valid input. -/
theorem square_valid : Valid square := (validBool_iff _).mp (by decide +kernel)

/-! ## Accepted matchings and their critical reports -/

/-- The empty matching of the empty input is accepted. -/
theorem empty_check : check empty [] (fun _ => 0) = true := by decide +kernel

/-- The empty input has no critical face. -/
theorem empty_report :
    (certify? empty [] (fun _ => 0)).map CertifiedMatching.criticalReport = some [] := by
  decide +kernel

/-- (B, AB) and (C, BC) on the path. -/
def pathPairs : Pairs path := [pr 1 3, pr 2 4]

/-- The path matching is accepted with its rank. -/
theorem path_check : check path pathPairs (rankOf [4, 2, 0, 3, 1]) = true := by
  decide +kernel

/-- Only A remains critical on the path. -/
theorem path_report :
    (certify? path pathPairs (rankOf [4, 2, 0, 3, 1])).map CertifiedMatching.criticalReport =
      some [(⟨0, by decide⟩, 0, 0)] := by
  decide +kernel

/-- (B, AB) alone on the path, with a rank; the accepted orientation of `reversedPairs`. -/
theorem pathSingle_check : check path [pr 1 3] (rankOf [4, 2, 1, 3, 0]) = true := by
  decide +kernel

/-- A valid matching with a bad rank is rejected, although the pairs form a matching. -/
theorem path_badRank :
    check path pathPairs (fun _ => 0) = false ∧ MatchingInput.IsMatching path pathPairs := by
  decide +kernel

/-- (B, AB) and (C, BC) on the hollow triangle. -/
def circlePairs : Pairs circle := [pr 1 3, pr 2 4]

/-- The hollow-triangle matching is accepted with its rank. -/
theorem circle_check : check circle circlePairs (rankOf [5, 3, 1, 4, 2, 0]) = true := by
  decide +kernel

/-- A and AC remain critical on the hollow triangle. -/
theorem circle_report :
    (certify? circle circlePairs (rankOf [5, 3, 1, 4, 2, 0])).map
        CertifiedMatching.criticalReport =
      some [(⟨0, by decide⟩, 0, 0), (⟨5, by decide⟩, 1, 0)] := by
  decide +kernel

/-- (B, AB), (C, BC) and (AC, ABC) on the filled triangle. -/
def filledPairs : Pairs filled := [pr 1 3, pr 2 4, pr 5 6]

/-- The filled-triangle matching is accepted with its rank. -/
theorem filled_check : check filled filledPairs (rankOf [6, 4, 2, 5, 3, 0, 1]) = true := by
  decide +kernel

/-- Only A remains critical on the filled triangle. -/
theorem filled_report :
    (certify? filled filledPairs (rankOf [6, 4, 2, 5, 3, 0, 1])).map
        CertifiedMatching.criticalReport =
      some [(⟨0, by decide⟩, 0, 0)] := by
  decide +kernel

/-- The empty matching of the filled triangle is accepted with its rank. -/
theorem filledEmpty_check : check filled [] (rankOf [2, 2, 2, 1, 1, 1, 0]) = true := by
  decide +kernel

/-- With the empty matching, all seven faces of the filled triangle are critical. -/
theorem filledEmpty_report :
    (certify? filled [] (rankOf [2, 2, 2, 1, 1, 1, 0])).map CertifiedMatching.criticalReport =
      some [(⟨0, by decide⟩, 0, 0), (⟨1, by decide⟩, 0, 0), (⟨2, by decide⟩, 0, 0),
        (⟨3, by decide⟩, 1, 0), (⟨4, by decide⟩, 1, 0), (⟨5, by decide⟩, 1, 0),
        (⟨6, by decide⟩, 2, 0)] := by
  decide +kernel

/-- (B, AB), (C, BC), (D, CD) and (AC, ABC) on the square. -/
def squarePairs : Pairs square := [pr 1 4, pr 2 5, pr 3 6, pr 8 9]

/-- The square matching is accepted with its rank. -/
theorem square_check :
    check square squarePairs (rankOf [10, 8, 6, 4, 9, 7, 5, 1, 2, 3, 0]) = true := by
  decide +kernel

/-- A, AD and ACD remain critical on the square, at dimensions 0, 1, 2 and grades 0, 1, 2. -/
theorem square_report :
    (certify? square squarePairs (rankOf [10, 8, 6, 4, 9, 7, 5, 1, 2, 3, 0])).map
        CertifiedMatching.criticalReport =
      some [(⟨0, by decide⟩, 0, 0), (⟨7, by decide⟩, 1, 1), (⟨10, by decide⟩, 2, 2)] := by
  decide +kernel

/-- The square pairs contain no duplicate pair. -/
theorem squarePairs_nodup : squarePairs.Nodup := by decide +kernel

/-- The square matching is a filtered acyclic matching of the represented complex. -/
theorem square_isFilteredAcyclicMatching :
    IsFilteredAcyclicMatching (gradeFilter square square_valid)
      (toRel square square_valid squarePairs) :=
  ((exists_check_iff_isFilteredAcyclicMatching square square_valid squarePairs).mp
    ⟨_, square_check⟩).2

/-! ## Rejected matchings -/

/-- A list that is not a list-level matching is rejected with every rank. -/
private theorem check_false_of_not {xs : Input} {pairs : Pairs xs}
    (hn : ¬ MatchingInput.IsMatching xs pairs) (rank : Fin xs.length → ℕ) :
    check xs pairs rank = false :=
  Bool.eq_false_iff.mpr fun hc => hn ((check_eq_true_iff xs pairs rank).mp hc).1

/-- B is used twice: (B, AB) and (B, BC). -/
def reusePairs : Pairs path := [pr 1 3, pr 1 4]

/-- `reusePairs` violates (N) only. -/
theorem reuse_conditions : ¬ (endpoints reusePairs).Nodup ∧
    (∀ p ∈ reusePairs, IsCover path p.1 p.2) ∧
    (∀ p ∈ reusePairs, (path.get p.1).2 = (path.get p.2).2) := by
  decide +kernel

/-- No rank is accepted for `reusePairs`. -/
theorem reuse_check : ∀ rank, check path reusePairs rank = false :=
  check_false_of_not fun h => reuse_conditions.1 h.1

/-- The identical pair (B, AB) twice. -/
def repeatedPairs : Pairs path := [pr 1 3, pr 1 3]

/-- `repeatedPairs` violates (N) only. -/
theorem repeated_conditions : ¬ (endpoints repeatedPairs).Nodup ∧
    (∀ p ∈ repeatedPairs, IsCover path p.1 p.2) ∧
    (∀ p ∈ repeatedPairs, (path.get p.1).2 = (path.get p.2).2) := by
  decide +kernel

/-- No rank is accepted for `repeatedPairs`. -/
theorem repeated_check : ∀ rank, check path repeatedPairs rank = false :=
  check_false_of_not fun h => repeated_conditions.1 h.1

/-- (C, AB): one more vertex, but not a subset. -/
def nonSubsetPairs : Pairs path := [pr 2 3]

/-- `nonSubsetPairs` violates (C) only. -/
theorem nonSubset_conditions : (endpoints nonSubsetPairs).Nodup ∧
    ¬ (∀ p ∈ nonSubsetPairs, IsCover path p.1 p.2) ∧
    (∀ p ∈ nonSubsetPairs, (path.get p.1).2 = (path.get p.2).2) := by
  decide +kernel

/-- No rank is accepted for `nonSubsetPairs`. -/
theorem nonSubset_check : ∀ rank, check path nonSubsetPairs rank = false :=
  check_false_of_not fun h => nonSubset_conditions.2.1 h.2.1

/-- (A, ABC): a subset with two more vertices. -/
def codimTwoPairs : Pairs filled := [pr 0 6]

/-- `codimTwoPairs` violates (C) only among the matching conditions. -/
theorem codimTwo_conditions : (endpoints codimTwoPairs).Nodup ∧
    ¬ (∀ p ∈ codimTwoPairs, IsCover filled p.1 p.2) ∧
    (∀ p ∈ codimTwoPairs, (filled.get p.1).2 = (filled.get p.2).2) := by
  decide +kernel

/-- No rank is accepted for `codimTwoPairs`. -/
theorem codimTwo_check : ∀ rank, check filled codimTwoPairs rank = false :=
  check_false_of_not fun h => codimTwo_conditions.2.1 h.2.1

/-- The arrows ABC → AB → A → ABC (positions 6 → 3 → 0 → 6) form a cycle, so no rank exists. -/
theorem codimTwo_no_rank :
    ∀ rank, ¬ MatchingInput.IsTopologicalRank filled codimTwoPairs rank := by
  intro rank h
  have h1 := h ⟨6, by decide⟩ ⟨3, by decide⟩ (by decide +kernel)
  have h2 := h ⟨3, by decide⟩ ⟨0, by decide⟩ (by decide +kernel)
  have h3 := h ⟨0, by decide⟩ ⟨6, by decide⟩ (by decide +kernel)
  omega

/-- (AB, B): the pair (B, AB) in reversed order. -/
def reversedPairs : Pairs path := [pr 3 1]

/-- `reversedPairs` violates (C) only. -/
theorem reversed_conditions : (endpoints reversedPairs).Nodup ∧
    ¬ (∀ p ∈ reversedPairs, IsCover path p.1 p.2) ∧
    (∀ p ∈ reversedPairs, (path.get p.1).2 = (path.get p.2).2) := by
  decide +kernel

/-- No rank is accepted for `reversedPairs`. -/
theorem reversed_check : ∀ rank, check path reversedPairs rank = false :=
  check_false_of_not fun h => reversed_conditions.2.1 h.2.1

/-- (C, BC) on `pathStep`, with grades 0 and 1. -/
def unequalGradePairs : Pairs pathStep := [pr 2 4]

/-- `unequalGradePairs` violates (G) only. -/
theorem unequalGrade_conditions : (endpoints unequalGradePairs).Nodup ∧
    (∀ p ∈ unequalGradePairs, IsCover pathStep p.1 p.2) ∧
    ¬ (∀ p ∈ unequalGradePairs, (pathStep.get p.1).2 = (pathStep.get p.2).2) := by
  decide +kernel

/-- No rank is accepted for `unequalGradePairs`. -/
theorem unequalGrade_check : ∀ rank, check pathStep unequalGradePairs rank = false :=
  check_false_of_not fun h => unequalGrade_conditions.2.2 h.2.2

/-! ## The cyclic circle -/

/-- (A, AB), (B, BC) and (C, AC) on the hollow triangle. -/
def cyclicPairs : Pairs circle := [pr 0 3, pr 1 4, pr 2 5]

/-- The cyclic pairs satisfy (N), (C) and (G). -/
theorem cyclic_isMatching : MatchingInput.IsMatching circle cyclicPairs := by decide +kernel

/-- The cycle A → AB → B → BC → C → AC → A on positions 0 → 3 → 1 → 4 → 2 → 5 → 0. -/
theorem cyclic_arrows :
    MatchingInput.arrow circle cyclicPairs ⟨0, by decide⟩ ⟨3, by decide⟩ ∧
    MatchingInput.arrow circle cyclicPairs ⟨3, by decide⟩ ⟨1, by decide⟩ ∧
    MatchingInput.arrow circle cyclicPairs ⟨1, by decide⟩ ⟨4, by decide⟩ ∧
    MatchingInput.arrow circle cyclicPairs ⟨4, by decide⟩ ⟨2, by decide⟩ ∧
    MatchingInput.arrow circle cyclicPairs ⟨2, by decide⟩ ⟨5, by decide⟩ ∧
    MatchingInput.arrow circle cyclicPairs ⟨5, by decide⟩ ⟨0, by decide⟩ := by
  decide +kernel

/-- The semantic matching of the cyclic pairs has a directed cycle. -/
theorem cyclic_not_isAcyclic : ¬ IsAcyclic (toRel circle circle_valid cyclicPairs) := by
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := cyclic_arrows
  intro hA
  have l := fun {u v : Fin circle.length} (huv : MatchingInput.arrow circle cyclicPairs u v) =>
    (arrow_iff circle circle_valid cyclicPairs u v).mp huv
  exact hA _ (.head (l a1) (.head (l a2) (.head (l a3) (.head (l a4) (.head (l a5)
    (.single (l a6)))))))

/-- No rank certificate is accepted for the cyclic pairs. -/
theorem cyclic_no_certificate : ∀ rank, check circle cyclicPairs rank = false := by
  intro rank
  refine Bool.eq_false_iff.mpr fun hc => ?_
  have hr := ((check_eq_true_iff circle cyclicPairs rank).mp hc).2
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := cyclic_arrows
  have := hr _ _ a1
  have := hr _ _ a2
  have := hr _ _ a3
  have := hr _ _ a4
  have := hr _ _ a5
  have := hr _ _ a6
  omega

end TDA.Persistence.Morse.FiniteInputMatchingExamples
