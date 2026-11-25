import TDA.Persistence.IntegerBottleneckCorrectness

/-!
# Integer bottleneck examples

The finite computations below are reduced by the kernel, then consumed through
the general correctness theorem for the existing real diagram bottleneck.
-/

namespace TDA.Persistence.IntegerBottleneck.Examples

open scoped ENNReal

private def empty : Presentation := ⟨[], []⟩
private def halfBar : Presentation := ⟨[(0, 1)], []⟩
private def twoCopies : Presentation := ⟨[(0, 4), (0, 4)], []⟩
private def oneCopy : Presentation := ⟨[(0, 4)], []⟩
private def farLeft : Presentation := ⟨[(0, 10)], []⟩
private def farRight : Presentation := ⟨[(100, 110)], []⟩
private def essentialLeft : Presentation := ⟨[], [0, 3]⟩
private def essentialRight : Presentation := ⟨[], [4, 1]⟩
private def mixedLeft : Presentation := ⟨[(0, 6)], [0]⟩
private def mixedRight : Presentation := ⟨[(100, 104)], [2]⟩
private def essentialDominant : Presentation := ⟨[], [5]⟩
private def finiteShort : Presentation := ⟨[(0, 2)], [0]⟩
private def reversed : Presentation := ⟨[(3, 1)], []⟩
private def negative : Presentation := ⟨[(-5, -2)], []⟩
private def diagonals : Presentation := ⟨[(0, 0), (-3, -3)], []⟩
private def repeatedEssential : Presentation := ⟨[], [2, 2]⟩
private def permutedLeft : Presentation := ⟨[(0, 4), (-5, -2)], [0, 3, 3]⟩
private def permutedRight : Presentation := ⟨[(-5, -2), (0, 4)], [3, 0, 3]⟩
private def labelledLeft : Presentation := ⟨[(7, 7), (0, 4), (5, 5)], []⟩
private def labelledRight : Presentation := ⟨[(1, 1), (2, 2), (0, 4)], []⟩
private def rectangularLeft : Presentation := ⟨[(0, 4), (10, 12)], []⟩

/-- Half-integral distance is represented exactly by the odd doubled value. -/
theorem half_bar : (run halfBar empty).twiceDistance = 1 ∧
    bottleneck (diagram halfBar) (diagram empty) = (1 : ℝ≥0∞) / 2 := by
  constructor
  · decide
  · simpa only [Nat.cast_one] using bottleneck_eq_of_twiceDistance halfBar empty 1 (by decide)

/-- Repeated finite values remain two occurrences. -/
theorem repeated_finite : (run twoCopies oneCopy).twiceDistance = 4 ∧
    bottleneck (diagram twoCopies) (diagram oneCopy) = 2 := by
  constructor
  · decide
  · simpa only [Nat.cast_ofNat] using bottleneck_eq_nat_of_twiceDistance twoCopies oneCopy 2 (by decide)

/-- Deleting both far-apart bars is preferable to forcing a finite pair. -/
theorem delete_both : (run farLeft farRight).twiceDistance = 10 ∧
    (run farLeft farRight).matching.map Candidate.finitePairs = some [] ∧
    bottleneck (diagram farLeft) (diagram farRight) = 5 := by
  refine ⟨by decide, by decide, ?_⟩
  simpa only [Nat.cast_ofNat] using bottleneck_eq_nat_of_twiceDistance farLeft farRight 5 (by decide)

/-- The returned essential bijection is the nonidentity optimal correspondence. -/
theorem essential_crossing : (run essentialLeft essentialRight).twiceDistance = 2 ∧
    (run essentialLeft essentialRight).matching.map Candidate.essentialPairs =
      some [(0, 1), (1, 0)] ∧
    bottleneck (diagram essentialLeft) (diagram essentialRight) = 1 := by
  refine ⟨by decide, by decide, ?_⟩
  simpa only [Nat.cast_one] using bottleneck_eq_nat_of_twiceDistance essentialLeft essentialRight 1 (by decide)

/-- Essential mismatch is a valid infinite result and has no witness. -/
theorem essential_mismatch :
    (run empty essentialLeft).twiceDistance = ⊤ ∧
    (run empty essentialLeft).matching = none ∧
    (run essentialLeft essentialDominant).twiceDistance = ⊤ ∧
    (run essentialLeft essentialDominant).matching = none := by decide

/-- The infinite branch also agrees with the established diagram bottleneck. -/
theorem essential_mismatch_semantics :
    bottleneck (diagram empty) (diagram essentialLeft) = ⊤ ∧
    bottleneck (diagram essentialLeft) (diagram essentialDominant) = ⊤ := by
  constructor
  · exact bottleneck_eq_top_of_twiceDistance empty essentialLeft (by decide)
  · exact bottleneck_eq_top_of_twiceDistance essentialLeft essentialDominant (by decide)

/-- Finite deletion and essential matching share one maximum; finite deletion
dominates in the first example and essential transport in the second. -/
theorem mixed_costs :
    (run mixedLeft mixedRight).twiceDistance = 6 ∧
    (run finiteShort essentialDominant).twiceDistance = 10 ∧
    bottleneck (diagram mixedLeft) (diagram mixedRight) = 3 ∧
    bottleneck (diagram finiteShort) (diagram essentialDominant) = 5 := by
  refine ⟨by decide, by decide, ?_, ?_⟩
  · simpa only [Nat.cast_ofNat] using bottleneck_eq_nat_of_twiceDistance mixedLeft mixedRight 3 (by decide)
  · simpa only [Nat.cast_ofNat] using bottleneck_eq_nat_of_twiceDistance finiteShort essentialDominant 5 (by decide)

/-- Empty and all-diagonal finite lists give zero, with an actual finite witness. -/
theorem empty_and_diagonal :
    (run empty empty).twiceDistance = 0 ∧
    (run diagonals empty).twiceDistance = 0 ∧
    (run diagonals empty).matching.map Candidate.finitePairs = some [] ∧
    bottleneck (diagram diagonals) (diagram empty) = 0 := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  simpa using bottleneck_eq_of_twiceDistance diagonals empty 0 (by decide)

/-- Reversed pairs and negative coordinates use magnitudes of integer differences. -/
theorem signed_coordinates :
    (run reversed empty).twiceDistance = 2 ∧
    (run negative empty).twiceDistance = 3 ∧
    bottleneck (diagram reversed) (diagram empty) = 1 ∧
    bottleneck (diagram negative) (diagram empty) = (3 : ℝ≥0∞) / 2 := by
  refine ⟨by decide, by decide, ?_, ?_⟩
  · simpa only [Nat.cast_one] using bottleneck_eq_nat_of_twiceDistance reversed empty 1 (by decide)
  · exact bottleneck_eq_of_twiceDistance negative empty 3 (by decide)

/-- Repeated essential births and simultaneous list permutations preserve zero. -/
theorem zero_permutations :
    (run repeatedEssential repeatedEssential).twiceDistance = 0 ∧
    (run permutedLeft permutedRight).twiceDistance = 0 ∧
    bottleneck (diagram permutedLeft) (diagram permutedRight) = 0 := by
  refine ⟨by decide, by decide, ?_⟩
  simpa using bottleneck_eq_of_twiceDistance permutedLeft permutedRight 0 (by decide)

/-- Filtering diagonal entries does not renumber the returned finite positions. -/
theorem original_positions :
    (run labelledLeft labelledRight).twiceDistance = 0 ∧
    (run labelledLeft labelledRight).matching.map Candidate.finitePairs = some [(1, 2)] ∧
    bottleneck (diagram labelledLeft) (diagram labelledRight) = 0 := by
  refine ⟨by decide, by decide, ?_⟩
  simpa using bottleneck_eq_of_twiceDistance labelledLeft labelledRight 0 (by decide)

/-- A genuinely rectangular search leaves a source unmatched; reversing it leaves
a target unmatched and produces the same positive cost. -/
theorem rectangular_both_sides :
    (run rectangularLeft oneCopy).twiceDistance = 2 ∧
    (run oneCopy rectangularLeft).twiceDistance = 2 ∧
    (run rectangularLeft oneCopy).matching.map Candidate.finitePairs = some [(0, 0)] ∧
    (run oneCopy rectangularLeft).matching.map Candidate.finitePairs = some [(0, 0)] ∧
    bottleneck (diagram rectangularLeft) (diagram oneCopy) = 1 ∧
    bottleneck (diagram oneCopy) (diagram rectangularLeft) = 1 := by
  refine ⟨by decide, by decide, by decide, by decide, ?_, ?_⟩
  · simpa only [Nat.cast_one] using bottleneck_eq_nat_of_twiceDistance rectangularLeft oneCopy 1 (by decide)
  · simpa only [Nat.cast_one] using bottleneck_eq_nat_of_twiceDistance oneCopy rectangularLeft 1 (by decide)

/-- The actual returned data, rather than a caller-supplied matching, interprets
to a cost-minimizing occurrence matching. -/
theorem returned_witness_semantics :
    ∃ a : Candidate labelledLeft labelledRight,
      (run labelledLeft labelledRight).matching = some a ∧
      a.finitePairs = [(1, 2)] ∧
      a.toMatching.cost (fun i => realFinite labelledLeft i.1)
        (fun j => realFinite labelledRight j.1)
        (realEssential labelledLeft) (realEssential labelledRight) =
          bottleneck (diagram labelledLeft) (diagram labelledRight) := by
  obtain ⟨a, ha⟩ := (solve_exists_iff labelledLeft labelledRight).mpr (by decide)
  refine ⟨a, ha, ?_, solve_cost_eq _ _ ha⟩
  have hp := original_positions.2.1
  simpa only [run_matching, ha, Option.map_some, Option.some.injEq] using hp

end TDA.Persistence.IntegerBottleneck.Examples
