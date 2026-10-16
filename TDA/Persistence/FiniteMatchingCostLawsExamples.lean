import TDA.Persistence.FiniteMatchingCostLaws

/-! Relabelling, multiplicity, the positive-lifetime boundary and four composition paths. -/

namespace TDA.Persistence.FiniteMatchingCostLawsExamples

private def positivePairs (i : Fin 2) : ℝ × ℝ := if i = 0 then (0, 2) else (1, 3)

private theorem permuted_zero :
    finiteFirstOrderMatchingCost (positivePairs ∘ Equiv.swap 0 1) positivePairs = 0 :=
  finiteFirstOrderMatchingCost_eq_zero_of_equiv _ _ (Equiv.swap 0 1) (fun _ => rfl)

private theorem permuted_presentations_differ :
    positivePairs ∘ Equiv.swap 0 1 ≠ positivePairs := by
  intro h
  have hzero := congrArg (fun f => f 0) h
  norm_num [positivePairs, Function.comp_def] at hzero

private theorem repeated_ne_singleton :
    finiteFirstOrderMatchingCost (fun _ : Fin 2 => ((0, 2) : ℝ × ℝ))
      (fun _ : Unit => (0, 2)) ≠ 0 := by
  intro hz
  obtain ⟨e, _⟩ := (finiteFirstOrderMatchingCost_eq_zero_iff _ _
    (fun _ => by norm_num) (fun _ => by norm_num)).mp hz
  have hc := Fintype.card_congr e
  norm_num at hc

private theorem diagonal_to_empty_zero :
    finiteFirstOrderMatchingCost (fun _ : Unit => ((0, 0) : ℝ × ℝ))
      (Fin.elim0 : Fin 0 → ℝ × ℝ) = 0 := by
  rw [finiteFirstOrderMatchingCost_of_isEmpty_right]
  simp [diagonalCost]

private theorem diagonal_to_empty_has_no_equiv : ¬ Nonempty (Unit ≃ Fin 0) := by
  rintro ⟨e⟩
  exact Fin.elim0 (e ())

private def firstMatching : OccurrenceMatching (Fin 2) (Fin 4) PEmpty.{1} PEmpty.{1} where
  finite i := if i = 0 then some 0 else some 1
  finite_injective := by
    intro i i' j hi hi'
    fin_cases i <;> fin_cases i' <;> simp_all <;> omega
  essential := Equiv.refl _

private def secondMatching : OccurrenceMatching (Fin 4) (Fin 2) PEmpty.{1} PEmpty.{1} where
  finite j := if j = 0 then some 0 else if j = 2 then some 1 else none
  finite_injective := by
    intro j j' k hj hj'
    fin_cases j <;> fin_cases j' <;> simp_all <;> omega
  essential := Equiv.refl _

private def source : Fin 2 → ℝ × ℝ := ![(0, 4), (0, 4)]
private def middle : Fin 4 → ℝ × ℝ := ![(1, 5), (1, 3), (4, 6), (10, 12)]
private def target : Fin 2 → ℝ × ℝ := ![(2, 6), (3, 7)]

/-- Middle labels 0/1/2/3 are respectively complete, source-ending,
target-starting and middle-only paths. -/
private theorem four_paths :
    (firstMatching.compose secondMatching).finite 0 = some 0 ∧
    (firstMatching.compose secondMatching).finite 1 = none ∧
    (¬ ∃ i, firstMatching.finite i = some 2) ∧ secondMatching.finite 2 = some 1 ∧
    (¬ ∃ i, firstMatching.finite i = some 3) ∧ secondMatching.finite 3 = none := by
  decide

private theorem first_total : firstMatching.totalFiniteCost source middle = 4 := by
  norm_num [OccurrenceMatching.totalFiniteCost, firstMatching, source, middle,
    Fin.sum_univ_succ, Fin.exists_fin_succ, finitePairCost, diagonalCost]
  simp +decide
  norm_num

private theorem second_total : secondMatching.totalFiniteCost middle target = 4 := by
  norm_num [OccurrenceMatching.totalFiniteCost, secondMatching, middle, target,
    Fin.sum_univ_succ, Fin.exists_fin_succ, finitePairCost, diagonalCost]
  simp +decide
  norm_num

private theorem composed_total :
    (firstMatching.compose secondMatching).totalFiniteCost source target = 6 := by
  norm_num [OccurrenceMatching.totalFiniteCost, OccurrenceMatching.compose,
    firstMatching, secondMatching, source, target,
    Fin.sum_univ_succ, Fin.exists_fin_succ, finitePairCost, diagonalCost]
  simp +decide
  norm_num

private theorem four_path_budget :
    (firstMatching.compose secondMatching).totalFiniteCost source target ≤
      firstMatching.totalFiniteCost source middle + secondMatching.totalFiniteCost middle target :=
  firstMatching.totalFiniteCost_compose_le secondMatching source middle target

end TDA.Persistence.FiniteMatchingCostLawsExamples
