import TDA.Persistence.FinitePBoundaryTransportLaws
import TDA.Persistence.FinitePBoundaryTransportExamples

/-!
# Finite real-p distance-law examples

The composition fixture contains all four middle roles as well as unmatched
endpoints. Exact singleton calculations test sharp rooted triangles at integer
and noninteger exponents. Relabelling, duplicate occurrences and free deletion
of diagonal points check the precise separation statement.
-/

noncomputable section
namespace TDA.Persistence.FinitePMatchingCostLawsExamples
open scoped Classical

private def firstMatching : OccurrenceMatching (Fin 3) (Fin 4) PEmpty.{1} PEmpty.{1} where
  finite i := if i = 0 then some 0 else if i = 1 then some 1 else none
  finite_injective := by
    intro i i' j hi hi'
    fin_cases i <;> fin_cases i' <;> simp_all <;> omega
  essential := Equiv.refl _

private def secondMatching : OccurrenceMatching (Fin 4) (Fin 3) PEmpty.{1} PEmpty.{1} where
  finite j := if j = 0 then some 0 else if j = 2 then some 1 else none
  finite_injective := by
    intro j j' k hj hj'
    fin_cases j <;> fin_cases j' <;> simp_all <;> omega
  essential := Equiv.refl _

private def source : Fin 3 → ℝ × ℝ := ![(0, 8), (2, 6), (0, 2)]
private def middle : Fin 4 → ℝ × ℝ := ![(1, 9), (2, 8), (4, 8), (0, 2)]
private def target : Fin 3 → ℝ × ℝ := ![(2, 10), (4, 10), (0, 2)]

/-- Middle labels 0/1/2/3 are complete, source-ending, target-starting,
and middle-only paths. Source 2 and target 2 are unmatched endpoints. -/
private theorem four_middle_roles :
    firstMatching.finite 0 = some 0 ∧ secondMatching.finite 0 = some 0 ∧
    firstMatching.finite 1 = some 1 ∧ secondMatching.finite 1 = none ∧
    (¬ ∃ i, firstMatching.finite i = some 2) ∧ secondMatching.finite 2 = some 1 ∧
    (¬ ∃ i, firstMatching.finite i = some 3) ∧ secondMatching.finite 3 = none ∧
    firstMatching.finite 2 = none ∧ (¬ ∃ j, secondMatching.finite j = some 2) := by
  decide

private theorem four_path_power_costs :
    firstMatching.totalFinitePowerCost 2 source middle = 11 ∧
    secondMatching.totalFinitePowerCost 2 middle target = 16 ∧
    (firstMatching.compose secondMatching).totalFinitePowerCost 2 source target = 19 := by
  repeat constructor
  all_goals
    norm_num [OccurrenceMatching.totalFinitePowerCost, OccurrenceMatching.totalBoundaryCost,
      OccurrenceMatching.compose, firstMatching, secondMatching, source, middle, target,
      Fin.sum_univ_succ, Fin.exists_fin_succ, finitePairCost, diagonalCost, Real.rpow_two]
    simp +decide
    norm_num

private theorem four_path_root_budget : Real.sqrt 19 ≤ Real.sqrt 11 + 4 := by
  have h := firstMatching.totalFinitePowerCost_compose_root_le secondMatching
    (p := 2) (by norm_num) source middle target
  obtain ⟨hM, hN, hcomp⟩ := four_path_power_costs
  rw [hM, hN, hcomp] at h
  norm_num [← Real.sqrt_eq_rpow] at h
  exact h

/-- This checks the actual singleton minimum, rather than assuming a chosen pair is optimal. -/
private theorem singleton_root_eq_pair_of_le_diagonal {p : ℝ} (hp : 1 ≤ p)
    (a b : ℝ × ℝ) (hc : (finitePairCost a b).toReal ≤ (diagonalCost a).toReal) :
    finitePBoundaryTransportCost p (fun _ : Fin 1 => a) (fun _ : Fin 1 => b) =
      (finitePairCost a b).toReal := by
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hp)
  have hcost : (finitePairCost a b).toReal ^ p ≤
      (diagonalCost a).toReal ^ p + (diagonalCost b).toReal ^ p :=
    (Real.rpow_le_rpow ENNReal.toReal_nonneg hc (zero_le_one.trans hp)).trans
      (le_add_of_nonneg_right (Real.rpow_nonneg ENNReal.toReal_nonneg _))
  rw [finitePBoundaryTransportCost_eq_matchingCost, finitePMatchingCost,
    finitePowerMatchingCost_singleton, min_eq_left hcost]
  exact Real.rpow_rpow_inv ENNReal.toReal_nonneg hp0

private theorem translated_roots {p : ℝ} (hp : 1 ≤ p) :
    finitePBoundaryTransportCost p (fun _ : Fin 1 => ((0, 10) : ℝ × ℝ))
      (fun _ : Fin 1 => (1, 11)) = 1 ∧
    finitePBoundaryTransportCost p (fun _ : Fin 1 => ((1, 11) : ℝ × ℝ))
      (fun _ : Fin 1 => (2, 12)) = 1 ∧
    finitePBoundaryTransportCost p (fun _ : Fin 1 => ((0, 10) : ℝ × ℝ))
      (fun _ : Fin 1 => (2, 12)) = 2 := by
  have h01 := singleton_root_eq_pair_of_le_diagonal hp (0, 10) (1, 11)
    (by norm_num [finitePairCost, diagonalCost])
  have h12 := singleton_root_eq_pair_of_le_diagonal hp (1, 11) (2, 12)
    (by norm_num [finitePairCost, diagonalCost])
  have h02 := singleton_root_eq_pair_of_le_diagonal hp (0, 10) (2, 12)
    (by norm_num [finitePairCost, diagonalCost])
  norm_num [finitePairCost] at h01 h12 h02
  exact ⟨h01, h12, h02⟩

private theorem translated_triangle_sharp {p : ℝ} (hp : 1 ≤ p) :
    finitePBoundaryTransportCost p (fun _ : Fin 1 => ((0, 10) : ℝ × ℝ))
      (fun _ : Fin 1 => (2, 12)) =
    finitePBoundaryTransportCost p (fun _ : Fin 1 => ((0, 10) : ℝ × ℝ))
        (fun _ : Fin 1 => (1, 11)) +
      finitePBoundaryTransportCost p (fun _ : Fin 1 => ((1, 11) : ℝ × ℝ))
        (fun _ : Fin 1 => (2, 12)) := by
  obtain ⟨h01, h12, h02⟩ := translated_roots hp
  rw [h01, h12, h02]
  norm_num

private theorem translated_roots_two :
    finitePBoundaryTransportCost 2 (fun _ : Fin 1 => ((0, 10) : ℝ × ℝ))
      (fun _ : Fin 1 => (2, 12)) = 2 := (translated_roots (p := 2) (by norm_num)).2.2

private theorem translated_roots_three_halves :
    finitePBoundaryTransportCost (3 / 2) (fun _ : Fin 1 => ((0, 10) : ℝ × ℝ))
      (fun _ : Fin 1 => (2, 12)) = 2 :=
  (translated_roots (p := 3 / 2) (by norm_num)).2.2

private def positivePairs (i : Fin 2) : ℝ × ℝ := if i = 0 then (0, 2) else (1, 3)

private theorem permuted_zero {p : ℝ} (hp : 1 ≤ p) :
    finitePBoundaryTransportCost p (positivePairs ∘ Equiv.swap 0 1) positivePairs = 0 :=
  finitePBoundaryTransportCost_eq_zero_of_equiv hp _ _ (Equiv.swap 0 1) (fun _ => rfl)

private theorem permuted_presentations_differ : positivePairs ∘ Equiv.swap 0 1 ≠ positivePairs := by
  intro h
  have hzero := congrArg (fun f => f 0) h
  norm_num [positivePairs, Function.comp_def] at hzero

private theorem repeated_positive_cost {p : ℝ} (hp : 1 ≤ p) :
    finitePBoundaryTransportCost p (fun _ : Fin 2 => ((0, 2) : ℝ × ℝ))
      (fun _ : Unit => (0, 2)) ≠ 0 := by
  intro hz
  obtain ⟨e, _⟩ := (finitePBoundaryTransportCost_eq_zero_iff hp _ _
    (fun _ => by norm_num) (fun _ => by norm_num)).mp hz
  have hc := Fintype.card_congr e
  norm_num at hc

private theorem diagonal_to_empty_zero {p : ℝ} (hp : 1 ≤ p) :
    finitePBoundaryTransportCost p (fun _ : Unit => ((0, 0) : ℝ × ℝ))
      (Fin.elim0 : Fin 0 → ℝ × ℝ) = 0 := by
  rw [finitePBoundaryTransportCost_of_isEmpty_right]
  simp [diagonalCost, Real.zero_rpow (ne_of_gt (lt_of_lt_of_le zero_lt_one hp)),
    Real.zero_rpow (inv_ne_zero (ne_of_gt (lt_of_lt_of_le zero_lt_one hp)))]

private theorem diagonal_to_empty_has_no_equiv : ¬ Nonempty (Unit ≃ Fin 0) := by
  rintro ⟨e⟩
  exact Fin.elim0 (e ())

private theorem empty_root_at_zero :
    finitePBoundaryTransportCost 0 (Fin.elim0 : Fin 0 → ℝ × ℝ)
      (Fin.elim0 : Fin 0 → ℝ × ℝ) = 1 := by
  simp [finitePBoundaryTransportCost]

private theorem first_order_triangle
    {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) (z : K → ℝ × ℝ) :
    finiteFirstOrderBoundaryTransportCost x z ≤
      finiteFirstOrderBoundaryTransportCost x y + finiteFirstOrderBoundaryTransportCost y z := by
  simpa only [finitePBoundaryTransportCost_one] using
    finitePBoundaryTransportCost_triangle (p := 1) (by norm_num) x y z

end TDA.Persistence.FinitePMatchingCostLawsExamples
