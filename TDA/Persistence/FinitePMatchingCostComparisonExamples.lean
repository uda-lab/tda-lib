import TDA.Persistence.FinitePMatchingCostComparison
import TDA.Persistence.FinitePBoundaryTransportExamples

/-! Empty inputs, a sharp multiplicity factor and a fractional-plan boundary. -/

noncomputable section
namespace TDA.Persistence.FinitePMatchingCostComparisonExamples

private def repeated : Fin 2 → ℝ × ℝ := fun _ => (0, 2)

private theorem repeated_root (p : ℝ) :
    finitePBoundaryTransportCost p repeated (Fin.elim0 : Fin 0 → ℝ × ℝ) =
      (2 : ℝ) ^ p⁻¹ := by
  rw [finitePBoundaryTransportCost_eq_matchingCost, finitePMatchingCost_of_isEmpty_right]
  norm_num [repeated, diagonalCost, Fin.sum_univ_two]

private theorem repeated_first :
    finiteFirstOrderBoundaryTransportCost repeated (Fin.elim0 : Fin 0 → ℝ × ℝ) = 2 := by
  rw [finiteFirstOrderBoundaryTransportCost_eq_matchingCost,
    finiteFirstOrderMatchingCost_of_isEmpty_right]
  norm_num [repeated, diagonalCost, Fin.sum_univ_two]

/-- Two equal bars retain two deletion charges and attain the upper factor. -/
private theorem repeated_upper_sharp (p : ℝ) :
    finiteFirstOrderBoundaryTransportCost repeated (Fin.elim0 : Fin 0 → ℝ × ℝ) =
      (2 : ℝ) ^ (1 - p⁻¹) *
        finitePBoundaryTransportCost p repeated (Fin.elim0 : Fin 0 → ℝ × ℝ) := by
  rw [repeated_first, repeated_root, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  simp

private theorem repeated_three_halves :
    finitePBoundaryTransportCost (3 / 2) repeated (Fin.elim0 : Fin 0 → ℝ × ℝ) =
        (2 : ℝ) ^ (2 / 3 : ℝ) ∧
      finiteFirstOrderBoundaryTransportCost repeated (Fin.elim0 : Fin 0 → ℝ × ℝ) =
        (2 : ℝ) ^ (1 / 3 : ℝ) *
          finitePBoundaryTransportCost (3 / 2) repeated (Fin.elim0 : Fin 0 → ℝ × ℝ) := by
  constructor
  · norm_num only [repeated_root, inv_div, one_mul]
  · convert repeated_upper_sharp (3 / 2) using 2; norm_num

/-- N=0 gives zero on both sides, including the factor 0^0 at p=1. -/
private theorem empty_comparison {p : ℝ} (hp : 1 ≤ p) :
    finitePBoundaryTransportCost p (Fin.elim0 : Fin 0 → ℝ × ℝ)
        (Fin.elim0 : Fin 0 → ℝ × ℝ) = 0 ∧
      finiteFirstOrderBoundaryTransportCost (Fin.elim0 : Fin 0 → ℝ × ℝ)
        (Fin.elim0 : Fin 0 → ℝ × ℝ) = (0 : ℝ) ^ (1 - p⁻¹) * 0 := by
  constructor
  · exact finitePBoundaryTransportCost_empty hp _ _
  · simp

private theorem first_order_recovery (x : Fin 2 → ℝ × ℝ) (y : Fin 3 → ℝ × ℝ) :
    finitePBoundaryTransportCost 1 x y = finiteFirstOrderBoundaryTransportCost x y ∧
      ((Fintype.card (Fin 2) + Fintype.card (Fin 3) : ℕ) : ℝ) ^ (1 - (1 : ℝ)⁻¹) = 1 := by
  simp

private def threeQuarterPlan : FiniteBoundaryPlan (Fin 1) (Fin 1) where
  mass _ _ := 3 / 4
  nonneg _ _ := by norm_num
  row_le_one _ := by norm_num
  col_le_one _ := by norm_num

/-- The lower optimum comparison cannot be asserted for each fractional candidate:
here C₁=C₂=1/2, so C₁²<C₂ even though the common optimum is zero. -/
private theorem fractional_candidate_square_lt_power :
    (threeQuarterPlan.powerCost 1 (fun _ => (0, 2)) (fun _ => (0, 2))) ^ 2 <
      threeQuarterPlan.powerCost 2 (fun _ => (0, 2)) (fun _ => (0, 2)) := by
  norm_num [threeQuarterPlan, FiniteBoundaryPlan.powerCost, FiniteBoundaryPlan.linearCost,
    FiniteBoundaryPlan.deletionMass, FiniteBoundaryPlan.insertionMass,
    finitePairCost, diagonalCost, Real.rpow_two]

/-- The four comparisons always concern the two optimized costs. -/
private def comparisonBounds {I J : Type*} [Fintype I] [Fintype J]
    (r s : ℝ) (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) : Prop :=
  finitePMatchingCost s x y ≤ finitePMatchingCost r x y ∧
  finitePMatchingCost r x y ≤
    ((Fintype.card I + Fintype.card J : ℕ) : ℝ) ^ (r⁻¹ - s⁻¹) *
      finitePMatchingCost s x y ∧
  finitePBoundaryTransportCost s x y ≤ finitePBoundaryTransportCost r x y ∧
  finitePBoundaryTransportCost r x y ≤
    ((Fintype.card I + Fintype.card J : ℕ) : ℝ) ^ (r⁻¹ - s⁻¹) *
      finitePBoundaryTransportCost s x y

private theorem optimized_comparisons {I J : Type*} [Fintype I] [Fintype J]
    {r s : ℝ} (hr : 1 ≤ r) (hrs : r ≤ s) (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    comparisonBounds r s x y :=
  ⟨finitePMatchingCost_le_of_exponent_le hr hrs x y,
    finitePMatchingCost_le_card_rpow_mul_of_exponent_le hr hrs x y,
    finitePBoundaryTransportCost_le_of_exponent_le hr hrs x y,
    finitePBoundaryTransportCost_le_card_rpow_mul_of_exponent_le hr hrs x y⟩

private def emptyFamily : Fin 0 → ℝ × ℝ := Fin.elim0

/-- Empty families exercise arbitrary real exponents and the actual two optima. -/
private theorem empty_two_exponents {r s : ℝ} (hr : 1 ≤ r) (hrs : r ≤ s) :
    finitePMatchingCost r emptyFamily emptyFamily = 0 ∧
    finitePMatchingCost s emptyFamily emptyFamily = 0 ∧
    finitePBoundaryTransportCost r emptyFamily emptyFamily = 0 ∧
    finitePBoundaryTransportCost s emptyFamily emptyFamily = 0 ∧
    comparisonBounds r s emptyFamily emptyFamily := by
  exact ⟨finitePMatchingCost_empty hr _ _, finitePMatchingCost_empty (hr.trans hrs) _ _,
    finitePBoundaryTransportCost_empty hr _ _,
    finitePBoundaryTransportCost_empty (hr.trans hrs) _ _,
    optimized_comparisons hr hrs _ _⟩

private theorem empty_equal_three_halves :
    finitePMatchingCost (3 / 2) emptyFamily emptyFamily = 0 ∧
    finitePBoundaryTransportCost (3 / 2) emptyFamily emptyFamily = 0 ∧
    (0 : ℝ) ^ (((3 / 2 : ℝ)⁻¹) - (3 / 2 : ℝ)⁻¹) = 1 ∧
    comparisonBounds (3 / 2) (3 / 2) emptyFamily emptyFamily := by
  exact ⟨finitePMatchingCost_empty (by norm_num) _ _,
    finitePBoundaryTransportCost_empty (by norm_num) _ _, by simp,
    optimized_comparisons (by norm_num) le_rfl _ _⟩

/-- Equal exponents require neither positive cardinality nor positive distance. -/
private theorem equal_exponents {I J : Type*} [Fintype I] [Fintype J]
    {r : ℝ} (hr : 1 ≤ r) (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    ((Fintype.card I + Fintype.card J : ℕ) : ℝ) ^ (r⁻¹ - r⁻¹) = 1 ∧
    comparisonBounds r r x y := by
  exact ⟨by simp, optimized_comparisons hr le_rfl x y⟩

private def oneBar : Fin 1 → ℝ × ℝ := fun _ => (0, 2)

private theorem oneBar_positive (i : Fin 1) : (oneBar i).1 < (oneBar i).2 := by
  norm_num [oneBar]

/-- Deletion and insertion orientations each have one unit charge. -/
private theorem one_bar_roots (t : ℝ) :
    finitePMatchingCost t oneBar emptyFamily = 1 ∧
    finitePMatchingCost t emptyFamily oneBar = 1 ∧
    finitePBoundaryTransportCost t oneBar emptyFamily = 1 ∧
    finitePBoundaryTransportCost t emptyFamily oneBar = 1 := by
  simp only [finitePBoundaryTransportCost_eq_matchingCost,
    finitePMatchingCost_of_isEmpty_right, finitePMatchingCost_of_isEmpty_left]
  norm_num [oneBar, diagonalCost]

private theorem one_bar_two_exponents :
    comparisonBounds (3 / 2) 3 oneBar emptyFamily ∧
    comparisonBounds (3 / 2) 3 emptyFamily oneBar ∧
    (1 : ℝ) ^ (((3 / 2 : ℝ)⁻¹) - (3 : ℝ)⁻¹) = 1 ∧
    finitePMatchingCost (3 / 2) oneBar emptyFamily = finitePMatchingCost 3 oneBar emptyFamily ∧
    finitePBoundaryTransportCost (3 / 2) oneBar emptyFamily =
      (1 : ℝ) ^ (((3 / 2 : ℝ)⁻¹) - (3 : ℝ)⁻¹) *
        finitePBoundaryTransportCost 3 oneBar emptyFamily ∧
    finitePMatchingCost (3 / 2) emptyFamily oneBar = finitePMatchingCost 3 emptyFamily oneBar ∧
    finitePBoundaryTransportCost (3 / 2) emptyFamily oneBar =
      (1 : ℝ) ^ (((3 / 2 : ℝ)⁻¹) - (3 : ℝ)⁻¹) *
        finitePBoundaryTransportCost 3 emptyFamily oneBar := by
  refine ⟨optimized_comparisons (by norm_num) (by norm_num) _ _,
    optimized_comparisons (by norm_num) (by norm_num) _ _, by simp, ?_⟩
  simp only [(one_bar_roots (3 / 2)).1, (one_bar_roots 3).1,
    (one_bar_roots (3 / 2)).2.1, (one_bar_roots 3).2.1,
    (one_bar_roots (3 / 2)).2.2.1, (one_bar_roots 3).2.2.1,
    (one_bar_roots (3 / 2)).2.2.2, (one_bar_roots 3).2.2.2,
    Real.one_rpow, one_mul, and_self]

private theorem repeated_positive (i : Fin 2) : (repeated i).1 < (repeated i).2 := by
  norm_num [repeated]

private theorem repeated_both_roots (t : ℝ) :
    finitePMatchingCost t repeated emptyFamily = (2 : ℝ) ^ t⁻¹ ∧
    finitePBoundaryTransportCost t repeated emptyFamily = (2 : ℝ) ^ t⁻¹ := by
  have h := repeated_root t
  exact ⟨by simpa only [emptyFamily, finitePBoundaryTransportCost_eq_matchingCost] using h, h⟩

/-- Distinct labels with identical coordinates attain the two-exponent cardinal bound. -/
private theorem repeated_two_exponents_sharp :
    finitePMatchingCost (3 / 2) repeated emptyFamily = (2 : ℝ) ^ (2 / 3 : ℝ) ∧
    finitePMatchingCost 3 repeated emptyFamily = (2 : ℝ) ^ (1 / 3 : ℝ) ∧
    finitePBoundaryTransportCost (3 / 2) repeated emptyFamily = (2 : ℝ) ^ (2 / 3 : ℝ) ∧
    finitePBoundaryTransportCost 3 repeated emptyFamily = (2 : ℝ) ^ (1 / 3 : ℝ) ∧
    (2 : ℝ) ^ (((3 / 2 : ℝ)⁻¹) - (3 : ℝ)⁻¹) = (2 : ℝ) ^ (1 / 3 : ℝ) ∧
    finitePMatchingCost (3 / 2) repeated emptyFamily =
      (2 : ℝ) ^ (1 / 3 : ℝ) * finitePMatchingCost 3 repeated emptyFamily ∧
    finitePBoundaryTransportCost (3 / 2) repeated emptyFamily =
      (2 : ℝ) ^ (1 / 3 : ℝ) * finitePBoundaryTransportCost 3 repeated emptyFamily ∧
    comparisonBounds (3 / 2) 3 repeated emptyFamily := by
  have hsharp : (2 : ℝ) ^ ((3 / 2 : ℝ)⁻¹) =
      (2 : ℝ) ^ (1 / 3 : ℝ) * (2 : ℝ) ^ ((3 : ℝ)⁻¹) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
    norm_num
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_,
    optimized_comparisons (by norm_num) (by norm_num) _ _⟩
  · norm_num only [(repeated_both_roots (3 / 2)).1, inv_div, one_mul]
  · simpa only [one_div] using (repeated_both_roots 3).1
  · norm_num only [(repeated_both_roots (3 / 2)).2, inv_div, one_mul]
  · simpa only [one_div] using (repeated_both_roots 3).2
  · norm_num
  · simpa only [(repeated_both_roots (3 / 2)).1, (repeated_both_roots 3).1] using hsharp
  · simpa only [(repeated_both_roots (3 / 2)).2, (repeated_both_roots 3).2] using hsharp

private def switchTarget : Fin 1 → ℝ × ℝ := fun _ => (3 / 2, 7 / 2)

private theorem switchTarget_positive (j : Fin 1) :
    (switchTarget j).1 < (switchTarget j).2 := by norm_num [switchTarget]

private theorem switch_roots :
    finitePMatchingCost 1 oneBar switchTarget = 3 / 2 ∧
    finitePMatchingCost 2 oneBar switchTarget = Real.sqrt 2 ∧
    finitePBoundaryTransportCost 1 oneBar switchTarget = 3 / 2 ∧
    finitePBoundaryTransportCost 2 oneBar switchTarget = Real.sqrt 2 := by
  have h1 : finitePBoundaryTransportCost 1 oneBar switchTarget = 3 / 2 := by
    unfold oneBar switchTarget
    rw [finitePBoundaryTransportCost, FinitePBoundaryTransportExamples.switch_power_one]
    norm_num
  have h2 : finitePBoundaryTransportCost 2 oneBar switchTarget = Real.sqrt 2 := by
    unfold oneBar switchTarget
    rw [finitePBoundaryTransportCost, FinitePBoundaryTransportExamples.switch_power_two]
    norm_num [Real.sqrt_eq_rpow]
  exact ⟨by simpa only [finitePBoundaryTransportCost_eq_matchingCost] using h1,
    by simpa only [finitePBoundaryTransportCost_eq_matchingCost] using h2, h1, h2⟩

/-- The pairing optimizer at one loses to deleting both at two. -/
private theorem switch_optimizers_and_comparison :
    FinitePBoundaryTransportExamples.pairSingletons.totalFinitePowerCost 1 oneBar switchTarget =
      finitePowerBoundaryTransportCost 1 oneBar switchTarget ∧
    finitePowerBoundaryTransportCost 2 oneBar switchTarget <
      FinitePBoundaryTransportExamples.pairSingletons.totalFinitePowerCost 2 oneBar switchTarget ∧
    (FiniteBoundaryPlan.zero : FiniteBoundaryPlan (Fin 1) (Fin 1)).powerCost 2 oneBar switchTarget =
      finitePowerBoundaryTransportCost 2 oneBar switchTarget ∧
    comparisonBounds 1 2 oneBar switchTarget :=
  ⟨FinitePBoundaryTransportExamples.optimizer_changes_with_exponent.1,
    FinitePBoundaryTransportExamples.optimizer_changes_with_exponent.2,
    FinitePBoundaryTransportExamples.deleting_both_optimal_at_two,
    optimized_comparisons le_rfl (by norm_num) _ _⟩

private def mixedSource : Fin 2 → ℝ × ℝ := ![(0, 2), (10, 12)]
private def mixedTarget : Fin 2 → ℝ × ℝ := ![(1, 3), (20, 24)]

private theorem mixed_positive :
    (∀ i, (mixedSource i).1 < (mixedSource i).2) ∧
    (∀ j, (mixedTarget j).1 < (mixedTarget j).2) := by
  constructor <;> intro i <;> fin_cases i <;> norm_num [mixedSource, mixedTarget]

private def mixedMatching : OccurrenceMatching (Fin 2) (Fin 2) PEmpty.{1} PEmpty.{1} where
  finite i := if i = 0 then some 0 else none
  finite_injective i i' j hi hi' := by
    by_cases h : i = 0
    · by_cases h' : i' = 0
      · exact h.trans h'.symm
      · simp [h'] at hi'
    · simp [h] at hi
  essential := Equiv.refl _

/-- One pair, one deletion and one insertion are all retained in the same sum. -/
private theorem mixed_charges_and_power (t : ℝ) :
    (finitePairCost (mixedSource 0) (mixedTarget 0)).toReal = 1 ∧
    (diagonalCost (mixedSource 1)).toReal = 1 ∧
    (diagonalCost (mixedTarget 1)).toReal = 2 ∧
    mixedMatching.finite 0 = some 0 ∧ mixedMatching.finite 1 = none ∧
    mixedMatching.totalFinitePowerCost t mixedSource mixedTarget = 2 + (2 : ℝ) ^ t := by
  norm_num [mixedSource, mixedTarget, mixedMatching, OccurrenceMatching.totalFinitePowerCost,
    OccurrenceMatching.totalBoundaryCost, Fin.sum_univ_two, Fin.exists_fin_succ,
    finitePairCost, diagonalCost]

private theorem mixed_square_and_comparison :
    mixedMatching.totalFinitePowerCost 2 mixedSource mixedTarget = 6 ∧
    comparisonBounds (3 / 2) 3 mixedSource mixedTarget := by
  refine ⟨?_, optimized_comparisons (by norm_num) (by norm_num) _ _⟩
  rw [(mixed_charges_and_power 2).2.2.2.2.2, Real.rpow_two]
  norm_num

private def farTarget : Fin 1 → ℝ × ℝ := fun _ => (6, 8)

private theorem farTarget_positive (j : Fin 1) :
    (farTarget j).1 < (farTarget j).2 := by norm_num [farTarget]

/-- Linear half masses produce 4 and 19, before taking their respective roots. -/
private theorem half_plan_nonzero_costs :
    (finitePairCost (oneBar 0) (farTarget 0)).toReal = 6 ∧
    (diagonalCost (oneBar 0)).toReal = 1 ∧
    (diagonalCost (farTarget 0)).toReal = 1 ∧
    FinitePBoundaryTransportExamples.halfPlan.deletionMass 0 = 1 / 2 ∧
    FinitePBoundaryTransportExamples.halfPlan.insertionMass 0 = 1 / 2 ∧
    FinitePBoundaryTransportExamples.halfPlan.powerCost 1 oneBar farTarget = 4 ∧
    FinitePBoundaryTransportExamples.halfPlan.powerCost 2 oneBar farTarget = 19 := by
  norm_num [oneBar, farTarget, FinitePBoundaryTransportExamples.halfPlan,
    FiniteBoundaryPlan.powerCost, FiniteBoundaryPlan.linearCost,
    FiniteBoundaryPlan.deletionMass, FiniteBoundaryPlan.insertionMass,
    finitePairCost, diagonalCost, Real.rpow_two]

private theorem half_plan_root_increases :
    FinitePBoundaryTransportExamples.halfPlan.powerCost 2 oneBar farTarget ^ (2 : ℝ)⁻¹ =
      Real.sqrt 19 ∧
    FinitePBoundaryTransportExamples.halfPlan.powerCost 1 oneBar farTarget <
      FinitePBoundaryTransportExamples.halfPlan.powerCost 2 oneBar farTarget ^ (2 : ℝ)⁻¹ := by
  rw [half_plan_nonzero_costs.2.2.2.2.2.1, half_plan_nonzero_costs.2.2.2.2.2.2]
  constructor
  · norm_num [Real.sqrt_eq_rpow]
  · rw [show (2 : ℝ)⁻¹ = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow]
    exact (Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 4)).mpr (by norm_num)

/-- The actual optima still decrease, despite the half-plan counterexample. -/
private theorem far_optimized_roots :
    finitePMatchingCost 1 oneBar farTarget = 2 ∧
    finitePMatchingCost 2 oneBar farTarget = Real.sqrt 2 ∧
    finitePBoundaryTransportCost 1 oneBar farTarget = 2 ∧
    finitePBoundaryTransportCost 2 oneBar farTarget = Real.sqrt 2 ∧
    comparisonBounds 1 2 oneBar farTarget := by
  have h1 : finitePMatchingCost 1 oneBar farTarget = 2 := by
    unfold oneBar farTarget
    rw [finitePMatchingCost, finitePowerMatchingCost_singleton]
    norm_num [finitePairCost, diagonalCost]
  have h2 : finitePMatchingCost 2 oneBar farTarget = Real.sqrt 2 := by
    unfold oneBar farTarget
    rw [finitePMatchingCost, finitePowerMatchingCost_singleton]
    norm_num [finitePairCost, diagonalCost, Real.rpow_two, Real.sqrt_eq_rpow]
  exact ⟨h1, h2, by simpa only [finitePBoundaryTransportCost_eq_matchingCost] using h1,
    by simpa only [finitePBoundaryTransportCost_eq_matchingCost] using h2,
    optimized_comparisons le_rfl (by norm_num) _ _⟩

end TDA.Persistence.FinitePMatchingCostComparisonExamples
