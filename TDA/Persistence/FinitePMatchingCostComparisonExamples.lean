import TDA.Persistence.FinitePMatchingCostComparison

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

end TDA.Persistence.FinitePMatchingCostComparisonExamples
