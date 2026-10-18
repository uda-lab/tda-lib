import TDA.Persistence.FinitePCostSimilarity

/-! Degenerate scales, negative diagonal shifts and a plane-translation counterexample. -/

noncomputable section
namespace TDA.Persistence.FinitePCostSimilarityExamples

private def repeated : Fin 2 → ℝ × ℝ := fun _ => (0, 2)

private theorem repeated_root (p : ℝ) :
    finitePBoundaryTransportCost p repeated (Fin.elim0 : Fin 0 → ℝ × ℝ) =
      (2 : ℝ) ^ p⁻¹ := by
  rw [finitePBoundaryTransportCost_eq_matchingCost, finitePMatchingCost_of_isEmpty_right]
  norm_num [repeated, diagonalCost, Fin.sum_univ_two]

/-- Births can become negative while every lifetime and occurrence charge is preserved. -/
private theorem negative_diagonal_shift (p : ℝ) :
    finitePBoundaryTransportCost p (fun _ : Fin 2 => ((-5, -3) : ℝ × ℝ))
      (Fin.elim0 : Fin 0 → ℝ × ℝ) = (2 : ℝ) ^ p⁻¹ := by
  have h := finitePBoundaryTransportCost_translate p repeated
    (Fin.elim0 : Fin 0 → ℝ × ℝ) (-5)
  have he : Prod.map (· + (-5 : ℝ)) (· + (-5 : ℝ)) ∘
      (Fin.elim0 : Fin 0 → ℝ × ℝ) = Fin.elim0 := by
    funext i
    exact Fin.elim0 i
  rw [he, repeated_root] at h
  norm_num [repeated, Function.comp_def, Prod.map] at h
  exact h

/-- Multiplicity is retained at a nonintegral exponent and a scale below one. -/
private theorem repeated_three_halves_half_scale :
    finitePBoundaryTransportCost (3 / 2) (fun _ : Fin 2 => ((0, 1) : ℝ × ℝ))
      (Fin.elim0 : Fin 0 → ℝ × ℝ) = (1 / 2 : ℝ) * (2 : ℝ) ^ (2 / 3 : ℝ) := by
  have h := finitePBoundaryTransportCost_scale (p := 3 / 2) (by norm_num) repeated
    (Fin.elim0 : Fin 0 → ℝ × ℝ) (a := 1 / 2) (by norm_num)
  norm_num [scaleFinitePair, repeated, Function.comp_def, repeated_root] at h ⊢
  exact h

/-- Collapsing both inputs to the diagonal gives zero even with different label counts. -/
private theorem zero_scale {p : ℝ} (hp : 1 ≤ p)
    (x : Fin 2 → ℝ × ℝ) (y : Fin 3 → ℝ × ℝ) :
    finitePBoundaryTransportCost p (scaleFinitePair 0 ∘ x) (scaleFinitePair 0 ∘ y) = 0 := by
  rw [finitePBoundaryTransportCost_scale hp x y (le_refl 0), zero_mul]

private theorem empty_inputs {p : ℝ} (hp : 1 ≤ p) (t : ℝ) {a : ℝ} (ha : 0 ≤ a) :
    finitePBoundaryTransportCost p
        (Prod.map (· + t) (· + t) ∘ (Fin.elim0 : Fin 0 → ℝ × ℝ))
        (Prod.map (· + t) (· + t) ∘ (Fin.elim0 : Fin 0 → ℝ × ℝ)) = 0 ∧
      finitePBoundaryTransportCost p
        (scaleFinitePair a ∘ (Fin.elim0 : Fin 0 → ℝ × ℝ))
        (scaleFinitePair a ∘ (Fin.elim0 : Fin 0 → ℝ × ℝ)) = 0 := by
  constructor
  · rw [finitePBoundaryTransportCost_translate]
    exact finitePBoundaryTransportCost_empty hp _ _
  · rw [finitePBoundaryTransportCost_scale hp _ _ ha,
      finitePBoundaryTransportCost_empty hp, mul_zero]

private theorem first_order_scaling :
    finitePBoundaryTransportCost 1 (scaleFinitePair 3 ∘ repeated)
      (Fin.elim0 : Fin 0 → ℝ × ℝ) = 6 := by
  have h := finitePBoundaryTransportCost_scale (p := 1) (by norm_num) repeated
    (Fin.elim0 : Fin 0 → ℝ × ℝ) (a := 3) (by norm_num)
  norm_num [scaleFinitePair, repeated, Function.comp_def, repeated_root] at h ⊢

/-- A common vertical shift keeps these lifetimes positive but changes deletion cost. -/
private theorem vertical_shift_changes_cost :
    finitePBoundaryTransportCost 1 (fun _ : Fin 1 => ((0, 2) : ℝ × ℝ))
        (Fin.elim0 : Fin 0 → ℝ × ℝ) = 1 ∧
      finitePBoundaryTransportCost 1 (fun _ : Fin 1 => ((0, 4) : ℝ × ℝ))
        (Fin.elim0 : Fin 0 → ℝ × ℝ) = 2 := by
  constructor <;>
    rw [finitePBoundaryTransportCost_eq_matchingCost,
      finitePMatchingCost_of_isEmpty_right] <;>
    norm_num [diagonalCost]

end TDA.Persistence.FinitePCostSimilarityExamples
