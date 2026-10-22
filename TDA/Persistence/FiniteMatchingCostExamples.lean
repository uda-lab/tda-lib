import TDA.Persistence.PersistenceImageMatching

/-! Empty, repeated and one-point matching minima, and a PI application. -/

namespace TDA.Persistence.FiniteMatchingCostExamples

private def pairSingletons : OccurrenceMatching Unit Unit PEmpty.{1} PEmpty.{1} where
  finite _ := some ()
  finite_injective _ _ _ _ _ := Subsingleton.elim _ _
  essential := Equiv.refl _

private theorem singleton_cost_cases
    (M : OccurrenceMatching Unit Unit PEmpty.{1} PEmpty.{1}) (p q : ℝ × ℝ) :
    M.totalFiniteCost (fun _ => p) (fun _ => q) =
      match M.finite () with
      | none => (diagonalCost p).toReal + (diagonalCost q).toReal
      | some _ => (finitePairCost p q).toReal := by
  cases h : M.finite () with
  | none => simp [OccurrenceMatching.totalFiniteCost, h]
  | some j => cases j; simp [OccurrenceMatching.totalFiniteCost, h]

private theorem singleton_minimum (p q : ℝ × ℝ) :
    finiteFirstOrderMatchingCost (fun _ : Unit => p) (fun _ : Unit => q) =
      min (finitePairCost p q).toReal ((diagonalCost p).toReal + (diagonalCost q).toReal) := by
  apply le_antisymm
  · apply le_min
    · have h := finiteFirstOrderMatchingCost_le_totalFiniteCost
        (fun _ : Unit => p) (fun _ : Unit => q) pairSingletons
      simpa [OccurrenceMatching.totalFiniteCost, pairSingletons] using h
    · simpa using finiteFirstOrderMatchingCost_le_diagonalSum
        (fun _ : Unit => p) (fun _ : Unit => q)
  · apply (le_finiteFirstOrderMatchingCost_iff _ _ _).mpr
    intro M
    rw [singleton_cost_cases]
    cases M.finite ()
    · exact min_le_right _ _
    · exact min_le_left _ _

private theorem pairing_preferred :
    finiteFirstOrderMatchingCost (fun _ : Unit => ((0, 4) : ℝ × ℝ))
      (fun _ : Unit => (1, 5)) = 1 := by
  rw [singleton_minimum]
  norm_num [finitePairCost, diagonalCost]

private theorem deletion_preferred :
    finiteFirstOrderMatchingCost (fun _ : Unit => ((0, 2) : ℝ × ℝ))
      (fun _ : Unit => (10, 12)) = 2 := by
  rw [singleton_minimum]
  norm_num [finitePairCost, diagonalCost]

private theorem coincident_singletons_zero :
    finiteFirstOrderMatchingCost (fun _ : Unit => ((0, 2) : ℝ × ℝ))
      (fun _ : Unit => (0, 2)) = 0 := by
  rw [singleton_minimum]
  norm_num [finitePairCost, diagonalCost]

private theorem repeated_to_empty :
    finiteFirstOrderMatchingCost (fun _ : Fin 2 => ((0, 2) : ℝ × ℝ))
      (Fin.elim0 : Fin 0 → ℝ × ℝ) = 2 := by
  rw [finiteFirstOrderMatchingCost_of_isEmpty_right, Fin.sum_univ_two]
  norm_num [diagonalCost]

private theorem empty_minimum :
    finiteFirstOrderMatchingCost (Fin.elim0 : Fin 0 → ℝ × ℝ)
      (Fin.elim0 : Fin 0 → ℝ × ℝ) = 0 := by simp

private theorem near_singletons_image_bound {K : Type*} [Fintype K]
    {σ A B : ℝ} (hσ : 0 < σ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (w : PersistenceImage.Weight A B) (P : K → Set (ℝ × ℝ))
    (hm : ∀ k, MeasurableSet (P k))
    (hd : Pairwise (fun i j => Disjoint (P i) (P j))) :
    ‖PersistenceImage.image σ w P (fun _ : Unit => ((0, 4) : ℝ × ℝ)) -
      PersistenceImage.image σ w P (fun _ : Unit => (1, 5))‖ ≤
      PersistenceImage.stabilityConstant σ A B := by
  simpa only [pairing_preferred, mul_one] using
    PersistenceImage.norm_image_sub_le_finiteFirstOrderMatchingCost hσ hA hB w P hm hd
      (fun _ : Unit => ((0, 4) : ℝ × ℝ)) (fun _ : Unit => (1, 5))
      (fun _ => by norm_num) (fun _ => by norm_num)

end TDA.Persistence.FiniteMatchingCostExamples
