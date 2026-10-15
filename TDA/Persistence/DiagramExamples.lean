import TDA.Persistence.Diagram

namespace TDA.Persistence

private def reverseOne : (Fin 1 → ℚ × ℚ) × (Fin 0 → ℚ) :=
  (fun _ => (2, 1), Fin.elim0)
private def forwardOne : (Fin 1 → ℚ × ℚ) × (Fin 0 → ℚ) :=
  (fun _ => (1, 2), Fin.elim0)
private def diagonalZero : (Fin 1 → ℚ × ℚ) × (Fin 0 → ℚ) :=
  (fun _ => (0, 0), Fin.elim0)
private def diagonalOne : (Fin 1 → ℚ × ℚ) × (Fin 0 → ℚ) :=
  (fun _ => (1, 1), Fin.elim0)
private def distinctDiagonalList : (Fin 2 → ℚ × ℚ) × (Fin 0 → ℚ) :=
  (fun i => if i = 0 then (0, 0) else (1, 1), Fin.elim0)
private def reverseTwo : (Fin 2 → ℚ × ℚ) × (Fin 0 → ℚ) :=
  (fun _ => (2, 1), Fin.elim0)
private def mixed : (Fin 4 → ℚ × ℚ) × (Fin 2 → ℚ) :=
  (fun i => match i with
    | ⟨0, _⟩ => (0, 2)
    | ⟨1, _⟩ => (2, 1)
    | ⟨2, _⟩ => (1, 1)
    | _ => (0, 2), fun _ => 0)

private theorem empty_points :
    (orderedQ 0 0 ((Fin.elim0 : Fin 0 → ℚ × ℚ), (Fin.elim0 : Fin 0 → ℚ))).points = 0 := by
  decide
private theorem empty_alpha :
    (orderedQ 0 0 ((Fin.elim0 : Fin 0 → Empty × Empty), (Fin.elim0 : Fin 0 → Empty))).points = 0 := by
  decide
private theorem diagonal_zero_points : (orderedQ 1 0 diagonalZero).points = 0 := by
  decide
private theorem diagonal_one_points : (orderedQ 1 0 diagonalOne).points = 0 := by
  decide
private theorem distinct_diagonal_list_points :
    (orderedQ 2 0 distinctDiagonalList).points = 0 := by
  decide
private theorem distinct_diagonals_equal :
    orderedQ 1 0 diagonalZero = orderedQ 1 0 diagonalOne := by
  apply Diagram.ext
  rw [diagonal_zero_points, diagonal_one_points]

private theorem reversed_points :
    (orderedQ 1 0 reverseOne).points = {(2, (1 : WithTop ℚ))} := by
  decide
private theorem reversed_count :
    (orderedQ 1 0 reverseOne).points.count (2, (1 : WithTop ℚ)) = 1 := by
  decide
private theorem reversed_nonpositive : ¬(orderedQ 1 0 reverseOne).IsPositive := by
  rw [orderedQ_isPositive_iff]
  decide
private theorem reversed_ne_forward :
    orderedQ 1 0 reverseOne ≠ orderedQ 1 0 forwardOne := by
  intro h
  have hc := congrArg (fun D : Diagram ℚ => D.points.count (2, (1 : WithTop ℚ))) h
  have hforward : (orderedQ 1 0 forwardOne).points.count (2, (1 : WithTop ℚ)) = 0 := by
    decide
  rw [reversed_count, hforward] at hc
  omega
private theorem repeated_reversed_count :
    (orderedQ 2 0 reverseTwo).points.count (2, (1 : WithTop ℚ)) = 2 := by
  decide

private theorem mixed_points :
    (orderedQ 4 2 mixed).points =
      {(0, (2 : WithTop ℚ)), (0, (2 : WithTop ℚ)),
        (2, (1 : WithTop ℚ)), (0, (⊤ : WithTop ℚ)),
        (0, (⊤ : WithTop ℚ))} := by
  decide
private theorem mixed_forward_count :
    (orderedQ 4 2 mixed).points.count (0, (2 : WithTop ℚ)) = 2 := by
  decide
private theorem mixed_reverse_count :
    (orderedQ 4 2 mixed).points.count (2, (1 : WithTop ℚ)) = 1 := by
  decide
private theorem mixed_essential_count :
    (orderedQ 4 2 mixed).points.count (0, (⊤ : WithTop ℚ)) = 2 := by
  decide
private theorem mixed_diagonal_zero :
    (orderedQ 4 2 mixed).points.count (1, (1 : WithTop ℚ)) = 0 := by
  decide
private theorem mixed_nonpositive : ¬(orderedQ 4 2 mixed).IsPositive := by
  rw [orderedQ_isPositive_iff]
  decide

private def permutationFinite : Fin 2 → ℚ × ℚ :=
  fun i => if i = 0 then (0, 2) else (2, 1)
private def permutationEssential : Fin 2 → ℚ :=
  fun i => if i = 0 then 0 else 1
private theorem genuine_permutation :
    orderedQ 2 2 (permutationFinite ∘ Equiv.swap (0 : Fin 2) 1,
      permutationEssential ∘ Equiv.swap (0 : Fin 2) 1) =
    orderedQ 2 2 (permutationFinite, permutationEssential) := by
  exact orderedQ_perm 2 2 (Equiv.swap 0 1) (Equiv.swap 0 1)
    permutationFinite permutationEssential

private def positiveWithDiagonal : (Fin 2 → ℚ × ℚ) × (Fin 1 → ℚ) :=
  (fun i => if i = 0 then (0, 0) else (0, 2), fun _ => 0)
private theorem positive_points :
    (orderedQ 2 1 positiveWithDiagonal).points =
      {(0, (2 : WithTop ℚ)), (0, (⊤ : WithTop ℚ))} := by
  decide
private theorem positive_with_diagonal : (orderedQ 2 1 positiveWithDiagonal).IsPositive := by
  rw [orderedQ_isPositive_iff]
  decide
private theorem positive_weak_order :
    (∀ i, (positiveWithDiagonal.1 i).1 ≤ (positiveWithDiagonal.1 i).2) := by
  exact (orderedQ_isPositive_iff 2 1 positiveWithDiagonal).mp positive_with_diagonal
private theorem same_birth_finite_count :
    (orderedQ 2 1 positiveWithDiagonal).points.count (0, (2 : WithTop ℚ)) = 1 := by
  decide
private theorem same_birth_essential_count :
    (orderedQ 2 1 positiveWithDiagonal).points.count (0, (⊤ : WithTop ℚ)) = 1 := by
  decide
private theorem natural_birth_zero_essential :
    (orderedQ 0 1 ((Fin.elim0 : Fin 0 → ℕ × ℕ), (fun _ => 0 : Fin 1 → ℕ))).points =
      {(0, (⊤ : WithTop ℕ))} := by
  decide
end TDA.Persistence
