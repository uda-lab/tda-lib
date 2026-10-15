import TDA.Persistence.DiagramLaws

namespace TDA.Persistence

private def appendLeft : (Fin 3 → ℚ × ℚ) × (Fin 2 → ℚ) :=
  (![(0, 2), (2, 1), (1, 1)], ![0, 3])
private def appendRight : (Fin 3 → ℚ × ℚ) × (Fin 2 → ℚ) :=
  (![(2, 1), (0, 2), (7, 7)], ![0, 0])

private theorem append_mixed_reversed_essential :
    (orderedQ 6 4 (Fin.append appendLeft.1 appendRight.1,
      Fin.append appendLeft.2 appendRight.2)).points =
      (orderedQ 3 2 appendLeft).points + (orderedQ 3 2 appendRight).points := by
  exact orderedQ_append 3 2 3 2 appendLeft appendRight

private theorem append_mixed_counts :
    (orderedQ 6 4 (Fin.append appendLeft.1 appendRight.1,
      Fin.append appendLeft.2 appendRight.2)).points.count (0, (2 : WithTop ℚ)) = 2 ∧
    (orderedQ 6 4 (Fin.append appendLeft.1 appendRight.1,
      Fin.append appendLeft.2 appendRight.2)).points.count (2, (1 : WithTop ℚ)) = 2 ∧
    (orderedQ 6 4 (Fin.append appendLeft.1 appendRight.1,
      Fin.append appendLeft.2 appendRight.2)).points.count (0, (⊤ : WithTop ℚ)) = 3 ∧
    (orderedQ 6 4 (Fin.append appendLeft.1 appendRight.1,
      Fin.append appendLeft.2 appendRight.2)).points.count (3, (⊤ : WithTop ℚ)) = 1 ∧
    (orderedQ 6 4 (Fin.append appendLeft.1 appendRight.1,
      Fin.append appendLeft.2 appendRight.2)).points.count (1, (1 : WithTop ℚ)) = 0 := by
  decide

private def crossLeft : (Fin 4 → ℚ × ℚ) × (Fin 2 → ℚ) :=
  (![(0, 2), (2, 1), (1, 1), (0, 2)], ![0, 0])
private def crossRight : (Fin 5 → ℚ × ℚ) × (Fin 2 → ℚ) :=
  (![(9, 9), (0, 2), (0, 2), (2, 1), (-1, -1)], ![0, 0])
private def changedEssential : (Fin 5 → ℚ × ℚ) × (Fin 2 → ℚ) :=
  (crossRight.1, ![0, 1])

private theorem cross_dimension_parts :
    (Multiset.ofList (List.ofFn crossLeft.1)).filter (fun p => p.1 ≠ p.2) =
      (Multiset.ofList (List.ofFn crossRight.1)).filter (fun p => p.1 ≠ p.2) ∧
    Multiset.ofList (List.ofFn crossLeft.2) =
      Multiset.ofList (List.ofFn crossRight.2) := by
  decide

private theorem cross_dimension_equal : orderedQ 4 2 crossLeft = orderedQ 5 2 crossRight := by
  exact (orderedQ_eq_iff 4 2 5 2 crossLeft crossRight).mpr cross_dimension_parts

private theorem changed_essential_ne : orderedQ 4 2 crossLeft ≠ orderedQ 5 2 changedEssential := by
  intro h
  have he := (orderedQ_eq_iff 4 2 5 2 crossLeft changedEssential).mp h |>.2
  have hne : Multiset.ofList (List.ofFn crossLeft.2) ≠
      Multiset.ofList (List.ofFn changedEssential.2) := by decide
  exact hne he

private def independentDiagram : Diagram ℚ where
  points := {(0, (2 : WithTop ℚ)), (0, (2 : WithTop ℚ)),
    (2, (1 : WithTop ℚ)), (0, (⊤ : WithTop ℚ)), (0, (⊤ : WithTop ℚ))}
  offDiagonal := by
    intro p hp
    simp at hp
    rcases hp with h | h | h <;> rw [h] <;> norm_num

private theorem independent_representation :
    ∃ (m n : ℕ) (z : (Fin m → ℚ × ℚ) × (Fin n → ℚ)),
      orderedQ m n z = independentDiagram := by
  exact orderedQ_surjective independentDiagram

private def concreteWitness : (Fin 3 → ℚ × ℚ) × (Fin 2 → ℚ) :=
  (![(0, 2), (2, 1), (0, 2)], ![0, 0])
private theorem independent_concrete_witness :
    orderedQ 3 2 concreteWitness = independentDiagram := by
  apply Diagram.ext
  decide

private def deletionFinite : Fin 5 → ℚ × ℚ :=
  ![(0, 2), (2, 1), (7, 7), (0, 2), (9, 9)]
private def deletionEssential : Fin 2 → ℚ := ![0, 3]
private theorem delete_interior :
    orderedQ 4 2 (Fin.removeNth 2 deletionFinite, deletionEssential) =
      orderedQ 5 2 (deletionFinite, deletionEssential) := by
  exact orderedQ_zeroLength 4 2 deletionFinite deletionEssential 2 (by decide)
private theorem delete_interior_counts :
    (orderedQ 4 2 (Fin.removeNth 2 deletionFinite, deletionEssential)).points.count
      (0, (2 : WithTop ℚ)) = 2 ∧
    (orderedQ 4 2 (Fin.removeNth 2 deletionFinite, deletionEssential)).points.count
      (2, (1 : WithTop ℚ)) = 1 ∧
    (orderedQ 4 2 (Fin.removeNth 2 deletionFinite, deletionEssential)).points.count
      (0, (⊤ : WithTop ℚ)) = 1 ∧
    (orderedQ 4 2 (Fin.removeNth 2 deletionFinite, deletionEssential)).points.count
      (3, (⊤ : WithTop ℚ)) = 1 := by
  decide

private def singletonFinite : Fin 1 → ℚ × ℚ := fun _ => (0, 0)
private theorem singleton_to_empty :
    orderedQ 0 0 (Fin.removeNth 0 singletonFinite, (Fin.elim0 : Fin 0 → ℚ)) =
      orderedQ 1 0 (singletonFinite, Fin.elim0) := by
  exact orderedQ_zeroLength 0 0 singletonFinite Fin.elim0 0 (by decide)

private def independentEmpty {α : Type*} [LinearOrder α] : Diagram α where
  points := 0
  offDiagonal := by simp

private theorem empty_carrier_mechanism {α : Type*} [LinearOrder α] [IsEmpty α] :
    orderedQ 0 0 ((Fin.elim0 : Fin 0 → α × α), (Fin.elim0 : Fin 0 → α)) =
      independentEmpty := by
  apply Diagram.ext
  rfl

private theorem empty_carrier_representation :
    ∃ (m n : ℕ) (z : (Fin m → Empty × Empty) × (Fin n → Empty)),
      orderedQ m n z = independentEmpty := by
  exact orderedQ_surjective independentEmpty

private def twoReversed : (Fin 3 → ℚ × ℚ) × (Fin 1 → ℚ) :=
  (![(2, 1), (2, 1), (0, 2)], ![0])
private def changedReversed : (Fin 3 → ℚ × ℚ) × (Fin 1 → ℚ) :=
  (![(2, 1), (5, 5), (0, 2)], ![0])
private def droppedEssential : (Fin 4 → ℚ × ℚ) × (Fin 1 → ℚ) :=
  (crossLeft.1, ![0])

private theorem changed_reversed_ne : orderedQ 3 1 twoReversed ≠ orderedQ 3 1 changedReversed := by
  intro h
  have hf := (orderedQ_eq_iff 3 1 3 1 twoReversed changedReversed).mp h |>.1
  have hne : (Multiset.ofList (List.ofFn twoReversed.1)).filter (fun p => p.1 ≠ p.2) ≠
      (Multiset.ofList (List.ofFn changedReversed.1)).filter (fun p => p.1 ≠ p.2) := by decide
  exact hne hf

private theorem dropped_essential_ne : orderedQ 4 2 crossLeft ≠ orderedQ 4 1 droppedEssential := by
  intro h
  have he := (orderedQ_eq_iff 4 2 4 1 crossLeft droppedEssential).mp h |>.2
  have hne : Multiset.ofList (List.ofFn crossLeft.2) ≠
      Multiset.ofList (List.ofFn droppedEssential.2) := by decide
  exact hne he

private def diagonalZero : (Fin 1 → ℚ × ℚ) × (Fin 0 → ℚ) :=
  (![((0 : ℚ), 0)], Fin.elim0)
private def diagonalOne : (Fin 1 → ℚ × ℚ) × (Fin 0 → ℚ) :=
  (![((1 : ℚ), 1)], Fin.elim0)

private theorem nonorbit_diagonal_equal :
    orderedQ 1 0 diagonalZero = orderedQ 1 0 diagonalOne := by
  apply (orderedQ_eq_iff 1 0 1 0 diagonalZero diagonalOne).mpr
  decide

private theorem nonorbit_tuple_ne : diagonalZero ≠ diagonalOne := by
  decide

private theorem append_no_diagonal (a : ℚ) :
    (orderedQ 6 4 (Fin.append appendLeft.1 appendRight.1,
      Fin.append appendLeft.2 appendRight.2)).points.count
        (a, (a : WithTop ℚ)) = 0 := by
  rw [append_mixed_reversed_essential, Multiset.count_add]
  have hz (z : (Fin 3 → ℚ × ℚ) × (Fin 2 → ℚ)) :
      (orderedQ 3 2 z).points.count (a, (a : WithTop ℚ)) = 0 := by
    apply Multiset.count_eq_zero.mpr
    intro hm
    exact (orderedQ 3 2 z).offDiagonal _ hm (by rfl)
  simp [hz]

private def boundaryFinite : Fin 6 → ℚ × ℚ :=
  ![(7, 7), (0, 2), (2, 1), (8, 8), (0, 2), (9, 9)]

private theorem delete_first :
    orderedQ 5 2 (Fin.removeNth 0 boundaryFinite, deletionEssential) =
      orderedQ 6 2 (boundaryFinite, deletionEssential) := by
  exact orderedQ_zeroLength 5 2 boundaryFinite deletionEssential 0 (by decide)

private theorem delete_last :
    orderedQ 5 2 (Fin.removeNth 5 boundaryFinite, deletionEssential) =
      orderedQ 6 2 (boundaryFinite, deletionEssential) := by
  exact orderedQ_zeroLength 5 2 boundaryFinite deletionEssential 5 (by decide)

private theorem boundary_deletion_counts :
    (orderedQ 5 2 (Fin.removeNth 0 boundaryFinite, deletionEssential)).points.count
      (0, (2 : WithTop ℚ)) = 2 ∧
    (orderedQ 5 2 (Fin.removeNth 5 boundaryFinite, deletionEssential)).points.count
      (2, (1 : WithTop ℚ)) = 1 ∧
    (orderedQ 5 2 (Fin.removeNth 0 boundaryFinite, deletionEssential)).points.count
      (0, (⊤ : WithTop ℚ)) = 1 ∧
    (orderedQ 5 2 (Fin.removeNth 5 boundaryFinite, deletionEssential)).points.count
      (3, (⊤ : WithTop ℚ)) = 1 := by
  rw [delete_first, delete_last]
  decide

private def independentFiniteOnly : Diagram ℚ where
  points := {(0, (2 : WithTop ℚ)), (2, (1 : WithTop ℚ)), (0, (2 : WithTop ℚ))}
  offDiagonal := by
    intro p hp
    simp at hp
    rcases hp with h | h | h <;> rw [h] <;> norm_num

private def independentEssentialOnly : Diagram ℚ where
  points := {(0, (⊤ : WithTop ℚ)), (0, (⊤ : WithTop ℚ)), (3, (⊤ : WithTop ℚ))}
  offDiagonal := by
    intro p hp
    simp at hp
    rcases hp with h | h <;> subst p <;> simp

private theorem finite_only_representation :
    (∃ (m n : ℕ) (z : (Fin m → ℚ × ℚ) × (Fin n → ℚ)),
      orderedQ m n z = independentFiniteOnly) ∧
    orderedQ 3 0 (![(0, 2), (2, 1), (0, 2)], Fin.elim0) = independentFiniteOnly := by
  constructor
  · exact orderedQ_surjective independentFiniteOnly
  · apply Diagram.ext
    decide

private theorem essential_only_representation :
    (∃ (m n : ℕ) (z : (Fin m → ℚ × ℚ) × (Fin n → ℚ)),
      orderedQ m n z = independentEssentialOnly) ∧
    orderedQ 0 3 (Fin.elim0, ![0, 0, 3]) = independentEssentialOnly := by
  constructor
  · exact orderedQ_surjective independentEssentialOnly
  · apply Diagram.ext
    decide

private def allDiagonalA : (Fin 3 → ℚ × ℚ) × (Fin 0 → ℚ) :=
  (![(1, 1), (9, 9), (-2, -2)], Fin.elim0)
private def allDiagonalB : (Fin 2 → ℚ × ℚ) × (Fin 0 → ℚ) :=
  (![(4, 4), (-7, -7)], Fin.elim0)

private theorem differing_diagonal_empty :
    orderedQ 3 0 allDiagonalA = orderedQ 2 0 allDiagonalB ∧
    orderedQ 3 0 allDiagonalA = independentEmpty ∧
    orderedQ 0 0 ((Fin.elim0 : Fin 0 → ℚ × ℚ), (Fin.elim0 : Fin 0 → ℚ)) = independentEmpty := by
  constructor
  · exact (orderedQ_eq_iff 3 0 2 0 allDiagonalA allDiagonalB).mpr (by decide)
  constructor <;> apply Diagram.ext <;> decide

private theorem empty_type_representation {α : Type*} [LinearOrder α] [IsEmpty α] :
    ∃ (m n : ℕ) (z : (Fin m → α × α) × (Fin n → α)),
      orderedQ m n z = independentEmpty := by
  exact orderedQ_surjective independentEmpty

end TDA.Persistence
