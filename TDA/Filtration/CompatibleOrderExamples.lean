import TDA.Filtration.CompatibleOrder

set_option autoImplicit false

/-!
# Executable examples for canonical compatible face orders

These fixtures exercise the exact order produced by the public constructor, including empty
presentations, tied grades, grade priority, and the colex tie-breaker. The final fixture is a
monotone-grade bijection that violates proper-face precedence.
-/

namespace TDA.Filtration.CompatibleOrderExamples

universe w

open TDA.Simplicial
open TDA.Simplicial.FiniteComplex
open CompatibleOrder

private def empty0 : FiniteComplex 0 where
  faces := ∅
  nonempty := by decide
  downClosed := by decide

private def empty3 : FiniteComplex 3 where
  faces := ∅
  nonempty := by decide
  downClosed := by decide

private def emptyFilter {n : ℕ} (C : FiniteComplex n)
    (h : C.faces = ∅) (α : Type w) [LinearOrder α] :
    FilterFunction C.toPre α where
  value := fun s => by
    have hs : s.val ∈ C.faces := s.property
    rw [h] at hs
    simp at hs
  mono := by
    intro s t _
    have hs : s.val ∈ C.faces := s.property
    rw [h] at hs

private def emptyVoidFilter : FilterFunction empty3.toPre Empty :=
  emptyFilter empty3 rfl Empty

private def singleton3 : FiniteComplex 3 where
  faces := {{0}}
  nonempty := by decide
  downClosed := by decide

private def edge3 : FiniteComplex 3 where
  faces := {{0}, {1}, {0, 1}}
  nonempty := by decide
  downClosed := by decide

private def triangle3 : FiniteComplex 3 where
  faces := {{0}, {1}, {2}, {0, 1}, {0, 2}, {1, 2}, {0, 1, 2}}
  nonempty := by decide
  downClosed := by decide

private def disjointEdges4 : FiniteComplex 4 where
  faces := {{0}, {1}, {0, 1}, {2}, {3}, {2, 3}}
  nonempty := by decide
  downClosed := by decide

private def crossedEdges4 : FiniteComplex 4 where
  faces := {{0}, {1}, {2}, {3}, {0, 3}, {1, 2}}
  nonempty := by decide
  downClosed := by decide

private def constantFilter {n : ℕ} (C : FiniteComplex n) (v : ℤ) :
    FilterFunction C.toPre ℤ where
  value := fun _ => v
  mono := by intros; exact le_rfl

private def edgeVariableFilter : FilterFunction edge3.toPre ℤ where
  value := fun s => if s.val = ({1} : Finset (Fin 3)) then 0 else 5
  mono := by
    intro s t h
    by_cases hs : s.val = ({1} : Finset (Fin 3))
    · simp only [hs, ↓reduceIte]
      split_ifs <;> omega
    by_cases ht : t.val = ({1} : Finset (Fin 3))
    · have hsne : s.val.Nonempty := edge3.nonempty s.val s.property
      have hst : s.val = t.val :=
        Finset.eq_of_subset_of_card_le h (by simpa [ht] using hsne.card_pos)
      exact (hs (hst.trans ht)).elim
    · simp [hs, ht]

private def disjointGradeFilter : FilterFunction disjointEdges4.toPre ℤ where
  value := fun s => if s.val ⊆ ({0, 1} : Finset (Fin 4)) then 0 else 1
  mono := by
    intro s t h
    by_cases hs : s.val ⊆ ({0, 1} : Finset (Fin 4))
    · simp only [hs, ↓reduceIte]
      split_ifs <;> omega
    by_cases ht : t.val ⊆ ({0, 1} : Finset (Fin 4))
    · exact (hs (h.trans ht)).elim
    · simp [hs, ht]

private def faceList {n : ℕ} (C : FiniteComplex n)
    (f : FilterFunction C.toPre ℤ) : List (Finset (Fin n)) :=
  List.ofFn (fun i => ((ofLex C f).enum i).val)

#eval faceList empty0 (emptyFilter empty0 rfl ℤ)
#eval faceList empty3 (emptyFilter empty3 rfl ℤ)
#eval (List.ofFn (fun i => ((ofLex empty3 emptyVoidFilter).enum i).val))
#eval faceList singleton3 (constantFilter singleton3 3)
#eval faceList edge3 (constantFilter edge3 5)
#eval faceList triangle3 (constantFilter triangle3 5)
#eval faceList edge3 edgeVariableFilter
#eval faceList disjointEdges4 disjointGradeFilter
#eval faceList crossedEdges4 (constantFilter crossedEdges4 5)

private def badEnum : Fin 3 ≃ TotalFace edge3.toPre where
  toFun := fun i =>
    (⟨if i = 0 then ({0, 1} : Finset (Fin 3))
      else if i = 1 then {0} else {1}, by fin_cases i <;> decide⟩ :
      TotalFace edge3.toPre)
  invFun := fun s => if s.val = ({0, 1} : Finset (Fin 3)) then 0
    else if s.val = {0} then 1 else 2
  left_inv := by decide
  right_inv := by decide

#eval List.ofFn (fun i : Fin 3 => (badEnum i).val)

private theorem badEnum_grade_mono :
    Monotone ((constantFilter edge3 5).value ∘ badEnum) := by
  intro i j _
  exact le_rfl

private theorem edge3_card : Fintype.card (TotalFace edge3.toPre) = 3 := by decide

/-- The finite presentation's direct actual-face enumeration remains the selected instance. -/
private theorem selected_fintype {n : ℕ} (C : FiniteComplex n) :
    (inferInstance : Fintype (TotalFace C.toPre)) = instFintypeTotalFace C := rfl

/-- Ambient actual-face order remains set inclusion, not the local key order. -/
private theorem ambient_singletons_incomparable :
    ¬ ((⟨{0}, by decide⟩ : TotalFace edge3.toPre) ≤
      (⟨{1}, by decide⟩ : TotalFace edge3.toPre)) ∧
    ¬ ((⟨{1}, by decide⟩ : TotalFace edge3.toPre) ≤
      (⟨{0}, by decide⟩ : TotalFace edge3.toPre)) := by
  constructor <;> decide

private theorem constructed_mono {n : ℕ} (C : FiniteComplex n)
    (f : FilterFunction C.toPre ℤ) : Monotone (f.value ∘ (ofLex C f).enum) :=
  (ofLex C f).monotone

private theorem constructed_face_lt {n : ℕ} (C : FiniteComplex n)
    (f : FilterFunction C.toPre ℤ) (i j)
    (h : ((ofLex C f).enum i).val ⊂ ((ofLex C f).enum j).val) : i < j :=
  (ofLex C f).face_lt i j h

private theorem badEnum_not_compatible (h : CompatibleOrder (constantFilter edge3 5)) :
    ∃ i : Fin 3, (h.enum (Fin.cast edge3_card.symm i)).val ≠ (badEnum i).val := by
  by_contra hn
  push Not at hn
  have hp : (h.enum (Fin.cast edge3_card.symm 1)).val ⊂
      (h.enum (Fin.cast edge3_card.symm 0)).val := by
    rw [hn 1, hn 0]
    decide
  have hi := h.face_lt _ _ hp
  exact (by decide : ¬ (Fin.cast edge3_card.symm (1 : Fin 3) <
    Fin.cast edge3_card.symm (0 : Fin 3))) hi

#print axioms empty0
#print axioms empty3
#print axioms emptyFilter
#print axioms emptyVoidFilter
#print axioms singleton3
#print axioms edge3
#print axioms triangle3
#print axioms disjointEdges4
#print axioms crossedEdges4
#print axioms constantFilter
#print axioms edgeVariableFilter
#print axioms disjointGradeFilter
#print axioms faceList
#print axioms badEnum
#print axioms badEnum_grade_mono
#print axioms edge3_card
#print axioms selected_fintype
#print axioms ambient_singletons_incomparable
#print axioms constructed_mono
#print axioms constructed_face_lt
#print axioms badEnum_not_compatible

end TDA.Filtration.CompatibleOrderExamples
