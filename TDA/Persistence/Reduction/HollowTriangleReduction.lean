import TDA.Persistence.Reduction.SimplicialAdapterTemplate
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.ZMod.Basic

open TDA.Persistence TDA.Simplicial TDA.Filtration TDA.Persistence.Reduction
namespace TDA.Persistence.Reduction.Examples.HollowTriangle
set_option maxRecDepth 10000
set_option maxHeartbeats 800000

def C : FiniteComplex 3 where
  faces := {{0}, {1}, {2}, {0,1}, {1,2}, {0,2}}
  nonempty := by decide +kernel
  downClosed := by decide +kernel

def f : FilterFunction C.toPre ℕ where
  value s := s.val.card - 1
  mono := fun h => Nat.sub_le_sub_right (Finset.card_le_card h) 1

def enumFun (i : Fin (faceCount C.toPre)) : TotalFace C.toPre :=
  if i.val = 0 then ⟨{0}, by decide⟩
  else if i.val = 1 then ⟨{1}, by decide⟩
  else if i.val = 2 then ⟨{2}, by decide⟩
  else if i.val = 3 then ⟨{0,1}, by decide⟩
  else if i.val = 4 then ⟨{1,2}, by decide⟩
  else ⟨{0,2}, by decide⟩

noncomputable def e : CompatibleOrder f where
  enum := Equiv.ofBijective enumFun (by decide +kernel)
  face_lt := by decide +kernel
  monotone := by decide +kernel

def expected : Matrix (Fin (faceCount C.toPre)) (Fin (faceCount C.toPre)) (ZMod 2) :=
  fun r c =>
    if c.val = 3 then (if r.val = 0 ∨ r.val = 1 then 1 else 0)
    else if c.val = 4 then (if r.val = 1 ∨ r.val = 2 then 1 else 0)
    else if c.val = 5 then (if r.val = 0 ∨ r.val = 2 then 1 else 0)
    else 0

private theorem s01 : ({0,1} : Finset (Fin 3)).sort (· ≤ ·) = [0,1] := by
  rw [Finset.sort_insert (· ≤ ·) (by decide) (by decide)]
  simp [Finset.sort_singleton]
private theorem s12 : ({1,2} : Finset (Fin 3)).sort (· ≤ ·) = [1,2] := by
  rw [Finset.sort_insert (· ≤ ·) (by decide) (by decide)]
  simp [Finset.sort_singleton]
private theorem s02 : ({0,2} : Finset (Fin 3)).sort (· ≤ ·) = [0,2] := by
  rw [Finset.sort_insert (· ≤ ·) (by decide) (by decide)]
  simp [Finset.sort_singleton]
private theorem s012 : ({0,1,2} : Finset (Fin 3)).sort (· ≤ ·) = [0,1,2] := by
  rw [Finset.sort_insert (· ≤ ·) (by decide) (by decide)]
  simp [s12]

theorem faceBoundaryMatrix_eq_expected : faceBoundaryMatrix (ZMod 2) e = expected := by
  funext i j
  rw [faceBoundaryMatrix_apply]
  fin_cases i <;> fin_cases j <;>
    norm_num [faceDegree, e, enumFun, expected, indexedFace, deletedFace,
      show (0 : Fin 3) ≠ 2 by decide, show (1 : Fin 3) ≠ 2 by decide,
      Fin.sum_univ_two, Fin.sum_univ_three, Finset.orderEmbOfFin_apply, s01, s12, s02, s012]

  all_goals decide +kernel

theorem hollow_pivots :
    List.ofFn (fun j : Fin (faceCount C.toPre) =>
      columnPivot ((reducedFaceBoundary (ZMod 2) e).col j)) =
      [none, none, none, some ⟨1, by decide⟩, some ⟨2, by decide⟩, none] := by
  rw [reducedFaceBoundary, faceBoundaryMatrix_eq_expected]
  decide +kernel

theorem hollow_essential (i : Fin (faceCount C.toPre)) :
    IsEssential (reducedFaceBoundary (ZMod 2) e) i ↔ i.val = 0 ∨ i.val = 5 := by
  rw [reducedFaceBoundary, faceBoundaryMatrix_eq_expected]
  unfold IsEssential IsPivot
  fin_cases i <;> decide +kernel

theorem face_grades :
    List.ofFn (fun i : Fin (faceCount C.toPre) => f.value (e.enum i)) =
      [0, 0, 0, 1, 1, 1] := by
  decide +kernel


end TDA.Persistence.Reduction.Examples.HollowTriangle
