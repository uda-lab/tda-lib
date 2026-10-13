import TDA.Persistence.Reduction.SimplicialAdapterTemplate
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.ZMod.Basic
open TDA.Persistence TDA.Simplicial TDA.Filtration TDA.Persistence.Reduction
namespace TDA.Persistence.Reduction.Examples.DelayedEdge
set_option maxRecDepth 10000
set_option maxHeartbeats 800000

def C : FiniteComplex 2 where
  faces := {{0}, {1}, {0,1}}
  nonempty := by decide +kernel
  downClosed := by decide +kernel

def f : FilterFunction C.toPre ℕ where
  value s := if s.val.card = 1 then 5 else 8
  mono := by decide +kernel

def enumFun (i : Fin (faceCount C.toPre)) : TotalFace C.toPre :=
  if i.val = 0 then ⟨{0}, by decide⟩
  else if i.val = 1 then ⟨{1}, by decide⟩
  else ⟨{0,1}, by decide⟩

noncomputable def e : CompatibleOrder f where
  enum := Equiv.ofBijective enumFun (by decide +kernel)
  face_lt := by decide +kernel
  monotone := by decide +kernel

def expected : Matrix (Fin (faceCount C.toPre)) (Fin (faceCount C.toPre)) (ZMod 2) :=
  fun r c => if c.val = 2 ∧ r.val < 2 then 1 else 0

private theorem s01 : ({0,1} : Finset (Fin 2)).sort (· ≤ ·) = [0,1] := by
  rw [Finset.sort_insert (· ≤ ·) (by decide) (by decide)]
  simp [Finset.sort_singleton]

theorem actual_eq : actualBoundaryMatrix (ZMod 2) e = expected := by
  funext i j
  rw [actualBoundaryMatrix_apply]
  fin_cases i <;> fin_cases j <;>
    norm_num [faceDegree, e, enumFun, expected, indexedFace, deletedFace,
      Finset.orderEmbOfFin_apply, s01]
  all_goals decide +kernel

theorem delayed_edge_pivots :
    List.ofFn (fun j : Fin (faceCount C.toPre) =>
      columnPivot ((actualReducedBoundary (ZMod 2) e).col j)) =
      [none, none, some ⟨1, by decide⟩] := by
  rw [actualReducedBoundary, actual_eq]
  decide +kernel

theorem delayed_edge_essential (i : Fin (faceCount C.toPre)) :
    IsEssential (actualReducedBoundary (ZMod 2) e) i ↔ i.val = 0 := by
  rw [actualReducedBoundary, actual_eq]
  unfold IsEssential IsPivot
  fin_cases i <;> decide +kernel

theorem delayed_edge_grades :
    List.ofFn (fun i : Fin (faceCount C.toPre) => f.value (e.enum i)) = [5,5,8] := by
  decide +kernel

def swappedEnumFun (i : Fin (faceCount C.toPre)) : TotalFace C.toPre :=
  if i.val = 0 then ⟨{1}, by decide⟩
  else if i.val = 1 then ⟨{0}, by decide⟩
  else ⟨{0,1}, by decide⟩

noncomputable def swappedOrder : CompatibleOrder f where
  enum := Equiv.ofBijective swappedEnumFun (by decide +kernel)
  face_lt := by decide +kernel
  monotone := by decide +kernel

theorem swapped_actual_eq : actualBoundaryMatrix (ZMod 2) swappedOrder = expected := by
  funext i j
  rw [actualBoundaryMatrix_apply]
  fin_cases i <;> fin_cases j <;>
    norm_num [faceDegree, swappedOrder, swappedEnumFun, expected, indexedFace, deletedFace,
      Finset.orderEmbOfFin_apply, s01]
  all_goals decide +kernel

theorem swapped_reduced_eq :
    actualReducedBoundary (ZMod 2) swappedOrder = actualReducedBoundary (ZMod 2) e := by
  simp only [actualReducedBoundary, swapped_actual_eq, actual_eq]

theorem equal_grade_reordering :
    (∀ i : Fin (faceCount C.toPre), f.value (swappedOrder.enum i) = f.value (e.enum i)) ∧
    (swappedOrder.enum ⟨1, by decide⟩).val = {0} ∧
    (e.enum ⟨1, by decide⟩).val = {1} := by decide +kernel

theorem equal_grade_diagram (p : ℕ) :
    evaluatePivotTemplate (ZMod 2) e f e.monotone p =
      evaluatePivotTemplate (ZMod 2) swappedOrder f swappedOrder.monotone p :=
  evaluatePivotTemplate_order_independent (ZMod 2)
    e swappedOrder f e.monotone swappedOrder.monotone p


end TDA.Persistence.Reduction.Examples.DelayedEdge
