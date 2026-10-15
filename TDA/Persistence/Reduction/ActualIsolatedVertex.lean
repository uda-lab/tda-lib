import TDA.Persistence.Reduction.PivotBarcode
import TDA.Persistence.Reduction.SimplicialAdapterTemplate
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.ZMod.Basic
open TDA.Persistence TDA.Simplicial TDA.Filtration TDA.Persistence.Reduction
namespace TDA.Persistence.Reduction.Examples.IsolatedVertex

def C : FiniteComplex 1 where
  faces := {{0}}
  nonempty := by decide +kernel
  downClosed := by decide +kernel

def f : FilterFunction C.toPre ℕ where
  value _ := 5
  mono := fun _ => le_rfl

def enumFun (_ : Fin (faceCount C.toPre)) : TotalFace C.toPre := ⟨{0}, by decide⟩

noncomputable def e : CompatibleOrder f where
  enum := Equiv.ofBijective enumFun (by decide +kernel)
  face_lt := by decide +kernel
  monotone := by decide +kernel

theorem actual_zero : actualBoundaryMatrix (ZMod 2) e = 0 := by
  funext i j
  rw [actualBoundaryMatrix_apply]
  have h : ¬ faceDegree e j = faceDegree e i + 1 := by decide +revert +kernel
  simp [h]

theorem reduced_zero : actualReducedBoundary (ZMod 2) e = 0 := by
  rw [actualReducedBoundary, actual_zero]
  funext i j
  fin_cases i <;> fin_cases j <;> decide +kernel

theorem essential (i : Fin (faceCount C.toPre)) :
    IsEssential (actualReducedBoundary (ZMod 2) e) i := by
  rw [reduced_zero]
  unfold IsEssential IsPivot
  fin_cases i <;> decide +kernel

theorem delayed_grade : List.ofFn (fun i : Fin (faceCount C.toPre) => f.value (e.enum i)) = [5] := by
  decide +kernel
end TDA.Persistence.Reduction.Examples.IsolatedVertex

namespace TDA.Persistence.Reduction.Examples.IsolatedVertex

theorem exact_pairs_zero :
    pivotIndexPairs (faceDegree e) (actualReducedBoundary (ZMod 2) e) 0 = 0 := by
  apply (pivotIndexPairs_nodup _ _ _ |>.ext (by decide +kernel)).mpr
  rintro ⟨i,j⟩
  have hpiv : DistinctPivots (actualReducedBoundary (ZMod 2) e) :=
    matrixReductionTrace_pivots_distinct _
  rw [mem_pivotIndexPairs_iff _ _ hpiv, reduced_zero]
  fin_cases i
  fin_cases j
  decide +kernel

theorem exact_essential_zero :
    pivotEssentialIndices (faceDegree e) (actualReducedBoundary (ZMod 2) e) 0 = {⟨0, by decide⟩} := by
  apply (pivotEssentialIndices_nodup _ _ _ |>.ext (by decide +kernel)).mpr
  intro i
  rw [mem_pivotEssentialIndices_iff]
  simp only [essential, true_and]
  fin_cases i
  decide +kernel

theorem actual_diagram_zero :
    (dgm (ZMod 2) f 0).points = {(5, (⊤ : WithTop ℕ))} := by
  rw [← evaluatePivotTemplate_eq_dgm (ZMod 2) e f e.monotone 0]
  simp only [evaluatePivotTemplate]
  rw [exact_pairs_zero, exact_essential_zero]
  simp [birthValue, f]
end TDA.Persistence.Reduction.Examples.IsolatedVertex
