import TDA.Persistence.Reduction.SimplicialAdapterTemplate
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.ZMod.Basic
open TDA.Persistence TDA.Simplicial TDA.Filtration TDA.Persistence.Reduction
namespace TDA.Persistence.Reduction.Examples.Empty

def C : FiniteComplex 0 where
  faces := ∅
  nonempty := by simp
  downClosed := by simp

def f : FilterFunction C.toPre ℕ where
  value _ := 0
  mono := fun _ => le_rfl

instance : IsEmpty (TotalFace C.toPre) := ⟨fun s => by have h := s.property; change s.val ∈ (∅ : Finset (Finset (Fin 0))) at h; simpa using h⟩
instance : IsEmpty (Fin (faceCount C.toPre)) := by
  change IsEmpty (Fin 0)
  infer_instance

noncomputable def e : CompatibleOrder f where
  enum := Equiv.equivOfIsEmpty _ _
  face_lt := fun i => isEmptyElim i
  monotone := fun i => isEmptyElim i

theorem empty_actual_matrix : actualBoundaryMatrix (ZMod 2) e = 0 := by
  funext i
  exact isEmptyElim i

theorem empty_reduced_matrix : actualReducedBoundary (ZMod 2) e = 0 := by
  funext i
  exact isEmptyElim i

theorem empty_pivots :
    List.ofFn (fun j : Fin (faceCount C.toPre) =>
      columnPivot ((actualReducedBoundary (ZMod 2) e).col j)) = [] := by
  exact List.ofFn_zero

theorem empty_index_pairs (p : ℕ) :
    pivotIndexPairs (faceDegree e) (actualReducedBoundary (ZMod 2) e) p = 0 := by
  classical
  simp [pivotIndexPairs]

theorem empty_essential_indices (p : ℕ) :
    pivotEssentialIndices (faceDegree e) (actualReducedBoundary (ZMod 2) e) p = 0 := by
  classical
  simp [pivotEssentialIndices]

theorem empty_actual_barcode (p : ℕ) : actualPivotBarcode (ZMod 2) e p = 0 := by
  classical
  simp [actualPivotBarcode, pivotBarcode, pivotPairIntervals, pivotEssentialIntervals]

theorem empty_actual_diagram (p : ℕ) : (dgm (ZMod 2) f p).points = 0 := by
  rw [← evaluatePivotTemplate_eq_dgm (ZMod 2) e f e.monotone p]
  simp [evaluatePivotTemplate, empty_index_pairs, empty_essential_indices]

end TDA.Persistence.Reduction.Examples.Empty
