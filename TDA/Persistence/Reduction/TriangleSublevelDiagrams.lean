import TDA.Persistence.Reduction.FilledTriangleReduction
import TDA.Persistence.Reduction.HollowTriangleReduction

open TDA.Persistence TDA.Simplicial TDA.Filtration TDA.Persistence.Reduction
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
namespace TDA.Persistence.Reduction.Examples.FilledTriangle

theorem exact_pairs_zero : pivotIndexPairs (faceDegree e) (reducedFaceBoundary (ZMod 2) e) 0 =
    {(⟨1, by decide⟩, ⟨3, by decide⟩), (⟨2, by decide⟩, ⟨4, by decide⟩)} := by
  apply (pivotIndexPairs_nodup _ _ _ |>.ext (by decide +kernel)).mpr
  rintro ⟨i,j⟩
  have hpiv : DistinctPivots (reducedFaceBoundary (ZMod 2) e) :=
    matrixReductionTrace_pivots_distinct _
  rw [mem_pivotIndexPairs_iff (faceDegree e) (reducedFaceBoundary (ZMod 2) e) hpiv]
  rw [reducedFaceBoundary, faceBoundaryMatrix_eq_expected]
  fin_cases i <;> fin_cases j <;> decide +kernel

theorem exact_pairs_one : pivotIndexPairs (faceDegree e) (reducedFaceBoundary (ZMod 2) e) 1 =
    {(⟨5, by decide⟩, ⟨6, by decide⟩)} := by
  apply (pivotIndexPairs_nodup _ _ _ |>.ext (by decide +kernel)).mpr
  rintro ⟨i,j⟩
  have hpiv : DistinctPivots (reducedFaceBoundary (ZMod 2) e) :=
    matrixReductionTrace_pivots_distinct _
  rw [mem_pivotIndexPairs_iff (faceDegree e) (reducedFaceBoundary (ZMod 2) e) hpiv]
  rw [reducedFaceBoundary, faceBoundaryMatrix_eq_expected]
  fin_cases i <;> fin_cases j <;> decide +kernel

theorem exact_essential_zero : pivotEssentialIndices (faceDegree e) (reducedFaceBoundary (ZMod 2) e) 0 =
    {⟨0, by decide⟩} := by
  apply (pivotEssentialIndices_nodup _ _ _ |>.ext (by decide +kernel)).mpr
  intro i
  rw [mem_pivotEssentialIndices_iff, filled_essential]
  fin_cases i <;> decide +kernel

theorem exact_essential_one : pivotEssentialIndices (faceDegree e) (reducedFaceBoundary (ZMod 2) e) 1 = 0 := by
  apply (pivotEssentialIndices_nodup _ _ _ |>.ext (by decide +kernel)).mpr
  intro i
  rw [mem_pivotEssentialIndices_iff, filled_essential]
  fin_cases i <;> decide +kernel
end TDA.Persistence.Reduction.Examples.FilledTriangle
namespace TDA.Persistence.Reduction.Examples.HollowTriangle

theorem exact_pairs_zero : pivotIndexPairs (faceDegree e) (reducedFaceBoundary (ZMod 2) e) 0 =
    {(⟨1, by decide⟩, ⟨3, by decide⟩), (⟨2, by decide⟩, ⟨4, by decide⟩)} := by
  apply (pivotIndexPairs_nodup _ _ _ |>.ext (by decide +kernel)).mpr
  rintro ⟨i,j⟩
  have hpiv : DistinctPivots (reducedFaceBoundary (ZMod 2) e) :=
    matrixReductionTrace_pivots_distinct _
  rw [mem_pivotIndexPairs_iff (faceDegree e) (reducedFaceBoundary (ZMod 2) e) hpiv]
  rw [reducedFaceBoundary, faceBoundaryMatrix_eq_expected]
  fin_cases i <;> fin_cases j <;> decide +kernel

theorem exact_pairs_one : pivotIndexPairs (faceDegree e) (reducedFaceBoundary (ZMod 2) e) 1 =
    0 := by
  apply (pivotIndexPairs_nodup _ _ _ |>.ext (by decide +kernel)).mpr
  rintro ⟨i,j⟩
  have hpiv : DistinctPivots (reducedFaceBoundary (ZMod 2) e) :=
    matrixReductionTrace_pivots_distinct _
  rw [mem_pivotIndexPairs_iff (faceDegree e) (reducedFaceBoundary (ZMod 2) e) hpiv]
  rw [reducedFaceBoundary, faceBoundaryMatrix_eq_expected]
  fin_cases i <;> fin_cases j <;> decide +kernel

theorem exact_essential_zero : pivotEssentialIndices (faceDegree e) (reducedFaceBoundary (ZMod 2) e) 0 =
    {⟨0, by decide⟩} := by
  apply (pivotEssentialIndices_nodup _ _ _ |>.ext (by decide +kernel)).mpr
  intro i
  rw [mem_pivotEssentialIndices_iff, hollow_essential]
  fin_cases i <;> decide +kernel

theorem exact_essential_one : pivotEssentialIndices (faceDegree e) (reducedFaceBoundary (ZMod 2) e) 1 = {⟨5, by decide⟩} := by
  apply (pivotEssentialIndices_nodup _ _ _ |>.ext (by decide +kernel)).mpr
  intro i
  rw [mem_pivotEssentialIndices_iff, hollow_essential]
  fin_cases i <;> decide +kernel
end TDA.Persistence.Reduction.Examples.HollowTriangle
namespace TDA.Persistence.Reduction.Examples.FilledTriangle

theorem diagram_zero :
    (dgm (ZMod 2) f 0).points = {(0, (1 : WithTop ℕ)), (0, 1), (0, ⊤)} := by
  rw [← evaluatePivotTemplate_eq_dgm (ZMod 2) e f e.monotone 0]
  simp only [evaluatePivotTemplate]
  rw [exact_pairs_zero, exact_essential_zero]
  simp [Multiset.filter_singleton, pairValues, birthValue, f, e, enumFun]

theorem diagram_one :
    (dgm (ZMod 2) f 1).points = {(1, (2 : WithTop ℕ))} := by
  rw [← evaluatePivotTemplate_eq_dgm (ZMod 2) e f e.monotone 1]
  simp only [evaluatePivotTemplate]
  rw [exact_pairs_one, exact_essential_one]
  simp [Multiset.filter_singleton, pairValues, birthValue, f, e, enumFun]

theorem tied_diagram_zero :
    (dgm (ZMod 2) tiedFilter 0).points = {(0, (1 : WithTop ℕ)), (0, 1), (0, ⊤)} := by
  rw [← evaluatePivotTemplate_eq_dgm (ZMod 2) e tiedFilter tiedOrder.monotone 0]
  simp only [evaluatePivotTemplate]
  rw [exact_pairs_zero, exact_essential_zero]
  simp [Multiset.filter_singleton, pairValues, birthValue, tiedFilter, e, enumFun]

theorem tied_diagram_one : (dgm (ZMod 2) tiedFilter 1).points = 0 := by
  rw [← evaluatePivotTemplate_eq_dgm (ZMod 2) e tiedFilter tiedOrder.monotone 1]
  simp only [evaluatePivotTemplate]
  rw [exact_pairs_one, exact_essential_one]
  simp [Multiset.filter_singleton, pairValues, birthValue, tiedFilter, e, enumFun]

end TDA.Persistence.Reduction.Examples.FilledTriangle

namespace TDA.Persistence.Reduction.Examples.FilledTriangle

theorem stage_intervals_zero :
    (facePivotBarcode (ZMod 2) e 0).map (fun I => (I.birth,I.death)) =
      {(2,4),(3,5),(1,8)} := by
  rw [facePivotBarcode, pivotBarcode_endpoints, exact_pairs_zero, exact_essential_zero]
  rfl

theorem stage_intervals_one :
    (facePivotBarcode (ZMod 2) e 1).map (fun I => (I.birth,I.death)) = {(6,7)} := by
  rw [facePivotBarcode, pivotBarcode_endpoints, exact_pairs_one, exact_essential_one]
  rfl

end TDA.Persistence.Reduction.Examples.FilledTriangle
namespace TDA.Persistence.Reduction.Examples.HollowTriangle

theorem diagram_zero :
    (dgm (ZMod 2) f 0).points = {(0, (1 : WithTop ℕ)), (0, 1), (0, ⊤)} := by
  rw [← evaluatePivotTemplate_eq_dgm (ZMod 2) e f e.monotone 0]
  simp only [evaluatePivotTemplate]
  rw [exact_pairs_zero, exact_essential_zero]
  simp [Multiset.filter_singleton, pairValues, birthValue, f, e, enumFun]

theorem diagram_one :
    (dgm (ZMod 2) f 1).points = {(1, (⊤ : WithTop ℕ))} := by
  rw [← evaluatePivotTemplate_eq_dgm (ZMod 2) e f e.monotone 1]
  simp only [evaluatePivotTemplate]
  rw [exact_pairs_one, exact_essential_one]
  simp [Multiset.filter_singleton, pairValues, birthValue, f, e, enumFun,
    show (0 : Fin 3) ≠ 2 by decide]

theorem stage_intervals_one :
    (facePivotBarcode (ZMod 2) e 1).map (fun I => (I.birth,I.death)) = {(6,7)} := by
  rw [facePivotBarcode, pivotBarcode_endpoints, exact_pairs_one, exact_essential_one]
  rfl
end TDA.Persistence.Reduction.Examples.HollowTriangle
