import TDA.Persistence.Reduction.ActualFilledTriangle
import TDA.Persistence.Reduction.ActualHollowTriangle
import TDA.Persistence.Reduction.ActualFixtureHelpers

open TDA.Persistence TDA.Simplicial TDA.Filtration TDA.Persistence.Reduction
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
namespace TDA.Persistence.Reduction.Examples.FilledTriangle

theorem exact_pairs_zero : pivotIndexPairs (faceDegree e) (actualReducedBoundary (ZMod 2) e) 0 =
    {(⟨1, by decide⟩, ⟨3, by decide⟩), (⟨2, by decide⟩, ⟨4, by decide⟩)} := by
  apply (fixture_pairs_nodup _ _ _ |>.ext (by decide +kernel)).mpr
  rintro ⟨i,j⟩
  have hpiv : DistinctPivots (actualReducedBoundary (ZMod 2) e) :=
    matrixReductionTrace_pivots_distinct _
  rw [fixture_pairs_mem (faceDegree e) (actualReducedBoundary (ZMod 2) e) hpiv]
  rw [actualReducedBoundary, actual_eq]
  fin_cases i <;> fin_cases j <;> decide +kernel

theorem exact_pairs_one : pivotIndexPairs (faceDegree e) (actualReducedBoundary (ZMod 2) e) 1 =
    {(⟨5, by decide⟩, ⟨6, by decide⟩)} := by
  apply (fixture_pairs_nodup _ _ _ |>.ext (by decide +kernel)).mpr
  rintro ⟨i,j⟩
  have hpiv : DistinctPivots (actualReducedBoundary (ZMod 2) e) :=
    matrixReductionTrace_pivots_distinct _
  rw [fixture_pairs_mem (faceDegree e) (actualReducedBoundary (ZMod 2) e) hpiv]
  rw [actualReducedBoundary, actual_eq]
  fin_cases i <;> fin_cases j <;> decide +kernel

theorem exact_essential_zero : pivotEssentialIndices (faceDegree e) (actualReducedBoundary (ZMod 2) e) 0 =
    {⟨0, by decide⟩} := by
  apply (fixture_essential_nodup _ _ _ |>.ext (by decide +kernel)).mpr
  intro i
  rw [fixture_essential_mem, filled_essential]
  fin_cases i <;> decide +kernel

theorem exact_essential_one : pivotEssentialIndices (faceDegree e) (actualReducedBoundary (ZMod 2) e) 1 = 0 := by
  apply (fixture_essential_nodup _ _ _ |>.ext (by decide +kernel)).mpr
  intro i
  rw [fixture_essential_mem, filled_essential]
  fin_cases i <;> decide +kernel
end TDA.Persistence.Reduction.Examples.FilledTriangle
namespace TDA.Persistence.Reduction.Examples.HollowTriangle

theorem exact_pairs_zero : pivotIndexPairs (faceDegree e) (actualReducedBoundary (ZMod 2) e) 0 =
    {(⟨1, by decide⟩, ⟨3, by decide⟩), (⟨2, by decide⟩, ⟨4, by decide⟩)} := by
  apply (fixture_pairs_nodup _ _ _ |>.ext (by decide +kernel)).mpr
  rintro ⟨i,j⟩
  have hpiv : DistinctPivots (actualReducedBoundary (ZMod 2) e) :=
    matrixReductionTrace_pivots_distinct _
  rw [fixture_pairs_mem (faceDegree e) (actualReducedBoundary (ZMod 2) e) hpiv]
  rw [actualReducedBoundary, actual_eq]
  fin_cases i <;> fin_cases j <;> decide +kernel

theorem exact_pairs_one : pivotIndexPairs (faceDegree e) (actualReducedBoundary (ZMod 2) e) 1 =
    0 := by
  apply (fixture_pairs_nodup _ _ _ |>.ext (by decide +kernel)).mpr
  rintro ⟨i,j⟩
  have hpiv : DistinctPivots (actualReducedBoundary (ZMod 2) e) :=
    matrixReductionTrace_pivots_distinct _
  rw [fixture_pairs_mem (faceDegree e) (actualReducedBoundary (ZMod 2) e) hpiv]
  rw [actualReducedBoundary, actual_eq]
  fin_cases i <;> fin_cases j <;> decide +kernel

theorem exact_essential_zero : pivotEssentialIndices (faceDegree e) (actualReducedBoundary (ZMod 2) e) 0 =
    {⟨0, by decide⟩} := by
  apply (fixture_essential_nodup _ _ _ |>.ext (by decide +kernel)).mpr
  intro i
  rw [fixture_essential_mem, hollow_essential]
  fin_cases i <;> decide +kernel

theorem exact_essential_one : pivotEssentialIndices (faceDegree e) (actualReducedBoundary (ZMod 2) e) 1 = {⟨5, by decide⟩} := by
  apply (fixture_essential_nodup _ _ _ |>.ext (by decide +kernel)).mpr
  intro i
  rw [fixture_essential_mem, hollow_essential]
  fin_cases i <;> decide +kernel
end TDA.Persistence.Reduction.Examples.HollowTriangle
namespace TDA.Persistence.Reduction.Examples.FilledTriangle

theorem actual_diagram_zero :
    (dgm (ZMod 2) f 0).points = {(0, (1 : WithTop ℕ)), (0, 1), (0, ⊤)} := by
  rw [← evaluatePivotTemplate_eq_dgm (ZMod 2) e f e.monotone 0]
  simp only [evaluatePivotTemplate]
  rw [exact_pairs_zero, exact_essential_zero]
  simp [Multiset.filter_singleton, pairValues, birthValue, f, e, enumFun]

theorem actual_diagram_one :
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

namespace TDA.Persistence.Reduction
variable {m : ℕ} {k : Type*} [Field k] [DecidableEq k]
theorem fixture_barcode_endpoints (degree : Fin m → ℕ)
    (R : Matrix (Fin m) (Fin m) k) (hs : StrictBoundary R) (p : ℕ) :
    (pivotBarcode degree R hs p).map (fun I => (I.birth, I.death)) =
      (pivotIndexPairs degree R p).map (fun q => (q.1.val+1,q.2.val+1)) +
      (pivotEssentialIndices degree R p).map (fun i => (i.val+1,m+1)) := by
  simp only [pivotBarcode, Multiset.map_add, pivotPairIntervals, pivotEssentialIntervals,
    pivotIndexPairs, pivotEssentialIndices, Multiset.map_map]
  rfl
end TDA.Persistence.Reduction
namespace TDA.Persistence.Reduction.Examples.FilledTriangle

theorem stage_intervals_zero :
    (actualPivotBarcode (ZMod 2) e 0).map (fun I => (I.birth,I.death)) =
      {(2,4),(3,5),(1,8)} := by
  rw [actualPivotBarcode, fixture_barcode_endpoints, exact_pairs_zero, exact_essential_zero]
  rfl

theorem stage_intervals_one :
    (actualPivotBarcode (ZMod 2) e 1).map (fun I => (I.birth,I.death)) = {(6,7)} := by
  rw [actualPivotBarcode, fixture_barcode_endpoints, exact_pairs_one, exact_essential_one]
  rfl

end TDA.Persistence.Reduction.Examples.FilledTriangle
namespace TDA.Persistence.Reduction.Examples.HollowTriangle

theorem actual_diagram_zero :
    (dgm (ZMod 2) f 0).points = {(0, (1 : WithTop ℕ)), (0, 1), (0, ⊤)} := by
  rw [← evaluatePivotTemplate_eq_dgm (ZMod 2) e f e.monotone 0]
  simp only [evaluatePivotTemplate]
  rw [exact_pairs_zero, exact_essential_zero]
  simp [Multiset.filter_singleton, pairValues, birthValue, f, e, enumFun]

theorem actual_diagram_one :
    (dgm (ZMod 2) f 1).points = {(1, (⊤ : WithTop ℕ))} := by
  rw [← evaluatePivotTemplate_eq_dgm (ZMod 2) e f e.monotone 1]
  simp only [evaluatePivotTemplate]
  rw [exact_pairs_one, exact_essential_one]
  simp [Multiset.filter_singleton, pairValues, birthValue, f, e, enumFun,
    show (0 : Fin 3) ≠ 2 by decide]

theorem stage_intervals_one :
    (actualPivotBarcode (ZMod 2) e 1).map (fun I => (I.birth,I.death)) = {(6,7)} := by
  rw [actualPivotBarcode, fixture_barcode_endpoints, exact_pairs_one, exact_essential_one]
  rfl
end TDA.Persistence.Reduction.Examples.HollowTriangle
