import TDA.Topology.NerveThickening
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Fixtures for small open thickenings of labelled nerves
-/

namespace TDA.Topology.NerveThickeningExamples

open Set Metric

/-- The labelled family `[0,1]`, `[1,2]`, `{0}`. -/
def intervalPathCover : CoverFamily ℝ (Fin 3) :=
  fun i => if i = 0 then Icc 0 1 else if i = 1 then Icc 1 2 else {0}

/-- The labelled family `[0,2]`, `[0,2]`, `{0}`. -/
def intervalTriangleCover : CoverFamily ℝ (Fin 3) :=
  fun i => if i = 2 then {0} else Icc 0 2

private theorem pathCover_compact (i : Fin 3) : IsCompact (intervalPathCover i) := by
  fin_cases i <;> norm_num [intervalPathCover, isCompact_Icc]

private theorem triangleCover_compact (i : Fin 3) : IsCompact (intervalTriangleCover i) := by
  fin_cases i <;> norm_num [intervalTriangleCover, isCompact_Icc]

private theorem pathCover_convex (i : Fin 3) : Convex ℝ (intervalPathCover i) := by
  fin_cases i <;> norm_num [intervalPathCover, convex_Icc, convex_singleton]

private theorem triangleCover_convex (i : Fin 3) : Convex ℝ (intervalTriangleCover i) := by
  fin_cases i <;> norm_num [intervalTriangleCover, convex_Icc, convex_singleton]

private theorem pathCover_subset_triangleCover (i : Fin 3) :
    intervalPathCover i ⊆ intervalTriangleCover i := by
  fin_cases i
  · exact Icc_subset_Icc (by norm_num) (by norm_num)
  · exact Icc_subset_Icc (by norm_num) (by norm_num)
  · exact Subset.rfl

private theorem pathCover_union : (⋃ i, intervalPathCover i) = Icc 0 2 := by
  ext x
  simp only [mem_iUnion]
  constructor
  · rintro ⟨i, hi⟩
    fin_cases i <;> norm_num [intervalPathCover] at hi
    · exact ⟨hi.1, hi.2.trans (by norm_num)⟩
    · exact ⟨(by norm_num : (0 : ℝ) ≤ 1).trans hi.1, hi.2⟩
    · simp [hi]
  · intro hx
    by_cases h : x ≤ 1
    · have hx' : x ∈ Icc (0 : ℝ) 1 := ⟨hx.1, h⟩
      exact ⟨0, by simpa [intervalPathCover] using hx'⟩
    · have hx' : x ∈ Icc (1 : ℝ) 2 := ⟨le_of_not_ge h, hx.2⟩
      exact ⟨1, by simpa [intervalPathCover] using hx'⟩

private theorem triangleCover_union : (⋃ i, intervalTriangleCover i) = Icc 0 2 := by
  ext x
  simp only [mem_iUnion]
  constructor
  · rintro ⟨i, hi⟩
    fin_cases i <;> norm_num [intervalTriangleCover] at hi
    · exact hi
    · exact hi
    · simp [hi]
  · intro hx
    exact ⟨0, by simpa [intervalTriangleCover] using hx⟩

private theorem path_edge₀₁ : ({0, 1} : Finset (Fin 3)) ∈ nerve intervalPathCover := by
  refine (mem_nerve_iff intervalPathCover _).2 ⟨by simp, 1, ?_⟩
  intro i hi
  rcases Finset.mem_insert.mp hi with rfl | hi
  · norm_num [intervalPathCover]
  · obtain rfl := Finset.mem_singleton.mp hi
    norm_num [intervalPathCover]

private theorem path_edge₀₂ : ({0, 2} : Finset (Fin 3)) ∈ nerve intervalPathCover := by
  refine (mem_nerve_iff intervalPathCover _).2 ⟨by simp, 0, ?_⟩
  intro i hi
  rcases Finset.mem_insert.mp hi with rfl | hi
  · norm_num [intervalPathCover]
  · obtain rfl := Finset.mem_singleton.mp hi
    norm_num [intervalPathCover]

private theorem path_no_edge₁₂ : ¬ ({1, 2} : Finset (Fin 3)) ∈ nerve intervalPathCover := by
  intro h
  obtain ⟨_, x, hx⟩ := (mem_nerve_iff intervalPathCover _).1 h
  have hx₁ := hx 1 (by simp)
  have hx₂ := hx 2 (by simp)
  norm_num [intervalPathCover] at hx₁ hx₂
  norm_num [hx₂] at hx₁

private theorem triangle_face : ({0, 1, 2} : Finset (Fin 3)) ∈ nerve intervalTriangleCover := by
  refine (mem_nerve_iff intervalTriangleCover _).2 ⟨by simp, 0, ?_⟩
  intro i _
  fin_cases i <;> norm_num [intervalTriangleCover]

private theorem pathNerve_lt_triangleNerve : nerve intervalPathCover < nerve intervalTriangleCover := by
  refine lt_of_le_not_ge (nerve_mono pathCover_subset_triangleCover) fun h => path_no_edge₁₂ (h ?_)
  exact mem_nerve_of_nonempty_subset intervalTriangleCover triangle_face (by decide) (by decide)

/-- The path and filled triangle cover the same interval. Their strict nerve inclusion and
the indicated faces are preserved at every sufficiently small positive radius. -/
theorem path_and_triangle_preserved :
    (⋃ i, intervalPathCover i) = (⋃ i, intervalTriangleCover i) ∧
    nerve intervalPathCover < nerve intervalTriangleCover ∧
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ δ →
      (⋃ i, thickening ε (intervalPathCover i)) = (⋃ i, thickening ε (intervalTriangleCover i)) ∧
      ({0, 1} : Finset (Fin 3)) ∈ nerve (fun i => thickening ε (intervalPathCover i)) ∧
      ({0, 2} : Finset (Fin 3)) ∈ nerve (fun i => thickening ε (intervalPathCover i)) ∧
      ¬ ({1, 2} : Finset (Fin 3)) ∈ nerve (fun i => thickening ε (intervalPathCover i)) ∧
      ({0, 1, 2} : Finset (Fin 3)) ∈ nerve (fun i => thickening ε (intervalTriangleCover i)) ∧
      nerve (fun i => thickening ε (intervalPathCover i)) <
        nerve (fun i => thickening ε (intervalTriangleCover i)) := by
  have hU := pathCover_union.trans triangleCover_union.symm
  refine ⟨hU, pathNerve_lt_triangleNerve, ?_⟩
  obtain ⟨δ, hδ, h⟩ := exists_pos_common_convex_thickening intervalPathCover intervalTriangleCover
    pathCover_compact triangleCover_compact pathCover_convex triangleCover_convex
    pathCover_subset_triangleCover hU
  refine ⟨δ, hδ, fun ε hε hεδ => ?_⟩
  obtain ⟨hC, hD, hUnionC, hUnionD, _⟩ := h ε hε hεδ
  refine ⟨hUnionC.trans hUnionD.symm, ?_⟩
  rw [hC, hD]
  exact ⟨path_edge₀₁, path_edge₀₂, path_no_edge₁₂, triangle_face, pathNerve_lt_triangleNerve⟩

/-- Two labels carry the same singleton and a third label carries the empty set. -/
def duplicateAndEmptyCover : CoverFamily ℝ (Fin 3) :=
  fun i => if i = 2 then ∅ else {0}

/-- Positive open thickenings preserve the edge between the duplicate labels and
leave the empty label absent. -/
theorem duplicate_edge_and_empty_label (ε : ℝ) (hε : 0 < ε) :
    ({0, 1} : Finset (Fin 3)) ∈ nerve (fun i => thickening ε (duplicateAndEmptyCover i)) ∧
      ¬ ({2} : Finset (Fin 3)) ∈ nerve (fun i => thickening ε (duplicateAndEmptyCover i)) := by
  constructor
  · apply nerve_mono (fun i => self_subset_thickening hε (duplicateAndEmptyCover i))
    refine (mem_nerve_iff duplicateAndEmptyCover _).2 ⟨by simp, 0, ?_⟩
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · norm_num [duplicateAndEmptyCover]
    · obtain rfl := Finset.mem_singleton.mp hi
      norm_num [duplicateAndEmptyCover]
  · simp [mem_nerve_singleton_iff, duplicateAndEmptyCover]

example {X : Type*} [MetricSpace X] (C : CoverFamily X Empty) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ δ →
      nerve (fun i => thickening ε (C i)) = nerve C :=
  exists_pos_nerve_thickening_eq C isEmptyElim

end TDA.Topology.NerveThickeningExamples
