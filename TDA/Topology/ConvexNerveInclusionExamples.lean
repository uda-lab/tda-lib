import TDA.Topology.ConvexNerveInclusion
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# A strict inclusion of interval nerves

The three smaller intervals form a path. Extending its left interval across zero
creates a common intersection and hence a filled triangle on the same labels.
-/

namespace TDA.Topology.ConvexNerveInclusionExamples

open Set CategoryTheory TDA.Simplicial

/-- Three open intervals with successive overlaps. -/
def pathIntervals (i : Fin 3) : Set ℝ :=
  if i = 0 then Ioo (-2) 0 else if i = 1 then Ioo (-1) 1 else Ioo 0 2

/-- Extend only the left interval, creating a triple intersection. -/
def triangleIntervals (i : Fin 3) : Set ℝ :=
  if i = 0 then Ioo (-2) (1 / 2) else pathIntervals i

/-- The path family is contained label by label in the triangle family. -/
theorem intervals_subset (i : Fin 3) : pathIntervals i ⊆ triangleIntervals i := by
  by_cases h : i = 0
  · subst i
    intro x hx
    change -2 < x ∧ x < 0 at hx
    exact ⟨hx.1, hx.2.trans (by norm_num : (0 : ℝ) < 1 / 2)⟩
  · simp [triangleIntervals, h]

/-- Both families cover the same open interval. -/
theorem intervals_iUnion_eq : (⋃ i, pathIntervals i) = ⋃ i, triangleIntervals i := by
  apply Subset.antisymm (iUnion_mono intervals_subset)
  intro x hx
  obtain ⟨i, hi⟩ := mem_iUnion.mp hx
  by_cases h : i = 0
  · subst i
    change -2 < x ∧ x < 1 / 2 at hi
    by_cases hneg : x < 0
    · exact mem_iUnion.mpr ⟨0, hi.1, hneg⟩
    · refine mem_iUnion.mpr ⟨1, ?_⟩
      change -1 < x ∧ x < 1
      constructor <;> linarith [hi.2]
  · exact mem_iUnion.mpr ⟨i, by simpa [triangleIntervals, h] using hi⟩

/-- The triple of labels is a face only after extending the left interval. -/
theorem triple_face_difference :
    Finset.univ ∈ nerve triangleIntervals ∧ Finset.univ ∉ nerve pathIntervals := by
  constructor
  · refine ⟨Finset.univ_nonempty, (1 / 4 : ℝ), ?_⟩
    intro i _
    fin_cases i <;> norm_num [triangleIntervals, pathIntervals, mem_Ioo]
  · rintro ⟨_, x, hx⟩
    have hleft : -2 < x ∧ x < 0 := hx 0 (Finset.mem_univ _)
    have hright : 0 < x ∧ x < 2 := hx 2 (Finset.mem_univ _)
    exact (lt_asymm hleft.2 hright.1)

/-- The strict labelled inclusion induces an isomorphism in each degree. -/
theorem strict_inclusion_isIso (R : Type*) [Ring R] (k : ℕ) :
    nerve pathIntervals < nerve triangleIntervals ∧
      IsIso (simplicialHomologyIncl R (nerve_mono intervals_subset) k) := by
  refine ⟨lt_of_le_not_ge (nerve_mono intervals_subset)
    (fun h => triple_face_difference.2 (h triple_face_difference.1)), ?_⟩
  apply ConvexNerve.isIso_simplicialHomologyIncl _ _ _ intervals_subset intervals_iUnion_eq
  · intro i
    unfold pathIntervals
    split_ifs <;> exact isOpen_Ioo
  · intro i
    unfold pathIntervals
    split_ifs <;> exact convex_Ioo _ _
  · intro i
    unfold triangleIntervals pathIntervals
    split_ifs <;> exact convex_Ioo _ _

end TDA.Topology.ConvexNerveInclusionExamples
