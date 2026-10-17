import TDA.Persistence.FiniteMatchingCost
import TDA.Persistence.DiagramBottleneckLaws

/-!
# Boundary augmentation of finite partial matchings

Rows are actual source occurrences `I` followed by target dummies `J`; columns
are actual target occurrences `J` followed by source dummies `I`. A deletion
cost is constant across its entire source row, and an insertion cost across its
entire target column. Dummy-to-dummy assignments cost zero. Restriction and
completion preserve the existing total finite cost. Completion is a section of
restriction; arbitrary permutations of dummies need not be recovered.
-/

noncomputable section

namespace TDA.Persistence

open scoped Classical

variable {I J : Type*} [Fintype I] [Fintype J]

/-- The raw boundary assignment cost. This cost matrix is not a metric. -/
def boundaryAssignmentEntry (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    I ⊕ J → J ⊕ I → ℝ
  | .inl i, .inl j => (finitePairCost (x i) (y j)).toReal
  | .inl i, .inr _ => (diagonalCost (x i)).toReal
  | .inr _, .inl j => (diagonalCost (y j)).toReal
  | .inr _, .inr _ => 0

/-- Unnormalized total cost of a boundary-augmented bijection. -/
def boundaryAssignmentCost (x : I → ℝ × ℝ) (y : J → ℝ × ℝ)
    (e : (I ⊕ J) ≃ (J ⊕ I)) : ℝ := ∑ z, boundaryAssignmentEntry x y z (e z)

namespace OccurrenceMatching

/-- Keep exactly the actual-source to actual-target assignments. -/
def ofBoundaryAssignment (e : (I ⊕ J) ≃ (J ⊕ I)) :
    OccurrenceMatching I J PEmpty.{1} PEmpty.{1} where
  finite i := match e (.inl i) with | .inl j => some j | .inr _ => none
  finite_injective := by
    intro i i' j hi hi'
    have h (k : I) :
        (match e (.inl k) with | .inl j => some j | .inr _ => none) = some j →
          e (.inl k) = .inl j := by
      cases e (.inl k) <;> simp_all
    exact Sum.inl_injective (e.injective ((h i hi).trans (h i' hi').symm))
  essential := Equiv.refl _

omit [Fintype I] [Fintype J] in
theorem ofBoundaryAssignment_some_iff (e : (I ⊕ J) ≃ (J ⊕ I)) (i : I) (j : J) :
    (ofBoundaryAssignment e).finite i = some j ↔ e (.inl i) = .inl j := by
  cases h : e (.inl i) <;> simp [ofBoundaryAssignment, h]

private def completionMap (M : OccurrenceMatching I J PEmpty.{1} PEmpty.{1}) :
    I ⊕ J → J ⊕ I
  | .inl i => match M.finite i with | some j => .inl j | none => .inr i
  | .inr j => match M.reverse.finite j with | some i => .inr i | none => .inl j

private theorem completionMap_leftInverse
    (M : OccurrenceMatching I J PEmpty.{1} PEmpty.{1}) :
    Function.LeftInverse (completionMap M.reverse) (completionMap M) := by
  intro z
  cases z with
  | inl i =>
    cases h : M.finite i with
    | some j =>
      have hr := (M.reverse_finite_some_iff j i).mpr h
      simp [completionMap, h, hr]
    | none => simp [completionMap, h, reverse_reverse]
  | inr j =>
    cases h : M.reverse.finite j with
    | some i =>
      have hr := (M.reverse_finite_some_iff j i).mp h
      simp [completionMap, h, hr, reverse_reverse]
    | none => simp [completionMap, h]

/-- Complete with labelled dummies, using the reverse partial injection. -/
def toBoundaryAssignment (M : OccurrenceMatching I J PEmpty.{1} PEmpty.{1}) :
    (I ⊕ J) ≃ (J ⊕ I) where
  toFun := completionMap M
  invFun := completionMap M.reverse
  left_inv := completionMap_leftInverse M
  right_inv := by
    intro z
    have h := completionMap_leftInverse M.reverse z
    simpa only [reverse_reverse] using h

/-- Completion is a section. No reverse identity for arbitrary dummy assignments is claimed. -/
theorem ofBoundaryAssignment_toBoundaryAssignment
    (M : OccurrenceMatching I J PEmpty.{1} PEmpty.{1}) :
    ofBoundaryAssignment M.toBoundaryAssignment = M := by
  apply OccurrenceMatching.ext
  · funext i
    cases h : M.finite i <;> simp [ofBoundaryAssignment, toBoundaryAssignment, completionMap, h]
  · exact Subsingleton.elim _ _

private def dummyTargetCharge (e : (I ⊕ J) ≃ (J ⊕ I)) (y : J → ℝ × ℝ) :
    J ⊕ I → ℝ
  | .inl j => match e.symm (.inl j) with
      | .inl _ => 0
      | .inr _ => (diagonalCost (y j)).toReal
  | .inr _ => 0

/-- Restriction preserves paired costs and both unmatched sums exactly. -/
theorem totalFiniteCost_ofBoundaryAssignment (e : (I ⊕ J) ≃ (J ⊕ I))
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    (ofBoundaryAssignment e).totalFiniteCost x y = boundaryAssignmentCost x y e := by
  have hs (i : I) :
      (match (ofBoundaryAssignment e).finite i with
        | some j => (finitePairCost (x i) (y j)).toReal
        | none => (diagonalCost (x i)).toReal) =
      boundaryAssignmentEntry x y (.inl i) (e (.inl i)) := by
    cases h : e (.inl i) <;> simp [ofBoundaryAssignment, boundaryAssignmentEntry, h]
  have hc (z : I ⊕ J) : dummyTargetCharge e y (e z) =
      match z with
      | .inl _ => 0
      | .inr _ => boundaryAssignmentEntry x y z (e z) := by
    cases z with
    | inl i =>
      cases h : e (.inl i) with
      | inl j => simp only [dummyTargetCharge, ← h, e.symm_apply_apply]
      | inr k => rfl
    | inr j =>
      cases h : e (.inr j) with
      | inl k => simp only [dummyTargetCharge, ← h, e.symm_apply_apply, boundaryAssignmentEntry]
      | inr i => rfl
  have ht (j : J) :
      (if ∃ i, (ofBoundaryAssignment e).finite i = some j then 0
        else (diagonalCost (y j)).toReal) = dummyTargetCharge e y (.inl j) := by
    simp_rw [ofBoundaryAssignment_some_iff]
    cases h : e.symm (.inl j) with
    | inl i =>
      have he : e (.inl i) = .inl j := by rw [← h, e.apply_symm_apply]
      simp [dummyTargetCharge, h, show ∃ i, e (.inl i) = .inl j from ⟨i, he⟩]
    | inr k =>
      have hn : ¬ ∃ i, e (.inl i) = .inl j := by
        rintro ⟨i, hi⟩
        have := congrArg e.symm hi
        rw [e.symm_apply_apply, h] at this
        cases this
      simp [dummyTargetCharge, h, hn]
  have hr := e.sum_comp (dummyTargetCharge e y)
  simp_rw [hc] at hr
  simp only [Fintype.sum_sum_type, Finset.sum_const_zero, zero_add] at hr
  calc
    _ = (∑ i, boundaryAssignmentEntry x y (.inl i) (e (.inl i))) +
        ∑ j, dummyTargetCharge e y (.inl j) :=
      congrArg₂ (· + ·) (Finset.sum_congr rfl (fun i _ => hs i))
        (Finset.sum_congr rfl (fun j _ => ht j))
    _ = _ := by
      unfold boundaryAssignmentCost
      rw [Fintype.sum_sum_type, hr]
      simp [dummyTargetCharge]

/-- The chosen completion has exactly the original partial-matching cost. -/
theorem boundaryAssignmentCost_toBoundaryAssignment
    (M : OccurrenceMatching I J PEmpty.{1} PEmpty.{1})
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    boundaryAssignmentCost x y M.toBoundaryAssignment = M.totalFiniteCost x y := by
  rw [← totalFiniteCost_ofBoundaryAssignment, ofBoundaryAssignment_toBoundaryAssignment]

end OccurrenceMatching

end TDA.Persistence
