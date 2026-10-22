import TDA.Persistence.BoundaryCost
import TDA.Persistence.DiagramBottleneckLaws

/-!
# Boundary augmentation of finite partial matchings

Rows are source occurrences `I` followed by target dummies `J`; columns
are target occurrences `J` followed by source dummies `I`. A deletion
cost is constant across its entire source row, and an insertion cost across its
entire target column. Dummy-to-dummy assignments cost zero. Restriction and
completion preserve the existing total finite cost. Completion is a section of
restriction; arbitrary permutations of dummies need not be recovered.
-/

noncomputable section

namespace TDA.Persistence

open scoped Classical

variable {I J : Type*} [Fintype I] [Fintype J]

/-- Full boundary blocks with arbitrary pair, deletion and insertion coefficients. -/
def boundaryAssignmentEntryWith (c : I → J → ℝ) (u : I → ℝ) (v : J → ℝ) :
    I ⊕ J → J ⊕ I → ℝ
  | .inl i, .inl j => c i j
  | .inl i, .inr _ => u i
  | .inr _, .inl j => v j
  | .inr _, .inr _ => 0

/-- Linear assignment cost for those full boundary blocks. -/
def boundaryAssignmentCostWith (c : I → J → ℝ) (u : I → ℝ) (v : J → ℝ)
    (e : (I ⊕ J) ≃ (J ⊕ I)) : ℝ :=
  ∑ z, boundaryAssignmentEntryWith c u v z (e z)

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

/-- Keep exactly the source-occurrence to target-occurrence assignments. -/
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

private def dummyTargetChargeWith (e : (I ⊕ J) ≃ (J ⊕ I)) (v : J → ℝ) :
    J ⊕ I → ℝ
  | .inl j => match e.symm (.inl j) with
      | .inl _ => 0
      | .inr _ => v j
  | .inr _ => 0

/-- Restriction preserves paired costs and both unmatched sums exactly. -/
theorem totalBoundaryCost_ofBoundaryAssignment (e : (I ⊕ J) ≃ (J ⊕ I))
    (c : I → J → ℝ) (u : I → ℝ) (v : J → ℝ) :
    (ofBoundaryAssignment e).totalBoundaryCost c u v = boundaryAssignmentCostWith c u v e := by
  have hs (i : I) :
      (match (ofBoundaryAssignment e).finite i with
        | some j => c i j
        | none => u i) =
      boundaryAssignmentEntryWith c u v (.inl i) (e (.inl i)) := by
    cases h : e (.inl i) <;> simp [ofBoundaryAssignment, boundaryAssignmentEntryWith, h]
  have hc (z : I ⊕ J) : dummyTargetChargeWith e v (e z) =
      match z with
      | .inl _ => 0
      | .inr _ => boundaryAssignmentEntryWith c u v z (e z) := by
    cases z with
    | inl i =>
      cases h : e (.inl i) with
      | inl j => simp only [dummyTargetChargeWith, ← h, e.symm_apply_apply]
      | inr k => rfl
    | inr j =>
      cases h : e (.inr j) with
      | inl k => simp only [dummyTargetChargeWith, ← h, e.symm_apply_apply, boundaryAssignmentEntryWith]
      | inr i => rfl
  have ht (j : J) :
      (if ∃ i, (ofBoundaryAssignment e).finite i = some j then 0
        else v j) = dummyTargetChargeWith e v (.inl j) := by
    simp_rw [ofBoundaryAssignment_some_iff]
    cases h : e.symm (.inl j) with
    | inl i =>
      have he : e (.inl i) = .inl j := by rw [← h, e.apply_symm_apply]
      simp [dummyTargetChargeWith, h, show ∃ i, e (.inl i) = .inl j from ⟨i, he⟩]
    | inr k =>
      have hn : ¬ ∃ i, e (.inl i) = .inl j := by
        rintro ⟨i, hi⟩
        have := congrArg e.symm hi
        rw [e.symm_apply_apply, h] at this
        cases this
      simp [dummyTargetChargeWith, h, hn]
  have hr := e.sum_comp (dummyTargetChargeWith e v)
  simp_rw [hc] at hr
  simp only [Fintype.sum_sum_type, Finset.sum_const_zero, zero_add] at hr
  calc
    _ = (∑ i, boundaryAssignmentEntryWith c u v (.inl i) (e (.inl i))) +
        ∑ j, dummyTargetChargeWith e v (.inl j) :=
      congrArg₂ (· + ·) (Finset.sum_congr rfl (fun i _ => hs i))
        (Finset.sum_congr rfl (fun j _ => ht j))
    _ = _ := by
      unfold boundaryAssignmentCostWith
      rw [Fintype.sum_sum_type, hr]
      simp [dummyTargetChargeWith]

/-- The first-order restriction theorem, with its original cost convention. -/
theorem totalFiniteCost_ofBoundaryAssignment (e : (I ⊕ J) ≃ (J ⊕ I))
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    (ofBoundaryAssignment e).totalFiniteCost x y = boundaryAssignmentCost x y e := by
  calc
    _ = (ofBoundaryAssignment e).totalBoundaryCost
        (fun i j => (finitePairCost (x i) (y j)).toReal)
        (fun i => (diagonalCost (x i)).toReal) (fun j => (diagonalCost (y j)).toReal) := rfl
    _ = boundaryAssignmentCostWith
        (fun i j => (finitePairCost (x i) (y j)).toReal)
        (fun i => (diagonalCost (x i)).toReal) (fun j => (diagonalCost (y j)).toReal) e :=
      totalBoundaryCost_ofBoundaryAssignment e _ _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro z _
      cases z with
      | inl i => cases e (.inl i) <;> rfl
      | inr j => cases e (.inr j) <;> rfl

/-- Completion preserves arbitrary coefficient-dependent boundary cost. -/
theorem boundaryAssignmentCostWith_toBoundaryAssignment
    (M : OccurrenceMatching I J PEmpty.{1} PEmpty.{1})
    (c : I → J → ℝ) (u : I → ℝ) (v : J → ℝ) :
    boundaryAssignmentCostWith c u v M.toBoundaryAssignment = M.totalBoundaryCost c u v := by
  rw [← totalBoundaryCost_ofBoundaryAssignment, ofBoundaryAssignment_toBoundaryAssignment]

/-- The chosen completion has exactly the original partial-matching cost. -/
theorem boundaryAssignmentCost_toBoundaryAssignment
    (M : OccurrenceMatching I J PEmpty.{1} PEmpty.{1})
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    boundaryAssignmentCost x y M.toBoundaryAssignment = M.totalFiniteCost x y := by
  rw [← totalFiniteCost_ofBoundaryAssignment, ofBoundaryAssignment_toBoundaryAssignment]

end OccurrenceMatching

end TDA.Persistence
