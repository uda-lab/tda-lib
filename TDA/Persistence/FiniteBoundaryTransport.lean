import TDA.Persistence.BoundaryAugmentedMatching
import TDA.Persistence.FiniteMatchingCostLaws
import Mathlib.Analysis.Convex.Birkhoff

/-!
# Finite first-order boundary transport

A plan has arbitrary nonnegative real mass between occurrence labels, with row
and column sums at most one. The remaining mass is deleted to or inserted from
the boundary at the existing maximum-norm diagonal cost. The optimum equals the
finite partial-matching minimum: padding gives a doubly stochastic matrix and
mathlib's Birkhoff decomposition supplies the fractional-to-matching inequality.

These are finite reservoir matrices with unit input mass per occurrence, not
Radon couplings on the closed upper half-plane. Boundary transport originates
with Figalli–Gigli; Divol–Lacombe develops its persistence-measure setting. The
finite assignment argument follows the pattern of Lacombe–Cuturi–Oudot,
Proposition 1 / Supplement §7.1, adapted to matching exponent 1 and ground norm ∞.
-/

noncomputable section

namespace TDA.Persistence

open scoped Classical

/-- Real mass may split, but each labelled source and target has unit capacity. -/
structure FiniteBoundaryPlan (I J : Type*) [Fintype I] [Fintype J] where
  mass : I → J → ℝ
  nonneg : ∀ i j, 0 ≤ mass i j
  row_le_one : ∀ i, ∑ j, mass i j ≤ 1
  col_le_one : ∀ j, ∑ i, mass i j ≤ 1

namespace FiniteBoundaryPlan

variable {I J : Type*} [Fintype I] [Fintype J]

/-- The feasible plan sending every source and target occurrence to the boundary. -/
def zero : FiniteBoundaryPlan I J where
  mass _ _ := 0
  nonneg _ _ := le_rfl
  row_le_one _ := by simp
  col_le_one _ := by simp

instance : Nonempty (FiniteBoundaryPlan I J) := ⟨zero⟩

/-- Source mass not sent to a target. -/
def deletionMass (a : FiniteBoundaryPlan I J) (i : I) : ℝ := 1 - ∑ j, a.mass i j

/-- Target mass supplied by the boundary. -/
def insertionMass (a : FiniteBoundaryPlan I J) (j : J) : ℝ := 1 - ∑ i, a.mass i j

theorem deletionMass_nonneg (a : FiniteBoundaryPlan I J) (i : I) :
    0 ≤ a.deletionMass i := sub_nonneg.mpr (a.row_le_one i)

theorem insertionMass_nonneg (a : FiniteBoundaryPlan I J) (j : J) :
    0 ≤ a.insertionMass j := sub_nonneg.mpr (a.col_le_one j)

theorem source_balance (a : FiniteBoundaryPlan I J) (i : I) :
    (∑ j, a.mass i j) + a.deletionMass i = 1 := by simp [deletionMass]

theorem target_balance (a : FiniteBoundaryPlan I J) (j : J) :
    (∑ i, a.mass i j) + a.insertionMass j = 1 := by simp [insertionMass]

/-- Linear cost of a feasible plan for independent pair and boundary coefficients. -/
def linearCost (a : FiniteBoundaryPlan I J)
    (c : I → J → ℝ) (u : I → ℝ) (v : J → ℝ) : ℝ :=
  (∑ i, ∑ j, a.mass i j * c i j) +
    (∑ i, a.deletionMass i * u i) + ∑ j, a.insertionMass j * v j

/-- Nonnegative coefficients give a nonnegative real-plan cost. -/
theorem linearCost_nonneg (a : FiniteBoundaryPlan I J)
    (c : I → J → ℝ) (u : I → ℝ) (v : J → ℝ)
    (hc : ∀ i j, 0 ≤ c i j) (hu : ∀ i, 0 ≤ u i) (hv : ∀ j, 0 ≤ v j) :
    0 ≤ a.linearCost c u v := by
  apply add_nonneg
  · apply add_nonneg
    · exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
        mul_nonneg (a.nonneg i j) (hc i j)
    · exact Finset.sum_nonneg fun i _ => mul_nonneg (a.deletionMass_nonneg i) (hu i)
  · exact Finset.sum_nonneg fun j _ => mul_nonneg (a.insertionMass_nonneg j) (hv j)

/-- Unnormalized first-order cost: transported mass plus both boundary residuals. -/
def cost (a : FiniteBoundaryPlan I J) (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) : ℝ :=
  (∑ i, ∑ j, a.mass i j * (finitePairCost (x i) (y j)).toReal) +
    (∑ i, a.deletionMass i * (diagonalCost (x i)).toReal) +
    ∑ j, a.insertionMass j * (diagonalCost (y j)).toReal

theorem cost_nonneg (a : FiniteBoundaryPlan I J)
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) : 0 ≤ a.cost x y := by
  apply add_nonneg
  · apply add_nonneg
    · exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
        mul_nonneg (a.nonneg i j) ENNReal.toReal_nonneg
    · exact Finset.sum_nonneg fun i _ =>
        mul_nonneg (a.deletionMass_nonneg i) ENNReal.toReal_nonneg
  · exact Finset.sum_nonneg fun j _ =>
      mul_nonneg (a.insertionMass_nonneg j) ENNReal.toReal_nonneg

omit [Fintype J] in
private theorem incidence_col_sum
    (M : OccurrenceMatching I J PEmpty.{1} PEmpty.{1}) (j : J) :
    (∑ i, if M.finite i = some j then (1 : ℝ) else 0) =
      if ∃ i, M.finite i = some j then 1 else 0 := by
  split_ifs with h
  · obtain ⟨i, hi⟩ := h
    rw [Finset.sum_eq_single i]
    · simp [hi]
    · intro k _ hki
      have hk : M.finite k ≠ some j := fun hk => hki (M.finite_injective k i j hk hi)
      simp [hk]
    · simp
  · simp [show ∀ i, M.finite i ≠ some j from fun i hi => h ⟨i, hi⟩]

/-- The 0–1 incidence plan of the existing partial injection. -/
def ofMatching (M : OccurrenceMatching I J PEmpty.{1} PEmpty.{1}) :
    FiniteBoundaryPlan I J where
  mass i j := if M.finite i = some j then 1 else 0
  nonneg _ _ := by split_ifs <;> norm_num
  row_le_one i := by cases M.finite i <;> simp
  col_le_one j := by rw [incidence_col_sum]; split_ifs <;> norm_num

/-- Incidence plans preserve all three coefficient families exactly. -/
theorem linearCost_ofMatching (M : OccurrenceMatching I J PEmpty.{1} PEmpty.{1})
    (c : I → J → ℝ) (u : I → ℝ) (v : J → ℝ) :
    (ofMatching M).linearCost c u v = M.totalBoundaryCost c u v := by
  unfold linearCost OccurrenceMatching.totalBoundaryCost
  rw [← Finset.sum_add_distrib]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    cases h : M.finite i <;> simp [ofMatching, deletionMass, h]
  · apply Finset.sum_congr rfl
    intro j _
    simp only [insertionMass, ofMatching, incidence_col_sum]
    split_ifs <;> simp

/-- Incidence plans charge exactly the original matching, without merging repeated values. -/
theorem cost_ofMatching (M : OccurrenceMatching I J PEmpty.{1} PEmpty.{1})
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    (ofMatching M).cost x y = M.totalFiniteCost x y :=
  linearCost_ofMatching M _ _ _

/-- Rectangular boundary augmentation: residuals on the two diagonal blocks. -/
def augmentedMass (a : FiniteBoundaryPlan I J) : I ⊕ J → J ⊕ I → ℝ
  | .inl i, .inl j => a.mass i j
  | .inl i, .inr i' => if i = i' then a.deletionMass i else 0
  | .inr j, .inl j' => if j = j' then a.insertionMass j else 0
  | .inr j, .inr i => a.mass i j

/-- Column reindexing puts the augmentation on one finite square index type. -/
def paddedMatrix (a : FiniteBoundaryPlan I J) : Matrix (I ⊕ J) (I ⊕ J) ℝ :=
  fun z w => a.augmentedMass z (Equiv.sumComm I J w)

/-- The explicit padding is doubly stochastic, including empty occurrence types. -/
theorem paddedMatrix_doublyStochastic (a : FiniteBoundaryPlan I J) :
    a.paddedMatrix ∈ doublyStochastic ℝ (I ⊕ J) := by
  rw [mem_doublyStochastic_iff_sum]
  refine ⟨?_, ?_, ?_⟩
  · intro z w
    cases z <;> cases w <;> simp only [paddedMatrix, Equiv.sumComm_apply, Sum.swap_inl, Sum.swap_inr, augmentedMass]
    · split_ifs
      · exact a.deletionMass_nonneg _
      · exact le_rfl
    · exact a.nonneg _ _
    · exact a.nonneg _ _
    · split_ifs
      · exact a.insertionMass_nonneg _
      · exact le_rfl
  · intro z
    cases z <;> simp [paddedMatrix, augmentedMass, Fintype.sum_sum_type,
      deletionMass, insertionMass]
  · intro w
    cases w <;> simp [paddedMatrix, augmentedMass, Fintype.sum_sum_type,
      deletionMass, insertionMass]

private def assignmentLinearCost (c : I → J → ℝ) (u : I → ℝ) (v : J → ℝ) :
    Matrix (I ⊕ J) (I ⊕ J) ℝ →ₗ[ℝ] ℝ where
  toFun Q := ∑ z, ∑ w, Q z w * boundaryAssignmentEntryWith c u v z (Equiv.sumComm I J w)
  map_add' Q R := by simp [add_mul, Finset.sum_add_distrib]
  map_smul' r Q := by
    change (∑ z, ∑ w, (r * Q z w) * _) = r * (∑ z, ∑ w, Q z w * _)
    simp only [mul_assoc, Finset.mul_sum]

private theorem assignmentLinearCost_padded (a : FiniteBoundaryPlan I J)
    (c : I → J → ℝ) (u : I → ℝ) (v : J → ℝ) :
    assignmentLinearCost c u v a.paddedMatrix = a.linearCost c u v := by
  simp [assignmentLinearCost, paddedMatrix, augmentedMass, boundaryAssignmentEntryWith,
    Fintype.sum_sum_type, Finset.sum_add_distrib, linearCost]
  ring

private theorem assignmentLinearCost_perm (c : I → J → ℝ) (u : I → ℝ) (v : J → ℝ)
    (σ : Equiv.Perm (I ⊕ J)) :
    assignmentLinearCost c u v (σ.permMatrix ℝ) =
      boundaryAssignmentCostWith c u v (σ.trans (Equiv.sumComm I J)) := by
  simp only [assignmentLinearCost, LinearMap.coe_mk, AddHom.coe_mk,
    PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq,
    ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true,
    boundaryAssignmentCostWith, Equiv.trans_apply]

/-- Birkhoff decomposition gives a partial matching no more expensive than
any real plan, for arbitrary fixed pair and boundary coefficients. -/
theorem exists_matching_linearCost_le (a : FiniteBoundaryPlan I J)
    (c : I → J → ℝ) (u : I → ℝ) (v : J → ℝ) :
    ∃ M : OccurrenceMatching I J PEmpty.{1} PEmpty.{1},
      M.totalBoundaryCost c u v ≤ a.linearCost c u v := by
  let : Nonempty (OccurrenceMatching I J PEmpty.{1} PEmpty.{1}) :=
    occurrenceMatching_nonempty_iff.mpr (by simp)
  obtain ⟨M, hM⟩ := exists_eq_ciInf_of_finite
    (f := fun M : OccurrenceMatching I J PEmpty.{1} PEmpty.{1} => M.totalBoundaryCost c u v)
  have hmin (N : OccurrenceMatching I J PEmpty.{1} PEmpty.{1}) :
      M.totalBoundaryCost c u v ≤ N.totalBoundaryCost c u v :=
    hM.le.trans (ciInf_le (Set.finite_range _).bddBelow N)
  obtain ⟨w, hw, hsum, hdecomp⟩ :=
    exists_eq_sum_perm_of_mem_doublyStochastic a.paddedMatrix_doublyStochastic
  have hl (σ : Equiv.Perm (I ⊕ J)) :
      M.totalBoundaryCost c u v ≤ assignmentLinearCost c u v (σ.permMatrix ℝ) := by
    rw [assignmentLinearCost_perm, ← OccurrenceMatching.totalBoundaryCost_ofBoundaryAssignment]
    exact hmin _
  refine ⟨M, ?_⟩
  calc
    _ = ∑ σ, w σ * M.totalBoundaryCost c u v := by rw [← Finset.sum_mul, hsum, one_mul]
    _ ≤ ∑ σ, w σ * assignmentLinearCost c u v (σ.permMatrix ℝ) :=
      Finset.sum_le_sum fun σ _ => mul_le_mul_of_nonneg_left (hl σ) (hw σ)
    _ = assignmentLinearCost c u v a.paddedMatrix := by rw [← hdecomp]; simp
    _ = _ := assignmentLinearCost_padded a c u v

/-- First-order matching remains bounded by every feasible fractional plan. -/
theorem matchingCost_le_cost (a : FiniteBoundaryPlan I J)
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    finiteFirstOrderMatchingCost x y ≤ a.cost x y := by
  obtain ⟨M, hM⟩ := a.exists_matching_linearCost_le
    (fun i j => (finitePairCost (x i) (y j)).toReal)
    (fun i => (diagonalCost (x i)).toReal) (fun j => (diagonalCost (y j)).toReal)
  change M.totalFiniteCost x y ≤ a.cost x y at hM
  exact (finiteFirstOrderMatchingCost_le_totalFiniteCost x y M).trans hM

end FiniteBoundaryPlan

variable {I J : Type*} [Fintype I] [Fintype J]

/-- Infimum over all feasible real boundary-reservoir plans at unit occurrence mass. -/
def finiteFirstOrderBoundaryTransportCost (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) : ℝ :=
  ⨅ a : FiniteBoundaryPlan I J, a.cost x y

theorem finiteFirstOrderBoundaryTransportCost_le_cost
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) (a : FiniteBoundaryPlan I J) :
    finiteFirstOrderBoundaryTransportCost x y ≤ a.cost x y :=
  ciInf_le ⟨0, by rintro _ ⟨b, rfl⟩; exact b.cost_nonneg x y⟩ a

/-- Exact equality of finite real reservoir transport and partial-matching optimization.
The algebra holds for arbitrary real pairs; positive lifetimes give the PD interpretation. -/
theorem finiteFirstOrderBoundaryTransportCost_eq_matchingCost
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    finiteFirstOrderBoundaryTransportCost x y = finiteFirstOrderMatchingCost x y := by
  apply le_antisymm
  · obtain ⟨M, hM⟩ := exists_minimizing_occurrenceMatching x y
    calc
      _ ≤ (FiniteBoundaryPlan.ofMatching M).cost x y :=
        finiteFirstOrderBoundaryTransportCost_le_cost _ _ _
      _ = _ := by rw [FiniteBoundaryPlan.cost_ofMatching, hM]
  · exact le_ciInf fun a => a.matchingCost_le_cost x y

/-- Some integral incidence plan attains the real infimum; other optima may be fractional. -/
theorem exists_minimizing_boundaryPlan (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    ∃ M : OccurrenceMatching I J PEmpty.{1} PEmpty.{1},
      (FiniteBoundaryPlan.ofMatching M).cost x y = finiteFirstOrderBoundaryTransportCost x y := by
  obtain ⟨M, hM⟩ := exists_minimizing_occurrenceMatching x y
  exact ⟨M, by rw [FiniteBoundaryPlan.cost_ofMatching,
    finiteFirstOrderBoundaryTransportCost_eq_matchingCost, hM]⟩

/-- Every real plan admits a partial matching of no greater cost. -/
theorem FiniteBoundaryPlan.exists_matching_cost_le (a : FiniteBoundaryPlan I J)
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    ∃ M : OccurrenceMatching I J PEmpty.{1} PEmpty.{1}, M.totalFiniteCost x y ≤ a.cost x y := by
  obtain ⟨M, hM⟩ := exists_minimizing_occurrenceMatching x y
  exact ⟨M, hM.le.trans (a.matchingCost_le_cost x y)⟩

@[simp] theorem finiteFirstOrderBoundaryTransportCost_of_isEmpty_right [IsEmpty J]
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    finiteFirstOrderBoundaryTransportCost x y = ∑ i, (diagonalCost (x i)).toReal := by
  rw [finiteFirstOrderBoundaryTransportCost_eq_matchingCost,
    finiteFirstOrderMatchingCost_of_isEmpty_right]

@[simp] theorem finiteFirstOrderBoundaryTransportCost_of_isEmpty_left [IsEmpty I]
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    finiteFirstOrderBoundaryTransportCost x y = ∑ j, (diagonalCost (y j)).toReal := by
  rw [finiteFirstOrderBoundaryTransportCost_eq_matchingCost,
    finiteFirstOrderMatchingCost_of_isEmpty_left]

@[simp] theorem finiteFirstOrderBoundaryTransportCost_empty [IsEmpty I] [IsEmpty J]
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) : finiteFirstOrderBoundaryTransportCost x y = 0 := by
  rw [finiteFirstOrderBoundaryTransportCost_of_isEmpty_right]
  exact Fintype.sum_empty _

theorem finiteFirstOrderBoundaryTransportCost_reindex {I' J' : Type*}
    [Fintype I'] [Fintype J'] (u : I' ≃ I) (v : J' ≃ J)
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    finiteFirstOrderBoundaryTransportCost (x ∘ u) (y ∘ v) =
      finiteFirstOrderBoundaryTransportCost x y := by
  simp only [finiteFirstOrderBoundaryTransportCost_eq_matchingCost,
    finiteFirstOrderMatchingCost_reindex]

end TDA.Persistence
