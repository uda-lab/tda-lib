import TDA.Filtration.SparseRips.UnionDeletion
import TDA.Filtration.SparseRips.Sparsity
import TDA.Filtration.SparseRips.LogDiagramStability

/-!
# Sparse Rips boundary and deletion examples

Two points at distance one have one finite insertion radius. At sparsification
parameter one third, the second vertex is deleted at time nine. Its singleton
is present in the closed active complex at time nine and absent at time ten,
while the sparse inclusion filtration retains the earlier singleton.
-/

namespace TDA.Filtration.SparseRips.Examples

open GreedyNet

noncomputable section

/-- Both weight breakpoints use their specified closed boundary values. -/
theorem weight_breakpoints : finiteWeight (1 / 3) 9 3 = 0 ∧
    finiteWeight (1 / 3) 9 6 = 3 / 2 ∧ finiteWeight (1 / 3) 9 9 = 3 := by
  norm_num [finiteWeight]

/-- Equal deletion times are closed-active and simultaneously cease to be open-active. -/
theorem deletion_tie : ClosedActive (some 9) 9 ∧ ¬ OpenActive (some 9) 9 := by
  norm_num [ClosedActive, OpenActive]

namespace TwoPoints

private def pts (i : Fin 2) : ℝ := i.val

private theorem pts_injective : Function.Injective pts := by
  intro i j hij
  apply Fin.ext
  change (i.val : ℝ) = (j.val : ℝ) at hij
  exact_mod_cast hij

local instance : MetricSpace (Fin 2) := MetricSpace.induced pts pts_injective inferInstance

private theorem metric_dist (i j : Fin 2) : dist i j = dist (pts i) (pts j) := rfl

private theorem next_zero : next (0 : Fin 2) ({0}) = 1 := by
  have hnot := next_not_mem (0 : Fin 2) (n := 0) (by decide)
  have hne : next (0 : Fin 2) ({0}) ≠ 0 := by simpa using hnot
  apply Fin.ext
  have hi := (next (0 : Fin 2) ({0})).isLt
  have hn : (next (0 : Fin 2) ({0})).val ≠ 0 := fun h => hne (Fin.ext h)
  omega

private theorem radius_zero : radius (0 : Fin 2) 0 = 1 := by
  norm_num [radius, next_zero, greedyPrefix, nearestDistance, metric_dist, pts, Real.dist_eq]

private theorem insertionIndex_one : insertionIndex (0 : Fin 2) 1 = 1 := by
  have hpos : 0 < insertionIndex (0 : Fin 2) 1 := by
    have hne := (insertionIndex_eq_zero_iff (0 : Fin 2) 1).not.mpr (by decide)
    omega
  have hmem : (1 : Fin 2) ∈ greedyPrefix 0 1 := by simp [greedyPrefix, next_zero]
  have hle : insertionIndex (0 : Fin 2) 1 ≤ 1 := by
    by_contra! hgt
    exact not_mem_before_insertionIndex 0 1 hgt hmem
  omega

theorem deletionTime_one : deletionTime (0 : Fin 2) (1 / 3) 1 = some 9 := by
  rw [deletionTime_of_ne 0 (1 / 3) (by decide)]
  norm_num [insertionIndex_one, radius_zero]

/-- The self-pair is weighted: its relaxed value is six at deletion time nine. -/
theorem weighted_self_pair :
    relaxedDistance (1 / 3) (deletionTime (0 : Fin 2) (1 / 3)) 9 1 1 = 6 := by
  rw [relaxedDistance_self, deletionTime_one]
  norm_num [weight, finiteWeight]

/-- The attained relaxed entry of the genuine edge is its metric distance.
The later deletion at time nine does not change this first entry. -/
theorem edge_pairEntry_eq_one :
    pairEntry (η := 1 / 3) (deletionTime (0 : Fin 2) (1 / 3)) 0 1 = 1 := by
  have hle : pairEntry (η := 1 / 3) (deletionTime (0 : Fin 2) (1 / 3)) 0 1 ≤ 1 :=
    (pairEntry_le_iff (by norm_num) (by norm_num)
      (deletionTime (0 : Fin 2) (1 / 3))
      (deletionTime_nonneg 0 (by norm_num) (by norm_num)) 0 1 (by norm_num)).mpr (by
        norm_num [relaxedDistance, deletionTime_one, weight, finiteWeight,
          metric_dist, pts, Real.dist_eq])
  have hge := dist_le_pairEntry (η := (1 / 3 : ℝ)) (by norm_num) (by norm_num)
    (deletionTime (0 : Fin 2) (1 / 3))
    (deletionTime_nonneg 0 (by norm_num) (by norm_num)) 0 1
  have hdist : dist (0 : Fin 2) 1 = 1 := by norm_num [metric_dist, pts, Real.dist_eq]
  exact le_antisymm hle (hdist ▸ hge)

/-- A genuine finite deletion, including the closed tie boundary. -/
theorem singleton_at_deletion :
    ({1} : Finset (Fin 2)) ∈ closedActiveComplex 0 (1 / 3) 9 := by
  refine ⟨⟨by simp, by norm_num, ?_⟩, ?_⟩
  · intro x hx y hy
    simp only [Finset.mem_singleton] at hx hy
    subst x; subst y
    rw [weighted_self_pair]
    norm_num
  · intro x hx
    simp only [Finset.mem_singleton] at hx
    subst x
    norm_num [deletionTime_one, ClosedActive]

theorem singleton_after_deletion :
    ({1} : Finset (Fin 2)) ∉ closedActiveComplex 0 (1 / 3) 10 := by
  intro h
  have hx := h.2 1 (by simp)
  norm_num [deletionTime_one, ClosedActive] at hx

/-- The moving active complexes shrink, while the ordinary sparse filtration retains the face. -/
theorem sparse_retains_deleted_singleton :
    ({1} : Finset (Fin 2)) ∈ sparseFiltration 0 (1 / 3) 10 :=
  ⟨9, by norm_num, by norm_num, singleton_at_deletion⟩

end TwoPoints

namespace LineSamples

private def point (n : ℕ) (i : Fin n) : ℝ := i.val

private theorem point_injective (n : ℕ) : Function.Injective (point n) := by
  intro i j hij
  apply Fin.ext
  change (i.val : ℝ) = (j.val : ℝ) at hij
  exact_mod_cast hij

local instance (n : ℕ) : MetricSpace (Fin n) :=
  MetricSpace.induced (point n) (point_injective n) inferInstance

/-- One doubling bound applies to every cardinality in the line-sample family. -/
theorem doubling_four (n : ℕ) : ClosedBallDoubling (V := Fin n) 4 :=
  ClosedBallDoubling.of_isometry_real (point n)
    (isometry_iff_dist_eq.mpr (fun _ _ => rfl))

/-- The same constant bounds every member of this increasing family of line samples. -/
theorem uniform_skeleton_bound (n m h : ℕ) {η : ℝ}
    (hη : 0 < η) (hη' : η ≤ 1 / 3)
    (hsmall : 2 / (2 : ℝ) ^ h < η * (1 - 2 * η)) :
    (skeletonFaces (0 : Fin (n + 1)) η m).card ≤
      (n + 1) * ∑ j ∈ Finset.range (m + 1), (4 ^ h) ^ j := by
  simpa using skeletonFaces_card_le (0 : Fin (n + 1)) hη hη' (doubling_four (n + 1)) h hsmall m

end LineSamples

end

end TDA.Filtration.SparseRips.Examples
