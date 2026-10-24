import TDA.Filtration.SparseRips.WeightContinuity

/-!
# Attained relaxed pair entry times

The relaxed threshold is closed, and its defining inequality remains valid at
all later nonnegative scales. This gives an actual first entry time, including
weighted self-pairs, without pretending the dissimilarity is a metric.
-/

namespace TDA.Filtration.SparseRips

noncomputable section

variable {V : Type*} [MetricSpace V] {η : ℝ}
    (hη : 0 ≤ η) (hη' : η ≤ 1 / 3) (time : V → Option ℝ)
    (ht : ∀ x t, t ∈ time x → 0 ≤ t)

/-- Closed admissible scales for a relaxed pair, including a self-pair. -/
def pairEntrySet (x y : V) : Set ℝ :=
  {r | 0 ≤ r ∧ relaxedDistance η time r x y ≤ r}

/-- The least scale at which a relaxed pair occurs. -/
def pairEntry (x y : V) : ℝ :=
  sInf (pairEntrySet (η := η) time x y)

include hη hη' ht

theorem pairEntrySet_closed (x y : V) : IsClosed (pairEntrySet (η := η) time x y) := by
  unfold pairEntrySet
  exact isClosed_Ici.inter
    (isClosed_le (continuous_relaxedDistance hη (by linarith) time ht x y) continuous_id)

omit ht in
theorem pairEntrySet_nonempty (x y : V) :
    (pairEntrySet (η := η) time x y).Nonempty := by
  refine ⟨3 * dist x y, ?_⟩
  have hr : 0 ≤ 3 * dist x y := by positivity
  have hx := weight_le hη (by linarith : η ≤ 1 / 2) hr (time x)
  have hy := weight_le hη (by linarith : η ≤ 1 / 2) hr (time y)
  change 0 ≤ 3 * dist x y ∧
    dist x y + weight η (time x) (3 * dist x y) +
      weight η (time y) (3 * dist x y) ≤ 3 * dist x y
  constructor
  · exact hr
  · nlinarith [dist_nonneg (x := x) (y := y)]

omit hη hη' ht in
theorem pairEntrySet_bddBelow (x y : V) :
    BddBelow (pairEntrySet (η := η) time x y) :=
  ⟨0, fun _ h => h.1⟩

theorem pairEntry_mem (x y : V) :
    pairEntry (η := η) time x y ∈ pairEntrySet (η := η) time x y :=
  (pairEntrySet_closed hη hη' time ht x y).csInf_mem
    (pairEntrySet_nonempty hη hη' time x y)
    (pairEntrySet_bddBelow (η := η) time x y)

theorem pairEntry_nonneg (x y : V) : 0 ≤ pairEntry (η := η) time x y :=
  (pairEntry_mem hη hη' time ht x y).1

omit hη hη' ht in
theorem pairEntry_le_of_mem (x y : V) {r : ℝ}
    (hr : r ∈ pairEntrySet (η := η) time x y) :
    pairEntry (η := η) time x y ≤ r :=
  csInf_le (pairEntrySet_bddBelow (η := η) time x y) hr

theorem pairEntrySet_mono (x y : V) {r s : ℝ}
    (hr : r ∈ pairEntrySet (η := η) time x y) (hrs : r ≤ s) :
    s ∈ pairEntrySet (η := η) time x y := by
  have hx := (weight_increment hη (by linarith : η ≤ 1 / 2)
    (time x) (ht x) hr.1 hrs).2
  have hy := (weight_increment hη (by linarith : η ≤ 1 / 2)
    (time y) (ht y) hr.1 hrs).2
  change 0 ≤ s ∧
    dist x y + weight η (time x) s + weight η (time y) s ≤ s
  constructor
  · exact hr.1.trans hrs
  · dsimp [pairEntrySet, relaxedDistance] at hr
    linarith [hr.2]

theorem pairEntry_le_iff (x y : V) {r : ℝ} (hr : 0 ≤ r) :
    pairEntry (η := η) time x y ≤ r ↔ relaxedDistance η time r x y ≤ r := by
  constructor
  · intro h
    exact (pairEntrySet_mono hη hη' time ht x y
      (pairEntry_mem hη hη' time ht x y) h).2
  · intro h
    exact pairEntry_le_of_mem (η := η) time x y ⟨hr, h⟩

/-- Distinct pair entry cannot precede its genuine metric distance. -/
theorem dist_le_pairEntry (x y : V) :
    dist x y ≤ pairEntry (η := η) time x y := by
  have h := (pairEntry_mem hη hη' time ht x y).2
  have hx := weight_nonneg hη (pairEntry_nonneg hη hη' time ht x y) (time x)
  have hy := weight_nonneg hη (pairEntry_nonneg hη hη' time ht x y) (time y)
  dsimp [relaxedDistance] at h
  linarith

end

end TDA.Filtration.SparseRips
