import TDA.Filtration.SparseRips.GreedyNet
import TDA.Filtration.SparseRips.Weight

/-!
# Geometric deletion maps for greedy sparse Rips complexes

Deletion time is the insertion radius divided by `η * (1 - 2 * η)`. The initial
vertex survives forever. A vertex deleted at scale `r` is sent to the greedy net
at threshold `η * r`, whose points have zero weight and survive strictly past `r`.
Active vertices are fixed. This gives the domination inequality used by simplicial
contiguity without assuming a net tree or a topological equivalence.
-/

namespace TDA.Filtration.SparseRips

open GreedyNet

noncomputable section

variable {V : Type*} [MetricSpace V] [Fintype V]

/-- Finite deletion times, with `none` for the initial vertex. -/
def deletionTime (seed : V) (η : ℝ) (x : V) : Option ℝ :=
  (insertionRadius seed x).map (fun ρ => ρ / (η * (1 - 2 * η)))

/-- The open active set uses a strict inequality at deletion-time ties. -/
def OpenActive (time : Option ℝ) (r : ℝ) : Prop :=
  time.elim True (fun t => r < t)

/-- The closed active set retains a vertex at its deletion time. -/
def ClosedActive (time : Option ℝ) (r : ℝ) : Prop :=
  time.elim True (fun t => r ≤ t)

@[simp] theorem deletionTime_seed (seed : V) (η : ℝ) : deletionTime seed η seed = none := by
  simp [deletionTime]

@[simp] theorem openActive_none (r : ℝ) : OpenActive none r := trivial

@[simp] theorem closedActive_none (r : ℝ) : ClosedActive none r := trivial

theorem deletionTime_of_ne (seed : V) (η : ℝ) {x : V} (hx : x ≠ seed) :
    deletionTime seed η x = some
      (radius seed (insertionIndex seed x - 1) / (η * (1 - 2 * η))) := by
  simp [deletionTime, insertionRadius, (insertionIndex_eq_zero_iff seed x).not.mpr hx]

private theorem parameter_pos {η : ℝ} (hη : 0 < η) (hη' : η ≤ 1 / 3) :
    0 < η * (1 - 2 * η) := mul_pos hη (by linarith)

theorem deletionTime_nonneg (seed : V) {η : ℝ} (hη : 0 < η) (hη' : η ≤ 1 / 3)
    (x : V) : ∀ t ∈ deletionTime seed η x, 0 ≤ t := by
  intro t ht
  by_cases hx : x = seed
  · simp [hx] at ht
  · rw [deletionTime_of_ne seed η hx] at ht
    have heq : t = radius seed (insertionIndex seed x - 1) / (η * (1 - 2 * η)) := by
      simpa [eq_comm] using ht
    rw [heq]
    exact div_nonneg (radius_nonneg seed _) (parameter_pos hη hη').le

/-- The geometric witness lies beyond the deletion boundary and has weight zero. -/
theorem netPoint_active_weight_zero (seed : V) {η r : ℝ}
    (hη : 0 < η) (hη' : η ≤ 1 / 3) (hr : 0 ≤ r) (x : V) :
    let q := netPoint seed (η * r) (mul_nonneg hη.le hr) x
    OpenActive (deletionTime seed η q) r ∧ weight η (deletionTime seed η q) r = 0 := by
  dsimp only
  let q := netPoint seed (η * r) (mul_nonneg hη.le hr) x
  change OpenActive (deletionTime seed η q) r ∧ weight η (deletionTime seed η q) r = 0
  have hq := (mem_threshold_iff seed q (η * r) (mul_nonneg hη.le hr)).mp
    (netPoint_mem seed (η * r) (mul_nonneg hη.le hr) x)
  rcases hq with hq | hq
  · rw [hq, deletionTime_seed]
    simp [OpenActive]
  · by_cases hqs : q = seed
    · rw [hqs, deletionTime_seed]
      simp [OpenActive]
    · rw [deletionTime_of_ne seed η hqs]
      simp only [OpenActive, Option.elim_some, weight_some]
      have hp := parameter_pos hη hη'
      have hfactor : 0 < 1 - 2 * η := by linarith
      have hηr := mul_nonneg hη.le hr
      have htime : r < radius seed (insertionIndex seed q - 1) / (η * (1 - 2 * η)) := by
        apply (lt_div_iff₀ hp).mpr
        have hprod := mul_nonneg hη.le hηr
        have hbound : η * (1 - 2 * η) * r ≤ η * r := by nlinarith
        nlinarith
      refine ⟨htime, finiteWeight_of_le ?_⟩
      have hcancel : (1 - 2 * η) *
          (radius seed (insertionIndex seed q - 1) / (η * (1 - 2 * η))) =
          radius seed (insertionIndex seed q - 1) / η := by
        field_simp [ne_of_gt hη, ne_of_gt hfactor]
      rw [hcancel]
      exact (le_div_iff₀ hη).mpr (by nlinarith)

/-- Fix active vertices and send removed vertices to the proved greedy covering net. -/
def deletionMap (seed : V) (η r : ℝ) (hη : 0 ≤ η) (hr : 0 ≤ r) (x : V) : V := by
  classical
  exact if OpenActive (deletionTime seed η x) r then x
    else netPoint seed (η * r) (mul_nonneg hη hr) x

@[simp] theorem deletionMap_of_active (seed : V) {η r : ℝ} (hη : 0 ≤ η) (hr : 0 ≤ r)
    {x : V} (hx : OpenActive (deletionTime seed η x) r) :
    deletionMap seed η r hη hr x = x := by
  simp [deletionMap, hx]

theorem deletionMap_active (seed : V) {η r : ℝ}
    (hη : 0 < η) (hη' : η ≤ 1 / 3) (hr : 0 ≤ r) (x : V) :
    OpenActive (deletionTime seed η (deletionMap seed η r hη.le hr x)) r := by
  classical
  by_cases hx : OpenActive (deletionTime seed η x) r
  · simp [deletionMap, hx]
  · simpa [deletionMap, hx] using (netPoint_active_weight_zero seed hη hη' hr x).1

/-- The deletion projection satisfies the precise weighted domination inequality. -/
theorem deletionMap_domination (seed : V) {η r : ℝ}
    (hη : 0 < η) (hη' : η ≤ 1 / 3) (hr : 0 ≤ r) (x : V) :
    dist x (deletionMap seed η r hη.le hr x) ≤
      weight η (deletionTime seed η x) r -
        weight η (deletionTime seed η (deletionMap seed η r hη.le hr x)) r := by
  classical
  by_cases hx : OpenActive (deletionTime seed η x) r
  · simp [deletionMap, hx]
  · have hxs : x ≠ seed := by
      intro h
      apply hx
      simp [h]
    have htime := deletionTime_of_ne seed η hxs
    have hfinite : 0 ≤ radius seed (insertionIndex seed x - 1) / (η * (1 - 2 * η)) :=
      div_nonneg (radius_nonneg seed _) (parameter_pos hη hη').le
    have hremoved : radius seed (insertionIndex seed x - 1) / (η * (1 - 2 * η)) ≤ r := by
      simpa [htime, OpenActive] using hx
    have hw : weight η (deletionTime seed η x) r = η * r := by
      rw [htime, weight_some]
      exact finiteWeight_of_time_le hη.le hfinite hremoved
    simp only [deletionMap, if_neg hx, hw]
    rw [(netPoint_active_weight_zero seed hη hη' hr x).2, sub_zero]
    exact dist_netPoint_le seed (η * r) (mul_nonneg hη.le hr) x

end

end TDA.Filtration.SparseRips
