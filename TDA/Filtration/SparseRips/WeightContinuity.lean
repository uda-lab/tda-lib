import TDA.Filtration.SparseRips.Relaxed

/-!
# Continuity of sparse Rips weights

The piecewise weight is the maximum of zero and the minimum of two affine
functions. This form makes the closed relaxed entry thresholds explicit.
-/

namespace TDA.Filtration.SparseRips

noncomputable section

/-- A continuous max/min form of the three weight branches. -/
theorem finiteWeight_eq_max_min {η t : ℝ} (hη : 0 ≤ η) (hη' : η ≤ 1 / 2)
    (ht : 0 ≤ t) (r : ℝ) :
    finiteWeight η t r = max 0 (min ((r - (1 - 2 * η) * t) / 2) (η * r)) := by
  have ha : 0 ≤ (1 - 2 * η) * t := mul_nonneg (by linarith) ht
  unfold finiteWeight
  split_ifs with h₁ h₂
  · have hm : min ((r - (1 - 2 * η) * t) / 2) (η * r) ≤ 0 :=
      (min_le_left _ _).trans (by linarith)
    exact (max_eq_left hm).symm
  · have hpos : 0 ≤ (r - (1 - 2 * η) * t) / 2 := by linarith
    have hmin : (r - (1 - 2 * η) * t) / 2 ≤ η * r := by
      nlinarith [mul_nonneg (show 0 ≤ 1 - 2 * η by linarith)
        (show 0 ≤ t - r by linarith)]
    rw [min_eq_left hmin, max_eq_right hpos]
  · have hr : 0 ≤ r := ht.trans (le_of_not_gt h₂)
    have hpos : 0 ≤ η * r := mul_nonneg hη hr
    have hmin : η * r ≤ (r - (1 - 2 * η) * t) / 2 := by
      nlinarith [mul_nonneg (show 0 ≤ 1 - 2 * η by linarith)
        (show 0 ≤ r - t by linarith)]
    rw [min_eq_right hmin, max_eq_right hpos]

/-- Each finite-deletion weight varies continuously with scale. -/
theorem continuous_finiteWeight {η t : ℝ} (hη : 0 ≤ η) (hη' : η ≤ 1 / 2)
    (ht : 0 ≤ t) : Continuous (finiteWeight η t) := by
  have hfun : Continuous (fun r : ℝ =>
      max 0 (min ((r - (1 - 2 * η) * t) / 2) (η * r))) := by
    fun_prop
  convert hfun using 1
  funext r
  exact finiteWeight_eq_max_min hη hη' ht r

/-- The immortal vertex has zero weight; other vertices inherit continuity. -/
theorem continuous_weight {η : ℝ} (hη : 0 ≤ η) (hη' : η ≤ 1 / 2)
    (time : Option ℝ) (ht : ∀ t ∈ time, 0 ≤ t) :
    Continuous (weight η time) := by
  cases time with
  | none =>
      change Continuous (fun _ : ℝ => (0 : ℝ))
      exact continuous_const
  | some t =>
      change Continuous (finiteWeight η t)
      exact continuous_finiteWeight hη hη' (ht t (by simp))

/-- Relaxed pairwise dissimilarity is continuous in the scale. -/
theorem continuous_relaxedDistance {V : Type*} [MetricSpace V] {η : ℝ}
    (hη : 0 ≤ η) (hη' : η ≤ 1 / 2) (time : V → Option ℝ)
    (ht : ∀ x t, t ∈ time x → 0 ≤ t) (x y : V) :
    Continuous (relaxedDistance η time · x y) := by
  change Continuous (fun r : ℝ =>
    dist x y + weight η (time x) r + weight η (time y) r)
  exact (continuous_const.add (continuous_weight hη hη' (time x) (ht x))).add
    (continuous_weight hη hη' (time y) (ht y))

end

end TDA.Filtration.SparseRips
