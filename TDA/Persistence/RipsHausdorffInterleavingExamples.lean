import TDA.Persistence.RipsHausdorffInterleaving
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Order.Interval.Set.Infinite

/-!
# Nonclosed infinite images in Rips module stability

The open and closed unit intervals have the same closure in ℝ. Their Rips
homology modules therefore have interleaving distance zero and actual
interleavings at every positive parameter, in every degree. The near-point
construction applies although one image is nonclosed. No zero-parameter
interleaving or fiberwise inclusion isomorphism is asserted.
-/

namespace TDA.Persistence.RipsHausdorffInterleavingExamples

open TDA.Filtration Set Metric
open scoped NNReal ENNReal

/-- The open unit interval, with its inherited metric and vertex order. -/
abbrev OpenInterval := Ioo (0 : ℝ) 1

/-- The closed unit interval, with its inherited metric and vertex order. -/
abbrev ClosedInterval := Icc (0 : ℝ) 1

private theorem open_range : range (Subtype.val : OpenInterval → ℝ) = Ioo (0 : ℝ) 1 := by
  ext x
  simp

private theorem closed_range : range (Subtype.val : ClosedInterval → ℝ) = Icc (0 : ℝ) 1 := by
  ext x
  simp

private theorem subtype_isometry (s : Set ℝ) : Isometry (Subtype.val : s → ℝ) :=
  fun _ _ => rfl

private theorem interval_hausdorffEDist :
    hausdorffEDist (range (Subtype.val : OpenInterval → ℝ))
      (range (Subtype.val : ClosedInterval → ℝ)) = 0 := by
  rw [open_range, closed_range, hausdorffEDist_zero_iff_closure_eq_closure,
    closure_Ioo (by norm_num : (0 : ℝ) ≠ 1), isClosed_Icc.closure_eq]

private theorem interval_hausdorffDist :
    hausdorffDist (range (Subtype.val : OpenInterval → ℝ))
      (range (Subtype.val : ClosedInterval → ℝ)) = 0 := by
  rw [hausdorffDist, interval_hausdorffEDist, ENNReal.toReal_zero]

/-- Both vertex spaces in this fixture are genuinely infinite. -/
theorem intervals_infinite : Infinite OpenInterval ∧ Infinite ClosedInterval :=
  ⟨Set.Ioo.infinite (by norm_num : (0 : ℝ) < 1),
    Set.Icc.infinite (by norm_num : (0 : ℝ) < 1)⟩

/-- The open image is nonclosed, so compact nearest-point selection is unavailable. -/
theorem open_image_not_isClosed : ¬ IsClosed (range (Subtype.val : OpenInterval → ℝ)) := by
  intro h
  have hzero : (0 : ℝ) ∈ closure (range (Subtype.val : OpenInterval → ℝ)) := by
    rw [open_range, closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
    norm_num
  rw [h.closure_eq, open_range] at hzero
  norm_num at hzero

/-- The total-bounded-image consumer gives distance zero for these infinite intervals. -/
theorem open_closed_interval_distance_zero (R : Type*) [Ring R] (n : ℕ) :
    realInterleavingDistance
      (sublevelModule R (Rips.filter (inferInstance : MetricSpace OpenInterval)) n)
      (sublevelModule R (Rips.filter (inferInstance : MetricSpace ClosedInterval)) n) = 0 := by
  let : Nonempty OpenInterval := ⟨⟨1 / 2, by norm_num⟩⟩
  let : Nonempty ClosedInterval := ⟨⟨0, by norm_num⟩⟩
  have hX : TotallyBounded (range (Subtype.val : OpenInterval → ℝ)) := by
    rw [open_range]
    exact isCompact_Icc.totallyBounded.subset Ioo_subset_Icc_self
  have hY : TotallyBounded (range (Subtype.val : ClosedInterval → ℝ)) := by
    rw [closed_range]
    exact isCompact_Icc.totallyBounded
  have h := Rips.realInterleavingDistance_le_two_mul_hausdorffDist_of_totallyBounded R
    (subtype_isometry (Ioo 0 1)) (subtype_isometry (Icc 0 1)) hX hY n
  exact nonpos_iff_eq_zero.mp (by simpa only [interval_hausdorffDist, mul_zero,
    ENNReal.ofReal_zero] using h)

/-- Every positive error has an actual canonical interleaving, with the empty
negative tail retained. Zero distance does not require an attained zero error. -/
noncomputable def open_closed_interval_interleaving (R : Type*) [Ring R]
    (ε : ℝ≥0) (hε : 0 < ε) (n : ℕ) :
    RealInterleaving ε
      (sublevelModule R (Rips.filter (inferInstance : MetricSpace OpenInterval)) n)
      (sublevelModule R (Rips.filter (inferInstance : MetricSpace ClosedInterval)) n) :=
  Rips.hausdorffInterleavingOfLt R (subtype_isometry (Ioo 0 1))
    (subtype_isometry (Icc 0 1))
    (by rw [interval_hausdorffEDist]; exact ENNReal.zero_ne_top)
    (by rw [interval_hausdorffDist, mul_zero]; exact hε) n

end TDA.Persistence.RipsHausdorffInterleavingExamples
