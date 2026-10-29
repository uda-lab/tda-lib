import TDA.Persistence.AffineSwitchArrangement

/-!
# A fixed-push regression for a single affine cut

For the four points `(0,3)`, `(3,0)`, `(0,4)`, `(5,4)`, all push branches remain
fixed along `m = 1`, `-1 < c < 3`. Nevertheless, the two endpoint costs are equal
at two distinct values of `c` and unequal between them. Both signed affine
factors are therefore needed to describe this comparison. This local regression
concerns a single affine cut for fixed pushes; it makes no claim against the
finite-Ω or finite-maximum theorems for matching distance.
-/

namespace TDA.Persistence.AffineSwitchExamples

open AffineSwitch

/-- The four push branches stay fixed throughout the open intercept interval. -/
theorem regression_pushes (c : ℝ) (hc₀ : -1 < c) (hc₁ : c < 3) :
    push (0, 3) (1, c) = 3 - c ∧
    push (3, 0) (1, c) = 3 ∧
    push (0, 4) (1, c) = 4 - c ∧
    push (5, 4) (1, c) = 5 := by
  simp only [push, one_mul, mul_zero, zero_sub]
  exact ⟨max_eq_right (by linarith), max_eq_left (by linarith),
    max_eq_right (by linarith), max_eq_left (by linarith)⟩

/-- With pair denominator `1` and diagonal denominator `2`, the difference is piecewise affine. -/
theorem regression_cost_difference (c : ℝ) (hc₀ : -1 < c) (hc₁ : c < 3) :
    cost (0, 3) (3, 0) (1, c) 1 - cost (0, 4) (5, 4) (1, c) 2 =
      |c| - (1 + c) / 2 := by
  obtain ⟨hu, hv, hw, hx⟩ := regression_pushes c hc₀ hc₁
  simp only [cost, hu, hv, hw, hx, max_self, mul_one, div_one]
  rw [show 3 - c - 3 = -c by ring, abs_neg,
    abs_of_nonpos (show 4 - c - 5 ≤ 0 by linarith)]
  ring

/-- The two distinct equality points occur inside the same push-branch region. -/
theorem regression_cost_eq_iff (c : ℝ) (hc₀ : -1 < c) (hc₁ : c < 3) :
    cost (0, 3) (3, 0) (1, c) 1 = cost (0, 4) (5, 4) (1, c) 2 ↔
      c = -(1 : ℝ) / 3 ∨ c = 1 := by
  rw [← sub_eq_zero, regression_cost_difference c hc₀ hc₁]
  constructor
  · intro h
    rcases le_total 0 c with hc | hc
    · rw [abs_of_nonneg hc] at h
      right
      linarith
    · rw [abs_of_nonpos hc] at h
      left
      linarith
  · rintro (rfl | rfl) <;> norm_num

/-- Equality at the negative intercept. -/
theorem regression_cost_eq_at_neg_third :
    cost (0, 3) (3, 0) (1, -(1 : ℝ) / 3) 1 =
      cost (0, 4) (5, 4) (1, -(1 : ℝ) / 3) 2 := by
  exact (regression_cost_eq_iff _ (by norm_num) (by norm_num)).2 (Or.inl rfl)

/-- Equality at the positive intercept. -/
theorem regression_cost_eq_at_one :
    cost (0, 3) (3, 0) (1, 1) 1 = cost (0, 4) (5, 4) (1, 1) 2 := by
  exact (regression_cost_eq_iff _ (by norm_num) (by norm_num)).2 (Or.inr rfl)

/-- At an intercept between the equality points, the costs are unequal. -/
theorem regression_cost_ne_at_zero :
    cost (0, 3) (3, 0) (1, 0) 1 ≠ cost (0, 4) (5, 4) (1, 0) 2 := by
  intro h
  have hc := (regression_cost_eq_iff 0 (by norm_num) (by norm_num)).1 h
  norm_num at hc

/-- No single affine equation in the intercept describes equality on this interval. -/
theorem regression_no_single_affine_zero_set :
    ¬ ∃ a b : ℝ, ∀ c : ℝ, -1 < c → c < 3 →
      (cost (0, 3) (3, 0) (1, c) 1 = cost (0, 4) (5, 4) (1, c) 2 ↔
        a * c + b = 0) := by
  rintro ⟨a, b, h⟩
  have hneg := (h (-(1 : ℝ) / 3) (by norm_num) (by norm_num)).1
    regression_cost_eq_at_neg_third
  have hpos := (h 1 (by norm_num) (by norm_num)).1 regression_cost_eq_at_one
  apply regression_cost_ne_at_zero
  apply (h 0 (by norm_num) (by norm_num)).2
  linarith

/-- The difference and sum factors give two separate affine cuts in `(m,c)`. -/
theorem regression_signed_factors (m c : ℝ) :
    2 * (3 - c - 3 * m) - (4 - c - 5 * m) = 2 - c - m ∧
    2 * (3 - c - 3 * m) + (4 - c - 5 * m) = 10 - 3 * c - 11 * m := by
  constructor <;> ring

/-- At slope one, the two signed factors vanish at the two equality points. -/
theorem regression_signed_factors_zero_iff (c : ℝ) :
    (2 - c - (1 : ℝ)) * (10 - 3 * c - 11 * 1) = 0 ↔
      c = -(1 : ℝ) / 3 ∨ c = 1 := by
  rw [mul_eq_zero]
  constructor
  · rintro (h | h)
    · right; linarith
    · left; linarith
  · rintro (rfl | rfl) <;> norm_num

/-- The union of the two signed affine cuts gives exactly the cost equalities. -/
theorem regression_cost_eq_signed_factors (c : ℝ) (hc₀ : -1 < c) (hc₁ : c < 3) :
    cost (0, 3) (3, 0) (1, c) 1 = cost (0, 4) (5, 4) (1, c) 2 ↔
      (2 - c - (1 : ℝ)) * (10 - 3 * c - 11 * 1) = 0 := by
  rw [regression_cost_eq_iff c hc₀ hc₁, regression_signed_factors_zero_iff]

/-- Two vertically aligned endpoints for a nonconstant-cost sign-cell example. -/
noncomputable def verticalPoints : Finset (ℝ × ℝ) := by
  classical
  exact {(0, 0), (0, 1)}

private theorem vertical_first {s : ℝ × ℝ} (hs : s ∈ verticalPoints) : s.1 = 0 := by
  simp only [verticalPoints, Finset.mem_insert, Finset.mem_singleton] at hs
  rcases hs with rfl | rfl <;> rfl

/-- Distinct slopes can lie in the same cell of the full exhaustive arrangement. -/
theorem vertical_sameCell : SameCell verticalPoints (2, -1) (3, -1) := by
  classical
  apply (sameCell_iff _ _ _).2
  intro f hf
  simp only [cuts, Finset.mem_insert, Finset.mem_union, Finset.mem_image] at hf
  rcases hf with rfl | ⟨s, hs, rfl⟩ | ⟨i, _, rfl⟩
  · norm_num [slopeCut, Form.eval]
  · simp [pushCut, Form.eval, vertical_first hs]
  · have hb (s : verticalPoints) (b : Bool) :
        (branch s b).eval (2, -1) = (branch s b).eval (3, -1) := by
      cases b <;> simp [branch, Form.eval, vertical_first s.property]
    simp only [SwitchIndex.form, eval_switchForm, hb]

/-- The endpoint cost is positive at both parameters, but its value changes. -/
theorem vertical_cost_values :
    cost (0, 0) (0, 1) (2, -1) 1 = (1 : ℝ) / 2 ∧
    cost (0, 0) (0, 1) (3, -1) 1 = (1 : ℝ) / 3 := by
  norm_num [cost, push]

/-- The public cell API preserves both a weak comparison and an equal-cost degeneracy. -/
theorem vertical_comparison_invariance :
    (cost (0, 0) (0, 1) (2, -1) 2 ≤ cost (0, 0) (0, 1) (2, -1) 1 ↔
      cost (0, 0) (0, 1) (3, -1) 2 ≤ cost (0, 0) (0, 1) (3, -1) 1) ∧
    (cost (0, 0) (0, 1) (2, -1) 1 = cost (0, 1) (0, 0) (2, -1) 1 ↔
      cost (0, 0) (0, 1) (3, -1) 1 = cost (0, 1) (0, 0) (3, -1) 1) := by
  let u : verticalPoints := ⟨(0, 0), by simp [verticalPoints]⟩
  let v : verticalPoints := ⟨(0, 1), by simp [verticalPoints]⟩
  exact ⟨vertical_sameCell.cost_le_iff u v u v true false,
    vertical_sameCell.cost_eq_iff u v v u false false⟩

/-- The zero cut remains present for this nonempty, nontrivial finite input. -/
theorem vertical_zero_mem_cuts : Form.mk 0 0 0 ∈ cuts verticalPoints := by
  apply zero_mem_cuts
  exact ⟨(0, 0), by simp [verticalPoints]⟩

/-- Both normalization formulas agree at the slope-one boundary. -/
theorem vertical_cost_at_slope_one : cost (0, 0) (0, 1) (1, -1) 1 = 1 := by
  rw [cost_of_slope_le_one _ _ _ _ (by norm_num)]
  norm_num [push]

end TDA.Persistence.AffineSwitchExamples
