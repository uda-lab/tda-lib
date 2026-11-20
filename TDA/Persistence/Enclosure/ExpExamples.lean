import TDA.Persistence.Enclosure.Exp
import TDA.Persistence.GaussianGram

/-!
# Executed rational enclosures of the exponential

Each interval fixture states the complete value of `expEnclosure?`.

* `schedule_zero`, `schedule_large`, `expTaylor_five`: the halvings, tolerance bits and number of
  Taylor terms of two requests, and one Taylor polynomial.
* `zero_coarse`: the argument `0`.
* `one_coarse`, `one_fine`, `one_tiny`: the argument `-1` at tolerances `1 / 100`, `1 / 10 ^ 6`
  and `1 / 10 ^ 30`; `one_refines` checks that the second interval lies inside the first.
* `reduced`, `third`: the arguments `-7 / 3`, with two halvings, and `-1 / 3`.
* `gaussian`, `huge`: a Gaussian exponent with a small bandwidth and the argument `-10 ^ 8`,
  with `6` and `27` halvings; the lower endpoint is `0`.
* `positive_argument`, `zero_tolerance`, `negative_tolerance`: rejected requests.
* `exp_neg_one_bounds`, `reduced_width`, `kernel_separated`: consumers of the containment and
  width theorems at executed intervals, for `Real.exp` and for the library kernel
  `WeightedKernel.kernel`.
-/

set_option autoImplicit false

namespace TDA.Persistence.Enclosure.ExpExamples

open TDA.Persistence.Enclosure TDA.Persistence.WeightedKernel

/-! ## The precision schedule -/

theorem schedule_zero : (expHalvings 0, toleranceBits (1 / 100), expTerms 10) = (0, 7, 7) := by
  decide +kernel

theorem schedule_large :
    (expHalvings (-10 ^ 8), toleranceBits (1 / 10 ^ 6), expTerms 50) = (27, 20, 18) := by
  decide +kernel

theorem expTaylor_five : expTaylor 5 (-1 / 2) = 233 / 384 := by decide +kernel

/-! ## Executed intervals -/

theorem zero_coarse : expEnclosure? 0 (1 / 100) = some (1023 / 1024, 1) := by decide +kernel

theorem one_coarse : expEnclosure? (-1) (1 / 100) = some (375 / 1024, 189 / 512) := by
  decide +kernel

theorem one_fine :
    expEnclosure? (-1) (1 / 10 ^ 6) = some (3085995 / 8388608, 1542999 / 4194304) := by
  decide +kernel

/-- Refinement: the interval at tolerance `1 / 10 ^ 6` lies inside the one at `1 / 100`. -/
theorem one_refines :
    (expEnclosure (-1) (1 / 100)).1 ≤ (expEnclosure (-1) (1 / 10 ^ 6)).1 ∧
      (expEnclosure (-1) (1 / 10 ^ 6)).2 ≤ (expEnclosure (-1) (1 / 100)).2 := by
  decide +kernel

theorem one_tiny :
    expEnclosure? (-1) (1 / 10 ^ 30) =
      some (3730740755300835732139668652359 / 10141204801825835211973625643008,
        1865370377650417866069834326181 / 5070602400912917605986812821504) := by
  decide +kernel

/-- Two halvings. -/
theorem reduced :
    expEnclosure? (-7 / 3) (1 / 10 ^ 6) = some (3253837 / 33554432, 3253841 / 33554432) := by
  decide +kernel

theorem third :
    expEnclosure? (-1 / 3) (1 / 10 ^ 12) =
      some (3151338030565 / 4398046511104, 6302676061133 / 8796093022208) := by
  decide +kernel

/-- A Gaussian exponent with a small bandwidth: `-((0 - 1/2)² + (1 - 2)²) / (2 (1/10)²)`. -/
theorem gaussian : expEnclosure? (-125 / 2) (1 / 10 ^ 6) = some (0, 1 / 2 ^ 29) := by
  decide +kernel

/-- Twenty-seven halvings. -/
theorem huge : expEnclosure? (-10 ^ 8) (1 / 10 ^ 6) = some (0, 1 / 2 ^ 50) := by
  decide +kernel

/-! ## Rejected requests -/

theorem positive_argument : expEnclosure? (1 / 2) (1 / 100) = none := by decide +kernel

theorem zero_tolerance : expEnclosure? (-1) 0 = none := by decide +kernel

theorem negative_tolerance : expEnclosure? (-1) (-1 / 100) = none := by decide +kernel

/-! ## Consumers: bounds for the actual exponential and the actual kernel -/

/-- Six decimal digits of `exp (-1)`. -/
theorem exp_neg_one_bounds :
    (0.367879 : ℝ) < Real.exp (-1) ∧ Real.exp (-1) < 0.367880 := by
  obtain ⟨h1, h2⟩ := (expEnclosure?_spec one_fine).1
  norm_num at h1 h2 ⊢
  constructor <;> linarith

/-- The width bound of the theorem, at an executed interval. -/
theorem reduced_width : (3253841 / 33554432 - 3253837 / 33554432 : ℚ) ≤ 1 / 10 ^ 6 :=
  (expEnclosure?_spec reduced).2

/-- The value of the library kernel at two separated points with bandwidth `1 / 10`. -/
theorem kernel_separated : kernel (1 / 10) (0, 1) (1 / 2, 2) ≤ 1 / 2 ^ 29 := by
  have h := (expEnclosure?_spec gaussian).1.2
  have e : kernel (1 / 10) (0, 1) (1 / 2, 2) = Real.exp ((-125 / 2 : ℚ) : ℝ) := by
    rw [kernel]
    congr 1
    norm_num
  rw [e]
  refine h.trans (le_of_eq ?_)
  norm_num

end TDA.Persistence.Enclosure.ExpExamples
