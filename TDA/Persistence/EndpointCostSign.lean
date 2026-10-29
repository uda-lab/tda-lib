import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Sign.Basic
import Mathlib.Tactic.Ring

/-!
# Signed comparison of normalized endpoint costs

For positive weights `δ` and `η`, comparing `|a| / δ` and `|b| / η`
is equivalent to comparing their squared cross-products. The difference of
these squares factors into **both** signed linear factors
`η * a - δ * b` and `η * a + δ * b`. The results retain zero inputs and
equal-cost degeneracies. A common positive normalization does not change the sign.

This is derived real algebra for finite affine arrangements, independent of any
geometric branch-selection or comparison-invariance assumption.
-/

namespace TDA.Persistence.EndpointCost

variable {a b δ η k : ℝ}

/-- Strict comparison of weighted absolute values is detected by the product
of the difference and sum of their signed cross-products. -/
theorem abs_div_lt_iff_factor_neg (hδ : 0 < δ) (hη : 0 < η) :
    |a| / δ < |b| / η ↔ (η * a - δ * b) * (η * a + δ * b) < 0 := by
  calc
    |a| / δ < |b| / η ↔ |η * a| < |δ * b| := by
      rw [div_lt_div_iff₀ hδ hη]
      simp only [abs_mul, abs_of_pos hδ, abs_of_pos hη, mul_comm]
    _ ↔ (η * a) ^ 2 < (δ * b) ^ 2 := sq_lt_sq.symm
    _ ↔ (η * a) ^ 2 - (δ * b) ^ 2 < 0 := sub_neg.symm
    _ ↔ (η * a - δ * b) * (η * a + δ * b) < 0 := by
      rw [show (η * a - δ * b) * (η * a + δ * b) =
        (η * a) ^ 2 - (δ * b) ^ 2 by ring]

/-- Weak comparison of weighted absolute values includes the zero-product case. -/
theorem abs_div_le_iff_factor_nonpos (hδ : 0 < δ) (hη : 0 < η) :
    |a| / δ ≤ |b| / η ↔ (η * a - δ * b) * (η * a + δ * b) ≤ 0 := by
  calc
    |a| / δ ≤ |b| / η ↔ |η * a| ≤ |δ * b| := by
      rw [div_le_div_iff₀ hδ hη]
      simp only [abs_mul, abs_of_pos hδ, abs_of_pos hη, mul_comm]
    _ ↔ (η * a) ^ 2 ≤ (δ * b) ^ 2 := sq_le_sq.symm
    _ ↔ (η * a) ^ 2 - (δ * b) ^ 2 ≤ 0 := sub_nonpos.symm
    _ ↔ (η * a - δ * b) * (η * a + δ * b) ≤ 0 := by
      rw [show (η * a - δ * b) * (η * a + δ * b) =
        (η * a) ^ 2 - (δ * b) ^ 2 by ring]

/-- The sign of a weighted absolute-value difference equals the sign of the
product of its two signed linear factors. No nonzero condition on `a` or `b`
is required. -/
theorem sign_abs_div_sub_eq_sign_factors (hδ : 0 < δ) (hη : 0 < η) :
    SignType.sign (|a| / δ - |b| / η) =
      SignType.sign ((η * a - δ * b) * (η * a + δ * b)) := by
  have hneg : |a| / δ - |b| / η < 0 ↔
      (η * a - δ * b) * (η * a + δ * b) < 0 := by
    simpa only [sub_neg] using abs_div_lt_iff_factor_neg (a := a) (b := b) hδ hη
  have hnonpos : |a| / δ - |b| / η ≤ 0 ↔
      (η * a - δ * b) * (η * a + δ * b) ≤ 0 := by
    simpa only [sub_nonpos] using abs_div_le_iff_factor_nonpos (a := a) (b := b) hδ hη
  have hpos : 0 < |a| / δ - |b| / η ↔
      0 < (η * a - δ * b) * (η * a + δ * b) := by
    simpa only [not_le] using not_congr hnonpos
  simp only [sign_apply, hpos, hneg]

/-- Equal weighted costs occur precisely when one of the signed factors vanishes. -/
theorem abs_div_eq_iff_factor_zero (hδ : 0 < δ) (hη : 0 < η) :
    |a| / δ = |b| / η ↔ (η * a - δ * b) * (η * a + δ * b) = 0 := by
  rw [← sub_eq_zero, ← sign_eq_zero_iff,
    sign_abs_div_sub_eq_sign_factors hδ hη, sign_eq_zero_iff]

/-- A common positive normalization in both denominators leaves the two-factor
comparison sign unchanged. -/
theorem sign_abs_div_mul_sub_eq_sign_factors (hδ : 0 < δ) (hη : 0 < η)
    (hk : 0 < k) :
    SignType.sign (|a| / (δ * k) - |b| / (η * k)) =
      SignType.sign ((η * a - δ * b) * (η * a + δ * b)) := by
  rw [show |a| / (δ * k) - |b| / (η * k) = (|a| / δ - |b| / η) / k by
    rw [sub_div, div_div, div_div]]
  calc
    SignType.sign ((|a| / δ - |b| / η) / k) =
        SignType.sign (|a| / δ - |b| / η) := by
      simp only [sign_apply, div_pos_iff_of_pos_right hk,
        div_lt_iff₀ hk, zero_mul]
    _ = _ := sign_abs_div_sub_eq_sign_factors hδ hη

end TDA.Persistence.EndpointCost
