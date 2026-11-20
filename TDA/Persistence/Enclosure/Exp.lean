import Mathlib.Analysis.Complex.Exponential
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Rat.BigOperators
import Mathlib.Data.Nat.Factorial.Basic

/-!
# Rational enclosures of the exponential at nonpositive rational arguments

`expEnclosure x δ` is a pair of rational numbers computed by rational arithmetic. For `x ≤ 0`
it encloses the real number `Real.exp x` (`expEnclosure_mem`), and for `0 < δ` its width is at
most `δ` (`expEnclosure_width`). `expEnclosure?` returns it for `x ≤ 0` and `0 < δ` and `none`
otherwise. These are the scalar enclosures needed for Gaussian kernel values
`exp (-‖p - q‖² / (2σ²))`.

## Algorithm

Write `k = expHalvings x`, so that `-x ≤ 2 ^ k`, `s = toleranceBits δ`, so that
`1 / 2 ^ s < δ`, and `p = k + s + 3`.

1. The argument is halved `k` times: `r = x / 2 ^ k` lies in `[-1, 0]`.
2. The Taylor polynomial `expTaylor n r` with `n = expTerms p` terms is evaluated exactly.
   Since `2 ^ (p + 1) ≤ n !`, mathlib's remainder bound `Real.exp_bound` places it within
   `1 / 2 ^ p` of `Real.exp r` (`abs_exp_sub_expTaylor_le`).
3. The value is rounded outward to the grid of multiples of `1 / 2 ^ p`, widened by one grid
   step on each side and clamped to `[0, 1]`. The result encloses `Real.exp r` and has width
   at most `4 / 2 ^ p`.
4. The interval is squared `k` times; each step rounds the lower endpoint down and the upper
   endpoint up to the grid. As both endpoints stay in `[0, 1]`, one step at most doubles the
   width and adds `2 / 2 ^ p`, so the final width is at most `6 * 2 ^ k / 2 ^ p`, which is
   `(3 / 4) / 2 ^ s`.

## Cost

The Taylor stage computes `n` powers and quotients and `n - 1` sums of exact rational numbers
at `r`, whose denominator is that of `x` times at most `2 ^ k`; the partial sums have
denominators dividing the `(n - 1)`-st power of that denominator times `(n - 1)!`, so their
size is about `n` times the size of `r` plus the size of `(n - 1)!`. No intermediate rounding
bounds this growth. The number `n` of terms is at most `p + 2` and is the first `n` with
`2 ^ (p + 1) ≤ n !`. The squaring stage makes `k` squarings of numbers with `p` binary digits,
each followed by one floor and one ceiling. The cost therefore grows with the logarithm of
`-x`, through `k` and `p`, with the number of digits of the tolerance and with the size of the
denominator of `x`. It is not a fixed-cost exponential, and no bound on the bit complexity is
proved. These counts are documented and are not theorems.

The precision used can exceed the request: `δ` is replaced by a smaller power of two, three
guard bits are added, and `k` further bits absorb the squarings.

The executable definitions use rational arithmetic, integer floor and ceiling and comparison
of rational numbers: no decision by `Classical` and no real-number comparison. This is shown
by evaluation: the proofs carried by the arithmetic of `ℚ` are the only reason
`#print axioms` lists `Classical.choice` for them.

## Scope

The width is absolute: the lower endpoint can be `0`, and no relative error is bounded.
Positive arguments are rejected. Enclosures of Gaussian kernel sums and of the squared RKHS
distance are not in this module.

These are elementary library results, not attributed to a source. See
`docs/math/kernel-enclosure.md`.
-/

set_option autoImplicit false

namespace TDA.Persistence.Enclosure

open Nat

/-! ## Outward rounding to a dyadic grid -/

/-- The largest multiple of `1 / 2 ^ p` below `q`. -/
def roundDown (p : ℕ) (q : ℚ) : ℚ := ⌊q * 2 ^ p⌋ / 2 ^ p

/-- The least multiple of `1 / 2 ^ p` above `q`. -/
def roundUp (p : ℕ) (q : ℚ) : ℚ := ⌈q * 2 ^ p⌉ / 2 ^ p

theorem roundDown_le (p : ℕ) (q : ℚ) : roundDown p q ≤ q := by
  rw [roundDown, div_le_iff₀ (by positivity)]
  exact Int.floor_le _

theorem lt_roundDown_add (p : ℕ) (q : ℚ) : q < roundDown p q + 1 / 2 ^ p := by
  rw [roundDown, ← add_div, lt_div_iff₀ (by positivity)]
  exact Int.lt_floor_add_one _

theorem le_roundUp (p : ℕ) (q : ℚ) : q ≤ roundUp p q := by
  rw [roundUp, le_div_iff₀ (by positivity)]
  exact Int.le_ceil _

theorem roundUp_lt_add (p : ℕ) (q : ℚ) : roundUp p q < q + 1 / 2 ^ p := by
  rw [roundUp, div_lt_iff₀ (by positivity), add_mul, one_div, inv_mul_cancel₀ (by positivity)]
  exact Int.ceil_lt_add_one _

theorem roundDown_nonneg (p : ℕ) {q : ℚ} (hq : 0 ≤ q) : 0 ≤ roundDown p q := by
  rw [roundDown]
  have : (0 : ℤ) ≤ ⌊q * 2 ^ p⌋ := Int.floor_nonneg.2 (by positivity)
  have h : (0 : ℚ) ≤ (⌊q * 2 ^ p⌋ : ℤ) := by exact_mod_cast this
  positivity

theorem roundUp_le_one (p : ℕ) {q : ℚ} (hq : q ≤ 1) : roundUp p q ≤ 1 := by
  rw [roundUp, div_le_one (by positivity)]
  have h : ⌈q * 2 ^ p⌉ ≤ (2 ^ p : ℤ) := by
    rw [Int.ceil_le]
    push_cast
    nlinarith [show (0 : ℚ) < 2 ^ p by positivity]
  exact_mod_cast h

/-! ## The precision schedule -/

/-- The Taylor polynomial `∑ i < n, x ^ i / i !` of the exponential. -/
def expTaylor (n : ℕ) (x : ℚ) : ℚ := ∑ i ∈ Finset.range n, x ^ i / (i ! : ℚ)

/-- The number of Taylor terms used at `p` bits: the first `n` with `2 ^ (p + 1) ≤ n !`, searched
from `0` up to `p + 2`. -/
def expTerms (p : ℕ) : ℕ :=
  ((List.range (p + 2)).find? fun n => 2 ^ (p + 1) ≤ n !).getD (p + 2)

/-- The number of halvings of the argument: `⌈-x⌉₊ ≤ 2 ^ expHalvings x`, and `0` when
`⌈-x⌉₊ ≤ 1`. -/
def expHalvings (x : ℚ) : ℕ := Nat.log2 (2 * ⌈-x⌉₊ - 1)

/-- The number of bits of the tolerance `δ`: `⌈δ⁻¹⌉₊ < 2 ^ toleranceBits δ`. -/
def toleranceBits (δ : ℚ) : ℕ := Nat.log2 ⌈δ⁻¹⌉₊ + 1

private theorem two_pow_le_factorial_succ (n : ℕ) : 2 ^ n ≤ (n + 1)! := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Nat.factorial_succ (n + 1), mul_comm]
    exact Nat.mul_le_mul (by omega) ih

theorem two_pow_le_factorial_expTerms (p : ℕ) : 2 ^ (p + 1) ≤ (expTerms p)! := by
  rw [expTerms]
  cases h : (List.range (p + 2)).find? fun n => 2 ^ (p + 1) ≤ n ! with
  | none => exact two_pow_le_factorial_succ (p + 1)
  | some n => simpa using List.find?_some h

theorem neg_le_two_pow_expHalvings (x : ℚ) : -x ≤ 2 ^ expHalvings x := by
  have h1 : -x ≤ (⌈-x⌉₊ : ℚ) := Nat.le_ceil _
  have h2 : ⌈-x⌉₊ ≤ 2 ^ expHalvings x := by
    have h := Nat.lt_log2_self (n := 2 * ⌈-x⌉₊ - 1)
    rw [expHalvings]
    rw [pow_succ] at h
    omega
  have h3 : ((⌈-x⌉₊ : ℕ) : ℚ) ≤ ((2 ^ expHalvings x : ℕ) : ℚ) := by exact_mod_cast h2
  push_cast at h3
  exact h1.trans h3

theorem one_div_two_pow_toleranceBits_lt {δ : ℚ} (hδ : 0 < δ) :
    1 / 2 ^ toleranceBits δ < δ := by
  have h1 : δ⁻¹ ≤ (⌈δ⁻¹⌉₊ : ℚ) := Nat.le_ceil _
  have h2 : ⌈δ⁻¹⌉₊ < 2 ^ toleranceBits δ := Nat.lt_log2_self
  have h3 : ((⌈δ⁻¹⌉₊ : ℕ) : ℚ) < ((2 ^ toleranceBits δ : ℕ) : ℚ) := by exact_mod_cast h2
  push_cast at h3
  rw [one_div, inv_lt_comm₀ (by positivity) hδ]
  exact h1.trans_lt h3

/-- The Taylor polynomial with `expTerms p` terms is within `1 / 2 ^ p` of the exponential on
`[-1, 1]`. -/
theorem abs_exp_sub_expTaylor_le (p : ℕ) {x : ℚ} (hx : |x| ≤ 1) :
    |Real.exp x - (expTaylor (expTerms p) x : ℚ)| ≤ 1 / 2 ^ p := by
  set n := expTerms p with hn
  have hfac : 2 ^ (p + 1) ≤ n ! := two_pow_le_factorial_expTerms p
  have hn0 : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · rw [h] at hfac
      simp at hfac
    · exact h
  have hxr : |(x : ℝ)| ≤ 1 := by exact_mod_cast hx
  have hb := Real.exp_bound hxr hn0
  have hcast : ((expTaylor n x : ℚ) : ℝ) = ∑ m ∈ Finset.range n, (x : ℝ) ^ m / (m ! : ℝ) := by
    simp [expTaylor]
  rw [hcast]
  refine hb.trans ?_
  have hfacr : (2 : ℝ) ^ (p + 1) ≤ (n ! : ℝ) := by exact_mod_cast hfac
  have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn0
  have hpow : |(x : ℝ)| ^ n ≤ 1 := pow_le_one₀ (abs_nonneg _) hxr
  have hfpos : (0 : ℝ) < (n ! : ℝ) := by positivity
  have h2 : ((n.succ : ℕ) : ℝ) / ((n ! : ℝ) * n) ≤ 1 / 2 ^ p := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    push_cast
    rw [pow_succ] at hfacr
    nlinarith [mul_le_mul hfacr hnr zero_le_one hfpos.le]
  calc |(x : ℝ)| ^ n * (((n.succ : ℕ) : ℝ) / ((n ! : ℝ) * n))
      ≤ 1 * (1 / 2 ^ p) := mul_le_mul hpow h2 (by positivity) zero_le_one
    _ = 1 / 2 ^ p := one_mul _

/-! ## The enclosure -/

/-- One squaring step at `p` bits: the lower endpoint is squared and rounded down, the upper
endpoint is squared and rounded up. -/
def expSquare (p : ℕ) (I : ℚ × ℚ) : ℚ × ℚ := (roundDown p (I.1 ^ 2), roundUp p (I.2 ^ 2))

/-- A rational interval for `Real.exp x`, `x ≤ 0`, of width at most `δ`, `0 < δ`. With
`k = expHalvings x` and `p = k + toleranceBits δ + 3` bits, the Taylor polynomial of
`expTerms p` terms at `x / 2 ^ k` is rounded outward to the grid `1 / 2 ^ p`, widened by one
grid step, clamped to `[0, 1]` and squared `k` times with outward rounding. -/
def expEnclosure (x δ : ℚ) : ℚ × ℚ :=
  let k := expHalvings x
  let p := k + toleranceBits δ + 3
  let t := expTaylor (expTerms p) (x / 2 ^ k)
  (expSquare p)^[k] (max 0 (roundDown p t - 1 / 2 ^ p), min 1 (roundUp p t + 1 / 2 ^ p))

/-- The enclosure for an admissible request: `none` unless `x ≤ 0` and `0 < δ`. -/
def expEnclosure? (x δ : ℚ) : Option (ℚ × ℚ) :=
  if x ≤ 0 ∧ 0 < δ then some (expEnclosure x δ) else none

private theorem expSquare_spec (p : ℕ) {y : ℝ} {I : ℚ × ℚ} (h0 : 0 ≤ I.1)
    (h1 : (I.1 : ℝ) ≤ y) (h2 : y ≤ (I.2 : ℝ)) (h3 : I.2 ≤ 1) :
    0 ≤ (expSquare p I).1 ∧ ((expSquare p I).1 : ℝ) ≤ y ^ 2 ∧ y ^ 2 ≤ ((expSquare p I).2 : ℝ) ∧
      (expSquare p I).2 ≤ 1 ∧
      (expSquare p I).2 - (expSquare p I).1 + 2 / 2 ^ p ≤ 2 * (I.2 - I.1 + 2 / 2 ^ p) := by
  have h0r : (0 : ℝ) ≤ (I.1 : ℝ) := by exact_mod_cast h0
  have hy : 0 ≤ y := h0r.trans h1
  have h12r : (I.1 : ℝ) ≤ (I.2 : ℝ) := h1.trans h2
  have h12 : I.1 ≤ I.2 := by exact_mod_cast h12r
  have h20 : 0 ≤ I.2 := h0.trans h12
  have hd : ((roundDown p (I.1 ^ 2) : ℚ) : ℝ) ≤ ((I.1 ^ 2 : ℚ) : ℝ) :=
    Rat.cast_le.2 (roundDown_le p (I.1 ^ 2))
  have hu : ((I.2 ^ 2 : ℚ) : ℝ) ≤ ((roundUp p (I.2 ^ 2) : ℚ) : ℝ) :=
    Rat.cast_le.2 (le_roundUp p (I.2 ^ 2))
  rw [Rat.cast_pow] at hd hu
  have hsq0 : 0 ≤ I.1 ^ 2 := by positivity
  simp only [expSquare]
  refine ⟨roundDown_nonneg p hsq0, ?_, ?_, roundUp_le_one p ?_, ?_⟩
  · exact hd.trans (pow_le_pow_left₀ h0r h1 2)
  · exact (pow_le_pow_left₀ hy h2 2).trans hu
  · exact pow_le_one₀ h20 h3
  · have ha := lt_roundDown_add p (I.1 ^ 2)
    have hb := roundUp_lt_add p (I.2 ^ 2)
    have hsq : I.2 ^ 2 - I.1 ^ 2 ≤ 2 * (I.2 - I.1) := by nlinarith
    have e : (2 : ℚ) / 2 ^ p = 2 * (1 / 2 ^ p) := by ring
    rw [e]
    linarith

private theorem iterate_expSquare_spec (p : ℕ) {y : ℝ} {I : ℚ × ℚ} (h0 : 0 ≤ I.1)
    (h1 : (I.1 : ℝ) ≤ y) (h2 : y ≤ (I.2 : ℝ)) (h3 : I.2 ≤ 1) (j : ℕ) :
    0 ≤ ((expSquare p)^[j] I).1 ∧ (((expSquare p)^[j] I).1 : ℝ) ≤ y ^ 2 ^ j ∧
      y ^ 2 ^ j ≤ (((expSquare p)^[j] I).2 : ℝ) ∧ ((expSquare p)^[j] I).2 ≤ 1 ∧
      ((expSquare p)^[j] I).2 - ((expSquare p)^[j] I).1 + 2 / 2 ^ p ≤
        2 ^ j * (I.2 - I.1 + 2 / 2 ^ p) := by
  induction j with
  | zero => simpa using ⟨h0, h1, h2, h3⟩
  | succ j ih =>
    obtain ⟨a0, a1, a2, a3, a4⟩ := ih
    obtain ⟨b0, b1, b2, b3, b4⟩ := expSquare_spec p a0 a1 a2 a3
    rw [Function.iterate_succ_apply']
    refine ⟨b0, ?_, ?_, b3, ?_⟩
    · rwa [pow_succ, pow_mul]
    · rwa [pow_succ, pow_mul]
    · rw [pow_succ, mul_comm (2 ^ j) 2, mul_assoc]
      exact b4.trans (by linarith)

private theorem expEnclosure_spec {x : ℚ} (hx : x ≤ 0) (δ : ℚ) :
    0 ≤ (expEnclosure x δ).1 ∧ ((expEnclosure x δ).1 : ℝ) ≤ Real.exp x ∧
      Real.exp x ≤ ((expEnclosure x δ).2 : ℝ) ∧ (expEnclosure x δ).2 ≤ 1 ∧
      (expEnclosure x δ).2 - (expEnclosure x δ).1 ≤ 1 / 2 ^ toleranceBits δ := by
  set k := expHalvings x with hk
  set p := k + toleranceBits δ + 3 with hp
  set r : ℚ := x / 2 ^ k with hr
  set t := expTaylor (expTerms p) r with ht
  have hpow : (0 : ℚ) < 2 ^ k := by positivity
  have hr0 : r ≤ 0 := div_nonpos_of_nonpos_of_nonneg hx hpow.le
  have hr1 : |r| ≤ 1 := by
    rw [abs_of_nonpos hr0, hr, ← neg_div, div_le_one hpow]
    exact neg_le_two_pow_expHalvings x
  have hT := abs_le.1 (abs_exp_sub_expTaylor_le p hr1)
  rw [← ht] at hT
  have hε : (0 : ℚ) < 1 / 2 ^ p := by positivity
  have hεr : ((1 / 2 ^ p : ℚ) : ℝ) = 1 / 2 ^ p := by push_cast; ring
  have hexp0 : 0 < Real.exp (r : ℝ) := Real.exp_pos _
  have hexp1 : Real.exp (r : ℝ) ≤ 1 := Real.exp_le_one_iff.2 (by exact_mod_cast hr0)
  have hd : ((roundDown p t : ℚ) : ℝ) ≤ (t : ℝ) := Rat.cast_le.2 (roundDown_le p t)
  have hu : (t : ℝ) ≤ ((roundUp p t : ℚ) : ℝ) := Rat.cast_le.2 (le_roundUp p t)
  set I : ℚ × ℚ := (max 0 (roundDown p t - 1 / 2 ^ p), min 1 (roundUp p t + 1 / 2 ^ p))
    with hI
  have h0 : 0 ≤ I.1 := le_max_left _ _
  have h1 : (I.1 : ℝ) ≤ Real.exp (r : ℝ) := by
    simp only [hI, Rat.cast_max, Rat.cast_zero, Rat.cast_sub, hεr]
    exact max_le hexp0.le (by linarith [hT.1])
  have h2 : Real.exp (r : ℝ) ≤ (I.2 : ℝ) := by
    simp only [hI, Rat.cast_min, Rat.cast_one, Rat.cast_add, hεr]
    exact le_min hexp1 (by linarith [hT.2])
  have h3 : I.2 ≤ 1 := min_le_left _ _
  have hw : I.2 - I.1 ≤ 4 * (1 / 2 ^ p) := by
    have ha := lt_roundDown_add p t
    have hb := roundUp_lt_add p t
    have hlo : roundDown p t - 1 / 2 ^ p ≤ I.1 := le_max_right _ _
    have hhi : I.2 ≤ roundUp p t + 1 / 2 ^ p := min_le_right _ _
    linarith
  obtain ⟨c0, c1, c2, c3, c4⟩ := iterate_expSquare_spec p h0 h1 h2 h3 k
  have hx' : Real.exp (r : ℝ) ^ 2 ^ k = Real.exp (x : ℝ) := by
    rw [← Real.exp_nat_mul]
    congr 1
    rw [hr]
    push_cast
    field_simp
  rw [hx'] at c1 c2
  have hE : expEnclosure x δ = (expSquare p)^[k] I := rfl
  rw [hE]
  refine ⟨c0, c1, c2, c3, ?_⟩
  have e1 : (2 : ℚ) / 2 ^ p = 2 * (1 / 2 ^ p) := by ring
  have e2 : (2 : ℚ) ^ k * (6 * (1 / 2 ^ p)) = 3 / 4 * (1 / 2 ^ toleranceBits δ) := by
    rw [hp, pow_add, pow_add]
    field_simp
    ring
  have hs : (0 : ℚ) < 1 / 2 ^ toleranceBits δ := by positivity
  have hmul : (2 : ℚ) ^ k * (I.2 - I.1 + 2 / 2 ^ p) ≤ 2 ^ k * (6 * (1 / 2 ^ p)) :=
    mul_le_mul_of_nonneg_left (by rw [e1]; linarith) hpow.le
  rw [e2] at hmul
  linarith

/-! ## Containment and width -/

/-- The interval contains the actual exponential, for every tolerance. -/
theorem expEnclosure_mem {x : ℚ} (hx : x ≤ 0) (δ : ℚ) :
    ((expEnclosure x δ).1 : ℝ) ≤ Real.exp x ∧ Real.exp x ≤ ((expEnclosure x δ).2 : ℝ) :=
  ⟨(expEnclosure_spec hx δ).2.1, (expEnclosure_spec hx δ).2.2.1⟩

/-- The width is at most the requested tolerance. -/
theorem expEnclosure_width {x δ : ℚ} (hx : x ≤ 0) (hδ : 0 < δ) :
    (expEnclosure x δ).2 - (expEnclosure x δ).1 ≤ δ :=
  (expEnclosure_spec hx δ).2.2.2.2.trans (one_div_two_pow_toleranceBits_lt hδ).le

theorem expEnclosure_fst_nonneg (x δ : ℚ) : 0 ≤ (expEnclosure x δ).1 := by
  rw [expEnclosure]
  cases expHalvings x with
  | zero => exact le_max_left _ _
  | succ k =>
    rw [Function.iterate_succ_apply']
    exact roundDown_nonneg _ (sq_nonneg _)

theorem expEnclosure_snd_le_one (x δ : ℚ) : (expEnclosure x δ).2 ≤ 1 := by
  rcases le_or_gt x 0 with hx | hx
  · exact (expEnclosure_spec hx δ).2.2.2.1
  · have hk : expHalvings x = 0 := by
      have h : ⌈-x⌉₊ = 0 := Nat.ceil_eq_zero.2 (by linarith)
      simp [expHalvings, h]
    rw [expEnclosure, hk]
    exact min_le_left _ _

theorem expEnclosure_fst_le_snd {x : ℚ} (hx : x ≤ 0) (δ : ℚ) :
    (expEnclosure x δ).1 ≤ (expEnclosure x δ).2 := by
  have h := (expEnclosure_mem hx δ).1.trans (expEnclosure_mem hx δ).2
  exact_mod_cast h

theorem expEnclosure?_eq_some_iff {x δ : ℚ} {I : ℚ × ℚ} :
    expEnclosure? x δ = some I ↔ (x ≤ 0 ∧ 0 < δ) ∧ I = expEnclosure x δ := by
  unfold expEnclosure?
  split_ifs with h
  · simp [h, eq_comm]
  · simp [h]

theorem expEnclosure?_eq_none_iff {x δ : ℚ} : expEnclosure? x δ = none ↔ ¬ (x ≤ 0 ∧ 0 < δ) := by
  unfold expEnclosure?
  split_ifs with h <;> simp [h]

/-- Every returned interval contains the actual exponential and has width at most `δ`. -/
theorem expEnclosure?_spec {x δ : ℚ} {I : ℚ × ℚ} (h : expEnclosure? x δ = some I) :
    ((I.1 : ℝ) ≤ Real.exp x ∧ Real.exp x ≤ (I.2 : ℝ)) ∧ I.2 - I.1 ≤ δ := by
  obtain ⟨⟨hx, hδ⟩, rfl⟩ := expEnclosure?_eq_some_iff.1 h
  exact ⟨expEnclosure_mem hx δ, expEnclosure_width hx hδ⟩

end TDA.Persistence.Enclosure
