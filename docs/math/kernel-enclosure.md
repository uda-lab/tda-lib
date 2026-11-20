# Rational enclosures for Gaussian kernel values

The [weighted Gaussian kernel](weighted-kernel-embedding.md) of two birth–death
points is `exp(x)` at the nonpositive exponent
x = −((p₁−q₁)² + (p₂−q₂)²) / (2σ²). For rational points and a rational bandwidth
this exponent is a rational number, and the kernel value is a real number that
rational arithmetic cannot represent. `TDA.Persistence.Enclosure.Exp` computes a
rational interval that provably contains `Real.exp x` and is as narrow as
requested.

This note covers the scalar exponential only. Enclosures of the Gram sums
`linearKernel` and of the squared RKHS distance of two embeddings are not
provided yet; they are the following units of
[Issue #926](https://github.com/uda-lab/tda-lib/issues/926).

## Request and result

A request is a rational exponent `x` and a rational tolerance `δ`.

- `expEnclosure x δ` is a pair `(lo, hi)` of rational numbers. It is defined for
  every request.
- `expEnclosure? x δ` returns `some (expEnclosure x δ)` when `x ≤ 0` and `0 < δ`,
  and `none` otherwise (`expEnclosure?_eq_some_iff`, `expEnclosure?_eq_none_iff`).
  A positive exponent, a zero tolerance and a negative tolerance are rejected.

The caller supplies no precision, no number of terms and no error bound.

## Statements

- **Containment.** For `x ≤ 0` and every `δ`,
  `lo ≤ Real.exp x ≤ hi` (`expEnclosure_mem`). The exponential is mathlib's
  `Real.exp` at the real number `x`. The tolerance only selects the precision,
  so no hypothesis on `δ` is needed.
- **Width.** For `x ≤ 0` and `0 < δ`, `hi − lo ≤ δ` (`expEnclosure_width`). This
  holds for every such request, whatever the size of `x` or `δ`.
- **Range.** `0 ≤ lo` and `hi ≤ 1` for every request (`expEnclosure_fst_nonneg`,
  `expEnclosure_snd_le_one`), and `lo ≤ hi` for `x ≤ 0`
  (`expEnclosure_fst_le_snd`).
- **Returned intervals.** If `expEnclosure? x δ = some I`, then `I` contains
  `Real.exp x` and has width at most `δ` (`expEnclosure?_spec`).

For `x > 0` the pair computed by the total function `expEnclosure` has no
meaning; its first component can exceed its second. `expEnclosure?` never
returns it.

## Algorithm and precision schedule

Write `k = expHalvings x`, `s = toleranceBits δ` and `p = k + s + 3`.

1. **Halvings.** `-x ≤ 2 ^ k` (`neg_le_two_pow_expHalvings`), and `k = 0` when
   `-1 ≤ x`. The reduced argument `r = x / 2 ^ k` lies in `[-1, 0]`, and
   `exp x = (exp r) ^ (2 ^ k)`.
2. **Tolerance bits.** `1 / 2 ^ s < δ` for `0 < δ`
   (`one_div_two_pow_toleranceBits_lt`).
3. **Taylor polynomial.** `expTaylor n r` is the sum of `r ^ i / i!` over
   `i < n`, evaluated exactly. The number of terms `n = expTerms p` is the first
   `n` with `2 ^ (p + 1) ≤ n!`, found by a search that ends at `p + 2` at the
   latest (`two_pow_le_factorial_expTerms`). Mathlib's remainder bound
   `Real.exp_bound` then gives `|exp r − expTaylor n r| ≤ 1 / 2 ^ p`
   (`abs_exp_sub_expTaylor_le`, stated for every rational argument of absolute
   value at most `1`).
4. **Base interval.** `roundDown p` and `roundUp p` round a rational number to
   the nearest multiple of `1 / 2 ^ p` below and above it (`roundDown_le`,
   `lt_roundDown_add`, `le_roundUp`, `roundUp_lt_add`). The Taylor value is
   rounded outward, widened by one grid step on each side and clamped to
   `[0, 1]`. The result contains `exp r` and has width at most `4 / 2 ^ p`.
5. **Squaring.** `expSquare p` squares both endpoints, rounding the lower one
   down and the upper one up to the same grid. It is applied `k` times. Both
   endpoints stay in `[0, 1]`, so one step at most doubles the width and adds
   `2 / 2 ^ p`. After `k` steps the width is at most
   `6 · 2 ^ k / 2 ^ p = (3/4) / 2 ^ s`, which is below `δ`.

The executable definitions use rational arithmetic, integer floor and ceiling,
comparison of rational numbers, and `Nat.log2`, factorials and a list search on
natural numbers. They make no decision by `Classical` and compare no real
numbers. This is shown by kernel evaluation of the fixtures. It is not visible
in `#print axioms`, which lists `Classical.choice` for every definition that uses
the arithmetic of `ℚ`, because that arithmetic carries proofs depending on it.

## What is not claimed

- **Relative error.** The width bound is absolute. For a very negative exponent
  the lower endpoint is `0` although `exp x > 0`; the result then says only that
  `exp x` is at most the upper endpoint. No positive lower bound and no relative
  error bound is given.
- **Positive exponents.** They are rejected. An interval of prescribed absolute
  width for `exp x` with `x > 0` needs a precision growing with `x` itself, and
  the Gaussian kernel never needs it.
- **Decisions.** An enclosure does not decide equalities or strict inequalities
  between exponentials.
- **Shape of the output.** No theorem states that the endpoints lie on the grid
  `1 / 2 ^ p`, that intervals for smaller tolerances are nested, that the
  endpoints are monotone in `x`, or that `expTerms p` and `expHalvings x` are
  minimal. One fixture checks nesting for one pair of tolerances by evaluation.
- **Kernel sums.** Nothing here mentions a weight, a bandwidth, a list of points
  or a diagram. One example consumes the enclosure for a single value of
  `WeightedKernel.kernel`.

## Cost

With `k`, `s`, `p` and `n` as above, `k` is about the binary logarithm of `-x`,
`s` is the number of binary digits of `⌈1/δ⌉`, and `n` is `8` for `p = 13`, `16`
for `p = 43`, `30` for `p = 103` and `71` for `p = 336`.

- The Taylor stage computes `n` powers and quotients and `n − 1` sums of exact
  rational numbers at `r`. The denominator of `r` is that of `x` times at most
  `2 ^ k`, and the partial sums have denominators dividing its `(n−1)`-st power
  times `(n−1)!`. No intermediate rounding bounds this growth, so a tolerance
  with many digits or an exponent with a long denominator makes this stage
  expensive. Each power is computed separately.
- The squaring stage makes `k` squarings of numbers with `p` binary digits, each
  followed by one floor and one ceiling.
- The precision used exceeds the request: `δ` is replaced by a power of two
  below it, three guard bits are added and `k` further bits absorb the
  squarings. There is no early exit for exponents so negative that the result is
  `(0, 1 / 2 ^ p)`.

The cost therefore grows with the logarithm of `-x`, with the number of digits
of `1/δ` and with the size of the denominator of `x`. It is not a fixed-cost
exponential. These counts are documented; no theorem states them and no bound on
the bit complexity is proved.

## Examples

`TDA.Persistence.Enclosure.ExpExamples` states the complete value of
`expEnclosure?` for each fixture and checks it by kernel evaluation.

| Exponent | Tolerance | Interval |
|---|---|---|
| `0` | `1/100` | `(1023/1024, 1)` |
| `-1` | `1/100` | `(375/1024, 189/512)` |
| `-1` | `1/10⁶` | `(3085995/8388608, 1542999/4194304)` |
| `-7/3` | `1/10⁶` | `(3253837/33554432, 3253841/33554432)` |
| `-125/2` | `1/10⁶` | `(0, 1/2²⁹)` |
| `-10⁸` | `1/10⁶` | `(0, 1/2⁵⁰)` |

Further fixtures cover the exponent `-1` at tolerance `1/10³⁰`, the exponent
`-1/3` at `1/10¹²`, the schedule of two requests, one Taylor polynomial and the
three kinds of rejected request. The interval for `-1` at `1/10⁶` lies inside the
one at `1/100`.

Three consumers use the theorems at executed intervals, without assuming any
value of a transcendental number:

- `0.367879 < exp(−1) < 0.367880` (`exp_neg_one_bounds`);
- the width bound at the interval for `-7/3` (`reduced_width`);
- `kernel (1/10) (0, 1) (1/2, 2) ≤ 1/2²⁹` for the library kernel, whose exponent
  at these points is `-125/2` (`kernel_separated`).

## Source scope

These are elementary library results derived from the pinned
[mathlib](references.md#mathlib-56a0058) remainder bound for the exponential
series. They are not attributed to a paper, and no source comparison is claimed.
