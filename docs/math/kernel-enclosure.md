# Rational enclosures for Gaussian kernel values

The [weighted Gaussian kernel](weighted-kernel-embedding.md) of two birth–death
points is `exp(x)` at the nonpositive exponent
x = −((p₁−q₁)² + (p₂−q₂)²) / (2σ²). For rational points and a rational bandwidth
this exponent is a rational number, and the kernel value is a real number that
rational arithmetic cannot represent in general; it is `1` at equal points.
`TDA.Persistence.Enclosure.Exp` computes a rational interval that provably
contains `Real.exp x` and is as narrow as requested.
`TDA.Persistence.Enclosure.Gram` uses it to enclose the Gram sums `linearKernel`
of two finite lists of rational birth–death pairs and the squared RKHS distance
of their embeddings.

The sections up to the first examples describe the scalar exponential. The
section [Gram sums and the squared RKHS distance](#gram-sums-and-the-squared-rkhs-distance)
describes the kernel sums.

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
4. **Base interval.** `roundDown p q` is the largest multiple of `1 / 2 ^ p`
   that is at most `q`, and `roundUp p q` is the least multiple that is at
   least `q` (`roundDown_le`, `lt_roundDown_add`, `le_roundUp`,
   `roundUp_lt_add`). The Taylor value is
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
- **Kernel sums.** The scalar module mentions no weight, bandwidth, list of
  points or diagram; these belong to `TDA.Persistence.Enclosure.Gram`, described
  below. One example of the scalar module consumes the enclosure for a single
  value of `WeightedKernel.kernel`.

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

## Gram sums and the squared RKHS distance

`TDA.Persistence.Enclosure.Gram` applies the scalar enclosure to the weighted
Gaussian Gram sum `linearKernel` and to the squared RKHS distance of two
embeddings.

### Input and semantic objects

The input is two lists `x`, `y` of rational pairs `(birth, death)`, a rational
bandwidth `σ`, a rational cap `c` and a rational tolerance `δ`. The caller
supplies no weight function, no precision and no error bound.

- `realPoint p` is the real point of a rational pair, and `realPoints x` is the
  occurrence family indexed by the positions of the list `x`. Every position is
  an occurrence: repeated pairs are repeated occurrences, and no pair is
  removed.
- `capWeight c hc` is the weight `u ↦ min c (max 0 u.2)` in birth–persistence
  coordinates, for a rational cap `0 ≤ c`. It is a `PersistenceImage.Weight`
  with Lipschitz constant `1` and bound the real number `c`. Persistence is
  truncated at `0` below and at `c` above, so pairs with `death ≤ birth` have
  weight `0`.

The enclosed values are the library values
`linearKernel σ (capWeight c hc) (realPoints x) (realPoints y)` and
`‖embedding σ w (realPoints x) − embedding σ w (realPoints y)‖²` with
`w = capWeight c hc`, at the real bandwidth obtained from the rational `σ`.

### Executed weight and exponent

- `pointWeight c (b, d) = min c (max 0 (d − b))` is the exact rational weight of
  a pair. Its cast is the library weight of the real point
  (`capWeight_realPoint`), and it is nonnegative for `0 ≤ c`
  (`pointWeight_nonneg`). `totalWeight c x` is the sum of the weights of a list.
- `gaussExponent σ p q = −((b₁−b₂)² + (d₁−d₂)²) / (2σ²)` is the exact rational
  exponent. It is nonpositive for every `σ` (`gaussExponent_nonpos`), and the
  library kernel at the two real points is `Real.exp` of it for every rational
  `σ` (`kernel_realPoint`).

These identities are theorems. No statement assumes that the rational formula
agrees with the library value.

### Gram sum and allocation of the tolerance

- `gramTerm σ c ε p q` multiplies both endpoints of
  `expEnclosure (gaussExponent σ p q) ε` by the product `w` of the two weights.
  For `w = 0` it is `(0, 0)` and no exponential is computed.
- `gramSum σ c ε x y` adds the terms over all pairs of positions
  (`gramSum_fst`, `gramSum_snd`). It contains the linear kernel for every `ε`
  (`gramSum_mem`), and for `0 < ε` its width is at most
  `ε · W(x) · W(y)`, where `W = totalWeight c` (`gramSum_width`).
- `gramEnclosure σ c δ x y` is the Gram sum at the scalar tolerance
  `ε = δ / max 1 (W(x) · W(y))`. The tolerance is computed from the executed
  total weights. Since `W(x) · W(y) ≤ max 1 (W(x) · W(y))`, the width is at
  most `δ`. If a total weight is `0`, every term is `(0, 0)` and the result is
  `(0, 0)`, the exact value. If the product of the total weights is below `1`,
  the result is narrower than requested.
- `sqDistEnclosure σ c δ x y` combines the Gram enclosures `A`, `B`, `C` of
  `(x, x)`, `(y, y)` and `(x, y)`, each at tolerance `δ/4`, as
  `(max 0 (A.lo + B.lo − 2·C.hi), A.hi + B.hi − 2·C.lo)`. This is
  `K(x,x) + K(y,y) − 2K(x,y)`, the squared distance by `norm_embedding_sub_sq`.
  The three widths add up to at most `δ/4 + δ/4 + 2·δ/4 = δ`. A negative lower
  endpoint is replaced by `0`; the squared norm is nonnegative, so containment
  is kept.
- `gramEnclosure?` and `sqDistEnclosure?` return these intervals when `0 < σ`,
  `0 < c` and `0 < δ`, and `none` otherwise (`gramEnclosure?_eq_some_iff`,
  `gramEnclosure?_eq_none_iff` and the two statements for the squared distance).
  A nonpositive bandwidth, cap or tolerance is rejected, not repaired.

### Statements

- **Containment.** For `0 ≤ c` and every `σ` and `δ`, `gramEnclosure` contains
  the linear kernel (`gramEnclosure_mem`) and `sqDistEnclosure` contains the
  squared RKHS distance (`sqDistEnclosure_mem`). The tolerance only selects the
  precision, and the kernel depends on the bandwidth through `σ²`. At `σ = 0`
  the library kernel is the all-ones kernel, by the convention for division by
  zero, the rational exponent is `0` as well, and the total functions enclose
  that value; the validated forms reject `σ ≤ 0`.
- **Width.** For `0 ≤ c` and `0 < δ` the width is at most `δ`
  (`gramEnclosure_width`, `sqDistEnclosure_width`). This holds for all lists:
  empty lists, zero total weight, repeated pairs and pairs with
  `death ≤ birth`.
- **Range.** The lower endpoint is at most the upper one for `0 ≤ c`
  (`gramEnclosure_fst_le_snd`, `sqDistEnclosure_fst_le_snd`), and the lower
  endpoint of the squared distance is nonnegative (`sqDistEnclosure_fst_nonneg`).
- **Returned intervals.** If `gramEnclosure? σ c δ x y = some I` or
  `sqDistEnclosure? σ c δ x y = some I`, then `I` contains the value and has
  width at most `δ` (`gramEnclosure?_spec`, `sqDistEnclosure?_spec`). The
  hypothesis `0 ≤ c` of these statements only serves to form the weight.
- **Diagrams.** If the finite part of a diagram `D` is the multiset of the real
  points of `x`, then `diagramEmbedding σ w D = embedding σ w (realPoints x)`
  for every weight `w` (`diagramEmbedding_eq_embedding_realPoints`). Essential
  bars of `D` are not in its finite part and play no role, as in the existing
  `diagramEmbedding`. A diagram excludes `birth = death` only, so a list with
  reversed pairs, `death < birth`, can be the finite part of a diagram and is
  covered. A list containing a pair with `death = birth` is not the finite part
  of any diagram.

The bandwidth of the statements is the real number obtained from the rational
`σ`. Library theorems about `linearKernel`, `embedding` and `Space` hold for
every real bandwidth and apply at it. In `linearKernel` the bandwidth is an
ordinary argument, and simplification can replace the cast of a numeral by the
real numeral. In `embedding` the bandwidth is part of the type `Space σ`.

### What is not claimed

- **Relative error.** The widths are absolute. For well separated points or a
  small bandwidth the lower endpoint of a Gram enclosure is `0`.
- **Decisions.** An enclosure does not decide equality. For identical or
  permuted lists the squared distance is `0`, and the result is an interval
  `(0, u)` with `u ≤ δ`; no theorem states that the embeddings are equal. A
  positive lower endpoint proves that two embeddings differ.
- **Diagonal pairs and diagrams.** No lemma removes pairs with `death = birth`
  from a list, and no diagram is constructed from a list. In the occurrence
  family such a pair has weight `0` and contributes nothing.
- **Essential bars.** The lists hold finite pairs only.
- **Other quantities.** The RKHS distance itself, which is a square root, the
  Gaussian diagram kernel of the embeddings, Gaussian pixel integrals and the
  `PiLp 1` persistence-image norm are not enclosed. Other weights, such as the
  arctan weight, are not covered.
- **Shape of the output.** No theorem states that intervals for smaller
  tolerances are nested, that the endpoints are monotone, that the widths are
  optimal, or that permuted lists give the same interval. Two fixtures check
  nesting for one pair of tolerances (`gram_cross_refines`,
  `sqDist_cross_refines`) and two check a permuted list (`gram_permuted`,
  `sqDist_identical`), by evaluation.

### Cost

Write `m` and `n` for the lengths of the lists.

- **Terms.** The cross Gram sum has `m·n` terms, and each term with a nonzero
  product of weights makes one call of `expEnclosure`. The squared distance
  makes at most `m² + n² + m·n` calls. The symmetry of `K(x,x)` is not used, and
  its diagonal terms are computed; their exponent is `0`, which needs no
  halving.
- **Scalar tolerance.** Each Gram sum has its own scalar tolerance, computed
  from its own pair of total weights: `δ / max 1 (W(x)·W(y))` for
  `gramEnclosure σ c δ x y`, and `(δ/4) / max 1 (W(x)²)`,
  `(δ/4) / max 1 (W(y)²)` and `(δ/4) / max 1 (W(x)·W(y))` for the three Gram
  sums of `sqDistEnclosure σ c δ x y`.
- **Scalar precision.** Each call has the cost of the scalar enclosure at the
  exponent of the two points and at the scalar tolerance `ε` of its Gram sum.
  The number of halvings is about the binary logarithm of the squared Euclidean
  distance divided by `2σ²`, and the number of tolerance bits is the number of
  binary digits of `1/ε`. A small bandwidth costs through the halvings; large
  total weights and a small tolerance cost through the tolerance bits.
- **Bit growth.** The exponent has the denominator of the squared coordinates
  times that of `2σ²`, and the Taylor stage of the scalar enclosure works with
  exact rational numbers at that exponent. The scalar endpoints are dyadic, the
  terms are weights times dyadic numbers, and the sums are exact.

These counts are documented. No theorem states them, and no fixed-cost
exponential and no bound on the bit complexity is claimed.

### Examples

`TDA.Persistence.Enclosure.GramExamples` states the complete value of
`gramEnclosure?` or `sqDistEnclosure?` for each fixture and checks it by kernel
evaluation. The lists are `pair = [(0, 1), (1, 3)]`, `single = [(0, 2)]`,
`weightless = [(1, 1), (3, 2)]` and `negative = [(-3, -1), (-1/2, 1/2)]`.
Unless stated otherwise the bandwidth is `1`, the cap is `1` and the tolerance
is `1/100`.

| Lists | Parameters | Gram sum | Squared distance |
|---|---|---|---|
| `pair`, `single` | | `(1993/2048, 1999/2048)` | `(19895/16384, 39853/32768)` |
| `pair`, `single` | `δ = 1/10⁶` | `(8173943/8388608, 4086973/4194304)` | `(326242939/268435456, 163121501/134217728)` |
| `pair`, `pair` | | `(17723/8192, 8865/4096)` | `(0, 7/16384)` |
| `[(0, 2), (0, 2)]`, `single` | | `(2047/1024, 2)` | `(2047/2048, 2049/2048)` |
| `[]`, `pair` | | `(0, 0)` | `(35455/16384, 70917/32768)` |
| `negative`, `[(-2, 1)]` | `c = 2` | `(1845/2048, 7387/8192)` | `(118845/16384, 29715/4096)` |
| `[(0, 1)]`, `[(10, 12)]` | | `(0, 1/2¹⁷)` | `(524159/262144, 2)` |
| `[(0, 1)]`, `[(0, 2)]` | `σ = 1/1000` | `(0, 1/2²⁹)` | `(2146959359/1073741824, 2)` |
| `[(0, 1)]`, `[(0, 1001/1000)]` | `σ = 1/1000` | `(155/256, 623/1024)` | `(1609/2048, 1613/2048)` |

Further fixtures cover executed weights, exponents and terms, a permuted list,
two empty lists, the list `weightless` of zero total weight, a Gram sum of six
terms with cap `3`, and the nonpositive bandwidths, caps and tolerances that are
rejected. The intervals at tolerance `1/10⁶` lie inside those at `1/100`. The
squared distance of `pair` and its reversal is enclosed by `(0, 7/16384)`.

The consumers use the theorems at executed intervals, without assuming any
value of a transcendental number:

- `1993/2048 ≤ linearKernel … (realPoints pair) (realPoints single) ≤ 1999/2048`
  for the library linear kernel with cap `1`, at the bandwidth obtained from
  the rational `1` (`linearKernel_bounds`) and with the bandwidth written as
  the real number `1` (`linearKernel_bounds_one`);
- the width bound at that interval (`gram_width`);
- the linear kernel of `weightless` and `pair` is exactly `0`
  (`linearKernel_weightless`);
- `19895/16384 ≤ ‖embedding … pair − embedding … single‖² ≤ 39853/32768`, so
  the two embeddings are distinct (`sqDist_bounds`);
- the squared distance of the embeddings of `pair` and of its reversal is at
  most `7/16384` (`sqDist_identical_bound`);
- the same two-sided bound for `diagramEmbedding` of the diagram with the
  finite points `(0, 1)`, `(1, 3)` and one essential bar, and of the diagram
  with the point `(0, 2)` (`diagram_sqDist_bounds`).

## Source scope

These are elementary library results. The scalar enclosure is derived from the
pinned [mathlib](references.md#mathlib-56a0058) remainder bound for the
exponential series. The Gram and distance parts rest in addition on the library
definitions of the weight, the kernel, `linearKernel` and the embedding, and on
the library identity `norm_embedding_sub_sq`. They are not attributed to a
paper, and no source comparison is claimed.
