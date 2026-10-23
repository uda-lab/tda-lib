# Persistence rectangle measures

Let `M` be a real-indexed persistence module over a field `k`. A structure map
across a strict inequality has finite-dimensional image when `M` is q-tame;
its source and target fibers may be infinite-dimensional.

For `a ≤ b < c ≤ d`, write `I(s,t)` for the image of `M(s → t)` and
`K(c,d)` for the kernel of `M(c → d)`. The rectangle value is the dimension
of the genuine quotient

```text
(I(b,c) ∩ K(c,d)) / (I(a,c) ∩ K(c,d)).
```

The denominator is interpreted inside the numerator using functoriality.
`PersistenceMeasureSpace` defines this quotient. Q-tameness makes it
finite-dimensional because its numerator lies in `I(b,c)`.
`persistenceMeasureValue` is its dimension. The construction requires no
interval decomposition.

`persistenceMeasureValue_four_rank` proves

```text
μ(a,b,c,d) = rank(b,c) - rank(a,c) - rank(b,d) + rank(a,d).
```

Each rank is a finite image dimension. Rank-nullity is applied inside these
images, so this formula does not require finite-dimensional fibers. The
nonnegative integer value comes from the quotient dimension, rather than
truncating a signed expression. `persistenceMeasureValue_split_birth` and
`persistenceMeasureValue_split_death` prove finite additivity along the two
coordinates. Degenerate strips have value zero, and each count is bounded
by the crossing rank `rank(b,c)`.

The boundary convention follows
[Chazal–de Silva–Glisse–Oudot, arXiv:1207.3674v3, §2.1](https://arxiv.org/pdf/1207.3674v3):
an interval contributes exactly when it contains `b,c` and excludes `a,d`.
This retains the information needed for decorated endpoints. For the
existing half-open interval `[0,2)`, the rectangle `[-1,0] × [1,2]` has
value one; `[0,1] × [3/2,2]` has value zero. A zero strict crossing map
has zero rectangle count, so ephemeral information is absent from separated
rectangles.

## The essential boundary

The quotient `PersistenceTailSpace` is `I(b,c) / I(a,c)`.
Its dimension `persistenceTailMeasureValue` is the extended rectangle value on
`[a,b] × [c,∞]`: it counts classes surviving to `c`, including their essential
contribution. It obeys

```text
μ(a,b,c,d) + tail(a,b,d) = tail(a,b,c).
```

Thus these natural numbers decrease as `c` increases. Their minimum is
attained, and q-tameness makes every later target retain that value.
`essentialMeasureValue` defines this eventual value on a birth strip.
`PModule.QTame.essentialMeasureValue_split_birth` proves its finite
additivity. An existing essential interval `[0,∞)` contributes one on
`[-1,0]` at this boundary.

These modules construct rectangle and essential-boundary measures. The
representation of these measures by a decorated locally finite diagram,
bottleneck stability for those diagrams, and compatibility with the full
finite diagram API remain outside these results. In particular the
finite `Diagram ℝ`, whose occurrences form a `Multiset`, does not represent
the general q-tame diagram.
