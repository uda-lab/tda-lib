# Total persistence and finite Rips–Čech bounds

For a real persistence diagram `D`, the degree-`p` total persistence is

`Pers_p(D) = Σ |d − b|^p`,

where the sum ranges over the finite bars `(b,d)` in `D`. Essential bars are excluded, as in
the finite-part kernel embeddings. The exponent `p` is a natural number, and the absolute value
makes the definition total on arbitrary diagrams. On a positive diagram, each summand is
`(d − b)^p`. At `p = 0`, total persistence is the number of finite bars, including
multiplicity.

## Diagram laws

Total persistence is nonnegative and is zero when the finite part is empty. For `c > 0`,
positive scaling of a diagram gives

`Pers_p(cD) = c^p Pers_p(D)`,

and translating both endpoints by the same real number leaves `Pers_p` unchanged for every
`p`. If every finite bar length is at most `M`, with `0 ≤ M`, then

`Pers_p(D) ≤ |D_fin| M^p`,

where `|D_fin|` is the finite-bar count. The same estimate follows when both finite coordinates
lie in `[0,M]`; positive bars then have length at most `M`.

## Coordinates and face counts

For a finite sublevel diagram, every finite coordinate is a value of the filter on a face.
Thus, if all face values lie in `[0,M]`, finite birth and death coordinates lie in that interval,
and essential birth coordinates lie in `[0,M]` as well.

For a Rips filter on a finite labelled metric space, `M` can be the diameter of the full carrier.
For a Čech filter, `M` can be any enclosing radius around an ambient point. If the label metric
is realized by the ambient distances, the label diameter is another valid choice. The enclosing
radius formulation does not require a metric on the labels.

Fix a compatible face order. Each face supplies at most one endpoint occurrence across all
degrees. A finite death in degree `n` can occur only at a face with `n + 2` vertices, while a
birth in degree `n` can occur only at a face with `n + 1` vertices. Consequently,

`# finite bars in degree n ≤ # Face K (n + 1)`,

and

`# essential bars in degree n ≤ # Face K n`.

For the full complex on `N` vertices these face counts are

`# Face (full complex) (n + 1) = C(N, n + 2)`

and

`# Face (full complex) n = C(N, n + 1)`.

Combining the finite-bar count with the coordinate estimate gives the size-dependent bound

`Pers_p(dgm k f n) ≤ C(N, n + 2) M^p`.

For Rips diagrams, `M` is the carrier diameter. For Čech diagrams, it may be an enclosing
radius or, under distance compatibility, the label diameter.

## Kernel consumer

The Rips weighted-kernel estimate replaces the two diagram-dependent finite-bar counts
by `2 C(N, n + 2)`. Thus, for a weight with stability constant `C_σ,A,B`, the embedding
difference is bounded by

`C_σ,A,B · (2 C(N, n + 2)) · pairwiseDiscrepancy(d,e)`.

This is a size-uniform statement for configurations on a fixed carrier size `N`; its constant
still depends on `N`.

These bounds supply the card-times-maximum total-persistence factors in KFH18 [eqs. (8)–(9)](references.md#KFH18).
In the `p = 1` use of eq. (9), the factor `Pers_0` is exactly the finite-bar count. The source's
card-independent total-persistence estimate in
Lemma 4 is not obtained here. In particular, this note does not formalize assumption (W1),
Proposition 8, Theorem 9, or Corollary 12. It also does not cover real exponents or the
vanishing of essential bars in degree `n ≥ 1` for Rips and Čech diagrams.

## Fixtures

The checked examples use coefficients in `ZMod 2`.

- The two-point Rips degree-zero diagram has one finite bar of length `2`; its total persistence
  is `2^p`, and the face-count bound is attained. The two-point Čech diagram has one finite bar
  of length `1`.
- On the library triangle, the degree-one finite-bar count for both Čech and Rips is at most
  `C(3,3) = 1`. The Čech degree-one first-order total persistence is at most `3`. In degree two,
  both finite parts have count zero by `C(3,4) = 0`.
- Repeated Čech labels have zero spread, so their finite part and total persistence vanish in
  every degree and exponent. This uses only the Čech filter and no label metric.
- The filled real triangle has degree-one bar `(1,2)`. Scaling its filter by `2` changes its
  first-order total persistence from `1` to `2` and its second-order total persistence to `4`.
- The two-point Rips degree-zero diagram has one essential bar, satisfying the general essential
  count bound, and its exponent-zero total persistence is the finite-bar count `1`.

## Lean interfaces

`TDA.Persistence.TotalPersistence` defines total persistence and its diagram-level laws.
`TDA.Persistence.TotalPersistenceRipsCech` proves coordinate, face-count, Rips, Čech and
size-uniform weighted-kernel bounds. `TDA.Persistence.TotalPersistenceRipsCechExamples`
contains the fixtures above. The endpoint-degree facts used by the face-count argument are
recorded in `TDA.Persistence.FaceEndpointUniqueness`.
