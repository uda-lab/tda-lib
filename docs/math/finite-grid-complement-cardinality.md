# Minimal-complement cardinalities in finite grids

For a finite lattice `S` with bottom and top, `minimalComplement p` is the set of
minimal elements outside the principal downset `↓p`; `complementCard p` counts
those elements, and `maxComplementCard` takes the maximum over `p`. These are
minimal generators of the complement, not covers above `p`.

In a finite product of nonempty finite linear orders, every minimal complement
has exactly one active coordinate. At that coordinate its value is a minimal
complement value, and all other coordinates are bottom. This gives an actual
injection into the index set and proves the bound by the number of factors,
including the empty product and singleton factors.

Adjoining a new top requires a correction: the old top has the singleton
complement consisting of the new top, while the new top itself has empty
complement. A non-top point retains precisely the old minimal complements.
Consequently the maximum for `WithTop S` is at most
`max 1 (maxComplementCard S)`.

For the existing interval-pair subtype
`PairPoset S = {q : WithTop S × WithTop S // q.1 ≤ q.2}`, a point `(j,k)` has
two disjoint minimal-complement families. The first consists of diagonal pairs
`(a,a)` for `a ∈ minimalComplement j` with `a ≤ k`. The second consists of
`(⊥,b)` for `b ∈ minimalComplement k`. The exact count is the restricted
diagonal-family cardinality plus `complementCard k`; bounding the first family
by `complementCard j` gives the pair maximum bound
`2 * max 1 (maxComplementCard S)`.

For an actual `CoordinateGrid n` with every coordinate factor nonempty, the
proved maxima are at most `n` on `G.Point`, at most `n` on `WithTop G.Point`
when `n ≥ 1`, and at most `2*n` on `PairPoset G.Point` when `n ≥ 1`. The
explicit positive-dimension hypothesis accounts for the new-top singleton
when the underlying point lattice has only one element.

Combining the point-grid count with the existing finite-injective Hom
dimension theorem proves `HasProjectiveDimensionLE (Hom(HookSum,M)) (n - 1)`
for every pointwise finite-dimensional ordinary injective `M` on the grid, over
any field. Every supplied certified minimal rank-projective resolution of
that Hom module vanishes above the same bound. The result supplies a
combinatorial input for later incidence-algebra estimates; it does not claim a
global-dimension bound or the `2n−2` persistence estimate.

The source context is [BOOS24-v3, §2.4 and Notations 5.2 and 5.9,
Proposition 5.14, and the minimal-complement count used in Theorem
5.16](references.md#BOOS24-v3). This formalization proves the displayed
finite-product, adjoined-top, and actual interval-pair counts directly. It
does not claim the rest of Theorem 5.16 or identify a source error.

The implementation is in `TDA.Persistence.FiniteLatticeComplementCardinality`
and `TDA.Persistence.FiniteGridInjectiveRankDimension`; the focused fixtures
are in `TDA.Persistence.FiniteGridComplementCardinalityExamples`.
