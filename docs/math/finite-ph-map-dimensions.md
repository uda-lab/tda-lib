# Computing the rank and nullity of a finite homology map

A simplicial map can merge homology classes or miss classes in its target.
`runHomologyDimensions` computes both the dimension of its image, called its
rank, and the dimension of its kernel, called its nullity. These are dimensions
of the actual signed simplicial homology map over F₂.

## Query and validation

Supply the finite simplex lists `xs` and `ys`, homological degree `p`, integer
thresholds `a` and `b`, and vertex function `f : ℕ → ℕ` used by
[the induced-map API](finite-ph-maps.md). The map goes from the source sublevel
at `a` to the target sublevel at `b`. The lists retain their existing validity
requirements, including face closure and compatible integer grades.

The procedure checks `VertexMapInput`: both lists must be valid, and the image
of every admitted source face must be listed at or below the target threshold.
The condition covers all admitted face degrees, even when the queried homology
groups vanish. Failure returns `none`.

Success returns `some out`, where `out : HomologyMapDimensions` has two fields:

- `rank`: the dimension of the image;
- `nullity`: the dimension of the kernel.

Their sum is the source Betti dimension, the number of records returned by the
existing degree-specific basis query. The map is injective exactly when
`nullity = 0`. It is surjective exactly when `rank` equals the **target** Betti
dimension. Empty source and target groups are handled by the same rules.

## A rectangular map with both a kernel and a cokernel

Let the source have three isolated vertices, all at grade −2, and the target
have four. Send the first source vertex to one target vertex and both remaining
source vertices to a second target vertex. On H₀ the source dimension is three,
the target dimension is four, and the query returns rank two and nullity one:

```lean
import TDA.Persistence.Reduction.FiniteInputHomologyDimensionsExamples

open TDA.Persistence.Reduction.FiniteInput
open TDA.Persistence.Reduction.FiniteInput.DimensionExamples

#eval runHomologyDimensions source target 0 (-2) (-2) merge
-- some { rank := 2, nullity := 1 }
```

The map is neither injective nor surjective; its cokernel has dimension two.
`DimensionExamples.rectangular_actual` proves the range and kernel dimensions
and both failures for the actual simplicial homology map.

For a positive-degree example, `DimensionExamples.theta_run` uses the theta
graph with the triangle `013` added at grade 2. The inclusion from grade 1 to
itself has H₁ rank two and nullity zero. The inclusion from grade 1 to grade 2
has rank one and nullity one: one loop becomes a boundary.

## Computation and correctness

The procedure materializes the existing induced-map matrix in the computed
source and target homology bases. It enumerates all source F₂ coordinate
vectors and counts their distinct images. For a linear map of rank `r` over
F₂, this count is exactly `2^r`; the count includes the zero vector. Thus a zero
image has cardinality one, and its base-two natural logarithm is zero.
Subtracting the rank from the source Betti dimension gives the nullity.

`homologyMap_image_card` proves the cardinality identity using Mathlib's
finite-module cardinality theorem. `homologyMapMatrix_range` transports the
actual image through the existing target coordinate equivalence.
`homologyMapDimensions_rank_actual` and
`homologyMapDimensions_nullity_actual` identify the computed fields with the
actual range and kernel dimensions. Rank-nullity justifies the natural-number
subtraction. `runHomologyDimensions_correct` obtains all geometric hypotheses
and both dimension equalities from successful execution. The injectivity and
surjectivity criteria are also public theorems.

Execution uses finite enumeration and F₂ arithmetic. Noncomputable dimensions
and coordinate equivalences occur only in proofs. Enumeration is exponential
in source Betti dimension, so the API is intended for small computed homology
groups. It supplies no efficient elimination algorithm or running-time bound.
For a particular target class, use the separate
[homology lift procedure](finite-ph-lifts.md) to obtain a source cycle and a
bounding-chain certificate.

The contract is derived from the existing Lean definitions, signed simplicial
adapter and proved coordinate equivalences. It is not a full-text comparison
with a primary article.
