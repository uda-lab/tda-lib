# Finite coordinates for actual simplicial cycles and boundaries

For a preabstract simplicial complex `K` with ordered vertices and a commutative
coefficient ring `R`, `chainCoordinates K R n` identifies the actual degree-`n`
chain module with functions on degree-`n` faces when that face type is finite.
`coordinateCycles K R n` is the pullback of the **actual** cycle submodule along
the inverse equivalence. Restricting that equivalence gives `cycleCoordinates`.
Its underlying function takes an actual cycle to its face coefficients.

In degree zero, the outgoing differential vanishes, so coordinate cycles are
the entire function module. In degree `n+1`, the existing actual-cycle kernel
equation and `boundaryMatrix_mulVec` identify coordinate cycles with the kernel
of `Matrix.toLin' (boundaryMatrix K R n)`. This matrix is the differential from
chains of degree `n+1` to degree `n`; in particular `boundaryMatrix K R 0`
is the incoming edge-to-vertex map and can be nonzero.

`coordinateBoundaryToCycles` restricts that concrete incoming matrix map to
coordinate cycles. It lands there because an actual boundary is an actual cycle:
in degree zero the outgoing differential is zero, and in positive degree this
is `boundary_comp_boundary`. `coordinateBoundaries` is its range **in the cycle
subtype**. A coordinate cycle belongs to this submodule exactly when it has a
preimage under the incoming matrix. The two directions of
`simplicialBoundaries_map_cycleCoordinates` use
`mem_simplicialBoundaries_iff`: an actual boundary yields its incoming
coordinate vector, and a coordinate preimage yields an actual chain by the
inverse coordinate equivalence. Thus the equality compares submodules inside
cycles, with no quotient construction.

For `K ≤ L` in one ordered ambient vertex type, `coordinateCycleIncl` restricts
the actual inclusion matrix to coordinate cycles. Actual cycle inclusion and
`chainInclusionMatrix_mulVec` prove that the restriction lands in target cycles
and that it commutes with `cycleCoordinates`. The matrix identity
`B_L,n J_(n+1) = J_n B_K,n` proves the incoming-map square; taking ranges
shows forward preservation of coordinate boundaries.

The private actual-face fixtures enumerate every displayed row and column by
proved face bijections. For the edge, the vertex incidence column is
`[-1; 1]`, so an edge coefficient `a : ℤ` has boundary `[-a; a]`.
The positive-degree kernel theorem and the coefficient at the second vertex
show that every degree-one coordinate cycle of this edge is zero. The isolated
vertex has all degree-zero coordinate vectors as cycles and no incoming
boundaries.

For the unfilled triangle, the signed actual edge chain `e01 - e02 + e12`
has coordinates `[1; -1; 1]`. The actual vertex rows
`[-1,-1,0]`, `[1,0,-1]`, `[0,1,1]` cancel on that vector. Its `e01`
coefficient proves it is nonzero; the absence of triangles proves it is not a
coordinate boundary. Inclusion into the filled triangle carries it to the
same coefficients on a distinct face subtype. There it is the incoming
boundary of the triangle coefficient `1`, while remaining nonzero as a cycle.
The inverse coordinate equivalence identifies this with the actual triangle
boundary. The edge-to-filled-triangle incoming square is also checked at a
variable integer coefficient and yields `[-a; a; 0]` on both sides.

All generic statements include the zero ring; `ZMod 1` exercises this case.
Finite total face sets permit local noncomputable degreewise `Fintype`
instances via `faceFintypeOfTotalFinite`. They do not supply an executable
face enumeration or a finite master filtration matrix. The construction makes
no coordinate homology quotient, barcode, rank, or reduction claim, and it
covers only same-ambient inclusions with the given vertex order.
