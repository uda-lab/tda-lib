# Finite coordinates for simplicial chains

For a face `σ : Face K n`, `Chain K R n` is the finitely supported
coefficient function on faces of cardinality `n + 1`. Over a commutative ring,
`chainCoordinates` uses `faceBasis.equivFun` to identify this chain with its
coefficient function when the degreewise face type is finite. Its forward map
returns `c σ` without changing the ordered orientation. The upstream chain,
boundary, and homology definitions retain their broader `Ring R` scope.

`boundaryMatrix K R n` is `LinearMap.toMatrix` of the existing signed map
`boundary K R n : C_(n+1) → C_n`. Rows are `n`-faces; columns are
`(n+1)`-faces. Deleting vertex `i` from a column gives coefficient
`(-1)^i` in the resulting row; every other row gets zero. Deletion indices
are distinct because deleting two different ordered vertices yields different
finsets. The entry theorem sums these signed indicators, and the individual
sign and zero-off-deletion theorems follow. These equalities hold in the zero
ring, where a signed entry may itself be zero.

The matrix-vector theorem identifies multiplication by this rectangular matrix
with the boundary on every chain. `boundaryMatrix_toLin` gives the
inverse conversion. Applying `toMatrix_comp` to the already proved
`boundary_comp_boundary` yields `B_n B_(n+1) = 0`, with rows in degree `n`
and columns in degree `n+2`. The ordinary outgoing degree-zero map is the
packaged chain-complex differential and is zero; `boundary K R 0` instead
maps edges to vertices and can be nonzero.

For `h : K ≤ L` in one ambient ordered vertex type, `chainInclusionMatrix`
coordinates the existing `chainIncl`. Its entry is one when the included
source face equals the target row and zero otherwise. Its matrix-vector square
holds for every chain. Applying `toMatrix_comp` to `boundary_chainIncl` gives
`B_L,n J_(n+1) = J_n B_K,n`. This uses two separately enumerated intermediate
face types. It covers same-ambient inclusions with one vertex order; no
orientation transport for different orders or vertex maps is asserted.

The generic matrix declarations use only the listed adjacent degreewise
`Fintype`, `DecidableEq`, and `Finite` assumptions. Domain columns need an
enumeration and decidable equality; the final row type needs only finiteness.
Face equality is available from the supplied vertex order and does not decide
membership in `K`. An order instance may itself be noncomputable. When total
faces are finite, `faceFintypeOfTotalFinite` explicitly and noncomputably
turns the existing degreewise `Finite` result into a local `Fintype`; it is
not a global instance and does not replace a caller's enumeration. Degree-zero
finiteness bounds the support of one complex, so its total faces are
mathematically finite, but this module proves no adapter from that observation.
For infinitely many filtration stages, stagewise finiteness alone gives no
finite total union. A finite set of stages permits a finite union after a
separate proof and chosen enumeration.

The private fixtures use faces of the empty complex, an isolated vertex,
a support-aware edge on vertices 0 and 1, and a filled triangle. Proved
bijections establish that their displayed integer arrays cover every row and
column: `B_edge,0 = [-1; 1]`, `B_triangle,0 = [-1 -1 0; 1 0 -1; 0 1 1]`,
and `B_triangle,1 = [1; -1; 1]` in edge order `01, 02, 12`. They prove
integer cancellation and the nontrivial edge-to-triangle inclusion square,
including variable scalar coefficients. A `ZMod 1` fixture checks the zero
ring. These are kernel proofs in a noncomputable theory path, not an executable
matrix enumeration or persistent-homology computation.

This module constructs no square master matrix, quotient-homology coordinates,
rank or barcode result, or reduction certificate. An executable adapter would
need exact finite face enumeration and further correspondence proofs.
