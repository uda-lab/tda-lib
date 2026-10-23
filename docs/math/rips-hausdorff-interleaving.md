# Hausdorff bounds for Rips homology modules

Let X and Y be metric spaces isometrically embedded by f and g in a common
metric space Z. Their vertex sets may be infinite, and their images need not
be closed. Write M_X and M_Y for their simplicial Rips homology persistence
modules in a fixed degree, over a fixed coefficient ring. Rips time is
diameter, thresholds are closed, and every negative stage is empty.

If the ambient Hausdorff distance r between the images is finite, then for
every ε > 2r there is an actual ε-interleaving between M_X and M_Y.
Consequently, their extended interleaving distance is at most 2r.
Nonempty totally bounded images satisfy the finiteness hypothesis; neither
completeness nor compactness is required. The coefficient and ambient
universes are independent of the common vertex universe. Auxiliary vertex
orders are arbitrary, and the isometries need not preserve them.

## Near points and the interleaving

Fix ε > 2r. The relation

C = {(x,y) | dist(f(x),g(y)) < ε/2}

is total in both directions: the strict inequality r < ε/2 guarantees a
near point in the opposite image. This uses the defining infimum property
of Hausdorff distance and does not require a closest point. For two related
pairs, the metric inequality gives

|dist(x,x′) − dist(y,y′)|
≤ dist(f(x),g(y)) + dist(f(x′),g(y′)) < ε.

`Rips.exists_relation_distortion_le_of_hausdorffDist_lt` proves this geometry.
`Rips.hausdorffInterleavingOfLt` then applies the existing canonical relation
interleaving to construct both natural transformations and their two
double-shift equations. It works in every degree over every ring, with the
closed thresholds and empty negative tail unchanged.

Every positive increment above 2r therefore bounds the interleaving distance.
Passing to the infimum gives
`realInterleavingDistance_le_two_mul_hausdorffDist_of_ne_top`.
The assumption `hausdorffEDist (range f) (range g) ≠ ⊤` makes the real-valued
Hausdorff distance in this statement meaningful. For arbitrary images,
`realInterleavingDistance_le_two_mul_hausdorffEDist` instead gives the bound
directly in the extended nonnegative reals, including the infinite case.

`realInterleavingDistance_le_two_mul_hausdorffDist_of_totallyBounded` supplies
the finite-distance premise from total boundedness of two nonempty images.
The ambient space itself may be noncompact and nonproper.

## An infinite nonclosed example

The open interval (0,1) and closed interval [0,1] in ℝ are both infinite and
totally bounded. Their closures agree, so their ambient Hausdorff distance
is zero. `RipsHausdorffInterleavingExamples` proves that the open image is
nonclosed, that the two Rips modules have interleaving distance zero, and
constructs an interleaving for every positive ε, over every ring and in
every degree. These statements do not identify the inclusion-induced maps
with fiberwise isomorphisms or claim that the infimum is attained at zero.

## Source correspondence and scope

The near-point relation and its factor-two distortion bound use the
correspondence mechanism in [CDSO13-v3 §4.2 and Lemma 4.3](references.md#CDSO13-v3).
The ring-coefficient module statements are library extensions of that
mechanism. The library retains its own whole-real negative-tail convention;
no equivalence with the source's nonpositive-time vertex remark is claimed.

The result concerns persistence modules and their actual interleavings.
To compare diagrams of infinite spaces, one also needs a persistence-measure
construction of locally finite diagrams, including essential bars, and
algebraic stability for those diagrams. Those conclusions are separate
from the module bound proved here.
