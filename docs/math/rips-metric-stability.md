# Metric input and Rips diagram stability

Fix a finite labelled vertex type V and two real-valued metrics d,e on V. The labels
identify the vertices being compared. The metrics are explicit `MetricSpace V` values;
the API does not require two metric instances on V at once.

## Diameter filtration

The full simplex complex contains every nonempty finite subset of V. For a finite
subset s, define

f_d(s) = max {d(v,w) : v,w ∈ s},

with the auxiliary empty maximum equal to zero. The empty set is excluded from the
complex. A singleton has diameter zero, and an edge has value exactly its endpoint
distance. Increasing a face can only increase its diameter.

The diameter values define a `FilterFunction` on this fixed full complex. Its sublevel
at r consists exactly of nonempty s with d(v,w) ≤ r for all v,w ∈ s, including self-pairs.
Thus vertices appear at zero and every stage below zero is empty. This is the closed
Rips filtration with diameter as its time parameter; no ball-radius rescaling is used.

## Perturbation bound

Define the distance-matrix discrepancy

δ = max { |d(v,w) − e(v,w)| : v,w ∈ V },

with δ = 0 when V is empty. For every finite s,

|f_d(s) − f_e(s)| ≤ δ.

Indeed, d(v,w) ≤ e(v,w) + δ ≤ f_e(s) + δ for each pair in s. Taking the maximum,
including its zero seed, gives f_d(s) ≤ f_e(s) + δ. Reversing the metrics proves the
absolute-value estimate. The zero seed also handles s empty without choosing a vertex.

Let dgm_k(f_d,n) be the existing diagram of simplicial sublevel homology in
degree n over a field k. The face supremum discrepancy is at most δ, so the existing
finite-face stability theorem gives

bottleneck(dgm_k(f_d,n), dgm_k(f_e,n)) ≤ δ.

In Lean the right side is `ENNReal.ofReal δ`. The theorem uses V : Type u with
`LinearOrder V` and `Fintype V`, and k : Type u with `Field k`, exactly as required by
the existing diagram interface after specializing to a finite carrier. It holds for
every n. It retains occurrence multiplicity, finite interval conventions and essential
deaths at `⊤`; no essential-cardinality or genericity hypothesis is added.

The [finite persistence-image consumer](rips-persistence-images.md) composes this bound
with Gaussian pixel stability and an explicit finite-bar-count factor. Essential bars
remain in the bottleneck comparison and are omitted from the image.

## Interfaces and examples

`TDA.Filtration.Rips` defines `fullComplex`, `diameter`, `filter` and
`pairwiseDiscrepancy`. `mem_sublevel_iff` identifies the closed Rips complex, and
`abs_diameter_sub_le_pairwiseDiscrepancy` supplies the elementary input estimate.
`TDA.Persistence.RipsStability` proves `faceSupDifference_filter_le` and
`bottleneck_dgm_le_pairwiseDiscrepancy`. Ordinary Filtration and Persistence imports
include their respective modules. These are noncomputable mathematical definitions;
they do not provide an executable distance-matrix or point-cloud reduction pipeline.

The example module checks the empty carrier and a singleton, then compares two metrics
on `Fin 2` with off-diagonal distances one and two. Their edge entry times are one and
two, their discrepancy is one, and their diagrams satisfy the stated bound in
every degree.

## Source correspondence and scope

The diameter threshold at nonnegative scales matches
[Chazal–de Silva–Oudot §4.2.1](references.md#CDSO13-v3). Section 4.2 defines
correspondence distortion; for the identity relation on a nonempty finite labelled
set, its displayed distance discrepancy has the same formula as δ. This observation
does not introduce a formal correspondence interface.

The source's nonpositive-scale vertex remark is not used here: the support-aware
library convention assigns singleton value zero and empty stages below zero. No full
real-indexed convention equivalence is claimed. The same-label diagram estimate is
independently derived through `bottleneck_dgm_le_faceSupDifference`; it does not
formalize the source's Lemma 4.3 interleaving or Theorem 5.2 Gromov–Hausdorff theorem.
The supplied-relation construction below compares different metric vertex types.
Čech comparison and Gromov–Hausdorff selection use separate constructions.

## Relations between different metric label types

Let X and Y carry explicit genuine metrics dX and dY. Supply a native relation C and
ε≥0 with |dX(x,x′)−dY(y,y′)|≤ε whenever (x,y),(x′,y′) belong to C. This includes
pairs with x=x′: two images of the same vertex can have distance at most ε.
For a source face at t, each pair in a nonempty finite subset of its relational
image has antecedents in that face. Hence dY≤dX+ε≤t+ε, proving the shifted
Rips face condition without totality or a finite-image premise. Reversing the relation
and the absolute difference proves the converse geometry.

When C and its native transpose are ambient-total, `Rips.relationInterleaving` uses
the canonical relation maps to construct a homology interleaving. Both fields
are exposed exactly; their double-shift composites are the inclusion-induced
transitions. This works over every ring, every natural homology degree, empty types
and infinite types, with independent orders in a common vertex universe. It bounds
the existing extended interleaving distance. For finite types and a field in the
diagram universe, `bottleneck_dgm_le_of_relation` derives constructibility and finite
dimensionality separately for the two filters. The existing different-grid
matching theorem then bounds their full diagrams, including essential occurrences.

Fixtures compare distance-two and distance-three pairs on different types, and a
singleton with a distance-two pair. Nonzero H₀ images and triangles are
evaluated; a two-vertex difference survives before an edge enters and collapses after
the required transition. Quantitative negative controls refute the geometric
predicate when the bound is too small. Empty, infinite, repeated-point metric
obstruction, noncentral matrix coefficient and trivial-ring cases retain the same
maps.

This implements the supplied-distortion mechanism in CDSO Lemma 4.3's proof,
through Proposition 4.2, at nonnegative scales. The target-distance estimate is
derived directly from the absolute bound; the printed proof's first displayed
comparison is not used without its additive allowance. No erratum is asserted.
The supplied-relation theorem accepts the relation as input. The finite GH bridge
below supplies one; the source's whole-real H₀ convention remains distinct.
Arbitrary-ring signed chains and the finite-diagram corollary are library extensions.
An arbitrary noninjective cloud has no genuine label metric agreeing with all
ambient pair distances; no pseudometric or quotient-cloud foundation is supplied.

## Gromov–Hausdorff stability and sampling

For finite nonempty metric spaces X and Y, every field k and every degree n,

bottleneck(dgm_k(Rips(X), n), dgm_k(Rips(Y), n)) ≤ 2 d_GH(X,Y).

`RipsGromovHausdorff` proves this bound for the full diagrams, with their
finite and essential occurrences. The Lean bound is
`ENNReal.ofReal (2 * GromovHausdorff.ghDist X Y)`. The GH normalization
is the usual half-distortion normalization; the constant two accompanies the
library's diameter time. There is no equal-cardinality or supplied-correspondence
hypothesis.

In a common metric ambient space, let f and g be isometric embeddings of X and Y,
and put r = d_H(range f, range g). The relation

C = {(x,y) | dist(f(x),g(y)) ≤ r}

is total on both sides: each finite image is compact, so the distance to it is
attained. The triangle inequality bounds the distortion of C by 2r, including
pairs sharing a source or target. The existing canonical relation interleaving
then bounds the diagrams by 2r. Mathlib's optimal coupling realizes
r = d_GH(X,Y), so the GH bound follows without assuming an optimizing
correspondence or taking a limit of diagram matchings. The ambient space itself
need not be compact or proper.

`bottleneck_dgm_le_two_mul_ghDist` is the ordered-label entry point. `diagram k X n`
also accepts an arbitrary finite metric space without a vertex order, even when
the field and the two spaces live in different universes. It is the existing
diagram on isometric finite labels in the field's universe.
`diagram_eq_dgm` identifies it with the existing diagram for every vertex order;
`dgm_eq_of_isometryEquiv` permits isometric relabellings that reverse that order.
The chosen finite enumeration changes neither the full diagram nor the estimates.

For finite samples isometrically embedded in one ambient space, Hausdorff error
at most ε gives bottleneck error at most 2ε. If two finite samples are within
extended Hausdorff errors ε and δ of the same possibly infinite set, their finite
diagrams are within 2(ε+δ). Extended Hausdorff distance is used for those hypotheses
so that an empty or unbounded target cannot create a spurious zero error through
the real-valued convention at infinity. Convergence in Hausdorff distance to a
fixed finite nonempty target therefore gives convergence of the full diagrams in bottleneck distance, with varying sample cardinalities allowed.

The correspondence argument specializes the mechanism of CDSO13-v3 §4.2 and
Lemma 4.3 to finite metric spaces, using mathlib's GH coupling and the library's
sublevel-diagram theorem. It retains the library's empty negative tail; it makes no
whole-real H₀ identification with the source's nonpositive-time vertex convention.
The finite sampling comparison above compares only finite diagrams. The
sections below construct the q-tame diagram of a possibly infinite target and
prove its exact Hausdorff and compact Gromov–Hausdorff stability.

These results are abstract existence and correctness statements. Finite labels can
support executable consumers when exact distance comparisons are available; no
algorithm for optimizing GH distance over arbitrary real data or for computing
homology over an arbitrary abstract field is asserted.

## Totally bounded spaces

For a field k, a real persistence module M is **q-tame** if the image of
M(a) → M(b) is finite-dimensional whenever a < b. The fibers M(a) need not be
finite-dimensional. In Lean, `PModule.QTame` uses
`FiniteDimensional k (LinearMap.range (structureMapLinear M hab.le))`.

Let X be any totally bounded metric space. Its closed diameter Rips homology
module is q-tame over every field and in every degree. Fix a < b and put
ε = (b−a)/2 > 0. Total boundedness supplies a finite ε/2-net F ⊆ X. The relation

C = {(x,f) ∈ X × F | dist(x,f) < ε/2}

is total on both sides, since the net covers X and every f is related to itself.
The triangle inequality bounds its pairwise distortion by ε. The canonical
relation interleaving gives a composite

M_X(a) → M_F(a+ε) → M_X((a+ε)+ε) = M_X(b).

The interleaving law identifies this composite with the structure map, and the
middle homology is finite-dimensional because F is finite. The range is
therefore finite-dimensional. This proof works for the empty space and all
real source times; no vertex is added to the negative tail.

`Rips.exists_finite_net_relation` proves the finite-net geometry and
`Rips.qTame_of_totallyBounded` gives the module theorem. The reusable
`finiteDimensional_range_of_factorization` and
`RealInterleaving.finiteDimensional_range_structureMap` expose the linear and
interleaving steps. Vertex and coefficient universes are independent; the
auxiliary vertex order may be chosen arbitrarily.
`Rips.sublevelModuleIsoOfIsometryEquiv` compares the modules under any
isometric relabelling, using the graph relation and its zero-interleaving,
without requiring order preservation or finiteness.

At time zero a genuine metric admits only singleton faces, so an infinite
vertex type gives infinite-dimensional unreduced H₀.
`Rips.not_finiteDimensional_zero_homology` proves this fact.
`RipsQTameExamples` applies both results to the infinite compact interval
[0,1] ⊆ ℝ. It witnesses finite-dimensional images across every strict gap
and an infinite-dimensional fiber at zero in the same example.

The finite-net argument formalizes the Rips part of CDSO13-v3 Proposition 5.1
through Lemma 4.3. The library retains closed thresholds and its empty negative
tail. The finite-net argument supplies q-tameness; the next construction
consumes that fact to obtain actual decorated diagram counts.


## Decorated diagrams of infinite Rips spaces

For every totally bounded X, field k and homological degree n,
`Rips.qTameDiagramMultiplicity` specializes the q-tame module's canonical
finite-death and essential multiplicities to the existing closed-diameter Rips
homology. The construction takes no finite sample or finite-dimensional fiber.
For each separated finite rectangle, the sum of positive decorated
multiplicities equals the Rips module's image-and-kernel quotient dimension.
On a birth strip at death infinity, it equals the stabilized essential quotient
count. On each separated tail rectangle, including finite deaths surviving the
tail threshold and the infinite-death boundary, it equals the actual finite-target
image quotient dimension. The tail has finite positive support; the full diagram
has countable positive support.

`RipsQTameDiagramExamples.unitInterval_infinite_fiber_with_diagram` combines
these conclusions for the compact interval [0,1] with its infinite-dimensional
unreduced H₀ fiber at time zero. This tests the intended q-tame infinite-space
case rather than a finite-only barcode. The result uses the finite-net
factorization of Chazal–de Silva–Oudot, Proposition 5.1, and the integer-content
extraction of Chazal–de Silva–Glisse–Oudot, Theorem 2.8 and §2.6, under the
library's closed-threshold and empty-negative-tail conventions.

For finite metric spaces, `Rips.qTameDiagramMultiplicity_eq_diagramOccurrenceCount`
identifies each canonical q-tame multiplicity with the occurrence count in the
existing finite Rips diagram. A finite occurrence `(b,d)` maps to
`(minusCut b, minusCut d)`; an essential occurrence `(b,⊤)` maps to
`(minusCut b, infinityCut)`. Thus the existing finite barcode's half-open
endpoint decorations and essential bars are preserved. The Lean theorem uses
`k : Type u` when the vertex type is `X : Type u`, matching the universe
restriction of the current rank-to-diagram API; no q-tameness or finite-fiber
assumption is passed by the caller. The mathematical compatibility statement
holds over every coefficient field.

`LocallyFiniteDiagramBottleneck` builds the canonical decorated occurrence
diagram of any q-tame real module directly from its persistence-measure
multiplicity. It retains countable support, finite separated rectangles and
finite tail rectangles, and defines an extended bottleneck matching-cost
infimum on finite and essential occurrence tokens. Decorations remain part of
the multiplicity; the cost forgets them only through their real endpoints.

For the existing full finite `Diagram ℝ` type, `Diagram.toLocallyFinite` takes
an explicit `Diagram.IsPositive` proof and preserves point multiplicities.
`bottleneck_toLocallyFinite` proves an isometry for positive finite diagrams.
Positivity is required because the legacy `Diagram` type also permits reverse
bars, while q-tame finite-death multiplicity is supported only on the positive
half of the decorated endpoint plane. For finite metric spaces,
`Rips.qTameLocallyFiniteDiagram_bottleneck_eq_finite` combines this result with
`Rips.qTameDiagramMultiplicity_eq_diagramOccurrenceCount`; the generic endpoint
map is definitionally the existing Rips occurrence map, including the true
`infinityCut` for essential deaths.

The finite results above are joined by a global compactness theorem. For
the finite-birth diagrams extracted from arbitrary q-tame modules,
`qTame_bottleneck_le_of_realInterleaving` bounds the bottleneck distance by the
parameter of each actual interleaving; its proof builds one global occurrence
matching with cost at most that parameter.
It uses finite saturation on each finite set of required vertices and a
coherent section of the resulting finite inverse system; no decomposition or
global-matching hypothesis is assumed. The generic diagram representation does
not include birth-at-minus-infinity strata.

For those finite-birth diagrams, `RealInterleaving.exists_finite_saturating_matching`
proves finite saturation from an actual interleaving: given finite prescribed
sets of finite bars longer than `2ε` and essential occurrences on each side, it
constructs finite injective edge sets that cover those tokens with pair costs at
most `ε`. The proof uses local finite-window counts and a coefficient-one
continuation argument, and does not assume a matching or interval decomposition.
As a metric consumer, `Rips.qTameLocallyFiniteDiagram_bottleneck_le_of_hausdorff_lt`
combines global algebraic stability with the existing actual Rips Hausdorff
interleaving for totally bounded spaces embedded isometrically in a common
ambient space. Under strict slack `2 * hausdorffDist < ε`, it bounds the
bottleneck distance of the complete locally finite q-tame diagrams by `ε`.
The Rips modules vanish at negative times, so their finite-birth diagrams have
no omitted birth-at-minus-infinity occurrences.

## Exact metric stability for the q-tame diagrams

If `X` and `Y` are nonempty totally bounded metric spaces with isometric
embeddings `f : X → Z` and `g : Y → Z` into a common metric space, then

`bottleneck(D_X, D_Y) ≤ ENNReal.ofReal (2 * hausdorffDist (range f) (range g))`.

Here `D_X` and `D_Y` include every finite-death and essential occurrence of the
q-tame Rips homology modules. The image sets need not be closed and no nearest
point is assumed to exist. The proof first uses each positive slack above twice
the Hausdorff distance in the strict interleaving theorem, then takes the
infimum of the slack in `ℝ≥0∞`. Total boundedness makes the real Hausdorff
distance finite. The vertex types `X` and `Y` currently share a Lean universe,
as required by the Rips relation-interleaving construction; the coefficient
field and ambient space may use independent universes. The public theorem
requires an auxiliary linear order on each vertex type, but the diagram itself
is order-independent: a module isomorphism preserves both separated-rectangle
and essential birth-strip contents, hence their actual multiplicities.

For nonempty compact metric spaces, mathlib's optimal compact Gromov–Hausdorff
coupling specializes the ambient theorem to
`bottleneck(D_X,D_Y) ≤ ENNReal.ofReal (2 * ghDist X Y)`. The isometries in the
optimal coupling need not preserve either auxiliary order. On finite spaces,
the exact compatibility theorem identifies these complete diagrams with the
existing full finite Rips diagrams.

There is also a convergence statement with varying finite sample types and
cardinalities. If nonempty finite Rips spaces embed isometrically in one ambient
space and their Hausdorff distances to a fixed nonempty totally bounded target
tend to zero, then the bottleneck distances of their q-tame diagrams to the
target diagram tend to zero. The target need not be finite or compact. The
checked fixture `RipsQTameInfiniteMetricStabilityExamples` uses increasing
initial samples of the genuinely infinite compact space
`{0} ∪ {1/(n+1) : n ∈ ℕ}`.

These Rips consumers use finite-net q-tameness and algebraic stability for
q-tame modules. They do not claim a theorem for arbitrary q-tame modules with
birth-at-minus-infinity strata, which are outside the current locally finite
diagram representation.
