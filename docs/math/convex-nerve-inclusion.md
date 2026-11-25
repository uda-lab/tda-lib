# Nerves of nested convex families

For two families of convex sets on the same labels, one inside the other label by
label and with the same union, the inclusion of their nerves induces an isomorphism
of simplicial homology. This note states that theorem with its hypotheses, the
thickening lemma that gives its compact form, and the realization, subdivision and
mesh results used on the way. The [API guide](../api.md#realizations-subdivision-mesh-and-nerves-of-nested-convex-families)
lists the remaining declarations.

Throughout, `CoverFamily X I` is `I → Set X`, and `nerve U` is the labelled complex
on `I` whose faces are the nonempty finite sets `s` with a point in `U i` for every
`i ∈ s`. Distinct labels with equal nonempty members are distinct vertices, and a
label with an empty member is not a vertex. For `C i ⊆ D i`,
`nerve_mono h : nerve C ≤ nerve D` is the inclusion on the same labels.

## The convex nerve inclusion theorem

`ConvexNerve.isIso_simplicialHomologyIncl` (namespace `TDA.Topology.ConvexNerve`)
assumes:

- a label type `I` with `[Fintype I] [LinearOrder I]`;
- a real normed space `E` (`[NormedAddCommGroup E] [NormedSpace ℝ E]`);
- families `C D : I → Set E` with every `C i` open (`IsOpen`) and convex, and every
  `D i` convex;
- `C i ⊆ D i` for every `i`, and `⋃ i, C i = ⋃ i, D i`.

For every ring `R` (`[Ring R]`, in any universe) and every degree `k : ℕ`, it
concludes `IsIso (simplicialHomologyIncl R (nerve_mono h) k)`. The hypotheses do not
ask for openness of `D i`, nonempty members, finite dimension of `E`, or a union
equal to `E`; an empty label type is handled directly, since both nerves are then
empty.

`ConvexNerve.isIso_simplicialHomologyIncl_of_compact` has the same conclusion
for `I` with `[LinearOrder I] [Finite I]` when every `C i` and every `D i` is compact
and convex, with `C i ⊆ D i` and equal unions; openness is not assumed. It applies
the first theorem to the open `δ`-thickenings of both families for the radius `δ` of
the thickening lemma below, and rewrites the two thickened nerves back to
`nerve C` and `nerve D`.

## The thickening lemma

In a metric space `X`, `Metric.thickening ε S` is the open `ε`-neighbourhood of `S`.
For `[Finite I]` and compact members, `exists_pos_nerve_thickening_eq` gives
`δ > 0` such that `nerve (fun i => thickening ε (C i)) = nerve C` for every
`0 < ε ≤ δ`. For a nonempty set of labels without a common point, compactness of one
member and the closed thickenings of all the members give a radius at which the open
thickenings still have no common point; the minimum over the finitely many label
sets is `δ`. `exists_pos_common_nerve_thickening_eq` takes the smaller of two such
radii for two families on the same labels.

In a real normed space and for any label type, `convex_thickening_of_iUnion_eq`
assumes convex `C i` and `D i`, `C i ⊆ D i` and `⋃ i, C i = ⋃ i, D i`. At every
real `ε` it states that both families of thickenings have union
`thickening ε (⋃ i, C i)`, that `thickening ε (C i) ⊆ thickening ε (D i)`, and that
every thickened member is open and convex.

`exists_pos_common_convex_thickening` combines the two under `[Finite I]`, compact
and convex members, `C i ⊆ D i` and equal unions: one `δ > 0` such that for every
`0 < ε ≤ δ` both nerve equalities and all the properties above hold. The radius is
existential; no value or lower bound for it is given.

## Realizations and coordinate stars

For `K : PreAbstractSimplicialComplex V`, `Realization K` consists of the points of
mathlib's `StdSimplex ℝ V` whose weight support is a face of `K`, with the subspace
topology, and `Realization.incl` is the continuous inclusion for `K ≤ L`. The open
star `coordinateStar K v` is the set of points with positive weight at `v`. For any
vertex type, the stars are open (`isOpen_coordinateStar`) and cover the realization
(`covers_coordinateStar`), a nonempty finite label set has a common star point
exactly when it is a face (`interMember_nonempty_iff`), and
`nerve_coordinateStar` states `nerve (coordinateStar K) = K`. `incl` pulls stars
back to stars (`pullback_coordinateStar`), and `starNerveInclusion_naturality`
identifies the induced map of star nerves with the inclusion `K ≤ L`.

Under `[Finite V]` only: `isEmbedding_weights` embeds the realization in `V → ℝ` by
its coordinates, and for a face `J` the straight-line homotopy `contraction` joins
the identity of `StarIntersection K J` to the constant map at `faceBarycenter`,
which gives `contractibleSpace_starIntersection`. The star cover is not used in the
proof of the convex nerve inclusion theorem.

## Iterated subdivision and its mesh

For `[Fintype V]`, `SubdivisionRealization.complex K n` is the `n`-fold barycentric
subdivision of `K` on labels `Vertex V n` that depend only on `V` and `n`, and
`complex_mono` carries `K ≤ L` to every depth. For a placement `p : V → E` in a real
normed space, `realize p K n` interpolates the iterated barycenters
`vertexPosition p n` on `Realization (complex K n)` and factors through
`barycentricProjection K n` (`realize_eq_comp_projection`). Each face `F` of
`complex K n` has an original face `originalFace n F ∈ K` (`originalFace_mem`).

`faceImage K p n F` is the image of the points supported in `F`, boundary included,
and `closedStarImage K p n v` is the union of the face images of the faces that
contain `v`; it is empty for an unused label. `diam_le` assumes `M ≥ 0`, that every
face of `K` has at most `d + 1` vertices, and that the placed vertices of each face
are pairwise within distance `M`. At depth `n` it bounds the diameter of every face
image by `(d / (d + 1)) ^ n * M` and of every closed-star image by
`2 * ((d / (d + 1)) ^ n * M)`. For nonempty `A ⊆ B` with `|B| ≤ d + 1`, the two
barycenters are within `|B \ A| / |B| ≤ d / (d + 1)` times the vertex bound; convexity
extends the bound to faces, and closed stars are measured through `v`.
`eventually_diam_lt` gives, for `ε > 0`, a depth from which both diameters are below
`ε`; `diam_eq_zero_of_card_le_one` treats faces with at most one vertex.

## Proof route

The proof of `ConvexNerve.isIso_simplicialHomologyIncl` for a nonempty label type has
four steps.

1. `exists_compatibleWitnesses` chooses a point `p J` for each label set, in `C i`
   for all `i ∈ J` when `J ∈ nerve C` and in `D i` when `J ∈ nerve D`.
   `exists_compact_witness_patch` shows that the convex hulls of these points over
   the flags of `nerve D` form a compact set inside `⋃ i, D i`, using convexity of
   the `D i`.
2. This set lies in the union of the open `C i`. A Lebesgue number and
   `eventually_diam_lt` give a depth `n` and a labeling of `Vertex (Finset I) n` by
   `I` whose closed-star images lie in the labelled members
   (`exists_subordinate_closedStars`). `exists_common_labeling` turns it into one
   vertex map from the subdivided flags of `nerve D` to `nerve C` that restricts
   literally to the subdivided flags of `nerve C`.
3. `chainHomotopy_labeling_lastVertex` makes this labeling chain homotopic, on each
   side, to `flagLastVertex`, the iterated last-vertex map, through the cone carriers
   of `TDA.Topology.ConeCarrierComparison`; convexity of the `C i` and `D i` enters
   here.
4. `isIso_flagLastVertex` (from `isIso_iteratedLastVertex`) makes the last-vertex
   maps homology isomorphisms over every ring, and `flagLastVertex_naturality` makes
   them commute with the inclusions; both use the scoped orders
   `SubdivisionRealization.vertexLinearOrder`. The labeling then supplies a two-sided
   inverse of the inclusion in homology.

## Fixtures

`NerveThickeningExamples.path_and_triangle_preserved` takes `[0,1]`, `[1,2]`, `{0}`
and `[0,2]`, `[0,2]`, `{0}` on three labels. It checks equal unions, a strict nerve
inclusion, and that for small positive `ε` the thickened path family keeps edges
`{0,1}`, `{0,2}` and lacks `{1,2}` while the thickened triangle family keeps
`{0,1,2}`. `duplicate_edge_and_empty_label` checks at every positive radius that
equal members keep their edge and an empty member stays absent. In `RealizationExamples` the three stars meet
in the filled triangle but not in its boundary, whose inclusion is not surjective.
`SubdivisionMeshExamples` uses the unit-vertex placement in `Fin 3 → ℝ` with the
supremum metric. It computes the projected coordinates `(1/2, 1/2, 0)` and
`(3/4, 1/4, 0)` of a depth-one and a depth-two vertex, in the boundary and in the
filled triangle, and obtains from `diam_le` the bounds `1/2` (boundary, `d = 1`) and
`8/9` (filled triangle, `d = 2`) on the closed-star diameter of that depth-two
vertex.

`ConvexNerveInclusionExamples.strict_inclusion_isIso` applies the theorem to three
open intervals whose nerve gains the triple face. For eight open boxes around a
square hole, enlarging one box gives a strict inclusion (`Annulus.nerve_boxes_lt`)
that is an isomorphism (`Annulus.isIso_simplicialHomologyIncl`), and
`Annulus.not_isZero_homology_one` shows that degree-one homology of the box nerve over
F₂ is nonzero. `Annulus.unequal_union_not_isIso` enlarges every box to the plane:
the members stay open and convex, the unions differ, and the inclusion is not an
isomorphism in degree one over F₂.

## Scope and limits

The theorems concern simplicial homology of labelled nerves and the inclusion induced
by `C i ⊆ D i` on the same finite, linearly ordered label type. No comparison of nerve
homology with the homology of the union, no homotopy equivalence of realizations, and
no statement for different label types or other maps of covers is proved. Apart from
the one instance in `Annulus.unequal_union_not_isIso`, where the equal-union
hypothesis fails, no fixture or theorem shows that a hypothesis is needed. Thickening
radii and subdivision depths are existential, and the constructions are
noncomputable. The compact form is used by `alphaCechIso`; see the
[α note](alpha-filtration-and-signed-coverage.md#source-correspondence).

## Derivation status

The results above are stated and proved in the library's own terms. The
[source register](references.md#existing-declaration-and-proof-mappings) records
`TDA.Topology.NerveThickening`, `Realization`, `SubdivisionRealization`,
`SubdivisionMesh`, `SubdivisionLastVertex`, `NerveStarLabeling`,
`ConeCarrierComparison`, `ConvexNerveInclusion` and their fixtures as library
derivations (**extension**) attributed to no source.
[NerveThickening.lean](../../TDA/Topology/NerveThickening.lean) ·
[Realization.lean](../../TDA/Topology/Realization.lean) ·
[SubdivisionMesh.lean](../../TDA/Topology/SubdivisionMesh.lean) ·
[ConvexNerveInclusion.lean](../../TDA/Topology/ConvexNerveInclusion.lean)
