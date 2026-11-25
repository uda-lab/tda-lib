# Closed α filtrations and signed planar coverage

## Closed cells and squared entrance grades

Let `sites : V ↪ E` embed a label type into a normed additive commutative
group. The closed Voronoi cell of `v` consists of the points at least as close
to `sites v` as to every other site. At real squared grade $t$, `Alpha.complex`
takes the nerve of these cells restricted by the closed inequalities
$\operatorname{dist}(x, \mathrm{sites}(v))^2 \le t$. Thus a face is a nonempty
finite set of labels with one witness satisfying the restrictions for every
label in the face. For $t \ge 0$, the restrictions are closed balls of radius
$\sqrt t$. The complex is empty below zero and each singleton enters at zero.
[Alpha.lean](../../TDA/Filtration/Alpha.lean)

The all-scales carrier is the nerve of the unrestricted closed cells. Its faces
are exactly those that occur at some finite grade. In a finite-dimensional
real inner-product space, `Alpha.filter` assigns each carrier face its attained
least entrance grade. For any vertex of that face, `isLeast_sq_dist` identifies
the grade with the minimum squared distance to that vertex over the common
cells. The sublevels of the filter are the closed stages, including equality
at entry. With finite labels, a single finite grade suffices for the carrier.
[Alpha.lean](../../TDA/Filtration/Alpha.lean)

`Alpha.labelledComplex` allows an arbitrary site function, including distinct
labels at coincident sites. It agrees with the embedding version on embedded
sites. A common witness retains all labels attaining the same nearest distance.
For the side-2 square the center $(1,1)$ witnesses all four labels at squared
grade $2$, or radius $\sqrt{2}$. The full closed nerve therefore includes a
four-label face. A supplied triangle split of that square generates faces of at
most three labels. The same nearest-site condition determines which cocircular
sets actually contribute a face.
[AlphaLabelled.lean](../../TDA/Filtration/AlphaLabelled.lean) ·
[Square grade table](../../TDA/Filtration/RationalAlphaExamples.lean) ·
[Square stage fixture](../../TDA/Filtration/RationalAlpha/SuppliedStagesExamples.lean)

## Degree-zero comparison with Čech

The library exposes two ambient Čech reindexings on the squared-grade line.
For $t \ge 0$ both use the closed ambient Čech complex at radius $\sqrt t$.
For $t < 0$, `Alpha.squaredCechFiltration` uses a negative radius and has empty
stages, as does labelled α. The reindexing along `Alpha.radius` uses radius
zero below grade zero and contains every singleton label there. On an empty
label type both targets are empty. `Alpha.filtration_le_cech` and
`Alpha.inclusion_natural` use the square-root reindexing. The Euclidean
`isIso_alpha_filtration_le_cech` uses that inclusion at nonnegative grades.
The all-real comparisons `alphaH0Iso` and `alphaCechIso` use
`Alpha.squaredCechFiltration`.
[Alpha.lean](../../TDA/Filtration/Alpha.lean) ·
[AlphaLabelled.lean](../../TDA/Filtration/AlphaLabelled.lean) ·
[AlphaCech.lean](../../TDA/Persistence/AlphaCech.lean) ·
[Grade-4 example](../../TDA/Persistence/AlphaCechExamples.lean)

For a finite linearly ordered label type, a site function into a real normed
vector space, and a coefficient field, `alphaH0Iso` identifies ordinary
degree-zero α and Čech persistence at every real squared grade. Its forward map
is `alphaH0Comparison`, induced at each grade by the actual inclusion on the
same labels. Below zero both complexes are empty. At a nonnegative grade,
`Alpha.cech_edge_reachable` replaces each Čech edge by a path of α edges at that
grade, using finiteness and decidable equality of labels. The abstract
`simplicialHomologyIncl_zero_isIso_of_edge_reachable` uses linearly ordered
labels, a field, an inclusion with every source singleton, and a source path
between the endpoints of each target edge;
`simplicialHomologyIncl_zero_isIso_of_edge_reachable_of_ring` states it over any ring. Signed boundaries telescope along
such paths. These are library arguments. For a finite linearly ordered label
type and sites in a finite-dimensional real inner-product space, the separate
`alphaCechIso` gives the comparison over a ring in every degree and specializes
to `alphaH0Iso` in degree zero over a field.
[AlphaH0.lean](../../TDA/Persistence/AlphaH0.lean) ·
[H0EdgePaths.lean](../../TDA/Simplicial/H0EdgePaths.lean) ·
[AlphaCech.lean](../../TDA/Persistence/AlphaCech.lean)

## Exact grades on rational planar sites

For a finite embedding `p : Fin n ↪ ℚ × ℚ`, the rational reference enumerates
sites, pair midpoints, and circumcenters of noncollinear triples. Squared
Euclidean distances are rational on rational points. The bisector equations are
linear, and `circumcenter?` solves them when their two normals have nonzero
determinant. A candidate record contains the center, its least squared
distance to the sites, and the full set of nearest labels. `entry?` chooses a
least-grade record whose nearest labels contain the nonempty face.
[Candidates.lean](../../TDA/Filtration/RationalAlpha/Candidates.lean)

`minimizer_mem_centers` shows that every minimizer of squared distance to a
selected face vertex over its common cells is the cast of an enumerated
candidate. `entry_witness`, `exists_entry_iff`, and `cast_grade` identify the
returned witness, the feasible carrier, and the actual attained value.
`gradedFaces` has one rational squared entrance grade per feasible nonempty
labelled face. After a permutation of the sites, transport each face by the
corresponding label bijection. Its common-witness condition and numerical
minimum are identical, by the geometric characterization of the grade.
`RationalAlpha.sublevel_eq_complex` identifies the stages at all real cutoffs.
[Geometry.lean](../../TDA/Filtration/RationalAlpha/Geometry.lean) ·
[RationalAlpha.lean](../../TDA/Filtration/RationalAlpha.lean)

Ordinary radii also give a direct displacement bound. Moving each matched site
by at most $\varepsilon$ increases the Čech witness radius by at most $\varepsilon$
by the triangle inequality. The radius-indexed α diagram bound uses this
Čech estimate after identifying the persistence modules. For the squares with
corners at $(\pm 7,\pm 7)$ and $(\pm 8,\pm 8)$, the degree-one bottleneck over
$\mathbb F_2$ is $\sqrt{2}$ on radii and $30$ on squared grades. The rational
F₂ barcode wrapper uses the squared grade table through the existing finite
reducer.
[Čech displacement](cech-displacement-stability.md) ·
[AlphaRadiusStability.lean](../../TDA/Persistence/AlphaRadiusStability.lean) ·
[Square bottlenecks](../../TDA/Persistence/AlphaRadiusStabilityExamples.lean) ·
[Exact planar α barcodes](finite-ph-computation.md#exact-planar-α-barcodes)

## Signed coverage of a certified planar hull

The rational determinant `orient a b c` is signed doubled area. It vanishes
exactly when the three cast points are collinear, including repeated points.
The unit-normal area formula uses a nonzero base. For a noncollinear triple,
the sign of `orient a b c * incircle a b c d` gives the open circumdisk
(positive) and its strict exterior (negative). Incircle zero gives the
circumcircle. For a counterclockwise triple these are also the signs of raw
`incircle`. The noncollinear comparison identifies the computed rational
center with the real simplex circumcenter. The finite all-site CCW check
accepts exactly when every incircle value is nonpositive, including ties on
the circle.
[Predicates.lean](../../TDA/Filtration/RationalAlpha/Predicates.lean) ·
[IncircleGrade.lean](../../TDA/Filtration/RationalAlpha/IncircleGrade.lean)

A `PolygonCertificate` for the real hull supplies compactness, convexity,
nonempty ambient interior, and equality of the frontier with the union of the
listed closed sides. Each oriented side has the hull on its closed left.
For each ordered pair of distinct side indices, at least one endpoint of the
first is strictly left of the second. A collinear subdivision of a side puts
both endpoints of one listed edge on the line of another and violates this
condition.
`hull_polygonCertificate_hullOnly` supplies the same certificate given
noncollinearity for triples of distinct hull positions and the real interior,
frontier and left-support hypotheses.
[SignedBoundaryCoverage.lean](../../TDA/Filtration/RationalAlpha/SignedBoundaryCoverage.lean)

For rational sites, use a supplied strict coarse corner cycle.
[`StrictCornerCycle` and `HullSitesLeft`](../../TDA/Filtration/RationalAlpha/SignedBoundaryCoverage.lean)
require, respectively, every nonincident corner to lie strictly left of each
directed side and every site to lie weakly left of each side.
[`cornerHullCheck`](../../TDA/Filtration/RationalAlpha/SignedBoundaryCoverage.lean)
checks both conditions by exact rational orientation, and
[`cornerHullCheck_true_iff`](../../TDA/Filtration/RationalAlpha/SignedBoundaryCoverage.lean)
identifies the weak test with all-site containment. The
[`cornerHullCheck_sound`](../../TDA/Filtration/RationalAlpha/SignedBoundaryCoverage.lean)
theorem supplies the strict coarse `PolygonCertificate` and identifies its
corner hull with the convex hull of all sites. A site in the relative interior
of a straight side remains a site in this route. A cycle that lists it as a
corner cannot itself carry a `PolygonCertificate`: the two distinct side
occurrences on that support line cannot satisfy
[`PolygonCertificate.strict_endpoint`](../../TDA/Filtration/RationalAlpha/SignedBoundaryCoverage.lean).
The fixtures record the behaviour of the checker.
[`midpoint_accepted`](../../TDA/Filtration/RationalAlpha/HullCertificateExamples.lean)
shows that `cornerHullCheck` accepts the strict coarse cycle with the midpoint
of a side among the sites.
[`subdivided_cycle_rejected`](../../TDA/Filtration/RationalAlpha/HullCertificateExamples.lean)
shows that the cycle listing that midpoint as a corner satisfies
`HullSitesLeft`, fails `StrictCornerCycle` and is rejected by
`cornerHullCheck`.

[`rational_cover_from_subdivided_signed_boundary`](../../TDA/Filtration/RationalAlpha/SubdividedBoundaryCoverage.lean)
uses that strict certificate for the coarse cycle while comparing the triangle
chain with its ordered, labelled refinements. It separately requires
`OrderedEdgeCuts` on each coarse side, containment of every triangle vertex in
the coarse hull, strict counterclockwise orientation of each ordered triangle,
and equality of the summed triangle signed-edge chain with the chain of the
refined labelled boundary. It proves closed coverage and off-edge multiplicity
for the triangles; its coverage conclusion makes no assertion of a weak-corner
`PolygonCertificate` for the subdivided cycle.
[`coverage_and_multiplicity`](../../TDA/Filtration/RationalAlpha/SubdividedBoundaryExamples.lean)
exhibits the side split through an ordered cut and the refined-chain equality.

`rational_cover_from_signed_boundary` takes the following data and hypotheses.

- An injective rational site map from a label type and an injective hull cycle
  indexed by `Fin (k + 3)`. The real hull is the convex hull of its cast vertices.
- A polygon certificate for that hull and its directed cyclic sides, with every
  cast site in the hull.
- A finite index type for the supplied triangles with a `Fintype` instance,
  a triple of labels for each index, and strict counterclockwise orientation of
  each triple in its given order.
- Equality of the sum of the signed integer edge chains of the triangles with
  the signed chain of the directed hull cycle.

Off every listed triangle and hull segment, the number of triangle interiors
containing the point equals the indicator of the hull interior. The union of
the closed triangle carriers equals the closed hull. These conclusions use
finiteness of the triangle and hull indices. The generic label type is
arbitrary. The signed interior-disjointness corollary uses the off-edge
multiplicity bound, and the pairwise intersection theorem adds global
noncollinearity of distinct site triples for its shared-face conclusion.
`allSitesUsed` describes occurrence of each label in a triangle. The
omitted-label fixture has closed coverage with an unused interior label.
The three-triangle fan uses every label and obtains its hull certificate from
positive orientation of the outer triangle. At the concrete off-edge point
$(2,1/2)$ its multiplicity is one by the signed-boundary theorem.
[Coverage and certificates](../../TDA/Filtration/RationalAlpha/SignedBoundaryCoverage.lean) ·
[Incidence](../../TDA/Filtration/RationalAlpha/TriangleIncidence.lean) ·
[Coverage fixtures](../../TDA/Filtration/RationalAlpha/SignedBoundaryExamples.lean)

## Supplied carrier and stages

`SuppliedCarrier.alphaCarrier_le_labelComplex_of_signed_boundary` uses the
closed-cover conclusion of `rational_cover_from_signed_boundary`. At the
barycenter of a nonempty actual α face, the closed cover supplies a triangle.
The affine functions from the two common-cell witnesses bound the squared
norm of each site from below. At the barycenter the functions agree, and the
positive weights of the face labels put each of those sites on the triangle's
circle. The triangle's barycentric weights may vanish. The contact condition
then places the face within that supplied triangle.

The reverse inclusion from actual α to the supplied complex takes a finite
rational site embedding, the signed coverage hypotheses, passing all-site
incircle checks for the given CCW triangles, and either the absence of a real circle through four distinct sites or
nonvanishing incircle determinants for every four distinct labels. Inclusion from the supplied complex into the actual carrier
uses the rational site embedding, CCW orientation and passing incircle checks,
allowing ties. Combining the directions identifies the actual carrier with
the nonempty labelled downward closure of the supplied triangles. The equality
also implies use of every label. The polygon cycle needs at least three sites.
[SuppliedCarrier.lean](../../TDA/Filtration/RationalAlpha/SuppliedCarrier.lean) ·
[No-four conditions](../../TDA/Filtration/RationalAlpha/SuppliedEdgeGrade.lean)

For supplied triangles `tri : Fin m → Fin 3 → Fin n`, the same certificate
hypotheses give `suppliedGrades_eq_reference`, which identifies the finite
rational row sets. `supplied_realStage_iff` identifies
the faces of the closed cutoff on those rows with actual α at every real
squared grade. For a rational cutoff, `realStageTable_cast` gives the
executable rational `stageTable`. This interface consumes supplied triangles
and their stated certificate. The exact reference table applies to finite
distinct rational sites, including degenerate configurations.
[SuppliedGradeEnumeration.lean](../../TDA/Filtration/RationalAlpha/SuppliedGradeEnumeration.lean) ·
[SuppliedStages.lean](../../TDA/Filtration/RationalAlpha/SuppliedStages.lean)

`carrier_eq_of_signed_boundary`, `suppliedGrades_eq_reference` and
`supplied_realStage_iff` compare the triangle chain with the chain of the hull
cycle itself, so every hull side is an edge of a supplied triangle
(`certified_hull_pair_face`). A site in the relative interior of a hull side
is treated by `rational_cover_from_subdivided_signed_boundary`, for coverage
and off-edge multiplicity, and is outside these three theorems: it lies in the
open circumdisk of the supplied triangle on that side, so the incircle test of
that triangle fails. The three theorems do not assume noncollinearity of site
triples; that hypothesis belongs to the pairwise-intersection, frontier and
non-hull-edge statements and to the assembly `certifiedComplex`.
[TriangulationAssembly.lean](../../TDA/Filtration/RationalAlpha/TriangulationAssembly.lean) ·
[SubdividedBoundaryCoverage.lean](../../TDA/Filtration/RationalAlpha/SubdividedBoundaryCoverage.lean)

## Source correspondence

The rational grading, degree-zero comparison, planar predicate proofs, signed
coverage and supplied applications above are library derivations. The geometric
α definition and least-grade results of [Alpha.lean](../../TDA/Filtration/Alpha.lean)
are stated in their own terms, and no numbered result of a source is attributed to
them. Bauer–Edelsbrunner is background: its
[source register entry](references.md#BE-1312.1231) records the comparison with its
arXiv v3 that the review of #1077 reported, with an unverified basis for that
automated processing, separately from the collapse work, which did not consult it.
The Edelsbrunner–Ölsböck PDF inspected in the same review is recorded as background
in [its entry](references.md#EO-2018-J-06).

The all-degree comparison `alphaCechIso`, its compact-convex input
`ConvexNerve.isIso_simplicialHomologyIncl_of_compact` and the radius stability
theorem `bottleneck_alphaRadiusDiagram_le_displacement` are library derivations
as well. At each nonnegative squared grade the restricted balls and the closed
balls are compact convex families on the same labels with equal unions.
`exists_pos_common_convex_thickening` gives one small open thickening that
preserves both labelled nerves, and the nerve-inclusion theorem for open convex
families with equal unions, `ConvexNerve.isIso_simplicialHomologyIncl`, applies
to the thickenings. The stability theorem reindexes `alphaCechIso` by the squared
radius and transports the existing Čech displacement bound along it. The Topology
modules behind these results, from the nerve thickening to the convex nerve
inclusion, are library derivations attributed to no source. The work cited as
BKRR in #1118 is recorded as prior work, with its version and comparison mode
unknown, in [its register entry](references.md#BKRR-2203.03571).
[AlphaCech.lean](../../TDA/Persistence/AlphaCech.lean) ·
[AlphaRadiusStability.lean](../../TDA/Persistence/AlphaRadiusStability.lean) ·
[ConvexNerveInclusion.lean](../../TDA/Topology/ConvexNerveInclusion.lean) ·
[NerveThickening.lean](../../TDA/Topology/NerveThickening.lean)
