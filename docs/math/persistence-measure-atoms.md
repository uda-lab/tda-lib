# Atomic representation of integer contents on decorated cells

A cut of a linearly ordered set consists of a lower part and its complementary upper
part, with every lower point strictly below every upper point. At a real endpoint `r`,
the cuts with lower parts `(-∞,r)` and `(-∞,r]` distinguish the two boundary decorations.
For endpoints `a,b`, the cell `cutCell a b` consists of cuts having `a` in the lower part
and `b` in the upper part. A persistence rectangle uses one such cell for births and
another for deaths, with endpoints `a < b < c < d`.

`DecoratedMeasureCuts` identifies the existing `Cut` with mathlib's bundled `LowerSet`.
The latter already has a complete linear order. In its order topology, the cell image is
both the closed interval `[Iic a,Iio b]` and the open interval `(Iio a,Iic b)`. It is
therefore compact and open. The two adjacent cuts at an endpoint are retained, so this
identification preserves the decorations.

`DecoratedRectangleCells` proves that the coordinate cells and the separated rectangle
cells form set semirings: they contain the empty set, intersections stay in the family,
and every difference is a finite disjoint union of cells. Splitting at an endpoint assigns
each cut to exactly one child cell. `DecoratedRectangleTopology` proves compactness and
openness of rectangle images and that inward endpoint refinements separate distinct cut
pairs. No order or topology instance is added to the existing `Cut` type.

For a set semiring `C`, mathlib's `AddContent ℕ C` is a natural-valued set function which
is finitely additive on disjoint finite cell unions. `IntegerContentAtoms` defines
`contentMultiplicity m x` as the minimum of `m U` over cells containing `x`. The minimum
is attained whenever a containing cell exists. If cells are open and a compact cell `K`
has positive content, some point of `K` has positive multiplicity: otherwise attaining
zero-content cells give an open cover, and a finite subcover contradicts finite-cover
subadditivity.

Subtracting one point content preserves natural-valued finite additivity. Induction on
`m K` then constructs a finite multiset reproducing the content of every subcell of `K`.
If cells separate points, the minimum-cell multiplicities equal the multiset counts.
Consequently their positive support is finite in each compact cell, and the cell content
is exactly the sum of these multiplicities. The multiset belongs to a single compact
cell; the results impose no finite bound on global support or total mass.

The atomic representation is an original compactness proof of the integer-content step
underlying Chazal–de Silva–Glisse–Oudot, *The structure and stability of persistence
modules*, [arXiv:1207.3674v3, Theorem 2.8](https://arxiv.org/pdf/1207.3674v3). Their proof uses
nested rectangle subdivisions. This formalization reuses mathlib's complete lower-set
order, compactness and additive-content finite-cover inequality.

For a real-indexed persistence module over a field, `PersistenceMeasureBoxContent` applies
mathlib's `BoxAdditiveMap.ofMapSplitAdd` to the proved birth and death splitting identities
of the image-and-kernel quotient dimensions. Q-tameness gives finite crossing images in
every subbox of a strictly separated outer rectangle. This proves the count identity for
an arbitrary finite box partition, without finite-dimensional fibers.

`DecoratedRectangleBox` takes preimages along pairs of minus cuts to turn actual decorated
rectangle covers into ordinary half-open box partitions. `PersistenceMeasureContent` uses
this construction to prove every finite disjoint-union axiom of `moduleRectangleContent`.
Its rectangle values equal the module's actual quotient dimensions. Neither a finite-tiling
certificate nor a diagram decomposition is supplied as an assumption.

`PersistenceMeasureDiagram` defines `moduleDiagramMultiplicity` by minimum containing-cell
content. The positive support is finite in every separated rectangle, and the sum of the
multiplicities there equals the actual persistence-measure value. Invisible points have
multiplicity zero. `DecoratedCutEndpoints` proves that every cut in a finite cell is one of
the two principal decorations of its real supremum; positive diagram points therefore
have strictly ordered finite numeric endpoints. The interval-module fixture extracts a
point of multiplicity one from the actual module `[0,2)`.

This constructs the finite-death part of the decorated persistence diagram. The essential
boundary, compatibility with the existing finite diagram type, and algebraic stability
remain separate obligations.
