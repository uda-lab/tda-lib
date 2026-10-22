# Finite simplicial coordinates on ordinary homology

The quotient in `coordinateHomology K R n` has **coordinate cycles** as its ambient
module and `coordinateBoundaries K R n` as its submodule. These are the cycle and incoming-boundary modules transported through finite face coordinates
by [the finite-cycle bridge](simplicial-finite-cycles.md). It is not a quotient
of all coordinate chains. In degree zero the outgoing differential is zero,
but the incoming edge boundary can identify vertex classes.

`quotientCoordinates` applies mathlib's canonical `Submodule.Quotient.equiv`
to `cycleCoordinates`. Its essential hypothesis is the existing equality
`simplicialBoundaries_map_cycleCoordinates`: the boundary submodule,
**inside cycles**, maps exactly onto the coordinate boundary submodule,
**inside coordinate cycles**. The private elaboration helper supplies those
same explicit arguments to `Submodule.Quotient.equiv`; it selects no new
quotient relation. Local `HasQuotient` witnesses use `Submodule.hasQuotient` for
both named cycle modules. The public type is a transparent abbreviation, so
its additive and module structures are the canonical quotient structures.

The representative equation `quotientCoordinates_mkQ` sends the class
`[z]` to `[cycleCoordinates z]`. The equivalence
`simplicialHomologyCoordinates` first uses the existing
`homologyKernelQuotient` comparison from **ordinary** simplicial homology to
the cycle/boundary quotient, then `quotientCoordinates`. In
`simplicialHomologyCoordinates_mkQ`, an ordinary homology class represented by
`z` is formed by applying the inverse of that same comparison to `[z]`.
Forward/inverse cancellation gives the coordinate class `[cycleCoordinates z]`;
there is no independent choice of a homology isomorphism.

For an inclusion `h : K ≤ L` in one ordered ambient vertex type,
`coordinateHomologyIncl` is `Submodule.mapQ` of the concrete
`coordinateCycleIncl R h n`, which itself comes from the finite inclusion
matrix. Boundary preservation makes the map well-defined. Its `mkQ` law
computes on coordinate cycle representatives. `quotientCoordinates_naturality`
uses the full cycle-coordinate inclusion square on every quotient
representative. `simplicialHomologyCoordinates_naturality` then composes that
square with the already proved ordinary-homology/cycle-quotient square. The
order is coordinate inclusion after the source comparison, equal to target
comparison after `simplicialHomologyIncl`. Surjectivity of
`quotientCoordinates` and the existing quotient inclusion laws give
identity and composition for coordinate quotient inclusions.

The face fixtures check bottom homology in degrees zero and one;
normalization and a nonzero ordinary class for an isolated vertex; and the
edge boundary `[-1, 1]`, which makes its endpoint classes equal. For the
unfilled triangle, the signed edge cycle has coefficients
`[1, -1, 1]`. Its source class is nonzero because there is no incoming
triangle boundary. Under inclusion into the filled triangle, the cycle
remains nonzero as a **cycle** but becomes the boundary of the unit triangle,
so its coordinate quotient class and its ordinary homology image are zero.
The fixtures also check class-level identity and composition with an arbitrary
integer vertex coefficient, generic local finite-total-face use, and the zero
ring `ZMod 1`.

The construction is noncomputable theory over any commutative ring, including
the zero ring. It needs enumerated, decidable degree `n+1` faces and only
finite degree `n` faces for one quotient; inclusion has the local additional
face instances needed by the existing matrix map. Vertex and coefficient
universes remain independent. Finite total face sets may provide the
required degreewise instances locally. This file provides no coordinate
persistence module, packaged natural isomorphism, homology basis, finite rank,
master matrix, barcode, or executable quotient algorithm. Its naturality is
for same-ambient inclusions preserving the chosen vertex order.
