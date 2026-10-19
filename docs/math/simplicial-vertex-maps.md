# Signed maps of actual simplicial chains

A simplicial vertex map can identify vertices and change their order. Its image
on an n-dimensional chain therefore uses both degeneracy and orientation:
a repeated image vertex makes the chain zero in degree n; an injective image
contributes the image face with the sign of its sorting permutation.

`vertexChainMap` implements this formula on the existing `Chain K R n` for an
arbitrary ring R. It assumes neither a finite vertex type nor an order-preserving
or injective map. Source and target have independent fixed vertex orders and
share a universe for the chain-complex packaging. Faces remain the actual
nonempty faces of `PreAbstractSimplicialComplex`; absent ambient singletons are
not added.

The underlying `orientedTuple` is zero for repeated tuples or absent faces.
Its boundary identity requires the tuple's image to be a present face. Without
that hypothesis an absent triangle could have three present boundary edges.
The repeated-vertex cancellation theorem itself needs no face-membership
hypothesis. It sorts the tuple, finds adjacent equal entries, cancels the two
corresponding deletion terms, and shows that every other deletion still repeats
a vertex. Reordering a deletion sum changes it by the permutation sign, so this
argument applies to arbitrary tuples. It never divides by two and therefore
works in rings with torsion as well.

`boundary_vertexChainMap` derives boundary commutation from this tuple identity.
`simplicialChainMap` packages the resulting actual chain map. Identity and
composition hold as equalities, including when a second map creates a repeated
image vertex. Identity vertex functions between subcomplexes give exactly the
existing chain inclusions.

`simplicialHomologyMap` applies mathlib's homology map to this constructed chain
map. It acts on the existing `simplicialHomology`, with identity, composition and
inclusion compatibility. `simplicialHomologyClass` is the usual projection of an
actual cycle, and its quotient comparison identifies its representative in the
existing kernel/image quotient. The class naturality theorem relates the
induced homology map to the actual chain image.

## Contiguity and the signed prism

Two vertex maps `f, g : VertexMap K L` are contiguous when
`f(s) ∪ g(s)` is a target face for every source face `s`. For an increasing
source face `[v₀, …, vₙ]`, the positive prism is

```text
Pₙ([v₀, …, vₙ]) = Σᵢ (-1)ⁱ [f(v₀), …, f(vᵢ), g(vᵢ), …, g(vₙ)].
```

Each bracket is the existing `orientedTuple`: it sorts the tuple with its sign
and vanishes when vertices repeat. Every mixed tuple has a nonempty image
contained in `f(s) ∪ g(s)`, so downward closure supplies its actual face
membership before the tuple boundary identity is used. Coefficients act on the
left, outside this signed sum; this also applies to noncommutative rings.

`Contiguous.prismMap` extends this formula linearly. Its boundary equations are
`∂P₀ = g₀ - f₀` and `∂Pₙ₊₁ + Pₙ∂ = gₙ₊₁ - fₙ₊₁`. In positive degrees,
the faces obtained by deleting a source vertex cancel the corresponding prism
faces. Adjacent mixed faces cancel in pairs, leaving the two endpoint maps.
Degree zero uses the unaugmented boundary convention separately.

`Contiguous.chainHomotopy` packages an actual mathlib homotopy from
`simplicialChainMap R f` to `simplicialChainMap R g`. Its degree-raising
component is `-Pₙ`, as required by mathlib's sign convention, and all other
components are zero. `Contiguous.simplicialHomologyMap_eq` then proves equality
of the induced maps on the existing homology in every natural degree. These
results retain the arbitrary ring and vertex-map assumptions above.

The examples distinguish the endpoint chain maps of an edge while proving
their common nonzero image on actual H₀. They also check an integer reversal
with a nonzero coefficient `-2`, its characteristic-two specialization, a
nonzero mixed triangle prism, collapsed tuples, disconnected endpoints with
distinct H₀ maps, absent ambient vertices, empty sources, and a noncentral
matrix coefficient.

## Shifted functions and canonical multivalued maps

For real-indexed filtrations F and G, a global function is ε-simplicial when it sends
every actual face at t to a face at t + ε. The geometric predicates in
`Filtration.ShiftedSimplicialMap` allow independent vertex universes and arbitrary real ε.
The actual signed homology construction retains the common vertex universe and independent
vertex orders described above.

A multivalued map is a native set relation C ⊆ X × Y, total on all ambient source
vertices. Its face condition requires every nonempty finite subset of C(σ) to be a face
of G(t + ε) whenever σ is a face of F(t). Relational images may be infinite. Totality
includes unsupported vertices, while the face condition tests actual faces only.

`shiftedSimplicialHomologyMap` gives a natural transformation whose components are the
existing actual homology maps of the global function. Both composites in its naturality
square have the same underlying vertex function, so strict composition and inclusion
compatibility prove the square. The target is reindexed by t ↦ t + ε; negative ε are
allowed for appropriately related filtrations. At nonnegative ε this target agrees with
`RealShift.shift`, and the zero-shift identity agrees with the existing zero identification.

`multivaluedSimplicialHomologyMap` chooses one global subordinate function and proves that
the resulting whole transformation equals the map of every subordinate function. For any
two such functions, the union of their finite images of σ is a nonempty finite subset of
C(σ). The face condition therefore proves actual contiguity, and the signed homotopy
proves equality on homology in every natural degree over any ring. A function graph gives
exactly the ordinary function's map. Parameterwise choices subordinate to one fixed valid
relation also give these canonical components; individual simplicial stage maps without
that common relation need not form a natural transformation.

To compare with the source's empty-subset convention, adjoin only the empty simplex to
each face collection. The relation image of the empty set is empty, so this adds no
condition to the nonempty finite-face tests. It changes none of the ordinary chain groups,
which use n + 1 vertices in degree n ≥ 0. Adding every ambient singleton would change
support and is a different construction. The empty ambient source and target require no
target inhabitation instance; a nonempty ambient source admits no total relation to an
empty target, even when its filtration has no faces.

The examples check shifted endpoint selectors with different chain maps and a common
nonzero H₀ image, negative shifts, a changing filtration in which an edge kills a nonzero
H₀ difference, infinite relational images, and disconnected-target selectors with distinct
H₀ maps. Ghost vertices, empty ambient types, a noncentral matrix coefficient and the
trivial ring test the construction's support and coefficient boundaries.

## Composition of shifted relations

For C from F to G of degree ε and D from G to H of degree δ, native `C.comp D`
means first C, then D. Its degree is ε + δ. To prove the face condition, take a
nonempty finite subset τ of the composite image of σ. Choose one intermediate
vertex for each member of τ and take their finite image ρ. Then ρ is a face at
t + ε and τ is a face at (t + ε) + δ. This proof uses neither finiteness of C(σ)
nor a default intermediate vertex; the choices range only over the members of τ.
Ambient totality composes separately, including ghosts.

`multivaluedSimplicialHomologyMap_comp` states that the actual whole canonical
transformations satisfy

`Φ_C ≫ reindexNatTrans(tr ε) Φ_D ≫ comparison.hom = Φ_(C.comp D)`,

where tr ε sends t to t + ε. The specialized comparison is
`shiftedSimplicialHomologyCompIso`; its component is exactly the actual
homology module's map along `(t + ε) + δ = t + (ε + δ)`. Composing global
subordinate functions and using selector independence proves this equation.
The ordinary function maps obey the same equation. Both degrees may be negative;
for nonnegative degrees the comparison is the existing `RealShift.compIso`.

The composition fixtures use nonzero classes through successively born point,
edge and triangle complexes, mixed-sign degrees with a failing degree-zero
control, and an infinite intermediate image followed by parity. Signed reversal
and collapse, ambient ghosts, empty types, both unit sides, a noncentral matrix
coefficient and the trivial ring test the actual maps and their stated domains.

## Canonical relation interleavings

A total subrelation C′ ⊆ C has the same actual canonical shifted homology
transformation as C. The geometric finite-face condition restricts along the
inclusion; one global selector for C′ is also subordinate to C, so selector
independence proves equality of the whole transformations. This holds at every
real degree, including negative degrees between appropriately related filtrations.

For a nonnegative ε, let C go from F to G and D from G to F, both total and
ε-simplicial. If the native composites C.comp D and D.comp C contain their
respective identity relations, `multivaluedSimplicialHomologyInterleaving`
constructs an actual `RealInterleaving ε`. Its two fields are exactly the existing
canonical maps. Composition identifies each round trip with the map of its
composite relation; subrelation invariance identifies that map with the identity
relation at degree 2ε. That identity map is the actual inclusion-induced transition,
which proves both double-shift triangles with `RealShift.compIso`.

A relation and its native converse satisfy both diagonal containments when both
are ambient-total. `multivaluedSimplicialHomologyConverseInterleaving` specializes
the construction to this case. Ghost vertices still participate in totality, while
face tests retain the actual support. No finiteness or nontriviality of coefficients
is required. Interleaving parameters remain finite nonnegative reals.

Fixtures evaluate both nonzero maps and triangles for a shifted point and edge,
negative-degree subrelations, an infinite relational image and its actual zero-shift
isomorphism, ghost-sensitive and empty inputs, and noncentral matrix coefficients.
A collapse from two isolated vertices followed by an endpoint choice has a different
actual H₀ round trip from the transition; individually simplicial total maps do not
supply the missing diagonal containment.

## Sources and scope

This is a source-motivated library bridge, proved for the library's actual
support-aware chains. Chazal–de Silva–Oudot,
[*Persistence stability for geometric complexes*, arXiv:1207.3885v3, §3](https://arxiv.org/html/1207.3885v3#S3),
uses simplicial maps and their induced homology maps in Definition 3.1 and
Proposition 3.3. The prism proves the contiguity step used there. The shifted construction realizes
Proposition 3.3's global-selector and naturality mechanism on these actual chains.
Composition implements Proposition 3.5's finite-face and composed-selector mechanism,
with the addition transport displayed explicitly. Total-subrelation invariance follows
Proposition 3.4's shared-selector proof. The native converse interleaving realizes
§4.1 Proposition 4.2's diagonal-containment deduction; the general two-relation
constructor is a supporting library extension.
Its arbitrary-ring statement specializes to the source's fixed field; the coefficient
generalization and explicit nonempty-face convention are supporting library extensions. The Munkres proofs cited by that article were not
directly audited.

The algebraic ingredients are the pinned mathlib tuple-sorting, permutation-sign,
Finsupp and homology APIs. TauCeti's
[ordered chain complex at revision 7b0d106](https://github.com/TauCetiProject/TauCeti/blob/7b0d106bf79dbea38ba8819985bd029989181287/TauCeti/AlgebraicTopology/SimplicialComplex/ChainComplex.lean)
also gives Ring-valued ordered chains and boundary square-zero. Its inspected
Maps and OrderedMap modules do not provide this arbitrary signed chain action;
the latter's cell-image and increasing-enumeration results require local
injectivity or order conditions. That source uses a different toolchain and is
not an installed dependency or copied implementation.

The finite-partition cancellation proof adapts the pinned mathlib
[`SimplicialObject/ChainHomotopy.lean`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/AlgebraicTopology/SimplicialObject/ChainHomotopy.lean).
The new module preserves Fabian Odermatt's copyright and Apache-2.0 notice and
identifies the adaptation. Mixed-tuple identities and actual face membership
connect that cancellation to this chain model; mathlib's homotopy theorem
supplies equality of the actual homology maps.

The [Rips relation consumer](rips-metric-stability.md) derives the geometric hypotheses
from an explicit pairwise distortion bound. Mapper refinement consumers, varying
vertex-type persistence modules and Hausdorff or Gromov–Hausdorff selection remain separate.
