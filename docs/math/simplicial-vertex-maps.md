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

## Sources and scope

This is a source-motivated library bridge, proved for the library's actual
support-aware chains. Chazal–de Silva–Oudot,
[*Persistence stability for geometric complexes*, arXiv:1207.3885v3, §3](https://arxiv.org/html/1207.3885v3#S3),
uses simplicial maps and their induced homology maps in Definition 3.1 and
Proposition 3.3. The prism proves the unfiltered contiguity step used there,
with arbitrary rings in place of the source's field coefficients. This is a
supporting library extension; the filtered selector-independence proposition
requires its own packaging. The Munkres proofs cited by that article were not
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

Independence of filtered refinement selectors, varying vertex-type persistence
modules, and correspondence or Hausdorff stability remain separate results.
The present construction supplies their unfiltered contiguity prerequisite.
