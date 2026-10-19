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

## Sources and scope

This is a source-motivated library bridge, proved for the library's actual
support-aware chains. Chazal–de Silva–Oudot,
[*Persistence stability for geometric complexes*, arXiv:1207.3885v3, §3](https://arxiv.org/html/1207.3885v3#S3),
uses simplicial maps and their induced homology maps in Definition 3.1 and
Proposition 3.3. It also uses equality of maps induced by contiguous simplicial
maps. That latter theorem and the Munkres proofs cited there are not established
by this unit. No numbered metric stability theorem is claimed as its result.

The algebraic ingredients are the pinned mathlib tuple-sorting, permutation-sign,
Finsupp and homology APIs. TauCeti's
[ordered chain complex at revision 7b0d106](https://github.com/TauCetiProject/TauCeti/blob/7b0d106bf79dbea38ba8819985bd029989181287/TauCeti/AlgebraicTopology/SimplicialComplex/ChainComplex.lean)
also gives Ring-valued ordered chains and boundary square-zero. Its inspected
Maps and OrderedMap modules do not provide this arbitrary signed chain action;
the latter's cell-image and increasing-enumeration results require local
injectivity or order conditions. That source uses a different toolchain and is
not an installed dependency or copied implementation.

Contiguity homotopies, independence of refinement selectors on homology, varying
vertex-type persistence modules, and correspondence or Hausdorff stability are
separate results. The present construction supplies their arbitrary-map chain
and homology prerequisite.
