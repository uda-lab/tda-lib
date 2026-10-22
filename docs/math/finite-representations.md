# Finite representations of persistence modules

A finite persistence module consists of vector spaces at `0, …, N - 1` and
compatible maps between ordered indices. Applications often supply only the
adjacent maps, or their matrices in chosen bases. The adapters in
`TDA/Persistence/FiniteLine.lean` and `MatrixSequence.lean` turn those inputs into
the existing `PModule` and reuse its interval decomposition.

## Adjacent linear maps and the finite line

`FiniteLine N` has vertices indexed by `Fin N` and an arrow precisely when
`i.val + 1 = j.val`. It is a separate quiver type: the preorder category on
`Fin N` already has a morphism for every inequality. There is exactly one path
between ordered vertices and none otherwise. The equivalence between its path
category and `Fin N` therefore induces an equivalence between representations
`Paths (FiniteLine N) ⥤ ModuleCat R` and `PModule R (Fin N)`.

`FiniteLine.moduleOfAdjacent V step` requires a module `V i` at each vertex
and one linear map for each adjacent pair. It supplies identities and all
chronological composites. `homMk` and `isoOfAdjacent` extend commuting adjacent
squares to natural transformations and natural isomorphisms. These
constructions work over a ring, including the empty line. They impose no
injectivity or chain-complex square-zero condition.

## Based matrices and coordinates

Over a commutative ring, `MatrixSequence R N` supplies natural-number dimensions
`dim i` and rectangular matrices `step i j h`. Rows index the target coordinates and columns index the
source coordinates. `toPModule` interprets them on `Fin (dim i) → R`.
`compositeMatrix` evaluates any structure map, with identities on the diagonal
and the later matrix on the left in a product. `Hom` consists of stage matrices
`F i` satisfying `B.step i j h * F i = F j * A.step i j h`; `toNatTrans`
extends those equations to every composite.

For `M : PModule R (Fin N)` and explicitly supplied finite bases `b i`,
`ofBases M d b` is its coordinate sequence. The map `coordinateIso M d b`
is a natural isomorphism from `M` to that sequence's module. Its components are
the basis coordinate equivalences, and `coordinateIso_naturality` identifies
every structure map in coordinates. Standard coordinate bases recover the
input sequence exactly. `coordinateHom` transports genuine natural
transformations, while `basisChangeIso` supplies the coordinate-change
maps between two choices of bases.

Over a field `k : Type u`, the coordinate fibers are finite-dimensional and
`MatrixSequence.barcode` is the existing `rankBarcode`. The chosen
`decompositionIso` uses `rankBarcodeIso`; no second classification proof is
introduced. `barcode_ofBases` and `barcode_basisChange` identify the resulting
interval multiset with that of the original module, independently of its bases.
As in the existing theorem, decomposition uses
`PModule.{u,0,u} k (Fin N)`. A finite interval is `[birth, death)` with
`birth < death ≤ N`; death `N` only says that the class survives the last
observed stage. It does not assert an infinite lifetime beyond the observations.

## Original real critical values

`MatrixSequenceReal.lean` takes a grid `c : Fin n ↪o ℝ` and a padded sequence
`A : MatrixSequence k (n + 1)`. Its stage zero describes the entire left tail;
`A.dim 0 = 0` is the hypothesis needed for the existing left-zero
constructibility contract. `realModule A c` pulls back along `cellIndex c`.
Thus stage `i + 1` occupies the half-open cell starting at `c i`, and the final
cell is explicitly constant and unbounded.

`criticalSampleIso` recovers the positive stages and all their maps.
`realDiagram_eq_ofIndexBars` labels their finite barcode by the original values
`c i`, and `realBarcodeIso` gives the existing natural reconstruction from that
real diagram. Here a terminal barcode occurrence has endpoint `⊤` because the
input construction explicitly supplies the constant final cell.
`realDiagram_refinement` proves that inserting observations into the grid
preserves real endpoints and multiplicities. Unequal spacing, negative critical
values, and rational values embedded in `ℝ` require no change of convention.

## Checked consumers

[`MatrixSequenceExamples.lean`](../../TDA/Persistence/MatrixSequenceExamples.lean)
uses rectangular inputs with dimensions `1,2,1`. Inclusion followed by the second
projection has barcode `[0,2) + [1,3)`; replacing it with the first projection
gives `[0,3) + [1,2)`. The adjacent ranks agree, so these examples also test that
the adapter retains composite maps. The same module exercises supplied bases,
nonidentity scalar maps, empty and one-stage inputs, and a nontrivial invertible
coordinate change.

[`FiniteRepresentationRealExamples.lean`](../../TDA/Persistence/FiniteRepresentationRealExamples.lean)
pads the zero-composite input by a zero stage and places it at `-1, 1/10, 4`.
Its diagram has `[-1,4)` and `[1/10,∞)`, with the latter lifetime supplied by the
constant final cell. Inserting `2` into the grid preserves these original real
endpoints. The reconstruction is a natural isomorphism.

## Mathematical and computational scope

The new results are adapter constructions, proved directly using mathlib's
[`CategoryTheory.Paths`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/CategoryTheory/PathCategory/Basic.lean),
category equivalences and
[`Matrix.toLin'` / `LinearMap.toMatrix'`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/LinearAlgebra/Matrix/ToLin.lean).
Their classification dependency is the existing
[finite interval decomposition](finite-interval-decomposition.md); the real
dependency is the existing finite-constructible reconstruction and refinement.
No numbered theorem from a representation-theory source is claimed here.

At the inspected [TauCeti revision](references.md#TauCeti-7b0d106),
[`Representation/Basic.lean`](https://github.com/TauCetiProject/TauCeti/blob/7b0d106bf79dbea38ba8819985bd029989181287/TauCeti/RepresentationTheory/Quiver/Representation/Basic.lean)
defines `QuiverRep` by the same functor shape
`Paths Q ⥤ ModuleCat k`. Its general path-algebra and Krull–Schmidt developments
are unnecessary for this finite-line adapter. No TauCeti source is copied or
imported, and its newer toolchain is not adopted.

These theory APIs may be noncomputable. In particular, their natural
isomorphisms and canonical rank barcode do not furnish an executable barcode
extraction algorithm. Arbitrary-field theorems are distinct from the library's
certified finite F₂ reduction. A future algorithm must specify coefficient
operations, decidable zero tests, executable output and a correctness theorem.
Natural-number persistence versus nonnegatively graded `k[t]`-modules, and
general real-indexed pointwise finite-dimensional interval decomposition, remain
separate interfaces and theorem milestones. Arbitrary real persistence is not
identified here with ordinary `k[t]`-module theory.
