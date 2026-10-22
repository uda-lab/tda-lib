# Support-aware simplicial homology bridge

## Decision and boundary

Use free oriented chains on the **actual faces** of a
`PreAbstractSimplicialComplex V`, with one fixed `LinearOrder V` for every
filtration stage. A face of cardinality `n+1` is one degree-`n` basis element.
The coefficient carrier is `Face K n →₀ R`; the ordinary differential in degree
zero is zero. No empty face, degree `-1` term, or unused ambient singleton is
added. This choice makes the face basis itself the finite matrix basis. It
requires no chain-model comparison before finite PH can use its coordinates.

The choice is an interface decision. The actual signed boundary, its square-zero
law, and same-ambient inclusion chain maps are proved. The later layers provide
functorial homology, finite coordinates, and certified finite F₂ persistence. The chain APIs are in
[TDA/Simplicial/Bridge.lean](../../TDA/Simplicial/Bridge.lean),
[TDA/Simplicial/Boundary.lean](../../TDA/Simplicial/Boundary.lean),
[TDA/Simplicial/ChainComplex.lean](../../TDA/Simplicial/ChainComplex.lean), and
[TDA/Simplicial/Inclusion.lean](../../TDA/Simplicial/Inclusion.lean).
Mathlib's `ChainComplex.of` and `ChainComplex.ofHom` accept caller-supplied differentials,
square-zero proofs and commutation proofs. The signed simplicial complex and inclusion map
construct these proofs internally.

| Route or layer | Reused declaration and source | Proposed declaration or obligation | Coefficients, universe, finite data |
| --- | --- | --- | --- |
| Actual faces | mathlib `PreAbstractSimplicialComplex`; merged `TDA.Filtration.singletonFace`, `vertexBirth`, `face_mono` | `Face K n`, `Chain K R n`, ordered deletion boundary | `V` linearly ordered, with one order across stages; `Ring R` for signed chain theory; no finite ambient `V` |
| Chain packaging | mathlib `Finsupp.basisSingleOne`, `ChainComplex.of`, `ChainComplex.ofHom` | General ordered-face `d²=0` and same-ambient inclusion commutation, identity, and composition are proved | `ModuleCat R` supports a general `Ring R`; no finite-face assumption is used |
| Ordinary homology | mathlib `ShortComplex.moduleCatMk`, `moduleCatToCycles`, `moduleCatHomologyIso`; persistence module API | `simplicialHomologyIncl` has identity, composition and quotient-naturality laws; `simplicialHomologyPModule` assembles the inclusion maps over a filtration | `Ring R`; no finite-face assumption; a nonzero vertex birth additionally needs `Nontrivial R` |
| Finite coordinates | mathlib `LinearMap.toMatrix`, `toMatrix_apply`, `toMatrix_comp` | `chainCoordinates` and `boundaryMatrix_mulVec` identify chains and their boundary matrices; `simplicialHomologyCoordinates` identifies quotient homology naturally under inclusions | `CommRing R`; degreewise finite faces and the stated `Fintype`/`DecidableEq` data for matrix columns. A finite total face set supplies degreewise finiteness; these theory coordinates are noncomputable |
| SSet alternative | mathlib `SSet.chainComplex`, `normalizedMooreComplex`, `inclusionOfMooreComplex`, Dold–Kan homotopy equivalence | Construct a support-preserving precomplex-to-SSet functor and a natural identification of normalized chains with the finite ordered-face basis | `SSet.{u}` with coefficients `ModuleCat.of R R` in `ModuleCat.{u} R` type-checks for `R : Type u`, `[Ring R]` after importing `ModuleCat.Colimits`. The alternating complex contains degenerate simplices, so finite input alone does not bound its chain groups |

The prototype's `TotalFace K` makes the missing finiteness hypothesis explicit;
`faceFiniteOfTotalFinite` passes it to each degree. Every individual face is a
`Finset`, but that does not make `TotalFace K` finite. Each filtration stage
being finite also does not supply one finite master matrix: a finite total
face set or a stated finite union across the chosen stages is needed.
`Fintype.ofFinite` can select a noncomputable enumeration for theory. Verified
execution must carry or construct a concrete enumeration and decidable
equality; this prototype does neither.

The alternative `SSet.chainComplex` type check needed
`Mathlib.Algebra.Category.ModuleCat.Colimits`, since the `SSet` API requires
coproducts at the simplicial-set universe. Its alternating-face construction
has simplex generators in every degree, including degeneracies. The pinned
normalized Moore complex and its natural inclusion into the alternating-face
complex, with the pinned Dold–Kan homotopy equivalence, already handle the
**abstract normalization** comparison. They do not construct the missing
support-preserving SSet or identify normalized generators with our face basis.
A face-poset nerve would use chains of faces instead of original faces and
would need a further proved, natural comparison. TauCeti's simplicial maps
are source references only; its recorded Lean toolchain differs from this
repository's pin.

## What the current chain layer proves

`Face K n` and `faceBasis` use only present `(n+1)`-faces. Same-ambient
`chainIncl` preserves each face; `chainIncl_id` and `chainIncl_comp` are proved
for all degrees and rings. `ChainComplex.lean` and `Inclusion.lean` construct the
signed chain complex and its inclusion maps.

`Boundary.lean` defines `deletedFace` by erasing the selected vertex from the
actual face and obtains its face membership from the precomplex lower-set law.
`enumerationAfterDeletion` identifies the resulting increasing enumeration with
the original enumeration composed with `Fin.succAbove`. The noncomputable
`boundary K R n` is the signed `Finsupp.linearCombination` of these deletions;
its public entry points use only `[Ring R]`, independent vertex and coefficient
universes, and no finiteness assumption on the ambient vertex type. In
particular `boundary K R 0` is the edge-to-vertex map.

For the merged #10 bottom and `singletonFace` complexes, the prototype proves
all bottom chain groups are zero, the singleton's positive-degree groups are
zero, bottom ordinary `H₀=0`, and singleton ordinary `H₀≅R`. The H₀ checks use
the actual degree-zero face chains and mathlib's zero-map short complex:
absence of degree-one faces forces any boundary from degree one to vanish,
and the ordinary degree-zero boundary is zero. The generic
`zeroBoundaryH0` helper is only a zero-differential fixture; it is not a
definition of the homology of an arbitrary complex. The singleton categorical
isomorphism uses `R : Type u` with `V : Type u`, so both ModuleCat objects
share a universe. No nonzero birth is asserted when `R` is the zero ring.

Using the general `boundary`, the full-triangle fixture on `Fin 3` checks
`∂₁[i,j]=[j]−[i]` for each increasing edge and
`∂₂[0,1,2]=[1,2]−[0,2]+[0,1]`. It also checks that the edge `{0,1}` has
coefficients `1` at vertex `1` and `-1` at vertex `0`, so `boundary K ℤ 0` is
not zero, and that the triangle's twice-applied boundary cancels. These are
fixture results; the general `d²=0` theorem is proved by `boundary_comp_boundary`.
The general boundary is
also zero as a linear map in every degree on the actual bottom and singleton
complexes, whose positive-degree chains have no faces.

The earlier private matrix and inclusion fixtures in `Bridge.lean` use their own
finite prototype maps; they are not claimed as coordinates of the general
boundary or the inclusion maps proved in `Inclusion.lean`.

## Issue #86 — actual inclusion chain maps

For `K ≤ L` in one ordered ambient `V`, `Inclusion.lean` proves
`faceIncl_deletedFace`, `chainIncl_single`, and `boundary_chainIncl` for
independent universes `V : Type u` and `R : Type v` with `[Ring R]`. The boundary
proof checks arbitrary-coefficient singleton chains and extends by Finsupp
linear extensionality. It keeps coefficients as left scalar multiples and does
not assume that `R` is commutative.

`simplicialChainIncl` uses the actual `simplicialChainComplex` values and
`ChainComplex.ofHom`; it supplies no caller-provided commutation or
square-zero field. Its component theorem identifies each component with
`ModuleCat.ofHom (chainIncl R h n)`, and the proved identity and composition
laws reuse `chainIncl_id` and `chainIncl_comp`.

`InclusionExamples.lean` checks two proper inclusions on actual faces of `Fin 4`,
including a two-step chain-map composite on an edge generator. The ℤ edge
fixture proves the actual boundary `[1] − [0]`, the inclusion square, target
coefficients `+1` and `−1`, and nonzeroness. The degree-two fixture computes
`[1,2] − [0,2] + [0,1]` from the actual boundary in both the triangle complex
and its ambient target, then checks their inclusion square. Bottom and singleton
support, the singleton's degree-zero image and positive-degree vanishing, the
actual ordinary `d₀ = 0`, and a specialization to `Matrix (Fin 2) (Fin 2) ℤ`
are also kernel checked. Every private fixture declaration prints its axiom
footprint in the example module; the public theorems and constructor are pinned
in the corresponding `scripts/print_axioms/<Area>.lean` files.

## Homology, coordinates and finite persistence

[Homology.lean](../../TDA/Simplicial/Homology.lean) defines ordinary homology over
`Ring R`, without a finite-face assumption. `simplicialHomologyIncl` is induced
by the face inclusion, with identity and composition laws;
`simplicialHomologyIncl_quotient_naturality` identifies it with the induced map
on the kernel quotient. [Simplicial.lean](../../TDA/Persistence/Simplicial.lean)
assembles these maps into `simplicialHomologyPModule` for a filtration over a
preorder. Empty support has `H₀=0`, and an isolated vertex has `H₀≅R`;
a nonzero vertex class additionally requires `Nontrivial R`.

[FiniteCoordinates.lean](../../TDA/Simplicial/FiniteCoordinates.lean) works over
`CommRing R`. `chainCoordinates` requires `Finite (Face K n)`;
`boundaryMatrix_mulVec` also requires `Fintype (Face K (n + 1))` and
`DecidableEq (Face K (n + 1))` and identifies matrix multiplication with the
signed boundary. [FiniteHomology.lean](../../TDA/Simplicial/FiniteHomology.lean)
uses the same degreewise data for `simplicialHomologyCoordinates`, a linear
equivalence with coordinate cycles modulo coordinate boundaries.
`simplicialHomologyCoordinates_naturality` proves compatibility with
same-ambient inclusions, using the corresponding source and target enumeration
data. These are noncomputable theory coordinates; finite total faces provide
the finiteness hypotheses, rather than an executable master matrix.

[FiniteInput.lean](../../TDA/Persistence/Reduction/FiniteInput.lean) supplies the
certified F₂ procedure for finite lists of natural-number-labelled simplices
with integer grades. `run_eq_some_iff` states that `run xs = some out` exactly
when `Valid xs` and `out = occurrences xs`; invalid lists return `none`.
For valid input, `outputDiagram_eq_dgm` identifies the output diagram in every
natural degree with `dgm (ZMod 2) (gradeFilter xs h)`. This executable procedure
and its correctness bridge are distinct from the noncomputable coordinate API.

[VertexChainMap.lean](../../TDA/Simplicial/VertexChainMap.lean) constructs signed
chain and homology maps for simplicial vertex maps, sending a collapsed face
to zero in its original degree.
[ContiguityHomotopy.lean](../../TDA/Simplicial/ContiguityHomotopy.lean) constructs
a chain homotopy for contiguous maps and proves equality of their induced
homology maps. General comparison with simplicial-set or singular homology,
and executable extraction over arbitrary fields, are not supplied by these
results. A second chain model needs natural chain equivalences and induced
homology isomorphisms, not only equal Betti numbers.
