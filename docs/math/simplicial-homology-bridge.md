# Support-aware simplicial homology bridge

## Decision and boundary

Use free oriented chains on the **actual faces** of a
`PreAbstractSimplicialComplex V`, with one fixed `LinearOrder V` for every
filtration stage. A face of cardinality `n+1` is one degree-`n` basis element.
The coefficient carrier is `Face K n →₀ R`; the ordinary differential in degree
zero is zero. No empty face, degree `-1` term, or unused ambient singleton is
added. This choice makes the face basis itself the finite matrix basis. It
requires no chain-model comparison before finite PH can use its coordinates.

The choice is an interface decision, not a claim that the general boundary,
`d²=0`, functorial homology, or a PH algorithm has been constructed. The
compiling prototype is [TDA/Simplicial/Bridge.lean](../../TDA/Simplicial/Bridge.lean).
`packagedComplex` accepts a proof of `d²=0`, and `packagedInclusion` accepts
commutation; neither supplies those proofs for general simplicial chains.

| Route or layer | Reused declaration and source | Proposed declaration or obligation | Coefficients, universe, finite data |
| --- | --- | --- | --- |
| Actual faces | mathlib `PreAbstractSimplicialComplex`; merged `TDA.Filtration.singletonFace`, `vertexBirth`, `face_mono` | `Face K n`, `Chain K R n`, ordered deletion boundary | `V` linearly ordered, with one order across stages; `Ring R` for signed chain theory; no finite ambient `V` |
| Chain packaging | mathlib `Finsupp.basisSingleOne`, `ChainComplex.of`, `ChainComplex.ofHom` | Prove general ordered-face `d²=0`; prove inclusion commutation, identity and composition | `ModuleCat R` supports a general `Ring R`; the supplied square-zero/commutation proofs are real prerequisites |
| Ordinary homology | mathlib `ShortComplex.moduleCatMk`, `moduleCatToCycles`, `moduleCatHomologyIso`; merged persistence module API | Identify `Hₙ` with `ker dₙ / range(dₙ₊₁ → ker dₙ)`, construct inclusion-induced maps and their identity/composition laws, then instantiate the covariant module of #11 | `Ring R`; a nonzero vertex birth additionally needs `Nontrivial R` |
| Finite coordinates | mathlib `LinearMap.toMatrix`, `toMatrix_apply`, `toMatrix_comp` | Coordinate equivalence for each `Cₙ`, differential and inclusion squares; transport cycles, boundaries and quotient homology naturally | Finite **total** face set for bounded finite-rank stages; actual `Fintype` and `DecidableEq` for executable enumeration. This matrix API uses `CommSemiring`; signed boundaries use `CommRing`, hence any `Field` |
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

## What the Lean prototype proves

`Face K n` and `faceBasis` use only present `(n+1)`-faces. Same-ambient
`chainIncl` preserves each face; `chainIncl_id` and `chainIncl_comp` are proved
for all degrees and rings. The `packagedComplex` and `packagedInclusion`
signatures compile at `ChainComplex (ModuleCat R) ℕ`.

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

For the full triangle on `Fin 3`, the checked ℤ fixture has
`∂₂[0,1,2]=[1,2]−[0,2]+[0,1]`. Its edge boundary maps are
`∂₁[i,j]=[j]−[i]`; `edge_cover` verifies those three edges exhaust the actual
degree-one face basis. Lean proves `∂₁∂₂[0,1,2]=0`, a nonzero degree-one
same-ambient inclusion square from the edge `{0,1}` into the triangle, and matrix
entries `M([1],[0,1])=1` and `M([0],[0,1])=-1`. The finite matrix example
uses classical `Fintype.ofFinite`, so it checks coordinate types and signs,
not an executable enumeration. These fixtures do not prove general `d²=0`.

## Required implementation theorems

1. Define `dₙ₊₁` by summing the ordered deletions of each actual face, with
   coefficient `(-1)^i`; define `d₀=0`. The precomplex lower-set property
   must supply membership of every nonempty deleted face. For `i<j`, deleting
   `i` then shifted `j−1` and deleting `j` then `i` give the same remaining
   face with signs `(-1)^(i+j−1)` and `(-1)^(i+j)`. Pairwise cancellation
   proves `d²=0`; the zero-degree case is separate.
2. For `K≤L` in the same ambient ordered `V`, prove
   `d_L ∘ chainIncl = chainIncl ∘ d_K` on a basis face, then extend linearly.
   The face and its order stay unchanged. Combine this with the proved
   `chainIncl_id` and `chainIncl_comp` to form actual `ChainComplex.ofHom`
   maps and show their identity/composition laws.
3. Use `ShortComplex.moduleCatHomologyIso` to expose the kernel quotient.
   A commuting chain square maps cycles to cycles and boundaries to
   boundaries, so it descends to homology. Prove the induced identity and
   composition laws and assemble the covariant `ModuleCat R` valued
   persistence module over the filtration preorder from #10 and #11.
   Empty support has `C₀=0`; a single isolated vertex has `C₀≅R` and
   `C₁=0`, hence ordinary `H₀≅R`. Its birth class is nonzero only when
   `Nontrivial R` is assumed.
4. Under a finite total face set, define coordinate isomorphisms from each
   free face module to the explicitly enumerated column module. Prove
   `M(d)·coord = coord·d` and the analogous inclusion square. Show the
   induced maps identify matrix kernels and images **inside kernels**, then
   descend to isomorphisms of quotient homology. Prove the naturality square
   for every same-ambient inclusion. Equality of dimensions or ranks alone
   does not meet this contract. Restrict this `LinearMap.toMatrix` route to
   `CommRing R`; retain `Ring R` for the abstract chain/homology theory.

Arbitrary vertex maps, collapsing simplices, general SSet comparison and PH
reduction are outside this initial bridge. Any later second chain model needs
natural chain equivalences and induced homology isomorphisms, not only equal
Betti numbers.
