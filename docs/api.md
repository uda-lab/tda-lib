# Public API and import guide

## Entry points

```lean
import TDA.Persistence -- one ordinary library area
```

Use `import TDA.Library` for all ordinary areas. These entry points exclude the
standalone example and acceptance modules. To use a particular worked example, import
its module directly, or import `TDA.Persistence.Examples` (and similarly for each area).
`TDA.Examples` collects all six example aggregators.

`import TDA` deliberately loads both `TDA.Library` and `TDA.Examples`. It is the
comprehensive root used by the build, theorem axiom audits, module-reachability coverage
and generated documentation. The default `lake build` therefore still builds every
module, even though ordinary consumer imports are smaller. Generated pages intentionally
include examples; generating them remains the separate local `scripts/build-docs.sh`
workflow. The documentation target is the comprehensive root, independently of the
consumer entry points.

This is a module boundary, not an export whitelist: Lean imports expose the declarations
of their dependencies, including existing small examples embedded in implementation
modules. The area aggregators and the library/example roots contain only imports.
Namespaces containing `Examples` are for demonstrations, not the main consumer API.

## Areas and intended use

| Import and namespace | Main definitions and theorem families | Requirements and scope |
|---|---|---|
| `TDA.Filtration` / `TDA.Filtration` | `SimplicialFiltration`, support, `FilterFunction`, sublevels, `CompatibleOrder`, `OrderingEquivalent` and order chambers | Values belong to actual nonempty faces. Ordered values are separate from the ambient vertices; compatible enumerations require finite total faces. Support can grow with the index. |
| `TDA.Simplicial` / `TDA.Simplicial` | Actual-face `Chain`, signed `boundary`, square-zero chain complex, inclusion maps, `simplicialHomology`, finite coordinates and `VertexMap` / `Contiguous` | Signed chains use an ambient vertex order and a ring. Finite-dimensional homology additionally uses a field and finite faces. A vertex map may identify vertices; contiguity is reflexive and symmetric, with composition laws, and is not asserted transitive. |
| `TDA.Persistence` / `TDA.Persistence` | `PModule`, structure maps and reindexing; finite intervals, rank barcodes and decomposition; `Diagram`, `dgm`, reduction, stability and calculus | The functor core needs a ring and a preorder, with independent coefficient/index/carrier universes. Finite decomposition has its narrower field, finite-chain, pointwise finite-dimensional and same carrier/coefficient universe assumptions. Actual face diagrams and calculus retain their stated vertex-order, finite-face and local-lift hypotheses. |
| `TDA.Topology` / `TDA.Topology` | `CoverFamily`, `Covers`, `Refinement`, `nerve`, `nerveMap`, `nerveMap_contiguous`, path-cover and cosheaf interfaces | An indexed set family need not cover anything; `Covers` states coverage separately. Labels may repeat and members may be empty. A nerve face is nonempty and has an actual common witness. Refinement selectors need not be injective. |
| `TDA.Reeb` / `TDA.Reeb` | Inverse-image path components, Reeb quotients and comparison maps; interval cosheaves, smoothing, interleavings and extended distance; finite data, graph realizations and `RGraph.cosheafEquivalence` | Components are path components of the inverse-image subspace. General quotient comparison is a natural transformation. The graph/constructible-cosheaf equivalence is scoped to the declared finite real-graph category and value universe `0`. Smoothing and geometric comparisons have separate contracts. |
| `TDA.Mapper` / `TDA.Mapper` | `ComponentIndex`, pullback component covers, `mapper`, its one-skeleton, refinement maps, graph-PL comparison and `CoherentCoverTower` | Input is a continuous map and an indexed target family. Coverage and multiplicity are explicit hypotheses where used. Finiteness is conditional; tower identity/composition are supplied coherence data. These constructions are noncomputable theory, not an executable Mapper implementation. |

For a small dependency footprint, import an individual implementation module rather than
the whole area. Generic simplicial contiguity depends only on the simplicial vertex-map
API; nerve-specific contiguity is owned by `TDA.Topology.NerveContiguity`. Mapper Tower
consumes that Topology theorem. This removes the previous Simplicial-to-Topology dependency.

Structure projections and the existing coercions provide access to values and vertex-map
functions; they do not erase support, monotonicity or face-preservation hypotheses. Use
the declared field/ring, order, finite-face and topological instances at the call site.
Universe requirements belong to each definition's signature; the areas do not impose a
single shared universe on the whole library.

## Persistent homology results and computational boundary

The finite decomposition API takes `M : PModule.{u,0,u} k (Fin N)` with
`k : Type u`, `[Field k]`, and `[∀ i : Fin N, FiniteDimensional k (M.obj i)]`. The index
universe is `0`, and the field and module-carrier universes are both `u`; this
does not extend the decomposition theorem to independent carrier universes.
`exists_barcode_decomposition` and `nonempty_rankBarcodeIso` construct genuine natural
interval semantics. `nonempty_iso_iff_structureMapRank_eq` classifies these modules by
the ranks of all actual structure maps, including composites. The canonical object is
the interval multiset; the chosen summands and isomorphism are not canonical. See
[finite interval decomposition](math/finite-interval-decomposition.md).

`FiniteConstructible.reconstructionIso` reconstructs a real-indexed module from a finite
chain of critical samples preceded by a zero stage. It uses left-closed/right-open strata,
an actual zero left tail and actual structure-map isomorphisms within each stratum; the
final tail may be nonzero. The reconstruction works over any ring with independent
module-carrier universe and no finite-dimensionality assumption. It supplies both natural
transformations and their inverse identities; interleaving distance and barcode isometry remain
separate work. See [finite-stratum reconstruction](math/constructible-modules.md).

`FiniteConstructible.barcodeRealizationIso` connects this reconstruction to finite
decomposition and `RealBarcode.realize`. It requires a coefficient field and carrier in
the same universe, with finite-dimensionality only at the critical fibers. The sampled
zero stage produces no bars; actual `Fin.succ` restriction preserves all remaining
occurrences before `ofIndexBars` assigns the real finite endpoints and essential tails.
The result is an actual natural isomorphism to the fixed grid's endpoint barcode, with
duplicate summands retained. See [real barcode realization](math/real-barcode-realization.md).

`RealShift` constructs real shifts and transitions over any ring, with natural unit
and composition identifications satisfying the coherence equations.
`RealInterleaving` contains actual natural maps and both double-shift identities;
zero-interleaving witnesses correspond to natural isomorphisms, and interleaving
with zero is equivalent to a zero double-shift structure map. Its interval examples
use nontrivial field coefficients. See [real interleaving witnesses](math/real-interleavings.md)
for the finite nonnegative parameters and witness equations.

`RealBarcode.matchingInterleaving` constructs a witness between the actual realizations
of two positive finite diagrams from an existing occurrence matching with cost at most ε.
Matched finite bars use endpoint bounds; unmatched bars have length at most `2ε`,
including equality; essential occurrences use the matching's total equivalence.
Multiplicity, actual structure maps and ε=0 are retained. See
[matching-induced interleavings](math/matching-interleavings.md) for the constructed
maps and exact source specialization. Interleaving distance and the reverse
interleaving-to-matching direction are separate results.

`dgm` is the diagram of actual simplicial sublevel homology, with multiplicities retained,
half-open finite intervals, omitted zero-length value bars and essential deaths at `⊤`.
The graded reduction adapter reaches this diagram through actual homology and natural
maps; `nonempty_actualPrefixHomologyIsoPivotBarcode` exposes its natural interval
isomorphism. The original boundary differential is distinct from its reduced matrix.
See [actual sublevel diagrams](math/finite-sublevel-diagram.md) and
[reduction](math/persistence-reduction.md).

`bottleneck_dgm_le_faceSupDifference` proves finite-complex real-filter stability over a
field, including pairing changes and closed interpolation endpoints. This is the
library's finite combinatorial counterpart of the geometric stability theorem; it does
not supply a comparison with singular homology of general tame functions.

The `ActualDiagramRegularity`, `ActualLossDerivative` and `ActualLossHessian` APIs use
ordered local representatives with explicit hypotheses on face values and loss lifts.
The full lift retains tied finite pairs, including their diagonal coordinates; the
Hessian includes both chain-rule terms. These are local results on the declared
neighborhoods, not a claim of global smoothness at arbitrary pairing changes. See
[local regularity](math/diagram-calculus.md) and
[actual loss Hessians](math/actual-ph-loss-hessians.md).

For general regularity, use `LocalCrDiagramLift r`, `DiagramContDiffAt r`,
`CrThroughAllRepresentatives r` and the face-template APIs `fixedFaceLift_contDiffOn_cr`
and `fixedFaceCrLift`. The C¹/C² lift structures and `actualFaceLossLift` /
`actualFaceLossC2Lift` remain convenient inputs to derivative and Hessian theorems.
Their conversions to/from the general layer preserve the carrier, coordinates and
factorization; at orders one and two the all-representative predicates are
definitionally equivalent. These wrappers do not supply stronger regularity or new
diagram-level derivatives. See [the calculus-layer guide](math/diagram-calculus.md#regularity-layers).

`TDA.Persistence.Reduction.FiniteInput.run` is an executable certified F₂/integer path
from a finite simplex list to occurrence records. It rejects invalid input instead of
normalizing it; `outputDiagram_eq_dgm` proves semantic correctness for valid lists in
every degree. Negative and tied grades, duplicate output points, empty input and
essential classes have explicit conventions. Proof-derived semantic objects and the
arbitrary-field decomposition remain noncomputable. See
[the input contract and correctness route](math/finite-ph-computation.md).

## Metric input and Rips diagrams

`TDA.Filtration.Rips` takes explicit metrics on a fixed finite labelled vertex type,
using the full complex of nonempty faces and their diameters. Singletons have value
zero, the empty face is excluded, and stages below zero are empty. Sublevels are closed
Rips complexes with diameter time. `pairwiseDiscrepancy` is the maximum absolute
distance-matrix difference, with empty maximum zero.

`TDA.Persistence.Rips.bottleneck_dgm_le_pairwiseDiscrepancy` bounds the actual diagrams
in every degree by that discrepancy. For V : Type u it requires `LinearOrder V`,
`Fintype V`, and a coefficient field k : Type u, retaining existing multiplicity and
essential-bar semantics. This noncomputable consumer of finite-face stability covers
the fixed labelled carrier. See [the construction, proof and source scope](math/rips-metric-stability.md).

## Finite first-order PD matching cost

`TDA.Persistence.FiniteMatchingCost` defines `finiteFirstOrderMatchingCost` from the
existing real `OccurrenceMatching.totalFiniteCost`: paired points use the birth–death
L∞ norm, and every unmatched occurrence costs |death−birth|/2. Finite occurrence types
retain repeated values; the PD interpretation requires birth < death and no essential
part. The supporting real-cost algebra needs no positivity hypothesis.

The feasible matching family is finite and nonempty. The API proves attainment,
nonnegativity, candidate upper bounds, universal lower bounds, exact empty-input
formulas and invariance under finite occurrence equivalences.
`TDA.Persistence.FiniteMatchingCostLaws` proves self cost zero, symmetry and the triangle
inequality using the existing partial-matching reversal and composition. For positive
lifetimes, `finiteFirstOrderMatchingCost_eq_zero_iff` identifies zero cost exactly with
an occurrence bijection preserving birth–death values, including multiplicities.
Raw presentations can differ by a permutation at zero cost; diagonal occurrences are
excluded from this separation result. No quotient metric instance or equality with
measure boundary transport is supplied.
See [the matching minimum and its scope](math/finite-first-order-matching.md).

## Gaussian persistence images

`TDA.Persistence.GaussianKernel` proves normalization and L¹ translation estimates for
the actual product Gaussian at positive bandwidth σ. `TDA.Persistence.PersistenceImage`
integrates its weighted surface over a fixed finite family of measurable pairwise
disjoint pixels. The target `PiLp 1` carries the pixel vector ℓ¹ norm. A nonnegative
weight bounded by B, maximum-norm Lipschitz with constant A, and zero at persistence zero
uses birth–persistence coordinates `(b,d−b)`.

`norm_image_sub_le_matching` bounds the difference of image sums by
`(2A + 3B sqrt(2/π)/σ)` times every finite partial matching's total birth–death L∞ cost,
including diagonal charges for unmatched occurrences. Real pairs satisfy birth < death;
multiplicities and empty inputs are retained, and essential bars are excluded.
`norm_image_sub_le_finiteFirstOrderMatchingCost` applies it to an attained minimizer,
giving the same coefficient times the finite first-order matching cost. No measure
boundary-transport or RKHS identification is asserted.
The Gaussian and pixel-integral definitions are noncomputable analytic APIs.
See [the construction, analytic proof and source correspondence](math/persistence-images.md).

## Distance matrices to finite Rips images

`PersistenceImage.finiteDiagramImage` applies the Gaussian image to a diagram's finite
occurrences, retaining multiplicity and omitting essential bars. For positive diagrams
with finite full bottleneck β, its pixel ℓ¹ error is at most C (N_D+N_E) β, where N_D,N_E
count finite occurrences and C is the existing PI coefficient. The finite bottleneck
condition is explicit because `ENNReal.toReal ⊤ = 0`.

`Rips.norm_finiteDiagramImage_sub_le_pairwiseDiscrepancy` specializes this to actual Rips
diagrams in every degree: error ≤ C (N_D+N_E) δ for maximum pairwise metric discrepancy δ.
It inherits the same finite ordered carrier and field assumptions as the Rips API, with
no new cardinality/genericity hypothesis. These noncomputable APIs give a count-dependent
certificate, with essential bars still present in the bottleneck comparison. See
[the definitions, bridge and exact scope](math/rips-persistence-images.md).

## Review and extension boundaries

The selected PH claims and their proof-critical bridges received the source-based review
recorded in [PR #220](https://github.com/uda-lab/tda-lib/pull/220). Its distinction between
source matches, checked finite specializations and independently proved extensions is
retained in the mathematical notes. This does not certify every helper or the entire
library against external sources.

Reeb/cosheaf and ordinary Mapper have merged bounded contract implementations, as
recorded in [#34](https://github.com/uda-lab/tda-lib/issues/34) and
[#168](https://github.com/uda-lab/tda-lib/issues/168). Their pre-publication source review
is separately tracked in [#215](https://github.com/uda-lab/tda-lib/issues/215); this guide
does not declare those reviews complete. The implemented graph/cosheaf equivalence and
component stability bounds do not establish all deferred geometric smoothing or distance
comparisons. Ordinary Mapper does not claim MultiNerve, the Nerve Lemma, homology
selector-independence, stability or Mapper–Reeb convergence.

General geometric tame-function PH stability, infinite/q-tame theory, manifold charts
and executable arbitrary-field decomposition are outside the reviewed PH scope. A first
stable release must state its selected results and limitations; it need not finish every
roadmap extension. This guide describes the current API and does not announce a release.
