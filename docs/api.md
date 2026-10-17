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
| `TDA.Topology` / `TDA.Topology` | `CoverFamily`, `Covers`, `Refinement`, `nerve`, `nerveMap`, `nerveMap_contiguous`, `MultiNerveCell`, its `projection` and `multiNerveMap`, path-cover and cosheaf interfaces | An indexed set family need not cover anything; `Covers` states coverage separately. Labels may repeat and members may be empty. A nerve face is nonempty and has an actual common witness. Refinement selectors need not be injective. A multinerve cell is a path component of a nonempty finite intersection; the projection to the nerve is an order isomorphism only under `IntersectionsPathSubsingleton`. |
| `TDA.Reeb` / `TDA.Reeb` | Inverse-image path components, Reeb quotients and comparison maps; interval cosheaves, smoothing, interleavings and extended distance; finite data, graph realizations and `RGraph.cosheafEquivalence` | Components are path components of the inverse-image subspace. General quotient comparison is a natural transformation. The graph/constructible-cosheaf equivalence is scoped to the declared finite real-graph category and value universe `0`. Smoothing and geometric comparisons have separate contracts; geometric thickening composes laxly, by a height-preserving addition map that is not an isomorphism but becomes one after the Reeb quotient. |
| `TDA.Mapper` / `TDA.Mapper` | `ComponentIndex`, pullback component covers, `mapper`, its one-skeleton, `multiNerveMapper` and its projection onto `mapper`, refinement maps including `multiNerveMapperMap`, graph-PL comparison and `CoherentCoverTower` | Input is a continuous map and an indexed target family. Coverage and multiplicity are explicit hypotheses where used. The MultiNerve Mapper is the multinerve of the component cover; its projection onto `mapper` is surjective and is an order isomorphism under `IntersectionsPathSubsingleton (componentCover f U)`. Finiteness is conditional; tower identity/composition are supplied coherence data. These constructions are noncomputable theory, not an executable Mapper implementation. |

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

`FiniteBarcode.monoEmbedding` takes a natural transformation of these finite modules
whose components are injective and constructs an embedding of their canonical barcode
occurrences. It preserves each observed death and bounds the target birth by the source
birth. At each death it pairs equal ordinals in birth/index order, retaining duplicates;
the embedding respects identities and mono composition. Its count comparison uses actual
image/kernel injections, with a separate terminal-image case. See
[finite-chain mono embeddings](math/finite-mono-matching.md) for the endpoint conventions,
proof and rank-domination boundary.

For a monotone `theta : Fin s →o Fin s` with `i ≤ theta i`, `TranslationTrivial`
means vanishing of the actual maps `i → theta i`. `finiteCokernel` is the categorical
cokernel; its shortness is proved equivalent to a target-image inclusion.
Under this shortness condition, the canonical mono embedding satisfies
`birth(target) ≤ birth(source) ≤ theta(birth(target))` and uniquely covers every
target bar with `theta(birth) < death`. Its shifted-prefix comparison uses actual
vector lifts and a separate terminal-image case. See
[quantitative mono matchings](math/finite-mono-translation.md) for the general finite
translation extension and the still unformalized real-grid connection.

`FiniteBarcode.epiEmbedding` takes an actual componentwise surjective transformation
`p : M ⟶ N` of the same finite modules and embeds target barcode occurrences back into
source occurrences. It preserves birth, bounds the target bar's death by the corresponding
source bar's death, and pairs equal ordinals in descending-death/original-index order at
each birth. Identities and epi composition give identity and contravariant composition
laws. Its count comparison uses actual image-quotient surjections, with a separate
initial-stage image case. See [finite-chain epi embeddings](math/finite-epi-matching.md).

For an arbitrary transformation `f : M ⟶ N`, `finiteImage f` constructs its actual
range-valued module and natural epi–mono factorization. `FiniteBarcode.inducedMatching`
embeds precisely the source occurrence labels selected by the epi embedding into the
target labels via their unique intermediate image occurrences. Its Option-valued
`inducedMap` exposes the partial injection on all labels, with exact domain/range,
qualitative endpoint order and an equivalence between image occurrences and matched pairs.
It specializes to the existing mono/epi correspondences and the identity matching;
composition laws apply to monos and epis. See
[finite induced matchings](math/finite-induced-matching.md).
`finiteKernel` is the actual categorical kernel, with evaluated component-kernel
fibers and finite dimensionality derived from the source. Its theta-shortness
gives shifted same-birth survival counts, canonical epi death bounds and unique
long-source coverage. These estimates and the mono/cokernel bounds transfer through
the actual image to the existing induced matching, with independent kernel and
cokernel translations. See
[quantitative finite induced matchings](math/finite-quantitative-induced-matching.md)
for terminal endpoint extension, hypotheses and the general finite-translation scope.

`FiniteConstructible.reconstructionIso` reconstructs a real-indexed module from a finite
chain of critical samples preceded by a zero stage. It uses left-closed/right-open strata,
an actual zero left tail and actual structure-map isomorphisms within each stratum; the
final tail may be nonzero. The reconstruction works over any ring with independent
module-carrier universe and no finite-dimensionality assumption. It supplies both natural
transformations and their inverse identities. See
[finite-stratum reconstruction](math/constructible-modules.md).

`FiniteConstructible.commonGrid` constructs a refinement from a sorted union of
critical values. Actual constructibility survives refinement and positive-evaluation
shift on the grid `c_i-ε`. `moduleDiagram_refinement` proves equality of real endpoint
diagrams, deriving finiteness at added critical values from the original ones and
retaining duplicate bars and essential tails. See
[common grids and diagram invariance](math/constructible-refinement.md).

`IsConstructible.kernel` and `IsConstructible.cokernel` prove constructibility of
actual categorical defects on a shared grid. `interleaving_critical_defects`
constructs that grid and derives finite sampled defect shortness from an actual
real interleaving, using natural sampling comparisons and within-cell cancellation.
See [constructible defects and critical sampling](math/constructible-defects-sampling.md)
for the rounded translation, terminal observation and coefficient scope.

`moduleDiagram_shift` proves that actual positive evaluation translates the
native shifted-grid diagram by −ε; its refinement version derives finiteness
at added observations. Finite and essential occurrence equivalences return
shifted target labels by +ε, and the complete matching of a diagram with its
own shift is constructed with its endpoint and cost bounds proved. The target
untranslation operation is available for existing occurrence matchings. See
[real shift diagrams and occurrence untranslation](math/constructible-shift-diagrams.md)
for multiplicities, boundary conventions and the target-return operation.

`FiniteConstructible.inducedOccurrenceMatching` transports the actual sampled
finite induced partial injection to real finite and essential occurrence labels.
Actual real kernel/cokernel annihilation gives exact endpoint and unmatched-length
bounds, unique coverage of strictly long finite bars and a total essential
equivalence. `interleaving_shifted_induced_matching` derives these bounds at `2ε`
from an actual interleaving on possibly different grids, into the translated target
`D_N−ε`. No mesh error or supplied matching is used. See
[real induced occurrence matchings](math/real-induced-matchings.md). `interleavingMatching` returns the actual target labels by +ε and
`interleavingMatching_cost_le` proves cost at most ε.

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

`RealInterleaving.kernel_transition_eq_zero` and `cokernel_transition_eq_zero`
prove that either comparison morphism has actual categorical kernel and cokernel
with zero `2ε`-transition, over any ring without dimension assumptions. See
[real interleaving defect shortness](math/real-interleaving-shortness.md)
for the naturality proof, the sharp threshold example and its constructible matching consumer.

`RealInterleaving.mono`, `trans` and `congr` enlarge parameters, add parameters
under composition, and transport both modules along natural isomorphisms.
`realInterleavingDistance` takes the ENNReal infimum of finite witness parameters.
It satisfies the extended pseudometric laws, including triangle with infinite
summands. Empty witness sets give `⊤`; zero distance means witnesses at every
positive parameter and need not give a zero-interleaving or an isomorphism.
The explicit ephemeral example exhibits this nonattainment. See
[distance and approximation](math/real-interleavings.md#distance-infinity-and-approximation).

`RealBarcode.matchingInterleaving` constructs a witness between the actual realizations
of two positive finite diagrams from an existing occurrence matching with cost at most ε.
Matched finite bars use endpoint bounds; unmatched bars have length at most `2ε`,
including equality; essential occurrences use the matching's total equivalence.
Multiplicity, actual structure maps and ε=0 are retained. See
[matching-induced interleavings](math/matching-interleavings.md) for the constructed
maps and exact source specialization. `RealBarcode.distance_le_bottleneck` bounds
the interleaving distance by the bottleneck, taking the infimum of the individual
matching-cost bounds without an attainment assumption. The matching type may be
empty when essential cardinalities differ, giving infinite bottleneck.
`FiniteConstructible.distance_le_bottleneck` transports the bound to modules on
independently sized critical grids using `barcodeRealizationIso`; its
`matchingInterleaving` also transports individual witnesses. These module results
retain the existing zero-left-tail, half-open strata, critical-fiber finiteness and
shared field/carrier-universe assumptions.
`FiniteConstructible.bottleneck_le_distance` proves the opposite inequality
by bounding every finite interleaving parameter before taking its infimum.
`bottleneck_eq_distance` gives extended-distance equality; `interleaving_iff_matching`
gives the witness equivalence at every finite ε, including zero.
`distance_eq_top_iff_essential_card_ne` characterizes infinity by unequal
essential multiplicities. These results allow different finite grids, zero left
tails, half-open strata and nonzero constant final tails. They require a field,
original critical-fiber finite dimensionality and the existing shared field/carrier
universe. No optimal matching or interleaving at the distance is assumed. See
[finite-constructible isometry](math/constructible-isometry.md); general infinite
or q-tame modules and arbitrary-ring isometry remain outside this scope.

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

## Ambient Čech complexes

`TDA.Filtration.Cech` defines the closed Čech complex of labelled points p : V → X in a
pseudometric space as the nerve of closed balls, with ball radius as time. It proves
Rips_r ⊆ Čech_r ⊆ Rips_{2r} in pairwise form for arbitrary labels, and in Rips-sublevel
form for a label metric agreeing with the ambient distances. The radius filter on the full
complex satisfies rips/2 ≤ čech ≤ rips. Its sublevels contain the Čech complexes, with
equality when X is proper. See [the conventions, proofs and fixtures](math/cech-rips-sandwich.md).

`TDA.Filtration.CechDisplacement` compares two labelled families p, q : V → X in one
ambient space label by label. Moving the points of a face by at most ε changes its Čech
value by at most ε; the closed-ball radius estimate also needs ε ≥ 0 for the empty set.
For a finite V, `displacement` is the largest label-wise distance with empty maximum
zero, and the Rips pairwise discrepancy of distance-compatible label metrics is at most
twice it. `TDA.Persistence.Cech.bottleneck_dgm_le_displacement` bounds the actual Čech
diagrams in every degree by the displacement, and
`bottleneck_rips_dgm_le_two_mul_displacement` bounds the actual Rips diagrams by twice
it. Both keep the `LinearOrder V`, `Fintype V` and field assumptions of finite-face
stability. These are same-label bounds, not Hausdorff bounds. See [the proofs, attained
constants and source scope](math/cech-displacement-stability.md).

`TDA.Filtration.CechWitness` compares Čech complexes over a witness space W mapped into X
by f. An isometry can only add faces and lower values; a 1-Lipschitz g : X → W fixing the
labelled points reverses both, so with both maps the complexes and values agree. The
subspace and intrinsic complexes are the cases of a subtype inclusion.
`TDA.Filtration.CechSupNorm` works in the sup-metric product ι → ℝ for a finite ι, not
in `EuclideanSpace`. There a nonempty label set is a Čech face at r exactly when its
points are pairwise within 2r, so Čech_r = Rips_{2r}, every Čech value is half the Rips
value, and the two filters are ordering-equivalent; no properness is assumed. The line
ℝ follows through `Fin 1 → ℝ`. See [the proofs, fixtures and source
scope](math/cech-supnorm-witness.md).

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

## Weighted Gaussian kernel embedding

`TDA.Persistence.GaussianGram` proves mathlib `Matrix.PosSemidef` over arbitrary index
types for Hadamard powers, the entrywise exponential, real inner-product kernels,
diagonal rescaling and the Gaussian Gram matrix `exp(-‖v i - v j‖² / (2σ²))` at every
real σ. The birth–death kernel `kernel σ` uses the Euclidean squared distance through
`WithLp 2 (ℝ × ℝ)`, not the library's maximum norm on `ℝ × ℝ`.

`TDA.Persistence.WeightedKernel` builds mathlib's RKHS `RKHS.OfKernel` of that kernel as
`Space σ`. It embeds an occurrence family as `Σ i, w (T (x i)) • featureAt σ (x i)` with
the persistence-image `Weight` in birth–persistence coordinates. `diagramEmbedding` is the
same embedding of a diagram's finite occurrences, keeping multiplicity and omitting
essential bars. The evaluation formula, `inner_embedding` (the linear kernel) and
`norm_embedding_sub_sq` are statements about the actual RKHS inner product and norm.
Linear and Gaussian diagram Gram matrices are positive semidefinite for any family of
diagrams. The RKHS norm is not the pixel ℓ¹ norm above; no identification, stability
estimate or computable kernel evaluation is supplied. See
[the conventions, proof route and source mapping](math/weighted-kernel-embedding.md).

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
comparisons. The MultiNerve Mapper is bounded to its cells, face order, projection onto
ordinary Mapper, isomorphism criterion and refinement maps. Neither Mapper construction
claims geometric realization, the Nerve Lemma, homology selector-independence, stability or
Mapper–Reeb convergence.

General geometric tame-function PH stability, infinite/q-tame theory, manifold charts
and executable arbitrary-field decomposition are outside the reviewed PH scope. A first
stable release must state its selected results and limitations; it need not finish every
roadmap extension. This guide describes the current API and does not announce a release.
