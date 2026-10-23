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
| `TDA.Filtration` / `TDA.Filtration` | `SimplicialFiltration`, support, `FilterFunction`, sublevels, `CompatibleOrder`, `OrderingEquivalent` and order chambers | Values belong to nonempty faces. Ordered values are separate from the ambient vertices; compatible enumerations require finite total faces. Support can grow with the index. |
| `TDA.Simplicial` / `TDA.Simplicial` | Face `Chain`, signed `boundary`, square-zero chain complex, inclusion maps, `vertexChainMap`, `simplicialChainMap`, `simplicialHomology` / `simplicialHomologyMap`, finite coordinates and `VertexMap` / `Contiguous` | Signed chains use an ambient vertex order and a ring. Finite-dimensional homology additionally uses a field and finite faces. A vertex map may identify vertices; contiguity is reflexive and symmetric, with composition laws, and is not asserted transitive. |
| `TDA.Persistence` / `TDA.Persistence` | `PModule`, structure maps and reindexing; finite intervals, rank barcodes and decomposition; `Diagram`, `dgm`, reduction, stability and calculus | The functor core needs a ring and a preorder, with independent coefficient/index/carrier universes. Finite decomposition has its narrower field, finite-chain, pointwise finite-dimensional and same carrier/coefficient universe assumptions. Sublevel diagrams and calculus retain their stated vertex-order, finite-face and local-lift hypotheses. |
| `TDA.Topology` / `TDA.Topology` | `CoverFamily`, `Covers`, `Refinement`, `nerve`, `nerveMap`, `nerveMap_contiguous`, `MultiNerveCell`, its `projection` and `multiNerveMap`, path-cover and cosheaf interfaces | An indexed set family need not cover anything; `Covers` states coverage separately. Labels may repeat and members may be empty. A nerve face is nonempty and has a common witness. Refinement selectors need not be injective. A multinerve cell is a path component of a nonempty finite intersection; the projection to the nerve is an order isomorphism only under `IntersectionsPathSubsingleton`. |
| `TDA.Reeb` / `TDA.Reeb` | Inverse-image path components, Reeb quotients and comparison maps; interval cosheaves, smoothing, interleavings and extended distance; finite data, graph realizations, the incidence quiver and `incidenceGraph` of finite data with `card_incidenceGraph_edgeSet_le` and `RGraph.cosheafEquivalence`; `thickeningQuotient`, `thickeningQuotientAbsorptionIso`, `thickeningQuotientCompIso`, and `isRGraph_quotient_thickening_of_isConstructibleSpace`; `rgraphToConstructible`, `quotientRGraphAdjunction`, `RGraph.constructibleSmoothing`, `ConstructibleInterleaving`, `ConstructibleInterleaving.equivGeometric`, `constructibleInterleavingDistance`, `constructibleInterleavingDistance_eq_geometricInterleavingDistance` and `constructibleInterleavingDistance_eq_interleavingDistance`; `CylinderPresentation.levelHomeomorph`, `realizationSpace`, `levelPerturbation`, `CriticalValues.translate`, and the [level-change stability, range and exact-distance API](math/reeb-geometric-interleaving-equivalence.md#level-perturbations-of-a-fixed-presentation) | Components are path components of the inverse-image subspace. General quotient comparison is a natural transformation. The graph/constructible-cosheaf equivalence is scoped to the declared finite real-graph category and value universe `0`. Smoothing and geometric comparisons have separate contracts; geometric thickening composes laxly, by a height-preserving addition map that is not an isomorphism but becomes one after the Reeb quotient, and geometric smoothing of graph objects composes additively, `U_ε U_δ ≅ U_(ε+δ)`; geometric interleavings of graph objects correspond bijectively to interleavings of their component cosheaves, so the geometric and cosheaf interleaving distances coincide and the geometric one satisfies the triangle inequality. Geometric smoothing enlarges along `ε ≤ δ`, geometric interleavings are monotone in the parameter, and every graph object is within geometric distance `ε` of its `ε`-smoothing. Constructible interleavings correspond bijectively to geometric interleavings of the Reeb graphs; the constructible distance equals the cosheaf distance of the interval components of the spaces themselves; zero distance does not give an isomorphism of spaces. The incidence graph forgets parallel edges; edge counts use `Nat.card`. An interval-local component obstruction excludes geometric interleavings whose double-thickening restriction is injective from a nontrivial to a subsingleton value; the parallel loop and the single edge have geometric distance exactly `1/4`. Absorption `ℛ T_ε ≅ U_ε ℛ` holds on all constructible ℝ-spaces; constructibility of `T_ε X` itself is not claimed. Level-change stability fixes the presentation and number of levels; compact locally path-connected pieces supply constructibility. Exact translation distance requires a nonempty realization. Arbitrary continuous perturbations are outside that API. |
| `TDA.Mapper` / `TDA.Mapper` | `ComponentIndex`, pullback component covers, `mapper`, its one-skeleton, `multiNerveMapper` and its projection onto `mapper`, refinement maps including `multiNerveMapperMap`, graph-PL comparison, uniform interval covers (`uniformCover`) with attained-range coverage, the label-set cell equivalence `cellsOverLabelsEquiv` with graph-PL edge cells, height-separating uniform covers (`HeightSeparating`, `exists_heightSeparating_uniformCover`, `range_plHeight_eq_Icc`) with the splitting `cellComponentsEquivSum`, vertex cells (`vertexCellsEquiv`) and the cell classification `uniformVertexCellsEquivLevel`, `uniformVertexCellsEquivSpans`, `uniformEdgeCellsEquivSpans` through `EdgeCrosses` and `EdgeSpans`, finite Reeb data of graph-PL input (`CoversVertexHeights`, `vertexHeightLevels`, `LevelVertex`, `SpanEdge`, `levelEnd`, `graphPLReebData`, `uncoveredEdgeEquivCrossesOfLevel`, `induceComponentsEquivOfEq`) with the star and gap bijections `graphPLStarEquiv`, `graphPLGapEquiv`, their incidence laws `graphPLStarEquiv_map_left`, `graphPLStarEquiv_map_right` and the finite-data isomorphism `graphPLExtractHom`, `graphPLExtractIso`, closed level sets of graph-PL height (`ClosedLevel`, `IsLevelWindow`, `closedLevelComponentsEquiv`, `componentMap_levelInclusion_bijective`, `graphPLReebDataVEquivClosedLevel`), constructibility and the cosheaf identification of graph-PL height (`isConstructibleAt_intervalComponents_plHeight`, `cellGraphIsoOfSameLevels`, `graphPLCosheafIsoOfIso`, `graphPLCosheafIso`, `isConstructibleCosheaf_intervalComponents_plHeight`, `cosheafFunctorGraphPLIso`, `geometricInterleavingDistance_graphPL`), the Reeb quotient of graph-PL height (`compactSpace_realization`, `exists_coversVertexHeights`, `graphPLReebMap`, `graphPLReebQuotientHomeomorph`, `graphPLReebQuotientIso`, `graphPLReebQuotientIsoOfIso`, `intervalComponentNatTrans_graphPLReebMap`, `isRGraph_graphPLReebQuotient`, `graphPLReebGraph`, `graphPLReebGraphIso`, `isIso_intervalComponentComparison_plHeight`, `geometricInterleavingDistance_graphPLReebGraph`), the graph-PL realization as a constructible ℝ-space (`barycentric`, `t2Space_realization`, `edgePoint_eq_vertex_iff`, `edgePoint_eq_edgePoint_iff`, `locallyPathConnectedSpace_realization`, `realizationMap_injective`, `LevelPiece`, `levelPieceHomeomorph`, `compactSpace_closedLevel`, `locallyPathConnectedSpace_closedLevel`, `graphPLPresentation`, `graphPLPresentationMap`, `graphPLPresentationHomeomorph`, `graphPLComponentDataIso`, `graphPLReebMap_graphPLPresentationMap`, `graphPLPresentationIso`, `isConstructibleSpace_graphPLOver`, `graphPLReebQuotientIsoOfIso_graphPLComponentDataIso`, `graphPLSpace`, `quotientRGraphFunctor_obj_graphPLSpace`, `overBaseMap_graphPLSpace`, `isRGraph_quotient_thickening_graphPLOver`), and `CoherentCoverTower`, member-adapted MultiNerve Mapper comparison (`LevelsAdapted`, `exists_levelsAdapted`, `labelFace`, `uniformMapperData`, `uniformMapperCellsEquiv`, `uniformMapperIso`), refinement of graph-PL finite Reeb data (`graphPLRefineIso`, `graphPLRefineHom_trans_v`, `uniformMapperCanonicalIso`, `graphPLRefineToOverIso`), the ordinary one-skeleton comparison `incidenceGraphUniformMapperIso`, `mapperOneSkeletonGraphPLIso` and `mapperOneSkeleton_connected_iff` | Input is a continuous map and an indexed target family. Coverage and multiplicity are explicit hypotheses where used. The MultiNerve Mapper is the multinerve of the component cover; its projection onto `mapper` is surjective and is an order isomorphism under `IntersectionsPathSubsingleton (componentCover f U)`. Every real number lies in at most two members of the uniform family exactly when `2g ≤ r` (for at least three members and `g < r`); its union is the window `(a, a + n(r − g) + g)` for `0 < g ≤ r`. The graph-PL finite Reeb data need no covering hypothesis; closed-level components are classified by `LevelVertex` for finite vertex sets, and inclusion into any level window is bijective on components. The star and gap comparison assumes every vertex height is a level of the critical list, while the Mapper comparison is at member-adapted levels. The refinement comparison assumes the coarser list covers the vertex heights. Constructibility at the specified critical list and the corresponding cosheaf identification assume a list covering the vertex heights and `V : Type`; constructibility at a noncovering list can fail (fixture D5). The Reeb quotient identification assumes a covering list, which cannot be dropped (fixture R6); the slice statements use `V : Type`, while the list-free corollaries need no list. The presentation map is injective for every list, while the homeomorphism assumes a covering list (fixture K5). Closed levels are compact and locally path-connected for finite vertex sets. The slice statements use `V : Type`. Finiteness is conditional; tower identity/composition are supplied coherence data. These constructions are noncomputable theory, not an executable Mapper implementation. The one-skeleton isomorphism assumes `2g ≤ r` and fails without it (fixture M5). |

For a small dependency footprint, import an individual implementation module rather than
the whole area. Generic simplicial contiguity depends only on the simplicial vertex-map
API; nerve-specific contiguity is owned by `TDA.Topology.NerveContiguity`. Mapper Tower
consumes that Topology theorem. This removes the previous Simplicial-to-Topology dependency.

Arbitrary vertex maps induce signed maps of the chains and homology over a ring,
with independent source and target orders in a common vertex universe. Collapsed faces
map to zero; injective images retain their permutation signs. Identity, composition and
compatibility with the existing inclusions are strict. Contiguous maps have a signed prism homotopy and induce equal homology maps in every natural degree.
For real-indexed filtrations, `shiftedSimplicialHomologyMap` gives the degree-ε
natural map of a global function, and `multivaluedSimplicialHomologyMap` gives the canonical
map of a total relation satisfying the nonempty finite-image face condition. It equals the
map of every subordinate function, over any ring and for every real ε. Its target evaluates
at t + ε and agrees with `RealShift.shift` for nonnegative ε. Relational images may be
infinite; totality covers ambient ghosts while face tests preserve support.
Native relation composition is first C then D. Their canonical homology maps
compose with degree ε + δ, using the second component at t + ε and the canonical
index transport `(t + ε) + δ = t + (ε + δ)`. The specialized comparison agrees with
`RealShift.compIso` for nonnegative degrees. Total subrelations induce the same canonical
transformation. Two total ε-simplicial relations whose native round trips contain the
identities give a `RealInterleaving ε`, with the canonical maps as its fields;
a relation and its converse specialize this construction. Subrelation invariance permits
all real degrees, while interleavings use finite nonnegative ε. See
[signed simplicial vertex maps](math/simplicial-vertex-maps.md).

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
the ranks of all structure maps, including composites. The canonical object is
the interval multiset; the chosen summands and isomorphism are not canonical. See
[finite interval decomposition](math/finite-interval-decomposition.md).

`FiniteLine.moduleOfAdjacent` constructs finite persistence from adjacent linear
maps, and its path-category equivalence identifies equioriented finite-line
representations with `PModule`. `MatrixSequence.toPModule` accepts rectangular
transition matrices with target rows and source columns; its morphisms extend
adjacent commuting squares to all structure maps. Supplied bases give genuine
natural coordinate isomorphisms, basis-independent barcodes, and the existing
finite decomposition. A zero-initial padded sequence can also be extended across
an explicit real critical grid, retaining its original endpoint values and a
constant final cell. These are theory adapters, not executable extraction.
See [finite representations](math/finite-representations.md).

`FiniteBarcode.monoEmbedding` takes a natural transformation of these finite modules
whose components are injective and constructs an embedding of their canonical barcode
occurrences. It preserves each observed death and bounds the target birth by the source
birth. At each death it pairs equal ordinals in birth/index order, retaining duplicates;
the embedding respects identities and mono composition. Its count comparison uses image/kernel injections, with a separate terminal-image case. See
[finite-chain mono embeddings](math/finite-mono-matching.md) for the endpoint conventions,
proof and rank-domination boundary.

For a monotone `theta : Fin s →o Fin s` with `i ≤ theta i`, `TranslationTrivial`
means vanishing of the maps `i → theta i`. `finiteCokernel` is the categorical
cokernel; its shortness is proved equivalent to a target-image inclusion.
Under this shortness condition, the canonical mono embedding satisfies
`birth(target) ≤ birth(source) ≤ theta(birth(target))` and uniquely covers every
target bar with `theta(birth) < death`. Its shifted-prefix comparison uses vector lifts and a separate terminal-image case. See
[quantitative mono matchings](math/finite-mono-translation.md) for the general finite
translation extension and the still unformalized real-grid connection.

`FiniteBarcode.epiEmbedding` takes a componentwise surjective transformation
`p : M ⟶ N` of the same finite modules and embeds target barcode occurrences back into
source occurrences. It preserves birth, bounds the target bar's death by the corresponding
source bar's death, and pairs equal ordinals in descending-death/original-index order at
each birth. Identities and epi composition give identity and contravariant composition
laws. Its count comparison uses image-quotient surjections, with a separate
initial-stage image case. See [finite-chain epi embeddings](math/finite-epi-matching.md).

For an arbitrary transformation `f : M ⟶ N`, `finiteImage f` constructs its range-valued module and natural epi–mono factorization. `FiniteBarcode.inducedMatching`
embeds precisely the source occurrence labels selected by the epi embedding into the
target labels via their unique intermediate image occurrences. Its Option-valued
`inducedMap` exposes the partial injection on all labels, with exact domain/range,
qualitative endpoint order and an equivalence between image occurrences and matched pairs.
It specializes to the existing mono/epi correspondences and the identity matching;
composition laws apply to monos and epis. See
[finite induced matchings](math/finite-induced-matching.md).
`finiteKernel` is the categorical kernel, with evaluated component-kernel
fibers and finite dimensionality derived from the source. Its theta-shortness
gives shifted same-birth survival counts, canonical epi death bounds and unique
long-source coverage. These estimates and the mono/cokernel bounds transfer through
the image to the existing induced matching, with independent kernel and
cokernel translations. See
[quantitative finite induced matchings](math/finite-quantitative-induced-matching.md)
for terminal endpoint extension, hypotheses and the general finite-translation scope.

`FiniteConstructible.reconstructionIso` reconstructs a real-indexed module from a finite
chain of critical samples preceded by a zero stage. It uses left-closed/right-open strata,
a zero left tail and structure-map isomorphisms within each stratum; the
final tail may be nonzero. The reconstruction works over any ring with independent
module-carrier universe and no finite-dimensionality assumption. It supplies both natural
transformations and their inverse identities. See
[finite-stratum reconstruction](math/constructible-modules.md).

`FiniteConstructible.commonGrid` constructs a refinement from a sorted union of
critical values. Constructibility survives refinement and positive-evaluation
shift on the grid `c_i-ε`. `moduleDiagram_refinement` proves equality of real endpoint
diagrams, deriving finiteness at added critical values from the original ones and
retaining duplicate bars and essential tails. See
[common grids and diagram invariance](math/constructible-refinement.md).

`IsConstructible.kernel` and `IsConstructible.cokernel` prove constructibility of
categorical defects on a shared grid. `interleaving_critical_defects`
constructs that grid and derives finite sampled defect shortness from a real interleaving, using natural sampling comparisons and within-cell cancellation.
See [constructible defects and critical sampling](math/constructible-defects-sampling.md)
for the rounded translation, terminal observation and coefficient scope.

`moduleDiagram_shift` proves that positive evaluation translates the
native shifted-grid diagram by −ε; its refinement version derives finiteness
at added observations. Finite and essential occurrence equivalences return
shifted target labels by +ε, and the complete matching of a diagram with its
own shift is constructed with its endpoint and cost bounds proved. The target
untranslation operation is available for existing occurrence matchings. See
[real shift diagrams and occurrence untranslation](math/constructible-shift-diagrams.md)
for multiplicities, boundary conventions and the target-return operation.

`FiniteConstructible.inducedOccurrenceMatching` transports the sampled
finite induced partial injection to real finite and essential occurrence labels.
Real kernel/cokernel annihilation gives exact endpoint and unmatched-length
bounds, unique coverage of strictly long finite bars and a total essential
equivalence. `interleaving_shifted_induced_matching` derives these bounds at `2ε`
from an interleaving on possibly different grids, into the translated target
`D_N−ε`. No mesh error or supplied matching is used. See
[real induced occurrence matchings](math/real-induced-matchings.md). `interleavingMatching` returns the target labels by +ε and
`interleavingMatching_cost_le` proves cost at most ε.

`FiniteConstructible.barcodeRealizationIso` connects this reconstruction to finite
decomposition and `RealBarcode.realize`. It requires a coefficient field and carrier in
the same universe, with finite-dimensionality only at the critical fibers. The sampled
zero stage produces no bars; `Fin.succ` restriction preserves all remaining
occurrences before `ofIndexBars` assigns the real finite endpoints and essential tails.
The result is a natural isomorphism to the fixed grid's endpoint barcode, with
duplicate summands retained. See [real barcode realization](math/real-barcode-realization.md).

`RealShift` constructs real shifts and transitions over any ring, with natural unit
and composition identifications satisfying the coherence equations.
`RealInterleaving` contains natural maps and both double-shift identities;
zero-interleaving witnesses correspond to natural isomorphisms, and interleaving
with zero is equivalent to a zero double-shift structure map. Its interval examples
use nontrivial field coefficients. See [real interleaving witnesses](math/real-interleavings.md)
for the finite nonnegative parameters and witness equations.

`TDA.Persistence.ModuleScaling` defines positive scaling of real persistence modules by
reindexing along `t ↦ c⁻¹ * t`. `PModule.scaleShiftIso` compares scaling with shifts,
`RealInterleaving.scale` transports witnesses with parameter `Real.toNNReal c * ε`, and
`nonempty_realInterleaving_scale_iff` together with `realInterleavingDistance_scale` gives
the exact `ENNReal.ofReal c` distance law over every ring, including `⊤`. See [positive
scaling](math/real-interleavings.md#positive-scaling).

`RealInterleaving.kernel_transition_eq_zero` and `cokernel_transition_eq_zero`
prove that either comparison morphism has categorical kernel and cokernel
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

`RealBarcode.matchingInterleaving` constructs a witness between the realizations
of two positive finite diagrams from an existing occurrence matching with cost at most ε.
Matched finite bars use endpoint bounds; unmatched bars have length at most `2ε`,
including equality; essential occurrences use the matching's total equivalence.
Multiplicity, structure maps and ε=0 are retained. See
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

`TDA.Persistence.ConstructibleScaleBarcode` transports finite critical grids and module
diagrams under positive scaling: `FiniteConstructible.scaleGrid`,
`FiniteConstructible.IsConstructible.scale`, and `FiniteConstructible.moduleDiagram_scale`
give the diagram formula, while `FiniteConstructible.bottleneck_moduleDiagram_scale` gives
its bottleneck consequence. `TDA.Persistence.SublevelScaling` identifies scaled filter
sublevel modules with `PModule.scale`, proves the ring-level distance law, and shows that
`moduleDiagram_sublevelModule_scale` agrees with `dgm_scale`; it also provides
`logModule_scale_shiftIso` for `1 ≤ c`. See [positive scaling](math/real-interleavings.md#positive-scaling).

`dgm` is the diagram of simplicial sublevel homology, with multiplicities retained,
half-open finite intervals, omitted zero-length value bars and essential deaths at `⊤`.
The graded reduction adapter reaches this diagram through homology and natural
maps; `nonempty_facePrefixHomologyIsoPivotBarcode` exposes its natural interval
isomorphism. The original boundary differential is distinct from its reduced matrix.
See [sublevel diagrams](math/finite-sublevel-diagram.md) and
[reduction](math/persistence-reduction.md).

`bottleneck_dgm_le_faceSupDifference` proves finite-complex real-filter stability over a
field, including pairing changes and closed interpolation endpoints. This is the
library's finite combinatorial counterpart of the geometric stability theorem; it does
not supply a comparison with singular homology of general tame functions.

`TDA.Filtration.FilterFunction.map` reparametrizes a filter along an order embedding
φ : α ↪o β, and `TDA.Persistence.Diagram.map` maps births and finite deaths of a diagram
along φ while fixing the essential top. Sublevels correspond at every source threshold, and
at every target threshold for an order isomorphism; `dgm_map` identifies the diagram
of `f.map φ` with `(dgm k f n).map φ` for every field, degree and finite complex.
`FilterFunction.scale` and `Diagram.scale` are the cases x ↦ c x with c > 0, and
`bottleneck_scale` multiplies the bottleneck distance of any two real diagrams by c,
including the value ⊤ for unequal essential counts. The merged translations are the maps
along x ↦ x + c. Monotone non-injective and order-reversing maps are not covered. See
[the conventions, proofs and fixtures](math/filter-reparametrization.md).

`TDA.Persistence.SublevelDiagramMonotone` adds the monotone, possibly non-injective
reparametrisation law `dgm_points_map_of_monotoneOn`. It maps births and deaths through
`φ : α → β` and filters out points that become diagonal, while essential deaths remain at
`⊤`; its hypotheses are monotonicity on `Set.range f.value` and
`g.value s = φ (f.value s)`. The same module proves
`finrank_sublevelHomology_eq_countP`, `not_isZero_sublevelHomology_of_mem_dgm` and
`dgm_points_eq_zero_of_isZero`. These are library extensions of the face-template and
rank-diagram APIs.

The `SublevelDiagramRegularity`, `SublevelLossDerivative` and `SublevelLossHessian` APIs use
ordered local representatives with explicit hypotheses on face values and loss lifts.
The full lift retains tied finite pairs, including their diagonal coordinates; the
Hessian includes both chain-rule terms. These are local results on the declared
neighborhoods, not a claim of global smoothness at arbitrary pairing changes. See
[local regularity](math/diagram-calculus.md) and
[loss Hessians](math/sublevel-loss-hessians.md).

For general regularity, use `LocalCrDiagramLift r`, `DiagramContDiffAt r`,
`CrThroughAllRepresentatives r` and the face-template APIs `fixedFaceLift_contDiffOn_cr`
and `fixedFaceCrLift`. The C¹/C² lift structures and `fixedFaceC1Lift` /
`fixedFaceC2Lift` remain convenient inputs to derivative and Hessian theorems.
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

## Compatible lifts and algebraic sums over the reals

`TDA.Persistence.CompatibleSections` constructs compatible sections of a persistence
module on any real subset when its transition maps are surjective. A section can
pass through any prescribed fiber vector. The proof uses a decreasing sequence
with a point below every index, together with the natural-number inverse-limit
theorem, without assuming finite underlying fibers. Open endpoints, singletons
and unbounded subsets are allowed.

`TDA.Persistence.CutSubspaces` uses cuts, which partition the parameter order into
a lower part and an upper part. Two cuts determine a possibly empty support,
which is an interval when nonempty; their image/kernel subspaces encode birth
and death conditions. For a pointwise finite-dimensional
module, the required surjectivity is derived for these subspaces. The module
transports their quotients isomorphically and chooses one global section complement
whose evaluations complement the corresponding lower subspace at every interval
point. The compatible lift and complement are constructed from finite dimension.

`TDA.Persistence.AlgebraicFamily` realizes families by algebraic direct sums. Its
canonical comparison with the existing `RealBarcode.familyModule` product is a
natural isomorphism when finitely many fibers are nonzero at each parameter.
Pointwise finite dimension of a direct-sum representation implies this local
finiteness, and only finitely many occurrences meet a finite observation list.
The index family may be uncountable. The full interval decomposition and equality
with finite-observation barcodes remain open in [the decomposition contract](https://github.com/uda-lab/tda-lib/issues/506).

## Metric input and Rips diagrams

`TDA.Filtration.Rips` takes explicit metrics on a fixed finite labelled vertex type,
using the full complex of nonempty faces and their diameters. Singletons have value
zero, the empty face is excluded, and stages below zero are empty. Sublevels are closed
Rips complexes with diameter time. `pairwiseDiscrepancy` is the maximum absolute
distance-matrix difference, with empty maximum zero.

`TDA.Persistence.Rips.bottleneck_dgm_le_pairwiseDiscrepancy` bounds the diagrams
in every degree by that discrepancy. For V : Type u it requires `LinearOrder V`,
`Fintype V`, and a coefficient field k : Type u, retaining existing multiplicity and
essential-bar semantics. This noncomputable consumer of finite-face stability covers
the fixed labelled carrier. See [the construction, proof and source scope](math/rips-metric-stability.md).
`RipsRelationInterleaving` compares different genuine metric label types using a native
relation and transpose total on both ambient sets. An absolute pairwise distortion bound ε
gives canonical homology maps forming `RealInterleaving ε` over any ring, with
exact forward/backward field formulas and an interleaving-distance bound. The geometric
finite-face theorem requires no totality or finite image; same-antecedent pairs remain
in the distortion premise. For finite ordered label types and a field, each Rips
filter supplies its own critical grid, giving a full sublevel-diagram bottleneck bound ε.
`RipsGromovHausdorff` selects a closed Hausdorff correspondence from isometric finite
images and uses mathlib's optimal GH coupling. It proves the full sublevel-diagram bound
`dB ≤ 2 dGH`, ambient Hausdorff sampling bounds and convergence to a fixed finite
target. The
order-free `Rips.diagram` accepts finite metric spaces and a field in independent
universes; `diagram_eq_dgm` identifies it with the existing diagram for every
auxiliary order. Finite samples of a common possibly infinite target are compared
only through their finite diagrams. General totally bounded/q-tame diagram existence
remains separate. See [metric-input stability](math/rips-metric-stability.md).

`TDA.Persistence.QTame` defines `PModule.QTame`: every structure map across
`a < b` has finite-dimensional image over the coefficient field.
`TDA.Persistence.RipsQTame` proves `Rips.qTame_of_totallyBounded` for the
existing closed diameter Rips homology of any totally bounded metric space,
over every field and in every degree. A finite net and the relation-interleaving
law give the actual factorization through finite-dimensional homology.
Empty spaces and negative source times are included. The auxiliary vertex
order is arbitrary; `sublevelModuleIsoOfIsometryEquiv` supplies natural
isomorphisms under isometric relabelling without order preservation.
The infinite compact unit interval is a checked example: its strict maps have
finite-dimensional images, while its unreduced H₀ fiber at zero is
infinite-dimensional. This result supplies q-tameness; locally finite diagrams
and their algebraic stability require separate foundations. See
[the finite-net proof](math/rips-metric-stability.md#totally-bounded-spaces).

## Ambient Čech complexes

`TDA.Filtration.Cech` defines the closed Čech complex of labelled points p : V → X in a
pseudometric space as the nerve of closed balls, with ball radius as time. It proves
Rips_r ⊆ Čech_r ⊆ Rips_{2r} in pairwise form for arbitrary labels, and in Rips-sublevel
form for a label metric agreeing with the ambient distances. The radius filter on the full
complex satisfies rips/2 ≤ čech ≤ rips. Its sublevels contain the Čech complexes, with
equality when X is proper. See [the conventions, proofs and fixtures](math/cech-rips-sandwich.md).

`TDA.Persistence.SublevelInterleaving` turns pointwise inclusions of simplicial filtrations
into morphisms of homology persistence modules, `inclusionHom`, whose components are the
homology inclusions. Real filtrations with F t ⊆ G (t + ε) and G t ⊆ F (t + ε)
give a `RealInterleaving ε`, `inclusionInterleaving`, with both double-shift
equations proved. For filters within ε face by face, `sublevelInterleaving` interleaves the
sublevel modules, and `realInterleavingDistance_sublevel_le_faceSupDifference` bounds their
distance by the largest face difference. `TDA.Persistence.CechRipsInterleaving` reindexes
along exp: a sandwich g ≤ f ≤ c · g with 1 ≤ c gives a `logParam c`-interleaving of the
log-scale modules, and `Cech.ripsCechLogInterleaving` is the log 2 case for Rips and Čech,
over every ring and in every pseudometric ambient. At radius level, `Cech.ripsToCech` and
`Cech.cechToRips` factor the doublings Rips_r ⊆ Rips_{2r} and Čech_r ⊆ Čech_{2r} for every
real r; these are structure maps only for r ≥ 0. The log-scale results make no diagram or
bottleneck statement in degree 0. See [the proofs, fixtures and scope](math/cech-rips-interleaving.md).

`TDA.Persistence.SublevelConstructible` proves that the sublevel module of a real filter on a
finite complex is finite-constructible on the critical values of the filter, over every ring,
`sublevelModule_isConstructible`. Over a field its critical fibers are finite-dimensional, and
`moduleDiagram_sublevelModule` identifies its module diagram on that grid with `dgm k f n` by
definition; `sublevelModuleRealizationIso` realizes the module from the diagram. For two
filters on the same complex, `bottleneck_dgm_eq_realInterleavingDistance` equates the
bottleneck distance of their diagrams with the interleaving distance of their sublevel
modules, for unrelated critical grids, and `nonempty_sublevelInterleaving_iff` is the
witness equivalence at every finite parameter. `bottleneck_dgm_le_faceSupDifference_algebraic`
rederives finite-filter stability from the inclusion interleaving, independently of the
face-order proof, and essential multiplicities agree. The scaling bridge in
`TDA.Persistence.SublevelScaling` adds the corresponding module and diagram identities.
The sublevel-constructibility results make no log-scale or cross-complex comparisons; the scaling
bridge's log-scale statement is `logModule_scale_shiftIso` for `1 ≤ c`, and
`TDA.Persistence.LogScaleScaling` adds the `logDgm` translation formula
`logDgm_scale` for every `0 < c`, the shift for `c ≤ 1`, and scale invariance of log-scale
bottleneck and interleaving distances. See [the proofs, fixtures and scope](math/sublevel-constructibility.md).

`TDA.Persistence.LogScaleDiagram` gives log-scale modules a diagram in degrees n ≥ 1. A filter
is `PositiveOnEdges` when every face with at least two vertices has positive value; Rips
filters of a metric and Čech filters with a compatible label metric are, by
`positiveOnEdges_rips` and `Cech.positiveOnEdges_cech`. `logGrid f` enumerates the logarithms
of the positive critical values, and for 1 ≤ n and positive filters
`logModule_isConstructible` proves the log-scale module finite-constructible on it, over every
ring. `logDgm k f n` is its module diagram over a field. For two positive filters on the same
complex, `bottleneck_logDgm_eq_realInterleavingDistance` is the isometry at log scale;
`bottleneck_logDgm_le_log` bounds the bottleneck by log c for a sandwich g ≤ f ≤ c · g, and
`Cech.bottleneck_logDgm_rips_cech_le` bounds the log-scale Rips and Čech diagrams by log 2 in
every pseudometric ambient. `not_isConstructible_logModule_zero` shows that in degree 0 the
module is constructible on no finite grid once a vertex has nonpositive value. In degrees
`n ≥ 1` under `PositiveOnEdges f`, the comparison API gives
`(logDgm k f n).map expEmb = dgm k f n`; the map is along the strictly increasing exponential,
not along `log`, which is not an order embedding of `ℝ`. No degree-0 log-scale identity,
diagram or bottleneck value is stated. See [the proofs, fixtures and scope](math/log-scale-diagrams.md).

`TDA.Persistence.LogScaleDiagramComparison` contains the supporting
`moduleDiagram_reindex_map`, which identifies module diagrams after reindexing along an order
embedding when the transported fibers are finite-dimensional; the exponential embedding `expEmb`
(with `expEmb_apply` and `expEmb_toOrderHom`); and the positive grid `positiveGrid` (with
`positiveGrid_apply`, `mem_range_positiveGrid_iff` and `refines_positiveGrid`). It proves
`sublevelModule_isConstructible_positiveGrid`,
`logDgm_map_exp`, `logDgm_points_eq_map_log`, `dgm_birth_pos` and `dgm_death_pos`; the latter
four results require `1 ≤ n` and `PositiveOnEdges f`, while constructibility on the positive
grid has the same hypotheses and works over a ring. The comparison and fixture results are
library extensions with no cited source theorem.

`TDA.Persistence.TriangleCechRipsExamples` computes the explicit triangle Čech and Rips
diagrams in degrees 0 and 1 at radius scale and in degree 1 at log scale over `ZMod 2`, the
exact bottleneck values including `triangle_logBottleneck_one` = `¼ log (5/4)`, and the
right-triangle negative control; see [the triangle fixtures](math/log-scale-diagrams.md).

`TDA.Filtration.CechDisplacement` compares two labelled families p, q : V → X in one
ambient space label by label. Moving the points of a face by at most ε changes its Čech
value by at most ε; the closed-ball radius estimate also needs ε ≥ 0 for the empty set.
For a finite V, `displacement` is the largest label-wise distance with empty maximum
zero, and the Rips pairwise discrepancy of distance-compatible label metrics is at most
twice it. `TDA.Persistence.Cech.bottleneck_dgm_le_displacement` bounds the Čech
diagrams in every degree by the displacement, and
`bottleneck_rips_dgm_le_two_mul_displacement` bounds the Rips diagrams by twice
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

`TDA.Persistence.CechSupNormDiagram` turns that value identity into diagram identities. The
sup-norm Čech filter is the Rips filter scaled by 2⁻¹, so the Čech diagram is the
Rips diagram with every finite coordinate halved, in every degree and over every
field, and the Čech bottleneck distance is half the Rips one. With Rips metric stability the
Čech diagrams are within half the pairwise discrepancy. The hypotheses are the merged
distance-compatibility conditions, with any finite ι and no properness; the line ℝ has the
same identities. See [the scaling law and fixtures](math/filter-reparametrization.md).

`TDA.Persistence.CechRipsAdditive` proves `bottleneck_self_scale_le`, the critical-value
coordinate lemmas `mem_criticalValues_of_mem_finitePart_dgm` and
`mem_criticalValues_of_mem_essentialPart_dgm`, and
`TDA.Filtration.Rips.filter_value_le_diameter_univ`. It then proves
`Cech.bottleneck_rips_cech_dgm_le_half_diameter` in the sup-norm product and
`Cech.bottleneck_rips_cech_dgm_le_half_diameter_real` on the line, together with the
embedding, kernel-value and finite-part image consequences in the product. See [Rips versus
Čech of one configuration](math/cech-weighted-kernel-images.md#rips-versus-čech-of-one-configuration).

`TDA.Persistence.CechRipsLogScaleConsumers` composes the log-scale bottleneck bounds with the
weighted-kernel and persistence-image consumers, including exact-bottleneck and `log 2` bounds
in a general pseudometric ambient.

`TDA.Persistence.TotalPersistence` and `TDA.Persistence.TotalPersistenceRipsCech` define total
persistence, finite-bar face-count bounds, and size-dependent Rips and Čech consequences; their
worked fixtures are in `TDA.Persistence.TotalPersistenceRipsCechExamples`.
`TDA.Simplicial.Cone` proves apex-cone acyclicity, and `TDA.Persistence.EssentialVanishing` proves
the essential-count identity, vanishing in degree `n ≥ 1` on the full complex, and size-uniform
consumers; their fixtures are in `TDA.Simplicial.ConeExamples` and
`TDA.Persistence.EssentialVanishingExamples`.

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
excluded from this separation result. No quotient metric instance is supplied.
See [the matching minimum and its scope](math/finite-first-order-matching.md).

`TDA.Persistence.FiniteBoundaryTransport` admits every nonnegative real matrix with
row and column sums at most one. Residual unit mass goes to or comes from the boundary.
`finiteFirstOrderBoundaryTransportCost_eq_matchingCost` identifies this finite real
optimization with the existing matching minimum, using cost-preserving boundary
augmentation and the pinned mathlib Birkhoff decomposition. An incidence plan attains
the minimum; fractional optima can coexist with it. Empty formulas and reindexing are
included. Equality with all Borel/Radon couplings remains outside the API.
See [finite boundary transport](math/finite-boundary-transport.md).

## Finite real-exponent matching and transport costs

`FinitePMatchingCost` and `FinitePBoundaryTransport` extend the finite optimization to
real matching exponents p≥1 with fixed maximum ground norm. Distances are powered
before summing; real transported and residual masses stay linear. Powered and rooted
matching/transport optima agree and are attained; empty formulas, occurrence reindexing
and p=1 compatibility are included. `FinitePMatchingCostLaws` proves sharp rooted
composition, self cost, symmetry, triangle inequality and positive-lifetime separation
by value-preserving occurrence equivalences. `FinitePBoundaryTransportLaws` transfers
these laws to the real-plan optimum. `FinitePMatchingCostBottleneck` bounds finite-part
real-p matching and boundary transport by N^(1/p) times a finite full bottleneck,
where N counts both finite occurrence sets. Explicit radius and cardinality-budget forms
are included. `FinitePFilterStability` applies these bounds to sublevel diagrams
using face-value perturbations, without a fixed pairing; essential bars remain outside
the finite-part transport cost. All-Radon-coupling equality and quotient/metric
instances remain outside this API. `FinitePBottleneckLimit` proves the reverse
bottleneck comparison and convergence of both optimized costs as the real exponent
tends to infinity, for fixed diagrams with empty essential parts. It includes the
empty-input case and both real and extended nonnegative real limits.
`FinitePBottleneckUniformLimit` proves a common error bound
|dₚ−B|≤((max(1,m))^(1/p)−1)R when both essential parts are empty, the total
finite count is at most m and the full bottleneck B is at most R≥0.
Both rooted optima converge uniformly in real p to B on that entire budget
class, including empty inputs and R=0, with no topology on diagrams required.
`FinitePCommonEssentialBottleneck` gives the same error and uniform limits when
the entire essential-birth multisets agree, retaining values and multiplicities.
The common multiset may vary across pairs without a count or birth-range budget.
These remain the existing finite-part costs; no essential p-cost is introduced.
Equal essential cardinalities alone do not suffice.
`CechFinitePBottleneckUniformLimit` derives the corresponding bounds and uniform
limits for `dgm k (Cech.filter a) n`, n≥1, on a fixed finite label type
under a same-label displacement budget R≥0. The total finite count is bounded
automatically by twice choose(card V,n+2), and both essential parts vanish. The ambient
pseudometric space may be arbitrary; these are infimal-radius sublevel diagrams,
with the existing proper-space specialization identifying closed Čech nerves.
Empty and repeated labels remain allowed.
`CechEssentialBirth` identifies the entire essential multiset of a nonempty Čech H₀ diagram as `{0}`, through the nonzero rank of a vertex
inclusion. `CechFinitePBottleneckAllDegrees` then supplies both error bounds
and both literal input-uniform limits for every natural degree, including H₀.
It derives equality of the essential multisets, the finite-count bound and the
full bottleneck bound from displacement alone, with empty labels and R=0
included. The birth-zero argument uses the library's empty negative tail;
the proper-space closed-nerve comparison is for nonnegative radii. These
real-parameter results leave the H₀ logarithmic left-tail obstruction intact.
`FinitePMatchingCostComparison` proves, for real 1≤r≤s,
dₛ≤dᵣ≤N^(1/r−1/s)dₛ for both optimized matching and real-plan costs, and
their antitonicity on [1,∞). N counts both occurrence families, including empty
ones; separate minimizers are used at the two exponents. These finite library
derivations use unnormalized unit masses and keep the maximum ground norm fixed.
`FinitePCostContinuity` proves continuity on [1,∞) in the real exponent of the
powered and rooted matching and real-plan optima, for fixed families.
The finite-minimum proof includes empty and zero-distance inputs and permits
optimizer changes. Exponent zero remains outside the public continuity domain.
`FinitePCostJointContinuity` proves joint continuity of the same four optimized
values in the exponent and both coordinate families, with fixed finite label
types and the ordinary product/Pi topology. Continuous parameter families with
p≥1 therefore give continuous optimized costs, including through zero costs,
coordinate collisions and changes of minimizing matching.
`FinitePCostSimilarity` proves invariance under
common diagonal translation and homogeneity under nonnegative coordinate scaling,
including zero scaling on raw coordinate families. See
[real-exponent finite transport](math/finite-p-boundary-transport.md).

## Finite real-weight boundary transport

`FiniteWeightedBoundaryTransport` allows arbitrary nonnegative real marginal
masses and splitting between finite labels, retaining both boundary
residuals at the existing maximum ground norm. The full feasible matrix set is
compact, and powered and rooted optima are attained at each real p≥1. Constant
unit masses recover the existing transport API exactly. Symmetry, equivalent
relabelling and weighted diagonal-moment formulas for empty inputs are included.
`FiniteWeightedDiagram` is a finitely supported mass function on the strict
upper half-plane; its transport consumers inherit these results. This
finite weighted model supplies no all-Radon coupling identification or weighted
exponent limit. See [finite real-weight boundary transport](math/finite-weighted-boundary-transport.md).

## Gaussian persistence images

`TDA.Persistence.GaussianKernel` proves normalization and L¹ translation estimates for
the product Gaussian at positive bandwidth σ. `TDA.Persistence.PersistenceImage`
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
`norm_embedding_sub_sq` are statements about the RKHS inner product and norm.
Linear and Gaussian diagram Gram matrices are positive semidefinite for any family of
diagrams. The RKHS norm is not the pixel ℓ¹ norm above; no identification or computable
kernel evaluation is supplied.

`TDA.Persistence.WeightedKernelInjectivity` factors the Gaussian kernel through exponential
characters and Dedekind's linear-independence lemma, proving strict positive definiteness
for injective point families through `posDef_kernel` and `posDef_kernel_family`. It gives
the finite-support `measureEmbedding` and its injectivity and distance-zero
characterization, together with the diagram `weightedMeasure` and the equality theorem
`diagramEmbedding_eq_measureEmbedding`. The diagram characterization
`diagramEmbedding_eq_iff`, its positive-diagram corollary and whole-diagram recovery
identify finite parts with multiplicity under σ ≠ 0 and pointwise positivity of the
finite-point weights. `eq_of_diagramEmbedding_eq` recovers the whole diagram only when
the essential parts are also assumed equal. The hypotheses are σ ≠ 0, not 0 < σ, and
pointwise positivity of the weight at the finite points.

`TDA.Persistence.WeightedKernelIsometry` constructs `KernelWeight.weightIsometry`,
a real linear isometry equivalence for any scalar PSD kernel and nowhere-zero real
weight. Its action on all functions is multiplication by the weight; its inverse
is pointwise division. `upperWeightIsometry` specializes KFH18 Proposition 7 to the
Gaussian on `UpperPoint` (birth < death), with positive weights and every real σ,
including zero. The arctan specialization requires C > 0, with no uniform positive
lower bound on the weight. `weightedUpperDiagramEmbedding` uses the weighted-kernel
RKHS on that domain; its finite-part inner products and pair norms agree with the
existing full-plane `diagramEmbedding`, even without weight positivity. Multiplicity
is retained and essential bars are omitted. No full-plane restriction isomorphism
or pixel-norm identification is asserted.

`TDA.Persistence.GaussianFeature` proves that unit vectors with inner product
`exp(-r² / (2s²))` are at distance at most `|r| / |s|`. It also builds the Gaussian RKHS
`GaussianSpace τ E` of any real inner product space with kernel functions
`gaussianFeature`. `TDA.Persistence.WeightedKernelStability` bounds
`‖featureAt σ p - featureAt σ q‖` by the Euclidean distance over `|σ|` and by `√2 / |σ|` times the maximum
norm. The embedding difference is bounded by `stabilityConstant σ A B = 2A + √2·B/|σ|`
times the total finite cost of every partial matching and times
`finiteFirstOrderMatchingCost`. For positive diagrams with finite bottleneck, it is
bounded by `stabilityConstant σ A B` times the occurrence count times the bottleneck
distance. `gaussianDiagramKernel` is the `(k,w)`-Gaussian kernel. Its feature map
`diagramGaussianFeature` and its kernel values are `1/|τ|`-Lipschitz in the embedding,
with matching-cost and count-times-bottleneck corollaries. No bandwidth hypothesis is
assumed. See
[the conventions, proof route and source mapping](math/weighted-kernel-embedding.md).

`TDA.Persistence.ArctanWeight` defines `PersistenceImage.arctanWeight C hC`, the weight
`arctan (C · max pers 0)` in `Weight C (π / 2)` for `0 ≤ C`. It equals KFH18's
`arctan (C · pers)` when birth ≤ death. `WeightedKernel.stabilityConstant_arctan` evaluates
the constant as `2C + √2·π/(2|σ|)`. The arctan corollaries give the embedding bounds against
the finite first-order matching cost and count-times-bottleneck, and the same two bounds
for `(k,w)`-Gaussian kernel values. See
[the weight, constant and boundaries](math/arctan-weight-rips-kernel.md).

`TDA.Persistence.ArctanPersistenceImage` evaluates the persistence-image constant at the
arctan weight as `PersistenceImage.stabilityConstant_arctan`, `2C + 3·√(π/2)/σ`. It gives the
arctan image bounds against the finite first-order matching cost and count-times-bottleneck,
`PersistenceImage.finiteDiagramImage_eq_sum` and the arctan Rips image consumer
`Rips.norm_finiteDiagramImage_sub_le_pairwiseDiscrepancy_arctan`. The image items keep
`0 < σ`. See [the constant and boundaries](math/cech-weighted-kernel-images.md).

## Distance matrices to finite Rips images

`PersistenceImage.finiteDiagramImage` applies the Gaussian image to a diagram's finite
occurrences, retaining multiplicity and omitting essential bars. For positive diagrams
with finite full bottleneck β, its pixel ℓ¹ error is at most C (N_D+N_E) β, where N_D,N_E
count finite occurrences and C is the existing PI coefficient. The finite bottleneck
condition is explicit because `ENNReal.toReal ⊤ = 0`.

`Rips.norm_finiteDiagramImage_sub_le_pairwiseDiscrepancy` specializes this to Rips
diagrams in every degree: error ≤ C (N_D+N_E) δ for maximum pairwise metric discrepancy δ.
It inherits the same finite ordered carrier and field assumptions as the Rips API, with
no new cardinality/genericity hypothesis. These noncomputable APIs give a count-dependent
certificate, with essential bars still present in the bottleneck comparison. See
[the definitions, bridge and exact scope](math/rips-persistence-images.md).

`TDA.Persistence.RipsWeightedKernel` proves `Rips.bottleneck_dgm_lt_top` and
`Rips.toReal_bottleneck_dgm_le_pairwiseDiscrepancy` for Rips diagrams. It bounds
the weighted-kernel embedding difference by `stabilityConstant σ A B (N_d+N_e) δ`, and
the second-level Gaussian feature difference and kernel-value change against an arbitrary
fixed diagram by the same quantity over `|τ|`. Arctan specializations carry the explicit
constant. No bandwidth sign hypothesis is assumed. See
[the composition](math/arctan-weight-rips-kernel.md).

`TDA.Persistence.CechWeightedKernel` and `TDA.Persistence.CechPersistenceImage` give the
same consumers for Čech diagrams of labelled configurations `p q : V → X` in one
pseudometric space. `Cech.bottleneck_dgm_lt_top` and
`Cech.toReal_bottleneck_dgm_le_displacement` bound the full bottleneck by the same-label
displacement δ. The embedding, second-level Gaussian feature, kernel-value and finite-part
image differences are bounded by the corresponding constant times `(N_p+N_q) δ`, with
arctan specializations for the embedding, kernel-value and image bounds. No label metric or
distance compatibility is assumed; only the image items carry `0 < σ`. See
[the Čech compositions](math/cech-weighted-kernel-images.md).

`TDA.Persistence.CechSupNormWeightedKernel` and
`TDA.Persistence.CechSupNormPersistenceImage` give the sup-norm consumers for any finite
ι and distance-compatible label metrics d, e. With the nonnegative weight bounds
`0 ≤ A`, `0 ≤ B` and a `PersistenceImage.Weight A B`, the embedding, feature, kernel-value
and image bounds use the corresponding constant times `(N_p+N_q)` times half the pairwise
discrepancy; the image items alone additionally require `0 < σ`, measurable pixels and
pairwise disjoint pixels. The line has the bottleneck form
`Cech.bottleneck_dgm_le_half_pairwiseDiscrepancy_real` only. See
[Sup-norm consumers](math/cech-weighted-kernel-images.md#sup-norm-consumers).

## Categorical Mapper and Reeb approximation

`categoricalMapperData` retains components of every nonempty cover intersection.
`categoricalMapperIsColimit` identifies its selected-simplex colimit over a test interval
with `categoricalMapperAssembly`, and `categoricalMapperCocone_map` characterizes the
inclusion-induced interval maps. Finite bounded interval families with finite pullback
component sets give a constructible cosheaf; `categoricalMapperReconstruction` applies the
existing finite real-graph reconstruction equivalence.

For a finite graph-PL input covered on its attained height range,
`geometricInterleavingDistance_mapperReeb_le_retained` bounds the geometric interleaving
distance from `graphPLMapperReconstruction` to the `GraphPL.graphPLReebGraph` by
`retainedCoverResolution`. Empty pullbacks may be removed through
`coverComponentsRetainedIso`; retained intervals contribute their full widths.
`clippedCoverResolution` separately defines the attained-range diameter maximum; it is not
the resolution used by this bound.
`tendsto_geometricInterleavingDistance_mapperReeb` and its `_retained` form permit varying
finite index types and prove convergence for vanishing full or retained resolutions.
`exists_graphPLMapperCover_resolution_le` retains the finite cover and resolution witness;
`exists_graphPLMapperReconstruction_error_le` gives its geometric estimate at every positive error. Horizontal edges, repeated
heights and disconnected graphs are allowed. The construction is abstract theory, with
geometric reconstruction in universe zero; the ordinary Mapper simple graph and executable
algorithms have separate contracts. See [categorical Mapper approximation](math/mapper-reeb-approximation.md).

## Review and extension boundaries

The selected PH claims and their proof-critical bridges received the source-based review
recorded in [PR #220](https://github.com/uda-lab/tda-lib/pull/220). Its distinction between
source matches, checked finite specializations and independently proved extensions is
retained in the mathematical notes. This does not certify every helper or the entire
library against external sources.

Reeb/cosheaf and ordinary Mapper have merged bounded contract implementations, as
recorded in [#34](https://github.com/uda-lab/tda-lib/issues/34) and
[#168](https://github.com/uda-lab/tda-lib/issues/168). The review recorded in
[#215](https://github.com/uda-lab/tda-lib/issues/215) is complete: it is source-based for
the selected PH, Mapper and DMP Reeb claims it covers, and digest-based for the
graph-realization, piecewise-linear and ordering adaptations. The implemented
graph/cosheaf equivalence, component bounds and smoothing results have their stated
finite-graph and constructible-space hypotheses. In the finite real-graph category,
geometric and cosheaf interleavings agree with equal extended distances. Product
thickenings of graph objects and smoothings of constructible cosheaves are
constructible; quotient absorption holds for every constructible real space, without
a general topological-space comparison.

For finite graph-PL input under the stated covering, adaptedness and gap/radius
hypotheses, MultiNerve Mapper finite Reeb data agree with extracted star-and-gap
components and their constructible interval-components cosheaf. The Reeb
quotient of the graph-PL realization is identified with its finite graph realization.
Categorical Mapper reconstruction for finite bounded interval covers of the attained
range has geometric error at most the full width of retained intervals; vanishing
full or retained resolution yields convergence to that quotient. These
results do not identify categorical Mapper with the ordinary Mapper simple graph
or supply an executable component algorithm. Neither Mapper construction claims
a Nerve Lemma or homology selector-independence. The quotient and convergence
claims concern finite graph-PL inputs, not arbitrary higher-dimensional Reeb spaces.

Finite GH–Rips stability and sampling compare full diagrams of finite metric spaces;
the possibly infinite sampling target has no diagram in these results. Finite
weighted boundary transport permits real masses but does not identify all Radon
couplings. Finite-line adapters construct modules over a ring; rectangular
matrix-sequence adapters require a commutative ring. Over a field, both reuse
finite interval classification without computing barcodes over arbitrary fields. Gaussian
C₀ universality and signed-measure separation concern the full birth–death plane;
positive persistence measures require a strictly positive weight and finite weighted
mass. These conclusions do not make finite-pixel images characteristic.

General geometric tame-function PH stability, locally finite diagrams and their stability
for infinite q-tame modules, manifold charts
and executable arbitrary-field decomposition are outside the reviewed PH scope. A first
stable release must state its selected results and limitations; it need not finish every
roadmap extension. This guide describes the current API and does not announce a release.


### Gaussian signed measures and C₀ universality

`TDA.Persistence.GaussianMeasureEmbedding` defines the Banach-valued signed integral
`signedEmbedding` into the existing `WeightedKernel.Space`. Continuity and unit feature norm
prove integrability for every finite signed Borel measure on ℝ². For nonzero bandwidth,
`signedEmbedding_injective` separates these measures, and `probabilityEmbedding_injective`
gives the probability characteristic corollary. `inner_signedEmbedding`,
`signedEmbedding_apply`, `norm_signedEmbedding_sq` and `norm_signedEmbedding_sub_sq` expose
signed pairing, evaluation and kernel energy. `norm_signedEmbedding_le_totalVariation`
controls the mean by total variation. Linearity, Jordan comparison and atomic formulas include compatibility with the existing finite-support and weighted finite-diagram
embeddings. `WeightedKernel.GaussianSpectral.eq_of_gaussian_integrals` supplies the
finite positive-measure separation result on the Euclidean plane.

At nonzero bandwidth, `TDA.Persistence.GaussianUniversality` proves every RKHS function
lies in C₀(ℝ²), with the continuous linear inclusion `rkhsToC0CLM` of norm at most one.
Gaussian sections span a uniformly dense subspace (`gaussian_sections_dense`), and
`denseRange_rkhsToC0` states
C₀ universality of the RKHS. `exists_gaussian_span_approx` exposes uniform approximation
without unfolding density. The bounded-functional representation used by the proof is
`TDA.Topology.C0MeasureRepresentation.exists_finite_regular_measure_sub`.

`TDA.Persistence.WeightedPersistenceMeasure` uses the existing open finite-bar space
`UpperPoint`. At nonzero bandwidth, a measurable strictly positive weight with finite
weighted mass gives `weightedPersistenceEmbedding_eq_iff`, recovering positive measures that
may have infinite original mass. `weightedPersistenceEmbedding_eq_iff_continuous` exposes the continuous
positive-weight Radon consumer. Finite weighted measures are regular; weighted-feature
integrability and the integral comparison are public. `weightedPersistenceEmbedding_finite_occurrences`
connects finite occurrence measures to the existing birth–persistence weighted embedding, and
`countableDiagramEmbedding_eq_iff` recovers locally finite occurrence measures under explicit
summability. `GaussianUniversalityExamples` includes a non-atomic signed Gaussian law with
noncompact support, unequal multiplicities, infinite-total-mass Radon data accumulating at the
diagonal with summable positive weights, cross-bandwidth uniform approximation, and explicit
zero-weight, zero-bandwidth and open-half-plane C₀ failure controls. Essential bars stay separate.
The results provide abstract noncomputable integration and approximation existence, with finite
atomic correctness bridges. They make no finite-pixel persistence-image characteristic claim
or second-level Gaussian universality claim. See [Gaussian measure embeddings and C₀ approximation](math/gaussian-measure-universality.md).

### Greedy sparse Rips geometry and deletion maps

`TDA.Filtration.SparseRips.GreedyNet` constructs a farthest-first permutation of a
finite metric space from a chosen initial vertex. Its prefixes satisfy covering
and separation bounds; insertion radii decrease. The initial vertex has no finite
insertion radius. `threshold_net` gives a closed covering bound and strict
separation at the same threshold, including threshold zero.

For `0 < η ≤ 1/3`, `deletionTime` assigns each other vertex its insertion radius
divided by `η(1−2η)`. The initial vertex's time is `none`, interpreted as survival
forever. `finiteWeight` implements the three specified weight branches.
`relaxedComplex` uses the dissimilarity `dist x y + w x + w y`, including self-pairs.
Its monotonicity and the diameter-scale Rips sandwich are proved. `sparseFiltration`
is the union of closed active complexes over earlier nonnegative scales and is
an ordinary inclusion filtration, extended by bottom at negative scales.

`deletionMap_domination` proves the weighted distance bound for an explicit
projection onto open active vertices. `closedActiveHomologyIso` identifies the
closed active complex with the relaxed complex at one nonnegative scale, in every
degree and over every ring in the existing ordered-vertex chain model, using the
signed prism homotopy.
`unionDeletionHomologyIso` proves the adjacent two-scale union step under an
explicit absence of intervening deletion times. `ClosedBallDoubling.packing_bound`
gives the uniform separated-set bound `Λ^h` from iterated closed-ball covers.
`facesOfDimension_card_le` bounds the number of distinct j-simplices in the full
all-scales carrier by `|P|·(Λ^h)^j`; `skeletonFaces_card_le` bounds its m-skeleton
by `|P|·Σ_{j=0}^m(Λ^h)^j`. Here `2/2^h < η(1−2η)`, and the depth can be chosen
from η alone. The constants are independent of cardinality, metric spread and
maximum scale. `LineSamples.uniform_skeleton_bound` uses one doubling bound of
four at every sample size.

The exported results do not yet identify the full sparse union's persistence module
with the relaxed module. The finite entry-time presentation, diagram approximation,
and full union comparison remain part of
[the sparse Rips theorem](https://github.com/uda-lab/tda-lib/issues/502).
