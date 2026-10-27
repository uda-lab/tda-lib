# Public API and import guide

## Entry points

```lean
import TDA.Persistence -- one ordinary library area
```

Use `import TDA.Library` for the six ordinary areas. `TDA.Probability` is a seventh area with
its own aggregator and pin file; `TDA.Library` does not import it, and its modules are reached
through `TDA.Persistence` or `import TDA`. These entry points exclude the
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
| `TDA.Filtration` / `TDA.Filtration` | `SimplicialFiltration`, support, `FilterFunction`, sublevels, `CompatibleOrder`, `OrderingEquivalent` and order chambers; ambient Čech complexes and relations (`Cech`); greedy sparse Rips (`SparseRips`) and normalized subdivision-Rips (`SubdivisionRips`) bifiltrations | Values belong to nonempty faces. Ordered values are separate from the ambient vertices; compatible enumerations require finite total faces. Support can grow with the index. |
| `TDA.Simplicial` / `TDA.Simplicial` | Face `Chain`, signed `boundary`, square-zero chain complex, inclusion maps, `vertexChainMap`, `simplicialChainMap`, `simplicialHomology` / `simplicialHomologyMap`, finite coordinates and `VertexMap` / `Contiguous` | Signed chains use an ambient vertex order and a ring. Finite-dimensional homology additionally uses a field and finite faces. A vertex map may identify vertices; contiguity is reflexive and symmetric, with composition laws, and is not asserted transitive. |
| `TDA.Persistence` / `TDA.Persistence` | `PModule`, structure maps and reindexing; finite intervals, rank barcodes and decomposition; `Diagram`, `dgm`, reduction, stability and calculus | The functor core needs a ring and a preorder, with independent coefficient/index/carrier universes. Finite decomposition has its narrower field, finite-chain, pointwise finite-dimensional and same carrier/coefficient universe assumptions. Sublevel diagrams and calculus retain their stated vertex-order, finite-face and local-lift hypotheses. |
| `TDA.Topology` / `TDA.Topology` | `CoverFamily`, `Covers`, `Refinement`, `nerve`, `nerveMap`, `nerveMap_contiguous`, `MultiNerveCell`, its `projection` and `multiNerveMap`, path-cover and cosheaf interfaces; measure bifiltrations on the restricted two-copy index (`MeasureBifiltration`), finite-uniform Gromov–Prokhorov witnesses (`FiniteGromovProkhorov`, `FiniteGromovProkhorovWitness`) and the large-face multicover cover (`MulticoverCover`) | An indexed set family need not cover anything; `Covers` states coverage separately. Labels may repeat and members may be empty. A nerve face is nonempty and has a common witness. Refinement selectors need not be injective. A multinerve cell is a path component of a nonempty finite intersection; the projection to the nerve is an order isomorphism only under `IntersectionsPathSubsingleton`. |
| `TDA.Probability` / `TDA.Probability` | Atomic `Coupling`, `iid`, `transportCost`, `wasserstein` and `wassersteinInfinity`; the `pairEnergy` and `pairMaximum` moment bounds; `gromovWasserstein` and `gromovWassersteinInfinity`; the measure forms `MeasureCoupling`, `iidMeasure`, `measureWasserstein`, `measureGromovWasserstein` and their infinity versions | Couplings have exact probability marginals and costs are extended nonnegative infima; no optimizer is assumed. Atomic inputs are `PMF`s, measure inputs `ProbabilityMeasure`s. Gromov–Wasserstein uses the one-half distortion convention. The area contains no diagrams; `TDA.Persistence.RipsSampling` and `RipsSamplingMeasureStability` consume it. |
| `TDA.Reeb` / `TDA.Reeb` | Inverse-image path components, Reeb quotients and comparison maps; interval cosheaves, smoothing, interleavings and extended distance; finite data, graph realizations with the finite tree criteria `isTree_iff_simplyConnectedSpace_realization` and `isTree_iff_contractibleSpace_realization`, the incidence quiver and `incidenceGraph` of finite data with `card_incidenceGraph_edgeSet_le` and `RGraph.cosheafEquivalence`; `thickeningQuotient`, `thickeningQuotientAbsorptionIso`, `thickeningQuotientCompIso`, and `isRGraph_quotient_thickening_of_isConstructibleSpace`; `rgraphToConstructible`, `quotientRGraphAdjunction`, `RGraph.constructibleSmoothing`, `ConstructibleInterleaving`, `ConstructibleInterleaving.equivGeometric`, `constructibleInterleavingDistance`, `constructibleInterleavingDistance_eq_geometricInterleavingDistance` and `constructibleInterleavingDistance_eq_interleavingDistance`; `CylinderPresentation.levelHomeomorph`, `realizationSpace`, `levelPerturbation`, `CriticalValues.translate`, the [vertex-height perturbation API](math/reeb-graph-pl.md#vertex-height-perturbations-of-a-fixed-graph) of graph-PL heights (`abs_plHeight_sub_le`, `edist_ofFun_plHeight`, `edist_ofFun_plHeight_eq_edist`, `vertexHeightInterleaving`, `interleavingDistance_intervalComponents_plHeight_le`, `interleavingDistance_intervalComponents_plHeight_le_edist_ofFun`), and the [level-change stability, range and exact-distance API](math/reeb-geometric-interleaving-equivalence.md#level-perturbations-of-a-fixed-presentation), and translation of interval precosheaves (`OpenInterval.translate`, `translateFunctor`, `translatePre`, `translationInterleaving`, `Interleaving.isEmpty_of_nonempty_of_isEmpty`, `le_interleavingDistance_of_forall_exists_isEmpty`, `intervalComponents_add_const`, `interleavingDistance_intervalComponents_add_const`) with `GraphPL.plHeight_add_const` and `RGraph.geometricInterleavingDistance_eq_zero_of_isEmpty`, and [vertical translation of graph objects](math/reeb-rgraph-translation.md) (`RGraph.translateOver`, `toOverTranslateIso`, `translateRGraph`, `translateRGraphZeroIso`, `translateRGraphCompIso`, `cosheafFunctor_translateRGraph_obj`, `Interleaving.translatePre`, `interleavingDistance_translatePre`, `geometricInterleavingDistance_translateRGraph`, `geometricInterleavingDistance_translateRGraph_self`, `reebRel_add_const_iff`, `quotientTranslateIso`, `thickeningTranslateIso`, `geometricSmoothingTranslateIso`); interval scaling (`OpenInterval.scale`, `scalePre`, `Interleaving.scalePre`, `interleavingDistance_scalePre`, `intervalComponents_smul`, `interleavingDistance_intervalComponents_smul`), and height-controlled map pairs (`HeightMapPair`, `HeightMapPair.natTrans`, `HeightMapPair.natTransSymm`, `HeightMapPair.natTrans_app_mk`, `HeightMapPair.natTransSymm_app_mk`, `HeightMapPair.interleaving`, `HeightMapPair.symm`, `HeightMapPair.ofUniformBound`, `HeightMapPair.interleavingDistance_le`, `HeightMapPair.interleaving_eq_perturbationInterleaving`) | Components are path components of the inverse-image subspace. The tree criteria assume a finite vertex type; realizations of infinite trees are not claimed. General quotient comparison is a natural transformation. The graph/constructible-cosheaf equivalence is scoped to the declared finite real-graph category and value universe `0`. Smoothing and geometric comparisons have separate contracts; geometric thickening composes laxly, by a height-preserving addition map that is not an isomorphism but becomes one after the Reeb quotient, and geometric smoothing of graph objects composes additively, `U_ε U_δ ≅ U_(ε+δ)`; geometric interleavings of graph objects correspond bijectively to interleavings of their component cosheaves, so the geometric and cosheaf interleaving distances coincide and the geometric one satisfies the triangle inequality. Geometric smoothing enlarges along `ε ≤ δ`, geometric interleavings are monotone in the parameter, and every graph object is within geometric distance `ε` of its `ε`-smoothing. Constructible interleavings correspond bijectively to geometric interleavings of the Reeb graphs; the constructible distance equals the cosheaf distance of the interval components of the spaces themselves; zero distance does not give an isomorphism of spaces. The incidence graph forgets parallel edges; edge counts use `Nat.card`. An interval-local component obstruction excludes geometric interleavings whose double-thickening restriction is injective from a nontrivial to a subsingleton value; the parallel loop and the single edge have geometric distance exactly `1/4`. Absorption `ℛ T_ε ≅ U_ε ℛ` holds on all constructible ℝ-spaces; constructibility of `T_ε X` itself is not claimed. Level-change stability fixes the presentation and number of levels; compact locally path-connected pieces supply constructibility. Exact translation distance requires a nonempty realization. Arbitrary continuous perturbations are outside that API. The vertex-height bound controls the piecewise-linear extension of the vertex heights on a fixed graph, not arbitrary continuous functions with the same vertex values. The exact translation distance of interval components assumes a nonempty space and a range bounded below; the identity height of `ℝ` shows the bound is needed. Translation of graph objects is an isometry of the geometric distance; the exact self-translation distance `|c|` assumes a nonempty total space and is `0` otherwise. Scaling on graph objects, translation of the display locale and of Mapper reconstructions as graph objects are not provided. Nonzero scaling multiplies interval-precosheaf distances by the absolute scalar; reflection is an isometry. A `HeightMapPair` supplies continuous maps with height error at most `ε` and composite paths with height deviation at most `2ε`; it is a sufficient interleaving criterion, with no converse, functional-distortion identity or optimality claim for the `2ε` path-deviation allowance. |
| `TDA.Mapper` / `TDA.Mapper` | `ComponentIndex`, pullback component covers, `mapper`, its one-skeleton, `multiNerveMapper` and its projection onto `mapper`, refinement maps including `multiNerveMapperMap`, graph-PL comparison, uniform interval covers (`uniformCover`) with attained-range coverage, the label-set cell equivalence `cellsOverLabelsEquiv` with graph-PL edge cells, height-separating uniform covers (`HeightSeparating`, `exists_heightSeparating_uniformCover`, `range_plHeight_eq_Icc`) with the splitting `cellComponentsEquivSum`, vertex cells (`vertexCellsEquiv`) and the cell classification `uniformVertexCellsEquivLevel`, `uniformVertexCellsEquivSpans`, `uniformEdgeCellsEquivSpans` through `EdgeCrosses` and `EdgeSpans`, finite Reeb data of graph-PL input (`CoversVertexHeights`, `vertexHeightLevels`, `LevelVertex`, `SpanEdge`, `levelEnd`, `graphPLReebData`, `uncoveredEdgeEquivCrossesOfLevel`, `induceComponentsEquivOfEq`) with the star and gap bijections `graphPLStarEquiv`, `graphPLGapEquiv`, their incidence laws `graphPLStarEquiv_map_left`, `graphPLStarEquiv_map_right` and the finite-data isomorphism `graphPLExtractHom`, `graphPLExtractIso`, closed level sets of graph-PL height (`ClosedLevel`, `IsLevelWindow`, `closedLevelComponentsEquiv`, `componentMap_levelInclusion_bijective`, `graphPLReebDataVEquivClosedLevel`), constructibility and the cosheaf identification of graph-PL height (`isConstructibleAt_intervalComponents_plHeight`, `cellGraphIsoOfSameLevels`, `graphPLCosheafIsoOfIso`, `graphPLCosheafIso`, `isConstructibleCosheaf_intervalComponents_plHeight`, `cosheafFunctorGraphPLIso`, `geometricInterleavingDistance_graphPL`), the Reeb quotient of graph-PL height (`compactSpace_realization`, `exists_coversVertexHeights`, `graphPLReebMap`, `graphPLReebQuotientHomeomorph`, `graphPLReebQuotientIso`, `graphPLReebQuotientIsoOfIso`, `intervalComponentNatTrans_graphPLReebMap`, `isRGraph_graphPLReebQuotient`, `graphPLReebGraph`, `graphPLReebGraphIso`, `isIso_intervalComponentComparison_plHeight`, `geometricInterleavingDistance_graphPLReebGraph`), vertex-height stability of the graph-PL Reeb quotient (`heightRange_graphPLReebGraph`, `geometricInterleavingDistance_graphPLReebGraph_le`, `geometricInterleavingDistance_graphPLReebGraph_le_edist_ofFun`, `geometricInterleavingDistance_graphPLReebGraph_le_edist`, and `geometricInterleavingDistance_graphPLReebGraph_le_of_heightMapPair`) with extremal vertex-height lower bounds and exact vertical translation (`sSup_range_plHeight`, `sInf_range_plHeight`, `ofReal_abs_sup'_sub_le_geometricInterleavingDistance_graphPLReebGraph`, `ofReal_abs_inf'_sub_le_geometricInterleavingDistance_graphPLReebGraph`, `geometricInterleavingDistance_graphPLReebGraph_add_const`), the graph-PL realization as a constructible ℝ-space (`barycentric`, `t2Space_realization`, `edgePoint_eq_vertex_iff`, `edgePoint_eq_edgePoint_iff`, `locallyPathConnectedSpace_realization`, `realizationMap_injective`, `LevelPiece`, `levelPieceHomeomorph`, `compactSpace_closedLevel`, `locallyPathConnectedSpace_closedLevel`, `graphPLPresentation`, `graphPLPresentationMap`, `graphPLPresentationHomeomorph`, `graphPLComponentDataIso`, `graphPLReebMap_graphPLPresentationMap`, `graphPLPresentationIso`, `isConstructibleSpace_graphPLOver`, `graphPLReebQuotientIsoOfIso_graphPLComponentDataIso`, `graphPLSpace`, `quotientRGraphFunctor_obj_graphPLSpace`, `overBaseMap_graphPLSpace`, `isRGraph_quotient_thickening_graphPLOver`), and `CoherentCoverTower`, member-adapted MultiNerve Mapper comparison (`LevelsAdapted`, `exists_levelsAdapted`, `labelFace`, `uniformMapperData`, `uniformMapperCellsEquiv`, `uniformMapperIso`), refinement of graph-PL finite Reeb data (`graphPLRefineIso`, `graphPLRefineHom_trans_v`, `uniformMapperCanonicalIso`, `graphPLRefineToOverIso`), the ordinary one-skeleton comparison `incidenceGraphUniformMapperIso`, `mapperOneSkeletonGraphPLIso` and `mapperOneSkeleton_connected_iff`, refinement-induced homology maps `mapperHomologyMap` with `mapperHomologyMap_eq`, `mapperChainHomotopy`, and the persistence module `mapperHomologyPModule` of refinements along a preorder with `mapperHomologyPModule_eq` and `CoherentCoverTower.structureMap_mapperHomologyPModule`, interleavings from cover maps between real towers (`mapperHomologyShiftMap`, `mapperHomologyInterleaving`, `mapperHomologyInterleaving_app_eq`, `realInterleavingDistance_mapperHomologyPModule_le`, `realInterleavingDistance_mapperHomologyPModule_le_add`), the pullback identification `mapperHomologyPModule_pullback`, and perturbation stability along the centred tower (`centredCover`, `centredCoverRefinement`, `centredMapperHomologyInterleaving`, `realInterleavingDistance_centredMapperHomology_le`), height-map-pair bounds for centred Mapper modules (`centredMapperPairVertexMap`, `_natural`, `_comp`, `centredMapperPairHomologyMap`, `centredMapperPairHomologyMapSymm`, `centredMapperPairInterleaving`, `realInterleavingDistance_centredMapperPair_le`, `_ofUniformBound`, `_graphPL_le`); these require supplied component orders but no finiteness, coverage or nonemptiness, and provide no diagram or bottleneck bound for the centred tower itself (the capped centred map-pair bounds are below), no converse, multinerve Mapper, order independence or executable extraction; and finite Mapper barcodes `mapperBarcode` with `mapperHomologyPModule_finiteDimensional`, `mapperBarcode_eq`, `nonempty_mapperBarcodeIso`, `finrank_range_mapperHomologyMap`, `mapperBarcode_eq_iff`, `nonempty_iso_iff_mapperBarcode_eq`, `CoherentCoverTower.finrank_range_simplicialHomologyMap` and the graph-PL face-finiteness instance `GraphPL.finite_mapperFace`, and two-input stability of categorical Mapper reconstructions (`interleavingDistance_coverComponents_le_add`, `geometricInterleavingDistance_graphPLMapperReconstruction_eq`, `geometricInterleavingDistance_mapperReeb_le_add_edist`, `geometricInterleavingDistance_graphPLReebGraph_le_mapperReeb_add`, `geometricInterleavingDistance_mapperReeb_le_graphPLReebGraph_add`, `ofReal_abs_sup'_sub_le_geometricInterleavingDistance_mapperReeb_add`, `tendsto_geometricInterleavingDistance_mapperReeb_pair`, `exists_graphPLMapperReconstruction_pair_le`), and rank obstructions to real interleavings (`finrank_range_structureMapLinear_le_of_realInterleaving`, `structureMap_eq_zero_of_realInterleaving`, `isEmpty_realInterleaving_of_finrank_lt`, `le_realInterleavingDistance_of_finrank_lt`, `le_realInterleavingDistance_of_structureMap_ne_zero`) with their Mapper and centred-tower forms (`isEmpty_face_mapper`, `isEmpty_realInterleaving_mapperHomologyPModule_of_finrank_lt`, `le_realInterleavingDistance_mapperHomologyPModule_of_finrank_lt`, `isEmpty_realInterleaving_mapperHomologyPModule_of_isEmpty_face`, `le_realInterleavingDistance_mapperHomologyPModule_of_isEmpty_face`, `le_realInterleavingDistance_centredMapperHomology_of_finrank_lt`), and diagrams of step towers (`mapper_eq_bot_of_isEmpty`, `mapper_eq_bot_of_isEmpty_componentIndex`, `isZero_simplicialHomology_mapper_of_isEmpty`, `stepTower`, `stepRefinement`, `mapperHomologyPModule_stepTower`, `isConstructible_stepTower`, `stepMapperDiagram`, `stepMapperDiagram_eq`, `stepMapperDiagram_isPositive`, `stepMapperDiagram_eq_ofIndexBars_succ`, `stepMapperDiagram_eq_ofIndexBars`, `bottleneck_stepMapperDiagram_le`, `bottleneck_stepMapperDiagram_le_add`, `bottleneck_stepMapperDiagram_eq`, `stepMapperDiagram_interleaving_iff_matching`, `realInterleavingDistance_stepTower_eq_top_iff`), and the tightness of the step bounds (`le_bottleneck_stepMapperDiagram_of_finrank_lt`, `le_bottleneck_stepMapperDiagram_of_isEmpty_face`, `le_bottleneck_stepMapperDiagram_of_structureMap_ne_zero`, `isEmpty_realInterleaving_stepTower_of_isEmpty_face`, `heq_stepTower_shiftGrid`, `stepTowerToShiftGrid`, `stepTowerOfShiftGrid`, `bottleneck_stepMapperDiagram_shiftGrid_le`, `SurvivesToLast`, `le_realInterleavingDistance_stepTower_shiftGrid`, `realInterleavingDistance_stepTower_shiftGrid_eq`, `bottleneck_stepMapperDiagram_shiftGrid_eq`, `mapperHomologyMap_zero_ne_zero`, `survivesToLast_zero`, `bottleneck_stepMapperDiagram_shiftGrid_eq_zero_degree`, `bottleneck_stepMapperDiagram_eq_top_iff`), and exact translation of categorical Mapper reconstructions (`coverResolution_add_const`, `coverComponentsTranslateIso`, `interleavingDistance_coverComponents_add_const`, `geometricInterleavingDistance_graphPLMapperReconstruction_add_const`, `_of_covers`, `isEmpty_graphPLMapperReconstruction_of_isEmpty_cover`, `geometricInterleavingDistance_graphPLMapperReconstruction_of_isEmpty`), and capped centred step towers (`centredInterval`, `cappedIndex`, `cappedCentredCover`, `stageRadius`, `mem_cappedCentredCover_succ_iff`, `cappedCentredRefinement`, `cappedCentredPullbackRefinement`, `cappedCentredDiagram`, `cappedCentredDiagram_eq_pullback`, `bottleneck_cappedCentredDiagram_le_of_stageRadius_le`, `bottleneck_cappedCentredDiagram_eq`, `bottleneck_cappedCentredDiagram_le`, `uniformGrid`, `bottleneck_cappedCentredDiagram_uniformGrid_le`, `bottleneck_cappedCentredDiagram_grid_le`, `bottleneck_cappedCentredDiagram_le_add`, `bottleneck_cappedCentredDiagram_plHeight_le`, `bottleneck_cappedCentredDiagram_plHeight_uniformGrid_le`), and direct different-domain capped centred map-pair results (`cappedCentredPairVertexMap`, `cappedCentredPairVertexMap_mk`, `cappedCentredPairVertexMapSymm`, `cappedCentredPairVertexMapSymm_mk`, `cappedCentredPairVertexMap_natural`, `cappedCentredPairVertexMap_comp`, `cappedCentredPairVertexMapSymm_comp`, `cappedCentredPairHomologyMap`, `cappedCentredPairHomologyMapSymm`, `cappedCentredPairInterleaving`, `bottleneck_cappedCentredDiagram_le_of_heightMapPair`, `bottleneck_cappedCentredDiagram_pair_le`, `bottleneck_cappedCentredDiagram_pair_uniformGrid_le`, `bottleneck_cappedCentredDiagram_pair_le_ofUniformBound`, `bottleneck_cappedCentredDiagram_pair_plHeight_le`, `bottleneck_cappedCentredDiagram_pair_plHeight_uniformGrid_le`), and essential counts (`card_essentialPart_stepMapperDiagram`, `bottleneck_stepMapperDiagram_lt_top_iff`, `fullComponentIndexEquiv`, `componentIndexFullEquiv`, `mapper_full_eq_top`, `fullMapperHomologyIso`, `finrank_simplicialHomology_mapper_full_zero`, `isZero_simplicialHomology_mapper_full_succ`, `isEmpty_mapper_face_one_of_unique`, `finrank_simplicialHomology_mapper_full_zero_of_unique`, `card_essentialPart_cappedCentredDiagram_zero`, `card_essentialPart_cappedCentredDiagram_succ`, `card_essentialPart_cappedCentredDiagram_zero_of_unique`, `bottleneck_cappedCentredDiagram_lt_top`, `card_essentialPart_cappedCentredDiagram_plHeight`, `card_essentialPart_cappedCentredDiagram_plHeight_zero_of_unique`); graph-PL height scaling (`plHeight_smul`, `geometricInterleavingDistance_graphPLReebGraph_smul`, `_neg`, `_affine`), split trees (`splitHeights`, `geometricInterleavingDistance_splitY`) and merge/split bounds (`ofReal_min_le_geometricInterleavingDistance_mergeY`, `_splitY`, `geometricInterleavingDistance_mergeY_bounds`, `_splitY_bounds`) | Input is a continuous map and an indexed target family. Coverage and multiplicity are explicit hypotheses where used. The MultiNerve Mapper is the multinerve of the component cover; its projection onto `mapper` is surjective and is an order isomorphism under `IntersectionsPathSubsingleton (componentCover f U)`. Every real number lies in at most two members of the uniform family exactly when `2g ≤ r` (for at least three members and `g < r`); its union is the window `(a, a + n(r − g) + g)` for `0 < g ≤ r`. The graph-PL finite Reeb data need no covering hypothesis; closed-level components are classified by `LevelVertex` for finite vertex sets, and inclusion into any level window is bijective on components. The star and gap comparison assumes every vertex height is a level of the critical list, while the Mapper comparison is at member-adapted levels. The refinement comparison assumes the coarser list covers the vertex heights. Constructibility at the specified critical list and the corresponding cosheaf identification assume a list covering the vertex heights and `V : Type`; constructibility at a noncovering list can fail (fixture D5). The Reeb quotient identification assumes a covering list, which cannot be dropped (fixture R6); the slice statements use `V : Type`, while the list-free corollaries need no list. The presentation map is injective for every list, while the homeomorphism assumes a covering list (fixture K5). Closed levels are compact and locally path-connected for finite vertex sets. The slice statements use `V : Type`. Finiteness is conditional; tower identity/composition are supplied coherence data. Refinement-induced homology maps use supplied linear orders on component-index types in one universe and any ring; two refinements between the same families induce the same map, and `mapperHomologyPModule` needs no selector identity or composition equations, agrees with the strict tower's maps and is independent of the selected refinements. A finite Mapper barcode is the canonical rank barcode of `mapperHomologyPModule` on `Fin N`; it needs finitely many faces of the given degree at every stage, a field, and the field, domain and index types in one universe. It is independent of the selected refinements and classifies these modules up to natural isomorphism; finite graphs with finitely many interval labels satisfy the finiteness hypothesis without coverage. Diagrams of real-indexed towers other than step towers, q-tame Mapper barcodes, independence of the component orders, multinerve barcodes and executable extraction are not provided. These constructions are noncomputable theory, not an executable Mapper implementation. The one-skeleton isomorphism assumes `2g ≤ r` and fails without it (fixture M5). Vertex-height stability fixes the graph and bounds the Reeb distance by `edist h g` without any order, level-count or constructibility hypothesis; it is not an equality in general, and extremal vertex heights bound it below and make it exact for vertical translations. Selected cover maps shifting by `η` in both directions between two real towers give an `η`-interleaving of their Mapper homology modules with no commutation assumed; maps at pointwise distance `δ` give a `δ`-interleaving along the centred tower. A step tower places finitely many cover families on the cells of a finite grid of radii, with an empty family before the first radius; its Mapper homology module is finite-constructible, and with finitely many faces in the given degree its real diagram `stepMapperDiagram` is the `ofIndexBars` image of the finite Mapper barcode. Cover maps shifting by `η` between two step towers bound the bottleneck distance of their diagrams by `η`, and that distance equals the real interleaving distance of the modules. No diagram or bottleneck statement is made for other towers, such as the centred tower, which is not finite-constructible on any grid; tightness is stated only for translations of the grid, below, and no order-independence statement is made. Capped centred step towers have an empty first stage, centred intervals of the grid radii and a full last stage. For maps at pointwise distance `δ`, their diagrams are at bottleneck distance at most `δ + μ` on a grid of mesh `μ`, and at most `δ` on a uniform grid of spacing `h` when `δ = p h`; for one map, two grids whose meshes, first radii and last radii are within `η` give diagrams within `η`. Fixtures show that neither the full last stage nor the mesh term can be dropped; coverage by a capped stage and sharpness of `δ + μ` are not claimed. Over a field, an `ε`-interleaving bounds the rank of each structure map `M(t → t + 2ε)` by the dimension of `N (t + ε)` when that one value is finite-dimensional; this gives lower bounds on the real interleaving distance, including the exact distance `1` of two shifted one-member towers and the bound `1/8` for the flat and steep maps. Bar-length lower bounds, tightness of the rank obstruction and the exact flat/steep distance are not claimed. Two-input Mapper bounds require each cover to cover its own height's attained range, are inequalities rather than equalities, and compare reconstructions over one fixed graph only. The rank obstructions bound the bottleneck distance of two step diagrams below through the stage of the second tower at `t + ε`. The step tower on `shiftGrid ε c` has at `t` the family of the step tower on `c` at `t + ε`, and the selected stage refinements are cover maps shifting by `ε` in both directions, so the two diagrams are at bottleneck distance at most `ε`. If the homology map of the selected refinement from the first nonempty stage to the last stage is nonzero in degree `n` (`SurvivesToLast`), the bottleneck distance and the real interleaving distance are exactly `ε`; in degree `0` this holds whenever the first nonempty stage has a component index. The bottleneck distance of two step diagrams is infinite exactly when their numbers of essential bars differ. Essential multiplicity equals last-stage homology dimension; finite bottleneck distance is equivalent to equality of these dimensions even for maps on different spaces. A finite nonempty full family on path-connected input is a simplex, so capped centred diagrams on nonempty grids have one essential degree-zero bar and none in positive degree, and any two such diagrams have finite bottleneck distance. With one label, the degree-zero count is the number of path components, or graph components for graph-PL input. Births, several-label disconnected degree-zero counts and finite bars are not computed. The survival hypothesis cannot be dropped (degree-one loop fixture). Exact distances for pairs of grids that are not translates, bar-length lower bounds and tightness of the bound `η` beyond translations are not claimed. Translating the height and a finite bounded cover by `c` moves the reconstruction by exactly `|c|` when some member has nonempty inverse image; over empty covers the distance is `0`. A continuous map `φ` with `f' ∘ φ = f` induces the vertex map `mapperDomainMap φ hφ U : mapper f U → mapper f' U` (`pullbackRestrict`, `domainIndexMap`, `componentDomainRefinement`, `mapperDomainMap_id`, `mapperDomainMap_comp`, `mapperMap_comp_mapperDomainMap`) and, for domains in one universe, homology maps `mapperHomologyDomainMap` and the module morphism `mapperHomologyPModuleMap` with identity and composition laws, commuting with the refinement-induced maps; the component orders of the two domains are independent supplied data and `φ` is arbitrary. A homeomorphism over the codomain gives the isomorphism `mapperHomologyPModuleIso`, real interleaving distance `0` (`realInterleavingDistance_mapperHomologyPModule_homeomorph`) and bottleneck distance `0` of step diagrams with an empty initial family (`bottleneck_stepMapperDiagram_homeomorph`) and of capped centred diagrams (`bottleneck_cappedCentredDiagram_homeomorph`); for a graph isomorphism with corresponding vertex heights, `realizationHomeomorph` and `bottleneck_cappedCentredDiagram_plHeight_iso` give distance `0` of the capped centred diagrams of the piecewise-linear heights. Equality of the diagrams, compatibility with interleavings and multinerve maps, and homotopy invariance are not provided. Common nonzero affine changes scale distances across finite graphs by the absolute slope. A `HeightMapPair` between finite graph-PL spaces bounds the geometric distance of their Reeb quotients; it supplies no map between graph objects and no Mapper cover or reconstruction consequence; its Mapper homology consequences are the centred and capped centred map-pair bounds above. For the three-edge merge tree, `mergeSection` and `exists_mergeSection_path` give height-preserving sections and bounded realization paths, including the horizontal top edge when `c = M`; `mergeFoldHeightMapPair` gives a `b/2` height-map pair. For `0 < a < b ≤ M`, `geometricInterleavingDistance_mergeY_eq_min` proves distance `min (b-a) (b/2)`, recovering `b-a` when `b ≤ 2a` and giving `b/2 < b-a` when `2a < b`. Reflection gives the same exact split-tree value (`geometricInterleavingDistance_splitY_eq_min`). These formulas are specific to this tree and do not give a converse to the height-map-pair bound. |

### Capped centred height-map pairs

`TDA.Mapper.RefinementHomologyCappedMapPair` adds direct stage maps, their strict naturality and
double-shift composite laws, the induced homology transformations, and
`cappedCentredPairInterleaving` for `HeightMapPair`s between possibly different domains. With
finite faces in the selected degree, `bottleneck_cappedCentredDiagram_le_of_heightMapPair`
transfers that interleaving to a bottleneck bound; the same-grid mesh and exact uniform-grid
corollaries include recovery from a same-domain pointwise bound and graph-PL specializations.
Fixtures cover the recovery, an edge-to-point bracket, and failure when only height-preserving
maps are supplied. Component orders are caller-supplied, and these results need no coverage or
nonempty-domain assumption.

Graph realizations expose `GraphRealization.edgeSegment` for the path along a dart between any two
parameters, with endpoint and evaluation laws `edgeSegment_zero`, `edgeSegment_one` and
`edgeSegment_apply`. `GraphPL.plHeight_edgeSegment_bounds` bounds the piecewise-linear height along
that path by its endpoint heights. These results apply to one dart and do not classify arbitrary
paths in a realization.

For a small dependency footprint, import an individual implementation module rather than
the whole area. Generic simplicial contiguity depends only on the simplicial vertex-map
API; nerve-specific contiguity is owned by `TDA.Topology.NerveContiguity`. Mapper Tower
consumes that Topology theorem. This removes the previous Simplicial-to-Topology dependency.
`TDA.Mapper.RefinementHomology` consumes the signed prism homotopy and the Persistence
functor core, `TDA.Mapper.RefinementHomologyInterleaving` consumes the real interleaving
distance, `TDA.Mapper.RefinementHomologyBarcode` consumes the finite interval
decomposition, `TDA.Mapper.RefinementHomologyLowerBound` consumes the real
interleaving distance and simplicial homology, `TDA.Mapper.RefinementHomologyDiagram`
consumes the finite-constructible isometry, `TDA.Mapper.RefinementHomologyDiagramTightness`
consumes the diagram and lower-bound modules, and `TDA.Mapper.RefinementHomologyCappedTower`
consumes the step diagrams and the bottleneck triangle inequality; the Persistence core does
not import Mapper. `TDA.Mapper.DomainMap` consumes only the refinement and vertex-chain-map
APIs; `TDA.Mapper.RefinementHomologyDomainMap` adds the capped tower and graph-PL heights;
`TDA.Mapper.RefinementHomologyMapPair` and `TDA.Mapper.RefinementHomologyCappedMapPair`
consume `TDA.Reeb.HeightMapPair`; and `TDA.Mapper.RefinementHomologyEssential` consumes the
simplicial cone, `H₀` augmentation and essential-vanishing APIs.

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

## Interval supports, presentations and rank-exact lifting

`SupportInterval.module` constructs a module on any order-convex subset of a
preorder over a ring, including the empty support. A structure map with an
endpoint outside the support is zero over any ring; the converse requires a
nontrivial ring. The comparison and morphism lemmas remain over fields.
`Rectangle.diagonal_maps_eq_zero_iff` gives the exact endpoint-sensitive
vanishing criterion for bounded rectangles over a field.
For a field, a lattice and a finite indexed family of generators,
`GeneratedUpsetResolution.term`, `differential` and `augmentation` construct the
join-indexed projective resolution of its generated-upset support module.
`term_projective`, `differential_comp_differential`,
`differential_comp_augmentation` and `resolution_pointwise_exact_at` establish
projectivity, the chain laws, surjectivity and exactness at every index. Repeated
generator values remain distinct occurrences; the empty-family boundary is stated
separately. `term_isZero_of_degree_ge` shows that the degree-`r` term vanishes for
`m ≤ r`; when `m ≥ 1`, the resolution therefore gives projective dimension at most
`m−1`. See [join-indexed upset resolutions](math/generated-upset-resolution.md).
`RectangleHall.card_le_neighbors` derives the Hall neighbor cardinality bound
from an actual ε-interleaving of finite rectangle sums: a selected family
whose `(4n−2)ε` transitions are nonzero has at least as many neighbors at radius
`(2n−1)ε`, retaining occurrence multiplicities, endpoint decorations and ε = 0.
For a field and n ≥ 1, `RectangleMatching.exists_matching` uses this bound and
the reversed interleaving to produce one radius-`(2n−1)ε` occurrence matching.
Every paired rectangle module has an actual interleaving at that radius, and
every unmatched module on either side is actually interleaved with zero.
`IsMatching.source_covered` and `IsMatching.target_covered` expose coverage of
all significant occurrences by that same matching. Multiplicities, arbitrary
endpoint decorations and ε = 0 are retained. `IsMatching.interleaving` assembles
these pair and deletion witnesses into an actual interleaving of the finite
biproduct families, with public component laws for paired and zero entries.
`RectangleMatching.bottleneckDistance` is the extended infimum of actual matching
radii. `two_sided_distance_bounds` proves `d_I ≤ d_B ≤ (2n−1)d_I` for n ≥ 1,
and `bottleneckDistance_eq_interleavingDistance_one` gives equality for this
decorated-rectangle family distance in dimension one. No minimizing radius is
assumed: over ℚ, a singleton module versus zero has distance zero without a
parameter-zero witness. On positive finite half-open intervals,
`RectangleBarcodeBridge.realizationIso` identifies the existing rectangle
biproduct with the reindexed existing real barcode realization, retaining every
occurrence. `rectangle_bottleneck_eq_diagram` and
`diagram_bottleneck_eq_real_distance` identify their distances;
`interleaving_iff_cost_matching` compares actual witnesses at every radius.
An actual matching may pair short intervals whose endpoint cost exceeds the
radius; the bridge removes those pairs and proves both ends deletable.
Empty occurrence families are included. Empty half-open supports are zero in
the raw barcode constructor and are excluded by the positive-length bridge;
other endpoint decorations are not identified with half-open modules. Zero
distance implies a natural isomorphism on this common subclass.
`RectangleSharpExample.interleaving` constructs Bjerkevik's Example 5.2 over
any field, using two Fin 3-indexed families of open rectangles and the source's
integral coefficient matrices. `interleavingDistance_eq_one` and
`bottleneckDistance_eq_three` prove the exact values 1 and 3, with lower
bounds on every actual witness radius. The explicit radius-three matching
retains all occurrences. `fails_smaller_constant` establishes sharpness of
the two-dimensional factor three, including in characteristic two; it makes
no optimality assertion in higher dimensions. `GradedFree.lift`
and `GradedFree.exists_lift_of_surjective` provide the natural universal property and lifting
property of graded free modules over a ring; `GradedFree.FinitelyPresented`
expresses finite presentation by homogeneous cokernels. For finitely presented modules on
`Fin n → ℝ`, `GradedFree.finitelyPresented_exists_finite_criticalCoordinates`
gives finite coordinate sets outside which comparable structure maps are
isomorphisms, and `GradedFree.finitelyPresented_exists_pos_structureMap_isIso`
gives positive right-diagonal slack at every index.
Over a field and any preorder, `GradedFree.finitelyPresented_finiteDimensional`
proves every fiber of a finitely presented module finite-dimensional. Its proof
uses the actual finite free cover and its componentwise surjectivity; finite
generators suffice, so this consequence needs neither finite relations nor a
finite indexing poset.
For a ring and any coordinate dimension, `finitelyPresented_exists_finiteGridKan`
constructs a finite product grid, its order embedding and an actual natural
isomorphism from the chosen Mathlib left Kan extension to the original module.
`finitelyPresented_exists_pfd_finiteGridKan` supplies pfd grid fibers over a
field. `Presentation.gridKanIso` gives the comparison for a chosen finite
presentation, and `gridHomEquiv` extends every natural map on that grid
uniquely. Its restriction laws expose the constructed maps.
More generally, `Presentation.kanIso` and `isLeftKanExtension` apply to an order
embedding containing all generator and relation births. Both comparison
inverse laws are derived using existing presentation lifting and Mathlib Kan
uniqueness. Repeated births remain separate generator occurrences, empty
families and n=0 are allowed, and the reconstructed module may have unbounded
support.

For a finite coordinate grid, `CoordinateGrid.lan` is Mathlib's actual left
Kan extension along the grid inclusion. At each real grade with a lower grid
point, `floor` selects the greatest such point and `appIso` identifies the
actual Kan fiber with the grid fiber there. `kanInclusion` is the Kan unit
followed by the real structure map; without a lower grid point, the actual
fiber is zero. `appIso_map_apply` and `appIso_structureMap_apply` identify the
images of actual Lan maps and transitions with the corresponding grid maps,
not only with equal fiber dimensions.

Over a field, `lan_finiteDimensional` preserves pointwise finite-dimensional
fibers. Here `IsRankExact` means a pointwise short exact sequence (the first map
is injective, the second is surjective, and the image of the first equals the
kernel of the second at every index), with finite-dimensional middle fibers
and additive ranks of structure-map images for every comparable pair. Given
such a sequence on the finite product grid, `lan_isPointwiseShortExact` proves
ordinary pointwise exactness after applying the actual Lan functor, while
`lan_isRankExact` preserves finite-dimensional middle fibers and rank
additivity. These theorems require a finite product coordinate grid; they do
not assert exactness for arbitrary order embeddings. The focused
`CoordinateGridKanExamples` module exercises nonzero finite-death lifts, actual
within-cell and death transitions, characteristic two, empty and zero inputs,
grades below the grid and a principal-upset tail.

At each pair of comparable indices, `IsPointwiseShortExact.rank_add_iff_lift_kernel`
equates rank additivity with lifting dying vectors when the middle source fiber
is finite dimensional. `lan_lift_kernel` gives the corresponding lift that dies
at the same real grade after applying the finite-grid Kan functor, and
`Hook.exists_lift` constructs lifts of finite-death hook morphisms in this
pointwise finite-dimensional domain.
`HookInfinity.homEquivFiber` identifies principal-upset morphisms with birth-fiber
vectors; surjectivity at birth suffices to lift them over any ring and preorder.

Over a field and partial order, `Hook.endRingEquiv` and
`HookInfinity.endRingEquiv` identify the actual endomorphism rings with the
coefficient field by evaluation at birth. Their public scalar/evaluation laws
imply categorical indecomposability, including unbounded supports.
`SupportInterval.support_eq_of_iso` recovers supports from natural isomorphisms.
`Hook.nonempty_iso_iff` retains both finite endpoints, and the corresponding
principal-upset law retains its birth; finite and infinite death cannot be
isomorphic. Death at or before birth gives the zero hook. These are results
about individual hooks. `FiniteRankProjectiveClassification.RankProjectiveHookTag`
records either a strict finite birth/death pair or the birth of a principal
upset; `rankProjectiveHookSum_multiplicity_unique` proves that isomorphic finite
sums of nonzero hooks have the same multiplicity for each tag.
`IsRankProjective` states the relative lifting property against actual rank-exact
sequences. Finite-death hooks, principal upsets and their finite categorical
biproducts satisfy it; natural isomorphisms and retracts preserve it. For a pfd
module M on a finite poset, `FiniteHookDeflation.π M` is an actual natural
surjection from a finite occurrence-indexed hook sum. Fiber and structure-map
kernel bases prove surjectivity and all dying-element lifts. `rankExact` gives
its actual rank-exact kernel sequence; both source and kernel are pfd.
`isRankProjective_iff_retract` characterizes rank projectivity by splitting this
constructed map. This proves enough relative projectives on finite posets,
without claiming minimality or signed stability. For pointwise finite-dimensional
modules on a finite poset, `rankProjective_iff_exists_canonical_subfamily`
characterizes rank projectivity exactly by isomorphism to a finite selection of
the actual cover occurrences, retaining repeated hooks.

Over a field, `IsPointwiseShortExact.of_iso` and `IsRankExact.of_iso` transport
actual short exact and rank-exact sequences along natural isomorphisms,
constructing the conjugated maps. For a finite coordinate grid,
`CoordinateGrid.lan_isRankProjective` preserves relative rank projectivity by
restricting an actual rank-exact sequence and using the Kan/restriction
adjunction. `lanBiproductIso` is the canonical comparison for finite
categorical sums over a ring, with projection and inclusion laws. Over a ring,
`infinityLanIso` identifies the actual Kan image of a principal upset with the
corresponding real principal upset and provides its coefficient law. Over a
field, `hookLanIso` does the same for finite-death hooks.
`embeddedCoverFamily` applies the coordinate embedding to the existing
occurrence-indexed `FiniteHookDeflation.family`, preserving multiplicities;
over a field, `finiteHookDeflationLanIso` gives its actual finite-biproduct
comparison with projection/inclusion equations. Finally,
`GradedFree.finitelyPresented_exists_finiteHookRankExactCover` constructs for
every originally finitely presented real-coordinate module a rank-exact map
from such a relative rank-projective hook sum, with pointwise finite-dimensional
kernel fibers. This theorem requires a field. It does not assert that this
kernel is finitely presented or that the cover is minimal. The focused
`CoordinateGridHookExamples` module checks planar death across a real
transition, principal-upset tails, repeated and mixed occurrences, empty and
zero-dimensional cases, characteristic two, and consumers of the cover
theorem over `ℚ` and `ZMod 2`.

`GradedFree.pfd_finitelyPresented_of_finite_poset` constructs a genuine finite
graded-free presentation of every pointwise finite-dimensional module on a
finite poset. Its generator and relation occurrences are finite basis indices
of the fibers and component kernels, and the componentwise image/kernel
equality identifies the actual quotient with the input. For a finite
coordinate grid, `CoordinateGrid.lanFreeIso` transports each finite free
occurrence sum through the actual Lan hook comparison, while
`GradedFree.finitelyPresented_lan_of_finiteGrid` conjugates the actual
relation map and uses preservation of its cokernel to prove that Lan preserves
finite presentation. Finally,
`GradedFree.finitelyPresented_exists_finiteHookRankExactCoverKernel` extends
the finite-dimensional grid kernel presentation and identifies its actual
Lan with the categorical kernel of the displayed `finiteHookDeflationLanIso`
cover map. Starting only from finite presentation of the original module, the
theorem returns this constructed finite-hook rank-exact cover, proves its
cover term relatively rank projective, and proves its actual categorical
kernel finitely presented. It does not assert generic finite-presentation
closure under kernels, minimality, or a resolution-length bound. The focused
`FinitePresentationHookKernelExamples` module applies the result to the
nonzero relation presentation over `ℚ` and `ZMod 2`, and checks empty-family
and zero-dimensional zero-module boundaries.
`finitelyPresented_actual_cover_kernel_finiteDimensional` applies the
finite-dimensional fiber theorem to the actual constructed kernel using only
the original module's finite-presentation hypothesis.

For a field `k`, `n ≥ 1`, and `M : PModule k (Fin n → ℝ)`,
`GradedFree.finitelyPresented_rankProjective_iff_exists_hook_sum` gives the
following classification under only the original
`GradedFree.FinitelyPresented M` predicate: `M` is rank projective exactly
when it is isomorphic to a finite biproduct of hooks tagged by
`RankProjectiveHookTag (Fin n → ℝ)`. A finite tag records a strict birth/death
pair; an infinite tag records the birth of a principal upset. The `Fin m`
indexing retains repeated occurrences, including the zero module as the empty
sum. The forward proof splits the actual cover from
`finitelyPresented_exists_finiteHookRankExactCover`, descends the section
through the actual grid Kan unit and finite-biproduct comparisons, and applies
the finite-poset canonical-subfamily classification. `CoordinateGrid.lanMapPreimage`
constructs a grid map representing any morphism between Lan images;
`CoordinateGrid.lan_map_preimage` proves that this grid map reconstructs the
morphism, and `CoordinateGrid.lan_map_surjective` states that every such
morphism arises this way. Together with `CoordinateGrid.lan_map_injective`,
these declarations expose full faithfulness, so the grid-map preimage is
unique. No hook decomposition is assumed for `M`.
`GradedFree.rankProjectiveHookSum_multiplicity_unique_of_iso` proves that any
two naturally isomorphic finite sums of real-coordinate hook tags have equal
occurrence counts for every tag. It constructs a common coordinate grid from
both families' endpoints and the queried tag, transports each actual hook sum
through the Lan hook and biproduct comparisons, reflects the isomorphism with
`lanMapPreimage`, `lan_map_preimage`, and `lan_map_injective`, then applies the
finite-poset multiplicity theorem. The result includes repeated hooks,
finite-death and infinite-death hooks, tags absent from either family, and empty
families. It needs no finite-presentation or pointwise finite-dimensionality
hypothesis, no preselected grid, and no endpoint-membership premise.
`FinitePresentationRankProjectiveClassificationExamples` checks a nonzero
finite-death hook, an unbounded principal upset, two repeated hooks, the
zero/empty-sum case, and multiplicity invariance for a reordered mixed sum and
empty families. Together, these results give choice-independent hook
multiplicities for finite real-coordinate rank-projective decompositions.
`FiniteRankProjectiveResolution.finitelyPresented_exists_minimal_resolution_with_hook_sum_terms`
then constructs a minimal resolution for every finitely presented module on
`Fin n → ℝ` (`n ≥ 1`), with each zero-padded term represented by an actual
finite hook sum. The proof transports the occurrence-indexed terms of a finite
grid resolution through the genuine left Kan extension, its hook and
biproduct isomorphisms, and the reconstructed presentation of the original
module. `MinimalFiniteRankProjectiveResolution.hookBettiMultiset_eq` combines
zero-padded termwise uniqueness with hook-sum multiplicity uniqueness to show
that the multiset in each degree is independent of the selected resolution
and of the finite hook presentation. Given a concrete term presentation,
`hookBettiMultiset_eq_tagMultiset` identifies its occurrence multiset with the
choice-based value without exposing the internal choice. `evenHookBetti_eq`
and `oddHookBetti_eq`
extend each finite sum by the empty multisets beyond the chosen resolution
length, so they remain invariant when the compared resolutions have different
raw lengths. `signedHookBarcode_eq` records those two finite multisets
separately; repeated hooks retain their multiplicity and even and odd degrees
are not cancelled against one another. The principal-upset example confirms
that positive-degree terms vanish when the resolved module is already
projective.

For a field `k`, `n ≥ 1`, and two finite occurrence-indexed families of these
finite-death or principal-upset hooks over `Fin n → ℝ`,
`HookMatching.exists_matching` turns an actual `ε`-interleaving of their
biproducts into an occurrence matching at radius `(2n−1)ε`. Every matched pair
has an actual `((2n−1)ε)`-interleaving, and every unmatched hook on either side
has an actual interleaving with zero at that radius. Repeated isomorphic tags
remain separate occurrences, and the unbounded principal-upset supports are
included. The proof derives the Hall
inequality `card_le_neighbors` from the component maps: endpoint geometry and
composition of the hook coefficients make the selected finite matrix product
triangular with unit diagonal, after which finite Hall matching and the
two-sided injection construction give the matching. For `ε = 0`, the result
uses hook-sum multiplicity uniqueness to produce the matching directly.
This is the finite-family matching consequence of
[Botnan–Oppermann–Oudot–Scoccola, Theorem 4.1 and Proposition 4.3](https://arxiv.org/html/2208.00300v3).
It does not assert countable-family stability or the signed-barcode stability
of a full resolution.

The signed-multiset results do not select a canonical hook decomposition or a
unique comparison isomorphism. Choice independence of the signed multisets is
not a stability theorem: these declarations do not establish signed-barcode
stability, the rank-exact structure axioms stated in
[Theorem 2.7(1)](https://arxiv.org/html/2208.00300v3), or the `2n−2`
resolution-length bound stated in
[Theorem 5.18](https://arxiv.org/html/2208.00300v3).

For a field `k`, `n ≥ 1`, and an originally finitely presented module
`M : PModule k (Fin n → ℝ)`,
`FiniteRankProjectiveResolution.finitelyPresented_exists_finiteRankProjectiveResolution`
constructs an actual finite rank-projective resolution of `M`. It first uses the
finite presentation to reconstruct `M` as the actual left Kan extension of a
pointwise finite-dimensional module on a finite coordinate grid. On that finite
poset it chooses rank-exact hook-sum covers with the fewest summands for each
successive kernel. A nonzero same-hook component into the preceding kernel
would split off a summand and contradict that choice. Thus every nonzero
differential arrow lowers the weight from its source hook to its target hook;
equivalently, the weights strictly increase as one passes to covers of
successive kernels. The weight is built from the sizes of the hooks' endpoint
lower sets, with infinite hooks placed above finite hooks. It is bounded on the
finite poset, so the iteration ends with zero kernel.
The existing Kan preservation maps then transport all rows and projective terms
back to `M`. No pfd, grid, hook decomposition, or resolution is an extra input.

For a quotient `π : Q ⟶ K`, `IsRankProjectiveCover π` certifies that `Q` is
rank-projective, that the actual categorical-kernel row
`kernel.ι π` followed by `π` is rank exact, and that every endomorphism of `Q`
fixed by `π` is an isomorphism. `IsRankProjectiveCover.exists_iso_over_quotient`
uses both covers' rank-projective lifting properties against the opposite
actual kernel rows and both quotient-fixed endomorphism criteria to show that
any two certified covers of the same target are naturally isomorphic over
that target. It makes no finiteness or resolution assumption, and does not
claim uniqueness of the comparison isomorphism or of an entire resolution.
On a finite poset, the separate
`FiniteRankProjectiveResolution.exists_minimalFiniteRankProjectiveResolution_of_pfd_finitePoset`
theorem constructs a resolution whose every quotient row has this certificate.
The public `CoordinateGrid.lanMinimalFiniteRankProjectiveResolution` transfers
the certificates through the actual left Kan extension. It preserves the
projective middle terms and rank-exactness of the actual categorical-kernel
rows; for the endomorphism condition,
it lifts each quotient-fixed endomorphism to the grid by full faithfulness,
applies the grid cover certificate, and maps the resulting isomorphism through
Lan.

For a field `k`, positive `n`, and `M : PModule k (Fin n → ℝ)`, the public
`GradedFree.FinitelyPresented M` hypothesis therefore proves that an actual
`MinimalFiniteRankProjectiveResolution` of `M` exists:
`FiniteRankProjectiveResolution.finitelyPresented_exists_minimalFiniteRankProjectiveResolution`.
The construction reconstructs `M` up to isomorphism as the actual left Kan
extension of a pointwise finite-dimensional module on a finite coordinate grid,
applies the finite-poset minimal theorem, transfers every row through Lan, and
transports the result across the reconstruction isomorphism. Every quotient
row in the returned resolution carries the public projective-cover certificate.
This is the finite-grid Kan transfer of [Theorem 2.7(2) and Appendix A of
Botnan–Oppermann–Oudot–Scoccola](https://arxiv.org/html/2208.00300v3).
`FiniteRankProjectiveResolutionKanExamples` checks the finite-resolution and
minimal-resolution interfaces on a nonzero principal-upset free module; the
earlier resolution examples retain the zero and contractible-row boundary cases.

For any field and any partially ordered index type, two
`MinimalFiniteRankProjectiveResolution`s of the same module have isomorphic
terms in each degree after padding the shorter resolution by zero:
`MinimalFiniteRankProjectiveResolution.termAt_nonempty_iso` returns the
comparison as a `Nonempty` isomorphism, and `termAt_rank_eq` shows that every
structure-map rank in corresponding terms is independent of the chosen
resolution. The theorem uses only the cover certificates carried by the two
inputs; it neither assumes equal raw lengths nor chooses a canonical
comparison isomorphism. The example
`FiniteRankProjectiveResolutionUniquenessExamples.principalHook_positive_terms_are_zero`
uses a one-term resolution of a principal-upset projective to show that every
positive-degree term in any minimal resolution of that module is zero.

`IsRankDeflation` means that a natural map is the quotient of an actual
rank-exact sequence. Its `rankExact_kernel` law supplies the categorical
kernel sequence; `id` and `comp` prove identity and composition closure.
`pullback_snd` proves closure under the actual categorical pullback along a
map from a pfd module. `PullbackFiber.mk`, its projection laws and
`element_ext` construct compatible pairs and distinguish their vectors;
the pullback fibers are pfd. Same-death lifts derive rank additivity without
an exact-category assumption. A principal upset surjecting onto its
finite-death truncation shows that an ordinary pointwise epimorphism need
not be rank admissible. The deflation-side closure laws do not establish the
full exact structure; inflation-side pushout closure is proved separately below.
`IsPointwiseShortExact.kernelIso` identifies a given exact sequence's left
term with its actual categorical kernel and preserves its inclusion.
`IsRankDeflation.splitKernelIso` derives a splitting when the quotient is
rank projective. For rank-exact sequences K→P→M and L→Q→N over a field,
with rank-projective P,Q, `RankSchanuel.interleavingOfSequences` constructs
an ε-interleaving between P⊕L[ε] and K[ε]⊕Q from an actual ε-interleaving
of M,N. The crossed-pullback maps, their projection laws and both
double-transition equations are public; the pullback construction itself
works over any ring. `kernelSumIso` gives the static specialization for
two deflations onto the same quotient. Consumers include redundant covers
with nonzero kernels, positive width, width zero, characteristic two, zero
modules and zero coordinate directions. This one-step result supplies the
first row in the finite-resolution comparison below; the uniform
resolution-length bound and signed-barcode stability require further results.

For a field `k`, finite coordinate dimension `n`, actual finite
rank-projective resolutions `R` of `M` and `S` of `N`, and an actual
`CoordinateInterleaving ε M N`,
`schanuelInterleavingOfResolutions R S ε i` constructs an
`ε`-interleaving between the following finite biproducts. Set
`L = max R.length S.length`, extend each resolution's term sequence by zero
after its last term, and shift its degree-`j` summand by `jε`. The first sum
uses `R` in even degrees and `S` in odd degrees; the second uses the opposite
choice. This is the rank-exact specialization of [Proposition 2.9 and
Appendix A](https://arxiv.org/html/2208.00300v3).

The theorem covers unequal lengths, including length zero, and includes both
interleaving maps and their two double-transition equations. It requires no
minimality, grid, or additional finiteness assumption on the given finite
resolutions. `RankSchanuelResolutionExamples` exercises the zero-length,
one-term, nonzero two-term-tail, unequal-length, and `ε = 0` cases. The result
retains the degree shifts; by itself it does not establish a shift-free signed
barcode inequality or a uniform bound on the resolution length.

### Pushouts of rank-exact sequences

Let `0 → L --ι→ M --π→ N → 0` be rank exact over a field, with `P` any
partially ordered set, and let `f : L ⟶ L'` have pointwise finite-dimensional
target fibers. `IsPointwiseShortExact.pushoutQuotient` defines the quotient map
from the actual categorical pushout by applying `π` on `M` and zero on `L'`.
`IsPointwiseShortExact.pushout_pointwise` proves that this quotient and the
canonical map from `L'` form a pointwise short exact row. `IsRankExact.pushout`
also proves that the pushout fibers are finite dimensional and that the new
row is rank exact. Each middle fiber is finite dimensional because the actual
`ModuleCat` pushout is a quotient of `M(p) ⊕ L'(p)`.

For rank additivity, the proof lifts a quotient vector killed by a structure
map through the original rank-exact row with a lift killed at the same grade,
then maps that lift into the pushout. `RankExactPushoutExamples` checks the
theorem on a nonzero pushout of a split sequence. This closure result supplies
the pushout part of the rank-exact theory; the remaining exact-structure laws
are separate results.

`FinitePresentationLifting` proves that maps from a presented module lift through
a natural transformation surjective at generator grades and injective at relation
grades. With bijectivity at generator grades, the lift is unique. For coordinatewise
real indices, import `RealCoordinates` and use `open scoped TDA.Persistence` to
select the preorder category; rectangles and finite grids already import it.
`CoordinateInterleaving` supplies actual diagonal-shift witnesses and their
composition laws. `GradedFree.CrossData` specifies shared shifted generators
and primitive homogeneous relations. `CrossData.quotientInterleaving` constructs
the interleaving of the resulting cross-presented quotients, over any ring;
`CrossData.interleavingOfIso` transports it along presentation isomorphisms.
For finitely presented modules,
`GradedFree.finitelyPresented_interleaving_iff_crossPresentation` equates an
actual ε-interleaving with finite shared cross-presentation data and natural
isomorphisms to both modules. `Presentation.crossData` reconstructs the data
from any supplied presentations and interleaving; `crossDataLeftIso` and
`crossDataRightIso` prove the quotient identifications. `Presentation.presentedShiftIso`
also identifies the quotient of a shifted presentation with its shifted quotient.
For two finitely presented modules on `Fin n → ℝ`,
`GradedFree.finitelyPresented_distance_le_iff_interleaving` identifies a finite
distance bound with an interleaving at that exact parameter. Finite distances
are attained, admissible parameter sets are closed, and distance zero is
equivalent to natural isomorphism, over any ring and including dimension zero.
`GradedFree.FinitePresentationIsoClasses` equips their natural-isomorphism classes
with an `EMetricSpace` whose extended distance agrees with the module distance.
See [attainment and separation](math/multiparameter-closure.md) and
[the constructions and their scope](math/multiparameter-foundations.md).

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

For q-tame real modules over a field, an actual `ε`-interleaving gives the
quotient family `RealInterleaving.exists_qTame_interpolating_family` on the closed
interval `[0, ε]`. Its endpoints are naturally isomorphic to the input modules,
each member is q-tame, and every pair has an actual interleaving witness at the
nonnegative distance between its parameters. This algebraic interpolation result
does not assert a bottleneck or metric stability theorem. See the
[real interleaving interpolation](math/real-interleavings.md#q-tame-algebraic-interpolation)
section for the quotient and the precise scope.

For an actual q-tame `ε`-interleaving, `RealInterleaving.exists_finite_saturating_matching`
constructs finite injective edge sets for any prescribed finite sets of finite-death
occurrences of lifetime greater than `2ε` and essential occurrences on both sides.
Every selected token is covered and every edge has cost at most `ε`. The
`FiniteSaturatingMatching` predicate states the injectivity, cost, and coverage
conditions explicitly. This finite saturation result does not assert a matching of
the full diagrams. `Rips.exists_finite_saturating_matching_of_hausdorff_lt` applies
it to totally bounded Rips spaces embedded isometrically in a common metric space,
when `2 * hausdorffDist < ε`. See [Rips metric stability](math/rips-metric-stability.md)
for this consumer and the scope of the result.

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

### Derived vertex tensors for the interval-pair incidence algebra

For a field `k`, a finite lattice `S`, and a strict vertex `v`,
let `A` be the interval-pair incidence algebra, `I` its diagonal ideal, and `B = A/I`.
`TDA.Persistence.IncidenceVertexTensorFunctor.vertexTensor v` is the additive functor from left
modules over the interval-pair incidence algebra to `k`-modules; write `F_v` for this functor. It
takes the actual character coinvariants, is left adjoint to `characterRestriction v`, and preserves
finite colimits, hence is right exact. Its Mathlib left-derived functors use the second,
left-module argument. The `diagonalQuotientProjectiveResolution` in
`TDA.Persistence.IncidenceVertexTor` is the actual projective resolution from the short exact row
`0 → I ↪ A ↠ B → 0`, with proved projectivity and exactness of these terms and maps. Applying the
functor gives zero in every positive derived degree, including one. The
canonical degree-zero comparison identifies `((F_v.leftDerived 0).obj B) ≅ k`, hence
`F_v(B) ≅ k`; the quotient-unit class maps to `1`. These statements hold for every strict vertex
and field. See [the resolution and derived comparison](math/incidence-vertex-tor.md) and the
focused consumers in `TDA.Persistence.IncidenceVertexTorExamples`.

`TDA.Persistence.IncidenceQuotientSimple` classifies the actual simple left modules over
`C = (A/I)ᵐᵒᵖ`, equivalently simple right modules over `B = A/I`. For every simple module there
is a unique strict vertex `v` with a `C`-linear isomorphism to the actual character-restriction
module `RightVertexModule v`; `rightVertexModule_iso_iff` distinguishes the vertices. The
underlying-`k` comparison with `((F_v.leftDerived 0).obj B)` is an existence isomorphism that
depends on the classification choice, while `IncidenceVertexTor.diagonalQuotient_leftDerivedZeroIso`
is the canonical degree-zero field comparison. Positive left-derived vanishing is supplied by
`IncidenceVertexTor.diagonalQuotient_leftDerived_pos_isZero`. See
[simple right modules over the quotient](math/incidence-quotient-simple-modules.md) and the
focused consumers in `TDA.Persistence.IncidenceQuotientSimpleExamples`. This is the simple-module
classification step used in BOOS24-v3 Lemma 5.7, specialized to the interval-pair quotient; it
does not assert the global-dimension conclusion of that lemma.

`TDA.Persistence.IncidenceQuotientDimension` proves that the projective dimension of any
finite-length right quotient module is bounded by the supremum of the dimensions of the actual
strict-vertex modules. It also gives the natural uniform-bound equivalence and the corresponding
results for modules finite-dimensional under the existing restricted `k`-action. The proof uses
the #699 classification in a Mathlib finite-length extension induction. It gives no numerical
dimension bound and no quotient-versus-incidence global-dimension comparison. See
[finite-length quotient dimensions](math/incidence-quotient-finite-length-dimension.md) and the
consumers in `TDA.Persistence.IncidenceQuotientDimensionExamples`.

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
The index family may be uncountable.

`TDA.Persistence.CutDecomposition` proves that the chosen interval complements
span every fiber and that every finite relation among distinct complements is
trivial. Its `sumIso` is a natural isomorphism from their algebraic direct sum
to any pointwise finite-dimensional real-indexed module over a field. The construction includes
singleton supports and assumes no decomposition or global countability. Finite
activity at each parameter, and finite activity over a finite observation list,
follow from finite dimension. `CutSubspacesExamples` checks cut endpoints and the
singleton image/kernel spaces of a module with zero maps at strict inequalities.
`TDA.Persistence.RealIntervalDecomposition` chooses a basis of each compatible
section complement and obtains scalar interval summands. Its `scalarIso` is a
natural isomorphism from their algebraic direct sum to any pointwise
finite-dimensional real-indexed module; `exists_interval_decomposition` states
the corresponding existence theorem. The nonempty supports are order-convex,
with open or closed endpoints, singletons, infinite tails and the whole real
line allowed. Finite activity is derived at every parameter, with no global
countability assumption.

`RealIntervalObservation` proves `RealIntervalDecomposition.rankBarcode_eq_sampledBarcode`, identifying the existing
rank barcode of every strict finite real observation list with the multiset of
nonempty sampled intersections of these summands, retaining multiplicities.
Only finitely many occurrences meet the list. `FiniteObservation` supplies the
rank and visible-occurrence arguments for arbitrary algebraic interval families.
No finite critical grid or continuity hypothesis is required.

`IntervalCompatibility` identifies the generic support modules with existing
real half-open interval modules and their finite diagram realizations by natural
isomorphisms, including the existing finite-constructible decomposition.
`EphemeralIntervalIso` proves `IntervalCompatibility.ephemeralIso`, realizing the real-indexed ephemeral module as the sum of all real
singleton intervals. The examples also include an empty family, both left-tail
conventions, and an infinite locally finite interval module family accumulating
at zero. These decomposition results require finite-dimensional fibers; the
q-tame class has a different hypothesis.

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
through their finite diagrams by this finite API. `RipsQTameDiagram` below
provides decorated multiplicities for totally bounded targets.
`RipsQTameFiniteCompatibility` proves that on finite
metric spaces its point multiplicities agree with the existing finite diagram,
using `(minusCut birth, minusCut death)` for finite bars and
`(minusCut birth, infinityCut)` for essential bars. This Lean compatibility
theorem currently requires the coefficient field and vertex type in the same
universe because the rank-to-diagram bridge has that universe restriction; the
mathematical statement is field-independent. See
[metric-input stability](math/rips-metric-stability.md).

`TDA.Persistence.DiagramBottleneckTopology` gives `Diagram ℝ` its extended
bottleneck metric and Borel topology. `TDA.Persistence.RipsSamplingMeasure`
defines `Rips.sampleLawMeasure` as the actual Borel probability law of an iid
sample diagram from a compact metric probability space. The sample map has
Lipschitz constant 2 and is continuous; its range is compact and has full law.
In positive degree, the law has finite `p`th moment from the empty diagram
for every real `p > 0`. Isometric embeddings preserve the law after pushforward,
and finite `PMF` inputs agree with the existing atomic `sampleLaw` after
`toMeasure`.
`RipsSamplingMeasureStability` proves that, for compact Borel probability
inputs, the actual diagram laws satisfy
`W_p ≤ 2 * choose(n,2)^(1/p) * GW_p` for real `p ≥ 1` and `n ≥ 2`, in every
natural degree, including full H₀ at degree zero
(`Rips.wasserstein_sampleLawMeasure_le_measureGromovWasserstein_allDegrees`). The Wasserstein cost is over couplings of whole diagrams with
`bottleneck` as its ground metric; the input distortion GW infimum ranges over
all probability couplings and needs no optimizer. The same module proves
`Rips.wassersteinInfinity_sampleLawMeasure_le_measureGromovWassersteinInfinity_allDegrees`:
for every sample size and degree, the whole-diagram bottleneck
`W_∞` distance between the laws is at most `2 * measureGromovWassersteinInfinity`.
This uses essential suprema directly, with the factor `2` from the half-distortion
GW convention; it assumes no optimal coupling or finite-`p` limit. See
[sampled Rips diagram laws](math/sampled-rips-laws.md).

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
infinite-dimensional. `RipsQTameDiagram` consumes this q-tameness to extract
decorated finite and essential occurrences with exact rectangle, essential-strip
and tail counts. Their support is countable and locally finite even for this
infinite-fiber example. On finite metric spaces,
`Rips.qTameDiagramMultiplicity_eq_diagramOccurrenceCount` identifies every
decorated point multiplicity with its occurrence count in the existing finite
`Rips.diagram`, including essential bars. The coefficient field and vertex
type must currently share a Lean universe for this theorem because the existing
rank/barcode bridge has that restriction; the mathematical compatibility holds
over every field. Isometric relabelling preserves the complete decorated diagram
even when the auxiliary linear orders are unrelated, by proving equality of the
finite-death rectangle contents and essential birth-strip contents.
`LocallyFiniteDiagramBottleneck` constructs a countably
supported, locally finite decorated occurrence diagram from any q-tame real
module and defines its extended matching-cost infimum. `Diagram.toLocallyFinite`
embeds a finite diagram only with an explicit `Diagram.IsPositive` proof, and
`bottleneck_toLocallyFinite` proves finite bottleneck compatibility on that
positive domain. `RipsQTameBottleneck` uses the Rips multiplicity theorem to
prove the corresponding finite Rips statement between two finite metric spaces.
`RipsQTameInfiniteMetricStability` passes the strict-slack Hausdorff interleaving
bound to the exact factor-two bound for the complete locally finite diagrams of
nonempty totally bounded spaces. The carrier types share a universe, while the
coefficient and ambient spaces may use independent universes. The compact
Gromov–Hausdorff consumer has the same carrier-universe restriction and needs no
order-preserving optimal-coupling isometries. Variable finite samples converge
to any nonempty totally bounded target when their ambient Hausdorff distances tend
to zero. `RipsQTameInfiniteMetricStabilityExamples` checks this with increasing
finite samples of the genuinely infinite compact set `{0} ∪ {1/(n+1) | n ∈ ℕ}`.
Endpoint decorations remain in multiplicity while only real endpoints enter
matching costs. See
[the finite-net proof](math/rips-metric-stability.md#totally-bounded-spaces).

`TDA.Persistence.RipsHausdorffInterleaving` compares the actual Rips homology
modules of arbitrary isometric images in a common metric space, over every
ring and in every degree. Finite Hausdorff distance r gives an actual
ε-interleaving whenever ε > 2r and hence a module-distance bound of 2r.
Near points with positive slack replace closest-point selection, so the
images may be nonclosed. An extended-Hausdorff-distance bound handles
arbitrary images; nonempty totally bounded images give the real-valued
bound without compactness or completeness. The infinite open and closed
unit intervals provide a nonclosed fixture at zero module distance.
These results make no infinite-diagram claim. See
[the construction and scope](math/rips-hausdorff-interleaving.md).

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

`TDA.Filtration.CechRelation` compares different label types through a native relation
whose related coordinates are within ε in one ambient space. It proves shifted-face
geometry for both infimum-radius sublevels and exact closed-ball nerves, without
assuming an optimal center. `TDA.Persistence.CechRelationInterleaving` supplies their
canonical homology interleavings over arbitrary rings and the full finite-diagram
relation bound over fields. `Cech.bottleneck_dgm_le_hausdorffDist` bounds the finite
radius-filter diagrams by the Hausdorff distance of their ranges, with constant one,
allowing unequal label counts and repeated coordinates. Its extended-distance form
gives an α+β bound for two finite samples of any common target; the target needs no
diagram. Same-range configurations have equal full diagrams. The real Hausdorff bound
requires nonempty configurations. See [ambient Čech Hausdorff stability](math/cech-hausdorff-stability.md).

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
upper half-plane; its transport consumers inherit these results.
`FiniteWeightedCoalescing` forms such a diagram from finite indexed strict bars
by summing masses at equal coordinates. Feasible matrices aggregate along the
coordinate fibers and split back by explicit proportional kernels. These maps
preserve the full geometric powered boundary cost and carry optimizers in both
directions, including zero weights and repeated coordinates. The powered and
rooted value identities hold for every real exponent; rooted minimization uses
p≥1. Unit weights recover the existing
unit-occurrence transport and matching values.
`BoundaryTransportAtomic` identifies its native matrix optima with boundary
transport over all Borel plans between the associated atomic measures, as
described below. A weighted exponent limit remains outside this API. See
[finite real-weight boundary transport](math/finite-weighted-boundary-transport.md).

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

## Vertex-height stability of graph-PL Reeb quotients

For a simple graph `G` and vertex heights `h g : V → ℝ` with `|h v - g v| ≤ ε` at every vertex,
`GraphPL.abs_plHeight_sub_le` bounds `|plHeight G h x - plHeight G g x|` by `ε` at every
realization point, for `V` in any universe and without finiteness. `GraphPL.edist_ofFun_plHeight`
identifies the `UniformFun` extended distance of the two piecewise-linear heights with that of the
vertex heights, and `GraphPL.edist_ofFun_plHeight_eq_edist` with the product extended distance
`edist h g` for `[Fintype V]`, which is `0` for empty `V`. `GraphPL.vertexHeightInterleaving` is
`perturbationInterleaving` for that bound, with representative-level maps given by inclusion of
inverse images. For `V : Type` and `[Finite V]`,
`GraphPL.geometricInterleavingDistance_graphPLReebGraph_le` bounds the geometric interleaving
distance of `graphPLReebGraph G h` and `graphPLReebGraph G g` by `ε`,
`GraphPL.geometricInterleavingDistance_graphPLReebGraph_le_edist_ofFun` by the `UniformFun`
distance of the vertex heights, and `GraphPL.geometricInterleavingDistance_graphPLReebGraph_le_edist`
by `edist h g` for `[Fintype V]`. The heights may cross, merge or separate, and horizontal edges
may appear or disappear; the graph is fixed. The bound is not an equality: reversing the endpoint
heights of a single edge gives distance `0` with `edist h g = 1`. For finite nonempty `V`,
`GraphPL.sSup_range_plHeight` and `GraphPL.sInf_range_plHeight` identify the extremes of the
attained range with `Finset.univ.sup' _ h` and `Finset.univ.inf' _ h`, and
`GraphPL.ofReal_abs_sup'_sub_le_geometricInterleavingDistance_graphPLReebGraph`, its `inf'` form
and its `max` form bound the distance below by the displacement of the extremal vertex heights
(`RGraph.ofReal_abs_sInf_sub_le_hausdorffEDist` is the real-line step). The distance equals
`edist h g` when `edist h g` equals one extremal displacement
(`GraphPL.geometricInterleavingDistance_graphPLReebGraph_eq_edist_of_sup'`, `_of_inf'`); in
particular `GraphPL.geometricInterleavingDistance_graphPLReebGraph_add_const` gives
`ENNReal.ofReal |c|` for the translate `fun v => h v + c`, on any graph. For empty `V` the distance
is `0` (`GraphPL.geometricInterleavingDistance_graphPLReebGraph_of_isEmpty`). The translate is
exact already for interval components: `interleavingDistance_intervalComponents_add_const` gives
`‖c‖₊` for every continuous height on a nonempty space with range bounded below, and with
`GraphPL.plHeight_add_const` it rederives the graph-PL value. For finite graphs `G` on `V` and `G'` on `V'` in `Type`,
every `HeightMapPair (plHeight G h) (plHeight G' h') ε` bounds the geometric interleaving
distance of `graphPLReebGraph G h` and `graphPLReebGraph G' h'` by `ε`
(`GraphPL.geometricInterleavingDistance_graphPLReebGraph_le_of_heightMapPair`), through the
identification of that distance with the interval-component distance; no map of graph objects is
constructed, and `HeightMapPair.ofUniformBound` recovers the fixed-graph vertex budget. See
[height-controlled maps](math/reeb-graph-pl.md#height-controlled-maps-between-graph-pl-spaces).
For the merge tree
`GraphPL.mergeY` with heights `GraphPL.mergeHeights a M = (0, 0, a, M)` and
`0 < a < b ≤ 2a`, `b ≤ M`, `GraphPL.geometricInterleavingDistance_mergeY` gives the exact
distance `ENNReal.ofReal (b - a)`, which is `edist` of the heights (`GraphPL.edist_mergeHeights`),
while both extremal displacements are `0` (`GraphPL.max_ofReal_abs_sub_mergeHeights_eq_zero`).
The lower bound is the cardinality obstruction
`le_interleavingDistance_of_forall_exists_card_lt` (with `_symm`,
`Interleaving.card_range_map_le`, `Interleaving.card_le_of_injective` and
`Interleaving.isEmpty_of_card_lt_card_range`) applied to the component counts
`GraphPL.card_cellComponents_eq_card_activeEdges` and `GraphPL.card_cellComponents_eq_one`;
`interleavingDistance_eq_top_of_card_ne`, `RGraph.geometricInterleavingDistance_eq_top_of_card_ne`
and `GraphPL.geometricInterleavingDistance_graphPLReebGraph_eq_top_of_card_ne` give distance `⊤`
for different top counts, in particular for finite graphs with different numbers of connected
components. For `0 < a < b ≤ M`, `GraphPL.geometricInterleavingDistance_mergeY_eq_min` proves the exact
merge-tree distance `ENNReal.ofReal (min (b-a) (b/2))`. The continuous section `mergeSection`,
its height identity `plHeight_mergeSection`, and path theorem `exists_mergeSection_path` construct
the fold; the path at `c = M` runs along the horizontal edge `2 — 3` to vertex `2` at constant
height. `mergeFoldHeightMapPair` gives the `b/2` map-pair bound. The formula recovers `b-a` for
`b ≤ 2a`, and equals `b/2 < b-a` for `2a < b` (`GraphPL.geometricInterleavingDistance_mergeY_eq_half`
for `2a ≤ b`, and `GraphPL.geometricInterleavingDistance_mergeY_lt_vertex_budget` for the strict
inequality below the vertex budget when `2a < b`). Reflection proves the same exact value for the
split tree (`GraphPL.geometricInterleavingDistance_splitY_eq_min`). No converse to the map-pair
bound or formula for other tree shapes is claimed.
Common nonzero affine changes multiply graph-PL Reeb distances by the absolute slope
(`GraphPL.geometricInterleavingDistance_graphPLReebGraph_smul`, `_neg`, `_affine`), including
across different finite graphs. Exact values for other perturbations are not claimed. The vertex-height
bound does not extend to continuous functions that agree with the heights only at the vertices. See [graph-PL heights](math/reeb-graph-pl.md#vertex-height-perturbations-of-a-fixed-graph).

For categorical Mapper reconstructions of two vertex-height functions on one finite graph, with
finite bounded covers of the two attained ranges and resolutions `res`, `res'`,
`interleavingDistance_coverComponents_le_add` bounds the assembled precosheaves of any
continuous `f, g` at pointwise distance `ε` by `r + ε + r'` (and `_edist`, `_le_two_mul_add`).
`geometricInterleavingDistance_mapperReeb_le_add_edist` bounds the reconstructions by
`res + edist h g + res'` for `[Fintype V]`; `geometricInterleavingDistance_mapperReeb_le_add` is
the vertex-budget form, `_retained` forms use retained resolutions and
`geometricInterleavingDistance_mapperReeb_le_two_mul_add_edist` is the one-cover form.
`geometricInterleavingDistance_graphPLReebGraph_le_mapperReeb_add` and
`geometricInterleavingDistance_mapperReeb_le_graphPLReebGraph_add` compare the Mapper and Reeb
distances up to `res + res'`; `ofReal_abs_sup'_sub_le_geometricInterleavingDistance_mapperReeb_add`
and its `inf'` form give lower bounds for finite nonempty `V`.
`tendsto_geometricInterleavingDistance_mapperReeb_pair` (and `_retained`) prove convergence to
`d_geo(ℛ(h), ℛ(g))` along covers with vanishing resolutions, and
`exists_graphPLMapperReconstruction_pair_le` gives finite covers with distance at most
`edist h g + 2 r`. Every cover must cover the attained range of its own height; the empty cover
of a nonempty graph is at distance `⊤` from the Reeb quotient. The bounds are not sharp in
general, and reconstructions over different graphs are not compared. For a vertical translate
with the translated cover the distance is exact:
`geometricInterleavingDistance_graphPLMapperReconstruction_add_const` gives `ENNReal.ofReal |c|`
at every finite cover with a member of nonempty inverse image (`_of_covers` under coverage on a
nonempty vertex type), through `coverComponentsTranslateIso` and
`interleavingDistance_coverComponents_add_const`. Without such a member it fails: reconstructions
over empty covers are at distance `0`
(`geometricInterleavingDistance_graphPLMapperReconstruction_of_isEmpty`, from
`RGraph.geometricInterleavingDistance_eq_zero_of_isEmpty`), while the Reeb quotients of `h` and
`h + 1` are at distance `1`. See
[categorical Mapper approximation](math/mapper-reeb-approximation.md#two-inputs).

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
a Nerve Lemma. Ordinary Mapper refinements induce selector-independent homology
maps on the ordered chain model; the resulting modules carry interleaving, finite-barcode,
step-diagram and capped centred bottleneck bounds, including bounds from height-map pairs
between different domains, for supplied component orders. No multinerve selector independence,
independence of the component orders, Nerve Lemma or diagram of the uncapped centred tower is
claimed. The Mapper–Reeb quotient identification and convergence
claims concern finite graph-PL inputs, not arbitrary higher-dimensional Reeb spaces.

Finite GH–Rips stability and sampling compare full diagrams of finite metric spaces;
the possibly infinite sampling target has no diagram in these results. Finite
weighted boundary transport permits real masses, and its canonical atomic
measures have the same optima over all Borel boundary plans. Attainment for
general finite Radon inputs remains open. Finite-line adapters construct modules
over a ring; rectangular matrix-sequence adapters require a commutative ring. Over a field, both reuse
finite interval classification without computing barcodes over arbitrary fields. Gaussian
C₀ universality and signed-measure separation concern the full birth–death plane;
positive persistence measures require a strictly positive weight and finite weighted
mass. These conclusions do not make finite-pixel images characteristic.

General geometric tame-function PH stability, locally finite diagrams and their stability
for infinite q-tame modules, manifold charts
and executable arbitrary-field decomposition are outside the reviewed PH scope. A first
stable release must state its selected results and limitations; it need not finish every
roadmap extension. This guide describes the current API and does not announce a release.


### Collapsed-boundary geometry

`TDA.Persistence.BoundaryTransportGeometry` equips the strict birth–death half-plane
with one additional boundary point. The distance between interior points is the
minimum of their maximum-coordinate distance and the sum of their distances to the
diagonal; the distance to the boundary is half the lifetime. This metric is complete
and separable. The interior has its usual topology, is open and dense, and its Borel
sets determine the Borel structure of the enlarged space. Collapsing the diagonal of
the closed half-plane defines a measurable Lipschitz map onto this space.

`TDA.Persistence.BoundaryPlans` uses Borel measures on closed-half-plane pairs
outside the diagonal–diagonal region. Their two interior marginals are prescribed;
boundary marginals are free. Every admissible plan has mass at most the sum of
the input masses. The explicit deletion/insertion plan sends each bar to its
nearest diagonal point and has cost equal to the sum of the diagonal persistence
moments. Finite moments therefore give a finite-cost competitor and a finite
powered infimum over all admissible plans. `BoundaryPlanLaws` proves self-value
zero and symmetry by identity plans and a cost-preserving measurable transposition.
The optimization and its reciprocal-p root remain extended nonnegative values.

`ReservoirMeasure` augments an interior measure to a common finite mass by adding
a boundary atom. The interior restriction is preserved, and for every positive p
the p-th boundary moment is exactly the original diagonal persistence moment.
Paired capacities dominate the sum of the original masses. Finite augmented
measures are regular on the collapsed Polish space; dividing by a positive
capacity gives probability measures and the corresponding moment scaling.

`BoundaryTransportForward` and `BoundaryTransportReverse` compare every admissible
plan in both directions. The forward map collapses the diagonal and adds a
boundary–boundary atom. The reverse map keeps a direct interior leg when its
distance is no greater than the two boundary legs, and otherwise splits it into
deletion and insertion. For p at least one, both transformations preserve the
required marginals and do not increase powered cost, including infinite values.
`BoundaryTransportComparison.boundaryTransportPowerValue_eq_reservoirPowerValue`
identifies the two infima for every finite capacity dominating the sum of the
original masses; the reservoir value is independent of that capacity. Taking the
reciprocal-p root gives the corresponding distance-value equality.

`ReservoirNormalization` proves the probability scaling law by multiplying every
competitor measure by the reciprocal capacity and reversing that operation.
The powered value scales by the capacity; for positive p its root scales by
the capacity raised to 1/p. Together with the comparison theorem, this identifies
boundary transport with that scaled capacity-one reservoir value. The paired
probability statement retains the full sum-of-masses capacity bound.

`BoundaryTransportZero` identifies the powered value against zero with the
diagonal persistence moment, for every finite-mass input and p at least one.
It gives both the reciprocal-p root formula and the p-th power of distance to
zero, including when the moment is infinite.

`BoundaryTransport.atomicMeasure` assigns each native finite weighted
diagram its positive atomic measure on the strict half-plane. Its singleton
masses are exactly the diagram's coefficients, so coincident terms in a
finitely supported sum contribute their combined mass. Every feasible native
matrix gives an admissible measure plan with exactly its native powered cost.
Conversely, every Borel plan between these atomic measures gives a feasible
matrix by taking its interior singleton-pair masses. The remaining row and
column masses equal its deletion and insertion masses, whose nearest-diagonal
charges bound the original plan's charges. This comparison permits arbitrary
diagonal endpoints, including a continuous distribution of them, and infinite
competitor costs.

`boundaryTransportPowerValue_atomic_eq_native` identifies the all-plan powered
infimum with the native finite weighted optimum for nonnegative exponents.
For p at least one, the reciprocal-p roots agree as well. The native finite
optimizer supplies an actual minimizing Borel boundary plan; fractional masses
and zero inputs are included.

In `BoundaryTransportIndexed`, `atomicMeasure_ofIndexed` identifies the same
measure with the original indexed Dirac sum. The indexed/coalesced plan maps
preserve the full powered boundary cost of every feasible finite matrix and
transport actual optimizers in both directions. Their all-Borel powered and
rooted values recover the indexed
weighted values for p≥0 and p≥1, respectively, and recover the existing finite
matching values for unit masses. The construction accepts repeated coordinates
and zero weights; splitting and then aggregating recovers every coalesced matrix
entry.

`BoundaryTransportAttainment` exports `exists_minimizing_boundaryPlan`, constructing a
minimizing Borel plan for arbitrary finite inputs and p≥1, including when the
optimal cost is infinite. `exists_minimizing_reservoirPlan` gives the
reservoir minimum for p≥0 and finite positive full sum-capacity.
`exists_finite_cost_minimizing_boundaryPlan` uses finite diagonal moments to
obtain finite cost, and `exists_minimizing_boundaryPlan_rooted` realizes both
powered and rooted values with the same plan. The proof derives weak
compactness and cost lower semicontinuity from pinned mathlib; neither is a
caller premise. A nonatomic band and a countable noncompact input with
infinite Euclidean first moment exercise the result. An admissible
infinite-cost competitor still permits a finite attained optimum.

`BoundaryTransportQuantization` identifies the native diagram of a simple
interior quantizer with the exact pushforward of its input. Its graph plan
uses a full sum-of-masses reservoir and bounds the native powered/rooted
costs. `BoundaryTransportApproximation` constructs `quantizedDiagram μ n`
with exactly the original mass at every index. For finite original mass,
finite diagonal p-persistence and p≥1, its powered and rooted transport
errors tend to zero. `exists_atomicMeasure_approx_same_mass` gives a native
diagram at every positive accuracy, including zero inputs. Quantizers take
only interior values; the added reservoir atom remains separate from the
original mass. Scaled nonatomic and countable noncompact inputs exercise
this [same-mass approximation](math/boundary-transport-approximation.md).

`BoundaryTransportNorm` identifies each coupling's actual mathlib `eLpNorm`
with its rooted collapsed cost. It exposes the reservoir and native boundary
values as literal infima of these norms over the two marginal equations.
`boundaryTransportDistance_eq_normalized_iInf_eLpNorm` gives the probability
form with the exact factor R^(1/p) and the full sum-of-masses capacity bound.

`BoundaryTransportMetric` exports `boundaryTransportDistance_triangle`, the sharp
triangle inequality for arbitrary finite original measures and p≥1, using one
common reservoir capacity, actual minimizing plans and pinned mathlib kernel
composition and Minkowski. `boundaryTransportDistance_eq_zero_iff` proves
separation. Both permit infinite distances and require no persistence moment;
finite moments give finite distance through the existing bound. Translated
unit atoms realize the sharp triangle, the wrong-capacity example has full
powered infimum four instead of the native value two, and two same-mass
approximants control the error in the original distance. See
[finite-measure metric laws](math/boundary-transport-metric.md).

The bridge to an independently maintained ordinary Wasserstein API remains
open in [the transport contract](https://github.com/uda-lab/tda-lib/issues/505).
The [ordinary-OT dependency map](math/boundary-transport-ot-dependency.md)
identifies incompatible package pins, the current native bridges and the
unresolved article-source comparison.

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

### Sampled Rips laws

`Probability.FiniteSampling`, `SamplingMoments`, and `GromovWasserstein` provide
atomic probability couplings, iid sampling with replacement, sharp unordered-pair
moment bounds, and distortion GW with factor one half. Their measure-valued
counterparts in `MeasureCoupling`, `MeasureSampling`, and `MeasureGromovWasserstein`
use actual `ProbabilityMeasure` couplings with exact marginals. `RipsSampling`
applies the atomic estimates to full diagrams of finite tuple ranges, and
`RipsSamplingMeasureStability` proves finite-p and `W_∞` bounds on whole diagram
laws with bottleneck ground cost in every natural degree `q`, including degree
zero. The theorems
`Rips.wasserstein_sampleLawMeasure_le_measureGromovWasserstein_allDegrees` and
`Rips.wassersteinInfinity_sampleLawMeasure_le_measureGromovWassersteinInfinity_allDegrees`
state these bounds. Writing `U_{n,q}(μ) = Rips.sampleLawMeasure k μ n q`, they are

\[
 W_p(U_{n,q}(μ),U_{n,q}(ν))
 \le 2 {n\choose2}^{1/p} GW_p(μ,ν), \qquad p\ge1,\ n\ge2,
\]

and `W_∞(U_{n,q}(μ),U_{n,q}(ν)) ≤ 2 GW_∞(μ,ν)` for every `n`. The existing
positive-degree wrappers retain the names
`Rips.wasserstein_sampleLawMeasure_le_measureGromovWasserstein` and
`Rips.wassersteinInfinity_sampleLawMeasure_le_measureGromovWassersteinInfinity`.
At `q = 0` these are laws of the actual full ordinary H₀ diagrams, including
the essential `(0, ⊤)` occurrence for each nonempty sample; they do not state a
probability-law bound for reduced H₀ diagrams. The factor `2` uses the
half-distortion convention, without an optimizer or a finite-`p` limit.
`RipsSampleQuotient` identifies tuple-index and metric-sample Rips homology
filtrations by a natural isomorphism. See [sampled Rips laws](math/sampled-rips-laws.md)
for the finite-p and infinity bounds and the ε regression. The real-valued input
law has positive atoms at `0` and `1` for `0 < ε < 1`; on the separate Bool metric
chart induced by those coordinates, the full H₀ diagram has a finite bar dying
at `1` and lies exactly `1/2` from the singleton diagram. In that chart, the
`n = 2` atomic sample-law mass at the nontrivial diagram is `2ε(1−ε)`, tending to zero
as `ε → 0`; `sampleLaw_map_isometry` transports the whole law under isometric
embeddings, and `epsilonTwoPoint_realSampleLaw_nontrivial_mass` states this atom
for the real-valued input law. This does not give an arbitrary-`n` atom formula.
The compact Borel law and its finite-PMF agreement are described with the
`Rips.sampleLawMeasure` API above. The finite-PMF transport cost has not yet been
identified with the infimum over all Borel couplings on finite support.
`RipsReducedH0` defines reduced sublevel H₀ as the categorical kernel of the
augmentation induced by collapsing each Rips sublevel to a point. For a finite
nonempty metric space, `reducedSublevelH0Diagram_points_eq_finitePart` identifies
its diagram points with the finite part of the ordinary H₀ diagram, and
`reducedSublevelH0Diagram_points_eq_eraseEssential` proves that removing one
`(0, ⊤)` occurrence gives that multiset, preserving all other multiplicities.
This pointwise finite-space bridge concerns reduced diagrams; the compact
sampled-law bounds above concern full H₀ diagrams.

### Barycentric subdivision and prism homotopies

`PrismAdmissible f g` weakens contiguity: every mixed prism tuple over a source face is a
target face, although `f(s) ∪ g(s)` need not be one. `PrismAdmissible.chainHomotopy` is the
same signed prism homotopy, and `simplicialHomologyMap_eq_of_prismAdmissible` gives equal
homology maps in every degree over any ring. `TDA.Simplicial.ArbitraryApexCone` inserts a
chosen apex into each oriented tuple at its position in the ambient order; when the apex can
be inserted into every face (`ApexInsertionClosed`), `boundary_arbitraryApexConeFill_add`
contracts positive-degree chains and `boundary_arbitraryApexConeFill_zero` subtracts the
coefficient sum at the apex in degree zero. `TDA.Simplicial.BarycentricHomology` takes the
barycentric subdivision to be the mass-zero normalized subdivision flag complex. For a finite
nonempty ordered vertex type, the subdivision chain map and the last-vertex map form
`barycentricChainHomotopyEquiv`, and `barycentricHomologyIso` is natural for inclusions of
complexes. Over a field, `simplicialHomologyClass_zeroVertexCycle_ne_zero` shows that every
vertex has a nonzero `H₀` class. These results are stated for the ordered chain model only;
no comparison with singular homology is made.

### Finite-tree realizations and quotient comparison

For a leaf `ℓ` of `G : SimpleGraph V` with neighbour `m`, `leafHomotopyEquiv` is a homotopy
equivalence from `Realization G` to the realization of `G.induce {ℓ}ᶜ`, with forward map
`leafCollapse` and inverse `deleteVertexInclusion`; collapsing after including is the identity
(`leafCollapse_comp_deleteVertexInclusion`), and the leaf step assumes no finiteness. For
`[Finite V]`, `contractibleSpace_realization_of_isTree` and
`simplyConnectedSpace_realization_of_isTree` prove that the realization of a tree is
contractible and simply connected, and with `isTree_of_simplyConnectedSpace` they give
`isTree_iff_simplyConnectedSpace_realization` and `isTree_iff_contractibleSpace_realization`.
On an empty vertex type both sides are false. Trees on infinite vertex types and fundamental
groups of realizations with cycles are not treated, and no Reeb-quotient, cosheaf or Mapper
result uses these criteria. See
[contractible realizations of finite trees](math/reeb-graph-tree-contraction.md).

The general quotient comparison is surjective at every open but not injective in general: for
the first coordinate of the topologist's sine curve,
`Examples.TopologistsSineCurve.componentComparison_not_injective` and
`intervalComponentComparison_not_injective` prove non-injectivity at `⊤` and at the interval
`ℝ`. They do not show that the two cosheaves are not isomorphic, that the Reeb quotient is
homeomorphic to `[0, 1]`, or failure at smaller intervals. See
[the topologist's sine curve](math/reeb-quotient-comparison.md#the-topologists-sine-curve).

### Normalized subdivision-Rips and measure stability

The normalized subdivision-Rips modules construct open-radius finite flag
bifiltrations and their actual simplicial homology, including restricted-index
stability for a bounded perturbation of one labelled distance matrix. Finite
sup-norm Čech/Rips flag homology diagrams agree naturally. Common-ambient
finite-uniform GP has exact finite sup-norm witness reduction, the arbitrary
outlier-mass bound, and a concrete multicover interleaving. The large-face cover
has the exact multicover union and contractible intersections in normed
ambients. Its flag inclusion is a natural isomorphism on actual simplicial homology
(`cechHomologyToLargeFaceNerveIso`, from `cechHomologyToLargeFaceNerve_isIso`), over every
ring and in every degree; barycentric subdivision invariance supplies the inverse. A GP witness
interleaves the two large-face nerve homology diagrams by near-label vertex maps, and these
isomorphisms transport that interleaving to the subdivision-Rips modules.
`subdivisionRipsHomologyInterleavingDistance_le_gromovProkhorovEDist` bounds their restricted
homology interleaving distance by the finite-uniform GP distance, for finite nonempty metric
inputs in one universe; `subdivisionRipsHomologyInterleaving_of_isometric_embedding` gives the
outlier consumer. No comparison with the homology of the multicover space, homotopy
interleaving or bound for non-uniform measures is stated. See
[normalized subdivision-Rips and measure stability](math/subdivision-rips.md).

### Q-tame persistence rectangle measures

`TDA.Persistence.PersistenceMeasure` constructs the image-and-kernel quotient
`PersistenceMeasureSpace` and its dimension `persistenceMeasureValue` for
real modules over a field. A finite crossing image suffices for the
four-rank formula, birth and death splitting, and the crossing-rank bound;
`PModule.QTame.persistenceMeasureSpace_finiteDimensional` supplies this
finiteness on every rectangle separated from the diagonal.
`TDA.Persistence.PersistenceMeasureEssential` constructs essential-boundary
strip counts as the eventual dimensions of image quotients and proves
birth-coordinate additivity. It includes no assumed interval decomposition.
The decorated multiplicity representation is constructed below; its
bottleneck stability remains open. See
[persistence rectangle measures](math/persistence-rectangle-measure.md).

`TDA.Persistence.PersistenceMeasureBox` derives a rectangle box inequality
from a real interleaving. Its local theorem needs only a finite-dimensional
crossing image in the expanded rectangle; q-tameness supplies this when that
rectangle stays strictly above the diagonal. The public crossing factorization
and a displaced-interval fixture check the comparison on actual modules. See
[interleavings and rectangle measures](math/persistence-measure-box.md).

`TDA.Persistence.PersistenceMeasureEssentialBox` compares finite-target tail
quotients along an actual interleaving. A finite expanded crossing image is
sufficient locally. The inequality of defined essential minima needs only
target q-tameness; its interpretation as a genuine essential birth-strip box
inequality requires q-tameness of both modules. See
[interleavings and essential birth strips](math/persistence-measure-essential-box.md).

`TDA.Persistence.PersistenceMeasureMatching` derives a finite local occurrence
matching from two-sided positive-square count inequalities. Source lifetimes
must exceed 4ε and distinct source values must be separated by more than 2ε.
Its Hall argument retains multiplicities and bounds unmatched target costs.
See [local matching from finite box counts](math/persistence-measure-matching.md)
for the precise hypotheses and the remaining algebraic-stability bridge.

`TDA.Persistence.DecoratedMeasureCuts` identifies the existing persistence cuts with
mathlib lower sets, retaining boundary decorations and compact open coordinate cells.
`DecoratedRectangleCells` proves the semiring laws for finite separated rectangles, and
`DecoratedRectangleTopology` proves their compactness, openness and point separation.
`IntegerContentAtoms` constructs minimum-cell multiplicities of natural-valued additive
contents, finite atomic representations on compact cells, and finite local positive
support with exact cell counts. The construction permits infinite global support.
`PersistenceMeasureBoxContent` proves arbitrary finite box-partition additivity from the
actual module quotient split identities; `PersistenceMeasureContent` constructs the
module's actual `AddContent`. `PersistenceMeasureDiagram.moduleDiagramMultiplicity`
extracts finite-death decorated point counts, with finite local support and exact rectangle
counts. `DecoratedCutEndpoints` supplies finite numeric endpoints.
`PersistenceMeasureEssentialContent` and `PersistenceMeasureEssentialDiagram`
construct the essential birth-strip content and its multiplicities.
`PersistenceMeasureExtendedDiagram.moduleExtendedDiagramMultiplicity` includes death at
infinity, with exact finite rectangle, essential strip and full tail-rectangle counts and
finite positive support on every separated tail rectangle.
`PersistenceMeasureDiagramCountability` proves countable global support;
`PersistenceMeasureLowerBound` transfers a module zero tail to a birth lower bound.
Finite diagram compatibility and algebraic stability remain separate obligations.
See [integer contents on decorated cells](math/persistence-measure-atoms.md).


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
explicit absence of intervening deletion times. `deletionGrid` consists of the
terminal scale and actual finite vertex-deletion times at or before it;
`sparseComplex_eq_activeUnion_deletionGrid` proves this finite union presents the
sparse complex. `tailDeletionHomologyIso` retracts the earliest stage from a
finite union when the remaining scales are later and no deletion occurs before
the next one. `isIso_terminal_activeUnion` iterates this retraction over a
complete grid. `isIso_sparse_relaxed` identifies the resulting sparse complex
with the relaxed complex on homology; `sparseRelaxedHomologyIso` is the natural
isomorphism of their real-indexed persistence modules, including degree zero
and negative scales. `sparseRipsLogInterleaving` combines that isomorphism
with the relaxed/Rips inclusions. Reindexing positive radii by `exp` gives an
interleaving with shift `log((1−2η)⁻¹)` in every degree, including degree zero.
`sparseRipsLogDistance_le` bounds the corresponding module interleaving distance.
Each relaxed pair, including a weighted self-pair, has a closed, attained first
entry time (`pairEntry_mem`); `finiteWeight_eq_max_min` writes each finite-deletion weight as
`max 0 (min ((r−(1−2η)t)/2) (ηr))`, so `continuous_relaxedDistance` makes every relaxed pair
threshold closed in the scale. `finiteSparseFiltration` chooses an initial vertex when one exists
and is bottom on empty input. `faceEntry` takes the maximum over a face's pairs.
`mem_sparseCarrier_iff_faceEntry` shows that a nonempty candidate face occurs
precisely when this entry is at most every finite vertex-deletion time, including
equality. On that actual carrier,
`sparseFilter_sublevel_eq` identifies the finite filter's closed sublevels with
the sparse filtration. For a coefficient field in the vertex universe, an auxiliary linear
order on the vertices and a degree `n ≥ 1`,
`sparseLogDiagram_bottleneck_le` bounds the bottleneck distance from its
log-scale diagram to the diameter-scale Rips log diagram by
`log((1−2η)⁻¹)`. The diagram bound uses the proved module interleaving and
finite-constructible matching. Degree zero retains the module interleaving;
zero-born classes do not fit the finite positive-log diagram.
`parameterOfTolerance` converts `0 < τ ≤ 1` to `η = τ/(2(1+τ))`, for which the
multiplicative factor is `1+τ`; at `η=1/3` the factor is `3`. `sparseFilter_positiveOnEdges`
supplies the positive filter. `TDA.Filtration.SparseRips.Examples` checks both weight
breakpoints, the deletion-time tie between closed and open activity, a weighted self-pair, an
edge entering at its distance, and a deleted singleton retained by the sparse union.
`ClosedBallDoubling.packing_bound`
gives the uniform separated-set bound `Λ^h` from iterated closed-ball covers.
`facesOfDimension_card_le` bounds the number of distinct j-simplices in the full
all-scales carrier by `Fintype.card V · (Λ^h)^j`; `skeletonFaces_card_le` bounds its m-skeleton
by `Fintype.card V · Σ_{j=0}^m (Λ^h)^j`. Here `2/2^h < η(1−2η)`, and the depth can be chosen
from η alone. The constants are independent of cardinality, metric spread and
maximum scale. `LineSamples.uniform_skeleton_bound` uses one doubling bound of
four at every sample size.

On four vertices with the shortest-path metric of a cycle, adjacent distances
are one and opposite distances are two. At scale one,
`H1Examples.sparseFilter_h1_nonzero` constructs a rational `H₁` class from the
four-edge chain: its boundary cancels, and there are no 2-faces to fill it.
`H1Examples.sparse_relaxed_h1_nonzero` shows that the sparse-to-relaxed
inclusion carries this class nontrivially. All four vertices remain active at
this scale. `H1Examples.deleted_pendant_h1_nonzero` extends the metric by a
short pendant point attached near the seed. That point passes its deletion time
before scale one (`pendant_inactive_one`), while the four cycle vertices remain
active. The core inclusion and collapse compose to the identity, so the cycle's
nonzero `H₁` class survives in the sparse complex and maps nontrivially to the
relaxed complex. The sparse complex retains faces from earlier scales through its union;
the deletion claim concerns the closed active complex at scale one.
