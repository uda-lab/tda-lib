# Public API and import guide

For a short overview, start with the [guide by subject](README.md). This guide
describes the current checkout; the [changelog](../CHANGELOG.md) links to published
versions and their migration information.

## Entry points

```lean
import TDA.Persistence -- one ordinary library area
```

Use `import TDA.Library` for all eight ordinary areas, including `TDA.Probability` and
`TDA.Sheaf`, which have their own aggregators and pin files. These entry points exclude the standalone example and
acceptance modules. The standalone `TDA.Persistence.EphemeralIntervalIso` module identifies
the algebraic sum of all real singleton intervals with the rational ephemeral module. The two
rational Hom-cover demonstrations are in
`TDA.Persistence.FiniteRankProjectiveHomCoverExamples`; import either module directly or use
`TDA.Persistence.Examples` for both and the other Persistence examples.
For other worked examples, import their module directly or import the area's example
aggregator.
`TDA.Examples` collects the seven example aggregators; `TDA.Probability` has no fixtures.

`import TDA` deliberately loads both `TDA.Library` and `TDA.Examples`. It is the
comprehensive root used by the build, theorem axiom audits and module-reachability
coverage. The default `lake build` therefore still builds every module, even though
ordinary consumer imports are smaller. `scripts/build-docs.sh` generates API pages
from `TDA.Library` and its transitive imports. Standalone examples remain available through
their source modules and example aggregators; they are outside the normal documentation target.

This is a module boundary, not an export whitelist: Lean imports expose the declarations
of their dependencies, including existing small examples embedded in implementation
modules. The area aggregators and the library/example roots contain only imports.
Namespaces containing `Examples` are for demonstrations, not the main consumer API.

## Areas and intended use

| Import and namespace | Main definitions and theorem families | Requirements and scope |
|---|---|---|
| `TDA.Filtration` / `TDA.Filtration` | `SimplicialFiltration`, support, `FilterFunction`, sublevels, `CompatibleOrder`, `OrderingEquivalent` and order chambers; ambient Čech complexes and relations (`Cech`); greedy sparse Rips filtrations (`SparseRips`, one-parameter) and normalized subdivision-Rips bifiltrations (`SubdivisionRips`) | Values belong to nonempty faces. Ordered values are separate from the ambient vertices; compatible enumerations require finite total faces. Support can grow with the index. |
| `TDA.Simplicial` / `TDA.Simplicial` | Face `Chain`, signed `boundary`, square-zero chain complex, inclusion maps, `vertexChainMap`, `simplicialChainMap`, `simplicialHomology` / `simplicialHomologyMap`, finite coordinates, `VertexMap` / `Contiguous` / `PrismAdmissible`, arbitrary-apex cones (`ApexInsertionClosed`) and `barycentricHomologyIso` ([barycentric subdivision and prism homotopies](#barycentric-subdivision-and-prism-homotopies)) | Signed chains use an ambient vertex order and a ring. `simplicialHomologyMap` takes its source and target vertex types in one universe, with the ring in an independent universe. Finite-dimensional homology additionally uses a field and finite faces. A vertex map may identify vertices; contiguity is reflexive and symmetric, with composition laws, and is not asserted transitive. Cone contractions assume the chosen apex is a face and can be inserted into every face (`ApexInsertionClosed`). For barycentric homology, the vertex type is finite and nonempty, and its finite subsets have an auxiliary `LinearOrder (Finset V)`; naturality is for same-carrier inclusions. |
| `TDA.Persistence` / `TDA.Persistence` | `PModule`, structure maps and reindexing; finite intervals, rank barcodes and decomposition; `Diagram`, `dgm`, reduction, stability and calculus | The functor core needs a ring and a preorder, with independent coefficient/index/carrier universes. Finite decomposition has its narrower field, finite-chain, pointwise finite-dimensional and same carrier/coefficient universe assumptions. Sublevel diagrams and calculus retain their stated vertex-order, finite-face and local-lift hypotheses. `dgm` takes its coefficient field in the universe of the vertex type (`V : Type u`, `k : Type u`). |
| `TDA.Topology` / `TDA.Topology` | `CoverFamily`, `Covers`, `Refinement`, `nerve`, `nerveMap`, `nerveMap_contiguous`, `MultiNerveCell`, its `projection` and `multiNerveMap`, path-cover and cosheaf interfaces; measure bifiltrations on the restricted two-copy index (`MeasureBifiltration`), finite-uniform Gromov–Prokhorov witnesses (`FiniteGromovProkhorov`, `FiniteGromovProkhorovWitness`) and the large-face multicover cover (`MulticoverCover`); [quotient maps after products](math/reeb-thickening-constructible.md#point-set-tools) with a locally compact or proper factor (`isQuotientMap_prodMap_id_left`, `isQuotientMap_prodMap_id_right`, `isQuotientMap_prodMap_id_Icc`, `isQuotientMap_prodMap_id_of_isProperMap`, `isQuotientMap_prodMap_id_of_compactSpace`); [realizations, subdivision mesh and nerves of nested convex families](#realizations-subdivision-mesh-and-nerves-of-nested-convex-families): `Realization`, `Realization.coordinateStar` and `Realization.nerve_coordinateStar`, iterated barycentric subdivision (`SubdivisionRealization.complex`, `realize`, `barycentricProjection`) with the mesh bound `SubdivisionRealization.diam_le`, nerve-preserving thickenings (`exists_pos_nerve_thickening_eq`, `exists_pos_common_convex_thickening`) and the nerve inclusion theorems `ConvexNerve.isIso_simplicialHomologyIncl` and `ConvexNerve.isIso_simplicialHomologyIncl_of_compact`; [the algebraic core of singular Mayer–Vietoris](#the-algebraic-core-of-singular-mayervietoris): small singular chains (`simplicesIn`, `smallSimplices`, `smallChains`), `shortExact_smallChains`, the connecting map `bicartδ` with `bicartδ_eq`, `bicartδ_flip` and `bicartδ_naturality`, and the criterion `quasiIso_of_iterate_mem`; [affine chains and the subdivision diameter bound](#affine-chains-and-the-subdivision-diameter-bound): `AffineChains.affineSSet`, the cone `coneMap` with `coneMap_d` and `coneMap_zero_d`, `toSingularChains`, and the bounds `IsSubdivisionSimplex.diam_range_realize_le` and `IsIteratedSubdivisionSimplex.diam_range_realize_le`; [small chains of a cover and the Mayer–Vietoris sequence](#small-chains-of-a-cover-and-the-mayervietoris-sequence): `quasiIso_smallChainsι` for a cover by interiors, `mayerVietorisδ` and the exactness lemmas `mayerVietoris_exact_inter`, `mayerVietoris_exact_sum` and `mayerVietoris_exact_space` | An indexed set family need not cover anything; `Covers` states coverage separately. Labels may repeat and members may be empty. A nerve face is nonempty and has a common witness. Refinement selectors need not be injective. A multinerve cell is a path component of a nonempty finite intersection; the projection to the nerve is an order isomorphism only under `IntersectionsPathSubsingleton`. The quotient-map product lemmas place no separation hypothesis on the quotient map; product stability is stated only for a locally compact factor or a proper surjection, not for arbitrary quotient maps. The convex nerve inclusion theorems take a finite linearly ordered index type and families of subsets of a real normed space; the subdivision, mesh and star-intersection contractibility statements take a finite vertex type. |
| `TDA.Probability` / `TDA.Probability` | Atomic `Coupling`, `iid`, `transportCost`, `wasserstein` and `wassersteinInfinity`; the `pairEnergy` and `pairMaximum` moment bounds; `gromovWasserstein` and `gromovWassersteinInfinity`; the measure forms `MeasureCoupling`, `iidMeasure`, `measureWasserstein`, `measureGromovWasserstein` and their infinity versions | Couplings have exact probability marginals and costs are extended nonnegative infima; no optimizer is assumed. Atomic inputs are `PMF`s, measure inputs `ProbabilityMeasure`s. Gromov–Wasserstein uses the one-half distortion convention. The area contains no diagrams; `TDA.Persistence.RipsSampling` and `RipsSamplingMeasureStability` consume it. |
| `TDA.Reeb` / `TDA.Reeb` | Inverse-image path components, Reeb quotients and comparison maps; interval cosheaves, smoothing, interleavings and extended distance; finite data, graph realizations with the finite tree criteria `isTree_iff_simplyConnectedSpace_realization` and `isTree_iff_contractibleSpace_realization`, the incidence quiver and `incidenceGraph` of finite data with `card_incidenceGraph_edgeSet_le` and `RGraph.cosheafEquivalence`; `thickeningQuotient`, `thickeningQuotientAbsorptionIso`, `thickeningQuotientCompIso`, and `isRGraph_quotient_thickening_of_isConstructibleSpace`; `rgraphToConstructible`, `quotientRGraphAdjunction`, `RGraph.constructibleSmoothing`, `ConstructibleInterleaving`, `ConstructibleInterleaving.equivGeometric`, `constructibleInterleavingDistance`, `constructibleInterleavingDistance_eq_geometricInterleavingDistance` and `constructibleInterleavingDistance_eq_interleavingDistance`; `CylinderPresentation.levelHomeomorph`, `realizationSpace`, `levelPerturbation`, `CriticalValues.translate`, the [vertex-height perturbation API](math/reeb-graph-pl.md#vertex-height-perturbations-of-a-fixed-graph) of graph-PL heights (`abs_plHeight_sub_le`, `edist_ofFun_plHeight`, `edist_ofFun_plHeight_eq_edist`, `vertexHeightInterleaving`, `interleavingDistance_intervalComponents_plHeight_le`, `interleavingDistance_intervalComponents_plHeight_le_edist_ofFun`), and the [level-change stability, range and exact-distance API](math/reeb-geometric-interleaving-equivalence.md#level-perturbations-of-a-fixed-presentation), and translation of interval precosheaves (`OpenInterval.translate`, `translateFunctor`, `translatePre`, `translationInterleaving`, `Interleaving.isEmpty_of_nonempty_of_isEmpty`, `le_interleavingDistance_of_forall_exists_isEmpty`, `intervalComponents_add_const`, `interleavingDistance_intervalComponents_add_const`) with `GraphPL.plHeight_add_const` and `RGraph.geometricInterleavingDistance_eq_zero_of_isEmpty`, and [vertical translation of graph objects](math/reeb-rgraph-translation.md) (`RGraph.translateOver`, `toOverTranslateIso`, `translateRGraph`, `translateRGraphZeroIso`, `translateRGraphCompIso`, `cosheafFunctor_translateRGraph_obj`, `Interleaving.translatePre`, `interleavingDistance_translatePre`, `geometricInterleavingDistance_translateRGraph`, `geometricInterleavingDistance_translateRGraph_self`, `reebRel_add_const_iff`, `quotientTranslateIso`, `thickeningTranslateIso`, `geometricSmoothingTranslateIso`); reindexing of interleavings along interval functors (`Interleaving.reindex`, `reindexIso`), interval scaling (`OpenInterval.scale`, `scalePre`, `Interleaving.scalePre`, `interleavingDistance_scalePre`, `intervalComponents_smul`, `interleavingDistance_intervalComponents_smul`), and height-controlled map pairs (`HeightMapPair`, `HeightMapPair.natTrans`, `HeightMapPair.natTransSymm`, `HeightMapPair.natTrans_app_mk`, `HeightMapPair.natTransSymm_app_mk`, `HeightMapPair.interleaving`, `HeightMapPair.symm`, `HeightMapPair.ofUniformBound`, `HeightMapPair.interleavingDistance_le`, `HeightMapPair.interleaving_eq_perturbationInterleaving`), and [presentation morphisms on a common grid](math/reeb-thickening-constructible.md#presentation-morphisms) (`CylinderPresentation.Hom`, `Hom.realize`, `Hom.height_realize`, `Hom.realize_id`, `Hom.realize_comp`, `Hom.toOverHom`, `FiniteReebData.Hom.toPresentationHom`, `realize_toPresentationHom`, `isQuotientMap_prodMap_quotMk`, `prodMap_quotMk_eq_iff`, `isQuotientMap_rawBandMap`), and the [thickening of one cylinder](math/reeb-thickening-constructible.md#one-cylinder) (`Thickening.cylinderThick`, `Thickening.cylinderThickHomeomorph`, `Thickening.cylinderHeight_cylinderThickHomeomorph`, `Thickening.vertexStripHomeomorph`, `Thickening.botIncl`, `Thickening.topIncl`, `Thickening.mapSpace`, `Thickening.pairThickHomeomorph`), [windows and transfers of a presentation](math/reeb-thickening-constructible.md#windows-and-transfers) (`CylinderPresentation.Window`, `windowMk_eq_iff`, `windowToSpace`, `transfer`, `transferFamily`, `transferHomeomorph`), and [the thickening presentation of a presentation](math/reeb-thickening-constructible.md#the-general-presentation) (`CylinderPresentation.thick`, `edgeIncl`, `vertexIncl`, `toProd`, `ofProd`, `thickHomeomorph`, `height_thickHomeomorph`, `shiftedThickHomeomorph`), and [constructibility of thickenings](math/reeb-thickening-constructible.md#theorem-427) (`CylinderPresentation.thickOverIso`, `isConstructibleSpace_thickening_of_isConstructibleSpace`, `thickeningFunctor`, `isConstructibleSpace_thickening_of_isRGraph`, `CylinderPresentation.windowFiberHomeomorph`), and the [thickening–cosheaf comparison on constructible ℝ-spaces](math/reeb-thickening-cosheaf-comparison.md) (`constructibleThickeningComparisonIso`, `constructibleThickeningQuotientComparisonIso`, `thickeningFunctorZeroSection`, `thickeningFunctorZeroIso`, `constructibleThickeningValueEquiv`, `constructibleThickeningQuotientValueEquiv`) | Components are path components of the inverse-image subspace. The tree criteria assume a finite vertex type; realizations of infinite trees are not claimed. General quotient comparison is a natural transformation. The graph/constructible-cosheaf equivalence is scoped to the declared finite real-graph category and value universe `0`. Smoothing and geometric comparisons have separate contracts; geometric thickening composes laxly, by a height-preserving addition map that is not an isomorphism but becomes one after the Reeb quotient, and geometric smoothing of graph objects composes additively, `U_ε U_δ ≅ U_(ε+δ)`; geometric interleavings of graph objects correspond bijectively to interleavings of their component cosheaves, so the geometric and cosheaf interleaving distances coincide and the geometric one satisfies the triangle inequality. Geometric smoothing enlarges along `ε ≤ δ`, geometric interleavings are monotone in the parameter, and every graph object is within geometric distance `ε` of its `ε`-smoothing. Constructible interleavings correspond bijectively to geometric interleavings of the Reeb graphs; the constructible distance equals the cosheaf distance of the interval components of the spaces themselves; zero distance does not give an isomorphism of spaces. The incidence graph forgets parallel edges; edge counts use `Nat.card`. An interval-local component obstruction excludes geometric interleavings whose double-thickening restriction is injective from a nontrivial to a subsingleton value; the parallel loop and the single edge have geometric distance exactly `1/4`. Absorption `ℛ T_ε ≅ U_ε ℛ` holds on all constructible ℝ-spaces; constructibility of `T_ε X` itself is the separate `isConstructibleSpace_thickening_of_isConstructibleSpace`. Level-change stability fixes the presentation and number of levels; compact locally path-connected pieces supply constructibility. Exact translation distance requires a nonempty realization. Arbitrary continuous perturbations are outside that API. The vertex-height bound controls the piecewise-linear extension of the vertex heights on a fixed graph, not arbitrary continuous functions with the same vertex values. The exact translation distance of interval components assumes a nonempty space and a range bounded below; the identity height of `ℝ` shows the bound is needed. Translation of graph objects is an isometry of the geometric distance; the exact self-translation distance `|c|` assumes a nonempty total space and is `0` otherwise. Scaling on graph objects, translation of the display locale and of Mapper reconstructions as graph objects are not provided. Nonzero scaling multiplies interval-precosheaf distances by the absolute scalar; reflection is an isometry. A `HeightMapPair` supplies continuous maps with height error at most `ε` and composite paths with height deviation at most `2ε`; it is a sufficient interleaving criterion, with no converse, functional-distortion identity or optimality claim for the `2ε` path-deviation allowance. Presentation morphisms fix the grid and the cylinder parameter and need no Hausdorff, compact or locally path-connected pieces; `isQuotientMap_rawBandMap` presents the thickened realization by its thickened raw pieces, and no colimit theorem for arbitrary constructible spaces is claimed. The realization of `cylinderThick` is homeomorphic to `E × [a, d] × [-ε, ε]`, preserving height, for every topological `E`, `ε ≥ 0` and `a ≤ d` on every grid listing the four events; for a whole presentation, `thickHomeomorph` is the corresponding homeomorphism on every grid listing the shifted levels. Windows carry the quotient topology of their raw pieces and are not claimed to be height-window subspaces; transfers need not be injective at slab ends. The thickening of every constructible ℝ-space is constructible for every `ε ≥ 0`, with no Hausdorff hypothesis, presented on the shifted witness `S.shifted ε`; this is an admissible critical set, and its minimality is not claimed. The identification of the vertex pieces with height fibers (`windowFiberHomeomorph`) follows from the theorem and is not used in its proof. On constructible ℝ-spaces, in universe `0`, `C' T_ε ≅ S_ε C'` (Theorem 4.24 restricted) and the companion `C'' ℛ T_ε ≅ S_ε C'` are natural in all height-preserving maps, with `S_ε` the smoothing of constructible cosheaves; the companion identifies components, not points of the Reeb quotient with points of the space, and on graph objects both are the existing graph comparisons. Degree-zero singular homology of interval preimages is naturally the linearized component cosheaf (`intervalSingularHomologyIso₀`; see the [API section](#degree-zero-singular-homology-of-interval-preimages)). |
| `TDA.Mapper` / `TDA.Mapper` | `ComponentIndex`, pullback component covers, `mapper`, its one-skeleton, `multiNerveMapper` and its projection onto `mapper`, refinement maps including `multiNerveMapperMap`, graph-PL comparison, uniform interval covers (`uniformCover`) with attained-range coverage, the label-set cell equivalence `cellsOverLabelsEquiv` with graph-PL edge cells, height-separating uniform covers (`HeightSeparating`, `exists_heightSeparating_uniformCover`, `range_plHeight_eq_Icc`) with the splitting `cellComponentsEquivSum`, vertex cells (`vertexCellsEquiv`) and the cell classification `uniformVertexCellsEquivLevel`, `uniformVertexCellsEquivSpans`, `uniformEdgeCellsEquivSpans` through `EdgeCrosses` and `EdgeSpans`, finite Reeb data of graph-PL input (`CoversVertexHeights`, `vertexHeightLevels`, `LevelVertex`, `SpanEdge`, `levelEnd`, `graphPLReebData`, `uncoveredEdgeEquivCrossesOfLevel`, `induceComponentsEquivOfEq`) with the star and gap bijections `graphPLStarEquiv`, `graphPLGapEquiv`, their incidence laws `graphPLStarEquiv_map_left`, `graphPLStarEquiv_map_right` and the finite-data isomorphism `graphPLExtractHom`, `graphPLExtractIso`, closed level sets of graph-PL height (`ClosedLevel`, `IsLevelWindow`, `closedLevelComponentsEquiv`, `componentMap_levelInclusion_bijective`, `graphPLReebDataVEquivClosedLevel`), constructibility and the cosheaf identification of graph-PL height (`isConstructibleAt_intervalComponents_plHeight`, `cellGraphIsoOfSameLevels`, `graphPLCosheafIsoOfIso`, `graphPLCosheafIso`, `isConstructibleCosheaf_intervalComponents_plHeight`, `cosheafFunctorGraphPLIso`, `geometricInterleavingDistance_graphPL`), the Reeb quotient of graph-PL height (`compactSpace_realization`, `exists_coversVertexHeights`, `graphPLReebMap`, `graphPLReebQuotientHomeomorph`, `graphPLReebQuotientIso`, `graphPLReebQuotientIsoOfIso`, `intervalComponentNatTrans_graphPLReebMap`, `isRGraph_graphPLReebQuotient`, `graphPLReebGraph`, `graphPLReebGraphIso`, `isIso_intervalComponentComparison_plHeight`, `geometricInterleavingDistance_graphPLReebGraph`), [executable incidence extraction](math/mapper.md#executable-incidence-extraction) from a Boolean adjacency function and rational heights (`HeightGraph`, `HeightGraph.Valid`, `HeightGraph.levels`, `HeightGraph.criticalValues`, `HeightGraph.coversVertexHeights`, `HeightGraph.label`, `HeightGraph.label_eq_label_iff_reachable`, `HeightGraph.componentEquiv`, `HeightGraph.cellList`, `HeightGraph.edgeList`, `HeightGraph.incidence`, `HeightGraph.incidence?`) and its identification with the finite Reeb data and the Reeb quotient (`HeightGraph.reebData`, `HeightGraph.reebDataIso`, `HeightGraph.reebDataIso_hom_v_inl`, `HeightGraph.reebDataIso_hom_v_inr`, `HeightGraph.reebDataIso_hom_e`, `HeightGraph.extractReebDataIso`, `HeightGraph.reebQuotientIso`, `HeightGraph.isEmpty_realization`), vertex-height stability of the graph-PL Reeb quotient (`heightRange_graphPLReebGraph`, `geometricInterleavingDistance_graphPLReebGraph_le`, `geometricInterleavingDistance_graphPLReebGraph_le_edist_ofFun`, `geometricInterleavingDistance_graphPLReebGraph_le_edist`, and `geometricInterleavingDistance_graphPLReebGraph_le_of_heightMapPair`) with extremal vertex-height lower bounds and exact vertical translation (`sSup_range_plHeight`, `sInf_range_plHeight`, `ofReal_abs_sup'_sub_le_geometricInterleavingDistance_graphPLReebGraph`, `ofReal_abs_inf'_sub_le_geometricInterleavingDistance_graphPLReebGraph`, `geometricInterleavingDistance_graphPLReebGraph_add_const`), the graph-PL realization as a constructible ℝ-space (`barycentric`, `t2Space_realization`, `edgePoint_eq_vertex_iff`, `edgePoint_eq_edgePoint_iff`, `locallyPathConnectedSpace_realization`, `realizationMap_injective`, `LevelPiece`, `levelPieceHomeomorph`, `compactSpace_closedLevel`, `locallyPathConnectedSpace_closedLevel`, `graphPLPresentation`, `graphPLPresentationMap`, `graphPLPresentationHomeomorph`, `graphPLComponentDataIso`, `graphPLReebMap_graphPLPresentationMap`, `graphPLPresentationIso`, `isConstructibleSpace_graphPLOver`, `graphPLReebQuotientIsoOfIso_graphPLComponentDataIso`, `graphPLSpace`, `quotientRGraphFunctor_obj_graphPLSpace`, `overBaseMap_graphPLSpace`, `isRGraph_quotient_thickening_graphPLOver`), and `CoherentCoverTower`, member-adapted MultiNerve Mapper comparison (`LevelsAdapted`, `exists_levelsAdapted`, `labelFace`, `uniformMapperData`, `uniformMapperCellsEquiv`, `uniformMapperIso`), refinement of graph-PL finite Reeb data (`graphPLRefineIso`, `graphPLRefineHom_trans_v`, `uniformMapperCanonicalIso`, `graphPLRefineToOverIso`), the ordinary one-skeleton comparison `incidenceGraphUniformMapperIso`, `mapperOneSkeletonGraphPLIso` and `mapperOneSkeleton_connected_iff`, refinement-induced homology maps `mapperHomologyMap` with `mapperHomologyMap_eq`, `mapperChainHomotopy`, and the persistence module `mapperHomologyPModule` of refinements along a preorder with `mapperHomologyPModule_eq` and `CoherentCoverTower.structureMap_mapperHomologyPModule`, interleavings from cover maps between real towers (`mapperHomologyShiftMap`, `mapperHomologyInterleaving`, `mapperHomologyInterleaving_app_eq`, `realInterleavingDistance_mapperHomologyPModule_le`, `realInterleavingDistance_mapperHomologyPModule_le_add`), the pullback identification `mapperHomologyPModule_pullback`, and perturbation stability along the centred tower (`centredCover`, `centredCoverRefinement`, `centredMapperHomologyInterleaving`, `realInterleavingDistance_centredMapperHomology_le`), height-map-pair bounds for centred Mapper modules (`centredMapperPairVertexMap`, `_natural`, `_comp`, `centredMapperPairHomologyMap`, `centredMapperPairHomologyMapSymm`, `centredMapperPairInterleaving`, `realInterleavingDistance_centredMapperPair_le`, `_ofUniformBound`, `_graphPL_le`); these require supplied component orders but no finiteness, coverage or nonemptiness, and provide no diagram or bottleneck bound for the centred tower itself (the capped centred map-pair bounds are below), no converse, multinerve Mapper, order independence or executable Mapper extraction; and finite Mapper barcodes `mapperBarcode` with `mapperHomologyPModule_finiteDimensional`, `mapperBarcode_eq`, `nonempty_mapperBarcodeIso`, `finrank_range_mapperHomologyMap`, `mapperBarcode_eq_iff`, `nonempty_iso_iff_mapperBarcode_eq`, `CoherentCoverTower.finrank_range_simplicialHomologyMap` and the graph-PL face-finiteness instance `GraphPL.finite_mapperFace`, and two-input stability of categorical Mapper reconstructions (`interleavingDistance_coverComponents_le_add`, `geometricInterleavingDistance_graphPLMapperReconstruction_eq`, `geometricInterleavingDistance_mapperReeb_le_add_edist`, `geometricInterleavingDistance_graphPLReebGraph_le_mapperReeb_add`, `geometricInterleavingDistance_mapperReeb_le_graphPLReebGraph_add`, `ofReal_abs_sup'_sub_le_geometricInterleavingDistance_mapperReeb_add`, `tendsto_geometricInterleavingDistance_mapperReeb_pair`, `exists_graphPLMapperReconstruction_pair_le`), and categorical Mapper reconstruction of constructible ℝ-spaces (`finite_intervalComponents_constructibleSpace`, `constructibleMapperReconstruction`, `geometricInterleavingDistance_constructibleMapperReeb_eq`, `_le`, `_le_retained`, `tendsto_geometricInterleavingDistance_constructibleMapperReeb`, `retainedCoverResolution_le_coverResolution`), and rank obstructions to real interleavings (`finrank_range_structureMapLinear_le_of_realInterleaving`, `structureMap_eq_zero_of_realInterleaving`, `isEmpty_realInterleaving_of_finrank_lt`, `le_realInterleavingDistance_of_finrank_lt`, `le_realInterleavingDistance_of_structureMap_ne_zero`) and the zero-map interleaving `nonempty_realInterleaving_of_structureMap_eq_zero`, with their Mapper and centred-tower forms (`isEmpty_face_mapper`, `isEmpty_realInterleaving_mapperHomologyPModule_of_finrank_lt`, `le_realInterleavingDistance_mapperHomologyPModule_of_finrank_lt`, `isEmpty_realInterleaving_mapperHomologyPModule_of_isEmpty_face`, `le_realInterleavingDistance_mapperHomologyPModule_of_isEmpty_face`, `le_realInterleavingDistance_centredMapperHomology_of_finrank_lt`), and diagrams of step towers (`mapper_eq_bot_of_isEmpty`, `mapper_eq_bot_of_isEmpty_componentIndex`, `isZero_simplicialHomology_mapper_of_isEmpty`, `stepTower`, `stepRefinement`, `mapperHomologyPModule_stepTower`, `isConstructible_stepTower`, `stepMapperDiagram`, `stepMapperDiagram_eq`, `stepMapperDiagram_isPositive`, `stepMapperDiagram_eq_ofIndexBars_succ`, `stepMapperDiagram_eq_ofIndexBars`, `bottleneck_stepMapperDiagram_le`, `bottleneck_stepMapperDiagram_le_add`, `bottleneck_stepMapperDiagram_eq`, `stepMapperDiagram_interleaving_iff_matching`, `realInterleavingDistance_stepTower_eq_top_iff`), and the tightness of the step bounds (`le_bottleneck_stepMapperDiagram_of_finrank_lt`, `le_bottleneck_stepMapperDiagram_of_isEmpty_face`, `le_bottleneck_stepMapperDiagram_of_structureMap_ne_zero`, `isEmpty_realInterleaving_stepTower_of_isEmpty_face`, `heq_stepTower_shiftGrid`, `stepTowerToShiftGrid`, `stepTowerOfShiftGrid`, `bottleneck_stepMapperDiagram_shiftGrid_le`, `SurvivesToLast`, `le_realInterleavingDistance_stepTower_shiftGrid`, `realInterleavingDistance_stepTower_shiftGrid_eq`, `bottleneck_stepMapperDiagram_shiftGrid_eq`, `mapperHomologyMap_zero_ne_zero`, `survivesToLast_zero`, `bottleneck_stepMapperDiagram_shiftGrid_eq_zero_degree`, `bottleneck_stepMapperDiagram_eq_top_iff`), and exact translation of categorical Mapper reconstructions (`coverResolution_add_const`, `coverComponentsTranslateIso`, `interleavingDistance_coverComponents_add_const`, `geometricInterleavingDistance_graphPLMapperReconstruction_add_const`, `_of_covers`, `isEmpty_graphPLMapperReconstruction_of_isEmpty_cover`, `geometricInterleavingDistance_graphPLMapperReconstruction_of_isEmpty`), and capped centred step towers (`centredInterval`, `cappedIndex`, `cappedCentredCover`, `stageRadius`, `mem_cappedCentredCover_succ_iff`, `cappedCentredRefinement`, `cappedCentredPullbackRefinement`, `cappedCentredDiagram`, `cappedCentredDiagram_eq_pullback`, `bottleneck_cappedCentredDiagram_le_of_stageRadius_le`, `bottleneck_cappedCentredDiagram_eq`, `bottleneck_cappedCentredDiagram_le`, `uniformGrid`, `bottleneck_cappedCentredDiagram_uniformGrid_le`, `bottleneck_cappedCentredDiagram_grid_le`, `bottleneck_cappedCentredDiagram_le_add`, `bottleneck_cappedCentredDiagram_plHeight_le`, `bottleneck_cappedCentredDiagram_plHeight_uniformGrid_le`), and direct different-domain capped centred map-pair results (`cappedCentredPairVertexMap`, `cappedCentredPairVertexMap_mk`, `cappedCentredPairVertexMapSymm`, `cappedCentredPairVertexMapSymm_mk`, `cappedCentredPairVertexMap_natural`, `cappedCentredPairVertexMap_comp`, `cappedCentredPairVertexMapSymm_comp`, `cappedCentredPairHomologyMap`, `cappedCentredPairHomologyMapSymm`, `cappedCentredPairInterleaving`, `bottleneck_cappedCentredDiagram_le_of_heightMapPair`, `bottleneck_cappedCentredDiagram_pair_le`, `bottleneck_cappedCentredDiagram_pair_uniformGrid_le`, `bottleneck_cappedCentredDiagram_pair_le_ofUniformBound`, `bottleneck_cappedCentredDiagram_pair_plHeight_le`, `bottleneck_cappedCentredDiagram_pair_plHeight_uniformGrid_le`), and essential counts (`card_essentialPart_stepMapperDiagram`, `bottleneck_stepMapperDiagram_lt_top_iff`, `fullComponentIndexEquiv`, `componentIndexFullEquiv`, `mapper_full_eq_top`, `fullMapperHomologyIso`, `finrank_simplicialHomology_mapper_full_zero`, `isZero_simplicialHomology_mapper_full_succ`, `isEmpty_mapper_face_one_of_unique`, `finrank_simplicialHomology_mapper_full_zero_of_unique`, `card_essentialPart_cappedCentredDiagram_zero`, `card_essentialPart_cappedCentredDiagram_succ`, `card_essentialPart_cappedCentredDiagram_zero_of_unique`, `bottleneck_cappedCentredDiagram_lt_top`, `card_essentialPart_cappedCentredDiagram_plHeight`, `card_essentialPart_cappedCentredDiagram_plHeight_zero_of_unique`); graph-PL height scaling (`plHeight_smul`, `geometricInterleavingDistance_graphPLReebGraph_smul`, `_neg`, `_affine`), split trees (`splitHeights`, `geometricInterleavingDistance_splitY`) and merge/split bounds (`ofReal_min_le_geometricInterleavingDistance_mergeY`, `_splitY`, `geometricInterleavingDistance_mergeY_bounds`, `_splitY_bounds`) | Input is a continuous map and an indexed target family. Coverage and multiplicity are explicit hypotheses where used. The MultiNerve Mapper is the multinerve of the component cover; its projection onto `mapper` is surjective and is an order isomorphism under `IntersectionsPathSubsingleton (componentCover f U)`. Every real number lies in at most two members of the uniform family exactly when `2g ≤ r` (for at least three members and `g < r`); its union is the window `(a, a + n(r − g) + g)` for `0 < g ≤ r`. The graph-PL finite Reeb data need no covering hypothesis; closed-level components are classified by `LevelVertex` for finite vertex sets, and inclusion into any level window is bijective on components. The star and gap comparison assumes every vertex height is a level of the critical list, while the Mapper comparison is at member-adapted levels. The refinement comparison assumes the coarser list covers the vertex heights. Constructibility at the specified critical list and the corresponding cosheaf identification assume a list covering the vertex heights and `V : Type`; constructibility at a noncovering list can fail (fixture D5). The Reeb quotient identification assumes a covering list, which cannot be dropped (fixture R6); the slice statements use `V : Type`, while the list-free corollaries need no list. The presentation map is injective for every list, while the homeomorphism assumes a covering list (fixture K5). Closed levels are compact and locally path-connected for finite vertex sets. The slice statements use `V : Type`. Finiteness is conditional; tower identity/composition are supplied coherence data. Refinement-induced homology maps use supplied linear orders on component-index types in one universe and any ring; two refinements between the same families induce the same map, and `mapperHomologyPModule` needs no selector identity or composition equations, agrees with the strict tower's maps and is independent of the selected refinements. A finite Mapper barcode is the canonical rank barcode of `mapperHomologyPModule` on `Fin N`; it needs finitely many faces of the given degree at every stage, a field, and the field, domain and index types in one universe. It is independent of the selected refinements and classifies these modules up to natural isomorphism; finite graphs with finitely many interval labels satisfy the finiteness hypothesis without coverage. Diagrams of real-indexed towers other than step towers, q-tame Mapper barcodes, independence of the component orders, multinerve barcodes and executable Mapper extraction are not provided. These constructions are noncomputable theory, not an executable Mapper implementation. The one-skeleton isomorphism assumes `2g ≤ r` and fails without it (fixture M5). Vertex-height stability fixes the graph and bounds the Reeb distance by `edist h g` without any order, level-count or constructibility hypothesis; it is not an equality in general, and extremal vertex heights bound it below and make it exact for vertical translations. Selected cover maps shifting by `η` in both directions between two real towers give an `η`-interleaving of their Mapper homology modules with no commutation assumed; maps at pointwise distance `δ` give a `δ`-interleaving along the centred tower. A step tower places finitely many cover families on the cells of a finite grid of radii, with an empty family before the first radius; its Mapper homology module is finite-constructible, and with finitely many faces in the given degree its real diagram `stepMapperDiagram` is the `ofIndexBars` image of the finite Mapper barcode. Cover maps shifting by `η` between two step towers bound the bottleneck distance of their diagrams by `η`, and that distance equals the real interleaving distance of the modules. No diagram or bottleneck statement is made for other towers, such as the centred tower, which is not finite-constructible on any grid; tightness is stated only for translations of the grid, below, and no order-independence statement is made. Capped centred step towers have an empty first stage, centred intervals of the grid radii and a full last stage. For maps at pointwise distance `δ`, their diagrams are at bottleneck distance at most `δ + μ` on a grid of mesh `μ`, and at most `δ` on a uniform grid of spacing `h` when `δ = p h`; for one map, two grids whose meshes, first radii and last radii are within `η` give diagrams within `η`. Fixtures show that neither the full last stage nor the mesh term can be dropped; coverage by a capped stage and sharpness of `δ + μ` are not claimed. Over a field, an `ε`-interleaving bounds the rank of each structure map `M(t → t + 2ε)` by the dimension of `N (t + ε)` when that one value is finite-dimensional; this gives lower bounds on the real interleaving distance, including the exact distance `1` of two shifted one-member towers and the bound `1/8` for the flat and steep maps. Bar-length lower bounds, tightness of the rank obstruction and the exact flat/steep distance are not claimed. Constructible-input reconstruction needs no Hausdorff, graph-PL or nonempty-input hypothesis and no supplied finiteness; its distance identity needs no coverage, while its error bounds and convergence need coverage of the attained heights. Two-input Mapper bounds require each cover to cover its own height's attained range, are inequalities rather than equalities, and compare reconstructions over one fixed graph only. The rank obstructions bound the bottleneck distance of two step diagrams below through the stage of the second tower at `t + ε`. The step tower on `shiftGrid ε c` has at `t` the family of the step tower on `c` at `t + ε`, and the selected stage refinements are cover maps shifting by `ε` in both directions, so the two diagrams are at bottleneck distance at most `ε`. If the homology map of the selected refinement from the first nonempty stage to the last stage is nonzero in degree `n` (`SurvivesToLast`), the bottleneck distance and the real interleaving distance are exactly `ε`; in degree `0` this holds whenever the first nonempty stage has a component index. The bottleneck distance of two step diagrams is infinite exactly when their numbers of essential bars differ. Essential multiplicity equals last-stage homology dimension; finite bottleneck distance is equivalent to equality of these dimensions even for maps on different spaces. A finite nonempty full family on path-connected input is a simplex, so capped centred diagrams on nonempty grids have one essential degree-zero bar and none in positive degree, and any two such diagrams have finite bottleneck distance. With one label, the degree-zero count is the number of path components, or graph components for graph-PL input. Births, several-label disconnected degree-zero counts and finite bars are not computed. The survival hypothesis cannot be dropped (degree-one loop fixture). Exact distances for pairs of grids that are not translates, bar-length lower bounds and tightness of the bound `η` beyond translations are not claimed. Translating the height and a finite bounded cover by `c` moves the reconstruction by exactly `|c|` when some member has nonempty inverse image; over empty covers the distance is `0`. A continuous map `φ` with `f' ∘ φ = f` induces the vertex map `mapperDomainMap φ hφ U : mapper f U → mapper f' U` (`pullbackRestrict`, `domainIndexMap`, `componentDomainRefinement`, `mapperDomainMap_id`, `mapperDomainMap_comp`, `mapperMap_comp_mapperDomainMap`) and, for domains in one universe, homology maps `mapperHomologyDomainMap` and the module morphism `mapperHomologyPModuleMap` with identity and composition laws, commuting with the refinement-induced maps; the component orders of the two domains are independent supplied data and `φ` is arbitrary. A homeomorphism over the codomain gives the isomorphism `mapperHomologyPModuleIso`, real interleaving distance `0` (`realInterleavingDistance_mapperHomologyPModule_homeomorph`) and bottleneck distance `0` of step diagrams with an empty initial family (`bottleneck_stepMapperDiagram_homeomorph`) and of capped centred diagrams (`bottleneck_cappedCentredDiagram_homeomorph`); for a graph isomorphism with corresponding vertex heights, `realizationHomeomorph` and `bottleneck_cappedCentredDiagram_plHeight_iso` give distance `0` of the capped centred diagrams of the piecewise-linear heights. Equality of the diagrams, compatibility with interleavings and multinerve maps, and homotopy invariance are not provided. Common nonzero affine changes scale distances across finite graphs by the absolute slope. A `HeightMapPair` between finite graph-PL spaces bounds the geometric distance of their Reeb quotients; it supplies no map between graph objects and no Mapper cover or reconstruction consequence; its Mapper homology consequences are the centred and capped centred map-pair bounds above. For the three-edge merge tree, `mergeSection` and `exists_mergeSection_path` give height-preserving sections and bounded realization paths, including the horizontal top edge when `c = M`; `mergeFoldHeightMapPair` gives a `b/2` height-map pair. For `0 < a < b ≤ M`, `geometricInterleavingDistance_mergeY_eq_min` proves distance `min (b-a) (b/2)`, recovering `b-a` when `b ≤ 2a` and giving `b/2 < b-a` when `2a < b`. Reflection gives the same exact split-tree value (`geometricInterleavingDistance_splitY_eq_min`). These formulas are specific to this tree and do not give a converse to the height-map-pair bound. |
| `TDA.Sheaf` / `TDA.Sheaf.Alexandrov` | `equivalence : X.Sheaf C ≌ (X ⥤ C)` with functor `principalSections` and inverse `kanSheaf`, `counitIso`, `unitIso`, `restrictionConeIsLimit`, `isPointwiseRightKanExtension`; `upperSetEquivalence`, `upperSetSectionsIso` for an unbundled preorder; `TDA.Sheaf.AlexandrovTranslation`: `sheafShift`, `shiftComparison`, `SheafInterleaving.equivRealInterleaving`, `sheafInterleavingDistance_eq` on `upperSpace ℝ`; `TDA.Sheaf.AlexandrovCoordinateTranslation`: the same with `SheafInterleaving.equivCoordinateInterleaving` and `coordinateInterleavingDistance` on `upperSpace (Fin n → ℝ)` | `X : TopCat.{v}` with `[Preorder X] [Topology.IsUpperSet X]`, `C : Type u` with `[Category.{v} C] [HasLimits C]`. Sheaves for the upper Alexandrov topology only; see [Alexandrov sheaves](#alexandrov-sheaves-of-persistence-modules). |

| `TDA.Sheaf` / `TDA.Sheaf.Alexandrov` | `equivalence : X.Sheaf C ≌ (X ⥤ C)` with functor `principalSections` and inverse `kanSheaf`, `counitIso`, `unitIso`, `restrictionConeIsLimit`, `isPointwiseRightKanExtension`; `upperSetEquivalence`, `upperSetSectionsIso` for an unbundled preorder; `TDA.Sheaf.AlexandrovTranslation`: `sheafShift`, `shiftComparison`, `SheafInterleaving.equivRealInterleaving`, `sheafInterleavingDistance_eq` on `upperSpace ℝ`; `TDA.Sheaf.RaySheaf`: `rayQ`, `rayB`, `rayLimitIso`, `rayCounitIso`, `unitInterleaving`, `raySheafInterleavingDistance_rayQ`, `isZero_rayQ_iff` on `raySpace` | `X : TopCat.{v}` with `[Preorder X] [Topology.IsUpperSet X]`, `C : Type u` with `[Category.{v} C] [HasLimits C]`. Sheaves for the upper Alexandrov topology only; see [Alexandrov sheaves](#alexandrov-sheaves-of-persistence-modules). |
| `TDA.Sheaf` / `TDA.Sheaf.AlternatingDecomposition` | `exists_decomposition`, `multiset_eq_of_iso`, `barcode`, `barcodeIso : M ≅ barcodeDiagram o (barcode M)`, `nonempty_iso_iff_barcode_eq`, `intervalMultiplicity`; `reflectSink` (additive functor), `reflectSinkIntervalSumIso`, `reflectSource`, `reflectSourceUnitIso`; `chainToDiagram` | `o : Fin n → Bool` orients the path on `Fin (n + 1)`; `M : Paths (Vertex o) ⥤ ModuleCat.{u} k` over a field with `[∀ X, FiniteDimensional k (M.obj X)]`. See [Finite alternating diagrams](#finite-alternating-diagrams). |
| `TDA.Sheaf` / `TDA.Sheaf.AlternatingHeredity` | `pathTensor`, `pathTensorAdjunction`, `projective_pathTensor`, `representable`, `pathTensorObjEquiv`; `resolution`, `resolutionSplitting`, `resolution_shortExact`, `enoughProjectives_diagram`, `hasProjectiveDimensionLT_two`, `ext_eq_zero` | Same diagrams `M : Paths (Vertex o) ⥤ ModuleCat.{u} k` over a field, with no finiteness assumption; `Ext` in any `HasExt` universe. See [Finite alternating diagrams](#finite-alternating-diagrams). |
| `TDA.Sheaf` / `TDA.Sheaf.RealStratification` | `orient`, `paths_hom_subsingleton`; `IsBasicOpen`, `isBasis_basicOpen`, `IsBasicOpen.inf`, `BasicCat`, `basicIncl`, `basicTopology`; `star`, `tau`, `tau_eq_iff`, `exists_star_tau`, `tauFunctor`; `isSheaf_basic_of_isIso_sameStratum`, `isSheaf_tauFunctor_comp`; `basisEquiv` | Breakpoints `p : Fin m → ℝ` strictly increasing; the basis sheaf condition holds for presheaves in any category; `basisEquiv` uses `ModuleCat.{0} k` for `k : Type`. See [Stratifications of the real line](#stratifications-of-the-real-line). |
| `TDA.Sheaf` / `TDA.Sheaf.LocalSystem` | `IsLocallyConstantOn`, `IsLocallyConstantOn.mono`, `restrict_isIso_of_isLocallyConstantOn`, `isIso_map_of_le_sup`; `transportIso`, `map_comp_transportIso_hom`, `transportIso_hom_eq_map`, `transportIso_trans`; `isIso_germ_of_isIso_map`, `isIso_germ_of_isLocallyConstantOn` | Sheaves of `ModuleCat.{0} k` on `realLine` for a ring `k : Type`; convex means `Set.OrdConnected`. The intended equivalence of `IsLocallyConstantOn` with "locally isomorphic to a constant sheaf" is not proved in Lean (#1250). See [Interval-local constancy on the real line](#interval-local-constancy-on-the-real-line). |
| `TDA.Sheaf` / `TDA.Sheaf.RealConstructible` | `IsConstructible`, `isIso_res_sameStratum`, `isConstructible_iff`; `starFunctor`, `sections`, `sections_obj_obj`, `sections_map_gen`; `basisSheaf`, `extension`, `extensionBasicIso`, `extensionStarIso`, `isConstructible_extension`, `finiteDimensional_sections`; `extensionSectionsIso`, `extensionSectionsIso_app_app`, `sectionsExtensionIso`; `Constructible`, `FinDiagram`, `sectionsFin`, `extensionFin`, `equivalence`, `equivalence_functor_obj_obj`, `equivalence_functor_obj_map_gen`, `equivalence_inverse_obj_obj` | Strictly increasing breakpoints `p : Fin m → ℝ`; `k : Type`, a ring for `isIso_res_sameStratum`, a division ring for `IsConstructible`, a field for the diagram side. Local constancy is the interval-local `IsLocallyConstantOn`; its intended equivalence with "locally isomorphic to a constant sheaf" is not proved in Lean (#1250). The derived comparison is #1183. See [Constructible sheaves on the real line](#constructible-sheaves-on-the-real-line). |
| `TDA.Sheaf` / `TDA.Sheaf.SheafFlasque` | `isFlasque_of_injective`, `GermSurjective`, `germSurjective_of_isFlasque`, `germSurjective_of_injective`, `germSurjective_of_epi`, `exists_local_preimage_of_exact`, `exists_glue₂` | Sheaves `X.Sheaf (ModuleCat k)` over a ring `k : Type` on `X : TopCat.{0}`. See [Flasque sheaves and section lifting on intervals](#flasque-sheaves-and-section-lifting-on-intervals). |
| `TDA.Sheaf` / `TDA.Sheaf.IntervalSections` | `openIoo`, `exists_section_lift_extend`, `exists_section_lift_Icc`, `sections_exact_Icc` | Subspaces `S ⊆ ℝ`; the extension step needs `S` order-connected, the global statements are for compact intervals `[u, v]` (all `u`, `v`). See [Flasque sheaves and section lifting on intervals](#flasque-sheaves-and-section-lifting-on-intervals). |
| `TDA.Sheaf` / `TDA.Sheaf.StalkPullback`, `TDA.Sheaf.PointSheaf` | `stalkPullbackSheafIso`, `stalkPullbackSheafIso_unit`, `germ_stalkPullbackSheafIso_hom` (and `germ_stalkPullbackSheafIso_hom_assoc`), `pullbackPushforwardAdjunction_unit_app_hom`, `stalkPullbackSheafIso_hom_naturality` (and `stalkPullbackSheafIso_hom_naturality_assoc`), `stalkPullbackSheafNatIso`, `stalkPullbackSheafNatIso_app`; `pt`, `toPt`, `eq_top_of_mem_pt`, `germ_top_bijective`, `exact_of_sections_top`, `isIso_of_bijective_app_top`, `constSh`, `germSurjective_constSh` | Continuous maps `f : X ⟶ Y` in `TopCat.{0}`, sheaves of `k`-modules over a ring `k : Type`. See [Cohomology of compact intervals](#cohomology-of-compact-intervals). |
| `TDA.Sheaf` / `TDA.Sheaf.RightDerivedHomology` | `homologyRightDerivedIsoOfInjective`, `homologyRightDerivedIsoOfQuasiIso`, `isIso_Q_map_comp_rightDerivedFunctorPlusUnit`, `singlePlus`, `singleFunctorIsoQ`, `rightDerivedFunctorPlusSingleIso` | Additive `F : C ⥤ D` between abelian categories, `C` with enough injectives; derived categories as instance arguments. See [Cohomology of compact intervals](#cohomology-of-compact-intervals). |
| `TDA.Sheaf` / `TDA.Sheaf.DerivedStalks` | `isIso_iff_isIso_stalk_homology` | `X : TopCat.{0}`, sheaves of `ModuleCat.{0} k` over a ring `k : Type`, `[HasDerivedCategory (X.Sheaf (ModuleCat k))]`. See [Cohomology of compact intervals](#cohomology-of-compact-intervals). |
| `TDA.Sheaf` / `TDA.Sheaf.IntervalCohomology` | `isZero_H_Icc`, `isIso_unit_constSh_Icc`, `isZero_H_constSh_Icc`, `isIso_derivedUnit_toPt_Icc` | `[u, v]` as `TopCat.of (Set.Icc u v)`, `k : Type` a ring; `Hⁱ` is homology of `pushforwardPlus k (toPt _)`. Vanishing holds for all `u`, `v`; the unit statements need `u ≤ v`. See [Cohomology of compact intervals](#cohomology-of-compact-intervals). |
| `TDA.Sheaf` / `TDA.Sheaf.FlasqueAcyclic` | `sections_exact_of_left_exact`, `epi_of_shortExact`, `isFlasque_of_shortExact`, `isFlasque_biprod`, `pushforward_shortExact_of_isFlasque`, `acyclic_pushforward_of_isFlasque`, `quasiIso_pushforward_of_isFlasque`, `isIso_rightDerivedFunctorPlusUnit_app_of_isFlasque`, `isIso_rightDerivedFunctorPlusUnit_app_toPt_of_isFlasque` | Sheaves of `k`-modules over a ring `k : Type` on `X : TopCat.{0}`, continuous `f : X ⟶ Y`; derived categories as instance arguments. See [Flasque acyclicity](#flasque-acyclicity). |
| `TDA.Sheaf` / `TDA.Sheaf.IntervalFibre` | `comp_toPt`, `H_iso_of_homeo`, `isIso_derivedUnit_toPt_app_of_homeo`, `isIso_toPt_Icc_self`, `isIso_derivedUnit_toPt_Icc_self`; `BandConvolution.fibre`, `fibreHomeo`, `coe_fibreHomeo_apply`, `fibreIso`, `fibreIso_toPt`, `isZero_H_fibre`, `isIso_derivedUnit_toPt_fibre` | Homeomorphisms `h : X ⟶ Y` in `TopCat.{0}` (`[IsIso h]`), `k : Type` a ring; fibres of the band projection `BandConvolution.q a`. The fibre statements take a derived category structure on `[y - a, y + a]` as an instance argument; the unit statement needs `0 ≤ a`. See [Cohomology of compact intervals](#cohomology-of-compact-intervals). |

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
separately. `termEvaluationEquiv` identifies the evaluated terms with the simplicial chains
of the active-occurrence simplex, sending the differential to the signed simplicial boundary.
`GeneratedUpsetResolution.chainComplex` and `projectiveResolution` package these actual maps
as a canonical Mathlib projective resolution, with characteristic object, differential and
augmentation equations. `term_isZero_of_degree_ge` shows that the degree-`r` term vanishes
for `m ≤ r`. `generatedSupport_hasProjectiveDimensionLE` and
`generatedSupport_projectiveDimension_le` give the actual ordinary dimension bound `m−1`,
with truncated natural subtraction. The empty-family module has numerical dimension `⊥`;
a singleton-generated upset is projective. Repeated labels need not give a shortest resolution.
The upset generated by the two incomparable atoms of `Bool × Bool` has ordinary dimension
exactly one over every field. No minimality or global-dimension conclusion is asserted.
See [join-indexed upset resolutions](math/generated-upset-resolution.md).
Over any field and for n ≥ 1, `RectangleHall.card_le_neighbors` applies to an
actual ε-interleaving of rectangle family modules with finite occurrence
indices `ι κ : Type` (universe 0). For selected source occurrences whose
`(4n−2)ε` transitions are nonzero, it bounds their count by the number of
neighbors at radius `(2n−1)ε`. A neighbor is a target occurrence whose
rectangle module has an actual interleaving at that radius with some selected
source module. Under the same field and n ≥ 1 hypotheses,
`RectangleMatching.exists_matching` uses this bound and the reversed
interleaving to produce one radius-`(2n−1)ε` occurrence matching.
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
other endpoint decorations are not identified with half-open modules. On this positive half-open
subclass, `real_distance_zero_iff_iso` shows that zero distance implies a natural isomorphism.
`RectangleHall.significant_iff_transition_ne_zero` identifies δ-significance of a rectangle
(some `p` and `p + δ·1` both lie in its support) with nonvanishing of its actual δ transition,
and `Rectangle.hom_ext` shows that a morphism of rectangle modules is determined by its scalar
at one point of a nonempty overlap. `RectangleFamily.module` is the finite biproduct of interval
modules with indices labelling occurrences, and `RectangleFamily.component_ext` lifts
componentwise equations to the family. `FiniteOccurrenceMatching.exists_two_sided` combines two
relation-preserving injections on selected occurrences from finite types `α β : Type` (universe 0)
into one partial matching covering both selected sides; the underlying `OccurrenceMatching`
structure is universe-polymorphic. The two Hall injections from the actual interleaving and its
reverse instantiate this combinator. For this rectangle instantiation, the
Schröder–Bernstein argument uses auxiliary labels to allow deletion only of
non-significant occurrences, then discards those labels.
The sharpness fixture is the standalone module
`TDA.Persistence.RectangleSharpExample`, loaded by
`TDA.Persistence.Examples` and not by the ordinary `TDA.Persistence`
aggregator. `RectangleSharpExample.interleaving` constructs Bjerkevik's
Example 5.2 over any field, using two Fin 3-indexed families of open rectangles
and the source's integral coefficient matrices. `interleavingDistance_eq_one` and
`bottleneckDistance_eq_three` prove the exact values 1 and 3, with lower
bounds on every actual witness radius. The explicit radius-three matching
retains all occurrences. `fails_smaller_constant` establishes sharpness of
the two-dimensional factor three, including in characteristic two; it makes
no optimality assertion in higher dimensions. `GradedFree.lift`
and `GradedFree.exists_lift_of_surjective` provide the natural universal property and lifting
property of graded free modules over a ring; `GradedFree.FinitelyPresented`
expresses finite presentation by homogeneous cokernels. For finitely presented modules on
`Fin n → ℝ`, `GradedFree.finitelyPresented_exists_finite_criticalCoordinates`
gives finite coordinate sets `S` such that `a ≤ b` has an invertible structure map whenever no
`Sᵢ` meets `(aᵢ, bᵢ]`, and `GradedFree.finitelyPresented_exists_pos_structureMap_isIso`
gives positive right-diagonal slack at every index.
Over a field and any preorder, `GradedFree.finitelyPresented_finiteDimensional`
proves every fiber of a finitely presented module finite-dimensional. Its proof
uses the actual finite free cover and its componentwise surjectivity; finite
generators suffice, so this consequence needs neither finite relations nor a
finite indexing poset.
The free module on a disjoint union of graded families has the sum universal property
(`GradedFree.sumDesc`, `GradedFree.sumDesc_unique`). `Presentation.adjoinRedundant` adjoins an
arbitrary graded family of redundant generators by adding the relations `new_v − chosenLift_v`,
and `Presentation.adjoinRedundantIso` proves the enlarged quotient naturally isomorphic to the
original one; finite families remain finite. For any morphism between two presented modules,
`Presentation.exists_chainMap_lift` supplies maps between their generator and relation free
modules making both presentation squares commute. These statements work over any ring and
preorder without finiteness assumptions. For real coordinate grades, `W(σ)` has generator grades
`gr(w) − σ`; `GradedFree.shiftIso` identifies `F(W(ε))` with `F(W)[ε]`, `GradedFree.delayedInclusion`
embeds `F(W(−ε))` in `F(W)`, `Presentation.cover_presentedShiftIso` records the free-cover
compatibility of `Presentation.presentedShiftIso`, and `GradedFree.finitelyPresented_shift` gives
closure of finite presentation under shifts. See
[the constructions and their scope](math/multiparameter-foundations.md#graded-free-modules-and-finite-presentations).
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

Naturally split pointwise short exact sequences with pointwise finite-dimensional middle fibers
are rank exact (`IsPointwiseShortExact.rankExact_of_section`), and restriction along a monotone
map preserves rank exactness (`IsRankExact.reindex`). Over a field, for `i < j` in a partial
order, the hook has support `{a | i ≤ a and j ≰ a}`, `Hook.homEquivKernel` identifies maps from it
to `N` with vectors of `N(i)` killed at `j`. `Hook.end_eq_smul_id` and
`HookInfinity.end_eq_smul_id` show that every endomorphism acts by one scalar throughout the
support, and `Hook.indecomposable` and `HookInfinity.indecomposable` prove indecomposability in
mathlib's categorical sense, with neither a finite grade set nor bounded support.
`RankDeflationExamples.epi_not_rankDeflation` verifies that the principal upset born at zero on
the two-grade chain surjects onto the hook dying at grade one without being a rank-exact
deflation. See
[rank exactness and hook lifting](math/multiparameter-foundations.md#rank-exactness-and-hook-lifting).

At each pair of comparable indices, `IsPointwiseShortExact.rank_add_iff_lift_kernel`
equates rank additivity with lifting dying vectors when the middle source fiber
is finite dimensional. `lan_lift_kernel` gives the corresponding lift that dies
at the same real grade after applying the finite-grid Kan functor, and
`Hook.exists_lift` constructs lifts of finite-death hook morphisms in this
pointwise finite-dimensional domain.
`HookInfinity.homEquivFiber` identifies principal-upset morphisms with birth-fiber
vectors; surjectivity at birth suffices to lift them over any ring and preorder.
Consequently, for `R : Type u` and `P : Type v` with `[Ring R]` and
`[Preorder P]`, `HookInfinity.module (R := R) i` is an ordinary projective
object of `PModule.{u,v,u} R P`; its canonical instance is available by
importing `TDA.Persistence.HookInfinityProjective`.

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
upset; on a finite poset with decidable equality, `rankProjectiveHookSum_multiplicity_unique`
proves that isomorphic finite sums of nonzero hooks have the same multiplicity for each tag;
`rankProjectiveHookSum_multiplicity_unique_of_iso` is the `Fin n → ℝ` form.
Over a field `k : Type u` and a partial order `P : Type`, the field-side
`IsRankProjective`, `IsRankDeflation`, `FiniteHookDeflation`, and
`IsRankExact.pushout` APIs use modules `PModule.{u,0,u} k P`. Here `P : Type`
is a universe-zero restriction, not a finiteness assumption. The generic
`IsPointwiseShortExact` and `IsRankExact` predicates remain generic over field
coefficients `k : Type u`, preorders `P : Type v`, and modules
`PModule.{u,v,w} k P`. The ring/preorder `HookInfinityProjective` and
`PullbackFiber` results also retain their broader universe-polymorphic scopes.
`IsRankProjective Q` itself has no pfd hypothesis on `Q` and no `[Fintype P]`
hypothesis; it states the relative lifting property against actual rank-exact
sequences. Finite-death hooks, principal
upsets and their finite categorical biproducts satisfy it; natural isomorphisms
and retracts preserve it. The finite-hook cover construction additionally
requires `[Fintype P]` and pfd fibers of its target `M`. For such an `M` on a
finite poset, `FiniteHookDeflation.π M` is an actual natural surjection from a
finite occurrence-indexed hook sum. Fiber and structure-map kernel bases prove
surjectivity and all dying-element lifts. `FiniteHookDeflation.rankExact` gives
the actual rank-exact kernel sequence; both source and kernel are pfd.
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
and zero-dimensional zero-module boundaries. Its fixture
`FinitePresentationHookKernel.Examples.finitelyPresented_actual_cover_kernel_finiteDimensional`
(an example, not loaded by `import TDA.Persistence`) applies the finite-dimensional fiber theorem
to the actual constructed kernel using only the original module's finite-presentation hypothesis.

For a field `k` and `M : PModule k (Fin n → ℝ)` (no positivity of `n` is needed),
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
`Fin n → ℝ`, with each zero-padded term represented by an actual
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
projective. These hook-Betti and signed-barcode declarations take
`M : PModule.{u,0,u} k (Fin n → ℝ)` with the finite-presentation hypothesis
`GradedFree.FinitelyPresented.{u,0,0}` (index carriers in `Type 0`), as the
existence and `2*n-2` bound theorems do, and assume no positivity of `n`.
`GradedFree.finitelyPresented_lowerIndexUniverse` converts a finite
presentation with index carriers in `Type u` to this form, and
`GradedFree.finitelyPresented_liftIndexUniverse` is the converse.

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

For a field and any preorder, `FiniteRankExactResolution.rank_eq_alternating_sum` proves, for a
supplied finite family of rank-exact rows `0 → K_(i+1) → Q_i → K_i → 0` (`i : Fin m`) with
`K_0 ≅ M` and `K_m ≅ 0`, that `r_M(a,b) = ∑ i, (-1)^i r_(Q_i)(a,b)` in the integers for every
`a ≤ b`, where `r` is the rank of the structure map; when `m = 0` the endpoint isomorphisms
identify `M` with zero. `FiniteRankProjectiveResolution.rank_eq_alternating_sum` gives the same
formula for the projective-resolution package, stated for partial-order index types in universe
zero; the telescope does not use projectivity. The statement concerns a supplied family of rows:
by itself it asserts no existence, minimality, uniqueness or length bound, and no stability.
`FiniteRankProjectiveResolutionExamples` covers the zero-length boundary, a nonzero
principal-upset hook and a two-term contractible resolution whose ranks cancel. See
[the Euler formula for finite rank-exact resolutions](math/finite-rank-projective-resolution.md).

For real-coordinate modules, `FiniteRankProjectiveResolution.identity` constructs the
selected length-one resolution from rank projectivity and pointwise finite-dimensional
fibers. `appendZero` and `appendZeros` preserve the zero-padded terms and add exactly the
requested number to the stored length; `termAt` reads the recorded term below that length
and returns zero afterward. When `0 < R.length`, `R.tail hpos` resolves the selected next
kernel and has stored length `R.length - 1`; no tail is defined at length zero. `R.shift ε`
transports the selected kernels, terms, rows and endpoint data along the diagonal evaluation
shift. The selected isomorphism `R.termAt_shiftIso ε j` identifies each zero-padded term
of the shifted resolution with the shift of the corresponding original zero-padded term.
The base-only examples include a nonminimal two-row resolution of zero whose tail resolves
the nonzero principal-upset module, and a positive shift carrying its actual map from
grades `-1` to `0` to the original map from `0` to `1`. These operations live in
`TDA.Persistence.FiniteRankProjectiveResolution`, so ordinary finite-resolution clients do
not need a Schanuel import. Open the `TDA.Persistence` scope to select coordinatewise order.
Padding can increase the stored length while leaving every `termAt` value unchanged.

When `R.length = S.length`,
`FiniteRankProjectiveResolution.biprod R S hlen` resolves the selected categorical sum `M ⊞ N`
and keeps the common stored length. Each kernel and term uses the `Fin.cast` alignment specified by
`hlen`; the row maps are the selected `biprod.map` morphisms. The public
`FiniteRankProjectiveResolution.termAt_biprodIso R S hlen j` identifies the result's
zero-padded term with the biproduct of the two zero-padded terms, using the chosen zero-biproduct
isomorphism at and beyond the common boundary. The constructor requires equal stored lengths;
pad a shorter input with `appendZero` or `appendZeros` before applying it. Repeated inputs remain
separate summands, and stored length is not a minimality or intrinsic-degree claim. The examples
include both nonzero component structure maps, repeated summands, zero summands and empty
resolutions, and the explicit padding of unequal original lengths.

The signed-multiset results do not select a canonical hook decomposition or a
unique comparison isomorphism. Choice independence of the signed multisets is by itself not a
stability theorem. Signed-barcode stability and the `2n−2` degree bound on the nonzero terms of
minimal resolutions (a bound on the highest nonzero zero-padded term, not on the stored length;
[Theorem 5.18](https://arxiv.org/html/2208.00300v3)) are proved separately: see the
real-coordinate degree bound below and
[signed hook bottleneck stability](#signed-hook-bottleneck-stability). The rank-exact structure
axioms of [Theorem 2.7(1)](https://arxiv.org/html/2208.00300v3) are not packaged as an
`ExactCategory` instance.

For any natural number `n`, field `k`, and originally finitely presented module
`M : PModule k (Fin n → ℝ)`,
`FiniteRankProjectiveResolution.exists_finiteRankProjectiveResolution_of_finitelyPresented`
constructs an actual finite rank-projective resolution of `M`. This includes
`n = 0`, where `Fin 0 → ℝ` is a one-point poset and the result applies to
nonzero modules as well. The existing
`finitelyPresented_exists_finiteRankProjectiveResolution` name remains the
positive-dimensional specialization. The proof first uses the finite
presentation to reconstruct `M` as the actual left Kan extension of a
pointwise finite-dimensional module on a finite coordinate grid. On that finite
poset it chooses rank-exact hook-sum covers with the fewest summands for each
successive kernel. A nonzero same-hook component into the preceding kernel
would split off a summand and contradict that choice. Thus every nonzero
differential arrow lowers the weight from its source hook to its target hook;
equivalently, the weights strictly increase as one passes to covers of
successive kernels. The weight is built from the sizes of the hooks' endpoint
lower sets, with infinite hooks placed above finite hooks. It is bounded on the
finite poset, so the iteration ends with zero kernel. The existing Kan
preservation maps then transport all rows and projective terms back to `M`.
No pfd, grid, hook decomposition, or resolution is an extra input.

For a quotient `π : Q ⟶ K`, `IsRankProjectiveCover π` certifies that `Q` is
rank-projective, that the actual categorical-kernel row
`kernel.ι π` followed by `π` is rank exact, and that every endomorphism of `Q`
fixed by `π` is an isomorphism. `IsRankProjectiveCover.exists_iso_over_quotient`
uses both covers' rank-projective lifting properties against the opposite
actual kernel rows and both quotient-fixed endomorphism criteria to show that
any two certified covers of the same target are naturally isomorphic over
that target. It makes no finiteness or resolution assumption, and does not
claim uniqueness of the comparison isomorphism or of an entire resolution.
For a coefficient field and partially ordered index type `P : Type`,
`IsRankProjectiveCover.of_identity` certifies the identity map of a pointwise
finite-dimensional rank-projective module, using its actual categorical-kernel
row.
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

For any natural number `n`, field `k`, and
`M : PModule k (Fin n → ℝ)`, the original public
`GradedFree.FinitelyPresented M` hypothesis proves that an actual
`MinimalFiniteRankProjectiveResolution` of `M` exists:
`FiniteRankProjectiveResolution.exists_minimalFiniteRankProjectiveResolution_of_finitelyPresented`.
This includes the one-point index poset at `n = 0`, including nonzero modules.
The existing
`finitelyPresented_exists_minimalFiniteRankProjectiveResolution` name remains
the positive-dimensional specialization. The construction reconstructs `M` up
to isomorphism as the actual left Kan extension of a pointwise finite-dimensional
module on a finite coordinate grid, applies the finite-poset minimal theorem,
transfers every row through Lan, and transports the result across the
reconstruction isomorphism. Every quotient row in the returned resolution
carries the public projective-cover certificate.
This is the finite-grid Kan transfer of [Theorem 2.7(2) and Appendix A of
Botnan–Oppermann–Oudot–Scoccola](https://arxiv.org/html/2208.00300v3).
`FiniteRankProjectiveResolutionKanExamples` checks the finite-resolution and
minimal-resolution interfaces on nonzero principal-upset free modules in zero
and one real coordinates. At zero coordinates it also derives both existence
results from an empty-generator presentation of the zero module.

For a certified minimal resolution `R`, `R.termAt j` is its recorded term when
`j < R.resolution.length` and the zero module afterward. Degree-vanishing
statements about `termAt` therefore concern the highest nonzero degree and do
not bound the stored length.

For arbitrary `k`, `n ≥ 1`, and only the original
`GradedFree.FinitelyPresented.{u,0,0}` hypothesis on `M`,
`FiniteRankProjectiveResolution.finitelyPresented_exists_minimalFiniteRankProjectiveResolution_with_bound`
constructs a certified minimal resolution whose `termAt j` is zero whenever
`2*n-2 < j`. The companion
`finitelyPresented_minimalFiniteRankProjectiveResolution_termAt_isZero` proves
the same strict bound for every supplied certified minimal resolution. Its
proof reuses the finite-grid theorem
`FiniteRankProjectiveHomQuotientDimension.coordinateGrid_minimalResolution_termAt_isZero`,
the actual left Kan transfer, and
`MinimalFiniteRankProjectiveResolution.termAt_nonempty_iso`; it assumes no
grid, pfd condition on `M`, or bound on the input resolution. The all-degree
comparison `CoordinateGrid.lanMinimalFiniteRankProjectiveResolutionObj_termAtIso`
exposes the correspondence of the actual transferred terms and zero padding.
This is a highest-nonzero-degree result, not a bound on the raw stored
`resolution.length`. Examples cover nonzero originally presented modules in
dimensions one and two, repeated birth occurrences, the zero module, and
arbitrary supplied resolutions. The proof follows the upper-bound portion of
BOOS Theorem 5.18 and Proposition 5.17; this upper-bound result itself has no
lower-witness or equality conclusion. In two real coordinates, the explicit
`RankResolutionDegreeTwo.realModule` is the actual Kan extension of a
three-point L-shaped finite-grid module. Its original finite-presentation
predicate is derived from the finite grid, and
`RankResolutionDegreeTwo.realMinimalResolution_termAt_two_iso` identifies the
second term of its concrete transferred minimal resolution with the actual
hook `H((1,1),(2,2))`. Every certified minimal resolution of that real module
has nonzero degree two and zero terms above degree two. Separately,
`finite_hookHom_projectiveDimension_eq_two` computes ordinary projective
dimension two for the finite hook-generator Hom object; it is not the ordinary
functor-category projective dimension of the module. See
[the degree-two rank-resolution witness](math/rank-resolution-degree-two.md)
for the maps, rank-exactness argument and claim boundaries. This concrete
two-coordinate equality case does not assert lower bounds in every dimension.
The same independently defined module is realized as the actual degree-one
simplicial homology of a four-vertex tetrahedron boundary filtration.
`RankResolutionDegreeTwoSimplicial.finiteIso` proves the grid-restricted natural
isomorphism, while `realIso` globalizes it to every real coordinate grade through
the canonical finite-simplicial Kan comparison. The actual homology's original
finite-presentation predicate is `homology_finitelyPresented`; the separate
`RankResolutionDegreeTwoSimplicialExamples` module proves actual nonzero arm maps,
cap deaths, and between-grid and below-grid behavior. See the [simplicial
realization note](math/rank-resolution-simplicial-realization.md) for the face
grades and signed-chain quotient proof.
Uniformly translating every face grade by a signed real parameter gives the
actual module `RankResolutionDegreeTwoSimplicial.translatedHomology`. Its exact
coordinate interleaving distance is `ENNReal.ofReal (min |t-s| (1/2))`; the
actual magnitude and half-radius witnesses and the subcritical obstruction are
documented in the [translation-distance note](math/rank-resolution-simplicial-translation.md).
Independent signed delays on the two actual face-grade coordinates have exact
distance `ENNReal.ofReal (min (max |v 0-u 0| |v 1-u 1|) (1/2))`; the actual
reindexing, witnesses, coordinate obstruction, and ordinary-import consumers
are documented in the [coordinate translation note](math/rank-resolution-simplicial-coordinate-translation.md).
Here the translated object is the full PH₁ persistence module: its fibers are
degree-one homology groups of the sublevel complexes, and its structure maps
are induced by their inclusions. The distance compares these modules with
their maps, not isolated homology groups.
Strictly positive independent coordinate scaling of the same actual PH₁ module
has an exact distance-to-zero formula from its two arm lifetimes; its reindexing,
actual transition maps and ordinary-import consumers are in the
[simplicial scaling note](math/rank-resolution-simplicial-scaling.md).
After fixing such a positive scale, adding a uniform signed delay to every
actual face grade gives a translated full PH₁ persistence module: its fibers
are the H₁ groups of the sublevel complexes and its maps are induced by their
inclusions. `scaledTranslatedHomology` defines this family, whose modules are
compared together with their maps. Its exact pairwise distance, actual
witnesses, and signed-delay consumers are documented in the
[scaled translation note](math/rank-resolution-simplicial-scaled-translation.md).
The finite-hypothesis signed hook stability result is proved in
[signed hook bottleneck stability](#signed-hook-bottleneck-stability). The
ordinary one-dimensional barcode connection and its half-open boundary
conventions are proved in [One-dimensional signed hooks and ordinary
barcodes](#one-dimensional-signed-hooks-and-ordinary-barcodes). The concrete
two-coordinate signed triangle failure is proved below. Finite-presentation
closure for categorical colimits, exact extensions and pullbacks, and composite
kernels is described in the corresponding sections below.

For any field and any partially ordered index type in universe zero, two
`MinimalFiniteRankProjectiveResolution`s of the same module have isomorphic
terms in each degree after padding the shorter resolution by zero:
`MinimalFiniteRankProjectiveResolution.termAt_nonempty_iso` returns the
comparison as a `Nonempty` isomorphism, and `termAt_rank_eq` shows that every
structure-map rank in corresponding terms is independent of the chosen
resolution. The theorem uses only the cover certificates carried by the two
inputs; it neither assumes equal raw lengths nor chooses a canonical
comparison isomorphism. The simp lemma
`MinimalFiniteRankProjectiveResolution.termAt_eq_resolution_termAt` is available from
`TDA.Persistence.FiniteRankProjectiveResolutionUniqueness`. The example
`FiniteRankProjectiveResolutionUniquenessExamples.principalHook_positive_terms_are_zero`
uses a one-term resolution of a principal-upset projective to show that every
positive-degree term in any minimal resolution of that module is zero.

`IsRankDeflation` means that a natural map is the quotient of an actual
rank-exact sequence. Its `rankExact_kernel` law supplies the categorical
kernel sequence; `IsRankDeflation.id` proves identity closure for pfd modules,
and `IsRankDeflation.comp` proves composition closure from two actual deflation
certificates without an extra pfd premise. `IsRankDeflation.pullback_snd`
proves closure under the actual categorical pullback along a map whose source
`T` is pfd. `PullbackFiber.mk` constructs compatible pairs; its projection laws
and `element_ext` characterize them by their two components. These
pullback-fiber constructions remain available over rings and preorders with
their broader universe-polymorphic scope.
In the field case, the pullback fibers are pfd when both source fibers are pfd.
Same-death lifts derive rank additivity without an exact-category assumption.
A principal upset surjecting onto its finite-death truncation shows that an
ordinary pointwise epimorphism need not be rank admissible. The deflation-side
closure laws do not establish the full exact structure; inflation-side pushout
closure is proved separately below.
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
first row in the finite-resolution comparison below. The real-coordinate
minimal-resolution degree bound is proved separately; the finite signed-hook
matching and squared bound are documented in
[signed hook bottleneck stability](#signed-hook-bottleneck-stability).

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
barcode inequality. That finite signed-hook result is documented in
[signed hook bottleneck stability](#signed-hook-bottleneck-stability). The
real-coordinate minimal-resolution degree bound is documented above; it does
not bound raw stored resolution lengths.

For any field `k`, `n ≥ 1`, and originally finitely presented modules
`M,N : PModule k (Fin n → ℝ)`, `RankSchanuelUnshifted` removes the shifts for
any supplied certified minimal resolutions `R,S`. From an actual
`ε`-interleaving of `M,N`, it constructs an interleaving of the unshifted
alternating biproducts at radius `(2*n-1)*ε`; the existence specialization
obtains the resolutions from the finite presentations. For these same
fixed-resolution objects it proves

```text
coordinateInterleavingDistance (unshiftedSchanuelLeftBiproduct R.resolution S.resolution)
  (unshiftedSchanuelRightBiproduct R.resolution S.resolution)
  ≤ ((2*n-1 : ℕ) : ℝ≥0∞) * coordinateInterleavingDistance M N.
```

The distance bound assumes neither finite distance nor an attained infimum.
The asymmetric finite-family comparison maps, their two equations, and their
component computation laws are in `CoordinateInterleavingDelay`. The explicit
parity-sum definitions and construction appear in
[unshifted Schanuel interleavings](math/unshifted-schanuel-stability.md).
This is the module-interleaving step only; the actual finite signed matching
and `(2*n-1)^2` bound are proved in
[signed hook bottleneck stability](#signed-hook-bottleneck-stability).

### Signed hook bottleneck stability

Let `k` be a field, `n ≥ 1`, and let `M,N : PModule k (Fin n → ℝ)` satisfy
the original `GradedFree.FinitelyPresented.{u,0,0}` hypotheses. For any
supplied certified minimal finite-rank-projective resolutions `R,S`, write
`C = R.signedHookBarcode M` and `D = S.signedHookBarcode N`. Their positive
and negative multisets remain separate. Put
`L = max R.resolution.length S.resolution.length`; the actual unshifted
Schanuel biproducts collect `R` in even degrees and `S` in odd degrees on one
side, with the choices exchanged on the other. Their finite hook-sum
presentations are constructed from the actual term presentations. The
occurrence-indexed biproduct construction
`FiniteHookSumPresentation.biproduct` proves that their tag multisets are
`C.positive + D.negative` and `D.positive + C.negative`, with every repeated
tag counted.

For any dimension `n` and finite occurrence-indexed family
`tag : Fin m → RealHookTag (n := n)`, `hookTagMultiset` retains every index,
including repeated tags. `hookTagMultiset_eq_ofFn` identifies it with the
`List.ofFn` enumeration, and `hookTagMultiset_eq_map_univ` identifies it with
the multiset map of `tag` over the value of `Finset.univ`; this maps indices
without deduplication. `hookTagMultiset_count` counts indices with each tag.
These enumeration and count statements include `m = 0` and `n = 0`.

`HasMultisetMatching ρ A B` means that exact finite enumerations of `A` and
`B` carry an existing `HookMatching.IsMatching`: each paired occurrence has
an actual coordinate interleaving, and every deleted occurrence on either
side has an actual interleaving with zero. The extended bottleneck
dissimilarity `hookMultisetBottleneckDistance A B` is the ENNReal infimum of
finite radii admitting such a matching. The signed dissimilarity is the
cross-sign comparison
`dHook(C.positive + D.negative, D.positive + C.negative)`, where
`dHook(A,B) := hookMultisetBottleneckDistance (k := k) A B` and
`dSigned(C,D) := signedHookBottleneckDissimilarity (k := k) C D` are shorthand
for the existing declarations.

For every actual `ε`-interleaving of `M,N`,
`finitelyPresented_exists_signedHookMultisetMatching` constructs an actual
matching of these cross-sign multisets at radius `(2*n-1)^2 * ε`. For any
fixed supplied `R,S`,
`finitelyPresented_signedHookBottleneckDistance_le` bounds their signed
dissimilarity by `((2*n-1 : ℕ) : ℝ≥0∞)^2` times the extended interleaving
distance:

```text
dSigned(C, D) ≤ ((2*n-1 : ℕ) : ℝ≥0∞)^2 * coordinateInterleavingDistance M N.
```

It assumes neither finite distance nor attainment. The module-level
barcode choice `finitelyPresentedSignedHookBarcode` comes from proved minimal
resolution existence and agrees with every supplied resolution by the
existing choice-independence theorem, giving
`finitelyPresented_moduleSignedHookBottleneckDistance_le` under the original
finite-presentation hypotheses alone. The result formalizes the finite-hook
matching argument of [BOOS Theorem 6.1 and §§2.7–2.9, with the finite part of
Proposition 4.3](https://arxiv.org/html/2208.00300v3); it does not claim the
source's countable extension or a metric instance. The ordinary one-dimensional
barcode connection is a separate result documented below; a concrete
two-coordinate signed triangle failure is proved in the next section. Examples apply
the capstone in dimensions one and two (coefficients one and nine), at zero interleaving
parameter, and to nonzero finite-presentation inputs; finite-death,
principal-upset, empty, and repeated cross-sign tags are also exercised. In
dimension one the capstone also compares two distinct principal upsets, born at
`0` and at `1`, through an explicit radius-one interleaving, giving signed
distance at most one.

### Finite simplicial input and grade perturbations

For `C : Simplicial.FiniteComplex m`, `Filtration.FiniteGraded C n` assigns
coordinatewise monotone grades in `Fin n → ℝ` to its nonempty faces.
`finiteSimplicialHomology k g q` is the actual inclusion-induced homology
module of its sublevels, for any field `k : Type u` and degree `q : ℕ`.
`finiteSimplicialHomology_finitelyPresented` derives the original
`GradedFree.FinitelyPresented.{u,0,0}` property from the finite input, using
finite-dimensional grid fibres and a natural grid Kan comparison.

For grades `g,h` on the same complex, a uniform coordinate error bound
`δ : ℝ≥0` constructs `finiteSimplicialHomology_interleaving` and bounds the
coordinate interleaving distance by `δ`. `FiniteGraded.supGradeError` is the
finite maximum of the face-coordinate errors, with empty maximum zero.
The same bounds hold for rank erosion; see
[weak-pair rank erosion](#weak-pair-rank-erosion).
For `n ≥ 1`, `finiteSimplicialSignedHookBarcode` uses the derived finite
presentation, and `finiteSimplicial_signedHookBottleneckDissimilarity_le`
bounds the canonical signed dissimilarity by `(2*n-1)^2 * δ`. The caller
supplies grades and their error bound, without a presentation or interleaving.
Repeated grades, empty input and arbitrary homology degrees are included;
the input, presentation and interleaving APIs also allow `n = 0`.
See [finite graded simplicial stability](math/finite-simplicial-stability.md)
for the proof and conventions.

### Two-coordinate signed hook triangle failure

For any field `k`, `RankSignedNontriangle` defines the two-coordinate
staircase with positive birth tags at `pᵢ = (i, 3 − i)` for `0 ≤ i ≤ 3` and
negative tags at the adjacent joins `qⱼ = (j + 1, 3 − j)` for `0 ≤ j ≤ 2`.
Each displayed point denotes its principal infinite-death hook tag. Define
`L = ({p₀}, 0)`, `C = ({p₀,p₁,p₂,p₃}, {q₀,q₁,q₂})`, and
`R = ({p₃}, 0)` as signed hook barcodes, with the displayed multisets retaining
all occurrences. The existing signed cross-sign dissimilarity has
`dSigned(L,C) ≤ 1`, `dSigned(C,R) ≤ 1`, and
`dSigned(L,R) = 3`, so this is an actual failure of the triangle inequality
on `SignedHookBarcode 2`. The upper bounds come from occurrence matchings,
and the long-edge lower bound applies to every matching radius, including
attempted deletion.

The module also constructs the support module generated by the four `pᵢ` and
the principal modules at `p₀` and `p₃`. It proves their original finite-
presentation hypotheses and identifies their existing
`finitelyPresentedSignedHookBarcode` choices with `C`, `L`, and `R`; the strict
inequality therefore holds for actual module-level choices without caller-
supplied resolutions or matching certificates. This is the concrete signed
example of [BOOS v3, §2.9 and Remark 6.3](https://arxiv.org/html/2208.00300v3#S6.SS2),
using the staircase of [Oudot--Scoccola v4, Example 4.1](https://arxiv.org/html/2112.11901v4)
rescaled by three. It does not show a triangle failure for ordinary numerical
bottleneck distance or identify `dSigned` with that distance.

### One-dimensional signed hooks and ordinary barcodes

For a real-indexed module `M`, the original input hypothesis is
`GradedFree.FinitelyPresented.{u,0,0}
(CoordinateRealBridge.fromReal M)`. The declarations in
`RankSignedBarcodeOneDimensional` use the existing choice
`finitelyPresentedSignedHookBarcode`; they derive a finite constructibility
grid and finite-dimensional critical fibers internally. In dimension one,
positive-degree terms of every minimal resolution vanish, so the positive
signed multiset is the degree-zero hook presentation and the negative multiset
is empty. `oneDimensionalHookEndpoints` sends finite hooks to `[b,d)` and
principal hooks to `[b,∞)`, retaining negative births and each occurrence.
`finitelyPresentedOneDimensionalBarcodeDiagram` is the resulting ordinary
diagram, and `finitelyPresentedOneDimensionalBarcodeRealizationIso` realizes
the original module by it.

`finiteHook_intervalIso a b hab` deliberately keeps a strict endpoint premise
to follow the nonempty finite branch of `RealHookTag`;
`oneDimensionalHookEndpoints_positive` records that endpoint condition. The
support identification behind the isomorphism itself is valid without strict
endpoints. For raw endpoints on a positive affine restriction, the existing
`PositiveAffineLine.finiteHook_reindex_eq` identifies the actual reindexed hook
with its interval, `PositiveAffineLine.finiteHook_structureMap_val` describes
its actual map, and `PositiveAffineLine.finiteHook_reindex_isZero_iff` detects
collapse. Equal or reversed entrance times give a zero module, so they are not
nonempty finite barcode tags. See [positive affine slices](#positive-affine-slices)
for this separate reindexing interface.

For every pair of modules with those original finite presentations,
`finitelyPresentedOneDimensionalBarcode_bottleneck_eq_distance` proves that
the ordinary bottleneck distance of their diagrams equals their real
interleaving distance. The coordinate-distance version follows through
`CoordinateRealBridge.distance_eq`. The proof compares with the module diagram
on an internally derived critical grid and reuses the existing finite-
constructible isometry; it assumes no supplied grid, matching, finite-distance
condition, or infimum attainment. This result concerns the ordinary diagrams
of the module-level signed barcode choice. It does not identify `dHook` or
`dSigned` with ordinary bottleneck distance; the separate two-coordinate
example above proves that `dSigned` is not triangular in general, without
affecting the ordinary metric result. The examples cover negative births,
repeated finite bars, finite and essential bars together, the empty diagram, the exact
finite-death deletion boundary, and a nonzero interval with an actual original
finite presentation. They apply the isometry both to that interval against
itself and to two distinct essential intervals, born at `0` and `1`, whose
bottleneck distance is bounded by an explicit radius-one interleaving. The endpoint conventions follow
[Bauer--Lesnick, §§2.1--2.3](https://arxiv.org/abs/1311.3681). This library's
critical-grade argument derives finite constructibility from the actual
presentation using its critical coordinates, free cover, and
transition-isomorphism criterion. The one-dimensional collapse and
ordinary-barcode connection follow the [BOOS v3 introduction after Result D](https://arxiv.org/html/2208.00300v3#S1),
[§2.10's one-dimensional paragraph](https://arxiv.org/html/2208.00300v3#S2.SS10),
and the `n = 1` consequence of [Theorem 5.18](https://arxiv.org/html/2208.00300v3#S5.Thmtheorem18);
[Theorem 6.1](https://arxiv.org/html/2208.00300v3#S6.SS1) gives signed-stability
context.

### Signed-hook cancellation along affine slices

`AffineSliceSignedBarcode` recovers the ordinary barcode of an actual
positive affine restriction from the canonical signed hook barcode of an
originally finitely presented module. Its main theorem proves
`B(slice M).points + slice(odd hooks) = slice(even hooks)` over every field.
Collapsed hooks are omitted, repeated endpoints retain their multiplicities,
and principal deaths remain infinite. Domination is proved before the
equivalent multiset-subtraction formula.

`RealBarcodeRankUniqueness` compares finite positive endpoint multisets
through all their rank counts. Its theorem
`RealBarcode.multiset_eq_of_rankCounts_eq` is the real instance of
`multiset_eq_of_sliceCounts_eq` of `TDA.Persistence.DiagramRankUniqueness`,
which holds over any linear order (with `Diagram.eq_of_sliceCounts_eq`).
`RankExactBarcodeCancellation` telescopes actual rank-exact rows, and
`AffineSliceRank` converts the actual hook-sum presentations into these
counts. The capstone derives the needed resolution and ordinary barcode
realization from the original presentation. See
[affine slice cancellation](math/affine-slice-cancellation.md).

### Positive affine slices

For `n ≥ 1`, `PositiveAffineLine` parameterizes a line `L(t) = b + t*a`
with every slope positive. Its entrance time is the maximum of
`(p i - b i) / a i`, characterized by `entrance p ≤ t ↔ p ≤ L(t)`.
`FinitePresentationReindex` uses this adjunction to regrade the actual
generators and relations while preserving their cokernel.
`AffineSlicePresentation` derives the original finite-presentation predicate
for the actual real restriction and its one-coordinate identification,
over arbitrary coefficient rings.

`AffineSliceHooks` identifies finite hook restrictions with
`[entrance p, entrance q)` and principal restrictions with
`[entrance p, ∞)`. Equal endpoints give the zero module. Its endpoint
multiset removes these collapsed intervals and preserves all multiplicities,
including collisions between distinct hooks. See
[positive affine slices](math/positive-affine-slices.md) for the construction,
coefficient scope and endpoint conventions.

### Matching distance of ordinary affine slices

`AffineSliceInterleaving` sends an actual coordinate `ε`-interleaving to a
real `ε/minSlope`-interleaving along any positive affine line. Its components
include the actual structure-map padding needed for unequal slopes. The
extended-distance bound works over arbitrary rings, without finite-distance
or attainment assumptions.

Over an arbitrary field, `AffineSliceMatching` derives ordinary slice
barcodes from original finite presentations. It bounds their weighted
bottleneck distance by coordinate interleaving distance and defines
`sliceMatchingDistance` as the supremum over lines with maximum slope one
and offset sum zero. The normalized family contains the diagonal line.
The resulting extended pseudometric is invariant under natural isomorphism
and is bounded by coordinate interleaving distance. See
[affine slice matching distance](math/affine-slice-matching.md).

### Finite presentations of categorical colimits

`GradedFree.FinitelyPresented` remains the existence of a finite graded-free
generators/relations presentation. `Presentation.cokernelPresentation` adjoins
the lifted source generators to the target relation occurrences, and
`Presentation.biprodPresentation` takes disjoint unions of both original
occurrence families. Their comparison isomorphisms identify these constructed
presentations with the actual categorical cokernel and binary biproduct; cover,
quotient, and inclusion laws expose how the canonical maps act on the chosen
presentations. Consequently,
`finitelyPresented_cokernel` and `finitelyPresented_biprod` prove closure for
actual categorical objects over any ring and preorder in the compatible
presentation universes. Repeated grades remain distinct occurrences, and empty
families or redundant relations are allowed.

`pushoutCokernelComparison` identifies the actual pushout with the cokernel of
`biprod.lift f (-g)`, using Mathlib's cokernel characterization of a pushout in
an abelian category. `finitelyPresented_pushout` therefore proves finite
presentation of actual pushouts from finite presentation of the three input
objects, with no closure certificate supplied by the caller. For a
rank-exact sequence over a field indexed by a partial order `P : Type` in
universe zero, `IsRankExact.pushout_finitelyPresented`
reuses `IsRankExact.pushout` and derives pointwise finite-dimensionality of the
new left object from its finite presentation. Pullback and composite-kernel closure are
proved in the next two subsections (`IsRankExact.pullback_finitelyPresented`,
`IsRankExact.comp_finitelyPresented`). These closure laws are standalone results: the
signed-stability proof obtains its finite resolutions by finite-grid Kan reconstruction and
does not consume them.

`FinitePresentationColimitsExamples` checks a nonzero quotient and actual
pushout, an empty/zero boundary, repeated grades with a genuine relation, a
redundant relation, and the arbitrary-field rank-exact consumer. It also
applies the cokernel theorem to the nonzero relation map between free modules
born at grades `0` and `2` (distinct for `n > 0`).
The constructions and their scope are summarized in the
[finite-presentation closure digest](math/multiparameter-foundations.md#finite-presentation-closure).

### Finite presentations of exact extensions and pullbacks

The field-side closure results of this and the next subsection, and
`IsRankExact.pushout_finitelyPresented` above, are stated for `P : Type`, modules in
`PModule.{u,0,u}` and presentations with index carriers in `Type 0`
(`GradedFree.FinitelyPresented.{u,0,0}`); a `FinitelyPresented.{u,0,u}`
witness is lowered to `{u,0,0}` by
`GradedFree.finitelyPresented_lowerIndexUniverse`. Let `k` be a field,
`P : Type` a partially ordered type, and
`0 → L → M → N → 0` a pointwise short exact row of persistence modules. If
`L` and `N` are finitely presented, `IsPointwiseShortExact.finitelyPresented_middle`
proves that `M` is finitely presented. The row is assumed pointwise exact in
each fiber; the result does not require pointwise finite-dimensionality or rank
exactness of the original row.

The proof chooses a finite presentation of `N` and pulls the quotient map back
along its free cover. The resulting row onto the finite graded-free module
splits because the free generators lift through the original quotient. Its
middle object is therefore finitely presented by closure under biproducts.
The lifted relation map then has image equal to the kernel of the projection
to `M`, and that projection is an epimorphism. Exactness identifies `M` with
the actual categorical cokernel of the lifted relation map. The relation map
need not be injective.

Given `π : M ⟶ N` in a pointwise short exact row and a map `f : T ⟶ N`, write
`S := Limits.pullback π f` for the actual categorical pullback.
`IsPointwiseShortExact.pullbackInclusion` and its projection laws give the
canonical ordinary short exact row `0 → L → S → T → 0`.
`IsPointwiseShortExact.finitelyPresented_pullback` proves finite presentation
of `S` from finite presentation of `L` and `T`.
For a rank-exact deflation, `IsRankExact.pullback_finitelyPresented` also proves
that the actual kernel of the pullback projection is finitely presented and
that its canonical kernel row is rank exact. Its only presentation inputs are
`L` and `T`; pointwise finite-dimensionality of `T` is derived from its finite
presentation. Closure for kernels of composites of deflations is not part of
this result.

`FinitePresentationPullbackExamples` checks the ordinary extension and
rank-exact pullback on the repeated-grade presentation with a genuine relation,
over an arbitrary field and with the smallest presentation-index universe. It
also checks the empty-presentation zero case. On the non-split row given by
the genuine relation, with both outer terms nonzero, it applies the extension
theorem and the pullback of the quotient map along itself, which contains a
pair with distinct coordinates.
The split-pullback argument and its hypotheses are summarized in the
[finite-presentation closure digest](math/multiparameter-foundations.md#finite-presentation-closure).

### Finite presentations of composite kernels

Over a field and a partially ordered index type `P : Type` (universe scope as in the previous
subsection), for any composable maps
`π : M ⟶ N` and `σ : N ⟶ O`, `kernelCompIsoPullback` identifies the actual
categorical kernel of `π ≫ σ` with the actual pullback of `π` along
`kernel.ι σ`. Its first and second projection laws and its inverse inclusion
law expose the comparison without unfolding its construction. The comparison
itself needs no exactness, finite-presentation, or epimorphism hypotheses.

Now suppose the maps occur in rank-exact rows
`0 → L → M --π→ N → 0` and `0 → K → N --σ→ O → 0`. If the original left
terms `L` and `K` are finitely presented, `IsRankExact.comp_finitelyPresented`
proves finite presentation of the actual categorical kernel of the composite
and rank exactness of its canonical kernel row. The proof transfers `K` to the
actual kernel of `σ`, applies finite presentation of actual pullbacks, and
transports the result along `kernelCompIsoPullback`. The unchanged middle and
right objects retain their presentation witnesses for callers working in the
original finite-presentation subcategory; the theorem itself takes only the
two original left-term presentations. It does not require finite presentation
of the new composite kernel as an input. This result covers kernels of
composites of rank-exact deflations, not kernels of arbitrary maps. The actual
pullback closure is exposed separately by
`IsRankExact.pullback_finitelyPresented`.

`FinitePresentationCompositeKernelExamples` checks the result over an arbitrary
field using the repeated-grade presentation with a genuine relation, including
a nonzero fiber of the actual composite kernel, and the empty/zero case. A
second consumer composes two split deflations whose rows have nonzero outer
terms and exhibits a composite-kernel vector outside the kernel of the first
deflation.
The kernel comparison and its finite-presentation scope are summarized in the
[finite-presentation closure digest](math/multiparameter-foundations.md#finite-presentation-closure).

### Pushouts of rank-exact sequences

Let `0 → L --ι→ M --π→ N → 0` be rank exact over a field, with partial order
`P : Type` in universe zero, and let `f : L ⟶ L'` have pointwise
finite-dimensional fibers in the new left term `L'`. This pushout result has no
finiteness assumption on `P`. `IsPointwiseShortExact.pushoutQuotient` defines the quotient map
from the actual categorical pushout by applying `π` on `M` and zero on `L'`.
`IsPointwiseShortExact.pushout_pointwise` proves that this quotient and the
canonical map from `L'` form a pointwise short exact row. `IsRankExact.pushout`
also proves that the pushout fibers are finite dimensional and that the new
row is rank exact. Each middle fiber is finite dimensional because the actual
`ModuleCat` pushout is a quotient of `M(p) ⊕ L'(p)`.

For rank additivity, the proof lifts a quotient vector killed by a structure
map through the original rank-exact row with a lift killed at the same grade,
then maps that lift into the pushout. `RankExactPushoutExamples` checks the
theorem on a nonzero pushout of a split sequence with zero left term. It also
pushes the nonzero left term of a split row out along a nonzero truncation map,
and exhibits a pushout vector that dies at a later grade while its quotient
image is nonzero. This closure result supplies
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

For a ring and `n : ℕ`, `CoordinateShift.shift` evaluates a module on `Fin n → ℝ` at `a + ε·1` for a
finite nonnegative parameter. A `CoordinateInterleaving ε M N` consists of natural maps `M → N[ε]`
and `N → M[ε]` whose two composites are the structure maps to `M[2ε]` and `N[2ε]`, and
`CoordinateInterleaving.zeroEquivIso` identifies zero interleavings with natural isomorphisms.
`coordinateInterleavingDistance` is the extended infimum of the admissible finite parameters; an
empty parameter set has distance infinity. `coordinateInterleavingDistance_eq_zero_of_iso` shows
that naturally isomorphic modules have distance zero, while
`coordinateInterleavingDistance_congr` gives invariance under natural isomorphisms in both
arguments. `coordinateInterleavingDistance_comm` gives symmetry, and
`coordinateInterleavingDistance_triangle` gives the extended triangle inequality. For a finitely presented
source, `GradedFree.finitelyPresented_exists_finite_postcomp_tests` gives a finite set of generator
and relation grades at which bijectivity of a natural map induces a bijection on maps out of the
module, and `GradedFree.finitelyPresented_exists_pos_postcomp_shiftLE_bijective` combines this test
set with a finitely presented target's finite critical coordinates so that `Hom(M,N[ε]) → Hom(M,N[ε+δ])` is bijective
for all sufficiently small `δ ≥ 0`. `CoordinateInterleaving.of_postcomp_lifting` is the algebraic
lowering step, taking the two surjections and the two injections as hypotheses; the
finite-presentation proof establishes all four. `FinitePresentationClosure` also proves
`finitelyPresented_interleaving_at_distance`, `finitelyPresented_distance_eq_zero_iff_iso`,
`finitelyPresented_interleaving_parameters_eq_Ici` and
`finitelyPresented_isClosed_interleaving_parameters`, and `FinitePresentationIsoClasses.edist_classOf`
identifies the descended distance on representatives. These statements include the zero ring, empty
presentations and `n = 0`.

`CoordinateRealBridge.interleavingEquiv` identifies the real-indexed and one-coordinate interleaving
witness types, and `CoordinateRealBridge.distance_eq` identifies their distances. Some hypothesis is
needed for attainment and separation: over a field, `RealRay.distance_eq_zero` shows that
`k_[0,∞)` and `k_(0,∞)` have interleaving distance zero, `RealRay.not_nonempty_iso` that they are not
naturally isomorphic, and `RealRay.not_nonempty_zero_interleaving` that the zero distance is not
attained. (Informally, the closed ray is finitely presented and the open ray is not; this
ray-presentability remark is not formalized.) For
right-continuous real modules on finite critical grids with zero left tails and finite-dimensional
critical fibers, over a field, `FiniteConstructible.distance_le_iff_interleaving`,
`FiniteConstructible.interleaving_at_distance`, `FiniteConstructible.isClosed_interleaving_parameters`
and `FiniteConstructible.distance_eq_zero_iff_iso` give the one-dimensional attainment, closedness
and separation from the barcode isometry and an optimal finite matching; they do not prove the
multidimensional finite-presentation theorem. See
[finite-constructible closure](math/constructible-isometry.md#attainment-and-separation) and
[why the finite-presentation hypothesis matters](math/multiparameter-closure.md).

### Weak-pair rank erosion

For a task-oriented route through these results see
[choosing a result](math/rank-erosion.md#choosing-a-result).

For field-valued modules on `Fin n → ℝ` with pointwise finite-dimensional fibers,
`RankErosion ε M N` compares the ranks of `M(a−ε → b+ε)` with `N(a → b)` and
vice versa for every weak pair `a ≤ b`. Diagonal ranks are included, also for
`n = 0`. `rankErosionDistance` is the extended infimum of admissible finite radii;
it has zero self-distance, symmetry and the extended triangle inequality, none
of which needs a finiteness hypothesis.
`CoordinateInterleaving.rankErosion` derives the inequalities from actual
interleaving maps, and `rankErosionDistance_le_coordinateInterleavingDistance`
proves `dE ≤ dI` without an attainment assumption.

`no_coordinateInterleaving_of_rank_violation` turns one failed rank comparison
into an obstruction at that radius.
`radius_le_coordinateInterleavingDistance_of_rank_violation` gives a non-strict
lower bound; `radius_lt_coordinateInterleavingDistance_of_rank_violation` makes
it strict for original finitely presented modules, using interleaving attainment.
`rankErosion_zero_iff` concerns erosion at radius zero, not the equation that its
infimum is zero, and makes no module-isomorphism claim. The current rank uses
`Module.finrank`; its intended scope is finite-dimensional fibers, not arbitrary
infinite-dimensional modules. `eRankOfStructureMap` (`TDA.Persistence.StructureMapERank`)
is the `ℕ∞`-valued image rank, `⊤` on an infinite-dimensional image; its composition
and four-point laws (`eRankOfStructureMap_trans_le_left`, `_trans_le_right`,
`_four_point`) need no finiteness, `rankOfStructureMap_eq_toNat_eRankOfStructureMap`
relates the two ranks for every module, and
`eRankOfStructureMap_eq_rankOfStructureMap_of_finiteDimensional` and
`eRankOfStructureMap_eq_rankOfStructureMap_of_finiteDimensional_source` identify
them on finite-dimensional images and source fibers. `ERankErosion` and
`eRankErosionDistance` (`TDA.Persistence.ERankErosion`) are erosion and its
distance on the extended rank; their laws and
`eRankErosionDistance_le_coordinateInterleavingDistance` need no finiteness, and
`eRankErosion_iff_rankErosion` and `eRankErosionDistance_eq_rankErosionDistance`
identify them with `RankErosion` and `rankErosionDistance` on pointwise
finite-dimensional modules. For one parameter only (`TDA.Persistence.ERankQTame`),
`PModule.qTame_iff_eRankOfStructureMap_fromReal_ne_top` characterizes q-tame real
modules by finite extended ranks on strict pairs, `RealInterleaving.eRankOfStructureMap_ne_top`
is the local finite-image bound through a finite-dimensional middle fibre, and
`RealInterleaving.eRankErosion` and
`eRankErosionDistance_fromReal_le_realInterleavingDistance` transport the
interleaving bound across `CoordinateRealBridge.fromReal`.
For several parameters (`TDA.Persistence.CoordinateQTame`), `PModule.CoordQTame`
is q-tameness with strictness in every coordinate (`∀ i, a i < b i`, not the
product-strict `a < b`), equivalent to finite extended rank of every positive
diagonal shift (`PModule.coordQTame_iff_eRankOfStructureMap_translation_ne_top`)
and to `PModule.QTame` for one coordinate (`PModule.qTame_iff_coordQTame_fromReal`);
`CoordinateInterleaving.eRankOfStructureMap_ne_top` is the local finite-image bound,
and `CoordinateInterleaving.eRankOfStructureMap_ne_top_of_coordQTame` gives finite
extended rank across gaps above `2ε` when the other module is coordinatewise q-tame.
Erosion test domains are unchanged.
For finite graded simplicial homology (`TDA.Persistence.FiniteSimplicialErosion`),
`finiteSimplicialHomology_rankErosion`,
`rankErosionDistance_finiteSimplicialHomology_le_supGradeError` and
`eRankErosionDistance_finiteSimplicialHomology_le_supGradeError` bound erosion by
the grade error, and `finiteSimplicialHomology_rankErosion_failure_certificate`
turns a failed test into `ε < dE ≤ dI ≤ supGradeError`.
For the uniform translates of the tetrahedron-boundary witness
(`TDA.Persistence.FiniteSimplicialErosionTranslation`),
`RankResolutionDegreeTwoSimplicial.translatedHomology_not_rankErosion` exhibits
failed tests below `min |t-s| (1/2)` from actual structure maps, and
`RankResolutionDegreeTwoSimplicial.rankErosionDistance_translatedHomology` and
`RankResolutionDegreeTwoSimplicial.eRankErosionDistance_translatedHomology` give both
erosion distances exactly `ENNReal.ofReal (min |t-s| (1/2))`, equal to the interleaving
distance.
For independent signed coordinate translates
(`TDA.Persistence.FiniteSimplicialErosionCoordinateTranslation`),
`RankResolutionDegreeTwoSimplicial.coordinateTranslatedHomology_not_rankErosion` exhibits
failed tests below `min (max |v 0 - u 0| |v 1 - u 1|) (1 / 2)`, and
`RankResolutionDegreeTwoSimplicial.rankErosionDistance_coordinateTranslatedHomology` and
`RankResolutionDegreeTwoSimplicial.eRankErosionDistance_coordinateTranslatedHomology` give
both erosion distances exactly that value, equal to the interleaving distance.
For signed delays of one positive scaling
(`TDA.Persistence.FiniteSimplicialErosionScaledTranslation`),
`RankResolutionDegreeTwoSimplicial.scaledTranslatedHomology_not_rankErosion` exhibits
failed tests below `min |t - u| (scaledLifetime s / 2)` at the longer arm, and
`RankResolutionDegreeTwoSimplicial.rankErosionDistance_scaledTranslatedHomology` and
`RankResolutionDegreeTwoSimplicial.eRankErosionDistance_scaledTranslatedHomology` give
both erosion distances exactly that value, equal to the interleaving distance.
For one positive scaling against the zero module
(`TDA.Persistence.FiniteSimplicialErosionScaling`),
`RankResolutionDegreeTwoSimplicial.scaledHomology_not_rankErosion_zero` exhibits failed
tests below `scaledLifetime s / 2` at the longer arm, and
`RankResolutionDegreeTwoSimplicial.rankErosionDistance_scaledHomology_zero` and
`RankResolutionDegreeTwoSimplicial.eRankErosionDistance_scaledHomology_zero` give both
erosion distances to zero exactly that value, equal to the interleaving distance.
For two uniform scalings of the tetrahedron-boundary witness
(`TDA.Persistence.FiniteSimplicialErosionTwoScales`), with `0 < c` and `0 < c'` over any
field, `RankResolutionDegreeTwoSimplicial.scaledHomology_const_not_rankErosion` and
`RankResolutionDegreeTwoSimplicial.scaledHomology_const_not_eRankErosion` exhibit failed tests
below `min (2 * |c - c'|) (max c c' / 2)` (the witness
`RankResolutionDegreeTwoSimplicial.scaledHomology_const_not_rankErosion_of_lt` takes the
separate strict hypotheses `ε < 2 * (c' - c)` and `2 * ε < c'`), and
`RankResolutionDegreeTwoSimplicial.rankErosionDistance_scaledHomology_const` and
`RankResolutionDegreeTwoSimplicial.eRankErosionDistance_scaledHomology_const` give both erosion
distances exactly `ENNReal.ofReal (min (2 * |c - c'|) (max c c' / 2))`. The first term comes
from the grade error (`RankResolutionDegreeTwoSimplicial.supGradeError_scaledGrading_const`
equals `Real.toNNReal (2 * |c - c'|)`); the second from the lifetime cap
`RankResolutionDegreeTwoSimplicial.scaledHomology_rankErosion_of_scaledLifetime_le` (with its
`eRankErosion` version), which holds for anisotropic scales although no distance formula is
claimed for them. For `c < c'`, the cap term is the smaller one exactly beyond the critical ratio `c'/c = 4/3`.
`RankResolutionDegreeTwoSimplicial.boundaryTetrahedronGrading_grade_mem_Icc` places every literal
face grade in `[0, 2]`, `RankResolutionDegreeTwoSimplicial.scaledGrading_grade_error` and
`RankResolutionDegreeTwoSimplicial.scaledGrading_const_grade_error` bound the grade error, and
`RankResolutionDegreeTwoSimplicial.scaledLifetime_const` gives the lifetime `c` of the uniform
scaling; `RankResolutionDegreeTwoSimplicial.scaledHomology_eRankErosion_of_scaledLifetime_le`
is the extended-rank cap.
`FiniteSimplicialErosionExamples.scaledHomology_const_not_rankErosion_threeQuarters` and
`FiniteSimplicialErosionExamples.scaledHomology_const_rankErosion_failure_certificate_threeQuarters`
record the failing radius `3/4` between the scales `1` and `2` with its failure certificate.
No equality with the interleaving distance is claimed.
Erosion attainment is supplied for finitely presented modules only (below); a
certified finite test exists for F₂ grid representations only
(`F2GridRep.runErosion`, below).

`StrictRankErosion ε M N` requires the same two inequalities only at the strict
pairs of the product order, `a ≤ b` and `a ≠ b` (`strictRankErosion_iff_lt`
restates this with `a < b`), and `strictRankErosionDistance` is its extended
infimum. `RankErosion.strict` gives the strict predicate from the weak one at
the same radius, for every `n`. For `[NeZero n]` and finite-dimensional fibers,
`StrictRankErosion.rankErosion_add` and `StrictRankErosion.rankErosion_of_lt`
give the weak predicate at every larger radius, and
`strictRankErosionDistance_eq_rankErosionDistance` equates the two distances.
The strict predicate has `symm`, `mono` (finite-dimensional fibers) and `trans`,
its distance has zero self-distance, symmetry and the extended triangle
inequality, and `strictRankErosion_zero_iff` describes radius zero. With no
coordinates there is no strict pair: `strictRankErosion_fin_zero` and
`strictRankErosionDistance_fin_zero` state that the strict predicate holds for
all modules and the strict distance is zero. For finite-dimensional fibers,
`le_rankErosionDistance_of_not_rankErosion` and
`le_strictRankErosionDistance_of_not_strictRankErosion` turn a radius at which
a predicate fails into a non-strict lower bound of its distance. The two
predicates are not equivalent at a fixed radius: the examples give a module
supported on a closed box for which the strict predicate holds and the weak one
fails at the same radius, while both distances equal that radius. For finitely
presented modules with at least one coordinate the two predicates are
equivalent at every fixed radius, as stated below. No coordinatewise-strict
predicate is supplied.

For modules `M`, `N` with original finite presentations
(`GradedFree.FinitelyPresented.{u,0,0}`), the infimum is attained.
`GradedFree.finitelyPresented_exists_pos_rankOfStructureMap_erosionUpper`
derives from the presentation that, at every weak pair, raising the target or
both grades by a small radius keeps the rank
(`erosionUpper_le_erosionUpper` supplies the comparison of the raised grades);
`GradedFree.finitelyPresented_exists_pos_not_rankErosion_add` shows that a
radius at which erosion fails is followed by an interval of such radii; and
`GradedFree.finitelyPresented_lt_rankErosionDistance_of_not_rankErosion` makes
a failed predicate a strict lower bound of the distance.
`GradedFree.finitelyPresented_rankErosionDistance_le_iff_rankErosion` states
`rankErosionDistance M N ≤ ε ↔ RankErosion ε M N`,
`GradedFree.finitelyPresented_rankErosion_at_distance` the admissibility of a
finite distance, `GradedFree.finitelyPresented_rankErosion_parameters_eq_Ici`
and `GradedFree.finitelyPresented_isClosed_rankErosion_parameters` the shape
of the admissible set, and
`GradedFree.finitelyPresented_rankErosionDistance_eq_zero_iff` identifies
distance zero with equality of all weak-pair ranks; it makes no
module-isomorphism claim. `GradedFree.finitelyPresented_zero` (the zero module
on a preordered index type) and `F2GridRep.finitelyPresented_lan_toModule` (the
Kan extension of a valid representation) supply the hypothesis for comparisons
with zero and for executed tests. Attainment fails for modules that have only
finite-dimensional fibers: with at least one coordinate, the module of the
closed box `[0, 2c]ⁿ` over `ℚ` has erosion distance `c` from zero
(`StrictRankErosionExamples.closedBox_rankErosionDistance`) while erosion fails
at radius `c` (`StrictRankErosionExamples.closedBox_not_rankErosion`). It is
therefore not finitely presented
(`RankErosionAttainmentExamples.closedBox_not_finitelyPresented`).

For finitely presented modules with at least one coordinate the two predicates
agree at every fixed radius:
`GradedFree.finitelyPresented_strictRankErosion_iff_rankErosion` (with
`[NeZero n]`). For every `n`,
`GradedFree.finitelyPresented_strictRankErosionDistance_le_iff_strictRankErosion`
states `strictRankErosionDistance M N ≤ ε ↔ StrictRankErosion ε M N` and
`GradedFree.finitelyPresented_lt_strictRankErosionDistance_of_not_strictRankErosion`
its strict lower bound. A failed predicate gives the certificate
`ε < rankErosionDistance M N ∧ rankErosionDistance M N ≤
coordinateInterleavingDistance M N`
(`GradedFree.finitelyPresented_rankErosion_failure_certificate`), hence
`ε < coordinateInterleavingDistance M N`
(`GradedFree.finitelyPresented_lt_coordinateInterleavingDistance_of_not_rankErosion`).
These take presentations in `GradedFree.FinitelyPresented.{u,0,0}` and no
finite-dimensionality instance.
`radius_lt_coordinateInterleavingDistance_of_rank_violation` reaches the last
bound from one violated inequality, for presentations in
`FinitelyPresented.{u,0,u}`, through interleaving attainment; the two universe
choices are exchanged by `GradedFree.finitelyPresented_liftIndexUniverse` and
`GradedFree.finitelyPresented_lowerIndexUniverse`. The examples show that the
equivalence fails with no coordinates and for the closed box, that with at
least one coordinate the closed box and zero are interleaved at every radius
above their interleaving distance and not at that distance, and that two
finitely presented two-parameter modules can have equal rank invariants,
erosion distance zero and nonzero interleaving distance.

For modules on two finite coordinate grids `G`, `H` and their actual Kan
extensions, the predicate is determined by finitely many grades.
`CoordinateGrid.rankOfStructureMap_lan` and `rankOfStructureMap_lan_eq_zero`
(combined in `rankOfStructureMap_lan_eq_dite`) read a rank of `G.lan.obj M` as
the rank of `M` between the two floors, or as zero where the source grade has
no lower grid point; no finite-dimensionality is assumed (ranks are
`Module.finrank` values, as elsewhere in this section).
`CoordinateGrid.erosionBreakpoints G H ε` collects, per coordinate, the values
of both grids and their shifts by `±ε`. For every finite grid `T` containing
these breakpoints, `CoordinateGrid.rankErosion_lan_iff_of_subset` proves that
`RankErosion ε (G.lan.obj M) (H.lan.obj N)` is equivalent to its two
inequalities at the comparable pairs `p ≤ q` of points of `T`, diagonal pairs
included; `rankErosion_lan_iff` is the case `T = erosionBreakpoints G H ε`.
The original grid values alone are not enough, as the examples show. The test
grades are real numbers and the statement is not an algorithm: nothing here is
executable.

Grid modules over F₂ can be given by executable data. A `RatGrid n` lists
finitely many rational values per coordinate, used as a finite set; its real
image `RatGrid.grid` is a `CoordinateGrid`, `RatGrid.ratPoint` and
`RatGrid.pointOfRat` identify its points with the rational grid grades
(`RatGrid.points`), and the executable `RatGrid.floor` of a rational grade is
the rational grade of the real floor (`RatGrid.ratPoint_floor`). An
`F2GridRep n` adds a fiber dimension for each rational grade and an F₂ matrix
for each pair of rational grades; only their values at grid grades and at
comparable pairs of them are read. `F2GridRep.Valid` is the decidable
statement that the matrices are identities on the diagonal and compose along
comparable triples of grid grades, and `F2GridRep.toModule` is the actual
module on the grid for a valid representation, with fibers
`Fin (dim a) → ZMod 2` and structure maps the stored matrices
(`F2GridRep.structureMapLinear_toModule`). `F2GridRep.rankAt x y` computes,
with `F2Matrix.rank`, the rank of the stored matrix between the floors of two
rational grades, or zero when `x` has no lower grid value;
`F2GridRep.rankAt_eq` proves that it is the rank of the actual Kan extension
of the grid module between the real grades of `x ≤ y`, and
`F2GridRep.rankAt_eq_of_eq` states the same at real grades given by equations.
Nothing is claimed for an invalid representation. Validation enumerates the
comparable triples of grid grades and each rank enumerates source vectors, so
the cost is exponential in the fiber dimension and in the number of
coordinates.

`F2GridRep.runErosion R S e` is a certified finite test of `RankErosion` for
two representations and a rational radius. It returns `invalid` when a
representation is not valid or `e < 0`; `pass` when both inequalities hold at
every comparable pair of grades of the rational breakpoint grid
(`RatGrid.erosionBreakpoints`); and otherwise `fail w`, where
`w : F2GridRep.ErosionFailure` records the direction of a violated inequality,
the pair of rational grades and the two ranks. `runErosion_eq_invalid_iff`,
`runErosion_eq_pass_iff` and `runErosion_eq_fail` characterise the outcomes for
the actual Kan extensions `R.grid.lan.obj (R.toModule hR)` and
`S.grid.lan.obj (S.toModule hS)` at the real radius `RatGrid.radius e he`:
`pass` holds exactly when the input is valid and `RankErosion` holds, and a
reported failure is a violation by those extensions with `RankErosion` false.
`erosionFailure?_eq_none_iff` is the underlying equivalence for valid input.
Which violation is reported depends on the enumeration order.

The Kan extensions of valid representations are finitely presented
(`F2GridRep.finitelyPresented_lan_toModule`), so an executed result decides
more than the predicate. For valid input and `0 ≤ e`,
`F2GridRep.runErosion_eq_pass_iff_rankErosionDistance_le` states that the test
passes exactly when the erosion distance of the two Kan extensions is at most
`e`, and `F2GridRep.runErosion_eq_pass_iff_strictRankErosion` (with
`[NeZero n]`) that it passes exactly when `StrictRankErosion` holds at `e`.
Three statements take only the executed equation and include validity in
their conclusion. `F2GridRep.runErosion_eq_pass_certificate`: after `pass`,
`RankErosion` and `StrictRankErosion` hold at `e` and both
`rankErosionDistance` and `strictRankErosionDistance` are at most `e`. The
interleaving distance need not be at most `e`: the test
`RankErosionCertificateExamples.arms_zero` passes at radius `0`, and
`RankErosionCertificateExamples.arms_nonseparation` gives the same two modules a
nonzero interleaving distance.
`F2GridRep.runErosion_eq_fail_certificate`: after `fail w`, `RankErosion`
fails at `e`, `e` is strictly below the erosion distance, and the erosion
distance is at most the interleaving distance, so `e` is strictly below the
interleaving distance. `F2GridRep.runErosion_eq_fail_strict_certificate`
(with `[NeZero n]`): after `fail w`, `StrictRankErosion` fails at `e` and `e`
is strictly below the strict distance; with no coordinates a failure says
nothing about the strict predicate. The test is restricted to F₂, minimises no
radius, and its cost grows exponentially with the number of coordinates and the
fiber dimensions.
`RatGradedInput.toF2GridRep` generates such a representation from a validated
rationally graded finite simplicial complex (`RatGradedInput.Valid`), using the
computed slice bases of `RatGradedInput.slice` and computed inclusion matrices,
and `RatGradedInput.toF2GridRep_valid` proves it valid (for an invalid input
the generated representation carries no meaning).
`RatGradedInput.toF2GridRep_lanIso` proves its Kan extension canonically
isomorphic, as a persistence module, to the actual homology
`RatGradedInput.homology`. `RatGradedInput.runErosion xs ys p e` validates
two inputs and the radius, reporting `invalidFirst`, `invalidSecond` or
`negativeRadius` separately (`RatGradedInput.runErosion_eq_invalid_iff`,
`RatGradedInput.runErosion_eq_negativeRadius_iff`). Otherwise it runs the test
on the two generated representations in degree `p`, and certifies the actual
homologies. `RatGradedInput.runErosion_eq_pass_iff`: `pass` exactly when both
inputs are valid, `0 ≤ e` and `RankErosion` holds between the actual modules.
`RatGradedInput.runErosion_eq_fail`: `fail w` records a direction, a
comparable pair of breakpoint grades and ranks equal to those of the actual
structure maps. `RatGradedInput.runErosion_eq_pass_certificate` and
`RatGradedInput.runErosion_eq_fail_certificate` give the distance consequences.
No runtime bound is claimed.

The public `TDA.Persistence` aggregator exports `RankErosion`,
`RankErosionInterleaving`, `RankErosionWitness`, `RankErosionGrid`, `F2GridRep`,
`F2GridErosion`, `StrictRankErosion`, `RankErosionAttainment`, `RankErosionCertificate`,
`F2GridHomologyInput`, `F2GridHomologyIso` and `F2GridHomologyErosion`; the
witness module includes
nonzero principal-upset
examples, diagonal and positive-radius off-diagonal tests. See
[rank erosion and its extension boundaries](math/rank-erosion.md).

## Persistent homology results and computational boundary

Finite discrete interval constructors and `barcodeModuleOfList` have executable
data paths using natural endpoint decisions. `barcodeEnumerationNatIso` executes
the existing nth-occurrence correspondence, preserving distinct coordinates for
repeated intervals. Public value laws expose forward/inverse coefficients; ℚ and
F₂ consumers check endpoints, empty modules and naturality. Proof-side classical
dependencies and arbitrary-multiset/decomposition boundaries are separate; see
[executing finite interval and list-barcode modules](math/constructive-finite-intervals.md).

The finite decomposition API takes `M : PModule.{u,0,u} k (Fin N)` with
`k : Type u`, `[Field k]`, and `[∀ i : Fin N, FiniteDimensional k (M.obj i)]`. The index
universe is `0`, and the field and module-carrier universes are both `u`; this
does not extend the decomposition theorem to independent carrier universes.
`exists_barcode_decomposition` and `nonempty_rankBarcodeIso` construct genuine natural
interval semantics. `nonempty_iso_iff_structureMapRank_eq` classifies these modules by
the ranks of all structure maps, including composites. The canonical object is
the interval multiset; the chosen summands and isomorphism are not canonical. See
[finite interval decomposition](math/finite-interval-decomposition.md).

For clients (#1252): `RealBarcode.realization_unique` is the real-line counterpart of
`barcode_decomposition_unique`: two positive diagrams whose realizations are isomorphic to
one module are equal, and `RealBarcode.diagram_eq_of_realize_iso` is the case of two
realizations. Positivity excludes endpoint pairs with empty support.
`barcode_decomposition_unique` asks for finite-dimensional fibers of the decomposed module.
`RealIntervalDecomposition.exists_interval_decomposition` gives existence for pointwise
finite-dimensional real modules, and `scalar_crossing_card_eq_of_iso_of_le` proves that
their crossing multiplicities are isomorphism invariants. `BarcodeUniquenessClientExamples`
is a downstream regression fixture. It replays
existence and uniqueness of the barcode on a finite chain, the classification by ranks,
uniqueness of a positive real realization, equality of the diagrams of filters with
isomorphic sublevel modules, and the real interval decomposition.

`FiniteLine.moduleOfAdjacent` constructs finite persistence from adjacent linear
maps, and its path-category equivalence identifies equioriented finite-line
representations with `PModule`. `MatrixSequence.toPModule` accepts rectangular
transition matrices with target rows and source columns; its morphisms extend
adjacent commuting squares to all structure maps. Supplied bases give genuine
natural coordinate isomorphisms, basis-independent barcodes, and the existing
finite decomposition. Mutually inverse matrix morphisms give a natural isomorphism
(`MatrixSequence.Hom.isoOfInverse`) and equal barcodes
(`MatrixSequence.barcode_eq_of_inverse_homs`); `MatrixSequenceClientExamples` is a
downstream regression fixture (#1263). A zero-initial padded sequence can also be extended
across an explicit real critical grid, retaining its original endpoint values and a
constant final cell. The finite-line path and explicit matrix composite data
execute over concrete coefficient operations, including ℚ and F₂; see
[chronological finite computation](math/finite-line-computation.md) for the
composition order, empty cases and proof boundaries. Supplied-basis, real-grid
and decomposition contracts are described in
[finite representations](math/finite-representations.md); no executable barcode
extraction is asserted.

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

`TDA.Persistence.RealInterleavingRankObstruction` exposes the generic rank and zero-fibre
obstructions in `TDA.Persistence.RealInterleaving`. Over a field, an `ε`-interleaving bounds
the rank of `M(t → t + 2ε)` by `dim N(t + ε)` when this single middle fibre is finite-dimensional,
as stated by `finrank_range_structureMapLinear_le_of_realInterleaving` and its primed form. A
zero middle fibre forces the structure map to vanish by
`structureMap_eq_zero_of_realInterleaving`.
`isEmpty_realInterleaving_of_finrank_lt` and
`isEmpty_realInterleaving_of_structureMap_ne_zero` exclude a witness when the rank exceeds that
dimension or a nonzero map factors through zero. The corresponding
`le_realInterleavingDistance_of_finrank_lt` and
`le_realInterleavingDistance_of_structureMap_ne_zero` results turn such obstructions at every
finite `ε < r` into `r ≤ d(M,N)`. Over any ring,
`nonempty_realInterleaving_of_structureMap_eq_zero` constructs a witness from the zero maps when
both modules' double-shift structure maps vanish. The eight generic declarations remain available
under their original `TDA.Mapper` names as compatibility theorems.

For q-tame real modules over a field, an actual `ε`-interleaving `i` gives the
public quotient family `RealInterleaving.interpolatingModule i` on the closed
interval `[0, ε]`, with endpoints `startTime ε` and `endTime ε`.
`interpolatingModuleStartIso` and `interpolatingModuleEndIso` identify its
endpoint members with the input modules, `interpolatingModule_qTame` shows each
member is q-tame, and `interpolatingModuleInterleaving` gives every pair an actual
interleaving witness at the nonnegative distance between its parameters.
`interpolatingModule_qTame_interpolation` collects these facts for this family, and
`RealInterleaving.exists_qTame_interpolating_family` states the existential form.
This algebraic interpolation result does not assert a bottleneck or metric
stability theorem. See the
[real interleaving interpolation](math/real-interleavings.md#q-tame-algebraic-interpolation)
section for the quotient and the precise scope.

For an actual q-tame `ε`-interleaving, `RealInterleaving.exists_finite_saturating_matching`
constructs finite injective edge sets for any prescribed finite sets of finite-death
occurrences of lifetime greater than `2ε` and essential occurrences on both sides.
Every selected token is covered and every edge has cost at most `ε`. The
`FiniteSaturatingMatching` predicate states the injectivity, cost, and coverage
conditions explicitly. This finite saturation result does not assert a matching of
the full diagrams; `qTame_bottleneck_le_of_realInterleaving` supplies the global matching of the
full extracted diagrams (see the q-tame rectangle-measure section below). `Rips.exists_finite_saturating_matching_of_hausdorff_lt` applies
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

For clients (#1249): `faceSupDifference_le_iff` states that `faceSupDifference f g ≤ ε`
holds exactly when `0 ≤ ε` and every face value changes by at most `ε`;
`faceSupDifference_comm` is its symmetry. `bottleneck_dgm_le_of_abs_sub_le` is the diagram
bound from such a pointwise bound, and `exists_lt_abs_sub_of_ofReal_lt_bottleneck_dgm` is its
threshold form for every real threshold. `realInterleavingDistance_sublevel_le` takes its
bound in `NNReal` and needs no finiteness; a real bound `ε ≥ 0` enters as `ε.toNNReal`.
`FilterStabilityClientExamples` is a downstream regression fixture. It replays the pointwise diagram bound, its threshold form, the
interleaving-distance and `p`-transport bounds, and the coordinate interleaving and signed
hook bounds for multiparameter grades.

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
every degree. Certified here means that the reducer is formally verified: `run` takes the
list alone and computes the reduction, and it does not check a reduction trace or
certificate supplied by the caller.
Negative and tied grades, duplicate output points, empty input and
essential classes have explicit conventions. For a validated finite input,
`listEquiv` computes the original position of each actual face by finite list search;
`faceFintype`, `gradeFilter`, `positionEquiv`, `compatibleOrder` and
`sublevelFaceIndex` preserve that position, its listed grade and the input order.
Validity proofs do not affect the index or grade. Actual quotient-homology
constructions and the arbitrary-field decomposition remain noncomputable. See
[the input contract and correctness route](math/finite-ph-computation.md).

`TDA.Persistence.Reduction.DistanceTable N` is an integer distance table on the
labels `Fin N`, and the module `TDA.Persistence.Reduction.RipsInput` executes the
complete Rips simplex list of such a table in the `FiniteInput` format.
`DistanceTable.Valid` (nonnegative entries, symmetry, zero diagonal, positive distance between distinct
labels, every triangle inequality) is decidable; `ripsInput?` and `ripsRun` return
`none` for an invalid table, and nothing is repaired. `ripsInput` has one entry
`(s.map Fin.valEmbedding, diameter s)` for each nonempty set `s` of labels
(`mem_ripsInput`, `length_ripsInput`), ordered by grade, then cardinality, then
lexicographically in the increasing label lists (`ripsInput_pairwise`), and it
satisfies `FiniteInput.Valid` for every table (`ripsInput_valid`). For a valid
table, `metric` is the metric on the labels, `cast_diameter` identifies the integer
diameter with `Rips.diameter`, `complex_ripsInput` identifies the represented
complex with the image of `Rips.fullComplex (Fin N)`, and `gradeFilter_ripsFace`
identifies the listed grade of each face with the value of `Rips.filter`. `ripsRun`
returns the occurrence records of the existing reduction on the list
(`ripsRun_eq_bind_run`). The list has `2 ^ N - 1` entries and costs `O(N² 2 ^ N)`
label and integer operations; the cost of the existing reduction is separate and
not bounded. See
[Rips input from an integer distance table](math/finite-ph-computation.md#rips-input-from-an-integer-distance-table).

The module `TDA.Persistence.Reduction.RipsInputDiagram` compares the executed
list of a valid table with the Rips filtration of the table metric.
`DistanceTable.outputDiagram_ripsInput` states that `FiniteInput.outputDiagram`
of the list, mapped along `TDA.Persistence.intCastOrderEmbedding : ℤ ↪o ℝ`, is
`dgm (ZMod 2) (Rips.filter (D.metric hD))` in every degree; the caller supplies
no metric, isomorphism or certificate. `mem_sublevel_gradeFilter_ripsInput` and
`mem_sublevel_rips_filter` describe the faces of the two filtrations at a
threshold by the integer diameter. `ripsLabelMap` is the inclusion of the labels
as a vertex map from the Rips complex at an integer threshold to the sublevel
complex of the list; it induces an isomorphism in homology in every degree and
over every ring (`simplicialHomologyMap_ripsLabelMap_isIso`), compatible with
raising the threshold (`simplicialHomologyMap_ripsLabelMap_naturality`).
`ripsRunInDegree p` returns the occurrence records of degree `p`; it is `none`
exactly for an invalid table, whatever the degree
(`ripsRunInDegree_eq_none_iff`), and `ripsRunInDegree_correct` reads a returned
list as the point multiset of the Rips diagram. A permutation of the labels of a
valid table gives a valid table with the same diagram of the executed list
(`valid_of_relabel`, `outputDiagram_ripsInput_of_relabel`). The homology
comparison is stated at integer thresholds, and the relabelling statement is an
equality of diagrams, not of lists. No bound on the cost of the existing
reduction, no representatives for the Rips complex and no statement for invalid
tables beyond rejection are provided.

`TDA.Filtration.Alpha` gives the closed squared-grade Voronoi nerve for a
site embedding into a normed additive commutative group. `Alpha.carrier`
is the full nerve of the closed cells. In a finite-dimensional real
inner-product space, `Alpha.isLeast_grade` and `Alpha.isLeast_sq_dist`
give the attained grade, and `Alpha.sublevel_eq_complex` identifies
the actual stages.

`TDA.Filtration.AlphaLabelled` gives `Alpha.labelledComplexFiltration` for
a site function, allowing coincident sites and retaining all nearest-site
ties at a common witness. It agrees with `Alpha.complexFiltration` on
embeddings. The squared-grade `Alpha.squaredCechFiltration` uses radius
`√t` at nonnegative grades, and both it and labelled α are empty below zero.
The square-root reindexing of `Alpha.filtration_le_cech` uses radius zero
below zero.

Migration (#1138): new squared-grade α–Čech results should target the canonical
`Alpha.squaredCechFiltration` (empty below zero). `Alpha.filtration_le_squaredCech` and
`Alpha.inclusion_natural_squaredCech` are the canonical counterparts of the legacy
`Alpha.filtration_le_cech` and `Alpha.inclusion_natural`, which keep their statements and
radius-zero behaviour below zero and are not yet deprecated. The two targets agree at every
`t ≥ 0` (`Alpha.reindex_radius_cech_eq_squaredCech_of_nonneg`); below zero the legacy one is
`Cech.complex sites 0` (`Alpha.reindex_radius_cech_apply_of_neg`) and contains the canonical
one (`Alpha.squaredCechFiltration_le_reindex_radius`). The α complex is the nerve of the closed
Voronoi cells cut off by closed balls, so cocircular sites give the full cocircular simplex.

For finite linearly ordered labels in a real normed vector space,
`TDA.Persistence.AlphaH0` gives `alphaH0Iso` in ordinary degree zero
over a field. Its forward map `alphaH0Comparison` is the inclusion on
the same labels at every real squared grade. `Alpha.cech_edge_reachable`
gives α paths for Čech edges at nonnegative grades, and
`TDA.Simplicial.H0EdgePaths` turns the path condition into a degree-zero
homology isomorphism, over a field and, as
`simplicialHomologyIncl_zero_isIso_of_edge_reachable_of_ring`, over any ring. See
[closed α and the degree-zero comparison](math/alpha-filtration-and-signed-coverage.md).

For a site function `sites : V → E` on a finite linearly ordered label type
(`[LinearOrder V] [Finite V]`) into a finite-dimensional real inner-product space,
`TDA.Persistence.alphaCechIso sites R n` (module `TDA.Persistence.AlphaCech`) gives the
inclusion-induced natural isomorphism
from the homology of `Alpha.labelledComplexFiltration sites` to that of
`Alpha.squaredCechFiltration sites`, in every degree over any ring. Its components are the
ordinary simplicial homology inclusions (`alphaCechIso_hom_app`) and commute with every
structure map (`alphaCechIso_naturality`). `isIso_alphaCechComparison_app` states that each
component is an isomorphism, at negative grades too, and `isIso_alphaIncl_cech` is the
statement at one grade `t ≥ 0` for the inclusion into `Cech.complex sites (Real.sqrt t)`.
For embedded sites, `isIso_alpha_filtration_le_cech` is that statement for
`Alpha.filtration_le_cech` at `t ≥ 0`, and `isIso_alpha_filtration_le_squaredCech` is the
canonical counterpart for `Alpha.filtration_le_squaredCech` at every grade. Over a field, `alphaCechIso_zero` recovers
`alphaH0Iso`. Distinct labels may have the same site, and nearest-site ties are allowed.
The proof applies `ConvexNerve.isIso_simplicialHomologyIncl_of_compact`
([nerves of nested convex families](#realizations-subdivision-mesh-and-nerves-of-nested-convex-families))
to the restricted balls `Alpha.restrictedBall`, which are compact and, at `t ≥ 0`, convex
with the same union as the closed balls of radius `Real.sqrt t`
(`Alpha.isCompact_restrictedBall`, `Alpha.convex_restrictedBall`,
`Alpha.iUnion_restrictedBall`). The five-point example
`AlphaCechExamples.fivePointH1Square` follows a nonzero F₂ class across squared grades
4 and 5, including the strict α-to-Čech inclusion at grade 4.

For two site functions `p q : V → E` on one finite linearly ordered label type
(`[LinearOrder V] [Fintype V]`) into one finite-dimensional real inner-product space,
`TDA.Persistence.bottleneck_alphaRadiusDiagram_le_displacement` (module
`TDA.Persistence.AlphaRadiusStability`) bounds the degree-`n`
radius α diagram distance by the largest matched-site displacement `Cech.displacement p q`.
The coefficient field lies in the universe of the label type (`V : Type u`, `k : Type u`).
`alphaRadiusGrade` sends a radius `r ≥ 0` to the squared grade `r²` and fixes `r < 0`;
`alphaSquaredGradeToRadius` is the order isomorphism of `ℝ` with this inverse.
`alphaRadiusModule` is α homology reindexed along `alphaRadiusGrade`, and
`alphaRadiusCechIso` identifies it with the sublevel module of `Cech.filter p`. Its diagram
`alphaRadiusDiagram` equals the ambient Čech diagram (`alphaRadiusDiagram_eq_cech`), and
`alphaRadiusDiagramRealizationIso` recovers the entire module, including essential bars.
With embedded sites, `alphaRadiusDiagram_eq_map` takes the square root of each finite endpoint.

Squaring endpoints in `[0,R]` multiplies an endpoint error by at most `2R`
(`abs_sq_sub_sq_le_of_radius_le`). For the squares with corners at `(±7,±7)` and
`(±8,±8)`, the displacement and radius H₁ bottleneck over F₂ both equal `√2`, while
the squared-grade bottleneck equals `30` (`AlphaRadiusStabilityExamples.square_bottlenecks`).
`square_stability_attained` applies the stability theorem to these squares: the bound `√2`
holds in every degree over every field in `Type`, and over F₂ in degree one it is attained.

On the obtuse triangle, `CollapsePersistenceExamples.alphaCechIso` also gives the comparison
over every ring, through collapses; see
[homology of collapses](math/discrete-morse-matchings.md#homology-of-collapses).

For finite distinct rational planar sites, `TDA.Filtration.RationalAlpha`
supplies exact face entry grades through `entry?`, `gradedFaces`,
`cast_grade`, and `sublevel_eq_complex`. Its `Candidates` module enumerates
the sites, midpoints and circumcenters while preserving full nearest-site
ties. Its `Geometry` module proves `minimizer_mem_centers`. The `Predicates`
module gives `orient_zero_iff_collinear`, `incircle_geometry_ccw` and
`incircle_circumsphere_signs`, with the orientation and noncollinearity
hypotheses of their respective circle comparisons.

`TDA.Filtration.RationalAlpha.SignedBoundaryCoverage` supplies
`PolygonCertificate` and `rational_cover_from_signed_boundary`. The latter
gives off-edge interior multiplicity and closed hull coverage for injective
rational sites, an injective cycle whose certified convex hull contains
every site, and finitely many CCW triangles with the hull's signed boundary.
The same module also derives the certificate of a hull cycle.
`hull_polygonCertificate_hullOnly` takes noncollinearity of triples of distinct hull
positions and the real interior, frontier and left-support hypotheses. For a finite label
type, `cornerHullCheck` decides `StrictCornerCycle` (every nonincident corner strictly left
of each directed side) and `HullSitesLeft` (every site weakly left of each side) by rational
orientation. `cornerHullCheck_true_iff` identifies acceptance with a strict corner cycle
whose hull contains every site (`rational_sites_left_iff`), and `cornerHullCheck_sound`
gives the certificate (`rational_corner_certificate`) and the equality of the corner hull
with the convex hull of all sites (`siteHull_eq_all_sites`). A site on a hull side that is
not a corner passes the weak test (`HullCertificateExamples.midpoint_accepted`).
The module `TDA.Filtration.RationalAlpha.SubdividedBoundaryCoverage` proves
`rational_cover_from_subdivided_signed_boundary`. It takes the certificate of the coarse
cycle, a cut list on each side satisfying `OrderedEdgeCuts`, CCW triangles with vertices in
the hull, and equality of the triangle chain with the chain of the subdivided boundary
(`subdividedEdge`). It gives the hull coverage and the multiplicity off the segments of
`subdividedListedEdges`, so it applies to a triangle family with a vertex in the relative
interior of a hull side (`SubdividedBoundaryExamples.coverage_and_multiplicity`). With
empty cuts it gives `rational_cover_from_signed_boundary_of_triangle_sites`, the conclusions
of `rational_cover_from_signed_boundary` without injectivity of the sites or of the hull
labels and with hull membership required only for triangle labels. See
[signed coverage](math/alpha-filtration-and-signed-coverage.md#signed-coverage-of-a-certified-planar-hull).

The modules `TriangleIncidence`, `DirectedEdgeIncidence` and `TriangulationAssembly` under
`TDA.Filtration.RationalAlpha` describe the incidences of the triangle family of
`rational_cover_from_signed_boundary`. `disjoint_interiors_of_signed_boundary` states that
distinct certified pieces whose signed boundaries sum to that of a certified hull have
disjoint interiors. `rational_edge_counts` takes injective sites, an injective certified
cycle, CCW triangles and the chain equality. It states that
`occurrenceEdge tri` is injective, that each hull side has `directedMultiplicity` one and
its reverse zero, and that every other occurring ordered pair has multiplicity one in both
directions, in two different triangles. `TriangulationAssembly.labelComplex tri` has the
nonempty subfaces of the triangles as faces, and `certified_hull_face_incidence` adds that
each hull side is one of them, with its closed segment on the hull frontier. The
remaining statements also assume every site in the hull and `hgen`, the noncollinearity
of every triple of distinct sites. `triangle_inter_eq_shared_labels_of_signed_boundary`
identifies the intersection of two distinct closed triangles with the convex hull of the
sites of their shared labels (`labelVertices`). `open_site_edge_mem_frontier_iff` states
that a point of the open segment of two distinct sites is on the hull frontier exactly when
the pair is a hull side. `certifiedComplex` is a mathlib
`Geometry.SimplicialComplex ℝ Plane` on the images of the faces of `labelComplex tri`; its
space is the hull (`certified_space_eq_siteHull`), it has a facet and every facet has three
vertices (`certified_facets_pure_two`), and
`certified_nonhull_face_incidence` gives the two opposite occurrences of an edge that is
not a hull side, with its open segment in the hull interior.

`IncircleGrade` works with an embedding `site : V ↪ ℚ × ℚ` and a CCW triple whose
circumcenter `circumcenter?` returns as `o`. `checkIncircle site a b c` decides
`incircle ≤ 0` at every label of a finite label type (`checkIncircle_eq_true_iff`). These
inequalities hold exactly when the three labels have a common point of their closed cells
(`checkIncircle_eq_true_iff_commonCells_nonempty`), and every such point is `castPoint o`
(`commonCells_triangle_point_eq`); `castPoint_apply_zero` and `castPoint_apply_one` give the
two real coordinates of `castPoint o`. `triangle_mem_actual_stage_iff` states that `{a, b, c}`
is a face of `Alpha.complex (castSites site) t` exactly when the inequalities hold and
`sqDist o (site a) ≤ t`; `triangle_actual_carrier_iff` and `triangle_actual_grade` are the
carrier and grade forms. `EdgeGrade` treats two distinct labels of `p : Fin n ↪ ℚ × ℚ`.
`bisectorPoint` parametrizes the perpendicular bisector from the midpoint,
`edgeParameters p a b` is the set of parameters whose points lie in the common cells
(`bisector_mem_commonCells_iff`, `edge_commonCells_eq_image`), and
`squared_radius_on_bisector` gives the squared radius
`D / 4 + D * t ^ 2` with `D = directionSq (p a) (p b)`. `edge_actual_grade_projection`
gives the grade of a carrier edge at a feasible parameter `z` of least square, and
`edge_stage_of_parameter_min` states that the edge is in the stage at `t` exactly when
`D / 4 + D * z ^ 2 ≤ t`; `edge_carrier_iff_parameters_nonempty` and
`edge_actual_grade_eq_midpoint_iff` are the carrier and midpoint criteria.
`SuppliedEdgeGrade` defines `IncidentCenter`, `HullDual` and `InteriorDual`. For an injective
certified cycle, CCW triangles with the hull's chain and passing `checkIncircle` tests,
`supplied_hull_dual` gives a `HullDual` for each hull side when every site is in the hull:
`edgeParameters` is `Iic upper`, the common cells are the closed ray from the incident
circumcenter in the direction `outward`, and the stage threshold is
`D / 4 + D * (min 0 upper) ^ 2` (`HullDual.grade`). `supplied_interior_dual` gives an
`InteriorDual` for a supplied edge that is not a hull side: `edgeParameters` is
`Icc lower upper`, the common cells are the segment between the two incident circumcenters,
and the threshold is `D / 4 + D * (max lower (min upper 0)) ^ 2` (`InteriorDual.grade`).
`NoFourIncircleZeros p` asks for a nonzero incircle determinant on every four distinct
labels, and `GeometricNoFourCocircular p` that no point of the plane is equidistant from
four distinct sites; either gives `lower < upper` (`InteriorDual.strict`,
`InteriorDual.strict_geometric`).

`SuppliedCarrier.carrier_eq_of_signed_boundary` states
`Alpha.carrier (realSites p) = labelComplex tri` for `p : Fin n ↪ ℚ × ℚ`. Its hypotheses
are an injective hull cycle, its `PolygonCertificate`, every site in the hull, CCW
triangles, equality of the triangle chain with the chain of the hull cycle, a passing
`checkIncircle` test for every triangle, and
`GeometricNoFourCocircular p ∨ NoFourIncircleZeros p`; `hgen` is not among them. The two
inclusions are `labelComplex_le_alphaCarrier`, from the CCW triangles and passing tests
alone, and `alphaCarrier_le_labelComplex_of_signed_boundary`, which uses the closed cover;
`allSitesUsed_of_carrier_eq` derives that every label is used. Under the same hypotheses
and for `tri : Fin m → Fin 3 → Fin n`, `SuppliedGradeEnumeration.suppliedGrades p tri` is an
executable finite set of rows of a face and a rational grade (`grade?`, `edgeGrade?`,
`triangleGrade?`; `mem_suppliedGrades` states that `(s, q)` is a row exactly when `s` is a
face of `labelComplex tri` and `grade? p tri s = some q`). `grade?` reads the face labels
through `Finset.sort` and does not reduce under `decide +kernel`; `kernelGrade?` reads them
through `sortedLabels` (`sortedLabels_eq_sort`) and does, and `kernelGrade?_eq_grade?` states
that the two lookups agree. `grade_on_supplied_face`
identifies each computed grade with the value of `Alpha.filter`, and
`suppliedGrades_eq_reference` states
`suppliedGrades p tri = gradedFaces p`. `SuppliedStages.realStageTable rows t` is the set of
faces with a row of grade at most the real `t` (`mem_realStageTable_iff`), and it is
`stageTable` at a rational cutoff (`realStageTable_cast`). `supplied_hasGradeTable` gives
`HasGradeTable (Alpha.complexFiltration (realSites p)) (suppliedGrades p tri)`, and
`supplied_realStage_iff` states
`s ∈ realStageTable (suppliedGrades p tri) t ↔ s ∈ Alpha.complex (realSites p) t` for every
real `t`, with `supplied_realStage_faces` the equality of the face sets and
`supplied_realStage_neg` the empty table for `t < 0`. `reference_hasGradeTable` is the table
statement for `gradedFaces p`, for every embedding `p`. In `SuppliedStagesExamples`,
`cornerHullCheck` supplies the certificate of `supplied_realStage_iff` for the trapezoid
(`trapezoid_checked_stages`) and for an input whose interior edge `{0,1}` is not Gabriel
(`inner_checked_stages`); that edge enters actual α at the squared grade `25/4`, above its
Gabriel value `4` (`inner_nonGabriel_cutoff`). These carrier, grade-row and stage
theorems compare the triangle chain with the chain of the hull cycle itself, so every hull
side is an edge of a supplied triangle (`TriangulationAssembly.certified_hull_pair_face`).
When a hull side carries site labels in its interior, the coarse triangle on that side fails
`checkIncircle`; supply the pieces that split the side instead. The chain of the ordered
subdivided hull sides is the hypothesis of `rational_cover_from_subdivided_signed_boundary`,
whose conclusions are the multiplicity and the coverage, and of
`SuppliedCarrier.carrier_eq_of_subdivided_boundary`, which states
`Alpha.carrier (realSites p) = labelComplex tri` from the strict `PolygonCertificate` of the
coarse hull, `OrderedEdgeCuts` for each side, every site in the coarse hull, CCW triangles,
the chain equality against `subdividedEdge (cycleEdges hull) cuts`, passing `checkIncircle`
tests and `GeometricNoFourCocircular p ∨ NoFourIncircleZeros p`; the hull labels need not be
injective. `alphaCarrier_le_labelComplex_of_subdivided_boundary` is the inclusion, and
`alphaCarrier_le_labelComplex_of_closed_cover` and `admitted_triangle_contact` are public
for clients with their own convex cover. `SuppliedCarrierExamples.split_carrier` (sites `splitEmb`) applies it to
a triangle whose bottom side is split at its midpoint, using `SubdividedBoundaryExamples`'s
`coarse_certificate`, `ordered_cuts` and `sites_contained`, and `split_side_faces` shows both
subedges are carrier faces and the coarse side is not.
`SubdividedStages` gives the grade rows and stages for the same inputs, with the same
hypotheses (the no-four-cocircular hypothesis only on rows and stages) and no injectivity of
the hull labels: `subdivided_hull_dual` (a `HullDual` for every refined side),
`subdivided_edge_counts` (each refined side occurs once forward and never backward),
`edge_grade_on_subdivided`, `suppliedGrades_eq_reference_of_subdivided_boundary`,
`supplied_hasGradeTable_of_subdivided_boundary` and
`supplied_realStage_iff_of_subdivided_boundary`, with `supplied_realStage_faces_of_subdivided_boundary`
and `supplied_realStage_neg_of_subdivided_boundary`. The coarse dual, row and stage theorems keep their
statements and call the hull-free cores `hull_dual_of_supporting_side`,
`interior_dual_of_opposite_occurrences`, `grade_on_face_of_edge_grades` and
`suppliedGrades_eq_reference_of_face_grades`; `subdivisionEdges_side` and the multiplicity
lemmas `multiplicity_absent`, `multiplicity_at_most_one` and `multiplicity_listed` are public.
`SubdividedStagesExamples.split_checked_stages` gives all real stages of the split triangle, with
`split_bc_cutoff` (the non-Gabriel edge BC enters at `5/2`) and `split_am_cutoff` (the refined
piece AM enters at `1/4`). The inputs of the split fixture are checked, not proved by hand:
`checkOrderedEdgeCuts` is an executable rational test with `orderedEdgeCuts_of_check`, and
`DirectedEdgeIncidence.chain_eq_of_directed_counts` reduces the chain equality to equal net
directed counts, a finite check. See
[supplied carrier and stages](math/alpha-filtration-and-signed-coverage.md#supplied-carrier-and-stages).

For finite rational planar point clouds, `TDA.Persistence.Reduction.AlphaInput.run`
computes an F₂ barcode with exact rational squared-radius endpoints. It accepts
the empty family and rejects precisely families with repeated coordinates.
`AlphaInput.run_correct` identifies the degreewise point multiset with the
diagram of actual closed α persistence; `run_correct_of_fintype` states the same
with injectivity taken from the successful run (`injective_of_run_eq_some`) and with
any `Fintype` instance on the faces. The label map identifies the sublevel
homology at any real threshold with the integer reducer sublevel, and commutes
with inclusion maps. Essential deaths and repeated occurrences are retained.
[Exact planar α barcodes](math/finite-ph-computation.md#exact-planar-α-barcodes).

The module `TDA.Persistence.SublevelDiagramVertexMap` holds the general
statements behind this comparison. `TDA.Simplicial.simplicialHomologyMap_congr`
states that vertex maps agreeing on the vertices of every face induce the same
map in homology, and `simplicialHomologyMap_comp_eq_id` that a vertex map
followed by one undoing it on those vertices induces the identity.
`TDA.Persistence.dgm_eq_of_vertexMaps` states that real filter functions on
complexes over two vertex types have the same diagram, in every degree and over
every field, when functions on the vertices in both directions preserve every
sublevel complex and are mutually inverse on the vertices of the faces. It is
stated for real grades only. See
[Diagram and homology of the Rips input](math/finite-ph-computation.md#diagram-and-homology-of-the-rips-input).

`FiniteInput.runWithRepresentatives` adds original face-index cycle supports and,
for finite occurrences, bounding supports while preserving that exact ordered
output. Its correctness API proves actual signed simplicial boundary identities,
nonzero classes at alive face prefixes and their unit normal-form coordinates.
`runAtGrade` selects value-alive records; `sublevelClass_naturality` follows their
actual integer-sublevel classes from birth onward, and `sublevelClass_nonzero_iff`
identifies finite death and essential survival. The API retains equal-grade
exclusion. `runDegreeAtGrade` selects one degree in that same order;
`sublevelBasis` proves that its returned cycle classes form a basis of the entire
actual sublevel homology. `sublevelCoordinates` gives each class its unique
coefficient vector, and `sublevelCoordinates_naturality` represents every
inclusion by the executable `basisTransition` matrix, matching original birth
indices across queries. `runCycleCoordinates` accepts arbitrary original-face F₂
vectors, checks that they are cycles in the selected degree and sublevel, and
returns their coefficients in that query order. Its correctness theorem identifies
the actual homology coordinates; zero and equality tests detect boundaries and
equal homology classes. `runCycleFilling` constructs an original-index filling
for every admitted cycle whose coordinates vanish. Its correctness API preserves
the returned coefficients in an actual sublevel chain and proves its signed
boundary is the supplied cycle; on admitted cycles, success is equivalent to
actual boundary membership. See
[cycle representatives](math/finite-ph-representatives.md).

`runHomologyMap` computes a vertex-induced homology map between two finite inputs
in these source and target bases. It validates every admitted face image, handles
noninjective vertex functions and proves agreement with the existing actual
`simplicialHomologyMap` on every class. Its matrix laws include identity,
composition and the existing sublevel-inclusion transition. See
[computing finite homology maps](math/finite-ph-maps.md).

`runHomologyLift` accepts a target cycle and computes a source cycle together
with a target chain whose boundary is the target minus the source image.
Success is equivalent to range membership for the actual induced homology map;
source coefficients round-trip in the existing basis order. The finite F₂ search
is exponential in source Betti dimension and intended for small groups. See
[homology preimages with chain certificates](math/finite-ph-lifts.md).

`runHomologyDimensions` computes the rank and nullity of the same finite F₂
induced map. Its correctness theorem identifies the returned numbers with the
actual homology map's image and kernel dimensions; public criteria characterize
injectivity and surjectivity. It validates all admitted face images even for
zero groups, and uses enumeration exponential in source Betti dimension.
See [homology-map dimensions](math/finite-ph-map-dimensions.md).

The same enumeration is available for any rectangular F₂ matrix, independently
of simplex input. For `M : Matrix (Fin m) (Fin n) (ZMod 2)`,
`F2Matrix.imageFinset M` is the computed set of images of all `2^n` source
vectors and `F2Matrix.rank M` is the base-two logarithm of its cardinality
(namespace `TDA.Persistence.Reduction`). `F2Matrix.rank_eq_finrank_range` and
`F2Matrix.rank_eq_matrixRank` identify the executed number with the dimension
of the range of `M.mulVecLin` and with Mathlib's noncomputable `Matrix.rank M`;
`F2Matrix.rank_toMatrix'` states the same for the matrix of a linear map
between coordinate spaces. `F2Matrix.rank_add_finrank_ker`,
`F2Matrix.rank_le_width` and `F2Matrix.rank_le_height` give rank–nullity and
the two shape bounds. There is no hypothesis on `m`, `n` or `M`: with no rows
or no columns the rank is zero. Write `F2Matrix.rank M`,
since `M.rank` in dot notation is Mathlib's function. The cost is exponential
in the number of columns; this is not an elimination algorithm.

`validateGlobalVertexMap xs ys f` checks both input lists and requires every
source face image to occur in the target at no later grade. Its correctness
lemmas identify this finite condition with preservation of every integer
sublevel, including cross-threshold maps. For any monotone sampling
`t : Fin s →o ℤ`, `sampledHomologyMap` constructs the natural transformation
of actual F₂ sublevel homology modules induced by that fixed vertex function.
Repeated and negative thresholds and collapsed faces are allowed.
`sampledHomologyMap_image_rank` identifies each image structure-map rank with
the range dimension of the actual simplicial map from the earlier source
sublevel to the later target sublevel. The generic
`finiteImage_structureMapRank` requires finite-dimensional target fibers,
with no finite-dimensional-source assumption. Identity specialization
recovers the ordinary source rank.

`runImageBarcode xs ys p f t` extracts a certified image barcode for the supplied
observations `t : Fin N → ℤ`. It returns `some out` exactly when both geometries,
global face-grade preservation and monotonicity of `t` validate. Empty, negative
and repeated observations are allowed; no observations are sorted or removed.
The executable path materializes every comparable-pair `homologyMapDimensions`
rank, extends that table by zero outside `0 ≤ i ≤ j < N`, and computes the signed
integer four-term differences. Their nonnegativity is proved before interpreting
them as natural multiplicities. Output intervals are ordered by birth, then
death, and equal intervals remain separate occurrences.

`imageBarcode_multiset` identifies the output multiset with `rankBarcode` of
the actual sampled image module. The multiplicity and rank laws retain all
endpoint counts and every forward rank; `imageBarcode_nonempty_iso` gives a
genuine natural isomorphism to its barcode realization. These are proof-side
consequences: extraction executes no quotient homology, chosen basis or
decomposition. Identity input yields the ordinary sampled source barcode.
Endpoints are observation indices with `birth < death ≤ N`; death `N` means
survival through the last observation only. It asserts no lifetime beyond or
between samples. The table uses quadratic storage and at most `N(N+1)/2` rank
evaluations, each using the existing enumeration exponential in source Betti
dimension. Output replication also costs the number of interval occurrences.


### Minimal-complement cardinalities for finite grids

Here `minimalComplement p` is the set of minimal elements of `{a | ¬ a ≤ p}` in a lattice; the cardinality and maximum functions add a `Finite` assumption. `PairPoset S` is the actual subtype `{q : WithTop S × WithTop S // q.1 ≤ q.2}` with inherited coordinatewise order. The grid bounds concern an actual `G : CoordinateGrid n` with nonempty coordinate factors.

`TDA.Persistence.FiniteLatticeComplementCardinality.mem_minimalComplement_pi_iff_of_orderBot` gives the caller-bound classification for products of lattices: membership in the product's minimal complement is equivalent to one coordinate being a minimal complement in its factor and every other coordinate equaling the supplied factor bottom. It needs no finiteness or linearity; each supplied `OrderBot` already provides its factor bottom and inhabitant, so no separate `Nonempty` assumption is needed. The compatibility theorem `mem_minimalComplement_pi_iff` retains its finite index and finite nonempty linear-factor assumptions, with canonical bottoms from the private factor enumeration `Fintype.ofFinite (T i)` and its `Fintype.toOrderBot` instances. The general classification alone does not bound the number of minimal complements by the number of factors, since a lattice factor may have multiple incomparable minimal complement values; the finite-chain product count retains its original hypotheses. The module also proves the old-top singleton correction for `WithTop`, and the exact restricted-diagonal plus bottom-axis decomposition for the existing `PairPoset` subtype. It then proves the `n`, `n`, and `2*n` maximum bounds for `G.Point`, `WithTop G.Point`, and `PairPoset G.Point` when the coordinate factors are nonempty (the last two require `n ≥ 1`). The old and new tops are treated as distinct elements.

`TDA.Persistence.FiniteGridInjectiveRankDimension.hasProjectiveDimensionLE_of_coordinateGrid` derives the actual `n - 1` Hom projective-dimension bound for every pointwise finite-dimensional ordinary injective on such a grid, for an arbitrary field. Its `termAt_isZero_of_coordinateGrid` consumer proves the same high-term vanishing for each supplied certified minimal resolution. The proof uses the proved grid count and the existing finite-injective dimension theorem; no dimension bound is supplied as input. These counts and the ordinary-injective Hom corollary are representation-side ingredients; the actual finite-dimensional incidence and quotient-module bound is stated below. That module result does not give a global-dimension bound for arbitrary modules or the universal `2n−2` persistence estimate. See [minimal-complement cardinalities in finite grids](math/finite-grid-complement-cardinality.md).

### Ordinary projective dimension on finite lattices

For an arbitrary field and finite bounded lattice, `TDA.Persistence.OrdinaryFiniteLatticeDimension.hasProjectiveDimensionLE`
proves that every pointwise finite-dimensional persistence functor itself has ordinary projective
dimension at most `FiniteInjectiveRankDimension.maxComplementCard`. The module also exposes the
actual hook-inclusion monomorphism, the ordinary dimension bound for finite hooks and pfd
rank-projectives, the loose bound from any actual finite rank-projective resolution's recorded
term count, and the complement-card bound for principal-downset and ordinary injective objects.
Its grid corollaries give bounds `n` on `CoordinateGrid n` and `2*n` on the actual interval-pair
poset when `n ≥ 1`.

This is a result in the actual `PModule` representation category. It does not assume an ordinary
dimension bound on the input, and it does not estimate arbitrary modules over the incidence
algebra. The actual Hom module and its finite-grid dimension bound are handled separately below;
they do not follow from this representation-category theorem alone. See
[ordinary projective dimension on finite lattices](math/ordinary-finite-lattice-dimension.md).

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
focused consumers in `TDA.Persistence.IncidenceQuotientSimpleExamples`. Its statements need no
scope or local instance in a client: the two-sidedness of the diagonal ideal that makes
`RightQuotient` a ring is the global instance `IncidenceQuotientSimple.diagonalIdealTwoSided`,
and `IncidenceQuotientSimpleClientExamples` states each classification theorem as a client
does. This is the simple-module
classification step used in BOOS24-v3 Lemma 5.7, specialized to the interval-pair quotient; it
does not assert the global-dimension conclusion of that lemma.

When a caller already has a `C`-linear isomorphism `i : M ≅ RightVertexModule v`,
`IncidenceQuotientSimple.leftDerivedZeroIso_of_rightVertexIso` constructs the `k`-linear
degree-zero comparison directly from that selected `i`, without requiring a simplicity instance.
The compatibility entry point `simpleModule_leftDerivedZeroIso` retains its simplicity-instance
parameter, and the simple-module classification APIs use that hypothesis. For positive degrees,
the derived object vanishes at every strict vertex, independently of the classified module; the
unique-vertex theorem packages this vanishing with its simple-module classification.

The reusable scalar transport from bundled left-module coinvariants to the natural quotient-field
action is public as `TDA.Persistence.IncidenceVertexTor.diagonalQuotientVertexCoinvariantsEquiv`,
with its representative law `diagonalQuotientVertexCoinvariantsEquiv_mkQ`. The constant family of
regular right-incidence modules used by the finite-free vertex biproduct is
`TDA.Persistence.IncidenceRegularVertex.regularFamily`. The quotient-resolution statements spell
out `ModuleCat.restrictScalars (quotientHom ...)` and `extensionFunctor` directly where each
construction occurs. The existing
`TDA.Persistence.FiniteRankProjectiveEndAlgebra.PairPoset` scope supplies the canonical
interval-pair instances.

`TDA.Persistence.IncidenceQuotientBaseChange.extensionFunctor` constructs actual right-module
extension along the quotient projection `A → A/I` by quotienting each incidence module by the
action of the kernel. The actual universal property is packaged as `extensionAdjunction`; the
functor preserves projectives and finite colimits (so it is right exact). `extensionRestrictionIso`
is the natural counit, identifying the extension of any restricted quotient module with that
module, and `regularExtensionIso` sends the regular incidence module to the regular quotient
module by the actual quotient map. For each strict vertex, `rightVertexExtensionDerivedZeroIso`
gives the canonical `C`-linear degree-zero derived comparison. The
`IncidenceQuotientDerivedOne` module proves that the actual quotient kernel is idempotent, that
extension preserves short exact rows with restricted quotient-module cokernel, and that applying
extension to any projective resolution of a restricted quotient module is exact at degree one.
Consequently `extension_leftDerived_one_isZero` proves the actual first left-derived vanishing for
every restricted quotient module, with `rightVertexExtension_leftDerived_one_isZero` as its
strict-vertex specialization. `IncidenceQuotientColumnAction` constructs an auxiliary additive
column functor whose natural assembly has image equal to the actual relation submodule and is
injective on every projective incidence module. `IncidenceQuotientDerived` uses this construction
to prove that the actual extension of every projective resolution is exact at every degree `n ≥ 2`
for every incidence module, and that `extension_leftDerived_isZero_atLeastTwo` gives the actual
categorical vanishing there. For a restricted quotient module, exactness and derived vanishing hold
in every positive degree, with `rightVertexExtension_leftDerived_positive_isZero` giving the
strict-vertex case. The unaugmented mapped resolution retains its potentially nonzero degree-zero
comparison; degree-one exactness for arbitrary incidence modules and degree-zero exactness are not
claimed. No numerical dimension bound or `2n−2` persistence estimate follows here. See
[right-module base change along the diagonal quotient](math/incidence-quotient-base-change.md)
and the focused consumers in `TDA.Persistence.IncidenceQuotientBaseChangeExamples`,
`TDA.Persistence.IncidenceQuotientDerivedOneExamples`, and
`TDA.Persistence.IncidenceQuotientDerivedExamples`.

`TDA.Persistence.IncidenceQuotientProjectiveResolution.extensionProjectiveResolution` turns any
actual projective resolution of a restricted quotient module into an augmented projective
resolution of the quotient module, with complex literally given by termwise extension and
augmentation followed by the natural counit. Its computation laws expose the terms,
differentials, and representative-class formula, and it transports any supplied termwise
vanishing-above-degree condition. `extension_hasProjectiveDimensionLE_restricted` transfers each
finite projective-dimension bound from the restricted module, while
`projectiveDimension_le_restriction` proves the unconditional comparison in `WithBot ℕ∞`,
including zero objects and infinite projective dimension. These results use the actual diagonal-column
assembly and ordinary projective epimorphisms; they do not imply a numerical incidence bound or a
`2n−2` stability estimate. See
[right-module base change along the diagonal quotient](math/incidence-quotient-base-change.md)
and the focused consumers in
`TDA.Persistence.IncidenceQuotientProjectiveResolutionExamples`.

`TDA.Persistence.IncidenceQuotientDimension` proves that the projective dimension of any
finite-length right quotient module is bounded by the supremum of the dimensions of the actual
strict-vertex modules. It also gives the natural uniform-bound equivalence and the corresponding
results for modules finite-dimensional under the existing restricted `k`-action. The proof uses
the #699 classification in a Mathlib finite-length extension induction. It gives no numerical
dimension bound and no quotient-versus-incidence global-dimension comparison. See
[finite-length quotient dimensions](math/incidence-quotient-finite-length-dimension.md) and the
consumers in `TDA.Persistence.IncidenceQuotientDimensionExamples`.

`TDA.Persistence.IncidenceVertexRepresentation.vertexFunctor` sends every actual right module
over the interval-pair incidence ring to its covariant representation on all diagonal-unit-fixed
vertex fibers, with the canonical restricted field action. The actual projector maps give a
linear equivalence between the module and the finite product of its fibers. An explicit
matrix-unit reconstruction proves full faithfulness and provides both Hom inverse laws.
`rightIncidenceShortExact_iff_vertexPointwise` characterizes actual categorical short exact rows
by pointwise fiber exactness, and `finiteDimensional_iff_vertexFibers` characterizes finite
dimension over the restricted field. The results apply to arbitrary modules and include
diagonal vertices; essential surjectivity, an equivalence with all persistence functors, and
projective-dimension transport by this representation theorem alone are not established here. The
separate finite-dimensional module comparison below uses the actual regular-module vertex image
and finite-free covers. See
[actual vertex representations of right incidence modules](math/incidence-vertex-representation.md)
and the Bool regular-module examples in `TDA.Persistence.IncidenceVertexRepresentationExamples`.
`IncidenceRegularVertex.regularVertexIso` identifies the regular module's actual vertex image with
the graded free module on interval-pair vertices; its public coefficient and birth laws compute
the identification on each fiber. `IncidenceRegularVertex.regular_finiteDimensional` proves
finite-dimensionality over `k` of the actual regular right-incidence module with its canonical
restricted field action. `IncidenceRegularVertex.incidence_finiteDimensional` proves
finite-dimensionality over `k` of the incidence algebra via `regularIncidenceLinearEquiv`, the
explicit `k`-linear equivalence induced by `unop`. These are vector-space dimension results, not
ordinary projective-dimension bounds.

### Canonical PairPoset instances

For incidence-algebra clients with `{k : Type u} [Field k]` and
`{S : Type} [Lattice S] [Finite S]`, use
`open scoped TDA.Persistence.FiniteRankProjectiveEndAlgebra.PairPoset` to activate the canonical
`PairPoset S` instances used by the library. The scope provides the existing finite
enumeration, order decisions, locally finite order, and two-sidedness proof for the diagonal
ideal. These transparent aliases select the producer's original data, including the filtered
subtype enumeration; they do not promise definitional equality with arbitrary caller-selected
noncanonical instances. The enumeration and locally finite order require `[Finite S]`; the
order decisions require only `[Lattice S]`, and the diagonal-ideal proof retains the field
assumption.

This scope does not provide endpoint or bounded-order structures. The incidence and quotient
projective-dimension bounds keep their `[OrderBot S] [OrderTop S]` assumptions and their
displayed `pairPosetLattice` and `pairPosetBoundedOrder` choices. Native finite instances on
`Bool` and `Fin 2` remain unchanged.

### Ordinary projective dimensions of actual incidence modules

For an arbitrary field and finite bounded lattice `S`,
`TDA.Persistence.IncidenceVertexProjectiveDimension.hasProjectiveDimensionLE` proves that every
finite-dimensional actual right module over the interval-pair incidence ring has projective
dimension at most the maximum minimal-complement count of `PairPoset S`. The module's ordinary
projective dimension is compared with that of its actual all-vertex representation by
`hasProjectiveDimensionLE_of_vertex`; the representation bound comes from
`OrdinaryFiniteLatticeDimension`. The quotient theorem
`quotient_hasProjectiveDimensionLE` gives the same bound for finite-dimensional actual right
modules over the diagonal quotient, measured with the canonical restricted `k`-action.

For an actual coordinate grid `G : CoordinateGrid n` with nonempty factors and `n ≥ 1`, the
incidence and quotient grid theorems give bound `2*n` for every such finite-dimensional module.
These are unconditional consequences for the stated finite-dimensional modules: no resolution or
projective-dimension bound is an input. The result does not establish essential surjectivity of the
vertex representation or finite projective dimension for arbitrary incidence modules. It also
does not establish the real-coordinate transfer or final stability result. See
[ordinary projective dimensions of actual incidence modules](math/incidence-projective-dimension.md)
and the focused consumers in
`TDA.Persistence.IncidenceVertexProjectiveDimensionExamples`, which apply the
complement-count bound and the incidence grid bound to zero modules and to the
nonzero regular module.

### Actual Hom modules and their cokernels

For any field `k`, finite indexing preorder `S`, and pointwise finite-dimensional
`X,Y : PModule k S`, `FiniteHomDimension.finiteDimensional_hom` proves that the
natural-transformation space `(X ⟶ Y)` is finite-dimensional over `k`. This is
the vector space of morphisms; the hook-generator persistence module
`H(M) = (homFunctor.obj M)` below is a different object, whose ordinary
projective dimension is treated separately.

For an arbitrary field and a finite bounded lattice `S`, let `P = PairPoset S` and let
`D(P) = maxComplementCard (S := P)`. Write `H(M) = (homFunctor.obj M)` and let `K(M)` be the
actual categorical cokernel of the map induced by `homFunctor` on the two-injective differential.
For every pointwise finite-dimensional `M : PModule k S`,
`FiniteRankProjectiveHomQuotientDimension.homCokernel_hasProjectiveDimensionLE` proves the
ordinary projective-dimension bound `D(P)` for `K(M)`. The proof establishes its
finite-dimensionality from `M`; neither a projective-dimension estimate nor compatible scalar
action is assumed.

For an actual `n`-coordinate grid with nonempty factors and `n ≥ 1`, the actual Hom cokernel has
ordinary projective dimension at most `2*n`, while `H(M)` has ordinary projective dimension at
most `2*n-2`. Every supplied certified
minimal finite-rank-projective resolution of such an `M` has zero `termAt j` for `j > 2*n-2`.
This concerns the highest nonzero degree and is insensitive to terminal zero padding; it is not a
bound on the raw stored length. The coefficient field remains arbitrary. Its real-coordinate
transfer is documented above; the finite signed-hook matching and squared
bound are proved in [signed hook bottleneck stability](#signed-hook-bottleneck-stability). See
[finite-grid Hom-module and Hom-cokernel dimensions](math/finite-rank-projective-hom-quotient-dimension.md)
and the rational and grid consumers in
`TDA.Persistence.FiniteRankProjectiveHomQuotientDimensionExamples`.

The standalone fixture `TDA.Persistence.FiniteRankProjectiveHomNonprojectiveExamples` exhibits
both rank nonprojectivity of a persistence module and ordinary categorical nonprojectivity of
its actual hook-generator Hom module. For every field, `bottomSimple` is the principal-downset
module at the bottom of `Square = Bool × Bool`; the actual Hom module has ordinary projective
dimension exactly one. Every certified minimal finite rank-projective resolution of
`bottomSimple` has a nonzero `termAt 1` and zero terms for `j > 1`, and a separate existential
theorem derives a certificate with those properties from the field alone. The exact dimension
claim is about the Hom module, and this finite-lattice example does not assert sharpness of the
`2*n-2` coordinate-grid bound. The fixture selects the preorder category with a public scoped
instance; consumers can use it with `open scoped TDA.Persistence.FiniteRankProjectiveHomNonprojectiveExamples`.

## Acyclic matchings for discrete Morse reduction

`TDA.Persistence.Morse.AcyclicMatching` (imported by `TDA.Persistence`) states matchings
on the faces `TotalFace K` of a preabstract simplicial complex `K` on any vertex type, as
relations `M σ τ` ("`σ` is matched with its codimension-one coface `τ`"). `IsMatching M`
requires `σ ⋖ τ` for every pair, at most one pair per lower cell and per upper cell, and no
upper cell that is also a lower cell; `TDA.Simplicial.covBy_iff_subset_card` reads `σ ⋖ τ`
as `σ ⊆ τ ∧ #τ = #σ + 1`.

`arrow M` is the modified Hasse diagram on all faces, including unmatched and isolated ones:
an unmatched cover pair `σ ⋖ τ` gives the arrow `τ → σ` (coface to face) and a matched pair
gives `σ → τ` (face to coface). `IsAcyclic M` forbids directed cycles of `arrow M`, and
`IsAcyclicMatching M` is `IsMatching M ∧ IsAcyclic M`; the empty matching satisfies it.
For a matching, `isAcyclic_iff_isMNAcyclic` proves acyclicity equivalent to the
Mischaikow–Nanda Def. 2.2 form `IsMNAcyclic` (the order generated by `mnRel` on matched
lower cells is a partial order; `isMNAcyclic_iff_irrefl` restates it as the absence of an
`mnRel` cycle).

`IsTopologicalRank M rank` asks for `rank : TotalFace K → ℕ` with `rank u < rank v` for every
arrow `u → v`; faces with no arrow between them may tie. Such a rank implies acyclicity, and
`isAcyclic_iff_exists_rank` proves the converse with finitely many faces
(`[Finite (TotalFace K)]`); that direction is a classical existence proof.

For `f : FilterFunction K α` over a linear order, `IsGradePreserving f M` requires equal
grades on every pair, and `restrictSublevel f r M` keeps the pairs inside `f.sublevel r`.
The restriction of an acyclic matching to every sublevel is an acyclic matching, and an
equal-grade pair never straddles a sublevel. `IsFilteredAcyclicMatching f M`, the
Mischaikow–Nanda Def. 4.1 form for sublevel frames, is a matching whose pairs never straddle
a sublevel and whose restriction to every sublevel is acyclic;
`isFilteredAcyclicMatching_iff` proves it equivalent to
`IsAcyclicMatching M ∧ IsGradePreserving f M`.

These are semantic predicates only. The module provides no executable checker, chain
contraction, Morse complex, persistence isomorphism, matching generation or runtime bound.
See [acyclic matchings for discrete Morse reduction](math/discrete-morse-matchings.md) and
the [MN13 source mapping](math/references.md#MN13).

`TDA.Persistence.Morse.FiniteInputMatching` (imported by `TDA.Persistence`, namespace
`TDA.Persistence.Morse.MatchingInput`) checks a matching supplied on a finite input
`xs : FiniteInput.Input`. Faces are list positions `Fin xs.length`, and a matching is a list
`pairs : Pairs xs` of ordered (lower, upper) position pairs. `IsMatching xs pairs` requires
pairwise distinct endpoints (`endpoints pairs`), a cover `IsCover xs i j` (subset with exactly
one more vertex) for every pair and equal grades. A reversed pair is rejected, not normalised,
and a pair listed twice counts as reuse. The certificate is `rank : Fin xs.length → ℕ`, and
`IsTopologicalRank xs pairs rank` asks for `rank u < rank v` along every list-level arrow
(unmatched cover pairs coface to face, listed pairs face to coface). `MatchingInput.check xs
pairs rank : Bool` decides both, and `check_eq_true_iff` proves that it returns `true` exactly
when `IsMatching xs pairs ∧ IsTopologicalRank xs pairs rank` holds. The executable predicates
need no validity proof.

For `h : Valid xs`, `toRel xs h pairs` is the induced relation on the faces of
`complex xs h`. `exists_check_iff` proves that some rank is accepted exactly when
`pairs.Nodup` holds and `toRel xs h pairs` is an acyclic matching with equal grades for
`gradeFilter xs h`, and `exists_check_iff_isFilteredAcyclicMatching` states the same with
`IsFilteredAcyclicMatching`. `pairs.Nodup` is needed because `toRel` forgets repeated pairs.
`certify? xs pairs rank` returns a `CertifiedMatching xs` (the pairs, the rank and both
proofs) exactly when `check` accepts. Its `critical` list holds the unmatched positions in
increasing order, and `criticalReport` lists each with its dimension `(xs.get i).1.card - 1`
and original grade `(xs.get i).2`; `trichotomy` and `critical_length_add` classify and count
the positions. `TDA.Persistence.Morse.FiniteInputMatchingExamples` (imported by
`TDA.Persistence.Examples`) holds accepted and rejected fixtures, including the multi-grade
square with critical faces A, AD and ACD. `check` does not search for a matching or rank, and
no runtime bound is stated; see
[checking a supplied matching](math/discrete-morse-matchings.md#checking-a-supplied-matching).

`TDA.Persistence.Morse.FiniteInputMatchingGeneration` (imported by `TDA.Persistence`, same
namespace) generates a certified matching. `MatchingInput.candidates xs` lists the same-grade
cover pairs of positions in the fixed lexicographic (lower, upper) order, and `generate xs :
CertifiedMatching xs` is one greedy pass over them from the empty matching: a candidate is
appended exactly when `certify?` accepts the extended list with the rank `candidateRank`
computes for it. `generate` is total and needs no `Valid` hypothesis.
`generate_pairs_sublist` proves that the generated pairs are a sublist of the candidates,
`generate_check` that `check` accepts them with the generated rank, and, for `h : Valid xs`,
`generate_isFilteredAcyclicMatching` that they form a filtered acyclic matching for
`gradeFilter xs h`. The result depends on the list order of `xs`. No maximality, optimality,
completeness of `candidateRank` (that it finds a rank whenever the extended list is acyclic,
so that every rejected candidate reuses a face or closes a cycle), invariance under reordering
or runtime bound is claimed.
`TDA.Persistence.Morse.FiniteInputMatchingGenerationExamples` (imported by
`TDA.Persistence.Examples`) evaluates the pass on the checker inputs; see
[generating a matching greedily](math/discrete-morse-matchings.md#generating-a-matching-greedily).

## Unit cancellation of filtered based complexes

`TDA.Persistence.Morse.UnitCancellation` (imported by `TDA.Persistence`, namespace
`TDA.Persistence.Morse.Cancellation`) cancels one unit pair of a finite based complex. The
carrier is a finite type `ι` with `D : Matrix ι ι k` over a commutative ring `k`, in the column
convention of `FiniteInput.boundary`: `D r c` is the coefficient of `r` in `d c`, and matrix
product is composition. `Cancellation.IsBasedDifferential degree D` asks for `D * D = 0` and
`D r c ≠ 0 → degree c = degree r + 1`; `Cancellation.IsFilteredDifferential degree grade D`
adds `GradeNonincreasing grade grade D` (`D r c ≠ 0 → grade r ≤ grade c`) for an integer grade.
No basis order, triangularity or free-face condition is assumed. `isFilteredDifferential_boundary`
proves that the boundary of every valid `FiniteInput` is a filtered differential for
`FiniteInput.degree` and the list grades.

`IsUnitPair D a b` is a structure with fields `ne : a ≠ b` and `coeff : D a b = 1`. The
survivors `PairSurvivor a b` are the subtype of generators other than `a` and `b`, with their
original IDs. `reducedDifferential D a b`, `projection D a b`, `inclusion D a b` and
`homotopy a b` (`H a = b`, zero elsewhere) are computable entry formulas, for instance
`reducedDifferential D a b r s = D r s - D r b * D a s`;
`reducedDifferential_eq`, `projection_eq` and `inclusion_eq` identify them with
`Q (D - D H D) J`, `Q (1 - D H)` and `(1 - H D) J` for every `D`. Under `D * D = 0` and
`IsUnitPair D a b`, the five contraction identities are `reducedDifferential_sq_zero`
(`d' d' = 0`), `projection_mul` (`p D = d' p`), `mul_inclusion` (`D i = i d'`),
`projection_mul_inclusion` (`p i = 1`, which needs only `a ≠ b`) and
`one_sub_inclusion_mul_projection` (`1 - i p = D H + H D`). `homotopy_mul_homotopy`,
`projection_mul_homotopy` and `homotopy_mul_inclusion` give `H H = 0`, `p H = 0` and `H i = 0`
from `a ≠ b` alone.

For a based differential and a unit pair, the degree theorems relate the degrees on the
supports of the four maps, and `isBasedDifferential_reduced` makes `d'` a based differential
for the inherited degree. If `D` is grade-nonincreasing and `grade a = grade b`, then `d'`,
`p`, `i` and `H` are grade-nonincreasing (`reducedDifferential_gradeNonincreasing`,
`projection_gradeNonincreasing`, `inclusion_gradeNonincreasing`,
`homotopy_gradeNonincreasing`), and
`GradeNonincreasing.mulVec_sublevelSupported` shows that such matrices preserve vectors
supported in grades `≤ t`. `isFilteredDifferential_reduced` proves that `d'` is a filtered
differential for a filtered differential, a unit pair and equal grades.
`TDA.Persistence.Morse.UnitCancellationExamples` (imported by `TDA.Persistence.Examples`)
evaluates the filled triangle, a pure unit pair, an unequal-grade pair with no
grade-nonincreasing contracting homotopy, and a tie-order example over `ZMod 2`. These modules
provide no iteration, homology or persistence isomorphism, chosen ordering of survivors to
`Fin`, rescaling by a general unit or runtime bound; see
[unit cancellation of a filtered chain complex](math/discrete-morse-cancellation.md).

## Filtered contractions of based complexes

`TDA.Persistence.Morse.FilteredContraction` (imported by `TDA.Persistence`, namespace
`TDA.Persistence.Morse.Cancellation`) bundles a contraction of based complexes as data.
`FilteredContraction degree grade D degree' grade' D'` takes finite carriers `ι` and `κ` with
decidable equality, a commutative ring `k`, the large complex `(degree, grade, D)` on `ι` and
the small complex `(degree', grade', D')` on `κ`, all as parameters. Its data are
`proj : Matrix κ ι k`, `incl : Matrix ι κ k` and `htpy : Matrix ι ι k`; its fields are the
chain-map equations `proj * D = D' * proj` and `D * incl = incl * D'`, `proj * incl = 1`,
`1 - incl * proj = D * htpy + htpy * D`, the side conditions `htpy * htpy = 0`,
`proj * htpy = 0` and `htpy * incl = 0`, degree support (`proj` and `incl` preserve degree and
`htpy` raises it by one on their supports) and `GradeNonincreasing` for all three matrices.
`D * D = 0` is not a field.

`FilteredContraction.refl` is the identity contraction. `c₁.trans c₂` composes in
diagrammatic order, with projection `c₂.proj * c₁.proj`, inclusion `c₁.incl * c₂.incl` and
homotopy `c₁.htpy + c₁.incl * c₂.htpy * c₁.proj`. `c.reindex e` transports the small complex
along `e : κ ≃ μ` by `submatrix`, and `c.copy hdeg hgr hD` keeps the matrices while rewriting
the small complex's degree, grade and differential along equalities. `ofUnitPair hD hp hg`
packages the cancellation of an equal-grade unit pair of a filtered differential as a
contraction onto `(degree ∘ Subtype.val, grade ∘ Subtype.val, reducedDifferential D a b)`.
Each construction has `@[simp]` `rfl` lemmas for its three matrices. `differential_eq` proves
`D' = proj * D * incl`; `sq_zero_target` derives `D' * D' = 0` from `D * D = 0`; and
`isBasedDifferential_target` and `isFilteredDifferential_target` transfer the based and
filtered differential properties to `D'`. `proj_mulVec_incl_mulVec` and
`sub_incl_mulVec_proj_mulVec` are the vector forms `proj (incl y) = y` and
`x - incl (proj x) = D (htpy x) + htpy (D x)`. `GradeNonincreasing.add` closes grade bounds
under sums. `TDA.Persistence.Morse.FilteredContractionExamples` (imported by
`TDA.Persistence.Examples`) composes two cancellations on the filled triangle and transports
the result to a flat subtype of critical cells, over `ZMod 2`. This module provides no
iteration, homology or persistence isomorphism; homology and the isomorphism induced by a
contraction are in
[sublevel homology of filtered based complexes](#sublevel-homology-of-filtered-based-complexes).
See
[filtered contractions and their composition](math/discrete-morse-cancellation.md#filtered-contractions-and-their-composition).

## Iterated cancellation along pivot schedules

`TDA.Persistence.Morse.IteratedCancellation` (imported by `TDA.Persistence`, namespace
`TDA.Persistence.Morse.Cancellation`) cancels a supplied list of unit pairs head first and
composes the single cancellations into one filtered contraction onto the generators that are
not cancelled. A schedule is a list `l : List (ι × ι)` of (lower, upper) pairs, and
`scheduleEndpoints l` lists its `2·|l|` endpoints in order. `IsPivotSchedule grade D l` asks
that the endpoints are distinct, that every pair `(a, b)` has `D a b = 1` and
`grade a = grade b`, and that `l.Pairwise fun p q => D p.1 q.2 = 0`: the lower generator of a
pair is never a face of the upper generator of a later pair. The instance
`IsPivotSchedule.decidable` decides it when equality of generators and of coefficients is
decidable, and `isPivotSchedule_iff_get` gives the indexed form: `D (a i) (b j) ≠ 0` with
`i ≠ j` forces `j < i`, so the matched block is unit lower triangular in schedule order.

`cancelStep D a b r s = D r s - D r b * D a s` is the entry formula of
`reducedDifferential D a b` on all of `ι`, and `scheduleMatrix l D` applies it along `l`,
head first. `cancelStep_apply_of_eq_zero` leaves every column `s` with `D a s = 0` unchanged,
and `IsPivotSchedule.cancelStep_apply_snd` applies this to the upper generators of the tail of
a pivot schedule. `IsPivotSchedule.cancelStep` proves that the tail is a pivot schedule for
`cancelStep D p.1 p.2`, `IsPivotSchedule.head_not_mem` that the two generators of the head
pair are distinct and are not endpoints of the tail, and `IsPivotSchedule.isUnitPair_reducedDifferential`
that every later pair is an `IsUnitPair` of `reducedDifferential D a b`.

`scheduleSurvivors l S` removes the endpoints from a Finset pair by pair
(`mem_scheduleSurvivors`), `criticalSet l = scheduleSurvivors l Finset.univ` consists of the
generators that are not endpoints (`mem_criticalSet`), and `Critical l` is the subtype of
original generators in `criticalSet l`, with
`Fintype.card (Critical l) = Fintype.card ι - 2 * l.length` for distinct endpoints
(`card_critical`). `criticalDifferential D l` is `scheduleMatrix l D` restricted to
`Critical l`; it takes no hypothesis.

For `hD : IsFilteredDifferential degree grade D` and `hl : IsPivotSchedule grade D l`,
`FilteredContraction.ofSchedule hD hl` is a `FilteredContraction` of `(degree, grade, D)` onto
`(degree ∘ Subtype.val, grade ∘ Subtype.val, criticalDifferential D l)` on `Critical l`. It is
`FilteredContraction.toUniv`, which restates the complex on `{x // x ∈ Finset.univ}`, followed
by `FilteredContraction.ofScheduleOn`, which composes with `trans` the steps
`FilteredContraction.cancelOn`: `ofUnitPair` on a Finset-indexed carrier, transported by
`reindex` along the concrete `FilteredContraction.survivorEquiv` and restated by `copy`.
`criticalDifferential_eq` proves `criticalDifferential D l = proj * D * incl`,
`isFilteredDifferential_criticalDifferential` that `criticalDifferential D l` is a filtered
differential for the inherited degree and grade, and `ofSchedule_congr` that the three
matrices depend on `D` only through its value. All data are computable.
`TDA.Persistence.Morse.IteratedCancellationExamples` (imported by `TDA.Persistence.Examples`)
evaluates the schedule contraction of the multi-grade square of
`TDA.Persistence.Morse.FiniteInputMatchingExamples` and of the regraded filled triangle, and
records that no order of the cyclic pairs on the hollow triangle is a pivot schedule, over
`ZMod 2` by `decide +kernel`. This module provides no derivation of a schedule from a
matching, no explicit path formula for the matrices, no order independence and no homology
statement for `ofSchedule`; see
[iterated cancellation along a pivot schedule](math/discrete-morse-cancellation.md#iterated-cancellation-along-a-pivot-schedule).
A schedule derived from a certified matching is in
[pivot schedules of certified matchings](#pivot-schedules-of-certified-matchings).

## Sublevel homology of filtered based complexes

`TDA.Persistence.Morse.FilteredHomology` (imported by `TDA.Persistence`, namespace
`TDA.Persistence.Morse.Cancellation`) forms the homology of the grade sublevels of a based
complex `(degree, grade, D)` on a finite carrier `ι : Type u` over a commutative ring
`k : Type v`, with `degree : ι → ℕ` and `grade : ι → ℤ`. `DegreeSupported degree p x` says that
`x` vanishes outside degree `p`. `sublevelChains degree grade p t` is the submodule of vectors
with `DegreeSupported degree p x` and `SublevelSupported grade t x`, `sublevelCycles` adds
`D.mulVec x = 0`, `sublevelBoundaries` is the image under `D` of the degree-`p + 1` sublevel
chains, and `sublevelHomology degree grade D p t` is the quotient of the cycles by the
boundaries that lie among them. The definitions take no hypothesis on `D`;
`sublevelBoundaries_le_sublevelCycles` proves that every sublevel boundary is a sublevel cycle
when `IsFilteredDifferential degree grade D` holds. `sublevelHomologyMap` is induced by the
inclusion of cycles for `t ≤ t'`, and `sublevelHomologyPModule degree grade D p` is the
persistence module `PModule.{v, 0, max u v} k ℤ` with these structure maps.

For `c : FilteredContraction degree grade D degree' grade' D'` with carriers `ι κ : Type u`,
`c.homologyProj p t` and `c.homologyIncl p t` are induced by `proj` and `incl`.
`c.sublevelHomologyEquiv p t` is a `LinearEquiv` with forward map `homologyProj` and inverse
`homologyIncl`, and `c.sublevelHomologyIso p` is the natural isomorphism
`sublevelHomologyPModule degree grade D p ≅ sublevelHomologyPModule degree' grade' D' p` from
the large complex to the small one, whose `hom` components are `homologyProj`
(`sublevelHomologyIso_hom_app`). `c.finrank_sublevelHomology_eq p t` equates the
`Module.finrank` of the two sublevel homologies. None of these results about `c` assumes
`D * D = 0`. The maps, the persistence module and the isomorphisms are `noncomputable`.
`TDA.Persistence.Morse.FilteredHomologyExamples` (imported by `TDA.Persistence.Examples`)
computes the sublevel homology dimensions of the critical complex of the filled triangle with
the grade `cGrade` over `ZMod 2`, and transports them to the triangle through the contraction.
These modules provide no bridge from `sublevelHomologyPModule` to `sublevelModule` or
`simplicialHomologyPModule`; see
[sublevel homology and the induced isomorphism](math/discrete-morse-cancellation.md#sublevel-homology-and-the-induced-isomorphism).
For the boundary complex of a valid `FiniteInput`, the bridge is in
[the simplicial bridge and the Morse persistence theorem](#the-simplicial-bridge-and-the-morse-persistence-theorem).

## Pivot schedules of certified matchings

`TDA.Persistence.Morse.MatchingSchedule` (imported by `TDA.Persistence`, namespace
`TDA.Persistence.Morse.MatchingInput`) connects a certified matching `c : CertifiedMatching xs`
on a finite integer-graded input to
[iterated cancellation along pivot schedules](#iterated-cancellation-along-pivot-schedules).
Over `ZMod 2`,
`coverIncidence xs i j` is `1` exactly when `IsCover xs i j` holds and the face at position
`i` is nonempty; `boundary_eq_coverIncidence` proves `FiniteInput.boundary xs = coverIncidence xs`
for every input. `isCover_of_boundary_ne_zero` shows that a nonzero boundary entry is a cover,
and, on a valid input, `boundary_eq_one_of_isCover` gives every cover the coefficient `1` and
`boundary_ne_zero_iff` identifies the nonzero entries with the covers.

`CertifiedMatching.schedule` is `c.pairs.insertionSort fun p q => c.rank p.1 ≤ c.rank q.1`,
the certified pairs sorted stably by non-decreasing rank of the lower face. `schedule_perm`
proves that it is a permutation of `c.pairs`, `schedule_pairwise_rank_le` that it is sorted,
and `scheduleEndpoints_perm` that its endpoints are those of `c.pairs`, reordered.
`rank_lt_of_boundary_ne_zero` proves `c.rank q.1 < c.rank p.1` for certified pairs `p ≠ q`
with `FiniteInput.boundary xs p.1 q.2 ≠ 0`, through the arrows `q.1 → q.2 → p.1`, and
`isPivotSchedule_schedule` that, for `h : Valid xs`, `c.schedule` is an `IsPivotSchedule` for
`FiniteInput.boundary xs` with the list grade `fun i => (xs.get i).2`.

`mem_criticalSet_schedule` identifies `criticalSet c.schedule` with the critical positions
`c.critical`, and `card_critical_schedule` counts `Critical c.schedule` as
`c.critical.length`. `CertifiedMatching.morseDifferential` is
`criticalDifferential (FiniteInput.boundary xs) c.schedule`; it takes no validity hypothesis
and is computable. For `h : Valid xs`, `CertifiedMatching.morseContraction` is
`FilteredContraction.ofSchedule` of the boundary complex `(degree xs, list grade, boundary)`
onto `(degree xs ∘ Subtype.val, list grade ∘ Subtype.val, morseDifferential)`,
`isFilteredDifferential_morseDifferential` proves that the Morse differential is a filtered
differential for these inherited degrees and grades, and `CertifiedMatching.morseHomologyIso`
is the `noncomputable` isomorphism `sublevelHomologyIso` of the contraction in each degree `p`.
`TDA.Persistence.Morse.MatchingScheduleExamples` (imported by `TDA.Persistence.Examples`)
evaluates the schedules, critical positions and Morse differentials of three certificates on
the multi-grade square, including a tie in the rank, by `decide +kernel`; each such `decide`
on a goal that mentions `FiniteInput.boundary` runs after rewriting with
`boundary_eq_coverIncidence`. This module provides no bridge from
`sublevelHomologyPModule` to `sublevelModule` or `simplicialHomologyPModule`, no main theorem
of #1041, no gradient-path formula for `morseDifferential`, no independence of it from the
rank or the tie order, no reducer adapter, ordering of the critical generators or `Equiv` to
`Fin`, and no homology computation by evaluation; see
[the pivot schedule of a certified matching](math/discrete-morse-cancellation.md#the-pivot-schedule-of-a-certified-matching).
The bridge and the main theorem of #1041 are in
[the simplicial bridge and the Morse persistence theorem](#the-simplicial-bridge-and-the-morse-persistence-theorem).
An order of the critical generators in which the Morse differential satisfies the input
conditions of the column reducer is in
[the reducer order of filtered based complexes](#the-reducer-order-of-filtered-based-complexes).

## The simplicial bridge and the Morse persistence theorem

`TDA.Persistence.Morse.SimplicialBridge` (imported by `TDA.Persistence`) works over `ZMod 2`
on a finite input `xs` with `h : Valid xs`. In namespace
`TDA.Persistence.Morse.SimplicialBridge`, `sublevelSupported_iff_prefixSupported` identifies
grade-sublevel support with support before `sublevelStage xs a`; it and the reducer version in
`ReducerDiagram` are instances of `Cancellation.sublevelSupported_iff_prefixSupported_of_iff`,
which needs only that the grades `≤ a` are the indices before the prefix length.
`cycleInput_iff_mem_sublevelCycles` identifies `FiniteInput.CycleInput` with the sublevel cycles
of the boundary complex `(degree xs, fun i => (xs.get i).2, FiniteInput.boundary xs)`.
`boundaryCycleCoordinates` is the computable restriction of `rawCycleCoordinates` to these
cycles; `boundaryCycleCoordinates_eq_zero_iff` and `ker_boundaryCycleCoordinates` identify its
kernel with the sublevel boundaries among the cycles, and `boundaryCycleCoordinates_surjective`
proves it surjective. The `noncomputable` `boundaryHomologyEquiv h p a` is a `LinearEquiv` from
`sublevelHomology` of the boundary complex to
`simplicialHomology ((gradeFilter xs h).sublevel a) (ZMod 2) p`; `boundaryHomologyEquiv_mk`
sends the class of a sublevel cycle to its `vectorSublevelClass`, and
`boundaryHomologyEquiv_naturality` gives naturality in the grade. `boundaryHomologyIso h p` is
the natural isomorphism
`sublevelHomologyPModule (degree xs) (fun i => (xs.get i).2) (FiniteInput.boundary xs) p ≅ sublevelModule (ZMod 2) (gradeFilter xs h) p`,
with components `boundaryHomologyIso_hom_app` and `boundaryHomologyIso_inv_app`, and
`finrank_sublevelHomology_boundary` equates dimensions.

In namespace `TDA.Persistence.Morse.MatchingInput.CertifiedMatching`, for
`c : CertifiedMatching xs`, `c.morseSublevelModuleIso h p` is
`(boundaryHomologyIso h p).symm ≪≫ c.morseHomologyIso h p`, a natural isomorphism from
`sublevelModule (ZMod 2) (gradeFilter xs h) p` to the grade-sublevel homology persistence
module of `c.morseDifferential` on the critical generators. This differential is
`scheduleMatrix c.schedule (FiniteInput.boundary xs)` restricted to the critical generators:
the iterated Schur complement of the boundary matrix at the unit entries of the schedule,
one `cancelStep` per pair. `morseSublevelModuleIso_hom_app`
and `morseSublevelModuleIso_inv_app` identify its components,
`morseSublevelModuleIso_hom_vectorSublevelClass` sends the class of a sublevel cycle vector `v`
to the class of `proj v`, and `finrank_simplicialHomology_eq` and
`rankOfStructureMap_sublevelModule_eq` equate dimensions and structure-map ranks. The bridge
and the isomorphisms are `noncomputable`.

`TDA.Persistence.Morse.SimplicialBridgeExamples` (imported by `TDA.Persistence.Examples`) has
fixtures M1–M7 on the multi-grade square. M1 evaluates the critical generators A, AD, ACD of
`sqCert` and its Morse differential `d ACD = AD` by `decide +kernel`; M2 proves the Morse
sublevel homology dimensions, and M3 transports them to the simplicial sublevel complexes
through `finrank_simplicialHomology_eq`; M4 proves the rank invariants of `[1,2)` in degree 1
and `[0,∞)` in degree 0; M5 shows that the loop AB + BC + CD + AD has a nonzero class at grade
1 that is filled at grade 2; M6 reads off the Morse complex of `genCert` through the main
theorem; and M7 proves that the square's diagram `dgm` is `{(1, 2)}` in degree 1 and
`{(0, ⊤)}` in degree 0, by `rank_sublevelHomologyMap`, not from the reducer. These modules
provide no interval decomposition over `ℤ`, no barcode statement other than M7, no agreement
with the reducer's barcode (it is in
[the reducer run on the Morse complex of a certificate](#the-reducer-run-on-the-morse-complex-of-a-certificate)),
no chain-level isomorphism with `simplicialChainComplex`,
no independence of the Morse complex from the certificate, no gradient-path formula and no
coefficient ring other than `ZMod 2`; see
[the simplicial bridge and the Morse persistence theorem](math/discrete-morse-cancellation.md#the-simplicial-bridge-and-the-morse-persistence-theorem).

## The reducer order of filtered based complexes

`TDA.Persistence.Morse.ReducerOrder` (imported by `TDA.Persistence`) orders the generators of
a filtered based complex `(ι, degree, grade, D)` whose finite carrier has a `LinearOrder`, for
the column reducer of `TDA.Persistence.Reduction`. `key degree grade x` is
`toLex (grade x, toLex (degree x, x))`; `key_injective` and `key_lt` hold, and
`key_lt_of_ne_zero` gives `key r < key c` for a nonzero entry `D r c` of a filtered
differential. `sortList` is `List.insertionSort` by `key`, with `sortList_perm`,
`pairwise_sortList_le`, `pairwise_sortList` and `sortList_eq_of_perm`. `sortedGenerators` sorts
`Finset.univ` through `Quotient.liftOn`; `sortedGenerators_eq` equates it with `sortList` of
any duplicate-free complete enumeration, and `mem_sortedGenerators`,
`pairwise_sortedGenerators`, `nodup_sortedGenerators` and `length_sortedGenerators` follow.
`reducerEquiv : Fin (sortedGenerators degree grade).length ≃ ι` is
`List.Nodup.getEquivOfForallMemList` of the sorted list (`reducerEquiv_apply`), with
`key_strictMono`, `lt_iff_key_lt` and `monotone_grade`.

`reducerMatrix degree grade D` is `D.submatrix (reducerEquiv …) (reducerEquiv …)`. For a
filtered differential, `reducerMatrix_sq_zero` and `isFilteredDifferential_reducerMatrix` hold
over a commutative ring; over a field, `strictBoundary_submatrix` (for any `e : Fin m ≃ ι`
along which `key` is strictly increasing), `strictBoundary_reducerMatrix` and
`lowersDegree_reducerMatrix` give the reducer's input conditions, and
`reducerMatrix_normalForm_input` is the existing `matrixReductionTrace_normalForm_input`
applied to the reducer matrix. `reducerContraction` is the identity filtered contraction
reindexed along the reducer order (`reducerContraction_proj`, `reducerContraction_incl`,
`reducerContraction_htpy`), and `reducerHomologyIso` (for `ι : Type`) is its
`sublevelHomologyIso`. `key`, `sortList`, `sortedGenerators`, `reducerEquiv`, `reducerMatrix`
and `reducerContraction` are computable; `reducerHomologyIso` is `noncomputable`.

`TDA.Persistence.Morse.ReducerOrderExamples` (imported by `TDA.Persistence.Examples`) has
fixtures R1–R3 over `ZMod 2`: R1, the survivors of the tie-order cancellation F4, on which the
reduced differential is not strictly upper triangular in the inherited order and the reducer
order is `r, s`; R2, a path
with a certified matching whose Morse differential `d AB = A + C` fails strict triangularity in
the inherited order A, AB, C and has reducer order A, C, AB; and R3, the reducer orders of the
certificates `sqCert` and `genCert` on the multi-grade square. The sorts and the reordered
matrices are evaluated by `decide +kernel`. These modules run no reduction and state no barcode
or diagram agreement with the reducer; see
[the reducer order of a filtered based complex](math/discrete-morse-cancellation.md#the-reducer-order-of-a-filtered-based-complex).
The reducer output on that order and its rank semantics are in
[the graded reducer output of filtered based complexes](#the-graded-reducer-output-of-filtered-based-complexes).

## The graded reducer output of filtered based complexes

`TDA.Persistence.DiagramRankUniqueness` (imported by `TDA.Persistence`) proves, over any
`LinearOrder α`, that two finite multisets of positive points in `α × WithTop α` with equal
slice counts are equal (`multiset_eq_of_sliceCounts_eq`), and the same for positive diagrams
(`Diagram.eq_of_sliceCounts_eq`). The slice count at `a ≤ b` counts the points `(b', d)` with
`b' ≤ a` and `b < d`, the predicate of `rank_sublevelHomologyMap`.

`TDA.Persistence.Morse.ReducerDiagram` (imported by `TDA.Persistence`) reads the output of the
column reducer of `TDA.Persistence.Reduction` on `D : Matrix (Fin m) (Fin m) k` over a field
with decidable equality, with `degree : Fin m → ℕ` and `grade : Fin m → ℤ`. `reduced` is
`replay D (matrixReductionTrace D)`; `pivotPairs` and `essentialIndices` list its pivot pairs
and essential indices (`mem_pivotPairs`, `mem_essentialIndices`); `pairOccurrence` gives
`none` for an equal-grade pair; `occurrences` lists `FiniteInput.Occurrence`s and
`diagram … p : Diagram ℤ` collects the degree-`p` points. On `FiniteInput.boundary xs` they
are `FiniteInput.occurrences` and `FiniteInput.outputDiagram` by `rfl` (`occurrences_boundary`,
`diagram_boundary`). The instances `decidableStrictBoundary` and `decidableLowersDegree` decide
the reducer's input conditions entrywise.

`stage grade a` counts the indices of grade `≤ a` (`stage_le`, `stage_mono`); for monotone
grades, `grade_le_iff_lt_stage`, `sublevelSupported_iff_prefixSupported`,
`sublevelCycles_eq_originalCycleSpace` and `mem_sublevelBoundaries_iff_originalBoundary`
identify grade sublevels with the reducer's prefixes. `prefixHomologyEquiv` identifies
`sublevelHomology … a` with the reducer's `originalHomology` at `stage grade a`
(`prefixHomologyEquiv_mk`, `prefixHomologyEquiv_naturality`,
`finrank_range_sublevelHomologyMap_eq`). For monotone grades, `countP_diagram` equates the slice
count of `diagram` with the right side of `matrixReductionTrace_originalHomologyMap_rank_formula`
at the stages. Under `D * D = 0`, `StrictBoundary D`, `LowersDegree degree D` and
`Monotone grade`, `rankOfStructureMap_eq_countP` states that the rank of the structure map
`a ≤ b` of `sublevelHomologyPModule degree grade D p` is that slice count,
`diagram_isPositive` holds, and `eq_diagram_of_rankCounts` states that `diagram` is the only
positive diagram with these slice counts.

For a finite linearly ordered carrier `ι : Type`, `reducerOccurrences` and `reducerDiagram` are
the output on `reducerMatrix` with the transported degree and grade. For a filtered
differential over a field, `rankOfStructureMap_eq_countP_reducerDiagram` gives the ranks of the
original complex's `sublevelHomologyPModule` as slice counts of `reducerDiagram`, through
`reducerHomologyIso`; `reducerDiagram_isPositive` and `eq_reducerDiagram_of_rankCounts`
follow. The builders, `stage`, `reducerOccurrences`, `reducerDiagram` and the two instances are
computable; `prefixHomologyEquiv` is `noncomputable`.

`TDA.Persistence.Morse.ReducerDiagramExamples` (imported by `TDA.Persistence.Examples`) has
fixtures P1–P3 over `ZMod 2` on written-out matrices: P1, a hollow triangle with staggered
edge grades, with its pivot pairs, essential indices, occurrences, diagrams and four ranks; P2,
the reducer matrix of the path R2, whose only pivot pair has equal grades and is dropped; and
P3, the reducer matrix of the square R3, with degree-1 diagram `{(1, 2)}` and two ranks.
These modules run no reducer on the Morse complex of a certificate and state no agreement with
`dgm`; see
[the graded reducer output and its rank semantics](math/discrete-morse-cancellation.md#the-graded-reducer-output-and-its-rank-semantics).
That run and its agreement with `dgm` are in
[the reducer run on the Morse complex of a certificate](#the-reducer-run-on-the-morse-complex-of-a-certificate).

## The reducer run on the Morse complex of a certificate

`TDA.Persistence.Morse.MorseDiagram` (imported by `TDA.Persistence`) runs the reducer output on
the Morse complex of a certified matching. In namespace
`TDA.Persistence.Morse.MatchingInput.CertifiedMatching`, for a finite input `xs` and
`c : CertifiedMatching xs`, `c.morseOccurrences : List FiniteInput.Occurrence` and
`c.morseDiagram p : Diagram ℤ` are `reducerOccurrences` and `reducerDiagram` of
`c.morseDifferential`, with the degrees and list grades inherited by the critical positions;
they take no validity hypothesis and are computable. On a valid input (`h : Valid xs`), over
`ZMod 2`, `rankOfStructureMap_sublevelModule_eq_countP` states that the ranks of
`sublevelModule (ZMod 2) (gradeFilter xs h) p` are the slice counts of `c.morseDiagram p`,
`morseDiagram_isPositive` holds, `morseDiagram_eq_dgm` states
`c.morseDiagram p = dgm (ZMod 2) (gradeFilter xs h) p` under `letI := faceFintype xs h`,
`morseDiagram_eq_outputDiagram` states `c.morseDiagram p = FiniteInput.outputDiagram xs p`,
the diagram of the ordinary run on the boundary matrix, and `morseDiagram_eq_morseDiagram`
states that two certified matchings give the same diagrams. `morseOccurrences_perm` and
`morseOccurrences_perm_of_run_eq_some` state that `c.morseOccurrences` is a permutation of
`FiniteInput.occurrences xs` and of the `L` in `FiniteInput.run xs = some L`.

In namespace `TDA.Persistence.Morse.ReducerDiagram`, `perm_of_degreePoints_eq` states that
occurrence lists with the same degree-`p` points in every degree `p` are permutations of each
other. For `ι : Type` with `[Fintype ι]`, two linear orders `o` and `o'` of `ι` and a filtered
differential over a field, `reducerDiagram_eq_of_linearOrder` states that `reducerDiagram` is
the same for `o` and `o'`, and `reducerOccurrences_perm_of_linearOrder` that the two occurrence
lists are permutations of each other: the reducer output is independent of the tie order of the
reducer order, the lists up to permutation.

`TDA.Persistence.Morse.MorseDiagramExamples` (imported by `TDA.Persistence.Examples`) has
fixtures Q1–Q6 over `ZMod 2`: Q1 and Q2, the Morse runs of `sqCert` and `genCert` on the
multi-grade square, with occurrences `[⟨1, 1, .finite 2⟩, ⟨0, 0, .essential⟩]`, degree-1 diagram
`{(1, 2)}` and degree-0 diagram `{(0, ⊤)}`; Q3, the ordinary run `FiniteInput.run square`, equal
to `some` of both Morse runs, and the square's `dgm` read off Q1 through `morseDiagram_eq_dgm`;
Q4, the path R2 with `pathCert`, whose Morse run is `[⟨0, 0, .essential⟩]` and whose ordinary
run `FiniteInput.run path` is `some` of it; Q5, the reducer runs on the tie-order complex F4
and its cancellation, both empty; and Q6, the path in the reversed order `dualOrder` of its
critical positions, with another essential generator and the same occurrence list. `morseOccurrences` and `morseDiagram` are computable;
the fixtures evaluate them by `decide +kernel` after rewriting the Morse differential to its
written-out form, and evaluate the ordinary run only after rewriting the boundary matrix with
`boundary_eq_coverIncidence`. These modules provide no interval decomposition over `ℤ`, no
list-order independence of `reducerOccurrences` or `morseOccurrences` from the tie order or the
certificate, no lifting of representatives to the input and no runtime claim; see
[the reducer run on the Morse complex of a certificate](math/discrete-morse-cancellation.md#the-reducer-run-on-the-morse-complex-of-a-certificate).

## Elementary collapses and a Čech-to-α collapse

`TDA.Simplicial.Collapse` (imported by `TDA.Simplicial`) defines, in namespace
`TDA.Simplicial`, for `K : PreAbstractSimplicialComplex V` and `σ τ : Finset V`, the predicate
`IsFreePair K σ τ` (both faces in `K`, `σ ⋖ τ`, and `τ` the only face of `K` strictly containing
`σ`) and the subcomplex `deletion K σ` of the faces of `K` not containing `σ` (`mem_deletion`,
`deletion_le`). `IsFreePair.mem_deletion_iff` states that on a free pair the deletion removes
exactly `σ` and `τ`. `ElementaryCollapsesTo K L` states that `L` is the deletion of the free face
of a free pair of `K`; `IsFreePair.elementaryCollapsesTo` gives it from a free pair, and
`ElementaryCollapsesTo.lt` states `L < K`. `CollapsesTo` is its reflexive transitive closure, a
finite, possibly empty, sequence of elementary collapses, and `CollapsesTo.le` states `L ≤ K`.
This module makes no homotopy or homology statement; the homology isomorphism of a collapse is
in `TDA.Simplicial.CollapseHomology`.

`TDA.Filtration.AlphaCollapseExamples` (imported by `TDA.Filtration.Examples`) works on
`RationalAlpha.Examples.obtuse`, the sites `(0,0)`, `(4,0)` and `(1,1)` with labels `0, 1, 2`,
and on the two stages `Alpha.squaredCechFiltration (realSites obtuse) t` and
`Alpha.labelledComplexFiltration (realSites obtuse) t` under the same labels, for `t : ℝ` a
squared grade, written `cech t` and `alpha t` below (local notation in the module).
`cechGrades` is the squared Čech grade table: the vertices 0, `{0,2}` 1/2, `{1,2}` 5/2,
`{0,1}` and `{0,1,2}` 4. `mem_cech_iff` states that a face is in the Čech stage
exactly when its grade in `cechGrades` is at most `t`, and `mem_alpha_iff` reads the α stage off
`gradedFaces obtuse`, where `{0,1}` and `{0,1,2}` have grade 5. `cechGrades_sdiff` states that
the two tables differ exactly in `({0,1}, 4)`, `({0,1,2}, 4)` against `({0,1}, 5)`,
`({0,1,2}, 5)`. For `4 ≤ t`, `isFreePair_long_edge` states that `({0,1}, {0,1,2})` is a free
pair of the Čech stage. For `t < 5`, `mem_alpha_iff_of_lt_five` states that the α stage is the
Čech stage without `{0,1}` and `{0,1,2}`, and `alpha_eq_deletion` that it is
`deletion (cech t) {0,1}`; `alpha_eq_deletion_iff` states that this equality holds exactly for
`t < 5`. `alpha_eq_cech` states that the two stages are equal for `t < 4 ∨ 5 ≤ t`, including the
empty stages below 0, and `alpha_eq_cech_iff` that they are equal exactly then.
`elementaryCollapsesTo_iff` states that the Čech stage collapses to the α stage in one
elementary collapse exactly for `4 ≤ t ∧ t < 5`, and `collapsesTo` that it collapses to the α
stage at every `t`, by the empty sequence outside `[4, 5)`. `not_exists_fixed_faces` states that
no fixed set `C` of faces has `s ∈ alpha t ↔ s ∈ cech t ∧ s ∈ C` for all `t` and `s`. The
labelled inclusion of the α stage into the Čech stage is the existing
`Alpha.labelledComplexFiltration_le_squaredCech`.

`TDA.Simplicial.CollapseHomology` (imported by `TDA.Simplicial`) has, in the same namespace,
`IsFreePair.card_upper` (`τ.card = σ.card + 1`), the retraction chain map
`IsFreePair.collapseRetraction R hp` onto the chain complex of `deletion K σ` with
`IsFreePair.simplicialChainIncl_comp_collapseRetraction` (inclusion, then retraction, is the
identity), and the chain homotopy equivalence `IsFreePair.collapseHomotopyEquiv R hp`, whose
forward map is `simplicialChainIncl R (deletion_le K σ)` (`_hom`) and whose inverse is the
retraction (`_inv`). `IsFreePair.isIso_simplicialHomologyIncl`,
`ElementaryCollapsesTo.isIso_simplicialHomologyIncl` and
`CollapsesTo.isIso_simplicialHomologyIncl` state that the homology inclusion of a free-face
deletion, of an elementary collapse and of a finite collapse sequence is an isomorphism, in every
degree `n : ℕ` and over every ring `R` (`[Ring R]`, not necessarily commutative), for ordinary
unaugmented homology; the last two take any inclusion proof `hle : L ≤ K`.
`CollapsesTo.simplicialHomologyIso` is the isomorphism, with forward map
`simplicialHomologyIncl R h.le n` (`_hom`). `TDA.Persistence.CollapsePersistence` (imported by
`TDA.Persistence`) has, for simplicial filtrations `F G` over a preorder with
`hle : ∀ p, F p ≤ G p` and `h : ∀ p, CollapsesTo (G p) (F p)`,
`isIso_inclusionHom_of_collapsesTo` (`IsIso (inclusionHom R n hle)`) and
`collapseInclusionIso R n hle h`, whose forward map is `inclusionHom R n hle`
(`collapseInclusionIso_hom`). Naturality is that of the inclusions; no compatibility of the
retractions at different indices is used. `TDA.Persistence.CollapsePersistenceExamples`
(imported by `TDA.Persistence.Examples`) applies these on the obtuse triangle, in every degree
and over every ring: `isIso_deletion_long_edge` (deleting `{0,1}` from the Čech stage at grade
4), `isIso_alpha_cech_four` (the labelled inclusion at grade 4), `isIso_inclusionHom` (the
inclusion morphism over all real grades, negative grades included), and
`CollapsePersistenceExamples.alphaCechIso`, the
natural isomorphism from α persistence to squared-grade Čech persistence of the obtuse
triangle, with forward map the `inclusionHom` of the labelled inclusions
(`CollapsePersistenceExamples.alphaCechIso_hom`). It is a different declaration from the
general `TDA.Persistence.alphaCechIso`. Over a field `k`,
`CollapsePersistenceExamples.alphaCechIso_zero_hom` states
`(CollapsePersistenceExamples.alphaCechIso k 0).hom = alphaH0Comparison (realSites obtuse) k`.
See [homology of collapses](math/discrete-morse-matchings.md#homology-of-collapses).

`TDA.Simplicial.CollapseCertificate` (imported by `TDA.Simplicial`) has, in namespace
`TDA.Simplicial`, for `[DecidableEq V]`, face tables `F T : Finset (Finset V)` and certificates
`steps : List (Finset V × Finset V)`: `IsFreePairTable F σ τ` (`σ ∈ F`, `τ ∈ F`, `σ ⊆ τ`,
`(τ \ σ).card = 1`, and every `ω ∈ F` with `σ ⊂ ω` is `τ`) with the decidability instance
`instDecidableIsFreePairTable`; `collapseTable F σ τ`, which erases `σ` and `τ`;
`runSteps F steps : Option (Finset (Finset V))`, which applies the steps in order and is `none`
at the first step that is not free; and `checkSteps F steps T : Bool`, which accepts exactly when
the run ends at `T` itself (`checkSteps_eq_true_iff`, `eq_of_checkSteps`, `checkSteps_nil`,
`checkSteps_cons`). For complexes `K`, `L` with `∀ s, s ∈ K ↔ s ∈ F` and
`∀ s, s ∈ L ↔ s ∈ T`, `isFreePair_iff_isFreePairTable` identifies the table test with
`IsFreePair`, `mem_deletion_iff_mem_collapseTable` identifies `collapseTable` with the deletion
on a free pair, `collapsesTo_of_checkSteps` (soundness) gives `CollapsesTo K L` from an accepted
certificate, `exists_checkSteps_of_collapsesTo` (completeness) gives an accepted certificate from
`CollapsesTo K L`, and `collapsesTo_iff_exists_checkSteps` combines the two.
`FiniteComplex.collapsesTo_of_checkSteps` is soundness for `C D : FiniteComplex m`, with face
tables `C.faces` and `D.faces`. No check is made that `F` is the face set of a complex.
`TDA.Simplicial.CollapseCertificateExamples` (imported by `TDA.Simplicial.Examples`) has the
tables `triangle`, `alphaTable`, `tetrahedron`, `simplex4` and `twoTriangles` and fourteen
fixtures, each decided by `decide +kernel` except `top_collapsesTo_vertex`. Accepted:
`checkSteps_triangle_alphaTable` (the obtuse step, ending exactly at `alphaTable`),
`checkSteps_triangle_vertex`, `checkSteps_tetrahedron_vertex`, `checkSteps_simplex4_vertex` (to
the vertex `{0}`) and `checkSteps_triangle_spine` (onto an edge and onto the spine). Rejected,
each with a conjunct stating its reason: `checkSteps_twoTriangles_extra_coface` (an extra coface
`{0,1,3}`), `checkSteps_alphaTable_not_mem` (`{0,1,2} ∉ alphaTable`),
`checkSteps_triangle_reversed` (reversed pair), `checkSteps_triangle_codim_two` (not a cover),
`checkSteps_triangle_wrong_order` (`{1}` is not free while `{1,2}` is present),
`checkSteps_triangle_wrong_endpoint` (the run ends at `alphaTable`, which is none of three
targets) and `checkSteps_triangle_repeated` (the faces of the repeated step have been erased).
`checkSteps_triangle_nil` accepts the empty certificate to `triangle` and rejects it to
`alphaTable`. `top_collapsesTo_vertex` is soundness on the actual full tetrahedron `⊤`.
`TDA.Filtration.AlphaCollapseCertificateExamples` (imported by `TDA.Filtration.Examples`) has, at
grade 4 only, `mem_cech_four_iff` (the faces of `cech 4` are `triangle`), `mem_alpha_four_iff`
(the faces of `alpha 4` are `alphaTable`) and `collapsesTo_four`
(`CollapsesTo (cech 4) (alpha 4)` through the checker). See
[checking supplied collapse sequences](math/discrete-morse-matchings.md#checking-supplied-collapse-sequences).

`TDA.Filtration.CollapseCertificateFamily` (imported by `TDA.Filtration`) works in namespace
`TDA.Filtration` with real-indexed filtrations `F G : SimplicialFiltration ℝ V` and rational
grade tables `g : Finset (Finset V × ℚ)`. `HasGradeTable K g` is
`∀ s t, s ∈ K t ↔ ∃ q, (s, q) ∈ g ∧ (q : ℝ) ≤ t`, so grades are closed. `stageTable g c` is the
face table of the rows of grade at most `c` (`mem_stageTable`), and at a rational grade it is the
face table of the stage (`HasGradeTable.mem_cast_iff`). `criticalGrades gF gG : Finset ℚ` is the
set of all grades of both tables (`mem_criticalGrades`). The regime lemmas are
`HasGradeTable.notMem_of_lt` and `HasGradeTable.mem_iff_mem_stageTable` for one table, and
`stages_of_lt_criticalGrades` (below the least critical grade both stages are empty),
`stages_eq_stageTable` (if `c ≤ t` and no critical grade lies in `(c, t]`, the stages at `t`
have the stage tables at `c`), its cases `stages_eq_stageTable_of_mem_Ico` (on `[c, d)` with no
critical grade in `(c, d)`) and `stages_eq_stageTable_of_le_of_forall_le` (on the tail `[c, ∞)`
with `c` at least every critical grade), and `stages_eq_of_regime` (`F t = F c ∧ G t = G c`).
For a supplied family `cert : ℚ → List (Finset V × Finset V)`, the Boolean
`checkCertificates gF gG cert` accepts exactly when `checkSteps (stageTable gG c) (cert c) (stageTable gF c) = true` at
every critical grade `c` (`checkCertificates_eq_true_iff`). For filtrations with these tables,
`collapsesTo_of_checkCertificates` (soundness) gives `CollapsesTo (G t) (F t)` at every real `t`,
`le_of_checkCertificates` gives `F t ≤ G t`, `exists_checkCertificates_of_collapsesTo`
(completeness) gives an accepted family from levelwise collapses, and
`collapsesTo_iff_exists_checkCertificates` combines the two. No filtration is constructed from a
table, and no closure check of a table is made. `TDA.Persistence.CollapseCertificatePersistence`
(imported by `TDA.Persistence`) has, for `[LinearOrder V]`, any `hle : ∀ t, F t ≤ G t`, every
ring `R` and every degree `n`, `isIso_inclusionHom_of_checkCertificates`
(`IsIso (inclusionHom R n hle)` after acceptance), `certificateInclusionIso` (the natural
isomorphism) and `certificateInclusionIso_hom` (its forward map is `inclusionHom R n hle`).
`TDA.Filtration.AlphaCollapseFamilyExamples` (imported by `TDA.Filtration.Examples`) has 12
declarations on the obtuse triangle: `hasGradeTable_cech` and `hasGradeTable_alpha` (the actual
squared-grade Čech and α filtrations have the tables `cechGrades` and `gradedFaces obtuse`),
`criticalGrades_obtuse` (`{0, 1/2, 5/2, 4, 5}`), `stageTable_four_five` (at 4 the stage tables
are `triangle` and `alphaTable`, at 5 both are `triangle`), the family `obtuseCertificate`
(`[({0,1}, {0,1,2})]` at 4, empty elsewhere), `checkCertificates_obtuse` (accepted),
`checkCertificates_nil` (the empty family is rejected; the stage tables at 4 differ),
`checkCertificates_removal_from_four` (the family removing the long edge at every grade from 4
on is rejected; at 5 the pair is still free in the Čech table, the run ends at `alphaTable`, and
`alphaTable` is not the α table at 5), `stages_of_neg` (no faces for `t < 0`),
`stages_of_mem_Ico_four` (on `[4, 5)` the α stage has the face table `alphaTable` and the Čech
stage `triangle`), `stages_of_five_le` (on `[5, ∞)` both have the face table `triangle`) and `collapsesTo_of_certificate`
(`CollapsesTo (cech t) (alpha t)` at every real `t` through the verifier).
`TDA.Persistence.CollapseCertificatePersistenceExamples` (imported by
`TDA.Persistence.Examples`) has `isIso_inclusionHom_of_certificate`, `alphaCechCertificateIso`,
`alphaCechCertificateIso_hom` and `alphaCechCertificateIso_eq` (the isomorphism is
`CollapsePersistenceExamples.alphaCechIso`). See
[certificates across critical grades](math/discrete-morse-matchings.md#certificates-across-critical-grades).

The collapse modules `TDA.Simplicial.Collapse`, `TDA.Simplicial.CollapseHomology`,
`TDA.Simplicial.CollapseCertificate`, `TDA.Filtration.CollapseCertificateFamily`,
`TDA.Persistence.CollapsePersistence`, `TDA.Persistence.CollapseCertificatePersistence` and their
example modules provide no general-position theorem, Delaunay–Čech stage, producer of collapse
certificates or source result; see
[elementary collapses and the obtuse triangle](math/discrete-morse-matchings.md#elementary-collapses-and-the-obtuse-triangle),
[homology of collapses](math/discrete-morse-matchings.md#homology-of-collapses),
[checking supplied collapse sequences](math/discrete-morse-matchings.md#checking-supplied-collapse-sequences)
and
[certificates across critical grades](math/discrete-morse-matchings.md#certificates-across-critical-grades).

## Compatible lifts and algebraic sums over the reals

The [real interval decomposition note](math/real-interval-decomposition.md)
explains the cut, compatible-lift and finite-observation constructions in
prerequisite order. The decomposition endpoints use a field `k : Type u` and
`M : PModule.{u,0,u} k ℝ` with finite-dimensional fibers. Their occurrence
indices are in `Type`, with no countability restriction.

`CompatibleSections` separately proves evaluation surjectivity for compatible
sections on real subsets when every transition there is surjective. This result
is for a ring `R` and `PModule.{u,0,w} R ℝ`, with arbitrary carrier universe
`w`, and needs no finite-dimensionality assumption. `CutSubspaces` derives the
required surjectivity and quotient transport from cut subspaces of the
finite-dimensional fibers in the decomposition endpoint, then uses one global
compatible-section complement to build an interval-supported subfunctor.
`CutDecomposition.sumIso` is oriented from the algebraic sum of these
intermediate, possibly higher-dimensional cut subfunctors to `M`.
`RealIntervalDecomposition.scalarIso` has the same orientation after choosing
bases and refining to scalar interval summands; the existence theorem states
the inverse orientation, from `M` to the scalar sum. Neither endpoint theorem
has a wider carrier-universe interface than `PModule.{u,0,u} k ℝ`.

`AlgebraicFamily` compares algebraic sums with the existing product-based
`RealBarcode.familyModule` when only finitely many summands are nonzero at each
parameter. The decomposition proves this finite activity from finite-dimensional
fibers; it is pointwise finite overlap, not topological local finiteness. The
public `FiniteObservation.locallyFinite_family_finiteDimensional` criterion gives
the forward implication: for any field `k : Type u` and occurrence type
`J : Type 0`, convex real supports with only finitely many active occurrences at
each parameter give finite-dimensional fibers of the algebraic family, with
fiber universe `u` (`PModule.{u,0,u}`). Infinite occurrence types are allowed;
the criterion assumes no interval decomposition. The
finite-observation results show that only finitely many occurrences meet a
strict finite sample list and identify its rank barcode with the sampled
interval multiset, retaining repeated occurrences. Finite samples do not
determine unsampled support or infinite real lifetimes.

`TDA.Persistence.RealIntervalObservation` (namespace
`TDA.Persistence.RealIntervalDecomposition`) counts the occurrences of the scalar
decomposition by structure-map ranks. For `s ≤ t`,
`persistenceImage_finrank_eq_scalar_crossing_of_le` states that the `finrank` of the image of
the structure map from `s` to `t` is the number of occurrences whose `scalarSupport` contains
both `s` and `t`; `persistenceImage_finrank_eq_scalar_crossing` is its strict case `s < t`.
`scalar_crossing_finite` states that this set of occurrences is finite, and
`scalar_crossing_card_eq_of_iso_of_le` (strict case `scalar_crossing_card_eq_of_iso`) that
naturally isomorphic modules have the same count, although their chosen index types may
differ. See
[crossing counts from structure-map ranks](math/real-interval-decomposition.md#crossing-counts-from-structure-map-ranks).

`IntervalCompatibility` gives natural isomorphisms with the existing half-open
interval modules and finite diagram realizations. Its `constructibleIso` result
additionally assumes the existing constructibility predicate and
finite-dimensionality at the supplied sample levels.
`IntervalCompatibility.ephemeralIso` applies specifically to
`PModule.{0,0,0} ℚ ℝ` and retains all real singleton occurrences. Examples cover
empty families, endpoints, singleton supports, both
left-tail conventions, nonidentity maps and an infinite family with pointwise
finite activity accumulating at zero. The q-tame class has a different
hypothesis from finite-dimensional fibers.

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

`TDA.Persistence.IntegerBottleneck.run` computes the exact bottleneck for finite
ordered integer endpoint lists, with a doubled `WithTop ℕ` value and an optimal
occurrence witness when finite. Original list positions and multiplicities are
preserved; essential-count mismatch gives infinity. The exhaustive search is
connected to the existing real diagram bottleneck by `run_correct` and
`solve_cost_eq`. See [integer bottleneck computation](math/integer-bottleneck.md)
for costs, witness extraction and the exhaustive search bound.
`IntegerBottleneck.Presentation.ofPoints` presents a list of integer diagram points, and
`bottleneck_eq_of_points_of_twiceDistance` reads the search on two such lists as the
bottleneck distance of any two real diagrams with those points
(`bottleneck_eq_top_of_points_of_twiceDistance` in the infinite case). For two distance
tables, `Reduction.DistanceTable.bottleneck_rips_dgm_eq_of_twiceDistance` composes this
with `ripsRunInDegree_correct`: the search on the two record lists gives the bottleneck
distance between the F₂ Rips diagrams of the two table metrics.
`Reduction.RipsInputBottleneckExamples` is a downstream regression fixture that computes
three such distances by kernel evaluation (#1268).

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

For a finite metric population, `FiniteTotalVariation` constructs the common-mass
coupling of two atomic input laws and measures its exact mismatch probability
(`maximalCoupling_mismatch`); `finiteTotalVariation_eq_half_sum_abs` identifies
the normalization with the usual finite total variation.
`FiniteGromovWassersteinTV` bounds half-normalized distortion GW by a diameter
bound `D` and finite total variation `δ`:
`2 GW_p ≤ D (2δ)^(1/p)` for `p > 0`
(`two_mul_gromovWasserstein_le_finiteTotalVariation`). `RipsSamplingEmpirical`
combines this with the atomic sampled-law bound to give
`W_p ≤ D * choose(s,2)^(1/p) * (2δ)^(1/p)` for `p ≥ 1`, resample size
`s ≥ 2`, and every degree, including full H₀
(`Rips.wasserstein_sampleLaw_le_finiteTotalVariation`). Its empirical PMF counts repeated
training observations among `m ≥ 1` indices; `m` is independent of `s`.
This estimates a law of future sampled diagrams from the finite input law;
it supplies no random-training confidence level or bound on one observed
diagram. See [finite-population total variation](math/sampled-rips-laws.md#finite-population-total-variation).

`RipsSamplingConfidence` bounds the probability that an iid sample's canonical
q-tame diagram differs from the diagram of its compact support. For a finite
open `r/2`-net with `N` centers and minimum ball probability `β > 0`, the bound
is `P[dB(D(sample), D(support)) > 2r] ≤ N * (1 - β)^n`, for `n ≥ 1`, every
coefficient field and every degree. `qTameSampleDiagram` uses the existing
`Rips.Sample` range, identifying repeated draws while retaining essential bars.
The actual distance event is measurable by two-Lipschitz stability and the
extended pseudometric on `LocallyFiniteDecoratedDiagram`.
`qTameSampleDiagramOrderFree` and `qTameCompactCarrierDiagramOrderFree` are the same
diagrams on a metric space with no `LinearOrder` instance, such as a Euclidean space;
`measure_bottleneck_qTameSampleDiagramOrderFree_gt_le`,
`measure_bottleneck_qTameSampleDiagramOrderFree_carrier_gt_le` and
`measure_bottleneck_qTameSampleDiagramOrderFree_support_gt_le` are the confidence bounds
for them, and `RipsConfidenceClientExamples` is a downstream regression fixture (#1266).
`Probability.SamplingCoverage` supplies exact avoidance probabilities, the
finite union bound and probability restriction to the support. The ambient
compact-support formulation uses a separable metric Borel probability space.
See [finite-sample Rips confidence](math/rips-sampling-confidence.md) for the
cover hypotheses and the distinction from offset-diagram confidence results.

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
order-preserving optimal-coupling isometries. The restriction exists because Rips homology of
a carrier in `Type u` lives in `ModuleCat.{max u v}`; no cross-universe isometry invariance is
stated, so a client puts both carriers in one universe from the start (for a finite sample
`ULift.{u} (Fin m)`) rather than lifting afterwards. Client-facing forms (#1206) need no sign
condition on the threshold and, in the order-free forms, no auxiliary order.
`half_lt_ghDist_of_ofReal_lt_qTameLocallyFiniteDiagram_bottleneck` turns
`ENNReal.ofReal ε < bottleneck` into `ε / 2 < ghDist X Y`, and
`qTameLocallyFiniteDiagram_bottleneck_le_ofReal_of_ghDist_le_half` is its contrapositive.
`qTameLocallyFiniteDiagram_congr_linearOrder` shows the diagram is independent of the vertex
order. `qTameLocallyFiniteDiagramOrderFree X k hX n` takes the space explicitly and chooses the
order classically; `qTameLocallyFiniteDiagramOrderFree_eq` identifies it with every ordered
diagram and `qTameLocallyFiniteDiagramOrderFree_eq_of_isometryEquiv` gives isometry invariance.
`qTameLocallyFiniteDiagramOrderFree_bottleneck_le_two_mul_ghDist` and
`half_lt_ghDist_of_ofReal_lt_qTameLocallyFiniteDiagramOrderFree_bottleneck` are the bound and the
threshold form for compact nonempty spaces with no `LinearOrder` instance. The event inclusions
`setOf_ofReal_lt_bottleneck_subset_setOf_half_lt_ghDist` (a family `X : Ω → Type u` of compact
spaces) and `setOf_ofReal_lt_bottleneck_subset_setOf_half_lt_ghDist_of_finite` (one finite
nonempty carrier with outcome-dependent metrics `d : Ω → MetricSpace S`, installed with `letI`)
need no measurability, so `measure_mono` transfers a Gromov–Hausdorff tail estimate to the
diagrams. `RipsGHClientExamples` is a downstream regression fixture that opens no scope and
declares no instance. It replays these inferences in `orderFree_bottleneck_le`,
`half_lt_ghDist_of_lt_bottleneck`, `half_lt_ghDist_of_lt_bottleneck_ordered`,
`bottleneck_le_of_ghDist_le_half`, `unitInterval_diagram_reversed_order`,
`orderFree_eq_unitInterval_diagram`, `diagramErrorEvent_subset`,
`diagram_tail_le_of_gh_tail_le`, `one_sub_le_measure_compl_diagramErrorEvent`,
`fin_diagram_tail_le_of_gh_tail_le` and `ulift_fin_diagram_tail_le_of_gh_tail_le`, with the
event definitions `diagramErrorEvent` and `ghErrorEvent`.
Variable finite samples converge
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
definition; `sublevelModuleRealizationIso` realizes the module from the diagram. For
filters on two finite complexes, with unrelated vertex types and critical grids,
`bottleneck_dgm_eq_realInterleavingDistance` equates the bottleneck distance of their
diagrams with the interleaving distance of their sublevel modules,
`bottleneck_dgm_le_of_sublevelInterleaving` bounds it by the parameter of an interleaving,
and `nonempty_sublevelInterleaving_iff` is the witness equivalence at every finite
parameter. On one complex, `bottleneck_dgm_le_faceSupDifference_algebraic`
rederives finite-filter stability from the inclusion interleaving, independently of the
face-order proof, and essential multiplicities agree. `InterleavingIsometryClientExamples` is
a downstream regression fixture; it replays the
bound, its converse and threshold forms for finite-constructible modules, the two-complex
bound and the triangle inequality for diagrams (#1259). The scaling bridge in
`TDA.Persistence.SublevelScaling` adds the corresponding module and diagram identities.
The scaling bridge's log-scale statement is `logModule_scale_shiftIso` for `1 ≤ c`, and
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

For clients (#1245): `Cech.dgm_eq_of_linearOrder` states that the diagram does not depend on
the auxiliary label order, as the two-orders case of `Cech.dgm_eq_of_range_eq`.
`Cech.exists_lt_dist_of_ofReal_lt_bottleneck_dgm` and
`Cech.lt_hausdorffDist_of_ofReal_lt_bottleneck_dgm` are the threshold forms of the same-label
and Hausdorff bounds, for every real threshold. Labels and the coefficient field share one
universe; lift the labels with `ULift` for a field in a higher universe.
`CechClientExamples` is a downstream regression fixture. It replays the noise bound, its threshold and event forms with the measure tail
transfer, the resampling bound, finite subsets of an unordered space, relabelling and the
`ULift` route.

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
`TDA.Persistence.TotalPersistenceRegularity` gives total persistence on an ordered
presentation (`totalPersistence_orderedQ`, for a nonzero exponent) and proves that for an even
positive exponent it is `Cʳ` through every ordered presentation
(`totalPersistence_crThroughAllRepresentatives`, with `C¹` and `C²` forms). These are the loss
hypotheses of `sublevelDiagramScalarLoss_c1_neighborhood` and of the second-order calculus;
`TotalPersistenceLossClientExamples` is a downstream regression fixture for the squared total
persistence of a `C¹` filter family (#1270).
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
included. For unit masses, `BoundaryTransport.boundaryTransportPowerValue_ofIndexed_unit`
identifies the infimum over all Borel boundary plans between the atomic measures with the
powered finite matching minimum `finitePowerMatchingCost p` for `p ≥ 0`. No identification
with an ordinary Wasserstein coupling API is provided; in particular the library's own
`TDA.Probability.measureWasserstein` (exact probability marginals, used for the sampled Rips
laws) is a separate definition not identified with the boundary-transport value.
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
the finite-part transport cost. For unit masses,
`BoundaryTransport.boundaryTransportDistance_ofIndexed_unit` identifies the rooted all-Borel
boundary-plan value with `finitePMatchingCost` for `p ≥ 1`; quotient/metric instances and an
ordinary-coupling identification remain outside this API. `FinitePBottleneckLimit` proves the reverse
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

`TDA.Persistence.Enclosure.Exp` computes rational enclosures of the scalar exponential
that the kernel needs. For a rational `x ≤ 0` and a rational `δ > 0`, `expEnclosure x δ`
is a pair of rational numbers, computed by rational arithmetic, with
`lo ≤ Real.exp x ≤ hi` (`expEnclosure_mem`) and `hi - lo ≤ δ` (`expEnclosure_width`).
`expEnclosure?` returns it for such a request and `none` for a positive argument or a
nonpositive tolerance; `expEnclosure?_spec` states containment and width for every
returned interval. The argument is halved until it lies in `[-1, 0]`, a Taylor
polynomial is bounded by mathlib's `Real.exp_bound`, and the result is squared back with
outward rounding to a dyadic grid; `expHalvings`, `toleranceBits`, `expTerms`,
`expTaylor`, `roundDown`, `roundUp` and `expSquare` are the public steps of this
schedule. The width is absolute, not relative: the lower endpoint can be `0`. The cost
grows with the logarithm of `-x`, the digits of `1/δ` and the denominator of `x`, and is
documented, not proved. `TDA.Persistence.Enclosure.ExpExamples` holds the kernel-checked
fixtures. See [the algorithm, statements and limits](math/kernel-enclosure.md).

`TDA.Persistence.Enclosure.Gram` encloses the Gram sum and the squared RKHS distance of
two lists `x`, `y` of rational birth–death pairs, for a rational bandwidth `σ`, cap `c`
and tolerance `δ`. `capWeight c hc` is the weight `min c (max 0 persistence)` in
`Weight 1 c` for a rational `0 ≤ c`, `realPoints x` is the occurrence family indexed by
the positions of `x`, and `pointWeight` and `gaussExponent` are the executed rational
weight and exponent, identified with the library weight and with the exponent of
`kernel` by `capWeight_realPoint` and `kernel_realPoint`. `gramEnclosure σ c δ x y`
contains `linearKernel σ (capWeight c hc) (realPoints x) (realPoints y)`
(`gramEnclosure_mem`, for `0 ≤ c`) and has width at most `δ` (`gramEnclosure_width`, for
`0 ≤ c` and `0 < δ`). `sqDistEnclosure σ c δ x y` does the same for
`‖embedding σ w (realPoints x) - embedding σ w (realPoints y)‖ ^ 2`
(`sqDistEnclosure_mem`, `sqDistEnclosure_width`), through `norm_embedding_sub_sq`.
`gramEnclosure?` and `sqDistEnclosure?` return the intervals for `0 < σ`, `0 < c` and
`0 < δ` and `none` otherwise, with `gramEnclosure?_spec` and `sqDistEnclosure?_spec`.
`gramTerm` and `gramSum` are the public steps: each term is a product of two weights
times a scalar enclosure at tolerance `δ / max 1 (W x * W y)`, with `W = totalWeight c`,
and terms of zero weight compute no exponential. The width bounds hold for all lists,
including empty lists, zero total weight, repeated pairs and pairs with death at most
birth. `diagramEmbedding_eq_embedding_realPoints` transfers the statements to
`diagramEmbedding` of a diagram whose finite part is listed by `x`; essential bars play
no role, and a list containing a pair with death equal to birth is not the finite part
of a diagram. The widths are absolute, an enclosure decides no equality, and only the
capped weight is covered. The RKHS distance itself, pixel integrals and the `PiLp 1`
image norm are not enclosed. The cost, `m n` scalar enclosures for a Gram sum and at
most `m² + n² + m n` for a squared distance, is documented, not proved.
`TDA.Persistence.Enclosure.GramExamples` holds the kernel-checked fixtures and consumers
for `linearKernel`, `embedding` and `diagramEmbedding`. See
[Gram sums and the squared RKHS distance](math/kernel-enclosure.md#gram-sums-and-the-squared-rkhs-distance).

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

For a constructible ℝ-space `A : ConstructibleSpaceCat` in universe zero and any finite label
type, possibly empty, `finite_intervalComponents_constructibleSpace` discharges the finiteness
hypothesis, and `constructibleMapperReconstruction A a b` is the categorical reconstruction
(`constructibleMapperReconstruction_eq`, counit `constructibleMapperReconstructionIso`).
`geometricInterleavingDistance_constructibleMapperReeb_eq` identifies its geometric distance to
`quotientRGraphFunctor.obj A` with the interleaving distance from `coverComponents` to
`intervalComponents`, with no coverage assumption. Under coverage of the attained heights,
`geometricInterleavingDistance_constructibleMapperReeb_le_retained` and `_le` bound it by the
retained and full resolutions, `retainedCoverResolution_le_coverResolution` compares them, and
`tendsto_geometricInterleavingDistance_constructibleMapperReeb` and its `_retained` form give
convergence along any filter of finite covers with varying label types. No Hausdorff, graph-PL or
nonempty-input hypothesis is used. `constructibleMapperReconstruction_graphPLSpace` identifies
the graph-PL reconstruction definitionally, so the graph-PL results are specializations.
Positive-error cover existence for arbitrary constructible input is not provided. See
[constructible ℝ-spaces](math/mapper-reeb-approximation.md#constructible-ℝ-spaces).

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

## Alexandrov sheaves of persistence modules

`TDA.Sheaf.Alexandrov` identifies covariant diagrams on a preorder with sheaves on its upper
Alexandrov topology. The core takes Mathlib's parameters: `X : TopCat.{v}` with
`[Preorder X] [Topology.IsUpperSet X]` (open sets are the upper sets) and a complete category
`C : Type u` with `[Category.{v} C] [HasLimits C]`. Write `L := Alexandrov.principals X`,
sending `p` to its principal open `↑p = {y | p ≤ y}`; `p ≤ q` gives `↑q ⊆ ↑p`.

- `principalSections X C : X.Sheaf C ⥤ (X ⥤ C)` is `TopCat.Sheaf.forget C X` followed by
  precomposition with `L`. `principalSections_obj_obj` gives `F(↑p)` at `p`, and
  `principalSections_obj_map` gives the restriction along `↑q ⊆ ↑p` for `p ≤ q`.
- `kanSheaf X C : (X ⥤ C) ⥤ X.Sheaf C` has underlying presheaf
  `L.pointwiseRightKanExtension M` (`kanSheaf_obj_presheaf`), a sheaf by Mathlib's
  `Alexandrov.isSheaf_principalsKanExtension`; on morphisms it is the
  `liftOfIsRightKanExtension` lift (`kanSheaf_map_hom`), acting componentwise on limits
  (`kanSheaf_map_hom_app_π`).
- `counitIso X C : kanSheaf X C ⋙ principalSections X C ≅ 𝟭 _` is the limit projection at
  `(p, 𝟙)` (`counitIso_hom_app_app`); `principalSections_kanSheaf_map_comp_counit` and
  `principalSections_kanSheaf_map` identify the transition of `Γ(A M)` with `M.map`, and
  `principalSections_kanSheaf_map_app` the action on morphisms.
- `unitIso X C : 𝟭 _ ≅ principalSections X C ⋙ kanSheaf X C` is, on an open `U`, the lift of
  the restrictions `F(U) ⟶ F(↑p)` for `↑p ⊆ U` (`unitIso_hom_app_hom_app`,
  `unitIso_hom_app_hom_app_π`); on `↑p` its inverse is the projection at `(p, 𝟙)`
  (`unitIso_inv_app_hom_app_principalOpen`). It is invertible for every sheaf, because the
  principal opens form a basis (`isBasis_principalOpen`).
- `equivalence X C : X.Sheaf C ≌ (X ⥤ C)` has these functors and isomorphisms
  (`equivalence_functor`, `equivalence_inverse`, `equivalence_unitIso`,
  `equivalence_counitIso`). `restrictionConeIsLimit` states that the restrictions to the
  principal opens inside any open form a limit cone, and `isPointwiseRightKanExtension` that
  every sheaf is the pointwise right Kan extension of its principal sections.

For an unbundled preorder `P : Type v`, `upperSpace P` is `TopCat.of (Topology.WithUpperSet P)`;
the topology of `P` itself is unchanged. `upperSetEquivalence P C : (P ⥤ C) ≌ (upperSpace P).Sheaf C`
composes `equivalence` with the order isomorphism `WithUpperSet.toUpperSetOrderIso`.
`upperSetSectionsIso M p` identifies the sections over `↑p` with `M.obj p`;
`upperSetSectionsIso_hom_naturality` identifies the restriction along `↑q ⊆ ↑p` with
`M.map (homOfLE h)` for `h : p ≤ q`, and `upperSetEquivalence_map_app_sectionsIso` the action
of a morphism `α` with `α.app p`. For `PModule.{0,0,0} K ℝ` over a field `K : Type`, take
`C = ModuleCat.{0} K`.

`TDA.Sheaf.AlexandrovExamples` checks the chain `0 ⟶ ℚ` on `Fin 2`, whose sections over the
whole space are zero and whose restriction to `↑1` is the noninvertible map into `ℚ`, a
morphism of chains that is invertible only over `↑1`, the empty open, the whole two-point
antichain `Unit ⊕ Unit` (not principal; `antichainIsProduct` gives a binary product for every
sheaf by `restrictionConeIsLimit`) and real-indexed modules over `ℚ` and `ZMod 2`. The
equivalence concerns the upper Alexandrov topology only, not sheaves on Euclidean space for
its ordinary topology; see [Alexandrov sheaves](math/alexandrov-sheaves.md).

`TDA.Sheaf.AlexandrovTranslation` translates sheaves on `X := upperSpace ℝ`. For `ε : ℝ≥0`,
`translate ε : X ⟶ X` is `x ↦ x - ε`, `WithUpperSet.map` of the monotone `downTranslation ε`.
Its preimage of an open `U` is the translate `U + ε` (`coe_map_translate`, `mem_map_translate`),
and `↑t` pulls back to `↑(t + ε)` (`map_translate_principalOpen`).

- `sheafShift C ε := TopCat.Sheaf.pushforward C (translate ε)`, for any category `C`, with
  `(S ε F)(U) = F(U + ε)` (`sheafShift_obj_presheaf_obj`, and
  `sheafShift_obj_presheaf_obj_principalOpen` on principal opens) and morphisms by
  `TopCat.Sheaf.pushforward_map` (`sheafShift_map_hom`).
- `sheafShiftLE C h : sheafShift C ε ⟶ sheafShift C δ` for `h : ε ≤ δ`,
  `sheafTransition C ε : 𝟭 _ ⟶ sheafShift C ε`, `sheafZeroIso C : sheafShift C 0 ≅ 𝟭 _`,
  `sheafCompIso C ε δ : sheafShift C δ ⋙ sheafShift C ε ≅ sheafShift C (ε + δ)` and
  `sheafCongrIso C h` for `h : ε = δ`. Every component is a restriction along an inclusion or
  equality of preimage opens (`map_translate_antitone`, `map_translate_le`,
  `map_translate_zero`, `map_translate_comp`); the coherence laws `sheafShiftLE_refl`,
  `sheafShiftLE_comp`, `sheafTransition_comp_shiftLE`, `sheafTransition_zero`,
  `sheafTransition_zero_eq`, `sheafTransition_add`, `sheafTransition_congr`,
  `sheafCongrIso_refl`, `sheafCompIso_zero_left`, `sheafCompIso_zero_right` and
  `sheafCompIso_assoc` mirror those of `RealShift`.
- `realSections C : X.Sheaf C ⥤ (ℝ ⥤ C)` is `principalSections` read along
  `WithUpperSet.toUpperSetOrderIso`, equal to `(upperSetEquivalence ℝ C).inverse`
  (`realSections_eq`), hence fully faithful (`realSectionsFullyFaithful`).
- `shiftComparison R ε : sheafShift ε ⋙ realSections ≅ realSections ⋙ RealShift.shift ε` for
  `C = ModuleCat.{0} R`, `R : Type u` a ring, has components the restrictions along
  `↑t + ε = ↑(t + ε)`. `shiftComparison_shiftLE`, `shiftComparison_transition`,
  `shiftComparison_zeroIso` and `shiftComparison_compIso` identify the sheaf order map,
  transition, zero and addition isomorphisms with `RealShift.shiftLE`, `RealShift.transition`,
  `RealShift.zeroIso` and `RealShift.compIso`.
- `SheafInterleaving ε F G` has arrows `φ : F ⟶ S ε G`, `ψ : G ⟶ S ε F` and the equations
  `φ ≫ S ε ψ ≫ (sheafCompIso C ε ε).hom.app F = (sheafTransition C (ε + ε)).app F` and its
  mirror, the orientation of `RealInterleaving`. For `ModuleCat.{0} R`,
  `SheafInterleaving.equivRealInterleaving : SheafInterleaving ε F G ≃ RealInterleaving ε (Γ F) (Γ G)`
  applies `Γ` and the comparison; its inverse composes with the inverse comparison and lifts
  along `Γ` (`map_equivRealInterleaving_symm_φ`, `map_equivRealInterleaving_symm_ψ`).
  `SheafInterleaving.zeroEquivIso : SheafInterleaving 0 F G ≃ (F ≅ G)` has
  `hom = φ ≫ (sheafZeroIso _).hom.app G` (`zeroEquivIso_apply_hom`, `zeroEquivIso_apply_inv`).
- `sheafInterleavingDistance F G` is the extended infimum of the radii with a sheaf witness;
  `sheafInterleavingDistance_eq` equates it with `realInterleavingDistance (Γ F) (Γ G)`, and
  `sheafInterleavingDistance_upperSet` with `realInterleavingDistance M N` on the sheaves
  attached to `M` and `N` (`nonempty_sheafInterleaving_upperSet_iff` for witnesses).
  `sheafInterleavingDistance_self`, `_comm` and `_triangle` are transported.
  `SheafInterleaving.equivUpperSet M N` identifies witnesses of the attached sheaves with
  `RealInterleaving ε M N`, by `equivRealInterleaving` and the unit of `upperSetEquivalence ℝ`.

The restriction identities used by both translation modules are in
`TDA.Sheaf.PresheafRestriction`, for a presheaf `P : (Opens X)ᵒᵖ ⥤ C` on any `X : TopCat`: any
two restrictions between the same opens agree (`presheaf_map_eq`), likewise composites
(`presheaf_map_comp_map`, `presheaf_map_comp_map_eq`, `presheaf_map_comp_map_eq_comp`), and
`restrictIso P h` is the restriction along `h : U = V` as an isomorphism.
`TDA.Sheaf.AlexandrovTranslation.restrictIso` is this isomorphism on `upperSpace ℝ`.

`TDA.Sheaf.AlexandrovTranslationExamples` evaluates the shift on the empty open, the whole line
and the non-principal open ray `(t, ∞)` (`sheafShift_bot`, `sheafShift_top`,
`sheafShift_openRay`), and checks the upper rays `[0, ∞)` and `[r, ∞)` over a field for
`0 ≤ r`: a module witness exists if and only if `r ≤ ε` (`rays_nonempty_iff`, with the
obstruction `rays_isEmpty` at `t = 0` and the comparison witness `rayInterleaving`, whose
arrows are nonzero), likewise a sheaf witness (`raySheaves_nonempty_iff`,
`raySheafInterleaving_φ_ne_zero`), and the sheaf distance is `r` (`raySheaves_distance`).

`TDA.Sheaf.AlexandrovCoordinateTranslation` translates sheaves on
`X := upperSpace (Fin n → ℝ)`, the product order with its upper Alexandrov topology, for every
`n` including `n = 0`. For `ε : ℝ≥0`, `translate ε : X ⟶ X` is `x ↦ x - ε · 1`, that is
`(translate ε x)_i = x_i - ε`, `WithUpperSet.map` of the monotone `downTranslation ε`. Its
preimage of an open `U` is the image of `U` under `CoordinateShift.translation ε`
(`coe_map_translate`, `mem_map_translate`), and `↑a` pulls back to
`↑(CoordinateShift.translation ε a)` (`map_translate_principalOpen`); inclusions and equalities
of preimages are proved coordinatewise (`map_translate_antitone`, `map_translate_le`,
`map_translate_zero`, `map_translate_comp`).

- `sheafShift C ε := TopCat.Sheaf.pushforward C (translate ε)`, with
  `(S ε F)(U) = F(U + ε · 1)` (`sheafShift_obj_presheaf_obj`,
  `sheafShift_obj_presheaf_obj_principalOpen`) and morphisms by `TopCat.Sheaf.pushforward_map`
  (`sheafShift_map_hom`). `sheafShiftLE`, `sheafTransition`, `sheafZeroIso`, `sheafCompIso` and
  `sheafCongrIso` are restrictions along preimage opens and satisfy the coherence laws of
  `CoordinateShift` under the same names as in `TDA.Sheaf.AlexandrovTranslation`.
- `coordinateSections C : X.Sheaf C ⥤ ((Fin n → ℝ) ⥤ C)` is `principalSections` read along
  `WithUpperSet.toUpperSetOrderIso`, equal to `(upperSetEquivalence (Fin n → ℝ) C).inverse`
  (`coordinateSections_eq`), hence fully faithful (`coordinateSectionsFullyFaithful`).
- `shiftComparison R ε : sheafShift ε ⋙ coordinateSections ≅ coordinateSections ⋙
  CoordinateShift.shift ε` for `C = ModuleCat.{0} R` has components the restrictions along
  `↑a + ε · 1 = ↑(a + ε · 1)`; `shiftComparison_shiftLE`, `shiftComparison_transition`,
  `shiftComparison_zeroIso` and `shiftComparison_compIso` identify the sheaf order map,
  transition, zero and addition isomorphisms with `CoordinateShift.shiftLE`,
  `CoordinateShift.transition`, `CoordinateShift.zeroIso` and `CoordinateShift.compIso`.
- `SheafInterleaving ε F G` has the orientation of `CoordinateInterleaving`. For
  `ModuleCat.{0} R`,
  `SheafInterleaving.equivCoordinateInterleaving : SheafInterleaving ε F G ≃
  CoordinateInterleaving ε (Γ F) (Γ G)` applies `Γ` and the comparison
  (`equivCoordinateInterleaving_apply_φ_app`: at `a`, the arrow over `↑a` followed by the
  comparison restriction), and `SheafInterleaving.equivUpperSet M N` composes it with the unit of
  `upperSetEquivalence` to `CoordinateInterleaving ε M N` for the sheaves attached to `M` and
  `N` (`equivUpperSet_apply_φ_app`, `equivUpperSet_apply_ψ_app`).
  `SheafInterleaving.zeroEquivIso : SheafInterleaving 0 F G ≃ (F ≅ G)` has
  `hom = φ ≫ (sheafZeroIso _).hom.app G`.
- `sheafInterleavingDistance_eq` equates `sheafInterleavingDistance F G` with
  `coordinateInterleavingDistance (Γ F) (Γ G)`, and `sheafInterleavingDistance_upperSet` with
  `coordinateInterleavingDistance M N`; `_self`, `_comm` and `_triangle` are transported.

`TDA.Sheaf.AlexandrovCoordinateTranslationExamples` checks three dimensions. For `n = 0` the
space is one point and every translation is the identity (`translate_eq_id_zero`,
`zeroDimShiftIso`); a witness at any radius gives an isomorphism (`isoOfSheafInterleaving`,
`zeroDim_nonempty_iff`), so the sheaf distance and `coordinateInterleavingDistance` are `0`
exactly for isomorphic objects and `∞` otherwise (`zeroDim_distance_eq_zero_iff`,
`zeroDim_distance_eq_top_iff`, `zeroDim_coordinateDistance_eq_zero_iff`,
`zeroDim_coordinateDistance_eq_top_iff`). For `n = 1`, `linePushforward` is the pushforward
along the homeomorphism `lineHomeomorph : upperSpace (Fin 1 → ℝ) ≃ₜ upperSpace ℝ` of the order
isomorphism `Fin 1 → ℝ ≃o ℝ`; it carries the coordinate shift to the real shift
(`linePushforward_sheafShift`), and `lineWitness` pushes both arrows of a witness forward. The
square commutes (`line_square`): `interleavingEquiv (equivRealInterleaving (lineWitness i))` is
`equivCoordinateInterleaving i` transported along `lineSectionsIso`, the restrictions along
`↑a = lineMap⁻¹ ↑(a 0)`. So `lineWitness` is bijective (`lineEquiv`) and the distances agree
(`line_sheafDistance_eq`, `line_distance_eq`). For `n = 2`, the upper set
`mixedUpset s = {x | s < x₀ ∧ s ≤ x₁}` pulls back to `mixedUpset (s + ε)`
(`map_translate_mixedUpset`), and for `0 < ε ≤ c` the point `(ε, c)` leaves it under the shift
while its second coordinate stays at `c` (`mixedUpset_status_change`).

### Real Alexandrov and upper ray sheaves

`TDA.Sheaf.RaySheaf` compares the upper Alexandrov line with the ray topology. `raySpace` is
`TopCat.of (WithUpper ℝ)`, Mathlib's upper topology, whose basic opens are the rays
`ray t = (t, ∞)` (`isBasis_ray`); `isOpen_ofUpper_preimage_iff` identifies its open sets with
the ordinary open upper sets of `ℝ`. `rayId : upperSpace ℝ ⟶ raySpace` is the continuous
identity, and `C : Type u` has `[Category.{0} C]` (with `[HasLimits C]` for `Q`).

- `rayQ C : (ℝ ⥤ C) ⥤ raySpace.Sheaf C` is `(upperSetEquivalence ℝ C).functor` followed by
  `TopCat.Sheaf.pushforward C rayId`; `rayB C : raySpace.Sheaf C ⥤ (ℝ ⥤ C)` is
  `B(F)(t) = F(ray t)` with the restrictions of `F` (`rayB_obj_obj`, `rayB_obj_map`).
- `rayProj M h : BQ(M)(t) ⟶ M(s)` for `h : t < s` is the Kan-extension projection at
  `↑s ⊆ (t, ∞)`. `rayConeIsLimit` and `rayLimitIso M t : BQ(M)(t) ≅ limit (rayDiagram M t)`
  identify `BQ(M)(t)` with `lim_{s > t} M(s)` (`rayLimitIso_hom_π`,
  `rayLimitIso_inv_rayProj`); `rayProj_comp_map`, `map_rayProj`, `map_app_rayProj` and
  `rayProj_ext` are the projection equations and extensionality, and `rayLift` builds maps into
  `BQ(M)(t)` from compatible families.
- `rayUnit C : 𝟭 ⟶ rayQ C ⋙ rayB C` has `η ≫ rayProj M h = M(t ≤ s)`
  (`rayUnit_app_app_rayProj`). `rayCounitIso C : rayB C ⋙ rayQ C ≅ 𝟭` compares `F(V)` with the
  limit of `F(ray p)` over the points `p` of `V`, by the sheaf condition for the ray cover
  (`iSup_ray`, with the empty cover of `⊥`, and `ray_inf`); on rays
  `rayCounitIso_inv_app_hom_app_rayProj`. `rayB_faithful` follows.
- `rayShift C ε` is `TopCat.Sheaf.pushforward` along `rayTranslate ε : x ↦ x - ε`
  (`map_rayTranslate_ray`), with `rayTransition`, `rayCompIso` and `rayTransition_add`.
  `pushforward_map_sheafShift_map`, `pushforward_map_sheafTransition` and
  `pushforward_map_sheafCompIso` match them with `sheafShift`, `sheafTransition` and
  `sheafCompIso` of `TDA.Sheaf.AlexandrovTranslation` at the same radius
  (`translate_comp_rayId`). For `ModuleCat.{0} R`,
  `rayShiftComparison R ε : rayShift ε ⋙ rayB ≅ rayB ⋙ RealShift.shift ε` carries them to
  `RealShift.transition` and `RealShift.compIso` (`rayShiftComparison_transition`,
  `rayShiftComparison_compIso`).
- `RaySheafInterleaving ε F G` has the orientation of `RealInterleaving`, with `symm`, `refl`
  and `congr`; `raySheafInterleavingDistance` is the extended infimum of radii with a witness
  (`raySheafInterleavingDistance_congr`). `RaySheafInterleaving.toRealInterleaving` (for `B`)
  and `RaySheafInterleaving.ofRealInterleaving` (for `Q`, through
  `SheafInterleaving.equivRealInterleaving` and `ofSheafInterleaving`) transport witnesses at
  the same radius.
- For `hε : 0 < ε`, `unitInterleaving M hε : RealInterleaving ε M (BQ M)` has forward arrow
  `M(t ≤ t + ε) ≫ η` (`unitInterleaving_φ_app`) and reverse arrow the projection to
  `M(t + ε)` (`unitInterleavingψ`); hence `realInterleavingDistance_rayB_rayQ`.
  `raySheafInterleavingDistance_rayQ` equates the ray-sheaf distance of `Q M, Q N` with
  `realInterleavingDistance M N`, and `realInterleavingDistance_rayB` the real distance of
  `B F, B G` with the ray-sheaf distance of `F, G`.
- `isZero_rayQ_iff`: `IsZero (Q M)` exactly when `M(s ≤ t) = 0` for all `s < t`;
  `isZero_iff_isZero_rayB` reduces zero sheaves to their values on rays.

`TDA.Sheaf.RaySheafExamples` checks the empty open (`rayCover_bot_isEmpty`,
`rayQ_obj_bot_isZero`), the singleton module `pointModule` over a field, nonzero with
`Q (pointModule) = 0`, at distance zero from `BQ(pointModule)` with no radius-zero witness
(`pointModule_distance`, `pointModule_isEmpty_zero`), and the constant module `constModule`,
whose unit is an isomorphism (`isIso_rayUnit_constModule`, `constModule_zeroInterleaving`).

## Finite alternating diagrams

An orientation `o : Fin n → Bool` of the path with vertices `Fin (n + 1)` points arrow `a` from
`a.castSucc` to `a.succ` when `o a = true` and backwards otherwise (`src`, `tgt`, `Arrow`). A
diagram is a functor `Diagram k o := Paths (Vertex o) ⥤ ModuleCat.{u} k` from the free
category, i.e. one linear map per arrow; `ofArrows`, `homMk` and `isoMk` build objects,
morphisms and isomorphisms from generators (`gen`), and `arr M i j` is the map along an arrow
or zero. Intervals are `FiniteInterval (n + 1)` read as segments `[birth, death - 1]`;
`interval o J` has the field on the segment, and `intervalSum o xs` (`barcodeDiagram o B` for a
multiset) is the iterated biproduct.

- `TDA.Sheaf.AlternatingDiagram`: subdiagrams `sub` and the internal direct sum
  `isoBiprodOfIsCompl` of stable complementary subspaces; `intervalIso`, a diagram with
  compatible spanning vectors nonzero exactly on `J` is `interval o J`; dimension vectors
  `finrank_intervalSum_obj` and arrow ranks `finrank_range_intervalSum_map` count the intervals
  containing one vertex, respectively both ends of the arrow.
- `TDA.Sheaf.AlternatingReflection`: for a sink `p` (`IsSink`) and an orientation `o'`
  reversing exactly the arrows at `p` (`IsFlipAt`), `reflectSink o' hs hf` replaces the space
  at `p` by the kernel of the signed sum of the incoming maps (`sinkSum`, sign `+1` from the left
  and `-1` from the right, i.e. the fibre product), with the coordinate projections as the new
  arrows. All reflected spaces are subspaces of the product of the vertex spaces (`sinkSpace`).
  It is an additive functor; `reflectSinkIntervalIso` and `isZero_reflectSink_singleton`
  compute it on intervals through `reflectInterval p`, which moves the endpoint next to `p`
  across `p` and removes `{p}`; `reflectInterval_reflectInterval` inverts it away from `{p}`.
- `TDA.Sheaf.AlternatingSourceReflection`: for a source `p`, `reflectSource o' hs hf M` replaces
  the space at `p` by the cokernel of the signed outgoing map (`srcDelta`, the pushout), as
  quotients of the product (`srcSpace`). When the outgoing maps are jointly injective
  (`OutInjective`), `reflectSourceUnitIso` identifies `M` with the sink reflection of its source
  reflection; otherwise `exists_singleton_summand` splits off `interval o (singletonInterval p)`
  with smaller total dimension.
- `TDA.Sheaf.AlternatingDecomposition`: `chainToDiagram` sends a module on the chain
  `Fin (n + 1)` to the all-forward diagram (`fwd n`), with `diagramToChain`,
  `isoChainToDiagram` and `chainIso`; `exists_decomposition_fwd` and
  `multiset_eq_of_iso_fwd` are `exists_list_interval_decomposition` and
  `barcode_decomposition_unique` read through it. For every orientation,
  `exists_decomposition o M` gives a list `xs` with `M ≅ intervalSum o xs`, by source
  reflections after the last backward arrow (`exists_source_step`, weight `weightE`) and
  singleton splitting, and `multiset_eq_of_iso` shows that isomorphic interval sums have the
  same multiset, by sink reflections at the first backward arrow (`exists_sink_step`, weight
  `weightU`) and the dimension at the sink. `barcode M` is that multiset, `barcodeIso M` a
  chosen isomorphism, `barcode_eq_of_iso` its characterization,
  `nonempty_iso_iff_barcode_eq` the classification, `intervalMultiplicity M J` the
  invariant multiplicities and `finrank_obj_eq_countP_barcode` the dimension vector.
- `TDA.Sheaf.AlternatingHeredity`: `pathTensor k o i`, the left adjoint
  `evaluationLeftAdjoint` of evaluation at `i`, sends `V` to `P_i ⊗ V`; `pathSlot i V p` is the
  copy of `V` at a path `p : i ⟶ t`, `pathSlot_map` composes paths, and
  `pathTensorObjEquiv_pathSlot` and `pathTensorObjEquiv_map` identify `(P_i ⊗ V)_t` with
  `(vtx o i ⟶ t) →₀ V`. `representable k o i` is `P_i = k[paths i → −]`, with the Yoneda
  equivalence `representableHomEquiv`. `pathTensorAdjunction` is the evaluation Hom adjunction
  `Hom(P_i ⊗ V, X) ≃ Hom(V, X_i)`, and `projective_pathTensor` makes `P_i ⊗ V` projective for
  every vector space `V`, as are the finite sums `sumTensor σ V`. `resolution M` is the short
  complex `resolutionLeft M ⟶ resolutionMiddle M ⟶ M`, i.e.
  `⊕_(a : i → j) P_j ⊗ M_i ⟶ ⊕_i P_i ⊗ M_i ⟶ M` with arrows indexed by `Edge o`:
  `leftSlot_resolutionDifferential_app` sends `u` in the slot of `a` and `q : j ⟶ t` to `u` in
  the slot of the path `a ≫ q` minus `M(a) u` in the slot of `q`, so with `q = 𝟙` to its own
  path slot and `-M(a) u` in the main slot of `j`; `middleSlot_resolutionAugmentation_app` is
  `M(p)` on the slot of `p`. `resolutionSplitting M t` splits it at every vertex through the
  contracting map `resolutionLift`, `resolution_map_evaluation_shortExact` is pointwise
  exactness and `resolution_shortExact` exactness in the diagram category. Hence
  `enoughProjectives_diagram`, the instance `hasProjectiveDimensionLT_two`, and `ext_eq_zero`
  and `subsingleton_ext` for `Ext^m(M, N)` with `2 ≤ m`, for every diagram, finite-dimensional
  or not, and every `HasExt` universe.

`TDA.Sheaf.AlternatingDiagramExamples` uses the fork `0 → 1 ← 2`: `[0, 2] + {1}` and
`[0, 1] + [1, 2]` have the same dimensions and arrow ranks but different barcodes, so they are
not isomorphic (`not_nonempty_iso_crossing_split`); a repeated summand has multiplicity two, the
zero diagram has the empty barcode, and the sink reflection at `1` keeps only `[0, 2]`.
`TDA.Sheaf.AlternatingHeredityExamples` resolves `[0, 2]` on the same fork
(`resolution_whole_shortExact`, `projective_resolution_whole`), shows
`Ext²([0, 2], {1}) = 0` and that the Yoneda product of two `Ext¹` classes vanishes
(`ext_one_comp_ext_one_eq_zero`), and that the path `0 → 1` gives a nonzero vector of `P_0` at
the sink.

## Degree-zero singular homology of interval preimages

For `f : C(X, ℝ)` with `X : Type u` and a ring `k : Type u`, `TDA.Reeb.intervalPreimageTopCat f :
OpenInterval ⥤ TopCat.{u}` sends `I` to the subspace `f ⁻¹ I` and `I ≤ J` to the actual
`preimageInclusion f` through `toOpensFunctor`. `intervalSingularHomology k n f` composes it with
`(AlgebraicTopology.singularHomologyFunctor (ModuleCat k) n).obj k₀`, `k₀ = ModuleCat.of k k`, and
`linearizedIntervalComponents k f = intervalComponents f ⋙ sigmaConst.obj k₀` is the free
`k`-module on the path-component precosheaf, both in `ModuleCat.{u} k`.

- `intervalSingularHomologyIso₀ k f : intervalSingularHomology k 0 f ≅ linearizedIntervalComponents k f`
  has components `TopCat.singularHomology₀Iso`; `_hom_app` and `_inv_app` are `rfl`. No
  compactness, tameness or local assumption is made, and `k` is any ring.
- For any space `X : TopCat.{w}` and `R` in a preadditive category with homology and coproducts of
  size `w`, `singularHomology₀Class X R x : R ⟶ H₀(X; R)` is the class of the point `x`.
  `singularHomology₀Class_comp_singularHomology₀Iso_hom` sends it to the coproduct injection
  indexed by `ZerothHomotopy.mk x`, `singularHomology₀Class_comp_map` sends it to the class of
  the image point under a continuous map, and `singularHomology₀Iso_hom_naturality` and
  `singularHomology₀ε_naturality` state naturality of `TopCat.singularHomology₀Iso` and of the
  augmentation for the map `componentMap` of path components. The proof tests on point
  representatives rather than on the chain-level epimorphism.
- Map rule: for `i : I ⟶ J` and `x : f ⁻¹ I`, `intervalClass_comp_map_comp_intervalSingularHomologyIso₀_hom_app`
  and `intervalClass_comp_intervalSingularHomologyIso₀_hom_app_comp_map` both send the class of `x`
  to the injection indexed by `ZerothHomotopy.mk` of the included point, along the homology square
  and the linearized component square (`intervalComponents_map_mk`).
- `isZero_intervalSingularHomology₀_obj_bot` and `isZero_linearizedIntervalComponents_obj_bot`: the
  empty interval has zero value.

`TDA.Reeb.IntervalSingularHomologyExamples` covers the empty interval, an empty source, the
identity of `ℝ` (path connected preimages, `id_map_isIso`) and `f t = t²`, where the inclusion of
the band `(1, 4)` into `(-1, 4)` merges the two path components `(-2, -1)` and `(1, 2)` of the
preimage and induces the fold `k ⊕ k ⟶ k` (`fold`). This is a degree-zero comparison only: it forgets
higher homology and is not a derived equivalence; see
[interval singular homology](math/reeb-interval-singular-homology.md).

### Perturbation stability of interval singular homology

`TDA.Reeb.IntervalSingularHomologyStability` (#1173): for `f g : C(X, ℝ)` and
`h : ∀ x, |f x - g x| ≤ ε`, in every degree `n` and over every ring `k`,
`intervalSingularHomologyInterleaving h : Interleaving ε (intervalSingularHomology k n f)
(intervalSingularHomology k n g)` is built by `Interleaving.ofApp` from
`intervalSingularHomologyPerturbation`, singular homology applied to
`perturbationInclusion h I` (as `perturbationTopHom h I`) and to the inclusions of the swapped bound
`perturbationBound_symm h`. The two triangles are functoriality, because the composed inclusions are
the same subtype inclusions as `thickenUnit` (`intervalPreimageTopCat_hom_ext`). The category-polymorphic
`smoothing`, `Interleaving` and `interleavingDistance` are reused. No compactness, tameness or
finiteness assumption is made.

- Laws: `intervalSingularHomologyInterleaving_self` (`f = g` is `Interleaving.refl`),
  `_symm`, `_mono` and `_trans`, as for `perturbationInterleaving`; `_φ`, `_ψ` and
  `nonempty_interleaving_intervalSingularHomology` are the projections and existence form.
- Distances: `interleavingDistance_intervalSingularHomology_le` is the radius inequality
  `d(H_n f, H_n g) ≤ ε`; `interleavingDistance_intervalSingularHomology_le_edist` is the extended
  supremum bound `d(H_n f, H_n g) ≤ edist (UniformFun.ofFun f) (UniformFun.ofFun g)` with the
  extended distance of mathlib's uniform structure, `⊤` allowed.
- Degree zero: `linearizedPerturbationInterleaving k h` is the existing path-component witness
  `perturbationInterleaving h` post-composed with `sigmaConst.obj (ModuleCat.of k k)`
  (`Interleaving.postcomp`). `intervalSingularHomologyPerturbation_zero` shows that the degree-zero
  witness equals the linearized one conjugated by `intervalSingularHomologyIso₀`, from the naturality
  `singularHomology₀Iso_hom_naturality` of the isomorphism for the inclusion
  (`intervalSingularHomologyPerturbation_app_comp_iso₀`), and `intervalSingularHomologyInterleaving_zero`
  states it for the interleaving, transported by `Interleaving.isoRight` and `symm`.
  `intervalClass_comp_intervalSingularHomologyPerturbation_app` sends the class of a point to the
  class of the same point.

`TDA.Reeb.IntervalSingularHomologyStabilityExamples` covers an empty source (every parameter, distance
`0`), parameter `0` (an isomorphism of interval functors, and `f = g` is the identity witness), empty
preimages (`isZero_obj_of_preimage_empty`), and constant maps from a point at heights `a` and `b` over
a nontrivial ring: the distance is exactly `|a - b|` (`interleavingDistance_const`). For the lower
bound (`isEmpty_interleaving_const`), if `ε < |a - b|`, a small open interval around `a` has an
`ε`-thickening omitting `b`; the first composite then factors through the zero value at that
thickening, while the transition on `H₀` of the point is the identity on `k`. Mayer–Vietoris
compatibility is a separate unit.

## The algebraic core of singular Mayer–Vietoris

`TDA.Topology.SmallChains`, `TDA.Topology.SingularMayerVietoris` and
`TDA.Topology.QuasiIsoOfIterate` (#1190, imported by `TDA.Topology`, namespace `TDA.Topology`)
work with the singular simplicial set `TopCat.toSSet.obj Y` of a space `Y : TopCat.{u}` and with
chains `SSet.chainComplex` and `singularChainComplexFunctor` with coefficients `R` in a category
with coproducts.

- Small chains, for arbitrary subsets `s t : Set Y`: `simplicesIn s` is the subcomplex of singular
  simplices with image in `s` (`mem_simplicesIn_iff`), the range of `toSSet` applied to
  `subsetIncl s`; `simplicesIn_mono`, `simplicesIn_inter` and `simplicesIn_univ` are its lattice
  rules. `smallSimplices s t = simplicesIn s ⊔ simplicesIn t` (`mem_smallSimplices_iff`: image in
  `s` or in `t`), `smallChains s t R` its chains and `smallChainsι s t R` the inclusion into all
  singular chains, a monomorphism (`mono_smallChainsι`). `toSSetSubsetIso s` and
  `singularChainsSubsetIso s R` identify the subspace with `simplicesIn s`, and for an embedding
  `g`, `range_toSSet_map_eq_simplicesIn` identifies the range of `toSSet.map g` with
  `simplicesIn (Set.range g)`.
- Short exactness, in any abelian category with coproducts: `isPushout_chainComplex` sends a
  bicartesian square of subcomplexes `SSet.Subcomplex.BicartSq A₁ A₂ A₃ A₄` to a pushout square of
  chain complexes. For a pushout square `t, l, r, b`, `mvShortComplex h` is the reducible short
  complex `X₁ ⟶ X₂ ⊞ X₃ ⟶ X₄` with maps `biprod.lift t (-l)` and `biprod.desc r b`, and
  `shortExact_mvShortComplex` proves it short exact when `t` is a monomorphism.
  `shortExact_smallChains R s t` is `0 → C(s ∩ t) → C(s) ⊞ C(t) → C^small(s, t) → 0`, with maps
  `(inc_s, -inc_t)` and the sum, and `shortExact_of_bicartSq` the same for any bicartesian square.
- Connecting map: `bicartδ R sq n : H_{n+1}(A₄) ⟶ H_n(A₁)` is the connecting map of this sequence.
  Its sign is `bicartδ_eq` (generally `mvShortComplex_δ_eq`): if a cycle of `A₄` is `a + b` with
  `a` a chain of `A₂` and `b` a chain of `A₃`, and `x` is the chain of `A₁` with image `∂a` in `A₂`,
  then `bicartδ` sends the class of `a + b` to the class of `x`. `bicartδ_flip` (generally
  `mvShortComplex_δ_flip`) states `bicartδ R (bicartSq_flip sq) n = -bicartδ R sq n` for all
  coefficients, and `bicartδ_naturality` is naturality for simplicial maps `φᵢ : Aᵢ ⟶ Aᵢ'` commuting
  with the four inclusions.
- Iteration criterion: for complexes of modules over a ring `k : Type u` in `ModuleCat.{u} k`,
  indexed by any `ComplexShape`, `quasiIso_of_iterate_mem` proves `QuasiIso i` for a monomorphism
  `i : A ⟶ B`, a chain map `S : B ⟶ B` and a homotopy `T : Homotopy S (𝟙 B)` such that `S` and the
  components of `T` carry the image of `i` into the image of `i`, and every chain of `B` is
  carried into the image of `i` by some iterate of `S`, the number of iterations depending on the
  chain. The proof uses the composite homotopies `S^N ≃ 𝟙`.

`TDA.Topology.SingularMayerVietorisExamples` (imported by `TDA.Topology.Examples`) covers the
open rays `(-∞, 1)` and `(0, ∞)` of `ℝ`, which cover the line (`lowerRay_union_upperRay`): constant
simplices at `1/2` and `2` lie in the intersection and in the upper ray only, the affine segment
from `2` to `-1` is not small (`segmentSimplex_not_mem_smallSimplices`), and the sequence of
small chains is short exact over `ℚ` with first map `(inc, -inc)` (`shortExact_rays`). Over `ℚ`,
`bicartδ_flip_ne` shows that the flipped connecting map differs from a nonzero connecting map,
and `quasiIso_zero_of_homotopy` applies the iteration criterion with `S = 0` and the zero
subcomplex to a complex with a homotopy `0 ≃ 𝟙`.

## Closed-band functors on `D⁺(Sh(ℝ; k))`

`TDA.Sheaf.DerivedPlus` works with sheaves of modules `X.Sheaf (ModuleCat k)` over a ring `k`
on `X : TopCat` and their bounded below derived categories `DerivedCategory.Plus`. Each
derived category structure is an instance argument `[HasDerivedCategory (X.Sheaf (ModuleCat k))]`;
the fixtures use Mathlib's `HasDerivedCategory.standard` as a local instance.

- `pullbackPlus k f` is the right derived functor of the exact inverse image `f⁻¹`
  (`pullback_preservesFiniteLimits`, `pullback_additive`); its comparison maps are invertible
  (`isIso_rightDerivedFunctorPlusUnit_of_exact`, `isIso_rightDerivedFunctorPlusUnith_of_exact`).
  `pushforwardPlus k f` is the derived direct image `Rf_*`.
- `pushforwardPlusComp k f g : R(f ≫ g)_* ⟶ Rf_* ⋙ Rg_*` is invertible
  (`isIso_pushforwardPlusComp`, `pushforwardPlusCompIso`), and `pullbackPlusCompIso k f g :
  g⁻¹ ⋙ f⁻¹ ≅ (f ≫ g)⁻¹` comes from the underived `pullbackCompIso`. Both are associative
  (`pushforwardPlusComp_assoc_app`, `pullbackPlusCompHom_assoc_app`,
  `pullbackPlusCompIso_hom_assoc_app`; underived `pullbackCompIso_assoc`), with
  characterizations on `Q K` (`pushforwardPlusComp_fac_app`, `pullbackPlusCompHom_fac_app`,
  `pullbackPlusCompIso_hom_fac_app`).
- `derivedUnit k f : 𝟭 ⟶ pullbackPlus k f ⋙ pushforwardPlus k f` is the termwise sheaf
  adjunction unit followed by the comparisons (`derivedUnit_app_Q`). It is invertible along a
  homeomorphism (`isIso_derivedUnit`, via `pushforwardEquivalence`) and coherent with
  composition (`derivedUnit_comp_app`, `derivedUnit_comp_app'`).
- `corrRestr k j p q : p⁻¹ ⋙ Rq_* ⟶ (j ≫ p)⁻¹ ⋙ R(j ≫ q)_*` restricts a correspondence
  transform along `j` (`corrRestr_app`); `corrRestr_id`, `corrRestr_comp` and `isIso_corrRestr`
  give identity, composition and invertibility along an isomorphism.

`TDA.Sheaf.BandConvolution` specializes to the closed bands `D a = {(x, y) | dist x y ≤ a}` with
projections `p a`, `q a`, both proper (`isProperMap_p`, `isProperMap_q`), closed inclusions
`incl h` for `h : a ≤ b` (`isClosedEmbedding_incl`, `incl_p`, `incl_q`) and the shear
homeomorphism `shear a : band a ≃ₜ Set.Icc (-a) a × ℝ` (`shear_snd`, `shear_add`). The derived
categories of the real line and of every band are instance arguments.

- `T k a := pullbackPlus k (p a) ⋙ pushforwardPlus k (q a)`, the functor `F ↦ R(q_a)_* p_a⁻¹ F`.
- `restr k h : T k b ⟶ T k a` is `corrRestr` along `incl h` (`restr_app`), with
  `restr_refl : restr k (le_refl a) = 𝟙 _` and
  `restr_trans : restr k hbc ≫ restr k hab = restr k (hab.trans hbc)`.
- `T0Iso k : T k 0 ≅ 𝟭 _` uses `p_zero_eq_q_zero` and the homeomorphism `q 0` (`isIso_q_zero`,
  inverse `diagonalZero`); `T0Iso_inv` identifies its inverse with the derived unit of `q 0`.
- `aug k h : T k a ⟶ 𝟭 _` for `h : 0 ≤ a` is `restr k h ≫ (T0Iso k).hom`, with `aug_zero` and
  `restr_comp_aug`.

`TDA.Sheaf.BandConvolutionExamples` checks `a = 0` (`T0Iso`, `aug_zero`) and `a = b`
(`restr_refl`) over `ℚ` and `ZMod 2`, the chain `0 ≤ 1 ≤ 2` for `restr_trans` and
`restr_comp_aug`, and that `q 1` identifies `(0, 0)` with `(1, 0)`, so it is not an isomorphism.

## Stratifications of the real line

`TDA.Sheaf.RealStratification` works on `realLine := TopCat.of ℝ` with strictly increasing
breakpoints `p : Fin m → ℝ` and their set `breakpoints p`. The strata are numbered by the
vertices of `Vertex (orient m)` from `TDA.Sheaf.AlternatingDiagram`: the even vertex `2j` is the
open cell `(p_{j-1}, p_j)` (with `p_{-1} = -∞` and `p_m = +∞`) and the odd vertex `2i+1` is the
point `p_i`.

- `orient m` points every arrow from a point to an adjacent cell (`arrow_orient_iff`), so the
  free category is thin: the instance `paths_hom_subsingleton`.
- `IsBasicOpen S U` for a finite `S : Finset ℝ`: `U` is a nonempty order-connected open set and
  `U ∩ S` is a subsingleton. These opens form a basis (`isBasis_basicOpen`,
  `isBasis_range_basicOpen`) closed under nonempty intersections (`IsBasicOpen.inf`).
  `Basic S` is their type, `BasicCat S` the full subcategory of `Opens realLine`
  (`basicCat_hom_subsingleton`), `basicIncl S` the inclusion, cover-dense by
  `basicIncl_isCoverDense`, and `basicTopology S` the induced Grothendieck topology.
- `star p v` is the cell `2j` itself or the open star `(p_{i-1}, p_{i+1})` of the point `2i+1`
  (`mem_star`, `apply_mem_star_iff`, `apply_mem_star`); every star is basic
  (`isBasicOpen_star`), and an arrow `v → w` gives `star p w ≤ star p v`
  (`star_le_star_of_arrow`). Membership in the breakpoints: `mem_breakpoints`,
  `apply_mem_breakpoints`.
- `tau p U` is the stratum of a basic open `U`, characterised by `tau_eq_iff`: `U ≤ star p v`
  and `star p v ∩ breakpoints p = U ∩ breakpoints p`. Its laws are `le_star_tau`,
  `star_tau_inter`, `tau_star`, `tau_eq_of_le_of_inter_eq` and `tau_eq_or_arrow` (an inclusion
  keeps the stratum or follows one arrow from a point to a cell); `exists_star_tau` collects
  them. `tauFunctor hp : (BasicCat (breakpoints p))ᵒᵖ ⥤ Paths (Vertex (orient m))` has
  `tauFunctor_obj` and sends inclusions with the same breakpoints to isomorphisms
  (`isIso_tauFunctor_map`).
- `isSheaf_basic_of_isIso_sameStratum`: a presheaf `P : (BasicCat S)ᵒᵖ ⥤ A`, in any category
  `A`, that inverts every inclusion `U ⊆ V` with `U ∩ S = V ∩ S` satisfies
  `Presheaf.IsSheaf (basicTopology S) P`. Hence `isSheaf_tauFunctor_comp`: `tauFunctor hp ⋙ M`
  is a sheaf for every `M : Paths (Vertex (orient m)) ⥤ A`.
- `basisEquiv S k : Sheaf (basicTopology S) (ModuleCat.{0} k) ≌
  Sheaf (Opens.grothendieckTopology realLine) (ModuleCat.{0} k)` for a ring `k : Type` is
  Mathlib's `Functor.sheafInducedTopologyEquivOfIsCoverDense` for this basis; its functor is
  the right Kan extension along `basicIncl S`.

`TDA.Sheaf.RealStratificationExamples` checks zero breakpoints (`star_fin_zero`,
`isBasicOpen_top_fin_zero`, `tau_fin_zero`) and the breakpoint `p₁ = 0` with strata
`0 ← 1 → 2`: the stars `(-∞, 0)`, `ℝ`, `(0, ∞)` (`coe_star_p₁_zero`, `coe_star_p₁_one`,
`coe_star_p₁_two`) and the strata of `(-2, -1)`, `(-1, 1)`, `(-1, 3)` and `(1, 2)` (`tau_left`,
`tau_center`, `tau_wide`, `tau_right`, via `tau_ioo_eq`). The constant presheaf is a sheaf on
the basis (`isSheaf_const`) and extends to `constLineSheaf` with the field as sections over
every basic open (`constLineSheafSectionsIso`). The point diagram `pointDiagram`, the field on
`pointSegment = {1}`, read through `tauFunctor` is a sheaf (`isSheaf_point`); its extension
`pointLineSheaf` has sections `pointLineSheafSectionsIso` of dimension one over `(-1, 1)`
(`finrank_pointLineSheaf_center`) and zero over `(1, 2)` (`finrank_pointLineSheaf_right`).

## Interval-local constancy on the real line

`TDA.Sheaf.LocalSystem` treats sheaves `F : TopCat.Sheaf (ModuleCat.{0} k) realLine` for a ring
`k : Type`. A convex open is an open `V` with `(V : Set ℝ).OrdConnected`.

- `IsLocallyConstantOn F U` for `U : Set ℝ`: every `x ∈ U` has an open `N ⊆ U` containing `x`
  such that `F(W) ⟶ F(V)` is an isomorphism for all nonempty convex opens `V ⊆ W ⊆ N`.
  `IsLocallyConstantOn.mono` passes it to open subsets.
  **Limitation:** this definition is intended to be equivalent, on `ℝ`, to "locally isomorphic
  to a constant sheaf", but that equivalence is not yet proved in Lean; the bridge is follow-up
  #1250. Whether the definition agrees with the one in the source article has not been checked.
- `restrict_isIso_of_isLocallyConstantOn`: if `F` is locally constant on a convex open `W`,
  then `F(W) ⟶ F(V)` is an isomorphism for every nonempty convex open `V ⊆ W`. The proof glues
  along the binary sheaf square (`TopCat.Sheaf.isLimitPullbackCone`), propagates along `W` with
  `IsPreconnected.induction₂'`, and concludes with `TopCat.Sheaf.existsUnique_gluing'` and
  `TopCat.Sheaf.eq_of_locally_eq'`. The gluing step is public as `isIso_map_of_le_sup`: for
  opens `A, B ⊆ D ⊆ A ∪ B` in any topological space and any coefficient category, if
  `F(B) ⟶ F(A ∩ B)` is an isomorphism then so is `F(D) ⟶ F(A)`.
- `transportIso F hWc hF h₁ h₂ … : F(V₁) ≅ F(V₂)` for nonempty convex `V₁, V₂ ⊆ W` is the
  inverse restriction to `V₁` followed by restriction to `V₂`. `map_comp_transportIso_hom`
  states its compatibility with restriction from `W`, `transportIso_hom_eq_map` that it is
  restriction when `V₂ ⊆ V₁`, and `transportIso_trans` that it composes.
- `isIso_germ_of_isIso_map`: for a presheaf of `k`-modules on `realLine`, if `F(T) ⟶ F(V)` is an
  isomorphism for every convex open neighbourhood `V ⊆ T` of `x`, the germ `F(T) ⟶ F_x` is an
  isomorphism. `isIso_germ_of_isLocallyConstantOn` applies it: if `F` is locally constant on a
  convex open `W`, then `F(W) ≅ F_x` for every `x ∈ W`.

`TDA.Sheaf.RealStratification.isIso_map_basisEquiv` reads restriction isomorphisms of a sheaf
extended by `basisEquiv` off its basis presheaf, and `RealStratification.isBasicOpen_empty` says
nonempty convex opens are basic without breakpoints.
`TDA.Sheaf.LocalSystemExamples` uses the sheaves of `TDA.Sheaf.RealStratificationExamples`. The constant sheaf `constLineSheaf k ∅` is locally constant on the whole line
(`isLocallyConstantOn_constLineSheaf`); the trivialisation gives `isIso_constLineSheaf_map_ioo`
and one-dimensional stalks (`finrank_stalk_constLineSheaf`). The point sheaf `pointLineSheaf` is
locally constant on the cell `(0, ∞)` (`isLocallyConstantOn_pointLineSheaf_Ioi`), with zero stalk
at `3/2` (`finrank_stalk_pointLineSheaf_right`), but not on the whole line
(`not_isLocallyConstantOn_pointLineSheaf_univ`): the trivialisation would identify its
one-dimensional sections over `(-1, 3)` (`finrank_pointLineSheaf_wide`) with its zero sections
over `(1, 2)`.

## Constructible sheaves on the real line

`TDA.Sheaf.RealConstructible` works with sheaves `F : TopCat.Sheaf (ModuleCat.{0} k) realLine`
for `k : Type`, strictly increasing breakpoints `p : Fin m → ℝ` (`hp : StrictMono p`) and the
strata, stars and basic opens of `TDA.Sheaf.RealStratification`, with `S = breakpoints p`.

- `IsConstructible S F` for a division ring `k`: `IsLocallyConstantOn F (↑S)ᶜ` and every stalk
  `F.presheaf.stalk x` is finite-dimensional.
  **Limitation:** local constancy here is the interval-local `IsLocallyConstantOn` of
  `TDA.Sheaf.LocalSystem`. It is intended to be equivalent, on `ℝ`, to "locally isomorphic to a
  constant sheaf", but that equivalence is not yet proved in Lean; the bridge is follow-up
  #1250.
- `isIso_res_sameStratum` (a ring `k` suffices): if `F` is locally constant on `(↑S)ᶜ`, then
  `F(V) ⟶ F(U)` is an isomorphism for basic opens `U ⊆ V` with `U ∩ S = V ∩ S`. Without a
  breakpoint this is `restrict_isIso_of_isLocallyConstantOn`; with a breakpoint `s` two binary
  gluings (`isIso_map_of_le_sup`) extend across `s` from `V ∩ (-∞, s)` and `V ∩ (s, ∞)`.
- `isConstructible_iff`: `IsConstructible S F` holds exactly when `F` inverts these inclusions
  and `F(U)` is finite-dimensional for every basic open `U`. The stalk at `x` is read on a basic
  open meeting `S` at most in `x`, through `isIso_germ_of_isIso_map`.
- The section functor `sections k p : TopCat.Sheaf (ModuleCat.{0} k) realLine ⥤
  Diagram k (orient m)` for a field `k` is restriction along `starFunctor p`. Pinned equations:
  `sections_obj_obj`, `(Γ F)(v) = F(star p v)`; `sections_map_gen`, `(Γ F)(gen h)` is the
  restriction `F(star p v) ⟶ F(star p w)` along `star_le_star_of_arrow`.
- The extension functor `extension k hp : Diagram k (orient m) ⥤
  TopCat.Sheaf (ModuleCat.{0} k) realLine` is `basisSheaf k hp` (the diagram composed with
  `tauFunctor hp`, a sheaf on the basis by `isSheaf_tauFunctor_comp`) followed by the functor of
  `basisEquiv`. `extensionBasicIso : (Φ M)(U) ≅ M(tau p U)` for basic `U`, and
  `extensionStarIso : (Φ M)(star p v) ≅ M v`. `isConstructible_extension`: `Φ M` is
  constructible when every `M.obj X` is finite-dimensional; `finiteDimensional_sections`: `Γ F`
  has finite-dimensional values when `F` is constructible.
- The counit `extensionSectionsIso : extension k hp ⋙ sections k p ≅ 𝟭 _` has components
  `extensionStarIso` (`extensionSectionsIso_app_app`). The unit
  `sectionsExtensionIso : ObjectProperty.ι _ ≅ ObjectProperty.ι _ ⋙ sections k p ⋙ extension k hp`
  on constructible sheaves is built from the counit of `basisEquiv` and the restrictions
  `F(star p (tau p U)) ⟶ F(U)` on basic opens, which are isomorphisms by
  `isIso_res_sameStratum`.
- `Constructible k p` and `FinDiagram k m` are the full subcategories of constructible sheaves
  and of diagrams with finite-dimensional values; `sectionsFin` and `extensionFin` are `Γ` and
  `Φ` between them, and `equivalence k hp : Constructible k p ≌ FinDiagram k m`
  (`Equivalence.mk` of the unit and counit above). `equivalence_functor_obj_obj` and
  `equivalence_inverse_obj_obj` identify its functors with `Γ` and `Φ`, and
  `equivalence_functor_obj_map_gen` gives the map equation through the equivalence.

The comparison with derived categories is not covered here; it is #1183.

`TDA.Sheaf.RealConstructibleExamples` covers three cases. The one-breakpoint sheaves are built
with `Φ` from interval diagrams; only the zero-breakpoint constant sheaf and Mathlib's skyscraper
are sheaves defined independently of `Φ`.

- No breakpoints (`p₀`, `p₀_strictMono`, `breakpoints_p₀`, `star_p₀`): constructible means
  locally constant on `ℝ` with finite-dimensional stalks (`isConstructible_p₀_iff`), `Γ F` is
  `F(ℝ)` (`sections_p₀`), and two constructible sheaves with isomorphic global sections are
  isomorphic (`nonempty_iso_of_iso_top`). The extension `constSheaf₀` of the one-vertex
  interval is constructible (`isConstructible_constSheaf₀`) with one-dimensional global
  sections (`finrank_constSheaf₀_top`).
- One breakpoint `p₁ = 0`, strata `0 ← 1 → 2` (`arrow_one_zero`, `arrow_one_two`): for every
  interval `J`, `intervalSheaf k J = Φ (interval J)` is constructible
  (`isConstructible_intervalSheaf`), `Γ (intervalSheaf k J) ≅ interval J`
  (`sectionsIntervalSheafIso`), its sections over the star of `v` have dimension one exactly on
  `J` (`finrank_intervalSheaf_star`), and restriction from the star of the point to a cell
  outside `J` is not invertible (`not_isIso_intervalSheaf_map`). The segments `segLeft = [0, 1]`
  and `segRight = [1, 2]` give `leftClosed` (the field on `(-∞, 0]`, dimensions `1, 1, 0`,
  `finrank_leftClosed`) and `rightClosed` (the field on `[0, ∞)`, `finrank_rightClosed`), with
  one noninvertible restriction each, on opposite sides (`not_isIso_leftClosed_right`,
  `not_isIso_rightClosed_left`); `pointSheaf` for `[1, 1]` has two
  (`not_isIso_pointSheaf`).
- Mathlib's skyscraper `sky k = skyscraperSheaf 0 (ModuleCat.of k k)` has sections `k` over
  opens containing `0` (`skyObjIso`) and zero sections elsewhere (`isZero_sky_obj`); it is
  constructible for `{0}` (`isConstructible_sky`), `Γ (sky k) ≅ interval [1, 1]`
  (`sectionsSkyIso`), and hence it is isomorphic to `pointSheaf` as a constructible sheaf
  (`skyIsoPointSheaf`).

## Flasque sheaves and section lifting on intervals

`TDA.Sheaf.SheafFlasque` treats sheaves of modules `X.Sheaf (ModuleCat k)` over a ring
`k : Type` on `X : TopCat.{0}`, with Mathlib's `TopCat.Sheaf.IsFlasque` (all restriction maps
are epimorphisms).

- `isFlasque_of_injective`: an injective sheaf is flasque. Its underlying presheaf is injective
  (`presheaf_isFlasque_of_injective` treats presheaves); a section over `U` is classified by a
  morphism out of the free presheaf `yoneda.obj U ⋙ ModuleCat.free k`, and for `U ≤ V` the
  induced map of free presheaves is a monomorphism (private helpers modelling Mathlib's
  `CategoryTheory.Presheaf.freeYoneda`).
- `GermSurjective k F`: every germ of `F` at `x` is the germ of a section over every open
  neighbourhood of `x`. It holds for flasque sheaves (`germSurjective_of_isFlasque`), hence for
  injective ones (`germSurjective_of_injective`), and passes to quotients
  (`germSurjective_of_epi`).
- `exists_local_preimage_of_exact`: along an exact complex `X₁ ⟶ X₂ ⟶ X₃`, a section of `X₂`
  that maps to zero comes from `X₁` near every point.
- Restriction identities on sections: `presheaf_map_map_apply`, `sheafHom_naturality_apply`,
  `shortComplex_g_f_apply`, and `exists_glue₂`, which glues two sections that agree on the
  intersection of their opens.

`TDA.Sheaf.IntervalSections` works on a subspace `S ⊆ ℝ`, as `TopCat.of S`, with the opens
`openIoo S p q = S ∩ (p, q)` (`mem_openIoo`, `openIoo_le_openIoo`, `exists_openIoo_le`). Let
`X₁ ⟶ X₂ ⟶ X₃` be exact with `X₁` germ-surjective, and let `s` be a global section of `X₃` that
lifts to `X₂` near every point.

- `exists_section_lift_extend` (order-connected `S`): for `l < a' < a` with `a' ∈ S` and
  `b ∈ S`, a lift of `s` over `openIoo S l a` extends to a lift over `openIoo S l t` for some
  `t > b`, unchanged over `openIoo S l a'`. Open and half-open intervals are not treated; the
  agreement clause is what a countable gluing of this step needs.
- `exists_section_lift_Icc`: on `[u, v]`, `s` lifts to a global section of `X₂`, for all `u`
  and `v` (the empty interval included).
- `sections_exact_Icc`: for `L₀ ⟶ L₁ ⟶ L₂ ⟶ L₃` on `[u, v]`, exact at `L₁` and `L₂` with `L₀`
  germ-surjective, global sections are exact at `Γ(L₂)`.

`TDA.Sheaf.IntervalSectionsExamples` works over `ℚ` on `I01 = [0, 1]`: the skyscraper `sky` at
`mid = 1/2` is flasque and germ-surjective (`sky_isFlasque`, `germSurjective_sky`); an
injective sheaf `Injective.under F` is flasque (`isFlasque_under`) and the cokernel of
`Injective.ι F` is germ-surjective (`germSurjective_cokernel_ι`); for the constant sheaf `K`,
every global section lifts along `sky ⊞ K ⟶ K` (`constant_section_lift` from
`sections_exact_Icc`, `constant_section_lift_of_local` from `exists_section_lift_Icc`); and the
lifting statement holds on the empty interval `[1, 0]` (`empty_section_lift`).

## Cohomology of compact intervals

Let `k : Type` be a ring. `pt` is the one-point space in `TopCat.{0}` and `toPt X : X ⟶ pt`
the unique map. For `X : TopCat.{0}` and a sheaf `G` of `k`-modules on `X`, `Hⁱ(X; G)` is
`(DerivedCategory.Plus.homologyFunctor _ i).obj ((pushforwardPlus k (toPt X)).obj
((DerivedCategory.Plus.singleFunctor _ 0).obj G))`, a sheaf of `k`-modules on `pt`. Derived
categories are instance arguments.

`TDA.Sheaf.StalkPullback`, for a continuous `f : X ⟶ Y` and a sheaf `F` of `k`-modules on `Y`:

- `stalkPullbackSheafIso k f F x : F_{f x} ≅ (f⁻¹ F)_x`, the stalk of the sheaf inverse image
  `TopCat.Sheaf.pullback (ModuleCat k) f`.
- `stalkPullbackSheafIso_unit` (elementwise) and `germ_stalkPullbackSheafIso_hom`: the germ at
  `f x` of a section over `V` goes to the germ at `x` of its image under the adjunction unit
  `F ⟶ f_* f⁻¹ F`. `pullbackPushforwardAdjunction_unit_app_hom` describes that unit through the
  presheaf adjunction and sheafification.
- `stalkPullbackSheafIso_hom_naturality` (with `_assoc`): for `φ : F ⟶ G`, the stalk map of `φ`
  at `f x` corresponds to the stalk map of `f⁻¹ φ` at `x`. `stalkPullbackSheafNatIso k f x` is
  the natural isomorphism `Sheaf.forget ⋙ stalkFunctor (f x) ≅ f⁻¹ ⋙ Sheaf.forget ⋙
  stalkFunctor x` of functors `Sh Y ⥤ ModuleCat k`, with components `stalkPullbackSheafNatIso_app`.

`TDA.Sheaf.DerivedStalks`: `isIso_iff_isIso_stalk_homology φ`, for a morphism `φ` of
`DerivedCategory.Plus (X.Sheaf (ModuleCat k))`: `φ` is an isomorphism if and only if, for every
`i : ℤ` and `x : X`, the stalk at `x` of the homology sheaf map `Hⁱ(φ)` is an isomorphism. It
combines `DerivedCategory.Plus.isIso_iff` with `TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso`.
It is stated for `X : TopCat.{0}`, `ModuleCat.{0} k` and `k : Type`, as in the rest of this
area.

`TDA.Sheaf.DerivedStalksExamples` works over `ℚ` with `HasDerivedCategory.standard` as a local
instance. `shift` is the translation `x ↦ x + 1` of `realLine`, a homeomorphism (`isIso_shift`);
`skyR` is the skyscraper at `1` with value `ℚ` and `skyShift` its inverse image along `shift`.
The stalk of `skyShift` at `0` is `ℚ` (`stalk_skyShift_zero`) and at `5` is zero
(`isZero_stalk_skyShift_five`); `stalk_skyShift_naturality` is naturality at `2 • 𝟙 skyR`; and
the stalk maps of the homology sheaf maps of the derived unit of `shift` at `skyR` are
isomorphisms (`isIso_stalk_homology_derivedUnit_shift`).

`TDA.Sheaf.PointSheaf`:

- `germ_top_bijective`: for a sheaf on `pt`, the germ map from global sections is bijective.
  Hence `exact_of_sections_top` (a complex on `pt` is exact when its global sections are) and
  `isIso_of_bijective_app_top` (a morphism bijective on global sections is an isomorphism).
- `constSh k X N := (toPt X)⁻¹ N` for `N : pt.Sheaf (ModuleCat k)`; `germSurjective_constSh`:
  every germ is the germ of a global section.

`TDA.Sheaf.RightDerivedHomology`, for an additive `F : C ⥤ D`, `C` with enough injectives:

- `homologyRightDerivedIsoOfInjective F K i : Hⁱ(RF(K)) ≅ Hⁱ(F K)` for a bounded below complex
  `K` of injective objects, and `homologyRightDerivedIsoOfQuasiIso F j i` through a
  quasi-isomorphism `j : K₀ ⟶ K` to such a complex.
- `isIso_Q_map_comp_rightDerivedFunctorPlusUnit`: for a quasi-isomorphism `j : A ⟶ B` to a
  bounded below complex of injective objects, `Q u` followed by the comparison
  `F A ⟶ RF(A)` is invertible when `u ≫ F j` is a quasi-isomorphism.
- `singlePlus n X`, the object `X` in degree `n` as a bounded below complex, and
  `singleFunctorIsoQ n X` comparing it with `DerivedCategory.Plus.singleFunctor _ n`.

`TDA.Sheaf.IntervalCohomology`, on `[u, v]` as `TopCat.of (Set.Icc u v)`:

- `isZero_H_Icc`: `Hⁱ([u, v]; G) = 0` for `2 ≤ i`, every sheaf `G` and all `u`, `v`.
- `isZero_H_constSh_Icc`: `Hⁱ([u, v]; constSh k _ N) = 0` for `1 ≤ i`, all `u`, `v`.
- `isIso_unit_constSh_Icc` (`u ≤ v`): the adjunction unit `N ⟶ (toPt _)_* constSh k _ N` is an
  isomorphism.
- `isIso_derivedUnit_toPt_Icc` (`u ≤ v`): the derived unit `derivedUnit k (toPt _)` is an
  isomorphism at `N` in degree `0`, for every sheaf `N` of `k`-modules on `pt`.

The proofs read `Hⁱ` off an injective resolution, and use `sections_exact_Icc` with
`germSurjective_of_injective` in degrees `≥ 2` and `germSurjective_constSh` in degree `1`; `H⁰`
of a constant sheaf follows from the connectedness of `[u, v]`.

`TDA.Sheaf.IntervalCohomologyExamples` works over `ℚ` with `HasDerivedCategory.standard` as a
local instance. With `kpt`, the sheaf on `pt` with value `ℚ`, the derived unit on `I01 = [0, 1]`
is an isomorphism (`isIso_derivedUnit_kpt`), giving `H⁰([0, 1]; constSh kpt) ≅ kpt`
(`H0_constSh_kpt`) and `H¹ = 0` (`isZero_H1_constSh_kpt`); the same unit statement holds on
`[1, 1]` (`isIso_derivedUnit_kpt_singleton`). `H²` vanishes for the skyscraper `sky` at `1/2`
(`isZero_H2_sky`) and for every sheaf on the empty interval `[1, 0]` (`isZero_H2_empty`). The
stalk of `constSh kpt` at `1/2` is `ℚ` (`stalk_constSh_kpt`).

`TDA.Sheaf.IntervalFibre` transports cohomology along homeomorphisms and applies it to the
fibres of the band projection `BandConvolution.q a`:

- `rightDerivedFunctorPlusSingleIso F n A` (in `TDA.Sheaf.RightDerivedHomology`): for an exact
  functor `F`, the right derived functor on `D⁺` sends `A` in degree `n` to `F A` in degree `n`.
- `comp_toPt h : h ≫ toPt Y = toPt X`.
- `H_iso_of_homeo h G i : Hⁱ(X; G) ≅ Hⁱ(Y; h_* G)` for a homeomorphism `h : X ⟶ Y`, through
  `pushforwardPlusCompIso k h (toPt Y)` and `rightDerivedFunctorPlusSingleIso` for the
  equivalence `h_*`.
- `isIso_derivedUnit_toPt_app_of_homeo h M`: the derived unit of `toPt X` is invertible at `M`
  when that of `toPt Y` is (`derivedUnit_comp_app'`).
- `isIso_toPt_Icc_self u` (an instance): `[u, u]` is homeomorphic to the point; hence
  `isIso_derivedUnit_toPt_Icc_self`, the derived unit of `toPt` on `[u, u]` is invertible.
- `BandConvolution.fibre a y` is the fibre `(q a)⁻¹ {y}` as a `TopCat.{0}`, and
  `fibreHomeo a y : (q a)⁻¹ {y} ≃ₜ [y - a, y + a]` is the first coordinate
  (`coe_fibreHomeo_apply`); `fibreIso a y` is the isomorphism in `TopCat`, with
  `fibreIso_toPt`.
- `isZero_H_fibre`: `Hⁱ((q a)⁻¹ {y}; G) = 0` for `2 ≤ i`, every sheaf `G` and all `a`, `y`.
- `isIso_derivedUnit_toPt_fibre` (`0 ≤ a`): the derived unit `N ⟶ RΓ((q a)⁻¹ {y}; constSh N)`
  is an isomorphism for every sheaf `N` of `k`-modules on `pt`.

`TDA.Sheaf.IntervalFibreExamples` works over `ℚ` with `HasDerivedCategory.standard` as a local
instance. `fibreHomeo 1 0` sends `half = (1/2, 0)` to `1/2` (`fibreHomeo_half`), and the fibre of
`q (-1)` is empty (`isEmpty_fibre_neg`). On the fibre `(q 1)⁻¹ {0} ≅ [-1, 1]` the derived unit at
`kpt` is an isomorphism (`isIso_derivedUnit_kpt_fibre`), so `H⁰ ≅ kpt` (`H0_constSh_kpt_fibre`);
the same unit statement holds on the one-point fibre `(q 0)⁻¹ {y}`
(`isIso_derivedUnit_kpt_fibre_zero`), and on `[2, 2]` the derived unit of `toPt` is invertible
(`isIso_derivedUnit_Icc_two`). For the skyscraper `skyHalf` at `half`, `H²` vanishes
(`isZero_H2_skyHalf`) and `H¹` is transported to `[-1, 1]` (`H1_skyHalf_iso`).

## Flasque acyclicity

`TDA.Sheaf.FlasqueAcyclic` treats sheaves of modules `X.Sheaf (ModuleCat k)` over a ring
`k : Type` on `X : TopCat.{0}`. At the pinned Mathlib, `TopCat.Sheaf.IsFlasque.epi_of_shortExact`
and its corollary are stated for sheaves of abelian groups only.

- `sections_exact_of_left_exact`: along an exact complex `X₁ ⟶ X₂ ⟶ X₃` with `X₁ ⟶ X₂` a
  monomorphism, a section of `X₂` over `U` that maps to zero comes from `X₁` over `U`.
- `epi_of_shortExact`: for a short exact sequence `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` with `X₁` flasque,
  `X₂(U) ⟶ X₃(U)` is an epimorphism (surjective) for every open `U` (Mathlib's Zorn argument).
- `isFlasque_of_shortExact`: if `X₁` and `X₂` are flasque, so is `X₃`.
- `isFlasque_of_iso`, `isFlasque_of_isZero`, `isFlasque_of_id_eq_add` (a sheaf with
  `𝟙 = p₁ ≫ i₁ + p₂ ≫ i₂` through flasque sheaves) and the instance `isFlasque_biprod`.
- `pushforward_shortExact_of_isFlasque`: for a continuous `f`, `f_*` keeps a short exact sequence
  with flasque first term short exact.
- `acyclic_pushforward_of_isFlasque`: `f_*` keeps a bounded below acyclic complex of flasque
  sheaves acyclic; `quasiIso_pushforward_of_isFlasque`: `f_*` keeps a quasi-isomorphism between
  bounded below complexes of flasque sheaves a quasi-isomorphism.
- `isIso_rightDerivedFunctorPlusUnit_app_of_isFlasque`: for a bounded below complex `K` of
  flasque sheaves (`CochainComplex.Plus`), the comparison `f_* K ⟶ Rf_* K` on `D⁺` is an
  isomorphism; `isIso_rightDerivedFunctorPlusUnit_app_toPt_of_isFlasque` is the case
  `f = toPt X` of global sections.

`TDA.Sheaf.FlasqueAcyclicExamples` works over `ℚ` on `I01 = [0, 1]` with
`HasDerivedCategory.standard` as a local instance. For the skyscraper `sky` at `1/2` and its
embedding into `Injective.under sky`, the cokernel sequence `embSc` is short exact
(`embSc_shortExact`); sections surject onto the cokernel over every open
(`surjective_cokernel_π`), the cokernel is flasque (`isFlasque_cokernel`) and global sections
keep `embSc` short exact (`shortExact_pushforward_embSc`). For `skyPlus = singlePlus 0 sky`, the
comparison is an isomorphism along the inclusion `ι : [0, 1] ⟶ ℝ` (`isIso_unit_skyPlus_ι`) and
for global sections (`isIso_unit_skyPlus_toPt`).

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
claimed. The categorical Mapper–Reeb quotient identification and convergence
results also cover constructible real-valued inputs under their explicit
constructibility and cover hypotheses. They do not cover arbitrary spaces or
multidimensional-valued Reeb spaces.

Finite GH–Rips stability and sampling compare full diagrams of finite metric spaces;
the possibly infinite sampling target has no diagram in these results; the q-tame Rips
diagrams above supply diagrams and sample convergence for totally bounded targets. Finite
weighted boundary transport permits real masses, and its canonical atomic
measures have the same optima over all Borel boundary plans, and minimizing Borel plans exist
for arbitrary finite Borel inputs and `p ≥ 1` (`BoundaryTransport.exists_minimizing_boundaryPlan`),
with no moment or support hypothesis. Finite-line adapters construct modules
over a ring; rectangular matrix-sequence adapters require a commutative ring. Over a field, both reuse
finite interval classification without computing barcodes over arbitrary fields. Gaussian
C₀ universality and signed-measure separation concern the full birth–death plane;
positive persistence measures require a strictly positive weight and finite weighted
mass. These conclusions do not make finite-pixel images characteristic.

General geometric tame-function PH stability, manifold charts and executable
arbitrary-field decomposition are outside the reviewed PH scope. Locally finite decorated
diagrams of q-tame modules and their algebraic stability are proved, but are not covered by
the source-based review above. A first
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

`BoundaryTransportGeometryCore` is the canonical reusable import; it retains the
arbitrary interior geometry, density and small-positive-boundary-distance results.
`BoundaryTransportGeometryExamples` contains the fixed far-point witnesses. The old
`BoundaryTransportGeometry` import continues to expose both modules.

`TDA.Persistence.BoundaryPlans` uses Borel measures on closed-half-plane pairs
outside the diagonal–diagonal region. Their two interior marginals are prescribed;
boundary marginals are free. Every admissible plan has mass at most the sum of
the input masses. The explicit deletion/insertion plan sends each bar to its
nearest diagonal point and has cost equal to the sum of the diagonal persistence
moments. Finite moments therefore give a finite-cost competitor and a finite
powered infimum over all admissible plans. The simp lemmas
`interiorIncl_mem_image` and `diagonalProjection_not_mem_image` support basic
fiber-membership proofs by identifying interior-inclusion membership and
excluding diagonal projections. `BoundaryPlanLaws` proves self-value
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


`BoundaryTransportReverseCore` is the canonical reusable reverse-plan import and
exports `Reverse.boundaryPlan_add`. Its `Reverse.boundaryPlan_dirac_points_cost`
states the actual selected plan cost for any real exponent: the `≤` case retains
the direct leg at a tie. This is not an optimal-cost formula. Fixed far atoms and
their cost calculations live in `BoundaryTransportReverseExamples`. The old
`BoundaryTransportReverse` import keeps its prior declarations and types, and
continues to provide Geometry through its imports.

`ReservoirNormalization` proves the probability scaling law by multiplying every
competitor measure by the reciprocal capacity and reversing that operation.
The powered value scales by the capacity; for positive p its root scales by
the capacity raised to 1/p. Together with the comparison theorem, this identifies
boundary transport with that scaled capacity-one reservoir value. The paired
probability statement retains the full sum-of-masses capacity bound.


`TDA.Persistence` imports the Geometry and Reverse Core modules, not the fixed
far-atom examples. A client that previously reached those specific names only
through `TDA.Persistence` or `TDA.Library` should explicitly import the matching
Examples module or the corresponding old compatibility entrance.
`TDA.Persistence.Examples` imports both Examples modules and both old entrances.

`BoundaryTransportZero` identifies the powered value against zero with the
diagonal persistence moment, for every finite-mass input and p at least one.
`boundaryTransportPowerValue_zero_target_of_isFiniteMeasure`,
`boundaryTransportDistance_zero_target_of_isFiniteMeasure`, and
`boundaryTransportDistance_zero_target_rpow_of_isFiniteMeasure` expose those
formulas under `[IsFiniteMeasure μ]`. The reciprocal-p root and
p-th power formulas hold in the extended nonnegative reals, including when the
moment is infinite.

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

### Gaussian stability under native boundary transport

`WeightedBoundaryTransportFeature` identifies the native strict half-plane with
`UpperPoint` and proves bounded-feature integrability for every finite original
measure. In `WeightedBoundaryTransportStability`,
`enorm_weightedPersistenceEmbedding_sub_le_boundaryTransportDistance` bounds the
actual full-plane RKHS embedding difference by
`(2*A + √2*B/|σ|) * BT₁(μ,ν)` in extended nonnegative values. The birth–persistence
weight is nonnegative, bounded by B, A-Lipschitz and zero at persistence zero,
with A,B ≥ 0. Inputs may have unequal masses and nonatomic or noncompact support;
the estimate requires no moment. Its real-valued companion proves transport
finiteness from finite first diagonal moments before taking `.toReal`.

`WeightedBoundaryTransportApproximation` gives real-mass atomic sum formulas,
the native finite weighted-diagram bound, and
`weightedPersistenceEmbedding_quantizedDiagram_tendsto`: the existing
same-original-mass quantizations converge in RKHS norm under finite first
diagonal moment. Zero weights and coincident fractional atoms are included.
See [the statement, direct-plan proof and source boundaries](math/weighted-boundary-transport.md).

### Sampled Rips laws

`Probability.FiniteSampling`, `SamplingMoments`, and `GromovWasserstein` provide
atomic probability couplings, iid sampling with replacement, unordered-pair
moment bounds with the constant `C(n,2)` (non-strict; optimality is not claimed), and distortion GW with factor one half. Their measure-valued
counterparts in `MeasureCoupling`, `MeasureSampling`, and `MeasureGromovWasserstein`
use actual `ProbabilityMeasure` couplings with exact marginals. `RipsSampling`
applies the atomic estimates to full diagrams of finite tuple ranges. For `PMF`
inputs on arbitrary metric spaces, with no compactness assumption,
`Rips.wasserstein_sampleLaw_le_gromovWasserstein_allDegrees` and
`Rips.wassersteinInfinity_sampleLaw_le_gromovWassersteinInfinity_allDegrees`
prove the same finite-p and `W_∞` bounds for the atomic laws `Rips.sampleLaw` in
every natural degree `q`, including full H₀ at degree zero. Positive-degree
specializations are also available without the `_allDegrees` suffix.
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

and `W_∞(U_{n,q}(μ),U_{n,q}(ν)) ≤ 2 GW_∞(μ,ν)` for every `n`. Positive-degree
specializations are also available as
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
The degree-zero fixture `weighted_twoPoint_sampleLaw_bound_degreeZero` applies
the atomic all-degree finite-p bound to this input law and a one-point input, and
`twoPoint_pair_sampleLaw_bound_degreeZero` applies it to the `n = 2` laws of two
weights `ε` and `ε'`, together with both exact rare-atom masses and the fact that
the two laws differ whenever those masses differ. The positive-degree fixture
`weighted_twoPoint_sampleLaw_bound` only instantiates the `q+1` wrapper.
The compact Borel law and its finite-PMF agreement are described with the
`Rips.sampleLawMeasure` API above. The finite-PMF transport cost has not yet been
identified with the infimum over all Borel couplings on finite support.
For finite input laws, `RipsSamplingEmpirical` instead works directly with the
atomic `sampleLaw` and its full-degree Wasserstein bound. It uses a proved
common-mass coupling and a uniform-index empirical PMF, with no full-support
assumption. Its bound is deterministic in the empirical law; random training
concentration is separate.
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
target face, although `f(s) ∪ g(s)` need not be one; `Contiguous.prismAdmissible` derives it from
contiguity (no fixture shows the weakening is strict). `PrismAdmissible.chainHomotopy` is the
signed prism homotopy, of the same shape as the separately constructed `Contiguous.chainHomotopy`,
and `simplicialHomologyMap_eq_of_prismAdmissible` gives equal homology maps in every degree over
any ring. `TDA.Simplicial.ArbitraryApexCone` inserts a
chosen apex into each oriented tuple at its position in the ambient order; when the apex can
be inserted into every face (`ApexInsertionClosed`), `boundary_arbitraryApexConeFill_add`
contracts positive-degree chains and `boundary_arbitraryApexConeFill_zero` subtracts the
coefficient sum at the apex in degree zero. `TDA.Simplicial.BarycentricHomology` takes the
barycentric subdivision to be the mass-zero normalized subdivision flag complex. For a finite
nonempty ordered vertex type with an auxiliary linear order on its finite subsets, the
subdivision chain map and the last-vertex map form `barycentricChainHomotopyEquiv`, and `barycentricHomologyIso` is natural for inclusions of
complexes. Over a field, `simplicialHomologyClass_zeroVertexCycle_ne_zero` shows that every
vertex has a nonzero `H₀` class. These results are stated for the ordered chain model only;
no comparison with singular homology is made.

### Realizations, subdivision mesh and nerves of nested convex families

`TDA.Topology.NerveThickening` (imported by `TDA.Topology`, namespace `TDA.Topology`) treats
open thickenings of a `CoverFamily X I` in a metric space. For a finite index type and
compact members, `exists_pos_nerve_thickening_eq` gives `δ > 0` with
`nerve (fun i => thickening ε (C i)) = nerve C` for every `0 < ε ≤ δ`, and
`exists_pos_common_nerve_thickening_eq` gives one such `δ` for two families. In a real
normed space, `convex_thickening_of_iUnion_eq` takes convex families with `C i ⊆ D i` and
`⋃ i, C i = ⋃ i, D i`, with any index type, and states at every real `ε` that both families
of thickenings have union `thickening ε (⋃ i, C i)`, that they are nested and that their
members are open and convex. `exists_pos_common_convex_thickening` assumes in addition a
finite index type and compact members and gives one `δ > 0` with all these properties and
both nerve equalities for `0 < ε ≤ δ`.

`TDA.Topology.Realization` defines `Realization K`, for
`K : PreAbstractSimplicialComplex V`, as the points of mathlib's `StdSimplex ℝ V` whose
weight support is a face of `K`, and the continuous `Realization.incl` for `K ≤ L`. In
namespace `TDA.Topology.Realization`, `coordinateStar K v` is the set of points with
positive weight at `v`. For every vertex type the stars are open (`isOpen_coordinateStar`)
and cover the realization (`covers_coordinateStar`), a nonempty finite set of labels has a
common star point exactly when it is a face (`interMember_nonempty_iff`), and
`nerve_coordinateStar` states `nerve (coordinateStar K) = K`. Under `[Finite V]`,
`isEmbedding_weights` embeds the realization in `V → ℝ` by its coordinates, and for a face
`J` the homotopy `contraction` joins the identity of `StarIntersection K J` to the constant
map at `faceBarycenter` along straight lines, which gives
`contractibleSpace_starIntersection`. `pullback_coordinateStar` states that `incl` pulls
stars back to stars, and `starNerveInclusion_naturality` that the induced map of star nerves
is the inclusion `K ≤ L` under `nerve_coordinateStar`.

`TDA.Topology.SubdivisionRealization` (namespace of the same name) iterates barycentric
subdivision for a finite vertex type `V`. The labels `Vertex V n` depend only on `V` and
`n`, `complex K n` is the `n`-fold `barycentricSubdivision` of `K`, and `complex_mono`
carries `K ≤ L` to every depth. For a placement `p : V → E` in a real normed space,
`vertexPosition p n` places a label at its iterated barycenter and
`realize p K n : C(Realization (complex K n), E)` interpolates these positions.
`barycentricProjection K n : C(Realization (complex K n), Realization K)` composes the
one-step maps `projectStep`; `realize_eq_comp_projection` states
`realize p K n = (realize p K 0).comp (barycentricProjection K n)`, and `projection_incl`
and `realize_incl` state compatibility with `Realization.incl`. `originalFace n F` is the
face of `K` that supports a face `F` of `complex K n` (`originalFace_mem`), and
`projection_support` states that the support of a projected point is the original face of
the support of the point.
`TDA.Topology.SubdivisionMesh`, in the same namespace, defines `faceImage K p n F`, the
image under `realize` of the points supported in `F`, and `closedStarImage K p n v`, the
union of the images of the faces containing `v`. `diam_le` assumes that every face of `K`
has at most `d + 1` vertices and that the placed vertices of each face are pairwise within
`M ≥ 0`; then every face image at depth `n` has diameter at most `(d / (d + 1)) ^ n * M`
and every closed-star image at most twice that. `eventually_diam_lt` gives a depth from
which both are smaller than a given `ε > 0`, and `diam_eq_zero_of_card_le_one` is the case
of faces with at most one vertex.

`TDA.Topology.ConvexNerveInclusion` (namespace `TDA.Topology.ConvexNerve`) proves
`ConvexNerve.isIso_simplicialHomologyIncl`. Its hypotheses are an index type `I` with
`[Fintype I] [LinearOrder I]`, a real normed space `E` and families `C D : I → Set E` with
every `C i` open and convex, every `D i` convex, `C i ⊆ D i` and `⋃ i, C i = ⋃ i, D i`. Its
conclusion is `IsIso (simplicialHomologyIncl R (nerve_mono h) k)` for every ring `R` and
every degree `k`: the inclusion `nerve C ≤ nerve D` on the same labels induces an
isomorphism of simplicial homology. `ConvexNerve.isIso_simplicialHomologyIncl_of_compact` has the same
conclusion for `[LinearOrder I] [Finite I]` when every `C i` and `D i` is compact and
convex, by `exists_pos_common_convex_thickening`. The supporting modules are
`TDA.Topology.SubdivisionLastVertex` (`iteratedLastVertex`, its naturality
`iteratedLastVertex_naturality` and `isIso_iteratedLastVertex`, and the flag versions
`flagLastVertex`, `isIso_flagLastVertex`), `TDA.Topology.NerveStarLabeling`
(`exists_subordinate_closedStars` and `exists_common_labeling`, a vertex map from an
iterated subdivision of `nerve D` to `nerve C` whose closed-star images lie in the members
of `C` that label them) and `TDA.Topology.ConeCarrierComparison`
(`coneCarrier`, `exists_contiguous_apexMap` and
`chainHomotopy_of_contiguous_after_lastVertex`). `Vertex V n` is not reducible, so its
linear order `SubdivisionRealization.vertexLinearOrder` (the order of `V` at depth `0`, the
fixed face order `faceLinearOrder` at positive depths) is a global instance on these labels
only, and does not apply to an unrelated `Finset`. The labels `Vertex (Finset I) n` of
`subdividedFlags K n` take `flagVertexLinearOrder`, which starts from `faceLinearOrder I` on
the flags and has priority over any other order on `Finset I` in context; a complex whose
original labels are finsets with a different order therefore needs that order passed
explicitly to `vertexLinearOrder`. A client states and applies `isIso_iteratedLastVertex`,
`isIso_flagLastVertex`, `chainHomotopy_labeling_lastVertex`,
`exists_common_chain_comparisons` and `exists_contiguous_apexMap` without opening a scope or
declaring an instance, at a variable or a literal depth; `exists_contiguous_apexMap` takes
`[DecidableEq I]`. `TDA.Topology.LastVertexClientExamples` (imported by
`TDA.Topology.Examples`) states each of them this way, at depth `1` where a depth occurs, and
applies the flag statement with another order on `Finset I` in context.
`TDA.Topology.ConvexNerveInclusionExamples` (imported by `TDA.Topology.Examples`) has three
intervals whose nerve inclusion is strict and an isomorphism (`strict_inclusion_isIso`),
eight open boxes around a square hole where enlarging one box gives a strict inclusion
(`Annulus.nerve_boxes_lt`) that is an isomorphism (`Annulus.isIso_simplicialHomologyIncl`)
with nonzero first homology over F₂ (`Annulus.not_isZero_homology_one`), and the
enlargement of every box to the plane, where the unions differ and the inclusion is not an
isomorphism in degree one over F₂ (`Annulus.unequal_union_not_isIso`).
See [nerves of nested convex families](math/convex-nerve-inclusion.md).
The source register records these Topology modules as library derivations attributed to no
source; see its [declaration mappings](math/references.md#existing-declaration-and-proof-mappings).

### Affine chains and the subdivision diameter bound

`TDA.Topology.AffineChains` (imported by `TDA.Topology`, namespace
`TDA.Topology.AffineChains`) prepares the singular subdivision of #1190. For any type `X`,
`affineSSet X` is the simplicial set whose `n`-simplices are the vertex tuples
`Fin (n + 1) → X` (`affineSSet.mk`, `affineSSet.vertices`, `affineSSet.equiv`); a simplicial
operator acts by precomposition, so the `i`-th face deletes vertex `i` (`affineSSet.δ_mk`), and
the chain complex `(affineSSet X).chainComplex R` uses Mathlib's alternating face differential
`SSet.ιChainComplex_d` with no sign convention of its own. The coefficients `R` lie in any
preadditive category `C` with coproducts, for example `ModuleCat.of k k` over a ring `k`.
`cone b σ = Fin.cons b σ` puts the apex at vertex `0`, and `coneMap R b n` is the cone on
`n`-chains (`ιChainComplex_coneMap`). `coneMap_d` states
`coneMap R b (n + 1) ≫ d (n + 2) (n + 1) = 𝟙 - d (n + 1) n ≫ coneMap R b n`, that is
`∂(b · c) = c - b · ∂c` in positive degree, with the simplex form `ιChainComplex_coneMap_d`;
`coneMap_zero_d` states `∂(b · c) = c - ε(c) · b` in degree zero, where `augmentation R S`
sends every vertex generator of a simplicial set `S` to `𝟙 R`. `affineSSet.map f` is the map
induced by `f : X → Y`, and `coneMap_comp_chainComplexMap` is its compatibility with cones.

For `K : Set (StdSimplex ℝ (Fin (m + 1)))` with `hK : IsConvexSet ℝ K`,
`realize hK σ : C(StdSimplex ℝ (Fin (n + 1)), K)` is the affine map sending vertex `i` to `σ i`
(`coe_realize_apply`, `realize_single`, `realize_injective`); faces realize by
`StdSimplex.map` (`realize_comp`), the realized cone is Mathlib's `AffineMap.cone`
(`coe_realize_cons`), and an affine map of ambient simplices carrying `K` into `K'` commutes with
realization (`coe_realize_mapsTo`). For `Y : TopCat.{u}` and `e : C(K, Y)`, `toSingular hK Y e`
is the map of simplicial sets to `TopCat.toSSet.obj Y` sending `σ` to `e ∘ realize hK σ`,
natural in `Y` (`toSingular_comp`) and a monomorphism for injective `e` (`mono_toSingular`);
`toSingularChains hK Y e R` is the induced chain map into the singular chains of `Y`.

`TDA.Topology.SubdivisionDiameter` (same namespace) defines the barycentre
`simplexBarycenter hK σ`, the image of `StdSimplex.barycenter` under `realize hK σ`, and the
inductive predicate `IsSubdivisionSimplex hK σ τ` for the simplices of the recursive
barycentric subdivision `sd(σ) = b_σ · sd(∂σ)`: a vertex is its own subdivision, and
`cone (simplexBarycenter hK σ) τ` is a simplex of `sd(σ)` when `τ` is one of `sd(σ ∘ i.succAbove)`.
`IsIteratedSubdivisionSimplex hK N σ τ` composes `N` steps. Distances are measured through
`position L x = L x.weights` for any linear map `L : (Fin (m + 1) →₀ ℝ) →ₗ[ℝ] E` into a real
normed space `E`; every affine map from the simplex to `E` is of this form.
`diam_range_position_realize` identifies the diameter of a realized simplex with that of its
vertices, and `dist_position_simplexBarycenter_le` bounds the distance from the barycentre of an
`n`-simplex to any of its points by `n / (n + 1)` times its diameter. Every subdivision simplex
lies in `σ` (`IsSubdivisionSimplex.range_realize_subset`) and has realized diameter at most
`n / (n + 1)` times that of `σ` (`IsSubdivisionSimplex.diam_range_realize_le`, vertex form
`IsSubdivisionSimplex.diam_le`); after `N` steps the factor is `(n / (n + 1)) ^ N`
(`IsIteratedSubdivisionSimplex.diam_range_realize_le`). Both predicates are preserved by affine
maps carrying `K` into `K'` (`mapsTo`).
`TDA.Topology.AffineChainsExamples` (imported by `TDA.Topology.Examples`) proves
`∂(b · [p, q]) = [p, q] - [b, q] + [b, p]` over any ring (`cone_boundary_segment`) and the factor
`2 / 3` for a subdivision simplex of the standard `2`-simplex in any norm
(`diam_subdivisionTriangle_le`, `diam_iterated_triangle_le`).

### Singular barycentric subdivision

`TDA.Topology.AffineSubdivision` (imported by `TDA.Topology`, namespace
`TDA.Topology.AffineChains`) defines, for a convex `K` in a standard simplex and coefficients `R`
in a preadditive category with coproducts, the barycentric subdivision chain map
`affineSubdivision hK R` on `(affineSSet K).chainComplex R`. It is the identity in degree `0`
(`affineSubdivision_f_zero`), and on a simplex `σ` of positive dimension it is the cone from the
barycentre on the subdivided boundary, `sd(σ) = b_σ · sd(∂σ)`
(`ιChainComplex_affineSubdivision_f_succ`); on a segment it is `[b, v₁] - [b, v₀]`
(`ιChainComplex_affineSubdivision_f_one`). The chain-map property uses `coneMap_d`,
`coneMap_zero_d` and `d_comp_augmentation` (the augmentation vanishes on boundaries).
`affineSubdivisionHomotopy hK R : Homotopy (affineSubdivision hK R) (𝟙 _)` is `0` in degree `0`
and `T(σ) = b_σ · (sd(σ) - σ - T(∂σ))` in positive degree
(`ιChainComplex_affineSubdivisionHomotopy_hom_succ`); it is built with `chainHomotopyOfSucc`, the
homotopy of `ℕ`-indexed chain complexes given by degreewise maps `h n : P.X n ⟶ Q.X (n + 1)`
(`chainHomotopyOfSucc_hom_succ`). Both commute with the chain maps of affine maps carrying `K`
into `K'` (`affineSubdivision_comp_chainComplexMap`,
`affineSubdivisionHomotopy_hom_comp_chainComplexMap`). The subdivision of a simplex `σ` lies in
the additive subgroup generated by the generators of the simplices `τ` with
`IsSubdivisionSimplex hK σ τ` (`ιChainComplex_affineSubdivision_mem_closure`), and one more
subdivision carries integer combinations of `N`-fold subdivision simplices to integer
combinations of `(N + 1)`-fold ones (`comp_affineSubdivision_mem_closure`).

`TDA.Topology.SingularSubdivision` (namespace `TDA.Topology`) uses the standard simplex as a
convex subset of itself, `modelSimplex n` with `isConvexSet_modelSimplex n`, its identity affine
simplex `idSimplex n`, and for a singular simplex `σ` the map `modelMap σ` on the model; the chain
map `toSingularChains (isConvexSet_modelSimplex n) X (modelMap σ) R` sends `idSimplex n` to `σ`
(`toSingular_idSimplex`, `ιChainComplex_idSimplex_toSingularChains`). Singular chains are written
`(TopCat.toSSet.obj X).chainComplex R`, which is by definition
`((singularChainComplexFunctor C).obj R).obj X`, and `toSingularChains` has this target.
`singularSubdivision R X` sends a generator `σ` to `σ_*` of the subdivision of `idSimplex n`
(`ιChainComplex_singularSubdivision_f`); it is the identity in degree `0`
(`singularSubdivision_f_zero`), commutes with `e_*` for every continuous `e` from a convex subset
of a standard simplex (`toSingularChains_comp_singularSubdivision`), and is natural in `X`
(`singularSubdivision_naturality`, `singularSubdivisionNatTrans`).
`singularSubdivisionHomotopy R X : Homotopy (singularSubdivision R X) (𝟙 _)` is `σ_*` of the
affine homotopy of `idSimplex n` (`ιChainComplex_singularSubdivisionHomotopy_hom`), with the same
compatibility (`toSingularChains_comp_singularSubdivisionHomotopy_hom`) and naturality
(`singularSubdivisionHomotopy_hom_naturality`). Supporting lemmas: `map_comp_toSingular`
(affine reparametrization of `toSingular`) and `range_toSingular_le`.

For a subcomplex `A` of singular simplices that contains, with each simplex, every singular
simplex with image in its image, the subdivision and the homotopy factor through the chains of
`A` (`exists_singularSubdivision_f_lift`, `exists_singularSubdivisionHomotopy_hom_lift`);
`simplicesIn_range_le_smallSimplices` shows that the small simplices of two subsets form such a
subcomplex. Over a ring `k`, `singularSubdivision_f_apply_mem_range_smallChainsι` and
`singularSubdivisionHomotopy_hom_apply_mem_range_smallChainsι` are the hypotheses `hS` and `hT`
of `quasiIso_of_iterate_mem` for `smallChainsι s t M`. `TDA.Topology.SingularSubdivisionExamples`
(imported by `TDA.Topology.Examples`) shows, over any ring, that a singular segment subdivides to
its two half-segments from the midpoint with signs `+` towards `v₁` and `-` towards `v₀`
(`singularSubdivision_segment`, `halfSegment_apply_zero`, `halfSegment_apply_one`), that the
boundary is preserved (`singularSubdivision_segment_d`), and one naturality instance
(`singularSubdivision_segment_naturality`).

### Small chains of a cover and the Mayer–Vietoris sequence

`TDA.Topology.SmallChainsQuasiIso` (#1190, imported by `TDA.Topology`, namespace `TDA.Topology`)
proves that small chains compute singular homology. For subsets `s` and `t` of `X : TopCat.{u}`
with `interior s ∪ interior t = Set.univ` and coefficients in any module `M : ModuleCat.{u} k`
over a ring `k : Type u`, `quasiIso_smallChainsι s t M h : QuasiIso (smallChainsι s t M)`. It
applies `quasiIso_of_iterate_mem` to `singularSubdivision` and `singularSubdivisionHomotopy`; the
remaining hypothesis is proved in three steps.

- `exists_isIteratedSubdivisionSimplex_subset`: for an open cover of `modelSimplex n` there is an
  `N` such that for every `N' ≥ N` each simplex of the `N'`-fold subdivision of `idSimplex n`
  lies in one member. Distances are taken on weight vectors in `Fin (n + 1) → ℝ`, with Mathlib's
  `lebesgue_number_lemma_of_metric` on the compact simplex and the bound
  `IsIteratedSubdivisionSimplex.diam_range_realize_le`.
- `exists_iterate_singularSubdivision_ιChainComplex_mem_range`: for a singular simplex `σ` there is
  an `N` such that every iterate `sd^{N'}`, `N' ≥ N`, carries the generators `r · σ` into the
  image of `smallChainsι s t M`.
- `exists_iterate_singularSubdivision_mem_range_smallChainsι` extends this to every chain, which is
  a finite sum of generators: `iSup_range_ιChainComplex` states that the simplicial `n`-chains with
  coefficients in a module are spanned by the images of the summand inclusions.

With `shortExact_smallChains` this gives the Mayer–Vietoris long exact sequence on
`singularHomologyFunctor`: the connecting map `mayerVietorisδ s t M h n : H_{n+1}(X) ⟶ H_n(s ∩ t)`
(the inverse of the homology isomorphism of `smallChainsι`, then `bicartδ`, whose sign is
`bicartδ_eq`), `mayerVietorisInterMap s t M n : H_n(s ∩ t) ⟶ H_n(s) ⊞ H_n(t)` (the inclusions,
with the sign `(inc, -inc)`), and `mayerVietorisSumMap s t M n : H_n(s) ⊞ H_n(t) ⟶ H_n(X)` (the
sum of the inclusions). The composites vanish (`mayerVietorisδ_comp_mayerVietorisInterMap`,
`mayerVietorisInterMap_comp_mayerVietorisSumMap`, `mayerVietorisSumMap_comp_mayerVietorisδ`), and
the sequence is exact at `H_n(s ∩ t)` (`mayerVietoris_exact_inter`), at `H_n(s) ⊞ H_n(t)`
(`mayerVietoris_exact_sum`) and at `H_{n+1}(X)` (`mayerVietoris_exact_space`). Naturality of the
connecting map in the space and the interval-square specialisation are not part of this module.
`TDA.Topology.SmallChainsQuasiIsoExamples` (imported by `TDA.Topology.Examples`) shows that the
small chains of the two open rays of `ℝ` compute the singular homology of the line
(`quasiIso_smallChainsι_rays`), with the exact Mayer–Vietoris sequence of the rays
(`mayerVietoris_exact_rays`); that the segment from `2` to `-1`, which is not small, has small
iterated subdivisions from some step on (`segmentSimplex_not_small_and_eventually_small`); and a
Lebesgue step for the cover of the model `1`-simplex by the open parts where the weight of
vertex `0` is below `2/3` and above `1/3` (`exists_isIteratedSubdivisionSimplex_one_subset`).

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
outlier consumer. The distance is the infimum over the public predicate
`SubdivisionRipsHomologyInterleavingExistsAt`, and
`subdivisionRipsHomologyInterleavingDistance_le_of_interleaving` bounds it by the scale of any
supplied restricted-index interleaving. No comparison with the homology of the multicover space, homotopy
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
The decorated multiplicity representation is constructed below; for q-tame modules over a
field, `qTame_bottleneck_le_of_realInterleaving` bounds the bottleneck distance of the extracted
diagrams by the parameter of any actual interleaving. See
[persistence rectangle measures](math/persistence-rectangle-measure.md).

For a field `k : Type u` and modules `M N : PModule.{u,0,w} k ℝ`,
`LocallyFiniteDecoratedDiagram.qTame_bottleneck_le_realInterleavingDistance` bounds the
bottleneck distance of their finite-birth diagrams by the extended real interleaving
distance, assuming only that both modules are q-tame. The field and carrier universes
`u` and `w` are independent; finite distance and an attained minimizer are not required.
`LocallyFiniteDecoratedDiagram.ofQModule_eq_of_iso` identifies the extracted diagrams
under a natural module isomorphism, including essential `infinityCut` deaths. The bottleneck bound
does not reverse for arbitrary q-tame modules: in `TDA.Persistence.WholeLineObstructionExamples`,
`canonical_zero_but_module_distance_top` states that, over a field, the constant scalar module
on `ℝ` and the zero module have the same diagram `LocallyFiniteDecoratedDiagram.ofQModule`,
hence bottleneck distance `0`, while their real interleaving distance is `⊤`; see
[a whole-line module](math/real-interval-decomposition.md#a-whole-line-module-and-the-finite-birth-diagram).
The finite diagram base point `Diagram.empty` is defined alongside the general diagram API in
`TDA.Persistence.Diagram`.

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
for the precise hypotheses. The global algebraic-stability bridge,
`qTame_bottleneck_le_of_realInterleaving`, is proved by finite window matching and saturation
rather than through this separated local step:
`PersistenceMeasureWindowMatching.exists_finite_window_matching_of_center_counts` is the
finite-window step, which, for `δ ≥ 0` and source point values separated by more than `2δ`,
uses closed-ball count comparisons at the source values to inject every source occurrence
within distance `δ`, and the reverse comparison at each target value whose exit value exceeds
`δ` to cover that target occurrence; repeated values remain separate tokens and target values
need no separation.

`TDA.Persistence.DecoratedMeasureCuts` identifies the existing persistence cuts with
mathlib lower sets, retaining boundary decorations and compact open coordinate cells.
`DecoratedRectangleCells` proves the semiring laws for finite separated rectangles, and
`DecoratedRectangleTopology` proves their compactness, openness and point separation.
`IntegerContentAtoms` constructs minimum-cell multiplicities of natural-valued additive
contents, finite atomic representations on compact cells, and finite local positive
support with exact cell counts. The construction permits infinite global support.
`PersistenceMeasureBoxContent` proves arbitrary finite box-partition additivity from the
actual module quotient split identities; `PersistenceMeasureContent` constructs the
module's actual `AddContent`. `DecoratedRectangleBox` turns decorated rectangle covers into
ordinary half-open box partitions by taking preimages along pairs of minus cuts, and
`IntegerContentTransport` transports additive contents along such preimages and converts a
cellwise nonnegative integer content to a natural-valued one. `PersistenceMeasureDiagram.moduleDiagramMultiplicity`
extracts finite-death decorated point counts, with finite local support and exact rectangle
counts. `DecoratedCutEndpoints` supplies finite numeric endpoints.
`PersistenceMeasureEssentialContent` and `PersistenceMeasureEssentialDiagram`
construct the essential birth-strip content and its multiplicities.
`PersistenceMeasureExtendedDiagram.moduleExtendedDiagramMultiplicity` includes death at
infinity, with exact finite rectangle, essential strip and full tail-rectangle counts and
finite positive support on every separated tail rectangle.
`PersistenceMeasureDiagramCountability` proves countable global support;
`PersistenceMeasureLowerBound` transfers a module zero tail to a birth lower bound.
`TDA.Persistence.LocallyFiniteDiagramBottleneck` packages these extended multiplicities of a
q-tame module as `LocallyFiniteDecoratedDiagram.ofQModule`, with countable support and finite
positive support on every separated and tail rectangle; its `bottleneck` is the extended infimum
of global occurrence-matching costs. For an actual ε-interleaving of q-tame modules over a field,
`RealInterleaving.exists_finite_saturating_matching` covers any prescribed finite sets of
finite-death occurrences longer than `2ε` and of essential occurrences on both sides by injective
edge sets of cost at most ε, and `qTame_bottleneck_le_of_realInterleaving` in
`LocallyFiniteMatchingCompactness` passes to one global matching through a coherent section of
the finite inverse system, bounding the bottleneck distance of the two extracted diagrams by ε.
No interval decomposition is assumed. The extracted diagrams have finite births;
birth-at-minus-infinity strata of unrestricted q-tame modules are not represented. Positive
finite diagrams embed isometrically (`Diagram.toLocallyFinite`, `bottleneck_toLocallyFinite`), and
`TDA.Persistence.ConstructibleQTameCompatibility` identifies the canonical diagram with the
finite barcode for a real module over any field satisfying `FiniteConstructible.IsConstructible`
on a finite critical grid and having finite-dimensional critical fibers. This is the
right-continuous convention: the module is zero before the first critical value, constant
up to isomorphism on cells `[cᵢ,cᵢ₊₁)`, and may have a nonzero final tail. Pointwise
finite-dimensionality follows from `finiteDimensional_of_isConstructible`, and
`FiniteConstructible.qTame_of_isConstructible` derives q-tameness.
`FiniteConstructible.moduleExtendedDiagramMultiplicity_eq_count` says that at every decorated
point the canonical multiplicity counts the occurrences in `moduleDiagram`, including
repeated and essential bars. The decoration map sends a finite bar `(b,d)` to
`(minusCut b,minusCut d)` and an essential bar `(b,∞)` to `(minusCut b,infinityCut)`.
`FiniteConstructible.ofQModule_eq_toLocallyFinite` identifies the resulting diagrams.
`FiniteConstructible.ofQModuleMatchingEquiv` transports finite occurrence matchings to
the canonical diagram with their costs preserved, using
`Diagram.toLocallyFiniteMatchingEquiv` and its cost theorem.
`FiniteConstructible.ofQModule_bottleneck_eq_finite` then gives equality of their locally
finite and finite bottleneck values through `bottleneck_toLocallyFinite`, including different
or empty grids and infinite distances.
The theorem concerns these half-open bars and finite births; arbitrary endpoint decorations
and singleton summands of general pointwise finite-dimensional modules are outside its scope.
`Rips.qTameDiagramMultiplicity_eq_diagramOccurrenceCount` retains the finite-metric-space
specialization. See [integer contents on decorated cells](math/persistence-measure-atoms.md) and
[decorated diagrams of infinite Rips spaces](math/rips-metric-stability.md#decorated-diagrams-of-infinite-rips-spaces).


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
precisely when this entry is at most the deletion time of each of its vertices (`≤`, so a
tie at a deletion time is allowed). On that actual carrier,
`sparseFilter_sublevel_eq` identifies the finite filter's closed sublevels with
the sparse filtration. For a coefficient field in the vertex universe, an auxiliary linear
order on the vertices and a degree `n ≥ 1`,
`sparseLogDiagram_bottleneck_le` bounds the bottleneck distance from its
log-scale diagram to the diameter-scale Rips log diagram by
`log((1−2η)⁻¹)`. The diagram bound uses the proved module interleaving and
finite-constructible matching. Degree zero retains the module interleaving;
zero-born classes do not fit the finite positive-log diagram.

The homology equivalence `sparseRelaxedHomologyIso`, log-scale APIs
`sparseRipsLogInterleaving` and `sparseRipsLogDistance_le`, and diagram bound
`sparseLogDiagram_bottleneck_le` take an explicit `seed : V`, using
`sparseFiltration seed η` or `sparseFilter seed η` as their sparse input.
Use these seeded constructions when applying the results. The seed-free
`finiteSparseFiltration` wrapper chooses its seed classically on nonempty input.

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

## Finite affine endpoint-cost arrangement

`TDA.Persistence.EndpointCostSign` proves the two-factor sign identity for
weighted absolute differences. `TDA.Persistence.AffineSwitchArrangement`
constructs finite affine cuts from a finite set of coordinate pairs and derives
`AffineSwitch.SameCell.sign_cost_sub_eq`, `cost_le_iff`, and `cost_eq_iff`.
Push branches, the slope-one normalization boundary, repeated endpoints, and
zero forms are retained. This is an endpoint comparison result; barcode
transport and matching-distance maximum attainment remain separate. See
[finite affine cuts](math/affine-switch-arrangement.md) for definitions, proof,
and the two-cut regression.
