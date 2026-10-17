-- Live axiom audit pins for Mapper. Append new pins here; do not remove existing pins.
import TDA

-- Path-component pullback covers and selected component refinements.
#print axioms TDA.Mapper.PullbackSpace
#print axioms TDA.Mapper.ComponentIndex
#print axioms TDA.Mapper.componentCover
#print axioms TDA.Mapper.componentClass_proof_irrel
#print axioms TDA.Mapper.mem_componentCover_iff
#print axioms TDA.Mapper.componentCover_nonempty
#print axioms TDA.Mapper.componentCover_disjoint
#print axioms TDA.Mapper.iUnion_componentCover_fiber
#print axioms TDA.Mapper.iUnion_componentCover
#print axioms TDA.Mapper.componentCover_covers
#print axioms TDA.Mapper.componentCover_covers_range
#print axioms TDA.Mapper.componentType_isEmpty
#print axioms TDA.Mapper.no_componentIndex_of_isEmpty
#print axioms TDA.Mapper.componentIndex_ne_of_index_ne
#print axioms TDA.Mapper.refinementInclusion
#print axioms TDA.Mapper.componentRefinementMap
#print axioms TDA.Mapper.componentRefinement
#print axioms TDA.Mapper.componentRefinement_selector_mk
#print axioms TDA.Mapper.componentRefinement_id
#print axioms TDA.Mapper.componentRefinement_comp
#print axioms TDA.Mapper.componentCover_mk_eq_pathComponentIn
#print axioms TDA.Mapper.componentCover_isOpen

-- Path-component pullback-cover fixtures.
#print axioms TDA.Mapper.Examples.emptyDomainMap
#print axioms TDA.Mapper.Examples.unitCover
#print axioms TDA.Mapper.Examples.emptyDomain_componentIndex_isEmpty
#print axioms TDA.Mapper.Examples.emptyMemberFamily
#print axioms TDA.Mapper.Examples.emptyMember_no_component_index
#print axioms TDA.Mapper.Examples.boolToUnit
#print axioms TDA.Mapper.Examples.boolPoint
#print axioms TDA.Mapper.Examples.boolComponentIndex
#print axioms TDA.Mapper.Examples.bool_component_member
#print axioms TDA.Mapper.Examples.bool_component_classes_ne
#print axioms TDA.Mapper.Examples.bool_component_indices_ne
#print axioms TDA.Mapper.Examples.bool_component_indices_exhaustive
#print axioms TDA.Mapper.Examples.duplicateUnitCover
#print axioms TDA.Mapper.Examples.duplicateComponentIndex
#print axioms TDA.Mapper.Examples.duplicate_component_member
#print axioms TDA.Mapper.Examples.duplicate_labels_remain_distinct
#print axioms TDA.Mapper.Examples.realMap
#print axioms TDA.Mapper.Examples.twoIntervalCover
#print axioms TDA.Mapper.Examples.middleIntervalCover
#print axioms TDA.Mapper.Examples.wideIntervalCover
#print axioms TDA.Mapper.Examples.intervalRefinement
#print axioms TDA.Mapper.Examples.wideIntervalRefinement
#print axioms TDA.Mapper.Examples.leftSourcePoint
#print axioms TDA.Mapper.Examples.rightSourcePoint
#print axioms TDA.Mapper.Examples.twoIntervalCover_nonempty
#print axioms TDA.Mapper.Examples.intervalRefinement_proper
#print axioms TDA.Mapper.Examples.source_interval_classes_ne
#print axioms TDA.Mapper.Examples.source_interval_indices_ne
#print axioms TDA.Mapper.Examples.interval_transport_merges_classes
#print axioms TDA.Mapper.Examples.interval_componentRefinement_merges
#print axioms TDA.Mapper.Examples.interval_refinement_left_representative
#print axioms TDA.Mapper.Examples.interval_identity_left_representative
#print axioms TDA.Mapper.Examples.interval_composition_left_representative

-- Ordinary Mapper, multiplicity bounds, and the supported one-skeleton.
#print axioms TDA.Mapper.mapper
#print axioms TDA.Mapper.mem_mapper_iff
#print axioms TDA.Mapper.componentIndex_supported
#print axioms TDA.Mapper.eq_of_mem_mapper_face_of_fst_eq
#print axioms TDA.Mapper.componentLabel_injOn_face
#print axioms TDA.Mapper.CoverMultiplicityAtMost
#print axioms TDA.Mapper.mapper_face_card_le_of_multiplicity
#print axioms TDA.Mapper.MapperVertex
#print axioms TDA.Mapper.toMapperVertex
#print axioms TDA.Mapper.mapperOneSkeleton
#print axioms TDA.Mapper.mapperOneSkeleton_adj_iff
#print axioms TDA.Mapper.mem_mapper_iff_supported_singleton_or_adjacent_pair

-- Refinement-induced Mapper maps and bijective relabelling laws.
#print axioms TDA.Mapper.mapperMap
#print axioms TDA.Mapper.mapperMap_apply
#print axioms TDA.Mapper.mapperMap_mk
#print axioms TDA.Mapper.mapperMap_id
#print axioms TDA.Mapper.mapperMap_comp
#print axioms TDA.Mapper.mapperMap_reindex_comp
#print axioms TDA.Mapper.mapperMap_reindex_symm_comp

-- Ordinary Mapper fixtures.
#print axioms TDA.Mapper.Examples.boolMapperVertex
#print axioms TDA.Mapper.Examples.bool_mapper_two_isolated_vertices
#print axioms TDA.Mapper.Examples.duplicateMapperVertex
#print axioms TDA.Mapper.Examples.duplicate_labels_give_distinct_adjacent_vertices
#print axioms TDA.Mapper.Examples.triangleMap
#print axioms TDA.Mapper.Examples.tripleUnitCover
#print axioms TDA.Mapper.Examples.triangleComponentIndex
#print axioms TDA.Mapper.Examples.triple_duplicate_cover_has_triangle
#print axioms TDA.Mapper.Examples.leftIntervalMapperVertex
#print axioms TDA.Mapper.Examples.rightIntervalMapperVertex
#print axioms TDA.Mapper.Examples.interval_mapper_refinement_is_noninjective
#print axioms TDA.Mapper.Examples.emptyDomain_multiplicity_two
#print axioms TDA.Mapper.Examples.emptyDomain_mapper_eq_bot
#print axioms TDA.Mapper.Examples.emptyDomain_mapper_graph_characterization
#print axioms TDA.Mapper.Examples.bool_multiplicity_two
#print axioms TDA.Mapper.Examples.bool_mapper_graph_characterization

-- Graph-PL incidence relabelling, refinement transport, and conditional finiteness.
#print axioms TDA.Mapper.GraphPL.IncidenceComponentIndex
#print axioms TDA.Mapper.GraphPL.componentIndexEquiv
#print axioms TDA.Mapper.GraphPL.incidenceComponentCover
#print axioms TDA.Mapper.GraphPL.incidenceMapper
#print axioms TDA.Mapper.GraphPL.incidenceComponentCover_covers
#print axioms TDA.Mapper.GraphPL.mem_mapper_iff_incidenceMapper_image
#print axioms TDA.Mapper.GraphPL.mem_incidenceMapper_iff_mapper_image_symm
#print axioms TDA.Mapper.GraphPL.incidenceRefinementMap
#print axioms TDA.Mapper.GraphPL.componentIndexEquiv_mapperMap
#print axioms TDA.Mapper.GraphPL.incidenceMapperMap
#print axioms TDA.Mapper.GraphPL.incidenceMapperMap_apply
#print axioms TDA.Mapper.GraphPL.finite_componentIndex
#print axioms TDA.Mapper.GraphPL.finite_mapperVertex
#print axioms TDA.Mapper.GraphPL.finite_mapperFaces

-- Exact graph-PL Mapper fixtures.
#print axioms TDA.Mapper.GraphPL.Examples.natToUnit
#print axioms TDA.Mapper.GraphPL.Examples.natMapperVertexEquiv
#print axioms TDA.Mapper.GraphPL.Examples.overlappingIntervals
#print axioms TDA.Mapper.GraphPL.Examples.overlappingIntervals_cover_edge_range
#print axioms TDA.Mapper.GraphPL.Examples.singleArcIntervals
#print axioms TDA.Mapper.GraphPL.Examples.singleArc_mapper_exact
#print axioms TDA.Mapper.GraphPL.Examples.edgeOverlapIndex
#print axioms TDA.Mapper.GraphPL.Examples.singleEdge_overlap_exact
#print axioms TDA.Mapper.GraphPL.Examples.twoEdgeGraph
#print axioms TDA.Mapper.GraphPL.Examples.twoEdgeHeight
#print axioms TDA.Mapper.GraphPL.Examples.twoEdgeDart
#print axioms TDA.Mapper.GraphPL.Examples.overlappingIntervals_cover_twoEdge_range
#print axioms TDA.Mapper.GraphPL.Examples.twoEdgeOverlapIndex
#print axioms TDA.Mapper.GraphPL.Examples.twoEdgeIndexEquiv
#print axioms TDA.Mapper.GraphPL.Examples.wideIntervals
#print axioms TDA.Mapper.GraphPL.Examples.overlapToWide
#print axioms TDA.Mapper.GraphPL.Examples.wideIntervals_cover_twoEdge_range
#print axioms TDA.Mapper.GraphPL.Examples.twoEdge_wide_refinement_incidence
#print axioms TDA.Mapper.GraphPL.Examples.twoEdge_cross_componentCover_disjoint
#print axioms TDA.Mapper.GraphPL.Examples.twoEdge_mapper_two_disjoint_edges
#print axioms TDA.Mapper.GraphPL.Examples.twoEdge_wide_refinement_behavior

-- Coherent cover towers and their ordinary Mapper towers.
#print axioms TDA.Mapper.CoherentCoverTower
#print axioms TDA.Mapper.CoherentCoverTower.mapperComplex
#print axioms TDA.Mapper.CoherentCoverTower.mapperMap
#print axioms TDA.Mapper.CoherentCoverTower.mapperMap_refl
#print axioms TDA.Mapper.CoherentCoverTower.mapperMap_trans
#print axioms TDA.Mapper.mapperMap_contiguous

-- Contiguity and coherent-tower fixtures.
#print axioms TDA.Mapper.TowerExamples.selectorSource
#print axioms TDA.Mapper.TowerExamples.selectorTarget
#print axioms TDA.Mapper.TowerExamples.selectFalse
#print axioms TDA.Mapper.TowerExamples.selectTrue
#print axioms TDA.Mapper.TowerExamples.distinct_selector_maps_are_contiguous
#print axioms TDA.Mapper.TowerExamples.oneSource
#print axioms TDA.Mapper.TowerExamples.isolatedTarget
#print axioms TDA.Mapper.TowerExamples.mapToIsolated
#print axioms TDA.Mapper.TowerExamples.isolated_vertex_maps_are_not_contiguous
#print axioms TDA.Mapper.TowerExamples.empty_source_maps_are_contiguous
#print axioms TDA.Mapper.TowerExamples.ThreeStage
#print axioms TDA.Mapper.TowerExamples.ThreeStage.ofNat_ctorIdx
#print axioms TDA.Mapper.TowerExamples.ThreeStageLE
#print axioms TDA.Mapper.TowerExamples.instLEThreeStage
#print axioms TDA.Mapper.TowerExamples.instPreorderThreeStage
#print axioms TDA.Mapper.TowerExamples.threeStageIndex
#print axioms TDA.Mapper.TowerExamples.threeStageCover
#print axioms TDA.Mapper.TowerExamples.threeStageSelector
#print axioms TDA.Mapper.TowerExamples.threeStageRefinement
#print axioms TDA.Mapper.TowerExamples.threeStageTower
#print axioms TDA.Mapper.TowerExamples.threeStageMap
#print axioms TDA.Mapper.TowerExamples.threeStageComponentIndex
#print axioms TDA.Mapper.TowerExamples.three_stage_tower_composite_and_collapsing_edge

-- MultiNerve Mapper (Issue #277).
#print axioms TDA.Mapper.multiNerveMapper
#print axioms TDA.Mapper.multiNerveMapper_projection
#print axioms TDA.Mapper.multiNerveMapper_projection_coe
#print axioms TDA.Mapper.multiNerveMapper_projection_surjective
#print axioms TDA.Mapper.multiNerveMapper_projection_monotone
#print axioms TDA.Mapper.componentCover_isPathConnected
#print axioms TDA.Mapper.existsUnique_cell_support_singleton
#print axioms TDA.Mapper.vertexCell
#print axioms TDA.Mapper.support_vertexCell
#print axioms TDA.Mapper.eq_vertexCell_of_support_eq
#print axioms TDA.Mapper.vertexCellEquiv
#print axioms TDA.Mapper.support_eq_singleton_vertexCellEquiv
#print axioms TDA.Mapper.multiNerveMapper_card_le_of_multiplicity
#print axioms TDA.Mapper.multiNerveMapperOrderIso
#print axioms TDA.Mapper.coe_multiNerveMapperOrderIso
#print axioms TDA.Mapper.PreimageIntersectionsPathConnected
#print axioms TDA.Mapper.intersectionsPathSubsingleton_of_preimage
#print axioms TDA.Mapper.GraphPL.Examples.overlap_components_subsingleton
#print axioms TDA.Mapper.GraphPL.Examples.overlappingIntervals_multiplicity_two
#print axioms TDA.Mapper.MultiNerveExamples.cycle_preimage_subsingleton
#print axioms TDA.Mapper.MultiNerveExamples.cycle_preimage_card
#print axioms TDA.Mapper.MultiNerveExamples.cycleIndex
#print axioms TDA.Mapper.MultiNerveExamples.componentCover_cycleIndex
#print axioms TDA.Mapper.MultiNerveExamples.cycleEdge
#print axioms TDA.Mapper.MultiNerveExamples.cycle_interMember_eq
#print axioms TDA.Mapper.MultiNerveExamples.cycleInterComponentsEquiv
#print axioms TDA.Mapper.MultiNerveExamples.cycleEdgeCell
#print axioms TDA.Mapper.MultiNerveExamples.cycleEdgeCellOne
#print axioms TDA.Mapper.MultiNerveExamples.cycleEdgeCellThree
#print axioms TDA.Mapper.MultiNerveExamples.cycleInterComponentsEquiv_one
#print axioms TDA.Mapper.MultiNerveExamples.cycleInterComponentsEquiv_three
#print axioms TDA.Mapper.MultiNerveExamples.cycleEdgeCellOne_ne_three
#print axioms TDA.Mapper.MultiNerveExamples.cycle_cells_over_edge
#print axioms TDA.Mapper.MultiNerveExamples.cycle_multiNerveMapper_ne_mapper
#print axioms TDA.Mapper.MultiNerveExamples.singleEdge_preimageIntersectionsPathConnected
#print axioms TDA.Mapper.MultiNerveExamples.singleEdgeMultiNerveOrderIso
#print axioms TDA.Mapper.MultiNerveExamples.singleEdge_multiNerveMapper_agrees
#print axioms TDA.Mapper.MultiNerveExamples.triangle_intersectionsPathSubsingleton
#print axioms TDA.Mapper.MultiNerveExamples.triangle_multiNerveMapper_cell
#print axioms TDA.Mapper.MultiNerveExamples.emptyDomain_multiNerveMapper_isEmpty


-- Refinement maps of MultiNerve Mappers (Issue #289).
#print axioms TDA.Mapper.componentCover_interMember_subset_preimage
#print axioms TDA.Mapper.interMemberPreimageMap
#print axioms TDA.Mapper.interMemberPreimageMap_injective
#print axioms TDA.Mapper.multiNerveMapperMap
#print axioms TDA.Mapper.support_multiNerveMapperMap
#print axioms TDA.Mapper.multiNerveMapperMap_monotone
#print axioms TDA.Mapper.multiNerveMapperMap_id
#print axioms TDA.Mapper.multiNerveMapperMap_comp
#print axioms TDA.Mapper.multiNerveMapper_projection_multiNerveMapperMap
#print axioms TDA.Mapper.multiNerveMapperMap_vertexCell
#print axioms TDA.Mapper.CoherentCoverTower.multiNerveMapperMap
#print axioms TDA.Mapper.CoherentCoverTower.multiNerveMapperMap_refl
#print axioms TDA.Mapper.CoherentCoverTower.multiNerveMapperMap_trans
#print axioms TDA.Mapper.GraphPL.Examples.twoEdge_edge_eq
#print axioms TDA.Mapper.GraphPL.Examples.twoEdge_midpoint_height
#print axioms TDA.Mapper.GraphPL.Examples.twoEdgeOverlapPoint
#print axioms TDA.Mapper.MultiNerveRefinementExamples.threeStagePair
#print axioms TDA.Mapper.MultiNerveRefinementExamples.threeStagePairCell
#print axioms TDA.Mapper.MultiNerveRefinementExamples.three_stage_multiNerve_tower
#print axioms TDA.Mapper.MultiNerveRefinementExamples.doubleWideIntervals
#print axioms TDA.Mapper.MultiNerveRefinementExamples.overlapToDoubleWide
#print axioms TDA.Mapper.MultiNerveRefinementExamples.cycle_doubleWide_mapperMap_injective
#print axioms TDA.Mapper.MultiNerveRefinementExamples.cycle_doubleWide_edgeCells_merge
#print axioms TDA.Mapper.MultiNerveRefinementExamples.cycle_doubleWide_multiNerve_merge
#print axioms TDA.Mapper.MultiNerveRefinementExamples.twoEdge_not_preimageIntersectionsPathConnected
#print axioms TDA.Mapper.MultiNerveRefinementExamples.twoEdge_intersectionsPathSubsingleton
#print axioms TDA.Mapper.MultiNerveRefinementExamples.twoEdgeMultiNerveOrderIso
#print axioms TDA.Mapper.MultiNerveRefinementExamples.twoEdge_multiNerveMapper_separation
