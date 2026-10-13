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
#print axioms TDA.Mapper.preimageSetInclusion
#print axioms TDA.Mapper.preimageSetInclusion_apply
#print axioms TDA.Mapper.preimageSetInclusion_eq_preimageInclusion
#print axioms TDA.Mapper.preimageSetInclusion_id
#print axioms TDA.Mapper.preimageSetInclusion_comp
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
