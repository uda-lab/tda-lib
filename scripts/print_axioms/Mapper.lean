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
