-- Live axiom audit pins for Topology. Append new pins here; do not remove existing pins.
import TDA


-- Path-local open-cover subdivision (Issue #25).
#print axioms TDA.Topology.exists_subdivision
#print axioms TDA.Topology.exists_subpath_chain
#print axioms TDA.Topology.exists_overlap_chain
#print axioms TDA.Topology.reflTransGen_of_path
#print axioms TDA.Topology.reflTransGen_of_joined
#print axioms TDA.Topology.exists_subdivision_opens
#print axioms TDA.Topology.reflTransGen_preimage
#print axioms TDA.Topology.Examples.twoOpens_isOpen
#print axioms TDA.Topology.Examples.twoOpens_cover
#print axioms TDA.Topology.Examples.segment_chain_exists
#print axioms TDA.Topology.Examples.segment_chain_uses_both
#print axioms TDA.Topology.Examples.refl_subdivision_mem
#print axioms TDA.Topology.Examples.emptyDupCover_isOpen
#print axioms TDA.Topology.Examples.emptyDupCover_never_empty
#print axioms TDA.Topology.Examples.emptyDupCover_duplicates_admissible
#print axioms TDA.Topology.Examples.singletons_no_subdivision

-- Pairwise-intersection cosheaf condition and component gluing (Issue #26).
#print axioms TDA.Topology.coverCocone
#print axioms TDA.Topology.overlapRel
#print axioms TDA.Topology.eqvGen_overlapRel_apply_eq
#print axioms TDA.Topology.nonempty_isColimit_mapCocone_iff
#print axioms TDA.Topology.existsUnique_glue_of_surjective_of_eqvGen
#print axioms TDA.Topology.IsPairwiseCosheaf

-- Smoothing preserves the interval cosheaf condition (Issue #31).
#print axioms TDA.Topology.map_apply_eq_of_thin
#print axioms TDA.Topology.map_map_apply_of_thin

-- Indexed set covers, selected refinements and pullbacks.
#print axioms TDA.Topology.CoverFamily
#print axioms TDA.Topology.Covers
#print axioms TDA.Topology.Refinement
#print axioms TDA.Topology.Refinement.id
#print axioms TDA.Topology.Refinement.comp
#print axioms TDA.Topology.Refinement.id_selector
#print axioms TDA.Topology.Refinement.comp_selector
#print axioms TDA.Topology.Refinement.ext
#print axioms TDA.Topology.Refinement.ext_iff
#print axioms TDA.Topology.Refinement.comp_id
#print axioms TDA.Topology.Refinement.id_comp
#print axioms TDA.Topology.Refinement.comp_assoc
#print axioms TDA.Topology.pullback
#print axioms TDA.Topology.pullbackRefinement
#print axioms TDA.Topology.covers_pullback
#print axioms TDA.Topology.covers_range_pullback
#print axioms TDA.Topology.pullback_id
#print axioms TDA.Topology.pullback_comp
#print axioms TDA.Topology.pullbackRefinement_id
#print axioms TDA.Topology.pullbackRefinement_comp
#print axioms TDA.Topology.pullbackRefinement_refinement_id
#print axioms TDA.Topology.pullbackRefinement_refinement_comp

-- Indexed set-cover fixtures.
#print axioms TDA.Topology.ProbeFixtures.emptyFamily
#print axioms TDA.Topology.ProbeFixtures.emptyFamily_covers_iff
#print axioms TDA.Topology.ProbeFixtures.emptyFamily_not_full
#print axioms TDA.Topology.ProbeFixtures.duplicatedFamily
#print axioms TDA.Topology.ProbeFixtures.singletonFamily
#print axioms TDA.Topology.ProbeFixtures.mergeDuplicated
#print axioms TDA.Topology.ProbeFixtures.duplicated_singleton_fixture
#print axioms TDA.Topology.ProbeFixtures.boolCode
#print axioms TDA.Topology.ProbeFixtures.rangeFamily
#print axioms TDA.Topology.ProbeFixtures.rangeFamily_covers_range
#print axioms TDA.Topology.ProbeFixtures.rangeFamily_not_full
#print axioms TDA.Topology.ProbeFixtures.range_pullback_full
#print axioms TDA.Topology.ProbeFixtures.missingRangeFamily
#print axioms TDA.Topology.ProbeFixtures.missingRange_pullback_empty
#print axioms TDA.Topology.ProbeFixtures.allFamily
#print axioms TDA.Topology.ProbeFixtures.identitySelector
#print axioms TDA.Topology.ProbeFixtures.swappedSelector
#print axioms TDA.Topology.ProbeFixtures.selectors_are_distinct

-- Support-aware ordinary nerves of indexed families.
#print axioms TDA.Topology.nerve
#print axioms TDA.Topology.mem_nerve_iff
#print axioms TDA.Topology.mem_nerve_singleton_iff
#print axioms TDA.Topology.mem_nerve_of_nonempty_subset
#print axioms TDA.Topology.nerve_mono
#print axioms TDA.Topology.nerve_eq_bot_of_isEmpty
#print axioms TDA.Topology.mem_nerve_relabel_iff
#print axioms TDA.Topology.mem_nerve_pullback_iff
#print axioms TDA.Topology.nerve_pullback_le
#print axioms TDA.Topology.nerve_pullback_eq_of_surjective

-- Concrete support-aware ordinary-nerve fixtures.
#print axioms TDA.Topology.NerveExamples.emptyMemberFamily
#print axioms TDA.Topology.NerveExamples.emptyMember_has_no_vertex
#print axioms TDA.Topology.NerveExamples.duplicateFamily
#print axioms TDA.Topology.NerveExamples.duplicateFamily_has_two_vertices
#print axioms TDA.Topology.NerveExamples.duplicateFamily_has_edge
#print axioms TDA.Topology.NerveExamples.pairwiseFamily
#print axioms TDA.Topology.NerveExamples.pairwiseFamily_has_all_edges
#print axioms TDA.Topology.NerveExamples.pairwiseFamily_has_no_triangle
#print axioms TDA.Topology.NerveExamples.disjointFamily
#print axioms TDA.Topology.NerveExamples.constantMap
#print axioms TDA.Topology.NerveExamples.disjointFamily_has_target_vertices
#print axioms TDA.Topology.NerveExamples.constantPullback_has_first_vertex
#print axioms TDA.Topology.NerveExamples.constantPullback_has_no_second_vertex
#print axioms TDA.Topology.NerveExamples.constantPullback_is_proper_subcomplex
#print axioms TDA.Topology.NerveExamples.emptyAmbientFamily
#print axioms TDA.Topology.NerveExamples.emptyAmbient_nerve_is_bot
#print axioms TDA.Topology.NerveExamples.emptyIndexFamily
#print axioms TDA.Topology.NerveExamples.emptyIndex_nerve_is_bot

-- Refinement-induced maps of ordinary nerves.
#print axioms TDA.Topology.nerveMap
#print axioms TDA.Topology.nerveMap_apply
#print axioms TDA.Topology.nerveMap_id
#print axioms TDA.Topology.nerveMap_comp
#print axioms TDA.Topology.reindexRefinement
#print axioms TDA.Topology.reindexRefinement_symm
#print axioms TDA.Topology.nerveMap_reindex_comp
#print axioms TDA.Topology.nerveMap_reindex_symm_comp

-- Refinement-induced nerve-map fixtures.
#print axioms TDA.Topology.NerveMapExamples.duplicate_edge_maps_to_singleton
#print axioms TDA.Topology.NerveMapExamples.permutation_reindex_inverse_fixture
#print axioms TDA.Topology.NerveMapExamples.composable_refinements_have_direct_composite
