-- Live axiom audit pins for Topology. Append new pins here; do not remove existing pins.
import TDA


-- Generic path-component maps and inverse-image inclusions.
#print axioms TDA.Topology.componentMap_mk
#print axioms TDA.Topology.componentMap_id
#print axioms TDA.Topology.componentMap_comp
#print axioms TDA.Topology.preimageSetInclusion
#print axioms TDA.Topology.preimageSetInclusion_apply
#print axioms TDA.Topology.preimageSetInclusion_id
#print axioms TDA.Topology.preimageSetInclusion_comp
#print axioms TDA.Topology.mk_eq_of_joinedIn


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

-- Contiguity of refinement-induced nerve maps.
#print axioms TDA.Topology.nerveMap_contiguous

-- Multinerves of indexed families (Issue #277).
#print axioms TDA.Topology.interMember
#print axioms TDA.Topology.mem_interMember_iff
#print axioms TDA.Topology.interMember_anti
#print axioms TDA.Topology.interMember_subset
#print axioms TDA.Topology.interMember_singleton
#print axioms TDA.Topology.interMember_insert
#print axioms TDA.Topology.faceMap
#print axioms TDA.Topology.faceMap_mk
#print axioms TDA.Topology.faceMap_refl
#print axioms TDA.Topology.faceMap_self
#print axioms TDA.Topology.faceMap_trans
#print axioms TDA.Topology.faceMap_faceMap
#print axioms TDA.Topology.MultiNerveCell
#print axioms TDA.Topology.isEmpty_cellsOver_iff
#print axioms TDA.Topology.MultiNerveCell.mk
#print axioms TDA.Topology.MultiNerveCell.support
#print axioms TDA.Topology.MultiNerveCell.component
#print axioms TDA.Topology.MultiNerveCell.carrier
#print axioms TDA.Topology.MultiNerveCell.support_mk
#print axioms TDA.Topology.MultiNerveCell.component_mk
#print axioms TDA.Topology.MultiNerveCell.support_nonempty
#print axioms TDA.Topology.MultiNerveCell.eta
#print axioms TDA.Topology.MultiNerveCell.ext_of_support_eq
#print axioms TDA.Topology.MultiNerveCell.carrier_subset
#print axioms TDA.Topology.MultiNerveCell.carrier_nonempty
#print axioms TDA.Topology.MultiNerveCell.instPartialOrder
#print axioms TDA.Topology.MultiNerveCell.le_def
#print axioms TDA.Topology.MultiNerveCell.support_mono
#print axioms TDA.Topology.MultiNerveCell.face
#print axioms TDA.Topology.MultiNerveCell.support_face
#print axioms TDA.Topology.MultiNerveCell.face_le
#print axioms TDA.Topology.MultiNerveCell.eq_face_of_le
#print axioms TDA.Topology.MultiNerveCell.face_le_face_iff
#print axioms TDA.Topology.MultiNerveCell.lowerSetOrderIso
#print axioms TDA.Topology.MultiNerveCell.lowerSetOrderIso_apply
#print axioms TDA.Topology.MultiNerveCell.support_mem_nerve
#print axioms TDA.Topology.MultiNerveCell.exists_cell_of_mem_nerve
#print axioms TDA.Topology.projection
#print axioms TDA.Topology.projection_coe
#print axioms TDA.Topology.projection_monotone
#print axioms TDA.Topology.projection_surjective
#print axioms TDA.Topology.cellsOverEquiv
#print axioms TDA.Topology.cellsOverEquiv_symm_apply
#print axioms TDA.Topology.IntersectionsPathSubsingleton
#print axioms TDA.Topology.projection_injective_iff
#print axioms TDA.Topology.multiNerveOrderIso
#print axioms TDA.Topology.coe_multiNerveOrderIso
#print axioms TDA.Topology.subsingleton_zerothHomotopy_of_isPathConnected
#print axioms TDA.Topology.intersectionsPathSubsingleton_of_isPathConnected
#print axioms TDA.Topology.MultiNerveExamples.singletonFamily
#print axioms TDA.Topology.MultiNerveExamples.singletonFamily_interMember_pair
#print axioms TDA.Topology.MultiNerveExamples.singletonFamily_no_cell_over_pair
#print axioms TDA.Topology.MultiNerveExamples.duplicateFamily
#print axioms TDA.Topology.MultiNerveExamples.duplicateCell
#print axioms TDA.Topology.MultiNerveExamples.duplicate_labels_distinct_vertex_cells


-- Refinement-induced maps of multinerves (Issue #289).
#print axioms TDA.Topology.interMember_image_subset
#print axioms TDA.Topology.refinementFaceMap
#print axioms TDA.Topology.refinementFaceMap_mk
#print axioms TDA.Topology.refinementFaceMap_faceMap
#print axioms TDA.Topology.multiNerveMap
#print axioms TDA.Topology.support_multiNerveMap
#print axioms TDA.Topology.multiNerveMap_mk
#print axioms TDA.Topology.multiNerveMap_monotone
#print axioms TDA.Topology.multiNerveMap_face
#print axioms TDA.Topology.multiNerveMap_id
#print axioms TDA.Topology.multiNerveMap_comp
#print axioms TDA.Topology.projection_multiNerveMap
#print axioms TDA.Topology.MultiNerveMapExamples.carrier_subsingleton_of_discrete
#print axioms TDA.Topology.MultiNerveMapExamples.fullFamily
#print axioms TDA.Topology.MultiNerveMapExamples.collapseRefinement
#print axioms TDA.Topology.MultiNerveMapExamples.pointCell
#print axioms TDA.Topology.MultiNerveMapExamples.collapse_nerveMap_not_injective
#print axioms TDA.Topology.MultiNerveMapExamples.collapse_multiNerveMap_separates
#print axioms TDA.Topology.MultiNerveMapExamples.multiNerveMap_id_pointCell

-- Bounded C₀ functionals and compact-support approximation.
#print axioms TDA.Topology.C0MeasureRepresentation.denseRange_compactlySupported
#print axioms TDA.Topology.C0MeasureRepresentation.exists_finite_regular_measure_sub

-- Normalized subdivision-Rips and restricted measure bifiltrations.
#print axioms TDA.Topology.MeasureBifiltration.cross_le_iff
#print axioms TDA.Topology.MeasureBifiltration.stage_mono
#print axioms TDA.Topology.MeasureBifiltration.ball_mass_le
#print axioms TDA.Topology.MeasureBifiltration.stage_cross
#print axioms TDA.Topology.MeasureBifiltration.interleavingDiagram_left
#print axioms TDA.Topology.MeasureBifiltration.interleavingDiagram_right
#print axioms TDA.Topology.MeasureBifiltration.uniformMeasure_apply
#print axioms TDA.Topology.MeasureBifiltration.uniformMeasure_real
#print axioms TDA.Topology.MeasureBifiltration.topologicalInterleaving_left
#print axioms TDA.Topology.MeasureBifiltration.topologicalInterleaving_right
#print axioms TDA.Topology.MeasureBifiltration.interleavingDiagram
#print axioms TDA.Topology.MeasureBifiltration.topologicalInterleaving
#print axioms TDA.Topology.MeasureBifiltration.uniformInterleavingDiagram
#print axioms TDA.Topology.MeasureBifiltration.uniformMeasure_probability
#print axioms TDA.Topology.MeasureBifiltration.interleavingIndex_le_iff

-- Finite uniform GP, outliers and concrete multicover comparisons.
#print axioms TDA.Topology.MeasureBifiltration.labelCount_le_card
#print axioms TDA.Topology.MeasureBifiltration.labelCount_comp_embedding_le
#print axioms TDA.Topology.MeasureBifiltration.uniformMeasure_real_comp_embedding_le
#print axioms TDA.Topology.MeasureBifiltration.levyProkhorovDist_uniform_embedding_le
#print axioms TDA.Topology.MeasureBifiltration.levyProkhorovEDist_uniform_embedding_le
#print axioms TDA.Topology.MeasureBifiltration.uniformOutlierInterleaving
#print axioms TDA.Topology.MeasureBifiltration.uniformOutlierInterleaving_left
#print axioms TDA.Topology.MeasureBifiltration.uniformOutlierInterleaving_right
#print axioms TDA.Topology.MeasureBifiltration.uniformMeasure_apply_le_of_label_mem
#print axioms TDA.Topology.MeasureBifiltration.levyProkhorovDist_uniform_le_of_cross_dist_le
#print axioms TDA.Topology.MeasureBifiltration.levyProkhorovEDist_uniform_le_of_cross_dist_le
#print axioms TDA.Topology.MeasureBifiltration.levyProkhorovEDist_uniform_eq_of_cross_dist_eq
#print axioms TDA.Topology.FiniteGromovProkhorov.CommonAmbient.isometry_left
#print axioms TDA.Topology.FiniteGromovProkhorov.CommonAmbient.isometry_right
#print axioms TDA.Topology.FiniteGromovProkhorov.CommonAmbient.symm
#print axioms TDA.Topology.FiniteGromovProkhorov.disjointAmbient
#print axioms TDA.Topology.FiniteGromovProkhorov.landmarkCoordinates
#print axioms TDA.Topology.FiniteGromovProkhorov.landmarkCoordinates_dist
#print axioms TDA.Topology.FiniteGromovProkhorov.coordinatesAmbient
#print axioms TDA.Topology.FiniteGromovProkhorov.CommonAmbient.cost
#print axioms TDA.Topology.FiniteGromovProkhorov.gromovProkhorovEDist
#print axioms TDA.Topology.FiniteGromovProkhorov.gromovProkhorovEDist_le_cost
#print axioms TDA.Topology.FiniteGromovProkhorov.gromovProkhorovEDist_lt_iff
#print axioms TDA.Topology.FiniteGromovProkhorov.CommonAmbient.cost_symm
#print axioms TDA.Topology.FiniteGromovProkhorov.gromovProkhorovEDist_comm
#print axioms TDA.Topology.FiniteGromovProkhorov.coordinatesAmbient_cost
#print axioms TDA.Topology.FiniteGromovProkhorov.gromovProkhorovEDist_le_ambient
#print axioms TDA.Topology.FiniteGromovProkhorov.CommonAmbient.cost_le_one
#print axioms TDA.Topology.FiniteGromovProkhorov.gromovProkhorovEDist_le_one
#print axioms TDA.Topology.FiniteGromovProkhorov.inclusionAmbient
#print axioms TDA.Topology.FiniteGromovProkhorov.gromovProkhorovEDist_embedding_le
#print axioms TDA.Topology.FiniteGromovProkhorov.gromovProkhorovEDist_self
#print axioms TDA.Topology.MeasureBifiltration.faceRegion
#print axioms TDA.Topology.MeasureBifiltration.mem_stage_uniform_iff_large_face
#print axioms TDA.Topology.MeasureBifiltration.stage_uniform_eq_iUnion_large_face
#print axioms TDA.Topology.MeasureBifiltration.isOpen_faceRegion
#print axioms TDA.Topology.MeasureBifiltration.largeFaceCover
#print axioms TDA.Topology.MeasureBifiltration.largeFaceCover_mono
#print axioms TDA.Topology.MeasureBifiltration.subdivision_openCech_le_largeFaceNerve
#print axioms TDA.Topology.MeasureBifiltration.stage_uniform_eq_iUnion_largeFaceCover
#print axioms TDA.Topology.MeasureBifiltration.mem_largeFaceNerve_iff
#print axioms TDA.Topology.MeasureBifiltration.largeFaceNerveBifiltration
#print axioms TDA.Topology.MeasureBifiltration.isOpen_largeFaceCover
#print axioms TDA.Topology.MeasureBifiltration.convex_faceRegion
#print axioms TDA.Topology.MeasureBifiltration.convex_largeFaceCover
#print axioms TDA.Topology.MeasureBifiltration.contractibleSpace_largeFaceCover_intersection
#print axioms TDA.Topology.MeasureBifiltration.levyProkhorovDist_uniform_le_of_isClosed
#print axioms TDA.Topology.FiniteGromovProkhorov.supNormWitness
#print axioms TDA.Topology.FiniteGromovProkhorov.SupNormWitness.interleaving
#print axioms TDA.Topology.FiniteGromovProkhorov.SupNormWitness.interleaving_left
#print axioms TDA.Topology.FiniteGromovProkhorov.SupNormWitness.interleaving_right

-- Finite GP stability of the normalized subdivision-Rips homology consumer (Issue #504).
#print axioms TDA.Topology.FiniteGromovProkhorov.SupNormWitness.largeFaceNerveHomologyInterleaving_left
#print axioms TDA.Topology.FiniteGromovProkhorov.SupNormWitness.largeFaceNerveHomologyInterleaving_right
#print axioms TDA.Topology.FiniteGromovProkhorov.SupNormWitness.homologyInterleaving_left
#print axioms TDA.Topology.FiniteGromovProkhorov.SupNormWitness.homologyInterleaving_right
#print axioms TDA.Topology.FiniteGromovProkhorov.subdivisionRipsHomologyInterleavingDistance_le_gromovProkhorovEDist
#print axioms TDA.Topology.FiniteGromovProkhorov.subdivisionRipsHomologyInterleaving_of_isometric_embedding
