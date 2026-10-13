-- Live axiom audit pins for Simplicial. Append new pins here; do not remove existing pins.
import TDA


-- Support-aware simplicial bridge prototype (Issue #13).
#print axioms TDA.Simplicial.chainIncl_id
#print axioms TDA.Simplicial.chainIncl_comp
#print axioms TDA.Simplicial.emptyChain_eq_zero
#print axioms TDA.Simplicial.emptyH0_eq_zero
#print axioms TDA.Simplicial.singletonHigherChain_eq_zero
#print axioms TDA.Simplicial.faceFiniteOfTotalFinite
#print axioms TDA.Simplicial.emptyFaceIsEmpty
#print axioms TDA.Simplicial.singletonFaceZeroSubsingleton
#print axioms TDA.Simplicial.singletonFaceHigherIsEmpty

-- Ordered actual-face boundary (Issue #23).
#print axioms TDA.Simplicial.enumerationAfterDeletion
#print axioms TDA.Simplicial.boundary_single

-- Ordered actual-face square-zero and ordinary chain complex (Issue #39).
#print axioms TDA.Simplicial.boundary_comp_boundary
#print axioms TDA.Simplicial.simplicialChainComplex_X
#print axioms TDA.Simplicial.simplicialChainComplex_d
#print axioms TDA.Simplicial.simplicialChainComplex_d_zero

-- Actual simplicial chain inclusion naturality and chain maps (Issue #86).
#print axioms TDA.Simplicial.simplicialChainIncl
#print axioms TDA.Simplicial.faceIncl_deletedFace
#print axioms TDA.Simplicial.chainIncl_single
#print axioms TDA.Simplicial.boundary_chainIncl
#print axioms TDA.Simplicial.simplicialChainIncl_f
#print axioms TDA.Simplicial.simplicialChainIncl_id
#print axioms TDA.Simplicial.simplicialChainIncl_comp

-- Finite support-aware complex presentations and their exact actual-face conversion (Issue #97).
#print axioms TDA.Simplicial.FiniteComplex.mem_toPre
#print axioms TDA.Simplicial.FiniteComplex.empty_not_mem_faces
#print axioms TDA.Simplicial.FiniteComplex.image_univ_totalFace_val
#print axioms TDA.Simplicial.FiniteComplex.card_totalFace
#print axioms TDA.Simplicial.FiniteComplex.toPre_injective

-- Actual simplicial homology and inclusion (Issue #117).
#print axioms TDA.Simplicial.simplicialHomology
#print axioms TDA.Simplicial.simplicialCycles
#print axioms TDA.Simplicial.simplicialBoundaries
#print axioms TDA.Simplicial.simplicialCycles_zero
#print axioms TDA.Simplicial.simplicialCycles_succ
#print axioms TDA.Simplicial.mem_simplicialBoundaries_iff
#print axioms TDA.Simplicial.simplicialCycleIncl
#print axioms TDA.Simplicial.simplicialCycleIncl_coe
#print axioms TDA.Simplicial.simplicialCycleIncl_id
#print axioms TDA.Simplicial.simplicialCycleIncl_comp
#print axioms TDA.Simplicial.simplicialCycleIncl_toCycles
#print axioms TDA.Simplicial.simplicialBoundaries_le_comap
#print axioms TDA.Simplicial.simplicialQuotientIncl
#print axioms TDA.Simplicial.simplicialQuotientIncl_mkQ
#print axioms TDA.Simplicial.simplicialQuotientIncl_id
#print axioms TDA.Simplicial.simplicialQuotientIncl_comp
#print axioms TDA.Simplicial.simplicialHomologyIncl
#print axioms TDA.Simplicial.simplicialHomologyIncl_id
#print axioms TDA.Simplicial.simplicialHomologyIncl_comp
#print axioms TDA.Simplicial.simplicialHomologyIncl_quotient_naturality
#print axioms TDA.Simplicial.simplicialHomology_bot_zero
#print axioms TDA.Simplicial.simplicialSingletonH0Equiv
#print axioms TDA.Simplicial.simplicialSingletonH0Equiv_symm_one_ne_zero

#print axioms TDA.Simplicial.chainCoordinates_apply
#print axioms TDA.Simplicial.boundaryMatrix_apply
#print axioms TDA.Simplicial.boundaryMatrix_deletedFace
#print axioms TDA.Simplicial.boundaryMatrix_eq_zero_of_not_deletedFace
#print axioms TDA.Simplicial.boundaryMatrix_mulVec
#print axioms TDA.Simplicial.boundaryMatrix_toLin
#print axioms TDA.Simplicial.boundaryMatrix_mul_boundaryMatrix
#print axioms TDA.Simplicial.simplicialChainComplex_d_zero_toMatrix
#print axioms TDA.Simplicial.chainInclusionMatrix_apply
#print axioms TDA.Simplicial.chainInclusionMatrix_mulVec
#print axioms TDA.Simplicial.boundaryMatrix_chainInclusionMatrix

-- Coordinate cycles and incoming boundaries in actual finite simplicial chains.
#print axioms TDA.Simplicial.coordinateCycles_zero
#print axioms TDA.Simplicial.coordinateCycles_succ
#print axioms TDA.Simplicial.cycleCoordinates_coe
#print axioms TDA.Simplicial.coordinateBoundaryToCycles_coe
#print axioms TDA.Simplicial.mem_coordinateBoundaries_iff
#print axioms TDA.Simplicial.simplicialBoundaries_map_cycleCoordinates
#print axioms TDA.Simplicial.coordinateCycleIncl_coe
#print axioms TDA.Simplicial.cycleCoordinates_naturality
#print axioms TDA.Simplicial.coordinateCycleIncl_boundaryToCycles
#print axioms TDA.Simplicial.coordinateBoundaries_le_comap

-- TDA.Simplicial.FiniteHomology: canonical coordinate quotient and ordinary homology naturality.
#print axioms TDA.Simplicial.coordinateHomology
#print axioms TDA.Simplicial.quotientCoordinates
#print axioms TDA.Simplicial.simplicialHomologyCoordinates
#print axioms TDA.Simplicial.coordinateHomologyIncl
#print axioms TDA.Simplicial.quotientCoordinates_mkQ
#print axioms TDA.Simplicial.simplicialHomologyCoordinates_mkQ
#print axioms TDA.Simplicial.coordinateHomologyIncl_mkQ
#print axioms TDA.Simplicial.quotientCoordinates_naturality
#print axioms TDA.Simplicial.simplicialHomologyCoordinates_naturality
#print axioms TDA.Simplicial.coordinateHomologyIncl_id
#print axioms TDA.Simplicial.coordinateHomologyIncl_comp

-- Actual critical-grade simplicial homology and its canonical finite-index barcode (Issue #146).
#print axioms TDA.Simplicial.simplicialHomology_finiteDimensional

-- Actual one-simplex homology attachment (Issue #183).
#print axioms TDA.Simplicial.SimplexAttachment.inclusion
#print axioms TDA.Simplicial.SimplexAttachment.simplex_mem
#print axioms TDA.Simplicial.SimplexAttachment.faceIncl_injective
#print axioms TDA.Simplicial.SimplexAttachment.newFace_not_range
#print axioms TDA.Simplicial.SimplexAttachment.old_of_ne
#print axioms TDA.Simplicial.SimplexAttachment.old_of_degree_ne
#print axioms TDA.Simplicial.SimplexAttachment.old_face_of_degree_ne
#print axioms TDA.Simplicial.SimplexAttachment.chainIncl_injective
#print axioms TDA.Simplicial.SimplexAttachment.chainIncl_surjective_of_ne
#print axioms TDA.Simplicial.SimplexAttachment.chainIncl_new_coeff
#print axioms TDA.Simplicial.SimplexAttachment.chain_decomposition
#print axioms TDA.Simplicial.SimplexAttachment.chainIncl_range_iff_coeff_zero
#print axioms TDA.Simplicial.SimplexAttachment.cycleIncl_surjective_of_ne
#print axioms TDA.Simplicial.SimplexAttachment.old_cycle_of_included_chain
#print axioms TDA.Simplicial.SimplexAttachment.boundary_new_coeff_zero
#print axioms TDA.Simplicial.SimplexAttachment.boundaries_new_coeff_zero
#print axioms TDA.Simplicial.SimplexAttachment.cycleIncl_surjective_of_coeff_zero
#print axioms TDA.Simplicial.SimplexAttachment.quotientIncl_surjective_of_coeff_zero
#print axioms TDA.Simplicial.SimplexAttachment.new_cycle_class_not_range
#print axioms TDA.Simplicial.SimplexAttachment.quotient_range_sup_birth_span_eq_top
#print axioms TDA.Simplicial.SimplexAttachment.quotientIncl_birth_cokernel_finrank
#print axioms TDA.Simplicial.SimplexAttachment.boundary_reflect_of_ne
#print axioms TDA.Simplicial.SimplexAttachment.quotientIncl_injective_of_ne
#print axioms TDA.Simplicial.SimplexAttachment.quotientIncl_surjective_of_ne
#print axioms TDA.Simplicial.SimplexAttachment.homologyIncl_bijective_of_ne
#print axioms TDA.Simplicial.SimplexAttachment.homologyIncl_injective_of_succ_ne
#print axioms TDA.Simplicial.SimplexAttachment.homologyIncl_surjective_of_quotient
#print axioms TDA.Simplicial.SimplexAttachment.homologyIncl_birth_cokernel_finrank
#print axioms TDA.Simplicial.SimplexAttachment.homologyIncl_birth_generator
#print axioms TDA.Simplicial.SimplexAttachment.oldDeletedFace_incl
#print axioms TDA.Simplicial.SimplexAttachment.attachingBoundary_incl
#print axioms TDA.Simplicial.SimplexAttachment.attachingBoundary_ne_zero
#print axioms TDA.Simplicial.SimplexAttachment.boundary_of_decomposition
#print axioms TDA.Simplicial.SimplexAttachment.boundary_of_chain
#print axioms TDA.Simplicial.SimplexAttachment.attachingQuotientClass_maps_zero
#print axioms TDA.Simplicial.SimplexAttachment.quotientIncl_ker_eq_span_attachingClass
#print axioms TDA.Simplicial.SimplexAttachment.attachingHomologyClass_equiv
#print axioms TDA.Simplicial.SimplexAttachment.homologyIncl_ker_eq_span_attachingClass
#print axioms TDA.Simplicial.SimplexAttachment.homologyIncl_death_kernel_finrank
#print axioms TDA.Simplicial.SimplexAttachment.new_coeff_zero_of_attachingClass_ne_zero
#print axioms TDA.Simplicial.SimplexAttachment.homologyIncl_bijective_of_attachingClass_ne_zero
#print axioms TDA.Simplicial.SimplexAttachment.attachingClass_zero_iff_boundary
#print axioms TDA.Simplicial.SimplexAttachment.attachingClass_ne_zero_of_no_old_coface
#print axioms TDA.Simplicial.SimplexAttachment.birth_cycle_of_attachingClass_zero
#print axioms TDA.Simplicial.SimplexAttachment.isolatedVertexCycle_coeff
#print axioms TDA.Simplicial.SimplexAttachment.isolatedVertex_birth
#print axioms TDA.Simplicial.SimplexAttachment.isolatedVertex_generates
#print axioms TDA.Simplicial.SimplexAttachment.positive_birth
#print axioms TDA.Simplicial.SimplexAttachment.positive_birth_generator
#print axioms TDA.Simplicial.SimplexAttachment.positive_death
#print axioms TDA.Simplicial.SimplexAttachment.chain_decomposition_unique
#print axioms TDA.Simplicial.AttachmentExamples.filled_triangle_H1_birth_and_death
#print axioms TDA.Simplicial.zeroChainSum_single
#print axioms TDA.Simplicial.zeroChainSum_boundary
#print axioms TDA.Simplicial.zeroChainSum_chainIncl
#print axioms TDA.Simplicial.selectedZeroChainSum_single
#print axioms TDA.Simplicial.selectedZeroChainSum_boundary
#print axioms TDA.Simplicial.zeroVertexCycle_not_boundary
#print axioms TDA.Simplicial.vertexCombination_not_boundary_of_selected
#print axioms TDA.Simplicial.zeroShortF_of_no_edges
#print axioms TDA.Simplicial.zeroShortG
#print axioms TDA.Simplicial.finrank_zeroHomology_of_no_edges
#print axioms TDA.Simplicial.finrank_homologyIncl_range_eq_quotientIncl_range
#print axioms TDA.Simplicial.zeroVertexCycle_incl
#print axioms TDA.Simplicial.zeroVertexCycle_incl_not_boundary
#print axioms TDA.Simplicial.finrank_homologyIncl_range_pos_of_vertex
#print axioms TDA.Simplicial.quotientIncl_injective_of_two_vertices_separated
#print axioms TDA.Simplicial.SimplexAttachment.attachingHomologyClass_ne_zero_of_separated_vertices

-- Noninjective simplicial vertex maps.
#print axioms TDA.Simplicial.VertexMap
#print axioms TDA.Simplicial.VertexMap.id
#print axioms TDA.Simplicial.VertexMap.comp
#print axioms TDA.Simplicial.VertexMap.ext
#print axioms TDA.Simplicial.VertexMap.ext_iff
#print axioms TDA.Simplicial.VertexMap.comp_apply
#print axioms TDA.Simplicial.VertexMap.id_apply
#print axioms TDA.Simplicial.VertexMap.id_comp
#print axioms TDA.Simplicial.VertexMap.comp_id
#print axioms TDA.Simplicial.VertexMap.comp_assoc
#print axioms TDA.Simplicial.map_le_iff
#print axioms TDA.Simplicial.VertexMap.map_le_iff

-- Noninjective vertex-map fixtures.
#print axioms TDA.Simplicial.VertexMapExamples.edge_collapse_fixture
#print axioms TDA.Simplicial.VertexMapExamples.permutation_inverse_fixture
#print axioms TDA.Simplicial.VertexMapExamples.ghost_vertices_are_not_forced
