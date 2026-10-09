-- Live axiom audit input, consumed by scripts/check-axioms.sh.
-- Run after `lake build`:   lake env lean scripts/print_axioms.lean
--
-- Append one `#print axioms` line for every public theorem a PR claims as a result
-- (scripts/check-axiom-coverage.sh fails the gate when one is missing).
-- APPEND-ONLY: removing or renaming a line is a `needs-decision` change.
import TDA

-- Permanent smoke test of the audit path (TDA/Basic.lean). Never remove.
#print axioms TDA.placeholder_add_zero

-- Support-aware filtration API (Issue #10).
#print axioms TDA.Filtration.mem_support_iff
#print axioms TDA.Filtration.mem_bot_iff
#print axioms TDA.Filtration.face_mono
#print axioms TDA.Filtration.support_mono
#print axioms TDA.Filtration.support_eq_empty_of_eq_bot
#print axioms TDA.Filtration.mem_singletonFace_iff
#print axioms TDA.Filtration.vertexBirth_zero
#print axioms TDA.Filtration.vertexBirth_one
#print axioms TDA.Filtration.mem_vertexBirth_iff
#print axioms TDA.Filtration.vertexBirth_support_zero
#print axioms TDA.Filtration.vertexBirth_support_one
#print axioms TDA.Filtration.addSingletons_introduces_singleton
#print axioms TDA.Filtration.reindex_apply
#print axioms TDA.Filtration.reindex_id
#print axioms TDA.Filtration.reindex_comp

-- Preorder-indexed persistence-module API (Issue #11).
#print axioms TDA.Persistence.structureMap_self
#print axioms TDA.Persistence.structureMap_comp
#print axioms TDA.Persistence.structureMapLinear_self
#print axioms TDA.Persistence.structureMapLinear_comp
#print axioms TDA.Persistence.reindex_obj
#print axioms TDA.Persistence.structureMap_reindex
#print axioms TDA.Persistence.structureMapLinear_reindex
#print axioms TDA.Persistence.reindex_id
#print axioms TDA.Persistence.reindex_comp
#print axioms TDA.Persistence.reindexNatTrans_app
#print axioms TDA.Persistence.reindexNatTrans_id
#print axioms TDA.Persistence.reindexNatTrans_comp
#print axioms TDA.Persistence.integerZeroTransition_map
#print axioms TDA.Persistence.integerZeroTransition_nonidentity
#print axioms TDA.Persistence.zmodTwoZeroTransition_map
#print axioms TDA.Persistence.zmodTwoZeroTransition_nonidentity
#print axioms TDA.Persistence.integerIdentityTransition_map

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

-- Finite column pivots and cancellation (Issue #35).
#print axioms TDA.Persistence.Reduction.columnPivot_none_iff
#print axioms TDA.Persistence.Reduction.columnPivot_zero
#print axioms TDA.Persistence.Reduction.columnPivot_some_iff
#print axioms TDA.Persistence.Reduction.pivotHeight_none
#print axioms TDA.Persistence.Reduction.pivotHeight_some
#print axioms TDA.Persistence.Reduction.pivotHeight_eq_zero_iff
#print axioms TDA.Persistence.Reduction.cancelColumn_apply_pivot
#print axioms TDA.Persistence.Reduction.cancelColumn_apply_above
#print axioms TDA.Persistence.Reduction.pivotHeight_cancelColumn_lt
#print axioms TDA.Persistence.Reduction.col_mul_transvection
#print axioms TDA.Persistence.Reduction.col_mul_transvection_of_ne
#print axioms TDA.Persistence.Reduction.pivotHeight_mul_transvection_lt

-- Open-set path-component functors (Issue #24).
#print axioms TDA.Reeb.componentMap_mk
#print axioms TDA.Reeb.componentMap_id
#print axioms TDA.Reeb.componentMap_comp
#print axioms TDA.Reeb.preimageInclusion_eq_inclusion
#print axioms TDA.Reeb.componentFunctor_obj
#print axioms TDA.Reeb.componentFunctor_map_mk
#print axioms TDA.Reeb.componentFunctor_map_apply
#print axioms TDA.Reeb.componentFunctor_obj_bot_isEmpty
#print axioms TDA.Reeb.componentFunctor_obj_isEmpty_of_isEmpty
#print axioms TDA.Reeb.componentFunctor_obj_isEmpty_of_base_isEmpty
#print axioms TDA.Reeb.componentNatTrans_app_mk
#print axioms TDA.Reeb.componentNatTrans_app_apply
#print axioms TDA.Reeb.componentNatTrans_naturality
#print axioms TDA.Reeb.componentNatTrans_naturality_mk
#print axioms TDA.Reeb.componentNatTrans_id
#print axioms TDA.Reeb.componentNatTrans_comp
#print axioms TDA.Reeb.componentNatTrans_comp_app_mk
#print axioms TDA.Reeb.componentNatTrans_proof_irrel
#print axioms TDA.Reeb.Examples.eq_of_joined_of_discrete
#print axioms TDA.Reeb.Examples.boolComponentsEquiv_boolClass
#print axioms TDA.Reeb.Examples.boolClass_false_ne_true
#print axioms TDA.Reeb.Examples.boolClass_exhaustive
#print axioms TDA.Reeb.Examples.collapseNatTrans_identifies
#print axioms TDA.Reeb.Examples.collapseNatTrans_not_injective
#print axioms TDA.Reeb.Examples.swapNatTrans_boolClass
#print axioms TDA.Reeb.Examples.collapse_comp_swap
#print axioms TDA.Reeb.Examples.falseOpen_le_top
#print axioms TDA.Reeb.Examples.falseOpen_ne_top
#print axioms TDA.Reeb.Examples.true_absent_falseOpen
#print axioms TDA.Reeb.Examples.falseOpen_inclusion_mk
