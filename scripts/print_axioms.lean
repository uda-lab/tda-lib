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
