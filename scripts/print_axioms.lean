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

-- Path-component Reeb quotient and its universal property (Issue #27).
#print axioms TDA.Reeb.reebRel_iff_joinedIn
#print axioms TDA.Reeb.ReebRel.apply_eq
#print axioms TDA.Reeb.reebRel_iff_joined_fiber
#print axioms TDA.Reeb.ReebRel.refl
#print axioms TDA.Reeb.ReebRel.symm
#print axioms TDA.Reeb.ReebRel.trans
#print axioms TDA.Reeb.reebSetoid_r
#print axioms TDA.Reeb.reebRel_iff_eq_of_injective
#print axioms TDA.Reeb.reebRel_const_iff
#print axioms TDA.Reeb.ReebQuotient.mk_surjective
#print axioms TDA.Reeb.ReebQuotient.isQuotientMap_mk
#print axioms TDA.Reeb.ReebQuotient.continuous_mk
#print axioms TDA.Reeb.ReebQuotient.proj_apply
#print axioms TDA.Reeb.ReebQuotient.mk_eq_mk_iff
#print axioms TDA.Reeb.ReebQuotient.mk_eq_mk_of_path
#print axioms TDA.Reeb.ReebQuotient.ind
#print axioms TDA.Reeb.ReebQuotient.lift_mk
#print axioms TDA.Reeb.ReebQuotient.lift_comp_proj
#print axioms TDA.Reeb.ReebQuotient.lift_unique
#print axioms TDA.Reeb.ReebQuotient.hom_ext
#print axioms TDA.Reeb.ReebQuotient.existsUnique_lift
#print axioms TDA.Reeb.ReebQuotient.apply_eq_of_reebRel
#print axioms TDA.Reeb.ReebQuotient.height_mk
#print axioms TDA.Reeb.ReebQuotient.height_comp_proj
#print axioms TDA.Reeb.ReebQuotient.instIsEmpty
#print axioms TDA.Reeb.ReebQuotient.homeomorphOfInjective_mk
#print axioms TDA.Reeb.ReebQuotient.homeomorphZerothHomotopy_mk
#print axioms TDA.Reeb.ReebQuotient.subsingleton_of_const
#print axioms TDA.Reeb.Examples.boolConst_mk_false_ne_true
#print axioms TDA.Reeb.Examples.boolConst_eq_mk_false_or_mk_true
