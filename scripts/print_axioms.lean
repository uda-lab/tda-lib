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

-- Real open intervals and thickening (Issue #29).
#print axioms TDA.Reeb.OpenInterval
#print axioms TDA.Reeb.OpenInterval.ext
#print axioms TDA.Reeb.OpenInterval.ext_iff
#print axioms TDA.Reeb.OpenInterval.mem_mk
#print axioms TDA.Reeb.OpenInterval.coe_mk
#print axioms TDA.Reeb.OpenInterval.isOpen
#print axioms TDA.Reeb.OpenInterval.ordConnected
#print axioms TDA.Reeb.OpenInterval.le_iff_subset
#print axioms TDA.Reeb.OpenInterval.coe_bot
#print axioms TDA.Reeb.OpenInterval.coe_top
#print axioms TDA.Reeb.OpenInterval.ioo
#print axioms TDA.Reeb.OpenInterval.ioi
#print axioms TDA.Reeb.OpenInterval.iio
#print axioms TDA.Reeb.OpenInterval.coe_ioo
#print axioms TDA.Reeb.OpenInterval.coe_ioi
#print axioms TDA.Reeb.OpenInterval.coe_iio
#print axioms TDA.Reeb.OpenInterval.coe_inf
#print axioms TDA.Reeb.OpenInterval.ofEReal
#print axioms TDA.Reeb.OpenInterval.mem_ofEReal
#print axioms TDA.Reeb.OpenInterval.lower
#print axioms TDA.Reeb.OpenInterval.upper
#print axioms TDA.Reeb.OpenInterval.ofEReal_lower_upper
#print axioms TDA.Reeb.OpenInterval.exists_eq_ofEReal
#print axioms TDA.Reeb.OpenInterval.toOpens
#print axioms TDA.Reeb.OpenInterval.coe_toOpens
#print axioms TDA.Reeb.OpenInterval.toOpens_monotone
#print axioms TDA.Reeb.OpenInterval.toOpens_le_iff
#print axioms TDA.Reeb.OpenInterval.toOpens_inf
#print axioms TDA.Reeb.OpenInterval.iSup_toOpens_eq
#print axioms TDA.Reeb.OpenInterval.toOpensFunctor
#print axioms TDA.Reeb.OpenInterval.thickenSet
#print axioms TDA.Reeb.OpenInterval.mem_thickenSet
#print axioms TDA.Reeb.OpenInterval.isOpen_thickenSet
#print axioms TDA.Reeb.OpenInterval.ordConnected_thickenSet
#print axioms TDA.Reeb.OpenInterval.thicken
#print axioms TDA.Reeb.OpenInterval.coe_thicken
#print axioms TDA.Reeb.OpenInterval.mem_thicken
#print axioms TDA.Reeb.OpenInterval.thicken_zero
#print axioms TDA.Reeb.OpenInterval.thicken_bot
#print axioms TDA.Reeb.OpenInterval.thicken_top
#print axioms TDA.Reeb.OpenInterval.le_thicken
#print axioms TDA.Reeb.OpenInterval.thicken_mono
#print axioms TDA.Reeb.OpenInterval.thicken_monotone
#print axioms TDA.Reeb.OpenInterval.thicken_le_thicken_of_le
#print axioms TDA.Reeb.OpenInterval.thicken_thicken
#print axioms TDA.Reeb.OpenInterval.thicken_thicken'
#print axioms TDA.Reeb.OpenInterval.thicken_comm
#print axioms TDA.Reeb.OpenInterval.thicken_ioo
#print axioms TDA.Reeb.OpenInterval.thicken_ioi
#print axioms TDA.Reeb.OpenInterval.thicken_iio
#print axioms TDA.Reeb.OpenInterval.thickenSet_eq_thickening
#print axioms TDA.Reeb.OpenInterval.coe_thicken_eq_thickening
#print axioms TDA.Reeb.OpenInterval.thickenFunctor
#print axioms TDA.Reeb.OpenInterval.thickenFunctor_obj
#print axioms TDA.Reeb.OpenInterval.thickenUnit
#print axioms TDA.Reeb.OpenInterval.thickenMap
#print axioms TDA.Reeb.OpenInterval.thickenZeroIso
#print axioms TDA.Reeb.OpenInterval.thickenCompIso
#print axioms TDA.Reeb.OpenInterval.thickenUnit_comp

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

-- Component-language consequence of the path-local cover lemma (Issue #25).
#print axioms TDA.Reeb.componentFunctor_mk_eq_iff_joined
#print axioms TDA.Reeb.componentFunctor_reflTransGen_of_mk_eq
#print axioms TDA.Reeb.Examples.twoOpens_cover
#print axioms TDA.Reeb.Examples.twoOpens_zero_one_chain
#print axioms TDA.Reeb.Examples.twoOpens_zero_one_not_single_link

-- Reeb quotient functor and its comparison with path components (Issue #28).
#print axioms TDA.Reeb.ReebRel.map
#print axioms TDA.Reeb.overBaseMap
#print axioms TDA.Reeb.overBaseMap_comm
#print axioms TDA.Reeb.ReebQuotient.map
#print axioms TDA.Reeb.ReebQuotient.map_mk
#print axioms TDA.Reeb.ReebQuotient.map_comp_proj
#print axioms TDA.Reeb.ReebQuotient.map_unique
#print axioms TDA.Reeb.ReebQuotient.height_map_apply
#print axioms TDA.Reeb.ReebQuotient.height_comp_map
#print axioms TDA.Reeb.ReebQuotient.map_id
#print axioms TDA.Reeb.ReebQuotient.map_comp
#print axioms TDA.Reeb.ReebQuotient.map_surjective
#print axioms TDA.Reeb.ReebQuotient.componentComparison
#print axioms TDA.Reeb.ReebQuotient.componentComparison_app_mk
#print axioms TDA.Reeb.ReebQuotient.componentComparison_naturality
#print axioms TDA.Reeb.ReebQuotient.componentComparison_natural
#print axioms TDA.Reeb.ReebQuotient.componentComparison_app_surjective
#print axioms TDA.Reeb.ReebQuotient.toOver
#print axioms TDA.Reeb.ReebQuotient.projOver
#print axioms TDA.Reeb.ReebQuotient.quotientFunctor
#print axioms TDA.Reeb.ReebQuotient.projNatTrans
#print axioms TDA.Reeb.ReebQuotient.componentFunctorOver
#print axioms TDA.Reeb.ReebQuotient.componentComparisonOver
#print axioms TDA.Reeb.Examples.fold
#print axioms TDA.Reeb.Examples.fold_comm
#print axioms TDA.Reeb.Examples.fold_surjective
#print axioms TDA.Reeb.Examples.fold_not_injective
#print axioms TDA.Reeb.Examples.fold_mk_ne
#print axioms TDA.Reeb.Examples.map_fold_not_injective
#print axioms TDA.Reeb.Examples.componentNatTrans_fold_not_injective

-- Smoothing coherence and interleaving witness laws (Issue #30).
#print axioms TDA.Reeb.map_eq_map_of_interval
#print axioms TDA.Reeb.map_comp_map_of_interval
#print axioms TDA.Reeb.smoothing
#print axioms TDA.Reeb.smoothing_eq_whiskeringLeft
#print axioms TDA.Reeb.smoothing_obj
#print axioms TDA.Reeb.smoothing_map
#print axioms TDA.Reeb.smoothing_obj_obj
#print axioms TDA.Reeb.smoothing_obj_map
#print axioms TDA.Reeb.smoothing_map_app
#print axioms TDA.Reeb.smoothingUnit
#print axioms TDA.Reeb.smoothingUnit_app_app
#print axioms TDA.Reeb.smoothingMap
#print axioms TDA.Reeb.smoothingMap_app_app
#print axioms TDA.Reeb.smoothingZeroIso
#print axioms TDA.Reeb.smoothingZeroIso_hom_app_app
#print axioms TDA.Reeb.smoothingZeroIso_inv_app_app
#print axioms TDA.Reeb.smoothingCompIso
#print axioms TDA.Reeb.smoothingCompIso_hom_app_app
#print axioms TDA.Reeb.smoothingCompIso_inv_app_app
#print axioms TDA.Reeb.smoothingMap_refl
#print axioms TDA.Reeb.smoothingMap_comp
#print axioms TDA.Reeb.smoothingUnit_comp_smoothingMap
#print axioms TDA.Reeb.smoothingUnit_zero
#print axioms TDA.Reeb.smoothingUnit_comp_smoothingUnit
#print axioms TDA.Reeb.smoothingUnit_comp_map_smoothingUnit
#print axioms TDA.Reeb.smoothingCompIso_assoc
#print axioms TDA.Reeb.smoothingCompIso_zero_left
#print axioms TDA.Reeb.smoothingCompIso_zero_right
#print axioms TDA.Reeb.smoothingCommIso
#print axioms TDA.Reeb.smoothingCommIso_hom_app_app
#print axioms TDA.Reeb.smoothingObjBotIso
#print axioms TDA.Reeb.Interleaving
#print axioms TDA.Reeb.Interleaving.ext
#print axioms TDA.Reeb.Interleaving.ext_iff
#print axioms TDA.Reeb.Interleaving.φ_ψ_app
#print axioms TDA.Reeb.Interleaving.ψ_φ_app
#print axioms TDA.Reeb.Interleaving.φ_ψ_app_assoc
#print axioms TDA.Reeb.Interleaving.ψ_φ_app_assoc
#print axioms TDA.Reeb.Interleaving.ofApp
#print axioms TDA.Reeb.Interleaving.φ_map_ψ
#print axioms TDA.Reeb.Interleaving.φ_map_ψ_assoc
#print axioms TDA.Reeb.Interleaving.ψ_map_φ
#print axioms TDA.Reeb.Interleaving.ψ_map_φ_assoc
#print axioms TDA.Reeb.Interleaving.φ_map_map_ψ
#print axioms TDA.Reeb.Interleaving.φ_map_map_ψ_assoc
#print axioms TDA.Reeb.Interleaving.ψ_map_map_φ
#print axioms TDA.Reeb.Interleaving.ψ_map_map_φ_assoc
#print axioms TDA.Reeb.Interleaving.symm
#print axioms TDA.Reeb.Interleaving.refl
#print axioms TDA.Reeb.Interleaving.mono
#print axioms TDA.Reeb.Interleaving.trans
#print axioms TDA.Reeb.Interleaving.ofIso
#print axioms TDA.Reeb.Interleaving.toIso
#print axioms TDA.Reeb.Interleaving.zeroEquivIso
#print axioms TDA.Reeb.Interleaving.smooth
#print axioms TDA.Reeb.Interleaving.selfSmoothing
#print axioms TDA.Reeb.Examples.pointPrecosheaf
#print axioms TDA.Reeb.Examples.closurePrecosheaf
#print axioms TDA.Reeb.Examples.interleavingOfSubsingleton
#print axioms TDA.Reeb.Examples.pointShift
#print axioms TDA.Reeb.Examples.pointInterleaving
#print axioms TDA.Reeb.Examples.not_pointInterleaving_zero
#print axioms TDA.Reeb.Examples.point_closure_interleaving
#print axioms TDA.Reeb.Examples.instSubsingletonObjOpenIntervalPointPrecosheaf
#print axioms TDA.Reeb.Examples.instSubsingletonObjOpenIntervalClosurePrecosheaf

-- Pairwise-intersection cosheaf condition and component gluing (Issue #26).
#print axioms TDA.Topology.coverCocone
#print axioms TDA.Topology.overlapRel
#print axioms TDA.Topology.eqvGen_overlapRel_apply_eq
#print axioms TDA.Topology.nonempty_isColimit_mapCocone_iff
#print axioms TDA.Topology.existsUnique_glue_of_surjective_of_eqvGen
#print axioms TDA.Topology.IsPairwiseCosheaf
#print axioms TDA.Reeb.overlapRel_mk
#print axioms TDA.Reeb.componentFunctor_exists_map_eq
#print axioms TDA.Reeb.componentFunctor_map_eq_iff_eqvGen
#print axioms TDA.Reeb.componentFunctor_existsUnique_glue
#print axioms TDA.Reeb.componentFunctor_isColimit
#print axioms TDA.Reeb.componentFunctor_isColimit_coverCocone
#print axioms TDA.Reeb.componentFunctor_isPairwiseCosheaf
#print axioms TDA.Reeb.componentFunctor_glue_natTrans
#print axioms TDA.Reeb.Examples.twoOpens_classes_related
#print axioms TDA.Reeb.Examples.twoOpens_isColimit
#print axioms TDA.Reeb.Examples.negPos
#print axioms TDA.Reeb.Examples.negPos_overlapRel_fst
#print axioms TDA.Reeb.Examples.negPos_classes_ne
#print axioms TDA.Reeb.Examples.emptyCover_isEmpty
#print axioms TDA.Reeb.Examples.emptyCover_existsUnique_glue
#print axioms TDA.Reeb.Examples.bot_isColimit
#print axioms TDA.Reeb.Examples.dupCover_related
#print axioms TDA.Reeb.Examples.dupCover_isColimit
#print axioms TDA.Reeb.Examples.existsUnique_glue_sort
#print axioms TDA.Reeb.Examples.unitCover_cover
#print axioms TDA.Reeb.Examples.collapse_glue_identifies

-- Interval restriction of components and uniform perturbation (Issue #32).
#print axioms TDA.Reeb.intervalComponents
#print axioms TDA.Reeb.intervalComponents_obj
#print axioms TDA.Reeb.intervalComponents_map_mk
#print axioms TDA.Reeb.intervalComponents_obj_bot_isEmpty
#print axioms TDA.Reeb.mem_thicken_of_abs_sub_le
#print axioms TDA.Reeb.preimage_subset_preimage_thicken
#print axioms TDA.Reeb.perturbationBound_symm
#print axioms TDA.Reeb.perturbationInclusion
#print axioms TDA.Reeb.perturbationInclusion_eq_inclusion
#print axioms TDA.Reeb.perturbationNatTrans
#print axioms TDA.Reeb.perturbationNatTrans_app_mk
#print axioms TDA.Reeb.perturbationNatTrans_app_apply
#print axioms TDA.Reeb.perturbationInterleaving
#print axioms TDA.Reeb.perturbationInterleaving_φ
#print axioms TDA.Reeb.perturbationInterleaving_ψ
#print axioms TDA.Reeb.nonempty_interleaving_of_abs_sub_le
#print axioms TDA.Reeb.perturbationInterleaving_self
#print axioms TDA.Reeb.perturbationInterleaving_self_toIso
#print axioms TDA.Reeb.perturbationInterleaving_symm
#print axioms TDA.Reeb.perturbationInterleaving_mono
#print axioms TDA.Reeb.perturbationInterleaving_trans
#print axioms TDA.Reeb.Examples.heightShift
#print axioms TDA.Reeb.Examples.abs_sub_heightShift_le
#print axioms TDA.Reeb.Examples.heightShiftInterleaving
#print axioms TDA.Reeb.Examples.isEmpty_interleaving_const
#print axioms TDA.Reeb.Examples.sheetsF
#print axioms TDA.Reeb.Examples.sheetsG
#print axioms TDA.Reeb.Examples.sheets_bound
#print axioms TDA.Reeb.Examples.sheetLift
#print axioms TDA.Reeb.Examples.sheetLift_injective
#print axioms TDA.Reeb.Examples.sheets_φ_injective
#print axioms TDA.Reeb.Examples.sheets_two_components
#print axioms TDA.Reeb.Examples.sheets_not_zero_interleaved

-- Finite interval modules and rank recovery (Issue #14).
#print axioms TDA.Persistence.intervalMap_finrank_range
#print axioms TDA.Persistence.interval_alive_endpoints_iff
#print axioms TDA.Persistence.rank_barcodeMap
#print axioms TDA.Persistence.barcodeRankInteger_nat
#print axioms TDA.Persistence.barcodeRankInteger_neg_one
#print axioms TDA.Persistence.barcodeRankInteger_at_size
#print axioms TDA.Persistence.multiplicity_eq_rank_difference
#print axioms TDA.Persistence.barcodeRankInteger_injective
#print axioms TDA.Persistence.barcodeEnumerationNatIso
#print axioms TDA.Persistence.emptyBarcode_rank_N0
#print axioms TDA.Persistence.rank_single_fullInterval_N1
#print axioms TDA.Persistence.rank_fullObservedInterval
#print axioms TDA.Persistence.rank_duplicate_fullInterval_N1
#print axioms TDA.Persistence.fullInterval_boundary_difference
#print axioms TDA.Persistence.fullInterval_boundary_rank_sum_one
#print axioms TDA.Persistence.equal_dimensions_different_structureMapRanks
#print axioms TDA.Persistence.intervalModule_finiteDimensional
#print axioms TDA.Persistence.barcodeModuleOfList_finiteDimensional
#print axioms TDA.Persistence.barcodeModule_finiteDimensional
#print axioms TDA.Persistence.rank_emptyBarcode

-- Ordered actual-face square-zero and ordinary chain complex (Issue #39).
#print axioms TDA.Simplicial.boundary_comp_boundary
#print axioms TDA.Simplicial.simplicialChainComplex_X
#print axioms TDA.Simplicial.simplicialChainComplex_d
#print axioms TDA.Simplicial.simplicialChainComplex_d_zero
