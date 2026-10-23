-- Live axiom audit pins for Filtration. Append new pins here; do not remove existing pins.
import TDA


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

-- Face-value sublevel filtrations (Issue #71).
#print axioms TDA.Filtration.FilterFunction.mem_sublevel_iff
#print axioms TDA.Filtration.FilterFunction.mem_sublevel_iff_of_mem
#print axioms TDA.Filtration.FilterFunction.sublevel_le
#print axioms TDA.Filtration.FilterFunction.sublevel_mono
#print axioms TDA.Filtration.FilterFunction.sublevelFiltration_apply
#print axioms TDA.Filtration.FilterFunction.mem_support_sublevelFiltration_iff
#print axioms TDA.Filtration.FilterFunction.sublevel_eq_self_of_forall_le
#print axioms TDA.Filtration.FilterFunction.sublevel_eq_bot_of_forall_lt
#print axioms TDA.Filtration.FilterFunction.sublevel_bot

-- Finite critical-value enumeration and exact sublevel recovery (Issue #92).
#print axioms TDA.Filtration.FilterFunction.mem_criticalValues
#print axioms TDA.Filtration.FilterFunction.criticalValues_eq_empty_iff
#print axioms TDA.Filtration.FilterFunction.criticalValue_mem
#print axioms TDA.Filtration.FilterFunction.exists_criticalValue_eq
#print axioms TDA.Filtration.FilterFunction.gradeFiltration_apply
#print axioms TDA.Filtration.FilterFunction.sublevel_eq_bot_of_lt_first
#print axioms TDA.Filtration.FilterFunction.sublevel_eq_grade_of_gap
#print axioms TDA.Filtration.FilterFunction.sublevel_eq_grade_of_adjacent
#print axioms TDA.Filtration.FilterFunction.sublevel_eq_self_of_last_le
#print axioms TDA.Filtration.FilterFunction.sublevel_eq_bot_or_grade

-- Canonical grade-compatible face enumeration (Issue #99).
#print axioms TDA.Filtration.CompatibleOrder.mk
#print axioms TDA.Filtration.CompatibleOrder.enum
#print axioms TDA.Filtration.CompatibleOrder.face_lt
#print axioms TDA.Filtration.CompatibleOrder.monotone
#print axioms TDA.Filtration.CompatibleOrder.lexKey
#print axioms TDA.Filtration.CompatibleOrder.lexKey_injective
#print axioms TDA.Filtration.CompatibleOrder.ofLex
#print axioms TDA.Filtration.CompatibleOrder.ofLex_key_strictMono
#print axioms TDA.Filtration.CompatibleOrder.prefixComplex
#print axioms TDA.Filtration.CompatibleOrder.mem_prefixComplex
#print axioms TDA.Filtration.CompatibleOrder.prefixComplex_zero
#print axioms TDA.Filtration.CompatibleOrder.prefixComplex_eq_self_of_card_le
#print axioms TDA.Filtration.CompatibleOrder.prefixComplex_mono
#print axioms TDA.Filtration.CompatibleOrder.prefixFiltration
#print axioms TDA.Filtration.CompatibleOrder.sublevelCount
#print axioms TDA.Filtration.CompatibleOrder.sublevelCount_le_card
#print axioms TDA.Filtration.CompatibleOrder.sublevelCount_mono
#print axioms TDA.Filtration.CompatibleOrder.value_le_iff_index_lt_sublevelCount
#print axioms TDA.Filtration.CompatibleOrder.sublevel_eq_prefixComplex
#print axioms TDA.Filtration.CompatibleOrder.thresholdMap
#print axioms TDA.Filtration.CompatibleOrder.reindex_prefixFiltration

-- Ordering equivalence on faces and its attained-range characterization (Issue #107).
#print axioms TDA.Filtration.OrderingEquivalent.refl
#print axioms TDA.Filtration.OrderingEquivalent.symm
#print axioms TDA.Filtration.OrderingEquivalent.trans
#print axioms TDA.Filtration.OrderingEquivalent.value_eq_iff
#print axioms TDA.Filtration.OrderingEquivalent.sublevel_eq
#print axioms TDA.Filtration.orderingEquivalent_iff_exists_rangeOrderIso

-- Compatible enumeration transfer across grade functions (Issue #110).
#print axioms TDA.Filtration.CompatibleOrder.transfer
#print axioms TDA.Filtration.CompatibleOrder.transfer_enum
#print axioms TDA.Filtration.OrderingEquivalent.monotone_comp
#print axioms TDA.Filtration.CompatibleOrder.transferOfOrderingEquivalent
#print axioms TDA.Filtration.CompatibleOrder.transferOfOrderingEquivalent_enum

-- Generic finite face compatible-order laws (Issue #112).
#print axioms TDA.Filtration.exists_compatibleOrder
#print axioms TDA.Filtration.CompatibleOrder.monotone_enum_iff_reflects_lt

-- Closed fixed-enumeration compatibility locus (Issue #120).
#print axioms TDA.Filtration.CompatibleOrder.isClosed_compatible_locus
#print axioms TDA.Filtration.FilterFunction.mk.congr_simp

-- Finite continuous coordinate families and compatible-order chambers (Issue #160).
#print axioms TDA.Filtration.isOpen_orderChamber
#print axioms TDA.Filtration.dense_orderChamber
#print axioms TDA.Filtration.exists_open_le_iff_of_mem_orderChamber
#print axioms TDA.Filtration.FilterFunction.exists_open_orderingEquivalent_of_mem_orderChamber
#print axioms TDA.Filtration.CompatibleOrder.exists_open_sameEnum_of_mem_orderChamber

-- Same-label metric diameter filtrations (Issue #243).
#print axioms TDA.Filtration.Rips.mem_fullComplex_iff
#print axioms TDA.Filtration.Rips.diameter_empty
#print axioms TDA.Filtration.Rips.diameter_singleton
#print axioms TDA.Filtration.Rips.diameter_nonneg
#print axioms TDA.Filtration.Rips.diameter_le_iff
#print axioms TDA.Filtration.Rips.dist_le_diameter
#print axioms TDA.Filtration.Rips.diameter_mono
#print axioms TDA.Filtration.Rips.diameter_pair
#print axioms TDA.Filtration.Rips.filter_value
#print axioms TDA.Filtration.Rips.mem_sublevel_iff
#print axioms TDA.Filtration.Rips.sublevel_eq_bot_of_neg
#print axioms TDA.Filtration.Rips.pairwiseDiscrepancy_nonneg
#print axioms TDA.Filtration.Rips.abs_dist_sub_le_pairwiseDiscrepancy
#print axioms TDA.Filtration.Rips.pairwiseDiscrepancy_self
#print axioms TDA.Filtration.Rips.pairwiseDiscrepancy_of_isEmpty
#print axioms TDA.Filtration.Rips.abs_diameter_sub_le_pairwiseDiscrepancy

-- Closed ambient Čech complexes and the Rips/Čech sandwich (Issue #275).
#print axioms TDA.Filtration.Cech.mem_complex_iff
#print axioms TDA.Filtration.Cech.complex_mono
#print axioms TDA.Filtration.Cech.singleton_mem_complex_iff
#print axioms TDA.Filtration.Cech.complex_eq_bot_of_neg
#print axioms TDA.Filtration.Cech.mem_complex_of_pairwise
#print axioms TDA.Filtration.Cech.dist_le_two_mul_of_mem_complex
#print axioms TDA.Filtration.Cech.ripsSublevel_le_complex
#print axioms TDA.Filtration.Cech.complex_le_ripsSublevel_two_mul
#print axioms TDA.Filtration.Cech.radiusAt_nonneg
#print axioms TDA.Filtration.Cech.radiusAt_le_iff
#print axioms TDA.Filtration.Cech.dist_le_radiusAt
#print axioms TDA.Filtration.Cech.radiusAt_mono
#print axioms TDA.Filtration.Cech.radiusAt_le_radiusAt_add_dist
#print axioms TDA.Filtration.Cech.continuous_radiusAt
#print axioms TDA.Filtration.Cech.bddBelow_range_radiusAt
#print axioms TDA.Filtration.Cech.filter_value
#print axioms TDA.Filtration.Cech.filter_value_nonneg
#print axioms TDA.Filtration.Cech.filter_value_le_radiusAt
#print axioms TDA.Filtration.Cech.complex_le_sublevel
#print axioms TDA.Filtration.Cech.exists_radiusAt_eq_value
#print axioms TDA.Filtration.Cech.sublevel_eq_complex
#print axioms TDA.Filtration.Cech.filter_value_le_rips
#print axioms TDA.Filtration.Cech.rips_le_two_mul_filter_value
#print axioms TDA.Filtration.Cech.Examples.TwoPoints.pts_injective
#print axioms TDA.Filtration.Cech.Examples.TwoPoints.metric_dist
#print axioms TDA.Filtration.Cech.Examples.TwoPoints.edge_nonempty
#print axioms TDA.Filtration.Cech.Examples.TwoPoints.dist_pts
#print axioms TDA.Filtration.Cech.Examples.TwoPoints.edge_mem_complex_one
#print axioms TDA.Filtration.Cech.Examples.TwoPoints.edge_not_mem_complex
#print axioms TDA.Filtration.Cech.Examples.TwoPoints.edge_not_mem_rips_one
#print axioms TDA.Filtration.Cech.Examples.TwoPoints.edge_mem_rips_two
#print axioms TDA.Filtration.Cech.Examples.TwoPoints.rips_value
#print axioms TDA.Filtration.Cech.Examples.TwoPoints.cech_value
#print axioms TDA.Filtration.Cech.Examples.TwoPoints.rips_value_eq_two_mul_cech_value
#print axioms TDA.Filtration.Cech.Examples.Triangle.pts_zero
#print axioms TDA.Filtration.Cech.Examples.Triangle.pts_one
#print axioms TDA.Filtration.Cech.Examples.Triangle.pts_two
#print axioms TDA.Filtration.Cech.Examples.Triangle.dist_sq
#print axioms TDA.Filtration.Cech.Examples.Triangle.dist_le_of_sq_le
#print axioms TDA.Filtration.Cech.Examples.Triangle.sq_le_of_dist_le
#print axioms TDA.Filtration.Cech.Examples.Triangle.pts_injective
#print axioms TDA.Filtration.Cech.Examples.Triangle.metric_dist
#print axioms TDA.Filtration.Cech.Examples.Triangle.edge01_mem_complex
#print axioms TDA.Filtration.Cech.Examples.Triangle.edge02_mem_complex
#print axioms TDA.Filtration.Cech.Examples.Triangle.edge12_mem_complex
#print axioms TDA.Filtration.Cech.Examples.Triangle.tri_not_mem_complex
#print axioms TDA.Filtration.Cech.Examples.Triangle.tri_mem_rips
#print axioms TDA.Filtration.Cech.Examples.Triangle.edge01_not_mem_rips
#print axioms TDA.Filtration.Cech.Examples.Triangle.edge02_not_mem_rips
#print axioms TDA.Filtration.Cech.Examples.Triangle.edge12_not_mem_rips
#print axioms TDA.Filtration.Cech.Examples.Triangle.rips_lt_complex
#print axioms TDA.Filtration.Cech.Examples.Triangle.complex_lt_rips
#print axioms TDA.Filtration.Cech.Examples.Punctured.pts_injective
#print axioms TDA.Filtration.Cech.Examples.Punctured.metric_dist
#print axioms TDA.Filtration.Cech.Examples.Punctured.edge_nonempty
#print axioms TDA.Filtration.Cech.Examples.Punctured.edge_not_mem_complex_one
#print axioms TDA.Filtration.Cech.Examples.Punctured.cech_value
#print axioms TDA.Filtration.Cech.Examples.Punctured.edge_mem_sublevel_one
#print axioms TDA.Filtration.Cech.Examples.Punctured.sublevel_ne_complex
#print axioms TDA.Filtration.Cech.Examples.Repeated.edge_card
#print axioms TDA.Filtration.Cech.Examples.Repeated.edge_mem_complex_zero
#print axioms TDA.Filtration.Cech.Examples.Repeated.cech_value
#print axioms TDA.Filtration.Cech.Examples.complex_neg_one_eq_bot
#print axioms TDA.Filtration.Cech.Examples.singleton_not_mem_complex_neg_one

-- Same-label Čech displacement.
#print axioms TDA.Filtration.Cech.radiusAt_le_radiusAt_add_of_dist_le
#print axioms TDA.Filtration.Cech.abs_radiusAt_sub_le_of_dist_le
#print axioms TDA.Filtration.Cech.filter_value_le_add_of_dist_le
#print axioms TDA.Filtration.Cech.abs_filter_value_sub_le_of_dist_le
#print axioms TDA.Filtration.Cech.displacement_nonneg
#print axioms TDA.Filtration.Cech.dist_le_displacement
#print axioms TDA.Filtration.Cech.displacement_le_iff
#print axioms TDA.Filtration.Cech.displacement_comm
#print axioms TDA.Filtration.Cech.displacement_self
#print axioms TDA.Filtration.Cech.displacement_of_isEmpty
#print axioms TDA.Filtration.Cech.abs_filter_value_sub_le_displacement
#print axioms TDA.Filtration.Cech.pairwiseDiscrepancy_le_two_mul_displacement
#print axioms TDA.Filtration.Cech.abs_diameter_sub_le_two_mul_displacement
#print axioms TDA.Filtration.Cech.DisplacementExamples.ThreePoints.p_zero
#print axioms TDA.Filtration.Cech.DisplacementExamples.ThreePoints.p_two
#print axioms TDA.Filtration.Cech.DisplacementExamples.ThreePoints.q_zero
#print axioms TDA.Filtration.Cech.DisplacementExamples.ThreePoints.q_two
#print axioms TDA.Filtration.Cech.DisplacementExamples.ThreePoints.p_injective
#print axioms TDA.Filtration.Cech.DisplacementExamples.ThreePoints.q_injective
#print axioms TDA.Filtration.Cech.DisplacementExamples.ThreePoints.metricP_dist
#print axioms TDA.Filtration.Cech.DisplacementExamples.ThreePoints.metricQ_dist
#print axioms TDA.Filtration.Cech.DisplacementExamples.ThreePoints.displacement_eq
#print axioms TDA.Filtration.Cech.DisplacementExamples.ThreePoints.cech_value_p
#print axioms TDA.Filtration.Cech.DisplacementExamples.ThreePoints.cech_value_q
#print axioms TDA.Filtration.Cech.DisplacementExamples.ThreePoints.abs_cech_value_sub_eq_displacement
#print axioms TDA.Filtration.Cech.DisplacementExamples.ThreePoints.rips_value_p
#print axioms TDA.Filtration.Cech.DisplacementExamples.ThreePoints.rips_value_q
#print axioms TDA.Filtration.Cech.DisplacementExamples.ThreePoints.abs_rips_value_sub_eq_two_mul_displacement
#print axioms TDA.Filtration.Cech.DisplacementExamples.ThreePoints.pairwiseDiscrepancy_eq
#print axioms TDA.Filtration.Cech.DisplacementExamples.ThreePoints.pairwiseDiscrepancy_eq_two_mul_displacement
#print axioms TDA.Filtration.Cech.DisplacementExamples.ThreePoints.cech_change_lt_rips_change
#print axioms TDA.Filtration.Cech.DisplacementExamples.Swap.range_eq
#print axioms TDA.Filtration.Cech.DisplacementExamples.Swap.displacement_eq
#print axioms TDA.Filtration.Cech.DisplacementExamples.radiusAt_empty
#print axioms TDA.Filtration.Cech.DisplacementExamples.radiusAt_estimate_fails_of_neg

-- Čech witness-space change (Issue #292).
#print axioms TDA.Filtration.Cech.radiusAt_comp_of_isometry
#print axioms TDA.Filtration.Cech.complex_le_complex_comp
#print axioms TDA.Filtration.Cech.filter_comp_value_le
#print axioms TDA.Filtration.Cech.complex_comp_le_complex_of_retraction
#print axioms TDA.Filtration.Cech.filter_value_le_filter_comp_value_of_retraction
#print axioms TDA.Filtration.Cech.complex_comp_eq_of_retraction
#print axioms TDA.Filtration.Cech.filter_comp_value_eq_of_retraction
#print axioms TDA.Filtration.Cech.complex_le_complex_val
#print axioms TDA.Filtration.Cech.filter_val_value_le
#print axioms TDA.Filtration.Cech.complex_rangeFactorization_le
#print axioms TDA.Filtration.Cech.filter_value_le_filter_rangeFactorization_value
#print axioms TDA.Filtration.Cech.WitnessExamples.Intrinsic.q_injective
#print axioms TDA.Filtration.Cech.WitnessExamples.Intrinsic.metric_dist
#print axioms TDA.Filtration.Cech.WitnessExamples.Intrinsic.metric_dist_intrinsic
#print axioms TDA.Filtration.Cech.WitnessExamples.Intrinsic.edge_nonempty
#print axioms TDA.Filtration.Cech.WitnessExamples.Intrinsic.rips_value
#print axioms TDA.Filtration.Cech.WitnessExamples.Intrinsic.edge_mem_complex_one
#print axioms TDA.Filtration.Cech.WitnessExamples.Intrinsic.exists_far
#print axioms TDA.Filtration.Cech.WitnessExamples.Intrinsic.edge_not_mem_intrinsic_one
#print axioms TDA.Filtration.Cech.WitnessExamples.Intrinsic.cech_value
#print axioms TDA.Filtration.Cech.WitnessExamples.Intrinsic.intrinsic_value
#print axioms TDA.Filtration.Cech.WitnessExamples.Intrinsic.cech_value_lt_intrinsic
#print axioms TDA.Filtration.Cech.WitnessExamples.Intrinsic.intrinsic_lt_complex
#print axioms TDA.Filtration.Cech.WitnessExamples.Interval.lipschitzWith_g
#print axioms TDA.Filtration.Cech.WitnessExamples.Interval.g_val
#print axioms TDA.Filtration.Cech.WitnessExamples.Interval.complex_val_eq
#print axioms TDA.Filtration.Cech.WitnessExamples.Interval.filter_val_value_eq
#print axioms TDA.Filtration.Cech.WitnessExamples.Interval.val_p_injective
#print axioms TDA.Filtration.Cech.WitnessExamples.Interval.metric_dist
#print axioms TDA.Filtration.Cech.WitnessExamples.Interval.value_eq_one
#print axioms TDA.Filtration.Cech.WitnessExamples.Interval.edge_mem_complex_one
#print axioms TDA.Filtration.Cech.WitnessExamples.complex_id_comp
#print axioms TDA.Filtration.Cech.WitnessExamples.filter_id_comp_value

-- Sup-norm Čech/Rips equality (Issue #292).
#print axioms TDA.Filtration.Cech.dist_supNormWitness_le
#print axioms TDA.Filtration.Cech.mem_complex_iff_pairwise
#print axioms TDA.Filtration.Cech.filter_value_le_of_pairwise
#print axioms TDA.Filtration.Cech.complex_eq_ripsSublevel_two_mul
#print axioms TDA.Filtration.Cech.filter_value_eq_rips_div_two
#print axioms TDA.Filtration.Cech.sublevel_eq_ripsSublevel_two_mul
#print axioms TDA.Filtration.Cech.orderingEquivalent_rips
#print axioms TDA.Filtration.Cech.mem_complex_iff_pairwise_real
#print axioms TDA.Filtration.Cech.complex_eq_ripsSublevel_two_mul_real
#print axioms TDA.Filtration.Cech.filter_value_eq_rips_div_two_real
#print axioms TDA.Filtration.Cech.SupNormExamples.dist_le_of_coord
#print axioms TDA.Filtration.Cech.SupNormExamples.coord_le_dist
#print axioms TDA.Filtration.Cech.SupNormExamples.Triangle.pts_zero
#print axioms TDA.Filtration.Cech.SupNormExamples.Triangle.pts_one
#print axioms TDA.Filtration.Cech.SupNormExamples.Triangle.pts_two
#print axioms TDA.Filtration.Cech.SupNormExamples.Triangle.pts_mk_two
#print axioms TDA.Filtration.Cech.SupNormExamples.Triangle.pts_injective
#print axioms TDA.Filtration.Cech.SupNormExamples.Triangle.metric_dist
#print axioms TDA.Filtration.Cech.SupNormExamples.Triangle.dist_pts_le
#print axioms TDA.Filtration.Cech.SupNormExamples.Triangle.dist_pts_zero_one
#print axioms TDA.Filtration.Cech.SupNormExamples.Triangle.tri_nonempty
#print axioms TDA.Filtration.Cech.SupNormExamples.Triangle.supNormWitness_tri
#print axioms TDA.Filtration.Cech.SupNormExamples.Triangle.tri_mem_complex_one
#print axioms TDA.Filtration.Cech.SupNormExamples.Triangle.tri_not_mem_complex
#print axioms TDA.Filtration.Cech.SupNormExamples.Triangle.rips_value
#print axioms TDA.Filtration.Cech.SupNormExamples.Triangle.cech_value
#print axioms TDA.Filtration.Cech.SupNormExamples.Triangle.complex_one_eq_ripsSublevel_two
#print axioms TDA.Filtration.Cech.SupNormExamples.Triangle.tri_mem_complex_six_fifths
#print axioms TDA.Filtration.Cech.SupNormExamples.Triangle.euclidean_contrast
#print axioms TDA.Filtration.Cech.SupNormExamples.Diagonal.pts_injective
#print axioms TDA.Filtration.Cech.SupNormExamples.Diagonal.metric_dist
#print axioms TDA.Filtration.Cech.SupNormExamples.Diagonal.dist_pts
#print axioms TDA.Filtration.Cech.SupNormExamples.Diagonal.edge_nonempty
#print axioms TDA.Filtration.Cech.SupNormExamples.Diagonal.edge_mem_complex_one
#print axioms TDA.Filtration.Cech.SupNormExamples.Diagonal.rips_value
#print axioms TDA.Filtration.Cech.SupNormExamples.Diagonal.cech_value
#print axioms TDA.Filtration.Cech.SupNormExamples.Line.isometry_embed
#print axioms TDA.Filtration.Cech.SupNormExamples.Line.lipschitzWith_eval_zero
#print axioms TDA.Filtration.Cech.SupNormExamples.Line.q₁_eq
#print axioms TDA.Filtration.Cech.SupNormExamples.Line.value_eq
#print axioms TDA.Filtration.Cech.SupNormExamples.Line.q_eq_twoPoints
#print axioms TDA.Filtration.Cech.SupNormExamples.Line.cech_value
#print axioms TDA.Filtration.Cech.SupNormExamples.Line.cech_value₁
#print axioms TDA.Filtration.Cech.SupNormExamples.Line.cech_value_eq_twoPoints
#print axioms TDA.Filtration.Cech.SupNormExamples.EmptyIndex.mem_complex

-- Filter reparametrization along order embeddings and positive scaling (Issue #307).
#print axioms TDA.Filtration.FilterFunction.ext
#print axioms TDA.Filtration.FilterFunction.ext_iff
#print axioms TDA.Filtration.FilterFunction.map
#print axioms TDA.Filtration.FilterFunction.map_value
#print axioms TDA.Filtration.FilterFunction.map_sublevel_apply
#print axioms TDA.Filtration.FilterFunction.map_sublevel_orderIso
#print axioms TDA.Filtration.FilterFunction.orderingEquivalent_map
#print axioms TDA.Filtration.FilterFunction.map_refl
#print axioms TDA.Filtration.FilterFunction.map_map
#print axioms TDA.Filtration.FilterFunction.scale
#print axioms TDA.Filtration.FilterFunction.scale_value
#print axioms TDA.Filtration.FilterFunction.scale_sublevel
#print axioms TDA.Filtration.FilterFunction.scale_one
#print axioms TDA.Filtration.FilterFunction.scale_scale
#print axioms TDA.Filtration.FilterFunctionMapExamples.scale_sublevel_two
#print axioms TDA.Filtration.FilterFunctionMapExamples.scale_sublevel_four
#print axioms TDA.Filtration.FilterFunctionMapExamples.edge_not_mem_scale_two
#print axioms TDA.Filtration.FilterFunctionMapExamples.edge_mem_scale_four
#print axioms TDA.Filtration.FilterFunctionMapExamples.scale_edge_value
#print axioms TDA.Filtration.FilterFunctionMapExamples.vertexFace
#print axioms TDA.Filtration.FilterFunctionMapExamples.vertex_value
#print axioms TDA.Filtration.FilterFunctionMapExamples.no_negated_filter
#print axioms TDA.Filtration.FilterFunctionMapExamples.scale_round_trip
#print axioms TDA.Filtration.Rips.diameter_pos

-- shifted simplicial homology maps and canonical selectors.
#print axioms TDA.Filtration.IsShiftedSimplicial
#print axioms TDA.Filtration.IsShiftedSimplicialRelation
#print axioms TDA.Filtration.IsShiftedSimplicial.vertexMap
#print axioms TDA.Filtration.IsShiftedSimplicial.vertexMap_apply
#print axioms TDA.Filtration.IsShiftedSimplicialRelation.of_subordinate
#print axioms TDA.Filtration.IsShiftedSimplicialRelation.contiguous
#print axioms TDA.Filtration.isShiftedSimplicialRelation_graph_iff
#print axioms TDA.Filtration.isShiftedSimplicial_id

-- Native relation and shifted homology composition.
#print axioms TDA.Filtration.IsShiftedSimplicial.comp
#print axioms TDA.Filtration.IsShiftedSimplicial.comp_vertexMap
#print axioms TDA.Filtration.IsShiftedSimplicialRelation.comp

-- Subrelations preserve shifted finite-face geometry.
#print axioms TDA.Filtration.IsShiftedSimplicialRelation.of_subset

#print axioms TDA.Filtration.Rips.isShiftedSimplicialRelation_of_distortion

-- Different-label ambient Cech stability.
#print axioms TDA.Filtration.Cech.complexFiltration_apply
#print axioms TDA.Filtration.Cech.sublevelFiltration_eq_complexFiltration
#print axioms TDA.Filtration.Cech.radiusAt_le_add_of_relation
#print axioms TDA.Filtration.Cech.filter_value_le_add_of_relation
#print axioms TDA.Filtration.Cech.isShiftedSimplicialRelation_of_dist_le
#print axioms TDA.Filtration.Cech.isShiftedSimplicialRelation_complex_of_dist_le
