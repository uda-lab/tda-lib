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

-- Canonical grade-compatible actual-face enumeration (Issue #99).
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

-- Ordering equivalence on actual faces and its attained-range characterization (Issue #107).
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

-- Generic finite actual-face compatible-order laws (Issue #112).
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
