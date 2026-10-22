import TDA.Simplicial.Homology

/-! Face regressions for homology and its inclusion maps. -/

namespace TDA.Simplicial.HomologyExamples

open CategoryTheory TDA.Simplicial

private def onVertices (t : Finset (Fin 4)) : PreAbstractSimplicialComplex (Fin 4) where
  faces := {s | s.Nonempty ∧ s ⊆ t}
  isRelLowerSet_faces := by
    intro s hs
    refine ⟨hs.1, ?_⟩
    intro q hqs hq
    exact ⟨hq, hqs.trans hs.2⟩

private def K : PreAbstractSimplicialComplex (Fin 4) := onVertices {0, 1}
private def L : PreAbstractSimplicialComplex (Fin 4) := onVertices {0, 1, 2}
private def M : PreAbstractSimplicialComplex (Fin 4) := ⊤

private theorem K_le_L : K ≤ L := by
  intro s hs
  change s.Nonempty ∧ s ⊆ ({0, 1} : Finset (Fin 4)) at hs
  change s.Nonempty ∧ s ⊆ ({0, 1, 2} : Finset (Fin 4))
  exact ⟨hs.1, hs.2.trans (by decide)⟩

private theorem L_le_M : L ≤ M := by
  intro s hs
  exact hs.1

private theorem K_lt_L : K < L := by
  apply lt_of_le_of_ne K_le_L
  intro h
  have hmem : ({(2 : Fin 4)} : Finset (Fin 4)) ∈ K := by
    rw [h]
    change ({(2 : Fin 4)} : Finset (Fin 4)).Nonempty ∧
      ({(2 : Fin 4)} : Finset (Fin 4)) ⊆ ({0, 1, 2} : Finset (Fin 4))
    simp
  change ({(2 : Fin 4)} : Finset (Fin 4)).Nonempty ∧
    ({(2 : Fin 4)} : Finset (Fin 4)) ⊆ ({0, 1} : Finset (Fin 4)) at hmem
  exact (by decide : (2 : Fin 4) ∉ ({0, 1} : Finset (Fin 4)))
    (hmem.2 (by simp))

private theorem L_lt_M : L < M := by
  apply lt_of_le_of_ne L_le_M
  intro h
  have hmem : ({(3 : Fin 4)} : Finset (Fin 4)) ∈ L := by
    rw [h]
    change ({(3 : Fin 4)} : Finset (Fin 4)).Nonempty
    simp
  change ({(3 : Fin 4)} : Finset (Fin 4)).Nonempty ∧
    ({(3 : Fin 4)} : Finset (Fin 4)) ⊆ ({0, 1, 2} : Finset (Fin 4)) at hmem
  exact (by decide : (3 : Fin 4) ∉ ({0, 1, 2} : Finset (Fin 4)))
    (hmem.2 (by simp))

private def vertex0 : Face K 0 :=
  ⟨{0}, by change ({0} : Finset (Fin 4)).Nonempty ∧
    ({0} : Finset (Fin 4)) ⊆ {0, 1}; simp, by simp⟩

private def vertex1 : Face K 0 :=
  ⟨{1}, by change ({1} : Finset (Fin 4)).Nonempty ∧
    ({1} : Finset (Fin 4)) ⊆ {0, 1}; simp, by simp⟩

private theorem vertex0_ne_vertex1 : vertex0 ≠ vertex1 := by
  intro h
  have hv := congrArg Subtype.val h
  norm_num [vertex0, vertex1] at hv

private def edge01 : Face K 1 :=
  ⟨{0, 1}, by change ({0, 1} : Finset (Fin 4)).Nonempty ∧
    ({0, 1} : Finset (Fin 4)) ⊆ {0, 1}; simp, by decide⟩

private theorem edge01_orderEmb :
    edge01.1.orderEmbOfFin edge01.2.2 = Fin.castLEOrderEmb (by decide : 2 ≤ 4) := by
  symm
  apply Finset.orderEmbOfFin_unique'
  intro i
  fin_cases i <;> simp [edge01, Fin.castLEOrderEmb]

private theorem deleted_edge01_zero : deletedFace K 0 edge01 0 = vertex1 := by
  apply Subtype.ext
  change edge01.1.erase (edge01.1.orderEmbOfFin edge01.2.2 0) = {1}
  rw [edge01_orderEmb]
  decide

private theorem deleted_edge01_one : deletedFace K 0 edge01 1 = vertex0 := by
  apply Subtype.ext
  change edge01.1.erase (edge01.1.orderEmbOfFin edge01.2.2 1) = {0}
  rw [edge01_orderEmb]
  decide

private theorem edge01_boundary :
    boundary K ℤ 0 (Finsupp.single edge01 1) =
      Finsupp.single vertex1 1 - Finsupp.single vertex0 1 := by
  rw [boundary_single]
  simp only [Fin.sum_univ_succ, deleted_edge01_zero]
  have hdel : deletedFace K 0 edge01 (Fin.succ 0) = vertex0 := by
    simpa using deleted_edge01_one
  rw [hdel]
  norm_num
  rw [sub_eq_add_neg]

private theorem edge01_boundary_ne_zero :
    boundary K ℤ 0 (Finsupp.single edge01 1) ≠ 0 := by
  intro h
  have hc := congrArg (fun c : Chain K ℤ 0 => c vertex1) h
  rw [edge01_boundary] at hc
  simp [vertex0_ne_vertex1] at hc

private noncomputable def edgeCycle : simplicialCycles K ℤ 0 :=
  ⟨boundary K ℤ 0 (Finsupp.single edge01 1), by
    rw [simplicialCycles_zero]
    trivial⟩

private theorem edgeCycle_nonzero : (edgeCycle : Chain K ℤ 0) ≠ 0 :=
  edge01_boundary_ne_zero

private theorem edgeCycle_is_boundary : edgeCycle ∈ simplicialBoundaries K ℤ 0 :=
  (mem_simplicialBoundaries_iff ℤ K 0 edgeCycle).2
    ⟨Finsupp.single edge01 1, rfl⟩

private theorem edgeCycle_class_zero :
    (simplicialBoundaries K ℤ 0).mkQ edgeCycle = 0 := by
  exact (Submodule.Quotient.mk_eq_zero (simplicialBoundaries K ℤ 0)).2
    edgeCycle_is_boundary

private theorem edgeCycle_simplicialH0_zero :
    (homologyKernelQuotient ℤ (simplicialChainComplex K ℤ) 0).inv.hom
      ((simplicialBoundaries K ℤ 0).mkQ edgeCycle) = 0 := by
  rw [edgeCycle_class_zero]
  exact map_zero _

private theorem included_edgeCycle_class_zero :
    simplicialQuotientIncl ℤ K_le_L 0
      ((simplicialBoundaries K ℤ 0).mkQ edgeCycle) = 0 := by
  rw [simplicialQuotientIncl_mkQ]
  exact (Submodule.Quotient.mk_eq_zero (simplicialBoundaries L ℤ 0)).2
    (simplicialBoundaries_le_comap ℤ K_le_L 0 edgeCycle_is_boundary)

private theorem twoStep_cycles :
    simplicialCycleIncl ℤ (K_le_L.trans L_le_M) 0 =
      (simplicialCycleIncl ℤ L_le_M 0).comp (simplicialCycleIncl ℤ K_le_L 0) :=
  simplicialCycleIncl_comp ℤ K_le_L L_le_M 0

private theorem twoStep_quotients :
    simplicialQuotientIncl ℤ (K_le_L.trans L_le_M) 0 =
      (simplicialQuotientIncl ℤ L_le_M 0).comp (simplicialQuotientIncl ℤ K_le_L 0) :=
  simplicialQuotientIncl_comp ℤ K_le_L L_le_M 0

private theorem twoStep_homology :
    simplicialHomologyIncl ℤ (K_le_L.trans L_le_M) 0 =
      simplicialHomologyIncl ℤ K_le_L 0 ≫ simplicialHomologyIncl ℤ L_le_M 0 :=
  simplicialHomologyIncl_comp ℤ K_le_L L_le_M 0

private theorem fin3_bottom (z :
    simplicialHomology (⊥ : PreAbstractSimplicialComplex (Fin 3)) ℤ 0) : z = 0 :=
  simplicialHomology_bot_zero ℤ z

private noncomputable def matrixHomologyMap :
    simplicialHomology K (Matrix (Fin 2) (Fin 2) ℤ) 0 ⟶
      simplicialHomology L (Matrix (Fin 2) (Fin 2) ℤ) 0 :=
  simplicialHomologyIncl (Matrix (Fin 2) (Fin 2) ℤ) K_le_L 0

private noncomputable def charTwoHomology : ModuleCat (ZMod 2) :=
  simplicialHomology K (ZMod 2) 0

private noncomputable def zeroRingHomology : ModuleCat (ZMod 1) :=
  simplicialHomology K (ZMod 1) 0

#print axioms onVertices
#print axioms K
#print axioms L
#print axioms M
#print axioms K_le_L
#print axioms L_le_M
#print axioms K_lt_L
#print axioms L_lt_M
#print axioms vertex0
#print axioms vertex1
#print axioms vertex0_ne_vertex1
#print axioms edge01
#print axioms edge01_orderEmb
#print axioms deleted_edge01_zero
#print axioms deleted_edge01_one
#print axioms edge01_boundary
#print axioms edge01_boundary_ne_zero
#print axioms edgeCycle
#print axioms edgeCycle_nonzero
#print axioms edgeCycle_is_boundary
#print axioms edgeCycle_class_zero
#print axioms edgeCycle_simplicialH0_zero
#print axioms included_edgeCycle_class_zero
#print axioms twoStep_cycles
#print axioms twoStep_quotients
#print axioms twoStep_homology
#print axioms fin3_bottom
#print axioms matrixHomologyMap
#print axioms charTwoHomology
#print axioms zeroRingHomology

end TDA.Simplicial.HomologyExamples
