import TDA.Simplicial.Inclusion

/-!
# Finite checks for actual simplicial chain inclusions

These private fixtures exercise the public naturality and chain-map APIs on
proper subcomplexes in one ordered ambient type. Their `#print axioms` records
at the end of this file are intentional: the fixture declarations are not
public API entries, but each is included in the explicit axiom audit.
-/

namespace TDA.Simplicial.InclusionExamples

open CategoryTheory Module

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

private def vertexK0 : Face K 0 :=
  ⟨{0}, by change ({0} : Finset (Fin 4)).Nonempty ∧
    ({0} : Finset (Fin 4)) ⊆ {0, 1}; simp, by simp⟩

private def vertexK1 : Face K 0 :=
  ⟨{1}, by change ({1} : Finset (Fin 4)).Nonempty ∧
    ({1} : Finset (Fin 4)) ⊆ {0, 1}; simp, by simp⟩

private def vertexL0 : Face L 0 :=
  ⟨{0}, by change ({0} : Finset (Fin 4)).Nonempty ∧
    ({0} : Finset (Fin 4)) ⊆ {0, 1, 2}; simp, by simp⟩

private def vertexL1 : Face L 0 :=
  ⟨{1}, by change ({1} : Finset (Fin 4)).Nonempty ∧
    ({1} : Finset (Fin 4)) ⊆ {0, 1, 2}; simp, by simp⟩

private theorem vertexK0_ne_vertexK1 : vertexK0 ≠ vertexK1 := by
  intro h
  have hv := congrArg Subtype.val h
  norm_num [vertexK0, vertexK1] at hv

private theorem vertexL0_ne_vertexL1 : vertexL0 ≠ vertexL1 := by
  intro h
  have hv := congrArg Subtype.val h
  norm_num [vertexL0, vertexL1] at hv

private def edgeK01 : Face K 1 :=
  ⟨{0, 1}, by change ({0, 1} : Finset (Fin 4)).Nonempty ∧
    ({0, 1} : Finset (Fin 4)) ⊆ {0, 1}; simp, by decide⟩

private theorem edgeK01_orderEmb :
    edgeK01.1.orderEmbOfFin edgeK01.2.2 = Fin.castLEOrderEmb (by decide : 2 ≤ 4) := by
  symm
  apply Finset.orderEmbOfFin_unique'
  intro i
  fin_cases i <;> simp [edgeK01, Fin.castLEOrderEmb]

private theorem deleted_edgeK01_zero :
    deletedFace K 0 edgeK01 0 = vertexK1 := by
  apply Subtype.ext
  change edgeK01.1.erase (edgeK01.1.orderEmbOfFin edgeK01.2.2 0) = {1}
  rw [edgeK01_orderEmb]
  decide

private theorem deleted_edgeK01_one :
    deletedFace K 0 edgeK01 1 = vertexK0 := by
  apply Subtype.ext
  change edgeK01.1.erase (edgeK01.1.orderEmbOfFin edgeK01.2.2 1) = {0}
  rw [edgeK01_orderEmb]
  decide

private theorem edgeK01_boundary :
    boundary K ℤ 0 (Finsupp.single edgeK01 1) =
      Finsupp.single vertexK1 1 - Finsupp.single vertexK0 1 := by
  rw [boundary_single]
  simp only [Fin.sum_univ_succ, deleted_edgeK01_zero]
  have hdel : deletedFace K 0 edgeK01 (Fin.succ 0) = vertexK0 := by
    simpa using deleted_edgeK01_one
  rw [hdel]
  norm_num
  rw [sub_eq_add_neg]

private theorem edgeK01_boundary_vertex1 :
    (boundary K ℤ 0 (Finsupp.single edgeK01 1)) vertexK1 = 1 := by
  rw [edgeK01_boundary]
  simp [vertexK0_ne_vertexK1]

private theorem edgeK01_boundary_vertex0 :
    (boundary K ℤ 0 (Finsupp.single edgeK01 1)) vertexK0 = -1 := by
  rw [edgeK01_boundary]
  simp [vertexK0_ne_vertexK1]

private theorem edgeK01_boundary_ne_zero :
    boundary K ℤ 0 (Finsupp.single edgeK01 1) ≠ 0 := by
  intro h
  have hc := congrArg (fun c : Chain K ℤ 0 => c vertexK1) h
  rw [edgeK01_boundary_vertex1] at hc
  norm_num at hc

private theorem included_edgeK01_square :
    boundary L ℤ 0 (chainIncl ℤ K_le_L 1 (Finsupp.single edgeK01 1)) =
      chainIncl ℤ K_le_L 0
        (boundary K ℤ 0 (Finsupp.single edgeK01 1)) := by
  simpa using congrArg
    (fun f => f (Finsupp.single edgeK01 1)) (boundary_chainIncl (R := ℤ) K_le_L 0)

private theorem included_edgeK01_boundary :
    boundary L ℤ 0 (chainIncl ℤ K_le_L 1 (Finsupp.single edgeK01 1)) =
      Finsupp.single vertexL1 1 - Finsupp.single vertexL0 1 := by
  rw [included_edgeK01_square, edgeK01_boundary]
  simp only [map_sub, chainIncl_single]
  have h1 : faceIncl K_le_L 0 vertexK1 = vertexL1 := by
    apply Subtype.ext
    rfl
  have h0 : faceIncl K_le_L 0 vertexK0 = vertexL0 := by
    apply Subtype.ext
    rfl
  rw [h1, h0]

private theorem included_edgeK01_vertex1_coefficient :
    (boundary L ℤ 0 (chainIncl ℤ K_le_L 1 (Finsupp.single edgeK01 1)))
      vertexL1 = 1 := by
  rw [included_edgeK01_boundary]
  simp [vertexL0_ne_vertexL1]

private theorem included_edgeK01_vertex0_coefficient :
    (boundary L ℤ 0 (chainIncl ℤ K_le_L 1 (Finsupp.single edgeK01 1)))
      vertexL0 = -1 := by
  rw [included_edgeK01_boundary]
  simp [vertexL0_ne_vertexL1]

private theorem included_edgeK01_boundary_ne_zero :
    boundary L ℤ 0 (chainIncl ℤ K_le_L 1 (Finsupp.single edgeK01 1)) ≠ 0 := by
  intro h
  have hc := congrArg (fun c : Chain L ℤ 0 => c vertexL1) h
  rw [included_edgeK01_vertex1_coefficient] at hc
  norm_num at hc

private def vertexL2 : Face L 0 :=
  ⟨{2}, by change ({2} : Finset (Fin 4)).Nonempty ∧
    ({2} : Finset (Fin 4)) ⊆ {0, 1, 2}; simp, by simp⟩

private def edgeL01 : Face L 1 :=
  ⟨{0, 1}, by change ({0, 1} : Finset (Fin 4)).Nonempty ∧
    ({0, 1} : Finset (Fin 4)) ⊆ {0, 1, 2}; simp, by decide⟩

private def edgeL02 : Face L 1 :=
  ⟨{0, 2}, by change ({0, 2} : Finset (Fin 4)).Nonempty ∧
    ({0, 2} : Finset (Fin 4)) ⊆ {0, 1, 2}; simp, by decide⟩

private def edgeL12 : Face L 1 :=
  ⟨{1, 2}, by change ({1, 2} : Finset (Fin 4)).Nonempty ∧
    ({1, 2} : Finset (Fin 4)) ⊆ {0, 1, 2}; simp, by decide⟩

private def triangleL012 : Face L 2 :=
  ⟨{0, 1, 2}, by change ({0, 1, 2} : Finset (Fin 4)).Nonempty ∧
    ({0, 1, 2} : Finset (Fin 4)) ⊆ {0, 1, 2}; simp, by decide⟩

private def vertexM0 : Face M 0 :=
  ⟨{0}, by change ({0} : Finset (Fin 4)).Nonempty; simp, by simp⟩

private def vertexM1 : Face M 0 :=
  ⟨{1}, by change ({1} : Finset (Fin 4)).Nonempty; simp, by simp⟩

private def vertexM2 : Face M 0 :=
  ⟨{2}, by change ({2} : Finset (Fin 4)).Nonempty; simp, by simp⟩

private def edgeM01 : Face M 1 :=
  ⟨{0, 1}, by change ({0, 1} : Finset (Fin 4)).Nonempty; simp, by decide⟩

private def edgeM02 : Face M 1 :=
  ⟨{0, 2}, by change ({0, 2} : Finset (Fin 4)).Nonempty; simp, by decide⟩

private def edgeM12 : Face M 1 :=
  ⟨{1, 2}, by change ({1, 2} : Finset (Fin 4)).Nonempty; simp, by decide⟩

private def triangleM012 : Face M 2 :=
  ⟨{0, 1, 2}, by change ({0, 1, 2} : Finset (Fin 4)).Nonempty; simp, by decide⟩

private theorem triangleL012_orderEmb :
    triangleL012.1.orderEmbOfFin triangleL012.2.2 =
      Fin.castLEOrderEmb (by decide : 3 ≤ 4) := by
  symm
  apply Finset.orderEmbOfFin_unique'
  intro i
  fin_cases i <;> simp [triangleL012, Fin.castLEOrderEmb]

private theorem deleted_triangleL012_zero :
    deletedFace L 1 triangleL012 0 = edgeL12 := by
  apply Subtype.ext
  change triangleL012.1.erase
    (triangleL012.1.orderEmbOfFin triangleL012.2.2 0) = {1, 2}
  rw [triangleL012_orderEmb]
  decide

private theorem deleted_triangleL012_one :
    deletedFace L 1 triangleL012 (Fin.succ 0) = edgeL02 := by
  apply Subtype.ext
  change triangleL012.1.erase
    (triangleL012.1.orderEmbOfFin triangleL012.2.2 (Fin.succ 0)) = {0, 2}
  rw [triangleL012_orderEmb]
  decide

private theorem deleted_triangleL012_two :
    deletedFace L 1 triangleL012 (Fin.succ (Fin.succ 0)) = edgeL01 := by
  apply Subtype.ext
  change triangleL012.1.erase
    (triangleL012.1.orderEmbOfFin triangleL012.2.2 (Fin.succ (Fin.succ 0))) = {0, 1}
  rw [triangleL012_orderEmb]
  decide

private theorem triangleL012_boundary :
    boundary L ℤ 1 (Finsupp.single triangleL012 1) =
      Finsupp.single edgeL12 1 - Finsupp.single edgeL02 1 +
        Finsupp.single edgeL01 1 := by
  rw [boundary_single]
  simp only [Fin.sum_univ_succ, deleted_triangleL012_zero]
  have h1 : deletedFace L 1 triangleL012 (Fin.succ 0) = edgeL02 :=
    deleted_triangleL012_one
  have h2 : deletedFace L 1 triangleL012 (Fin.succ (Fin.succ 0)) = edgeL01 :=
    deleted_triangleL012_two
  rw [h1, h2]
  norm_num
  rw [sub_eq_add_neg, add_assoc]

private theorem faceIncl_edgeL01 : faceIncl L_le_M 1 edgeL01 = edgeM01 := by
  apply Subtype.ext
  rfl

private theorem faceIncl_edgeL02 : faceIncl L_le_M 1 edgeL02 = edgeM02 := by
  apply Subtype.ext
  rfl

private theorem faceIncl_edgeL12 : faceIncl L_le_M 1 edgeL12 = edgeM12 := by
  apply Subtype.ext
  rfl

private theorem faceIncl_triangleL012 :
    faceIncl L_le_M 2 triangleL012 = triangleM012 := by
  apply Subtype.ext
  rfl

private theorem triangleM012_orderEmb :
    triangleM012.1.orderEmbOfFin triangleM012.2.2 =
      Fin.castLEOrderEmb (by decide : 3 ≤ 4) := by
  symm
  apply Finset.orderEmbOfFin_unique'
  intro i
  fin_cases i <;> simp [triangleM012, Fin.castLEOrderEmb]

private theorem deleted_triangleM012_zero :
    deletedFace M 1 triangleM012 0 = edgeM12 := by
  apply Subtype.ext
  change triangleM012.1.erase
    (triangleM012.1.orderEmbOfFin triangleM012.2.2 0) = {1, 2}
  rw [triangleM012_orderEmb]
  decide

private theorem deleted_triangleM012_one :
    deletedFace M 1 triangleM012 (Fin.succ 0) = edgeM02 := by
  apply Subtype.ext
  change triangleM012.1.erase
    (triangleM012.1.orderEmbOfFin triangleM012.2.2 (Fin.succ 0)) = {0, 2}
  rw [triangleM012_orderEmb]
  decide

private theorem deleted_triangleM012_two :
    deletedFace M 1 triangleM012 (Fin.succ (Fin.succ 0)) = edgeM01 := by
  apply Subtype.ext
  change triangleM012.1.erase
    (triangleM012.1.orderEmbOfFin triangleM012.2.2 (Fin.succ (Fin.succ 0))) = {0, 1}
  rw [triangleM012_orderEmb]
  decide

private theorem triangle_inclusion_chain_square :
    boundary M ℤ 1 (chainIncl ℤ L_le_M 2 (Finsupp.single triangleL012 1)) =
      chainIncl ℤ L_le_M 1 (boundary L ℤ 1 (Finsupp.single triangleL012 1)) := by
  simpa using congrArg
    (fun f => f (Finsupp.single triangleL012 1)) (boundary_chainIncl (R := ℤ) L_le_M 1)

private theorem included_triangleL012_boundary :
    boundary M ℤ 1 (chainIncl ℤ L_le_M 2 (Finsupp.single triangleL012 1)) =
      Finsupp.single edgeM12 1 - Finsupp.single edgeM02 1 +
        Finsupp.single edgeM01 1 := by
  have h := triangle_inclusion_chain_square
  rw [triangleL012_boundary] at h
  simpa only [map_sub, map_add, chainIncl_single, faceIncl_edgeL12,
    faceIncl_edgeL02, faceIncl_edgeL01] using h

private theorem triangleM012_boundary :
    boundary M ℤ 1 (Finsupp.single triangleM012 1) =
      Finsupp.single edgeM12 1 - Finsupp.single edgeM02 1 +
        Finsupp.single edgeM01 1 := by
  rw [boundary_single]
  simp only [Fin.sum_univ_succ, deleted_triangleM012_zero]
  have h1 : deletedFace M 1 triangleM012 (Fin.succ 0) = edgeM02 :=
    deleted_triangleM012_one
  have h2 : deletedFace M 1 triangleM012 (Fin.succ (Fin.succ 0)) = edgeM01 :=
    deleted_triangleM012_two
  rw [h1, h2]
  norm_num
  rw [sub_eq_add_neg, add_assoc]

private theorem included_triangleL012_agrees_with_target_boundary :
    boundary M ℤ 1 (chainIncl ℤ L_le_M 2 (Finsupp.single triangleL012 1)) =
      boundary M ℤ 1 (Finsupp.single triangleM012 1) := by
  rw [included_triangleL012_boundary, triangleM012_boundary]

private theorem two_step_chainmap_edge :
    ((simplicialChainIncl ℤ (K_le_L.trans L_le_M)).f 1)
        (Finsupp.single edgeK01 1) =
      ((simplicialChainIncl ℤ K_le_L ≫ simplicialChainIncl ℤ L_le_M).f 1)
        (Finsupp.single edgeK01 1) := by
  have h := congrArg (fun f => f.f 1)
    (simplicialChainIncl_comp (R := ℤ) K_le_L L_le_M)
  simpa [HomologicalComplex.comp_f, simplicialChainIncl_f, chainIncl_single] using
    congrArg (fun f => f (Finsupp.single edgeK01 1)) h

private noncomputable def bottomToL : simplicialChainComplex (⊥ : PreAbstractSimplicialComplex (Fin 4)) ℤ ⟶
    simplicialChainComplex L ℤ := simplicialChainIncl ℤ (bot_le)

private theorem bottom_chains_vanish (n : ℕ)
    (c : Chain (⊥ : PreAbstractSimplicialComplex (Fin 4)) ℤ n) : c = 0 :=
  emptyChain_eq_zero ℤ n c

private theorem bottom_map_on_zero (n : ℕ)
    (c : Chain (⊥ : PreAbstractSimplicialComplex (Fin 4)) ℤ n) :
    (bottomToL.f n) c = 0 := by
  rw [bottom_chains_vanish n c]
  change (chainIncl ℤ (bot_le) n) 0 = 0
  exact map_zero _

private theorem singleton_le_K :
    Filtration.singletonFace (0 : Fin 4) ≤ K := by
  intro s hs
  change s = ({0} : Finset (Fin 4)) at hs
  subst s
  change ({0} : Finset (Fin 4)).Nonempty ∧
    ({0} : Finset (Fin 4)) ⊆ ({0, 1} : Finset (Fin 4))
  simp

private theorem singleton_vertex_inclusion :
    chainIncl ℤ singleton_le_K 0
      (Finsupp.single (singletonVertex (0 : Fin 4)) 1) =
        Finsupp.single vertexK0 1 := by
  rw [chainIncl_single]
  congr 1

private theorem singleton_positive_chains_vanish (n : ℕ)
    (c : Chain (Filtration.singletonFace (0 : Fin 4)) ℤ (n + 1)) : c = 0 :=
  singletonHigherChain_eq_zero (0 : Fin 4) ℤ n c

private theorem singleton_inclusion_component_zero :
    (simplicialChainIncl ℤ singleton_le_K).f 0 =
      ModuleCat.ofHom (chainIncl ℤ singleton_le_K 0) :=
  simplicialChainIncl_f ℤ singleton_le_K 0

private theorem singleton_inclusion_outgoing_zero :
    (simplicialChainIncl ℤ singleton_le_K).f 0 ≫
      (simplicialChainComplex K ℤ).d 0 0 = 0 := by
  rw [simplicialChainComplex_d_zero]
  rw [CategoryTheory.Limits.comp_zero]

private theorem matrix_boundary_naturality :
    (boundary L (Matrix (Fin 2) (Fin 2) ℤ) 0).comp
        (chainIncl (Matrix (Fin 2) (Fin 2) ℤ) K_le_L 1) =
      (chainIncl (Matrix (Fin 2) (Fin 2) ℤ) K_le_L 0).comp
        (boundary K (Matrix (Fin 2) (Fin 2) ℤ) 0) :=
  boundary_chainIncl (R := Matrix (Fin 2) (Fin 2) ℤ) K_le_L 0

private noncomputable def matrixInclusion :
    simplicialChainComplex K (Matrix (Fin 2) (Fin 2) ℤ) ⟶
      simplicialChainComplex L (Matrix (Fin 2) (Fin 2) ℤ) :=
  simplicialChainIncl (Matrix (Fin 2) (Fin 2) ℤ) K_le_L

private theorem matrix_chainIncl_single (a : Matrix (Fin 2) (Fin 2) ℤ) :
    chainIncl (Matrix (Fin 2) (Fin 2) ℤ) K_le_L 1 (Finsupp.single edgeK01 a) =
      Finsupp.single (faceIncl K_le_L 1 edgeK01) a :=
  chainIncl_single (R := Matrix (Fin 2) (Fin 2) ℤ) K_le_L 1 edgeK01 a

/-! ### Private fixture axiom audit -/

#print axioms onVertices
#print axioms K
#print axioms L
#print axioms M
#print axioms K_le_L
#print axioms L_le_M
#print axioms K_lt_L
#print axioms L_lt_M
#print axioms vertexK0
#print axioms vertexK1
#print axioms vertexL0
#print axioms vertexL1
#print axioms vertexK0_ne_vertexK1
#print axioms vertexL0_ne_vertexL1
#print axioms edgeK01
#print axioms edgeK01_orderEmb
#print axioms deleted_edgeK01_zero
#print axioms deleted_edgeK01_one
#print axioms edgeK01_boundary
#print axioms edgeK01_boundary_vertex1
#print axioms edgeK01_boundary_vertex0
#print axioms edgeK01_boundary_ne_zero
#print axioms included_edgeK01_square
#print axioms included_edgeK01_boundary
#print axioms included_edgeK01_vertex1_coefficient
#print axioms included_edgeK01_vertex0_coefficient
#print axioms included_edgeK01_boundary_ne_zero
#print axioms vertexL2
#print axioms edgeL01
#print axioms edgeL02
#print axioms edgeL12
#print axioms triangleL012
#print axioms vertexM0
#print axioms vertexM1
#print axioms vertexM2
#print axioms edgeM01
#print axioms edgeM02
#print axioms edgeM12
#print axioms triangleM012
#print axioms triangleL012_orderEmb
#print axioms deleted_triangleL012_zero
#print axioms deleted_triangleL012_one
#print axioms deleted_triangleL012_two
#print axioms triangleL012_boundary
#print axioms faceIncl_edgeL01
#print axioms faceIncl_edgeL02
#print axioms faceIncl_edgeL12
#print axioms faceIncl_triangleL012
#print axioms triangleM012_orderEmb
#print axioms deleted_triangleM012_zero
#print axioms deleted_triangleM012_one
#print axioms deleted_triangleM012_two
#print axioms triangle_inclusion_chain_square
#print axioms included_triangleL012_boundary
#print axioms triangleM012_boundary
#print axioms included_triangleL012_agrees_with_target_boundary
#print axioms two_step_chainmap_edge
#print axioms bottomToL
#print axioms bottom_chains_vanish
#print axioms bottom_map_on_zero
#print axioms singleton_le_K
#print axioms singleton_vertex_inclusion
#print axioms singleton_positive_chains_vanish
#print axioms singleton_inclusion_component_zero
#print axioms singleton_inclusion_outgoing_zero
#print axioms matrix_boundary_naturality
#print axioms matrixInclusion
#print axioms matrix_chainIncl_single

end TDA.Simplicial.InclusionExamples
