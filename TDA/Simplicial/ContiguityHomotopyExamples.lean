import TDA.Simplicial.ContiguityHomotopy
import TDA.Simplicial.VertexChainMapExamples
import TDA.Simplicial.H0Augmentation
import Mathlib.LinearAlgebra.Matrix.Notation

/-! Signed prisms, nonzero actual homology, collapse and support controls. -/

namespace TDA.Simplicial.ContiguityHomotopyExamples

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Module
open scoped BigOperators Matrix

noncomputable section

private def fullFace (n : ℕ) : Face (⊤ : PreAbstractSimplicialComplex (Fin (n + 1))) n :=
  ⟨Finset.univ, by change Finset.univ.Nonempty; simp, by simp⟩

private theorem fullFace_enumeration (n : ℕ) :
    (fullFace n).1.orderEmbOfFin (fullFace n).2.2 =
      (OrderIso.refl (Fin (n + 1))).toOrderEmbedding := by
  symm
  apply Finset.orderEmbOfFin_unique'
  intro i
  exact Finset.mem_univ i

private def fullMap {V W : Type} (q : V → W) :
    VertexMap (⊤ : PreAbstractSimplicialComplex V) (⊤ : PreAbstractSimplicialComplex W) where
  toFun := q
  map_face _ hs := by classical exact Finset.image_nonempty.mpr hs

private theorem full_contiguous {V W : Type} (a b : V → W) :
    Contiguous (fullMap a) (fullMap b) := by
  classical
  intro s hs
  exact (Finset.image_nonempty.mpr hs).mono Finset.subset_union_left

private theorem orientedTuple_id (R : Type) [Ring R] (n : ℕ) :
    orientedTuple (⊤ : PreAbstractSimplicialComplex (Fin (n + 1))) R (fun i => i) =
      Finsupp.single (fullFace n) (1 : R) := by
  have h := orientedTuple_face (⊤ : PreAbstractSimplicialComplex (Fin (n + 1))) R (fullFace n)
  rw [fullFace_enumeration] at h
  exact h

private theorem prism_vertex {V W : Type} [LinearOrder V] [LinearOrder W]
    {K : PreAbstractSimplicialComplex V} {L : PreAbstractSimplicialComplex W}
    (R : Type) [Ring R] {f g : VertexMap K L} (h : Contiguous f g) (s : Face K 0) (a : R) :
    Contiguous.prismMap R h 0 (Finsupp.single s a) = a • orientedTuple L R
      (fun k : Fin 2 => if k = 0 then f (s.1.orderEmbOfFin s.2.2 0)
        else g (s.1.orderEmbOfFin s.2.2 0)) := by
  rw [Contiguous.prismMap_single, Fin.sum_univ_one]
  simp only [Fin.val_zero, pow_zero, one_smul]
  congr 1
  congr 1
  funext k
  fin_cases k <;> rfl

private abbrev pointK := (⊤ : PreAbstractSimplicialComplex (Fin 1))
private abbrev edgeK := (⊤ : PreAbstractSimplicialComplex (Fin 2))
private abbrev triangleK := (⊤ : PreAbstractSimplicialComplex (Fin 3))

private def edgeVertex (i : Fin 2) : Face edgeK 0 :=
  ⟨{i}, by change ({i} : Finset (Fin 2)).Nonempty; simp, by simp⟩

private def endpoint (i : Fin 2) : VertexMap pointK edgeK := fullMap (fun _ => i)

private theorem endpoints_contiguous : Contiguous (endpoint 0) (endpoint 1) :=
  full_contiguous _ _

private theorem endpoint_vertex (R : Type) [Ring R] (i : Fin 2) (a : R) :
    vertexChainMap R (endpoint i) 0 (Finsupp.single (fullFace 0) a) =
      Finsupp.single (edgeVertex i) a := by
  rw [vertexChainMap_vertex]
  congr 1

private theorem endpoint_prism (R : Type) [Ring R] (a : R) :
    Contiguous.prismMap R endpoints_contiguous 0 (Finsupp.single (fullFace 0) a) =
      Finsupp.single (fullFace 1) a := by
  rw [prism_vertex]
  have ht : (fun k : Fin 2 => if k = 0 then endpoint 0
      ((fullFace 0).1.orderEmbOfFin (fullFace 0).2.2 0) else
      endpoint 1 ((fullFace 0).1.orderEmbOfFin (fullFace 0).2.2 0)) = (fun i => i) := by
    funext i
    fin_cases i <;> rfl
  rw [ht, orientedTuple_id]
  simp

private theorem edge_boundary (R : Type) [Ring R] (a : R) :
    boundary edgeK R 0 (Finsupp.single (fullFace 1) a) =
      Finsupp.single (edgeVertex 1) a - Finsupp.single (edgeVertex 0) a := by
  have h := LinearMap.congr_fun (Contiguous.boundary_prismMap_zero R endpoints_contiguous)
    (Finsupp.single (fullFace 0) a)
  simpa only [LinearMap.comp_apply, LinearMap.sub_apply, endpoint_prism, endpoint_vertex] using h

private theorem point_endpoint_chains_differ :
    vertexChainMap ℤ (endpoint 0) 0 ≠ vertexChainMap ℤ (endpoint 1) 0 := by
  intro h
  have hc := LinearMap.congr_fun h (Finsupp.single (fullFace 0) 1)
  rw [endpoint_vertex, endpoint_vertex] at hc
  have he := congrArg (fun c : Chain edgeK ℤ 0 => c (edgeVertex 0)) hc
  norm_num [edgeVertex] at he

private theorem endpoint_prism_nonzero_boundary :
    boundary edgeK ℤ 0
      (Contiguous.prismMap ℤ endpoints_contiguous 0 (Finsupp.single (fullFace 0) 1)) =
      Finsupp.single (edgeVertex 1) 1 - Finsupp.single (edgeVertex 0) 1 ∧
    boundary edgeK ℤ 0
      (Contiguous.prismMap ℤ endpoints_contiguous 0 (Finsupp.single (fullFace 0) 1)) ≠ 0 := by
  rw [endpoint_prism, edge_boundary]
  constructor
  · rfl
  · intro hz
    have hc := congrArg (fun c : Chain edgeK ℤ 0 => c (edgeVertex 1)) hz
    norm_num [edgeVertex] at hc

private theorem vertexClass_ne_zero {V : Type} [LinearOrder V]
    (K : PreAbstractSimplicialComplex V) (s : Face K 0) :
    simplicialHomologyClass ℚ K 0 (zeroVertexCycle K ℚ s) ≠ 0 := by
  intro hz
  have hq := congrArg (homologyKernelQuotient ℚ (simplicialChainComplex K ℚ) 0).hom.hom hz
  rw [simplicialHomologyClass_quotient, map_zero] at hq
  exact zeroVertexCycle_not_boundary K ℚ s ((Submodule.Quotient.mk_eq_zero _).mp hq)

private theorem endpoint_actualH0 :
    simplicialHomologyMap ℚ (endpoint 0) 0 = simplicialHomologyMap ℚ (endpoint 1) 0 ∧
    (simplicialHomologyMap ℚ (endpoint 0) 0).hom
      (simplicialHomologyClass ℚ pointK 0 (zeroVertexCycle pointK ℚ (fullFace 0))) ≠ 0 ∧
    simplicialHomologyClass ℚ pointK 0 (zeroVertexCycle pointK ℚ (fullFace 0)) ≠ 0 := by
  refine ⟨Contiguous.simplicialHomologyMap_eq ℚ endpoints_contiguous 0, ?_,
    vertexClass_ne_zero _ _⟩
  have hm := simplicialHomologyMap_class ℚ (endpoint 0) 0
    (zeroVertexCycle pointK ℚ (fullFace 0)) (zeroVertexCycle edgeK ℚ (edgeVertex 0))
    (endpoint_vertex ℚ 0 1)
  rw [hm]
  exact vertexClass_ne_zero _ _

private theorem prism_edge {W : Type} [LinearOrder W] {L : PreAbstractSimplicialComplex W}
    (R : Type) [Ring R] {f g : VertexMap edgeK L} (h : Contiguous f g) :
    Contiguous.prismMap R h 1 (Finsupp.single (fullFace 1) 1) =
      orientedTuple L R ![f 0, g 0, g 1] - orientedTuple L R ![f 0, f 1, g 1] := by
  rw [Contiguous.prismMap_single, fullFace_enumeration, Fin.sum_univ_two]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_smul,
    sub_eq_add_neg]
  apply congrArg₂ (fun x y : Chain L R 2 => x + -y)
  all_goals
    congr 1
    funext k
    fin_cases k <;> rfl

private def edgeId : VertexMap edgeK edgeK := fullMap id
private def edgeRev : VertexMap edgeK edgeK := fullMap (Equiv.swap (0 : Fin 2) 1)
private def edgeCollapse : VertexMap edgeK edgeK := fullMap (fun _ => 0)

private theorem id_chain (R : Type) [Ring R] (n : ℕ) :
    vertexChainMap R edgeId n = LinearMap.id := by
  have h : edgeId = VertexMap.id edgeK := by ext i; rfl
  rw [h, vertexChainMap_id]

private theorem reversal_edge (R : Type) [Ring R] :
    vertexChainMap R edgeRev 1 (Finsupp.single (fullFace 1) 1) =
      -Finsupp.single (fullFace 1) 1 := by
  rw [vertexChainMap_single, fullFace_enumeration, one_smul]
  have h := orientedTuple_comp_perm edgeK R (fun i => i) (Equiv.swap (0 : Fin 2) 1)
  simpa [edgeRev, fullMap, Function.comp_def, orientedTuple_id,
    Equiv.Perm.sign_swap (by decide : (0 : Fin 2) ≠ 1)] using h

private theorem reversal_prism (R : Type) [Ring R] :
    Contiguous.prismMap R (full_contiguous id (Equiv.swap (0 : Fin 2) 1)) 1
      (Finsupp.single (fullFace 1) 1) = 0 := by
  rw [prism_edge]
  have hr : orientedTuple edgeK R ![0, 1, 0] = 0 := by
    apply orientedTuple_of_not_injective
    intro hi
    have h := hi (show (![0, 1, 0] : Fin 3 → Fin 2) 0 = ![0, 1, 0] 2 by rfl)
    exact (by decide : (0 : Fin 3) ≠ 2) h
  change orientedTuple edgeK R ![0, 1, 0] - orientedTuple edgeK R ![0, 1, 0] = 0
  rw [hr]
  simp

private theorem reversal_boundary_prism (R : Type) [Ring R] :
    Contiguous.prismMap R (full_contiguous id (Equiv.swap (0 : Fin 2) 1)) 0
      (boundary edgeK R 0 (Finsupp.single (fullFace 1) 1)) =
      -Finsupp.single (fullFace 1) 1 - Finsupp.single (fullFace 1) 1 := by
  have h := LinearMap.congr_fun
    (Contiguous.boundary_prismMap_succ R (full_contiguous id (Equiv.swap (0 : Fin 2) 1)) 0)
    (Finsupp.single (fullFace 1) 1)
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.sub_apply] at h
  change boundary edgeK R 1 (Contiguous.prismMap R
      (full_contiguous id (Equiv.swap (0 : Fin 2) 1)) 1 (Finsupp.single (fullFace 1) 1)) +
    Contiguous.prismMap R (full_contiguous id (Equiv.swap (0 : Fin 2) 1)) 0
      (boundary edgeK R 0 (Finsupp.single (fullFace 1) 1)) =
    vertexChainMap R edgeRev 1 (Finsupp.single (fullFace 1) 1) -
      vertexChainMap R edgeId 1 (Finsupp.single (fullFace 1) 1) at h
  simpa only [reversal_prism, map_zero, zero_add, reversal_edge, id_chain,
    LinearMap.id_apply] using h

private theorem reversal_integer_nonzero :
    Contiguous.prismMap ℤ (full_contiguous id (Equiv.swap (0 : Fin 2) 1)) 0
      (boundary edgeK ℤ 0 (Finsupp.single (fullFace 1) 1)) =
      Finsupp.single (fullFace 1) (-2) ∧
    Contiguous.prismMap ℤ (full_contiguous id (Equiv.swap (0 : Fin 2) 1)) 0
      (boundary edgeK ℤ 0 (Finsupp.single (fullFace 1) 1)) ≠ 0 := by
  rw [reversal_boundary_prism]
  constructor
  · apply Finsupp.ext
    intro σ
    by_cases hs : fullFace 1 = σ <;> simp [hs]
  · intro hz
    have hc := congrArg (fun c : Chain edgeK ℤ 1 => c (fullFace 1)) hz
    norm_num at hc

private theorem reversal_characteristic_two :
    Contiguous.prismMap (ZMod 2) (full_contiguous id (Equiv.swap (0 : Fin 2) 1)) 0
      (boundary edgeK (ZMod 2) 0 (Finsupp.single (fullFace 1) 1)) = 0 ∧
    simplicialHomologyMap (ZMod 2) edgeId 1 = simplicialHomologyMap (ZMod 2) edgeRev 1 := by
  constructor
  · rw [reversal_boundary_prism]
    apply Finsupp.ext
    intro σ
    by_cases hs : fullFace 1 = σ <;> norm_num [Finsupp.single_apply, hs]
  · exact Contiguous.simplicialHomologyMap_eq (ZMod 2) (full_contiguous _ _) 1

private theorem prism_edge_vertex {W : Type} [LinearOrder W] {L : PreAbstractSimplicialComplex W}
    (R : Type) [Ring R] {f g : VertexMap edgeK L} (h : Contiguous f g) (i : Fin 2) (a : R) :
    Contiguous.prismMap R h 0 (Finsupp.single (edgeVertex i) a) =
      a • orientedTuple L R ![f i, g i] := by
  rw [prism_vertex]
  have hi : (edgeVertex i).1.orderEmbOfFin (edgeVertex i).2.2 0 = i :=
    Finset.mem_singleton.mp (Finset.orderEmbOfFin_mem _ _ 0)
  rw [hi]
  congr 2
  funext k
  fin_cases k <;> rfl

private theorem map_edge_tuple {W : Type} [LinearOrder W] {L : PreAbstractSimplicialComplex W}
    (R : Type) [Ring R] (f : VertexMap edgeK L) :
    vertexChainMap R f 1 (Finsupp.single (fullFace 1) 1) = orientedTuple L R ![f 0, f 1] := by
  rw [vertexChainMap_single, fullFace_enumeration, one_smul]
  congr 1
  funext k
  fin_cases k <;> rfl

private theorem constant_edge_tuple (R : Type) [Ring R] (i : Fin 2) :
    orientedTuple edgeK R ![i, i] = 0 := by
  apply orientedTuple_of_not_injective
  intro hi
  exact (by decide : (0 : Fin 2) ≠ 1) (hi (show (![i, i] : Fin 2 → Fin 2) 0 = ![i, i] 1 by rfl))

private def edgeTo01 : VertexMap edgeK triangleK := fullMap Fin.castSucc
private def edgeTo02 : VertexMap edgeK triangleK := fullMap (1 : Fin 3).succAbove
private theorem triangle_contiguous : Contiguous edgeTo01 edgeTo02 := full_contiguous _ _

private theorem mixed_triangle_prism :
    Contiguous.prismMap ℤ triangle_contiguous 1 (Finsupp.single (fullFace 1) 1) =
      -Finsupp.single (fullFace 2) 1 := by
  rw [prism_edge]
  change orientedTuple triangleK ℤ ![0, 0, 2] - orientedTuple triangleK ℤ ![0, 1, 2] = _
  have hz : orientedTuple triangleK ℤ ![0, 0, 2] = 0 := by
    apply orientedTuple_of_not_injective
    intro hi
    exact (by decide : (0 : Fin 3) ≠ 1)
      (hi (show (![0, 0, 2] : Fin 3 → Fin 3) 0 = ![0, 0, 2] 1 by rfl))
  have ht : (![0, 1, 2] : Fin 3 → Fin 3) = fun i => i := by
    funext i
    fin_cases i <;> rfl
  rw [hz, ht, orientedTuple_id, zero_sub]

private theorem mixed_triangle_prism_nonzero :
    Contiguous.prismMap ℤ triangle_contiguous 1 (Finsupp.single (fullFace 1) 1) ≠ 0 := by
  rw [mixed_triangle_prism]
  intro hz
  have he := congrArg (fun c : Chain triangleK ℤ 2 => c (fullFace 2)) hz
  norm_num at he

private theorem mixed_triangle_boundary_prism :
    Contiguous.prismMap ℤ triangle_contiguous 0
      (boundary edgeK ℤ 0 (Finsupp.single (fullFace 1) 1)) =
      orientedTuple triangleK ℤ ![1, 2] := by
  rw [edge_boundary, map_sub, prism_edge_vertex, prism_edge_vertex]
  simp only [one_smul]
  change orientedTuple triangleK ℤ ![1, 2] - orientedTuple triangleK ℤ ![0, 0] = _
  have hz : orientedTuple triangleK ℤ ![0, 0] = 0 := by
    apply orientedTuple_of_not_injective
    intro hi
    exact (by decide : (0 : Fin 2) ≠ 1)
      (hi (show (![0, 0] : Fin 2 → Fin 3) 0 = ![0, 0] 1 by rfl))
  rw [hz, sub_zero]

private theorem mixed_triangle_identity :
    boundary triangleK ℤ 1 (-Finsupp.single (fullFace 2) 1) +
      orientedTuple triangleK ℤ ![1, 2] =
      orientedTuple triangleK ℤ ![0, 2] - orientedTuple triangleK ℤ ![0, 1] := by
  have h := LinearMap.congr_fun (Contiguous.boundary_prismMap_succ ℤ triangle_contiguous 0)
    (Finsupp.single (fullFace 1) 1)
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.sub_apply] at h
  change boundary triangleK ℤ 1
      (Contiguous.prismMap ℤ triangle_contiguous 1 (Finsupp.single (fullFace 1) 1)) +
    Contiguous.prismMap ℤ triangle_contiguous 0
      (boundary edgeK ℤ 0 (Finsupp.single (fullFace 1) 1)) =
    vertexChainMap ℤ edgeTo02 1 (Finsupp.single (fullFace 1) 1) -
      vertexChainMap ℤ edgeTo01 1 (Finsupp.single (fullFace 1) 1) at h
  rw [mixed_triangle_prism, mixed_triangle_boundary_prism, map_edge_tuple, map_edge_tuple] at h
  exact h

private theorem collapse_prism :
    Contiguous.prismMap ℤ (full_contiguous (fun _ : Fin 2 => (0 : Fin 2)) id) 1
      (Finsupp.single (fullFace 1) 1) = 0 := by
  rw [prism_edge]
  change orientedTuple edgeK ℤ ![0, 0, 1] - orientedTuple edgeK ℤ ![0, 0, 1] = 0
  have hz : orientedTuple edgeK ℤ ![0, 0, 1] = 0 := by
    apply orientedTuple_of_not_injective
    intro hi
    exact (by decide : (0 : Fin 3) ≠ 1)
      (hi (show (![0, 0, 1] : Fin 3 → Fin 2) 0 = ![0, 0, 1] 1 by rfl))
  rw [hz]
  simp

private theorem collapse_edge :
    vertexChainMap ℤ edgeCollapse 1 (Finsupp.single (fullFace 1) 1) = 0 := by
  rw [map_edge_tuple]
  exact constant_edge_tuple ℤ 0

private theorem collapse_boundary_prism :
    Contiguous.prismMap ℤ (full_contiguous (fun _ : Fin 2 => (0 : Fin 2)) id) 0
      (boundary edgeK ℤ 0 (Finsupp.single (fullFace 1) 1)) = Finsupp.single (fullFace 1) 1 := by
  have h := LinearMap.congr_fun
    (Contiguous.boundary_prismMap_succ ℤ (full_contiguous (fun _ : Fin 2 => (0 : Fin 2)) id) 0)
    (Finsupp.single (fullFace 1) 1)
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.sub_apply] at h
  change boundary edgeK ℤ 1 (Contiguous.prismMap ℤ
      (full_contiguous (fun _ : Fin 2 => (0 : Fin 2)) id) 1 (Finsupp.single (fullFace 1) 1)) +
    Contiguous.prismMap ℤ (full_contiguous (fun _ : Fin 2 => (0 : Fin 2)) id) 0
      (boundary edgeK ℤ 0 (Finsupp.single (fullFace 1) 1)) =
    vertexChainMap ℤ edgeId 1 (Finsupp.single (fullFace 1) 1) -
      vertexChainMap ℤ edgeCollapse 1 (Finsupp.single (fullFace 1) 1) at h
  simpa only [collapse_prism, map_zero, zero_add, id_chain, LinearMap.id_apply,
    collapse_edge, sub_zero] using h

private def isolatedK : PreAbstractSimplicialComplex (Fin 2) where
  faces := {s | s.Nonempty ∧ s.card ≤ 1}
  isRelLowerSet_faces := by
    intro s hs
    exact ⟨hs.1, fun t hts htn => ⟨htn, (Finset.card_le_card hts).trans hs.2⟩⟩

private def isolatedVertex (i : Fin 2) : Face isolatedK 0 :=
  ⟨{i}, by constructor <;> simp, by simp⟩

private instance isolated_no_edges : IsEmpty (Face isolatedK 1) := ⟨by
  intro σ
  have hle : σ.1.card ≤ 1 := σ.2.1.2
  have heq := σ.2.2
  omega⟩

private def isolatedEndpoint (i : Fin 2) : VertexMap pointK isolatedK where
  toFun _ := i
  map_face s hs := by
    have he : @Finset.image (Fin 1) (Fin 2) (Classical.decEq _) (fun _ => i) s = {i} := by
      ext w
      simp only [Finset.mem_image, Finset.mem_singleton]
      constructor
      · rintro ⟨_, _, rfl⟩
        rfl
      · rintro rfl
        obtain ⟨v, hv⟩ := hs
        exact ⟨v, hv, rfl⟩
    rw [he]
    exact ⟨by simp, by simp⟩

private theorem isolated_endpoint_vertex (i : Fin 2) :
    vertexChainMap ℚ (isolatedEndpoint i) 0 (Finsupp.single (fullFace 0) 1) =
      Finsupp.single (isolatedVertex i) 1 := by
  rw [vertexChainMap_vertex]
  congr 1

private theorem isolated_endpoints_not_contiguous :
    ¬Contiguous (isolatedEndpoint 0) (isolatedEndpoint 1) := by
  intro h
  have ht := h {(0 : Fin 1)} (by change ({(0 : Fin 1)} : Finset (Fin 1)).Nonempty; simp)
  have hc := ht.2
  norm_num [isolatedEndpoint] at hc

private theorem isolated_actualH0_maps_differ :
    simplicialHomologyMap ℚ (isolatedEndpoint 0) 0 ≠
      simplicialHomologyMap ℚ (isolatedEndpoint 1) 0 := by
  intro he
  let z := zeroVertexCycle pointK ℚ (fullFace 0)
  let z₀ := zeroVertexCycle isolatedK ℚ (isolatedVertex 0)
  let z₁ := zeroVertexCycle isolatedK ℚ (isolatedVertex 1)
  have hm₀ := simplicialHomologyMap_class ℚ (isolatedEndpoint 0) 0 z z₀
    (isolated_endpoint_vertex 0)
  have hm₁ := simplicialHomologyMap_class ℚ (isolatedEndpoint 1) 0 z z₁
    (isolated_endpoint_vertex 1)
  have hc := congrArg (fun m => m.hom (simplicialHomologyClass ℚ pointK 0 z)) he
  rw [hm₀, hm₁] at hc
  have hq := congrArg (homologyKernelQuotient ℚ (simplicialChainComplex isolatedK ℚ) 0).hom.hom hc
  rw [simplicialHomologyClass_quotient, simplicialHomologyClass_quotient] at hq
  have hb : z₀ - z₁ ∈ simplicialBoundaries isolatedK ℚ 0 := (Submodule.Quotient.eq _).mp hq
  obtain ⟨c, hcb⟩ := (mem_simplicialBoundaries_iff ℚ isolatedK 0 (z₀ - z₁)).mp hb
  have hz : c = 0 := by
    apply Finsupp.ext
    intro σ
    exact isEmptyElim σ
  rw [hz, map_zero] at hcb
  have hv := congrArg (fun c : Chain isolatedK ℚ 0 => c (isolatedVertex 0)) hcb
  norm_num [z₀, z₁, zeroVertexCycle, isolatedVertex] at hv

private def ghostEdge : PreAbstractSimplicialComplex (Fin 3) where
  faces := {s | s.Nonempty ∧ s ⊆ {0, 1}}
  isRelLowerSet_faces := by
    intro s hs
    exact ⟨hs.1, fun t hts htn => ⟨htn, hts.trans hs.2⟩⟩

private def ghostEndpoint (i : Fin 2) : VertexMap pointK ghostEdge where
  toFun _ := i.castSucc
  map_face s hs := by
    have he : @Finset.image (Fin 1) (Fin 3) (Classical.decEq _)
        (fun _ => i.castSucc) s = {i.castSucc} := by
      ext w
      simp only [Finset.mem_image, Finset.mem_singleton]
      constructor
      · rintro ⟨_, _, rfl⟩
        rfl
      · rintro rfl
        obtain ⟨v, hv⟩ := hs
        exact ⟨v, hv, rfl⟩
    rw [he]
    constructor
    · simp
    · fin_cases i <;> decide

private theorem ghost_contiguous : Contiguous (ghostEndpoint 0) (ghostEndpoint 1) := by
  let : DecidableEq (Fin 3) := Classical.decEq _
  intro s hs
  have h₀ := (ghostEndpoint 0).map_face s hs
  have h₁ := (ghostEndpoint 1).map_face s hs
  exact ⟨h₀.1.mono Finset.subset_union_left, Finset.union_subset h₀.2 h₁.2⟩

private def ghostEdgeFace : Face ghostEdge 1 :=
  ⟨{0, 1}, by constructor <;> simp, by decide⟩

private theorem ghost_singleton_absent : ¬({(2 : Fin 3)} : Finset (Fin 3)) ∈ ghostEdge := by
  intro h
  have hi := h.2 (by simp : (2 : Fin 3) ∈ ({2} : Finset (Fin 3)))
  exact (by decide : ¬((2 : Fin 3) ∈ ({0, 1} : Finset (Fin 3)))) hi

private theorem ghost_prism :
    Contiguous.prismMap ℤ ghost_contiguous 0 (Finsupp.single (fullFace 0) 1) =
      Finsupp.single ghostEdgeFace 1 := by
  rw [prism_vertex, one_smul]
  have ht : (fun k : Fin 2 => if k = 0 then ghostEndpoint 0
      ((fullFace 0).1.orderEmbOfFin (fullFace 0).2.2 0) else
      ghostEndpoint 1 ((fullFace 0).1.orderEmbOfFin (fullFace 0).2.2 0)) =
      (![0, 1] : Fin 2 → Fin 3) := by
    funext i
    fin_cases i <;> rfl
  rw [ht]
  have hi : Function.Injective (![0, 1] : Fin 2 → Fin 3) := by decide
  have hm : Monotone (![0, 1] : Fin 2 → Fin 3) := by decide
  have hk : Finset.univ.image (![0, 1] : Fin 2 → Fin 3) ∈ ghostEdge := by
    constructor <;> decide
  rw [orientedTuple_of_monotone ghostEdge ℤ _ hi hk hm]
  congr 1

private theorem ghost_homotopy_component :
    (Contiguous.chainHomotopy ℤ ghost_contiguous).hom 0 1 =
      ModuleCat.ofHom (-Contiguous.prismMap ℤ ghost_contiguous 0) :=
  Contiguous.chainHomotopy_hom_succ ℤ ghost_contiguous 0

private def bottomF : VertexMap (⊥ : PreAbstractSimplicialComplex (Fin 2)) edgeK where
  toFun := id
  map_face _ hs := False.elim hs

private def bottomG : VertexMap (⊥ : PreAbstractSimplicialComplex (Fin 2)) edgeK where
  toFun _ := 0
  map_face _ hs := False.elim hs

private theorem bottom_contiguous : Contiguous bottomF bottomG := by
  intro _ hs
  exact False.elim hs

private theorem bottom_prism_zero (n : ℕ) : Contiguous.prismMap ℤ bottom_contiguous n = 0 := by
  apply Finsupp.lhom_ext
  intro s _
  exact False.elim s.2.1

private theorem bottom_homotopy_component_zero (n : ℕ) :
    (Contiguous.chainHomotopy ℤ bottom_contiguous).hom n (n + 1) = 0 := by
  rw [Contiguous.chainHomotopy_hom_succ, bottom_prism_zero, neg_zero]
  rfl

private theorem empty_ambient_prism_zero (n : ℕ) :
    Contiguous.prismMap ℤ
      (full_contiguous (Fin.elim0 : Fin 0 → Fin 1) (Fin.elim0 : Fin 0 → Fin 1)) n = 0 := by
  apply Finsupp.lhom_ext
  intro s _
  obtain ⟨i, _⟩ := s.2.1
  exact isEmptyElim i

private theorem matrix_left_coefficient_prism :
    let A : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; 0, 0]
    Contiguous.prismMap (Matrix (Fin 2) (Fin 2) ℤ) endpoints_contiguous 0
      (Finsupp.single (fullFace 0) A) = Finsupp.single (fullFace 1) A ∧
    boundary edgeK (Matrix (Fin 2) (Fin 2) ℤ) 0
      (Contiguous.prismMap (Matrix (Fin 2) (Fin 2) ℤ) endpoints_contiguous 0
        (Finsupp.single (fullFace 0) A)) =
      Finsupp.single (edgeVertex 1) A - Finsupp.single (edgeVertex 0) A ∧
    A * !![1, 0; 0, 0] ≠ !![1, 0; 0, 0] * A := by
  dsimp only
  refine ⟨endpoint_prism _ _, ?_, VertexChainMapExamples.matrix_coefficient_noncentral⟩
  rw [endpoint_prism, edge_boundary]

private theorem matrix_prism_nonzero :
    Contiguous.prismMap (Matrix (Fin 2) (Fin 2) ℤ) endpoints_contiguous 0
      (Finsupp.single (fullFace 0) !![0, 1; 0, 0]) ≠ 0 := by
  rw [endpoint_prism]
  intro hz
  have he := congrArg
    (fun c : Chain edgeK (Matrix (Fin 2) (Fin 2) ℤ) 1 => c (fullFace 1) 0 1) hz
  norm_num at he

end
end TDA.Simplicial.ContiguityHomotopyExamples
