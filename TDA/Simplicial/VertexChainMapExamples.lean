import TDA.Simplicial.VertexChainMap
import TDA.Simplicial.H0Augmentation
import Mathlib.LinearAlgebra.Matrix.Notation

/-! Concrete orientation, collapse, composition and simplicial-homology fixtures. -/

namespace TDA.Simplicial.VertexChainMapExamples

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open Equiv CategoryTheory
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

private def fullMap {V W : Type} (f : V → W) :
    VertexMap (⊤ : PreAbstractSimplicialComplex V) (⊤ : PreAbstractSimplicialComplex W) where
  toFun := f
  map_face s hs := by
    classical
    exact Finset.image_nonempty.mpr hs

private theorem fullMap_single {V : Type} [LinearOrder V] (R : Type) [Ring R]
    {n : ℕ} (f : Fin (n + 1) → V) (a : R) :
    vertexChainMap R (fullMap f) n (Finsupp.single (fullFace n) a) =
      a • orientedTuple (⊤ : PreAbstractSimplicialComplex V) R f := by
  rw [vertexChainMap_single, fullFace_enumeration]
  rfl

private theorem orientedTuple_id (R : Type) [Ring R] (n : ℕ) :
    orientedTuple (⊤ : PreAbstractSimplicialComplex (Fin (n + 1))) R
      (fun i => i) = Finsupp.single (fullFace n) (1 : R) := by
  have h := orientedTuple_face (⊤ : PreAbstractSimplicialComplex (Fin (n + 1))) R (fullFace n)
  rw [fullFace_enumeration] at h
  exact h

private def edgeVertex (i : Fin 2) : Face (⊤ : PreAbstractSimplicialComplex (Fin 2)) 0 :=
  ⟨{i}, by change ({i} : Finset (Fin 2)).Nonempty; simp, by simp⟩

private theorem edge_delete_zero :
    deletedFace (⊤ : PreAbstractSimplicialComplex (Fin 2)) 0 (fullFace 1) 0 = edgeVertex 1 := by
  apply Subtype.ext
  simp only [deletedFace, fullFace_enumeration]
  decide

private theorem edge_delete_one :
    deletedFace (⊤ : PreAbstractSimplicialComplex (Fin 2)) 0 (fullFace 1) 1 = edgeVertex 0 := by
  apply Subtype.ext
  simp only [deletedFace, fullFace_enumeration]
  decide

/-- The concrete edge boundary is nonzero over the integers. -/
theorem edge_boundary_nonzero :
    boundary (⊤ : PreAbstractSimplicialComplex (Fin 2)) ℤ 0
      (Finsupp.single (fullFace 1) 1) ≠ 0 := by
  intro hz
  have h := congrArg (fun c => c (edgeVertex 1)) hz
  simp [boundary_single, Fin.sum_univ_succ, edge_delete_zero, edge_delete_one,
    edgeVertex] at h

/-- Reversal changes the orientation of a nonzero edge chain. -/
theorem edge_reversal :
    vertexChainMap ℤ (fullMap (Equiv.swap (0 : Fin 2) 1)) 1
      (Finsupp.single (fullFace 1) 1) = -Finsupp.single (fullFace 1) 1 := by
  rw [fullMap_single, one_smul]
  have h := orientedTuple_comp_perm (⊤ : PreAbstractSimplicialComplex (Fin 2)) ℤ
    (fun i => i) (Equiv.swap (0 : Fin 2) 1)
  simpa [Function.comp_def, orientedTuple_id, Equiv.Perm.sign_swap (by decide : (0 : Fin 2) ≠ 1)] using h

/-- Its reversed boundary is nonzero and is the negative of the original boundary. -/
theorem edge_reversal_boundary :
    boundary (⊤ : PreAbstractSimplicialComplex (Fin 2)) ℤ 0
      (vertexChainMap ℤ (fullMap (Equiv.swap (0 : Fin 2) 1)) 1
        (Finsupp.single (fullFace 1) 1)) =
      -boundary (⊤ : PreAbstractSimplicialComplex (Fin 2)) ℤ 0
        (Finsupp.single (fullFace 1) 1) ∧
    boundary (⊤ : PreAbstractSimplicialComplex (Fin 2)) ℤ 0
      (vertexChainMap ℤ (fullMap (Equiv.swap (0 : Fin 2) 1)) 1
        (Finsupp.single (fullFace 1) 1)) ≠ 0 := by
  rw [edge_reversal, map_neg]
  exact ⟨rfl, neg_ne_zero.mpr edge_boundary_nonzero⟩

private def collapseMap : VertexMap (⊤ : PreAbstractSimplicialComplex (Fin 2))
    (Filtration.singletonFace (0 : Fin 1)) where
  toFun _ := 0
  map_face s hs := by
    change @Finset.image (Fin 2) (Fin 1) (Classical.decEq (Fin 1)) (fun _ => 0) s = {0}
    ext v
    simp only [Finset.mem_image, Finset.mem_singleton]
    constructor
    · rintro ⟨i, _, hi⟩
      exact hi.symm
    · intro hv
      obtain ⟨i, hi⟩ := hs
      exact ⟨i, hi, hv.symm⟩

/-- A collapsed edge contributes zero in degree one. -/
theorem edge_collapse :
    vertexChainMap ℤ collapseMap 1 (Finsupp.single (fullFace 1) 1) = 0 := by
  apply vertexChainMap_single_of_not_injective
  rw [fullFace_enumeration]
  intro h
  have he : (0 : Fin 2) = 1 := h (by rfl)
  exact (by decide : (0 : Fin 2) ≠ 1) he

private theorem collapse_vertex (R : Type) [Ring R] (i : Fin 2) :
    vertexChainMap R collapseMap 0 (Finsupp.single (edgeVertex i) 1) =
      Finsupp.single (singletonVertex (0 : Fin 1)) 1 := by
  rw [vertexChainMap_vertex]
  congr 1

/-- Both vertex terms of the nonzero edge boundary have the same image and cancel. -/
theorem edge_collapse_boundary :
    vertexChainMap ℤ collapseMap 0
      (boundary (⊤ : PreAbstractSimplicialComplex (Fin 2)) ℤ 0
        (Finsupp.single (fullFace 1) 1)) = 0 := by
  have h := LinearMap.congr_fun (boundary_vertexChainMap ℤ collapseMap 0)
    (Finsupp.single (fullFace 1) 1)
  simpa [edge_collapse] using h.symm

private def triangleCollapse (i : Fin 3) : Fin 2 := if i = 2 then 1 else 0

/-- A triangle with exactly one repeated image pair has zero degree-two image. -/
theorem triangle_one_pair_collapse :
    vertexChainMap ℤ (fullMap triangleCollapse) 2
      (Finsupp.single (fullFace 2) 1) = 0 := by
  apply vertexChainMap_single_of_not_injective
  rw [fullFace_enumeration]
  intro h
  have he : (0 : Fin 3) = 1 := h (by decide)
  exact (by decide : (0 : Fin 3) ≠ 1) he

/-- The alternating image-edge sum cancels in the one-pair repetition branch. -/
theorem triangle_one_pair_boundary :
    tupleBoundarySum (⊤ : PreAbstractSimplicialComplex (Fin 2)) ℤ triangleCollapse = 0 := by
  rw [← boundary_orientedTuple _ ℤ _ (by
    change (Finset.univ.image triangleCollapse).Nonempty
    exact Finset.image_nonempty.mpr Finset.univ_nonempty)]
  have hx : ¬Function.Injective triangleCollapse := by
    intro h
    exact (by decide : (0 : Fin 3) ≠ 1) (h (by decide))
  rw [orientedTuple_of_not_injective _ ℤ _ hx, map_zero]

/-- The triangle boundary has zero chain image by the general boundary equation. -/
theorem triangle_one_pair_boundary_image :
    vertexChainMap ℤ (fullMap triangleCollapse) 1
      (boundary (⊤ : PreAbstractSimplicialComplex (Fin 3)) ℤ 1
        (Finsupp.single (fullFace 2) 1)) = 0 := by
  have h := LinearMap.congr_fun (boundary_vertexChainMap ℤ (fullMap triangleCollapse) 1)
    (Finsupp.single (fullFace 2) 1)
  simpa [triangle_one_pair_collapse] using h.symm

/-- Two order-changing triangle maps obey the proved strict composition law. -/
theorem triangle_transpositions_compose :
    vertexChainMap ℤ
      (VertexMap.comp (fullMap (Equiv.swap (0 : Fin 3) 1))
        (fullMap (Equiv.swap (1 : Fin 3) 2))) 2 =
      (vertexChainMap ℤ (fullMap (Equiv.swap (1 : Fin 3) 2)) 2).comp
        (vertexChainMap ℤ (fullMap (Equiv.swap (0 : Fin 3) 1)) 2) :=
  vertexChainMap_comp _ _ _ _

/-- A second map can create degeneracy after an order-changing first map. -/
theorem triangle_second_map_collapses :
    vertexChainMap ℤ
      (VertexMap.comp (fullMap (Equiv.swap (0 : Fin 3) 1)) (fullMap triangleCollapse)) 2
      (Finsupp.single (fullFace 2) 1) = 0 := by
  apply vertexChainMap_single_of_not_injective
  rw [fullFace_enumeration]
  intro h
  have he : (0 : Fin 3) = 1 := h (by decide)
  exact (by decide : (0 : Fin 3) ≠ 1) he

/-- Reversal retains a noncentral coefficient over a noncommutative matrix ring. -/
theorem matrix_edge_reversal :
    vertexChainMap (Matrix (Fin 2) (Fin 2) ℤ)
      (fullMap (Equiv.swap (0 : Fin 2) 1)) 1
      (Finsupp.single (fullFace 1) !![0, 1; 0, 0]) =
      Finsupp.single (fullFace 1) (- !![0, 1; 0, 0]) := by
  rw [fullMap_single]
  have h := orientedTuple_comp_perm (⊤ : PreAbstractSimplicialComplex (Fin 2))
    (Matrix (Fin 2) (Fin 2) ℤ) (fun i => i) (Equiv.swap (0 : Fin 2) 1)
  have he : orientedTuple (⊤ : PreAbstractSimplicialComplex (Fin 2))
      (Matrix (Fin 2) (Fin 2) ℤ) (Equiv.swap (0 : Fin 2) 1) =
      -Finsupp.single (fullFace 1) 1 := by
    simpa [Function.comp_def, orientedTuple_id, Equiv.Perm.sign_swap (by decide : (0 : Fin 2) ≠ 1)] using h
  rw [he]
  simp only [smul_neg, Finsupp.smul_single, smul_eq_mul, mul_one, Finsupp.single_neg]

private theorem vertex_class_ne_zero {V : Type} [LinearOrder V]
    (K : PreAbstractSimplicialComplex V) (s : Face K 0) :
    simplicialHomologyClass ℚ K 0 (zeroVertexCycle K ℚ s) ≠ 0 := by
  intro hz
  have hq := congrArg (homologyKernelQuotient ℚ (simplicialChainComplex K ℚ) 0).hom.hom hz
  rw [simplicialHomologyClass_quotient, map_zero] at hq
  exact zeroVertexCycle_not_boundary K ℚ s ((Submodule.Quotient.mk_eq_zero _).mp hq)

/-- Edge collapse sends a nonzero vertex class to the normalized nonzero singleton class. -/
theorem edge_collapse_simplicialH0 :
    (simplicialHomologyMap ℚ collapseMap 0).hom
      (simplicialHomologyClass ℚ (⊤ : PreAbstractSimplicialComplex (Fin 2)) 0
        (zeroVertexCycle _ ℚ (edgeVertex 0))) =
      simplicialHomologyClass ℚ (Filtration.singletonFace (0 : Fin 1)) 0
        (zeroVertexCycle _ ℚ (singletonVertex (0 : Fin 1))) ∧
    simplicialHomologyClass ℚ (⊤ : PreAbstractSimplicialComplex (Fin 2)) 0
      (zeroVertexCycle _ ℚ (edgeVertex 0)) ≠ 0 ∧
    simplicialSingletonH0Equiv ℚ (0 : Fin 1)
      (simplicialHomologyClass ℚ (Filtration.singletonFace (0 : Fin 1)) 0
        (zeroVertexCycle _ ℚ (singletonVertex (0 : Fin 1)))) = 1 := by
  refine ⟨simplicialHomologyMap_class ℚ collapseMap 0 _ _ (collapse_vertex ℚ 0),
    vertex_class_ne_zero _ _, ?_⟩
  exact simplicialSingletonH0Equiv_class ℚ 0 1

private def ghostCollapse : VertexMap (⊤ : PreAbstractSimplicialComplex (Fin 2))
    (Filtration.singletonFace (0 : Fin 2)) where
  toFun _ := 0
  map_face s hs := by
    change @Finset.image (Fin 2) (Fin 2) (Classical.decEq (Fin 2)) (fun _ => 0) s = {0}
    ext v
    simp only [Finset.mem_image, Finset.mem_singleton]
    constructor
    · rintro ⟨i, _, hi⟩
      exact hi.symm
    · intro hv
      obtain ⟨i, hi⟩ := hs
      exact ⟨i, hi, hv.symm⟩

/-- A proper target retains its absent ambient singleton after a genuine edge collapse. -/
theorem ghost_vertex_stays_absent :
    ({1} : Finset (Fin 2)) ∉ Filtration.singletonFace (0 : Fin 2) ∧
    vertexChainMap ℤ ghostCollapse 1 (Finsupp.single (fullFace 1) 1) = 0 := by
  refine ⟨by simp [Filtration.mem_singletonFace_iff], ?_⟩
  apply vertexChainMap_single_of_not_injective
  rw [fullFace_enumeration]
  intro h
  have he : (0 : Fin 2) = 1 := h (by rfl)
  exact (by decide : (0 : Fin 2) ≠ 1) he

private def bottomMap : VertexMap (⊥ : PreAbstractSimplicialComplex (Fin 2))
    (⊥ : PreAbstractSimplicialComplex (Fin 2)) where
  toFun := Equiv.swap 0 1
  map_face _ hs := False.elim hs

/-- Bottom complexes need no nonempty face, even with a nonidentity ambient function. -/
theorem bottom_map_zero (n : ℕ) : vertexChainMap ℤ bottomMap n = 0 := by
  apply LinearMap.ext
  intro c
  rw [emptyChain_eq_zero ℤ n c]
  simp

/-- The identity on a genuinely empty ambient type has its required simplicial-chain behavior. -/
theorem empty_ambient_identity (n : ℕ) :
    vertexChainMap ℤ (VertexMap.id (⊤ : PreAbstractSimplicialComplex (Fin 0))) n =
      LinearMap.id := vertexChainMap_id _ _ _

private def edgeInTriangle : PreAbstractSimplicialComplex (Fin 3) where
  faces := {s | s.Nonempty ∧ s ⊆ {0, 1}}
  isRelLowerSet_faces := by
    intro s hs
    exact ⟨hs.1, fun t hts htn => ⟨htn, hts.trans hs.2⟩⟩

private theorem edgeInTriangle_le : edgeInTriangle ≤ (⊤ : PreAbstractSimplicialComplex (Fin 3)) :=
  fun _ hs => hs.1

private def includedEdge : Face edgeInTriangle 1 :=
  ⟨{0, 1}, by constructor <;> simp, by decide⟩

/-- A proper inclusion keeps the old nonzero degree-one inclusion map. -/
theorem proper_inclusion_agrees :
    vertexChainMap ℤ (inclusionVertexMap edgeInTriangle_le) 1
      (Finsupp.single includedEdge 1) =
      chainIncl ℤ edgeInTriangle_le 1 (Finsupp.single includedEdge 1) ∧
    chainIncl ℤ edgeInTriangle_le 1 (Finsupp.single includedEdge 1) ≠ 0 ∧
    simplicialChainMap ℤ (inclusionVertexMap edgeInTriangle_le) =
      simplicialChainIncl ℤ edgeInTriangle_le ∧
    simplicialHomologyMap ℚ (inclusionVertexMap edgeInTriangle_le) 0 =
      simplicialHomologyIncl ℚ edgeInTriangle_le 0 := by
  refine ⟨by rw [vertexChainMap_inclusion], ?_,
    simplicialChainMap_inclusion _ _, simplicialHomologyMap_inclusion _ _ _⟩
  rw [chainIncl_single]
  exact Finsupp.single_ne_zero.mpr (by decide)

/-- Homology identity and composition specialize to the explicit triangle maps. -/
theorem homology_functor_laws :
    simplicialHomologyMap ℚ (VertexMap.id (⊤ : PreAbstractSimplicialComplex (Fin 3))) 0 =
      𝟙 (simplicialHomology (⊤ : PreAbstractSimplicialComplex (Fin 3)) ℚ 0) ∧
    simplicialHomologyMap ℚ
      (VertexMap.comp (fullMap (Equiv.swap (0 : Fin 3) 1)) (fullMap triangleCollapse)) 0 =
      simplicialHomologyMap ℚ (fullMap (Equiv.swap (0 : Fin 3) 1)) 0 ≫
        simplicialHomologyMap ℚ (fullMap triangleCollapse) 0 := by
  exact ⟨simplicialHomologyMap_id _ _ _, simplicialHomologyMap_comp _ _ _ _⟩

/-- Exactly two nonzero edge brackets survive the repeated-pair triangle image. -/
theorem triangle_one_pair_terms :
    orientedTuple (⊤ : PreAbstractSimplicialComplex (Fin 2)) ℤ
      (triangleCollapse ∘ (0 : Fin 3).succAbove) = Finsupp.single (fullFace 1) 1 ∧
    orientedTuple (⊤ : PreAbstractSimplicialComplex (Fin 2)) ℤ
      (triangleCollapse ∘ (1 : Fin 3).succAbove) = Finsupp.single (fullFace 1) 1 ∧
    orientedTuple (⊤ : PreAbstractSimplicialComplex (Fin 2)) ℤ
      (triangleCollapse ∘ (2 : Fin 3).succAbove) = 0 ∧
    (Finsupp.single (fullFace 1) (1 : ℤ) : Chain (⊤ : PreAbstractSimplicialComplex (Fin 2)) ℤ 1) ≠ 0 := by
  have h0 : triangleCollapse ∘ (0 : Fin 3).succAbove = (fun i : Fin 2 => i) := by
    funext i
    fin_cases i <;> decide
  have h1 : triangleCollapse ∘ (1 : Fin 3).succAbove = (fun i : Fin 2 => i) := by
    funext i
    fin_cases i <;> decide
  refine ⟨by rw [h0, orientedTuple_id], by rw [h1, orientedTuple_id], ?_,
    Finsupp.single_ne_zero.mpr (by decide)⟩
  apply orientedTuple_of_not_injective
  intro h
  have he : (0 : Fin 2) = 1 := h (by decide)
  exact (by decide : (0 : Fin 2) ≠ 1) he

/-- The product of two triangle transpositions has positive orientation and a nonzero image. -/
theorem triangle_transpositions_image :
    vertexChainMap ℤ
      (VertexMap.comp (fullMap (Equiv.swap (0 : Fin 3) 1))
        (fullMap (Equiv.swap (1 : Fin 3) 2))) 2
      (Finsupp.single (fullFace 2) 1) = Finsupp.single (fullFace 2) 1 ∧
    (Finsupp.single (fullFace 2) (1 : ℤ) : Chain (⊤ : PreAbstractSimplicialComplex (Fin 3)) ℤ 2) ≠ 0 := by
  let p := (Equiv.swap (0 : Fin 3) 1).trans (Equiv.swap (1 : Fin 3) 2)
  have hm : VertexMap.comp (fullMap (Equiv.swap (0 : Fin 3) 1))
      (fullMap (Equiv.swap (1 : Fin 3) 2)) = fullMap p := by
    apply VertexMap.ext
    intro i
    rfl
  refine ⟨?_, Finsupp.single_ne_zero.mpr (by decide)⟩
  rw [hm, fullMap_single, one_smul]
  have h := orientedTuple_comp_perm (⊤ : PreAbstractSimplicialComplex (Fin 3)) ℤ
    (fun i => i) p
  have hs : Equiv.Perm.sign p = 1 := by
    simp [p, Equiv.Perm.sign_trans, Equiv.Perm.sign_swap (by decide : (0 : Fin 3) ≠ 1),
      Equiv.Perm.sign_swap (by decide : (1 : Fin 3) ≠ 2)]
  simpa [hs, Function.comp_def, orientedTuple_id] using h

/-- The included edge complex is a proper subcomplex of the triangle. -/
theorem proper_inclusion_missing_vertex :
    ({2} : Finset (Fin 3)) ∉ edgeInTriangle ∧
      ({2} : Finset (Fin 3)) ∈ (⊤ : PreAbstractSimplicialComplex (Fin 3)) := by
  constructor
  · change ¬ (({2} : Finset (Fin 3)).Nonempty ∧ ({2} : Finset (Fin 3)) ⊆ {0, 1})
    decide
  · change ({2} : Finset (Fin 3)).Nonempty
    simp

/-- The matrix coefficient used in the signed fixture is noncentral. -/
theorem matrix_coefficient_noncentral :
    (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℤ) * !![1, 0; 0, 0] ≠
      !![1, 0; 0, 0] * !![0, 1; 0, 0] := by
  intro h
  have he := congrArg (fun m : Matrix (Fin 2) (Fin 2) ℤ => m 0 1) h
  norm_num [Matrix.mul_apply, Fin.sum_univ_succ] at he

/-- The source edge itself is nonzero, independently of its nonzero boundary. -/
theorem edge_chain_nonzero :
    (Finsupp.single (fullFace 1) (1 : ℤ) : Chain (⊤ : PreAbstractSimplicialComplex (Fin 2)) ℤ 1) ≠ 0 :=
  Finsupp.single_ne_zero.mpr (by decide)

/-- Degeneracy introduced by the second map also vanishes in the composed linear map. -/
theorem triangle_composed_collapse :
    ((vertexChainMap ℤ (fullMap triangleCollapse) 2).comp
      (vertexChainMap ℤ (fullMap (Equiv.swap (0 : Fin 3) 1)) 2))
      (Finsupp.single (fullFace 2) 1) = 0 := by
  rw [← vertexChainMap_comp]
  exact triangle_second_map_collapses

/-- The unique map from an empty ambient type into a singleton has zero chains. -/
theorem empty_ambient_to_singleton (n : ℕ) :
    vertexChainMap ℤ (fullMap (Fin.elim0 : Fin 0 → Fin 1)) n = 0 := by
  have : IsEmpty (Face (⊤ : PreAbstractSimplicialComplex (Fin 0)) n) :=
    ⟨fun s => by
      obtain ⟨i, _⟩ := s.2.1
      exact Fin.elim0 i⟩
  apply LinearMap.ext
  intro c
  have hc : c = 0 := Subsingleton.elim _ _
  rw [hc]
  simp

end
end TDA.Simplicial.VertexChainMapExamples
