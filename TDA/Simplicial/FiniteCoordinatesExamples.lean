import TDA.Simplicial.FiniteCoordinates
import TDA.Simplicial.FiniteComplex
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Reindex

/-! # Face coordinate fixtures

The complete displayed arrays are reindexed through proved face bijections.
They use the boundary and inclusion matrices over integers and `ZMod 1`.
-/

universe u v

open scoped BigOperators Matrix
open Module

namespace TDA.Simplicial

variable {V : Type u} [LinearOrder V]

section TheoryFixtures

noncomputable local instance faceFintypeLocal
    (K : PreAbstractSimplicialComplex V) [Finite (TotalFace K)]
    (n : ℕ) : Fintype (Face K n) := faceFintypeOfTotalFinite K n

private theorem totalFinite_square (K : PreAbstractSimplicialComplex V)
    [Finite (TotalFace K)] (R : Type v) [CommRing R] (n : ℕ) :
    boundaryMatrix K R n * boundaryMatrix K R (n + 1) = 0 := by
  exact boundaryMatrix_mul_boundaryMatrix K R n

private theorem totalFinite_inclusion {K L : PreAbstractSimplicialComplex V}
    [Finite (TotalFace K)] [Finite (TotalFace L)]
    (R : Type v) [CommRing R] (h : K ≤ L) (n : ℕ) :
    boundaryMatrix L R n * chainInclusionMatrix R h (n + 1) =
      chainInclusionMatrix R h n * boundaryMatrix K R n := by
  exact boundaryMatrix_chainInclusionMatrix R h n

private theorem finiteTotal_bound (K : PreAbstractSimplicialComplex (Fin 3)) :
    Finite (TotalFace K) := inferInstance

private theorem bottom_matrix_zero (n : ℕ) :
    boundaryMatrix (⊥ : PreAbstractSimplicialComplex (Fin 3)) ℤ n = 0 := by
  ext τ σ
  exact isEmptyElim σ

private theorem bottom_outgoing_zero (j : ℕ) :
    LinearMap.toMatrix
      (faceBasis (⊥ : PreAbstractSimplicialComplex (Fin 3)) ℤ 0)
      (faceBasis (⊥ : PreAbstractSimplicialComplex (Fin 3)) ℤ j)
      ((simplicialChainComplex (⊥ : PreAbstractSimplicialComplex (Fin 3)) ℤ).d 0 j).hom =
      0 := by
  exact simplicialChainComplex_d_zero_toMatrix _ ℤ j

private theorem singleton_coordinate (a : ℤ) :
    chainCoordinates (Filtration.singletonFace (0 : Fin 3)) ℤ 0
      (Finsupp.single (singletonVertex 0) a)
      (singletonVertex 0) = a := by
  rw [chainCoordinates_apply]
  simp

private theorem singleton_matrix_zero :
    boundaryMatrix (Filtration.singletonFace (0 : Fin 3)) ℤ 0 = 0 := by
  ext τ σ
  exact isEmptyElim σ

private theorem singleton_outgoing_zero (j : ℕ) :
    LinearMap.toMatrix
      (faceBasis (Filtration.singletonFace (0 : Fin 3)) ℤ 0)
      (faceBasis (Filtration.singletonFace (0 : Fin 3)) ℤ j)
      ((simplicialChainComplex (Filtration.singletonFace (0 : Fin 3)) ℤ).d 0 j).hom =
        0 := by
  exact simplicialChainComplex_d_zero_toMatrix _ ℤ j

private def edgeK : PreAbstractSimplicialComplex (Fin 3) where
  faces := {s | s.Nonempty ∧ s ⊆ ({0, 1} : Finset (Fin 3))}
  isRelLowerSet_faces := by
    intro s hs
    exact ⟨hs.1, fun t hts ht => ⟨ht, hts.trans hs.2⟩⟩

private def triangleK : PreAbstractSimplicialComplex (Fin 3) := ⊤

private theorem singleton_le_edge :
    Filtration.singletonFace (0 : Fin 3) ≤ edgeK := by
  intro s hs
  have hs' := (Filtration.mem_singletonFace_iff (0 : Fin 3) s).mp hs
  change s.Nonempty ∧ s ⊆ ({0, 1} : Finset (Fin 3))
  subst s
  decide

private theorem edge_le_triangle : edgeK ≤ triangleK := by
  intro s hs
  exact hs.1

private def edgeVertex (i : Fin 2) : Face edgeK 0 :=
  ⟨{Fin.castLE (by decide : 2 ≤ 3) i}, by
    change ({Fin.castLE (by decide : 2 ≤ 3) i} : Finset (Fin 3)).Nonempty ∧
      ({Fin.castLE (by decide : 2 ≤ 3) i} : Finset (Fin 3)) ⊆
        ({0, 1} : Finset (Fin 3))
    fin_cases i <;> decide,
    by simp⟩

private def edge01 : Face edgeK 1 :=
  ⟨{0, 1}, by change ({0, 1} : Finset (Fin 3)).Nonempty ∧
    ({0, 1} : Finset (Fin 3)) ⊆ {0, 1}; decide, by decide⟩

private def triangleVertex (i : Fin 3) : Face triangleK 0 :=
  ⟨{i}, by change ({i} : Finset (Fin 3)).Nonempty; simp, by simp⟩

private def triangleEdge01 : Face triangleK 1 :=
  ⟨{0, 1}, by change ({0, 1} : Finset (Fin 3)).Nonempty; decide, by decide⟩

private def triangleEdge02 : Face triangleK 1 :=
  ⟨{0, 2}, by change ({0, 2} : Finset (Fin 3)).Nonempty; decide, by decide⟩

private def triangleEdge12 : Face triangleK 1 :=
  ⟨{1, 2}, by change ({1, 2} : Finset (Fin 3)).Nonempty; decide, by decide⟩

private def triangleEdge (i : Fin 3) : Face triangleK 1 :=
  if i = 0 then triangleEdge01 else if i = 1 then triangleEdge02 else triangleEdge12

private def triangleFace : Face triangleK 2 :=
  ⟨{0, 1, 2}, by change ({0, 1, 2} : Finset (Fin 3)).Nonempty; decide,
    by decide⟩

private def edgeColumn (_ : Fin 1) : Face edgeK 1 := edge01
private def triangleColumn (_ : Fin 1) : Face triangleK 2 := triangleFace

private theorem edgeVertex_bijective : Function.Bijective edgeVertex := by
  constructor
  · intro i j h
    have hv := congrArg Subtype.val h
    fin_cases i <;> fin_cases j <;>
      first | rfl |
        simp [edgeVertex] at hv
  · intro s
    have hc : s.1 = {(0 : Fin 3)} ∨ s.1 = {(1 : Fin 3)} := by
      have h : ∀ t : Finset (Fin 3), t.card = 1 →
          t ⊆ ({0, 1} : Finset (Fin 3)) →
          t = {0} ∨ t = {1} := by decide
      exact h s.1 s.2.2 s.2.1.2
    rcases hc with hc | hc
    · exact ⟨0, Subtype.ext (by simpa [edgeVertex] using hc.symm)⟩
    · exact ⟨1, Subtype.ext (by simpa [edgeVertex] using hc.symm)⟩

private theorem edgeColumn_bijective : Function.Bijective edgeColumn := by
  constructor
  · intro i j h
    exact Subsingleton.elim i j
  · intro s
    have h : ∀ t : Finset (Fin 3), t.card = 2 →
        t ⊆ ({0, 1} : Finset (Fin 3)) → t = {0, 1} := by decide
    exact ⟨0, Subtype.ext (by simpa [edgeColumn, edge01] using
      (h s.1 s.2.2 s.2.1.2).symm)⟩

private theorem triangleVertex_bijective : Function.Bijective triangleVertex := by
  constructor
  · intro i j h
    fin_cases i <;> fin_cases j <;> simp [triangleVertex] at h ⊢
  · intro s
    have h : ∀ t : Finset (Fin 3), t.card = 1 →
        t = {0} ∨ t = {1} ∨ t = {2} := by decide
    rcases h s.1 s.2.2 with hs | hs | hs
    · exact ⟨0, Subtype.ext (by simpa [triangleVertex] using hs.symm)⟩
    · exact ⟨1, Subtype.ext (by simpa [triangleVertex] using hs.symm)⟩
    · exact ⟨2, Subtype.ext (by simpa [triangleVertex] using hs.symm)⟩

private theorem triangleEdge_bijective : Function.Bijective triangleEdge := by
  constructor
  · intro i j h
    have hv := congrArg Subtype.val h
    fin_cases i <;> fin_cases j <;>
      first | rfl |
        (simp [triangleEdge, triangleEdge01, triangleEdge02, triangleEdge12] at hv
         exact False.elim (absurd hv (by decide)))
  · intro s
    have h : ∀ t : Finset (Fin 3), t.card = 2 →
        t = {0, 1} ∨ t = {0, 2} ∨ t = {1, 2} := by decide
    rcases h s.1 s.2.2 with hs | hs | hs
    · exact ⟨0, Subtype.ext (by simpa [triangleEdge, triangleEdge01] using hs.symm)⟩
    · exact ⟨1, Subtype.ext (by simpa [triangleEdge, triangleEdge02] using hs.symm)⟩
    · exact ⟨2, Subtype.ext (by simpa [triangleEdge, triangleEdge12] using hs.symm)⟩

private theorem triangleColumn_bijective : Function.Bijective triangleColumn := by
  constructor
  · intro i j h
    exact Subsingleton.elim i j
  · intro s
    have h : ∀ t : Finset (Fin 3), t.card = 3 → t = {0, 1, 2} := by decide
    exact ⟨0, Subtype.ext (by simpa [triangleColumn, triangleFace] using
      (h s.1 s.2.2).symm)⟩

private theorem edge01_orderEmb :
    edge01.1.orderEmbOfFin edge01.2.2 =
      Fin.castLEOrderEmb (by decide : 2 ≤ 3) := by
  symm
  apply Finset.orderEmbOfFin_unique'
  intro i
  fin_cases i <;> simp [edge01, Fin.castLEOrderEmb]

private theorem triangleEdge01_orderEmb :
    triangleEdge01.1.orderEmbOfFin triangleEdge01.2.2 =
      Fin.castLEOrderEmb (by decide : 2 ≤ 3) := by
  symm
  apply Finset.orderEmbOfFin_unique'
  intro i
  fin_cases i <;> simp [triangleEdge01, Fin.castLEOrderEmb]

private theorem triangleEdge02_orderEmb :
    triangleEdge02.1.orderEmbOfFin triangleEdge02.2.2 =
      Fin.succAboveOrderEmb (1 : Fin 3) := by
  symm
  apply Finset.orderEmbOfFin_unique'
  intro i
  fin_cases i <;> simp [triangleEdge02, Fin.succAboveOrderEmb, Fin.succAbove]

private theorem triangleEdge12_orderEmb :
    triangleEdge12.1.orderEmbOfFin triangleEdge12.2.2 =
      Fin.succAboveOrderEmb (0 : Fin 3) := by
  symm
  apply Finset.orderEmbOfFin_unique'
  intro i
  fin_cases i <;> simp [triangleEdge12, Fin.succAboveOrderEmb, Fin.succAbove]

private theorem triangleFace_orderEmb :
    triangleFace.1.orderEmbOfFin triangleFace.2.2 =
      (OrderIso.refl (Fin 3)).toOrderEmbedding := by
  symm
  apply Finset.orderEmbOfFin_unique'
  intro i
  fin_cases i <;> simp [triangleFace]

private theorem edge_del0 : deletedFace edgeK 0 edge01 0 = edgeVertex 1 := by
  apply Subtype.ext
  change edge01.1.erase (edge01.1.orderEmbOfFin edge01.2.2 0) =
    (edgeVertex 1).1
  rw [edge01_orderEmb]
  decide

private theorem edge_del1 : deletedFace edgeK 0 edge01 1 = edgeVertex 0 := by
  apply Subtype.ext
  change edge01.1.erase (edge01.1.orderEmbOfFin edge01.2.2 1) =
    (edgeVertex 0).1
  rw [edge01_orderEmb]
  decide

private theorem triangleEdge01_del0 : deletedFace triangleK 0 triangleEdge01 0 = triangleVertex 1 := by
  apply Subtype.ext
  change triangleEdge01.1.erase (triangleEdge01.1.orderEmbOfFin triangleEdge01.2.2 0) =
    (triangleVertex 1).1
  rw [triangleEdge01_orderEmb]
  decide

private theorem triangleEdge01_del1 : deletedFace triangleK 0 triangleEdge01 1 = triangleVertex 0 := by
  apply Subtype.ext
  change triangleEdge01.1.erase (triangleEdge01.1.orderEmbOfFin triangleEdge01.2.2 1) =
    (triangleVertex 0).1
  rw [triangleEdge01_orderEmb]
  decide

private theorem triangleEdge02_del0 : deletedFace triangleK 0 triangleEdge02 0 = triangleVertex 2 := by
  apply Subtype.ext
  change triangleEdge02.1.erase (triangleEdge02.1.orderEmbOfFin triangleEdge02.2.2 0) =
    (triangleVertex 2).1
  rw [triangleEdge02_orderEmb]
  decide

private theorem triangleEdge02_del1 : deletedFace triangleK 0 triangleEdge02 1 = triangleVertex 0 := by
  apply Subtype.ext
  change triangleEdge02.1.erase (triangleEdge02.1.orderEmbOfFin triangleEdge02.2.2 1) =
    (triangleVertex 0).1
  rw [triangleEdge02_orderEmb]
  decide

private theorem triangleEdge12_del0 : deletedFace triangleK 0 triangleEdge12 0 = triangleVertex 2 := by
  apply Subtype.ext
  change triangleEdge12.1.erase (triangleEdge12.1.orderEmbOfFin triangleEdge12.2.2 0) =
    (triangleVertex 2).1
  rw [triangleEdge12_orderEmb]
  decide

private theorem triangleEdge12_del1 : deletedFace triangleK 0 triangleEdge12 1 = triangleVertex 1 := by
  apply Subtype.ext
  change triangleEdge12.1.erase (triangleEdge12.1.orderEmbOfFin triangleEdge12.2.2 1) =
    (triangleVertex 1).1
  rw [triangleEdge12_orderEmb]
  decide

private theorem triangleFace_del0 : deletedFace triangleK 1 triangleFace 0 = triangleEdge12 := by
  apply Subtype.ext
  change triangleFace.1.erase (triangleFace.1.orderEmbOfFin triangleFace.2.2 0) =
    triangleEdge12.1
  rw [triangleFace_orderEmb]
  decide

private theorem triangleFace_del1 : deletedFace triangleK 1 triangleFace 1 = triangleEdge02 := by
  apply Subtype.ext
  change triangleFace.1.erase (triangleFace.1.orderEmbOfFin triangleFace.2.2 1) =
    triangleEdge02.1
  rw [triangleFace_orderEmb]
  decide

private theorem triangleFace_del2 : deletedFace triangleK 1 triangleFace 2 = triangleEdge01 := by
  apply Subtype.ext
  change triangleFace.1.erase (triangleFace.1.orderEmbOfFin triangleFace.2.2 2) =
    triangleEdge01.1
  rw [triangleFace_orderEmb]
  decide

private theorem edgeB0_array :
    (fun i j => boundaryMatrix edgeK ℤ 0 (edgeVertex i) (edgeColumn j)) =
      !![-1; 1] := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    (simp only [boundaryMatrix_apply, Fin.sum_univ_succ, edgeColumn,
      deletedFace, edge01_orderEmb]
     decide)

private theorem triangleB0_array :
    (fun i j => boundaryMatrix triangleK ℤ 0
      (triangleVertex i) (triangleEdge j)) =
      !![-1, -1, 0; 1, 0, -1; 0, 1, 1] := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    (norm_num [boundaryMatrix_apply, Fin.sum_univ_succ, triangleEdge,
        triangleEdge01_del0, triangleEdge01_del1,
        triangleEdge02_del0, triangleEdge02_del1,
        triangleEdge12_del0, triangleEdge12_del1, triangleVertex]
     all_goals decide)

private theorem triangleB1_array :
    (fun i j => boundaryMatrix triangleK ℤ 1
      (triangleEdge i) (triangleColumn j)) =
      !![1; -1; 1] := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    (simp only [boundaryMatrix_apply, Fin.sum_univ_succ, triangleColumn,
      deletedFace, triangleFace_orderEmb]
     decide)

private def singletonColumn (_ : Fin 1) :
    Face (Filtration.singletonFace (0 : Fin 3)) 0 := singletonVertex 0

private theorem singletonColumn_bijective : Function.Bijective singletonColumn := by
  constructor
  · intro i j _
    exact Subsingleton.elim i j
  · intro s
    exact ⟨0, Subsingleton.elim _ _⟩

private theorem singletonJ0_array :
    (fun i j => chainInclusionMatrix ℤ singleton_le_edge 0
      (edgeVertex i) (singletonColumn j)) = !![1; 0] := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    (norm_num [chainInclusionMatrix_apply, faceIncl, edgeVertex,
        singletonColumn, singletonVertex]
     all_goals decide)

private theorem edgeJ0_array :
    (fun i j => chainInclusionMatrix ℤ edge_le_triangle 0
      (triangleVertex i) (edgeVertex j)) =
      !![1, 0; 0, 1; 0, 0] := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    (norm_num [chainInclusionMatrix_apply, faceIncl, edgeVertex, triangleVertex]
     all_goals decide)

private theorem edgeJ1_array :
    (fun i j => chainInclusionMatrix ℤ edge_le_triangle 1
      (triangleEdge i) (edgeColumn j)) = !![1; 0; 0] := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    (norm_num [chainInclusionMatrix_apply, faceIncl, triangleEdge,
        triangleEdge01, triangleEdge02, triangleEdge12, edgeColumn, edge01]
     all_goals decide)

private theorem triangle_arrays_cancel :
    (!![-1, -1, 0; 1, 0, -1; 0, 1, 1] : Matrix (Fin 3) (Fin 3) ℤ) *
      (!![1; -1; 1] : Matrix (Fin 3) (Fin 1) ℤ) = 0 := by
  decide

private theorem edge_triangle_arrays_agree :
    (!![-1, -1, 0; 1, 0, -1; 0, 1, 1] : Matrix (Fin 3) (Fin 3) ℤ) *
      (!![1; 0; 0] : Matrix (Fin 3) (Fin 1) ℤ) =
    (!![1, 0; 0, 1; 0, 0] : Matrix (Fin 3) (Fin 2) ℤ) *
      (!![-1; 1] : Matrix (Fin 2) (Fin 1) ℤ) := by
  decide

private theorem edge_triangle_common_column :
    (!![-1, -1, 0; 1, 0, -1; 0, 1, 1] : Matrix (Fin 3) (Fin 3) ℤ) *
      (!![1; 0; 0] : Matrix (Fin 3) (Fin 1) ℤ) = !![-1; 1; 0] := by
  decide

private theorem triangle_square :
    boundaryMatrix triangleK ℤ 0 * boundaryMatrix triangleK ℤ 1 = 0 :=
  boundaryMatrix_mul_boundaryMatrix triangleK ℤ 0

private theorem edge_triangle_square :
    boundaryMatrix triangleK ℤ 0 * chainInclusionMatrix ℤ edge_le_triangle 1 =
      chainInclusionMatrix ℤ edge_le_triangle 0 * boundaryMatrix edgeK ℤ 0 :=
  boundaryMatrix_chainInclusionMatrix ℤ edge_le_triangle 0

private theorem singleton_edge_square :
    boundaryMatrix edgeK ℤ 0 * chainInclusionMatrix ℤ singleton_le_edge 1 =
      chainInclusionMatrix ℤ singleton_le_edge 0 *
        boundaryMatrix (Filtration.singletonFace (0 : Fin 3)) ℤ 0 :=
  boundaryMatrix_chainInclusionMatrix ℤ singleton_le_edge 0

private theorem edge_scalar (a : ℤ) (i : Fin 2) :
    chainCoordinates edgeK ℤ 0
      (boundary edgeK ℤ 0 (Finsupp.single edge01 a)) (edgeVertex i) =
      if i = 0 then -a else a := by
  rw [chainCoordinates_apply, boundary_single]
  fin_cases i <;>
    simp [Fin.sum_univ_succ, edge_del0, edge_del1, edgeVertex]

private theorem triangle_middle_generic (R : Type v) [CommRing R] :
    boundaryMatrix triangleK R 1 triangleEdge02 triangleFace = (-1 : R) := by
  rw [← triangleFace_del1]
  simpa using boundaryMatrix_deletedFace triangleK R 1 triangleFace 1

private theorem triangle_middle_zero_ring :
    boundaryMatrix triangleK (ZMod 1) 1 triangleEdge02 triangleFace = 0 := by
  exact Subsingleton.elim _ _

private theorem triangle_off_deletion_zero :
    boundaryMatrix triangleK ℤ 0 (triangleVertex 2) triangleEdge01 = 0 := by
  have h := congrFun (congrFun triangleB0_array (2 : Fin 3)) (0 : Fin 3)
  simpa [triangleEdge] using h

private theorem edge_inclusion_scalar (a : ℤ) :
    chainInclusionMatrix ℤ edge_le_triangle 1 *ᵥ
        chainCoordinates edgeK ℤ 1 (Finsupp.single edge01 a) =
      chainCoordinates triangleK ℤ 1
        (chainIncl ℤ edge_le_triangle 1 (Finsupp.single edge01 a)) :=
  chainInclusionMatrix_mulVec ℤ edge_le_triangle 1 _

private noncomputable def edgeVertexEquiv : Fin 2 ≃ Face edgeK 0 :=
  Equiv.ofBijective edgeVertex edgeVertex_bijective

private noncomputable def edgeColumnEquiv : Fin 1 ≃ Face edgeK 1 :=
  Equiv.ofBijective edgeColumn edgeColumn_bijective

private noncomputable def triangleVertexEquiv : Fin 3 ≃ Face triangleK 0 :=
  Equiv.ofBijective triangleVertex triangleVertex_bijective

private noncomputable def triangleEdgeEquiv : Fin 3 ≃ Face triangleK 1 :=
  Equiv.ofBijective triangleEdge triangleEdge_bijective

private noncomputable def triangleColumnEquiv : Fin 1 ≃ Face triangleK 2 :=
  Equiv.ofBijective triangleColumn triangleColumn_bijective

private noncomputable def singletonColumnEquiv :
    Fin 1 ≃ Face (Filtration.singletonFace (0 : Fin 3)) 0 :=
  Equiv.ofBijective singletonColumn singletonColumn_bijective

private theorem triangleB0_reindexed :
    Matrix.reindex triangleVertexEquiv.symm triangleEdgeEquiv.symm
      (boundaryMatrix triangleK ℤ 0) =
        !![-1, -1, 0; 1, 0, -1; 0, 1, 1] := by
  ext i j
  simpa [Matrix.reindex_apply, triangleVertexEquiv, triangleEdgeEquiv] using
    congrFun (congrFun triangleB0_array i) j

private theorem triangleB1_reindexed :
    Matrix.reindex triangleEdgeEquiv.symm triangleColumnEquiv.symm
      (boundaryMatrix triangleK ℤ 1) = !![1; -1; 1] := by
  ext i j
  simpa [Matrix.reindex_apply, triangleEdgeEquiv, triangleColumnEquiv] using
    congrFun (congrFun triangleB1_array i) j

private theorem edgeB0_reindexed :
    Matrix.reindex edgeVertexEquiv.symm edgeColumnEquiv.symm
      (boundaryMatrix edgeK ℤ 0) = !![-1; 1] := by
  ext i j
  simpa [Matrix.reindex_apply, edgeVertexEquiv, edgeColumnEquiv] using
    congrFun (congrFun edgeB0_array i) j

private theorem edgeJ0_reindexed :
    Matrix.reindex triangleVertexEquiv.symm edgeVertexEquiv.symm
      (chainInclusionMatrix ℤ edge_le_triangle 0) =
        !![1, 0; 0, 1; 0, 0] := by
  ext i j
  simpa [Matrix.reindex_apply, triangleVertexEquiv, edgeVertexEquiv] using
    congrFun (congrFun edgeJ0_array i) j

private theorem edgeJ1_reindexed :
    Matrix.reindex triangleEdgeEquiv.symm edgeColumnEquiv.symm
      (chainInclusionMatrix ℤ edge_le_triangle 1) = !![1; 0; 0] := by
  ext i j
  simpa [Matrix.reindex_apply, triangleEdgeEquiv, edgeColumnEquiv] using
    congrFun (congrFun edgeJ1_array i) j

private theorem singletonJ0_reindexed :
    Matrix.reindex edgeVertexEquiv.symm singletonColumnEquiv.symm
      (chainInclusionMatrix ℤ singleton_le_edge 0) = !![1; 0] := by
  ext i j
  simpa [Matrix.reindex_apply, edgeVertexEquiv, singletonColumnEquiv] using
    congrFun (congrFun singletonJ0_array i) j

private theorem triangle_cancel_reindexed :
    Matrix.reindex triangleVertexEquiv.symm triangleColumnEquiv.symm
      (boundaryMatrix triangleK ℤ 0 * boundaryMatrix triangleK ℤ 1) = 0 := by
  change (Matrix.reindexLinearEquiv ℤ ℤ
    triangleVertexEquiv.symm triangleColumnEquiv.symm)
    (boundaryMatrix triangleK ℤ 0 * boundaryMatrix triangleK ℤ 1) = 0
  rw [← Matrix.reindexLinearEquiv_mul (R := ℤ) (A := ℤ)
    triangleVertexEquiv.symm triangleEdgeEquiv.symm triangleColumnEquiv.symm
    (boundaryMatrix triangleK ℤ 0) (boundaryMatrix triangleK ℤ 1)]
  change Matrix.reindex triangleVertexEquiv.symm triangleEdgeEquiv.symm
      (boundaryMatrix triangleK ℤ 0) *
    Matrix.reindex triangleEdgeEquiv.symm triangleColumnEquiv.symm
      (boundaryMatrix triangleK ℤ 1) = 0
  rw [triangleB0_reindexed, triangleB1_reindexed, triangle_arrays_cancel]

private theorem edge_triangle_common_reindexed :
    Matrix.reindex triangleVertexEquiv.symm edgeColumnEquiv.symm
      (boundaryMatrix triangleK ℤ 0 * chainInclusionMatrix ℤ edge_le_triangle 1) =
        !![-1; 1; 0] := by
  change (Matrix.reindexLinearEquiv ℤ ℤ
    triangleVertexEquiv.symm edgeColumnEquiv.symm)
    (boundaryMatrix triangleK ℤ 0 * chainInclusionMatrix ℤ edge_le_triangle 1) =
      !![-1; 1; 0]
  rw [← Matrix.reindexLinearEquiv_mul (R := ℤ) (A := ℤ)
    triangleVertexEquiv.symm triangleEdgeEquiv.symm edgeColumnEquiv.symm
    (boundaryMatrix triangleK ℤ 0) (chainInclusionMatrix ℤ edge_le_triangle 1)]
  change Matrix.reindex triangleVertexEquiv.symm triangleEdgeEquiv.symm
      (boundaryMatrix triangleK ℤ 0) *
    Matrix.reindex triangleEdgeEquiv.symm edgeColumnEquiv.symm
      (chainInclusionMatrix ℤ edge_le_triangle 1) = !![-1; 1; 0]
  rw [triangleB0_reindexed, edgeJ1_reindexed, edge_triangle_common_column]

private theorem edge_triangle_right_reindexed :
    Matrix.reindex triangleVertexEquiv.symm edgeColumnEquiv.symm
      (chainInclusionMatrix ℤ edge_le_triangle 0 * boundaryMatrix edgeK ℤ 0) =
        !![-1; 1; 0] := by
  change (Matrix.reindexLinearEquiv ℤ ℤ
    triangleVertexEquiv.symm edgeColumnEquiv.symm)
    (chainInclusionMatrix ℤ edge_le_triangle 0 * boundaryMatrix edgeK ℤ 0) =
      !![-1; 1; 0]
  rw [← Matrix.reindexLinearEquiv_mul (R := ℤ) (A := ℤ)
    triangleVertexEquiv.symm edgeVertexEquiv.symm edgeColumnEquiv.symm
    (chainInclusionMatrix ℤ edge_le_triangle 0) (boundaryMatrix edgeK ℤ 0)]
  change Matrix.reindex triangleVertexEquiv.symm edgeVertexEquiv.symm
      (chainInclusionMatrix ℤ edge_le_triangle 0) *
    Matrix.reindex edgeVertexEquiv.symm edgeColumnEquiv.symm
      (boundaryMatrix edgeK ℤ 0) = !![-1; 1; 0]
  rw [edgeJ0_reindexed, edgeB0_reindexed]
  decide

end TheoryFixtures

-- Trust inventory for private fixture declarations and generated auxiliaries.
#print axioms faceFintypeLocal
#print axioms totalFinite_square
#print axioms totalFinite_inclusion
#print axioms finiteTotal_bound
#print axioms bottom_matrix_zero
#print axioms bottom_outgoing_zero
#print axioms singleton_coordinate
#print axioms singleton_matrix_zero
#print axioms singleton_outgoing_zero
#print axioms edgeK
#print axioms triangleK
#print axioms singleton_le_edge
#print axioms edge_le_triangle
#print axioms edgeVertex
#print axioms edge01
#print axioms triangleVertex
#print axioms triangleEdge01
#print axioms triangleEdge02
#print axioms triangleEdge12
#print axioms triangleEdge
#print axioms triangleFace
#print axioms edgeColumn
#print axioms triangleColumn
#print axioms edgeVertex_bijective
#print axioms edgeColumn_bijective
#print axioms triangleVertex_bijective
#print axioms triangleEdge_bijective
#print axioms triangleColumn_bijective
#print axioms edge01_orderEmb
#print axioms triangleEdge01_orderEmb
#print axioms triangleEdge02_orderEmb
#print axioms triangleEdge12_orderEmb
#print axioms triangleFace_orderEmb
#print axioms edge_del0
#print axioms edge_del1
#print axioms triangleEdge01_del0
#print axioms triangleEdge01_del1
#print axioms triangleEdge02_del0
#print axioms triangleEdge02_del1
#print axioms triangleEdge12_del0
#print axioms triangleEdge12_del1
#print axioms triangleFace_del0
#print axioms triangleFace_del1
#print axioms triangleFace_del2
#print axioms edgeB0_array
#print axioms triangleB0_array
#print axioms triangleB1_array
#print axioms singletonColumn
#print axioms singletonColumn_bijective
#print axioms singletonJ0_array
#print axioms edgeJ0_array
#print axioms edgeJ1_array
#print axioms triangle_arrays_cancel
#print axioms edge_triangle_arrays_agree
#print axioms edge_triangle_common_column
#print axioms triangle_square
#print axioms edge_triangle_square
#print axioms singleton_edge_square
#print axioms edge_scalar
#print axioms triangle_middle_generic
#print axioms triangle_middle_zero_ring
#print axioms triangle_off_deletion_zero
#print axioms edge_inclusion_scalar
#print axioms edgeVertexEquiv
#print axioms edgeColumnEquiv
#print axioms triangleVertexEquiv
#print axioms triangleEdgeEquiv
#print axioms triangleColumnEquiv
#print axioms singletonColumnEquiv
#print axioms triangleB0_reindexed
#print axioms triangleB1_reindexed
#print axioms edgeB0_reindexed
#print axioms edgeJ0_reindexed
#print axioms edgeJ1_reindexed
#print axioms singletonJ0_reindexed
#print axioms triangle_cancel_reindexed
#print axioms edge_triangle_common_reindexed
#print axioms edge_triangle_right_reindexed
#print axioms edge01._proof_1
#print axioms edge01.eq_1
#print axioms edgeColumn.eq_1
#print axioms edgeColumnEquiv.eq_1
#print axioms edgeK._proof_1
#print axioms edgeK._proof_2
#print axioms edgeVertex._proof_1
#print axioms edgeVertex._proof_2
#print axioms edgeVertex.eq_1
#print axioms edgeVertexEquiv.eq_1
#print axioms singletonColumn.eq_1
#print axioms singletonColumnEquiv.eq_1
#print axioms triangleColumn.eq_1
#print axioms triangleColumnEquiv.eq_1
#print axioms triangleEdge.eq_1
#print axioms triangleEdge01._proof_1
#print axioms triangleEdge01.eq_1
#print axioms triangleEdge02._proof_1
#print axioms triangleEdge02.eq_1
#print axioms triangleEdge12._proof_1
#print axioms triangleEdge12.eq_1
#print axioms triangleEdgeEquiv.eq_1
#print axioms triangleFace._proof_1
#print axioms triangleFace.eq_1
#print axioms triangleVertex._proof_1
#print axioms triangleVertex.eq_1
#print axioms triangleVertexEquiv.eq_1

end TDA.Simplicial
