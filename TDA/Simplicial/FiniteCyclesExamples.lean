import TDA.Simplicial.FiniteCycles
import TDA.Simplicial.FiniteComplex
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Reindex

/-! # Actual-face coordinate fixtures

The complete displayed arrays are reindexed through proved face bijections.
They use the actual boundary and inclusion matrices over integers and `ZMod 1`.
-/

universe u v

open scoped BigOperators Matrix
open Module

namespace TDA.Simplicial.InternalFiniteCycleFixtures

variable {V : Type u} [LinearOrder V]

section TheoryFixtures

noncomputable local instance finiteCyclesFaceFintype
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

def edgeK : PreAbstractSimplicialComplex (Fin 3) where
  faces := {s | s.Nonempty ∧ s ⊆ ({0, 1} : Finset (Fin 3))}
  isRelLowerSet_faces := by
    intro s hs
    exact ⟨hs.1, fun t hts ht => ⟨ht, hts.trans hs.2⟩⟩

def triangleK : PreAbstractSimplicialComplex (Fin 3) := ⊤

theorem singleton_le_edge :
    Filtration.singletonFace (0 : Fin 3) ≤ edgeK := by
  intro s hs
  have hs' := (Filtration.mem_singletonFace_iff (0 : Fin 3) s).mp hs
  change s.Nonempty ∧ s ⊆ ({0, 1} : Finset (Fin 3))
  subst s
  decide

theorem edge_le_triangle : edgeK ≤ triangleK := by
  intro s hs
  exact hs.1

def edgeVertex (i : Fin 2) : Face edgeK 0 :=
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

theorem edgeVertex_bijective : Function.Bijective edgeVertex := by
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

private theorem triangle_square_actual :
    boundaryMatrix triangleK ℤ 0 * boundaryMatrix triangleK ℤ 1 = 0 :=
  boundaryMatrix_mul_boundaryMatrix triangleK ℤ 0

private theorem edge_triangle_square_actual :
    boundaryMatrix triangleK ℤ 0 * chainInclusionMatrix ℤ edge_le_triangle 1 =
      chainInclusionMatrix ℤ edge_le_triangle 0 * boundaryMatrix edgeK ℤ 0 :=
  boundaryMatrix_chainInclusionMatrix ℤ edge_le_triangle 0

private theorem singleton_edge_square_actual :
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

private theorem triangle_actual_cancel_reindexed :
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

private theorem edge_triangle_actual_common_reindexed :
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

private theorem edge_triangle_actual_right_reindexed :
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

def unfilledK : PreAbstractSimplicialComplex (Fin 3) where
  faces := {s | s.Nonempty ∧ s.card ≤ 2}
  isRelLowerSet_faces := by
    intro s hs
    exact ⟨hs.1, fun t hts ht => ⟨ht, (Finset.card_le_card hts).trans hs.2⟩⟩

theorem unfilled_le_triangle : unfilledK ≤ triangleK := by
  intro s hs
  exact hs.1

private def unfilledEdge01 : Face unfilledK 1 :=
  ⟨{0, 1}, by change ({0, 1} : Finset (Fin 3)).Nonempty ∧
    ({0, 1} : Finset (Fin 3)).card ≤ 2; decide, by decide⟩
private def unfilledEdge02 : Face unfilledK 1 :=
  ⟨{0, 2}, by change ({0, 2} : Finset (Fin 3)).Nonempty ∧
    ({0, 2} : Finset (Fin 3)).card ≤ 2; decide, by decide⟩
private def unfilledEdge12 : Face unfilledK 1 :=
  ⟨{1, 2}, by change ({1, 2} : Finset (Fin 3)).Nonempty ∧
    ({1, 2} : Finset (Fin 3)).card ≤ 2; decide, by decide⟩

private def unfilledEdge (i : Fin 3) : Face unfilledK 1 :=
  if i = 0 then unfilledEdge01 else if i = 1 then unfilledEdge02 else unfilledEdge12

private theorem unfilledEdge_bijective : Function.Bijective unfilledEdge := by
  constructor
  · intro i j h
    have hv := congrArg Subtype.val h
    fin_cases i <;> fin_cases j <;>
      first | rfl |
        (simp [unfilledEdge, unfilledEdge01, unfilledEdge02, unfilledEdge12] at hv
         exact False.elim (absurd hv (by decide)))
  · intro s
    have h : ∀ t : Finset (Fin 3), t.card = 2 →
        t = {0, 1} ∨ t = {0, 2} ∨ t = {1, 2} := by decide
    rcases h s.1 s.2.2 with hs | hs | hs
    · exact ⟨0, Subtype.ext (by simpa [unfilledEdge, unfilledEdge01] using hs.symm)⟩
    · exact ⟨1, Subtype.ext (by simpa [unfilledEdge, unfilledEdge02] using hs.symm)⟩
    · exact ⟨2, Subtype.ext (by simpa [unfilledEdge, unfilledEdge12] using hs.symm)⟩

private noncomputable def unfilledEdgeEquiv : Fin 3 ≃ Face unfilledK 1 :=
  Equiv.ofBijective unfilledEdge unfilledEdge_bijective

private theorem unfilledFace2_empty : IsEmpty (Face unfilledK 2) := by
  refine ⟨fun s => ?_⟩
  have hc : s.1.card = 3 := s.2.2
  have hle : s.1.card ≤ 2 := s.2.1.2
  omega

private theorem unfilled_to_triangle_edges (i : Fin 3) :
    faceIncl unfilled_le_triangle 1 (unfilledEdge i) = triangleEdge i := by
  fin_cases i <;> apply Subtype.ext <;>
    simp [unfilledEdge, triangleEdge, unfilledEdge01, unfilledEdge02,
      unfilledEdge12, triangleEdge01, triangleEdge02, triangleEdge12, faceIncl]

private noncomputable def signedUnfilled : Chain unfilledK ℤ 1 :=
  Finsupp.single unfilledEdge01 1 - Finsupp.single unfilledEdge02 1 +
    Finsupp.single unfilledEdge12 1

private theorem signedUnfilled_coeff (i : Fin 3) :
    signedUnfilled (unfilledEdge i) =
      if i = 0 then 1 else if i = 1 then -1 else 1 := by
  fin_cases i <;>
    (simp [signedUnfilled, unfilledEdge, unfilledEdge01, unfilledEdge02,
      unfilledEdge12, Finsupp.single_apply]
     all_goals decide)

private theorem triangleFace_boundary_signed :
    boundary triangleK ℤ 1 (Finsupp.single triangleFace 1) =
      Finsupp.single triangleEdge01 1 - Finsupp.single triangleEdge02 1 +
        Finsupp.single triangleEdge12 1 := by
  rw [boundary_single]
  simp [Fin.sum_univ_succ, triangleFace_del0, triangleFace_del1,
    triangleFace_del2, Finsupp.smul_single]
  abel

private theorem signedUnfilled_includes_boundary :
    chainIncl ℤ unfilled_le_triangle 1 signedUnfilled =
      boundary triangleK ℤ 1 (Finsupp.single triangleFace 1) := by
  rw [triangleFace_boundary_signed]
  simp only [signedUnfilled, map_add, map_sub, chainIncl_single]
  congr 1

private theorem chainIncl_injective_fixture
    {A B : PreAbstractSimplicialComplex (Fin 3)} (h : A ≤ B) (n : ℕ) :
    Function.Injective (chainIncl ℤ h n) := by
  intro a b hab
  have hf : Function.Injective (faceIncl h n) := by
    intro x y hxy
    have hv : x.1 = y.1 := congrArg (fun z : Face B n => z.1) hxy
    exact Subtype.ext hv
  apply Finsupp.mapDomain_injective hf
  simpa only [chainIncl, Finsupp.lmapDomain_apply] using hab

private theorem signedUnfilled_cycle :
    signedUnfilled ∈ simplicialCycles unfilledK ℤ 1 := by
  rw [simplicialCycles_succ]
  change boundary unfilledK ℤ 0 signedUnfilled = 0
  have hs := congrArg (fun f : Chain unfilledK ℤ 1 →ₗ[ℤ] Chain triangleK ℤ 0 =>
    f signedUnfilled) (boundary_chainIncl ℤ unfilled_le_triangle 0)
  change boundary triangleK ℤ 0 (chainIncl ℤ unfilled_le_triangle 1 signedUnfilled) =
    chainIncl ℤ unfilled_le_triangle 0 (boundary unfilledK ℤ 0 signedUnfilled) at hs
  rw [signedUnfilled_includes_boundary] at hs
  have hzero := congrArg
    (fun f : Chain triangleK ℤ 2 →ₗ[ℤ] Chain triangleK ℤ 0 =>
      f (Finsupp.single triangleFace 1)) (boundary_comp_boundary triangleK ℤ 0)
  simp only [LinearMap.comp_apply, LinearMap.zero_apply] at hzero
  rw [hzero] at hs
  exact chainIncl_injective_fixture unfilled_le_triangle 0
    (hs.symm.trans (map_zero _).symm)

noncomputable def signedUnfilledCycle : simplicialCycles unfilledK ℤ 1 :=
  ⟨signedUnfilled, signedUnfilled_cycle⟩

noncomputable def signedUnfilledCoord : coordinateCycles unfilledK ℤ 1 :=
  cycleCoordinates unfilledK ℤ 1 signedUnfilledCycle

private theorem signedUnfilledCoord_coeff (i : Fin 3) :
    (signedUnfilledCoord : Face unfilledK 1 → ℤ) (unfilledEdge i) =
      if i = 0 then 1 else if i = 1 then -1 else 1 := by
  rw [signedUnfilledCoord, cycleCoordinates_coe, chainCoordinates_apply]
  exact signedUnfilled_coeff i

private theorem signedUnfilledCoord_ne_zero : signedUnfilledCoord ≠ 0 := by
  intro hz
  have h := signedUnfilledCoord_coeff 0
  rw [hz] at h
  norm_num at h

private theorem unfilledBoundaries_bot : coordinateBoundaries unfilledK ℤ 1 = ⊥ := by
  apply le_antisymm _ bot_le
  intro z hz
  obtain ⟨x, hx⟩ := (mem_coordinateBoundaries_iff unfilledK ℤ 1 z).mp hz
  have hx0 : x = 0 := by
    funext σ
    exact isEmptyElim (unfilledFace2_empty.false σ)
  subst x
  simp only [Matrix.mulVec_zero] at hx
  change z = 0
  exact Subtype.ext hx.symm

theorem signedUnfilledCoord_not_boundary :
    signedUnfilledCoord ∉ coordinateBoundaries unfilledK ℤ 1 := by
  rw [unfilledBoundaries_bot]
  simpa using signedUnfilledCoord_ne_zero

theorem signedUnfilled_included_boundary :
    coordinateCycleIncl ℤ unfilled_le_triangle 1 signedUnfilledCoord ∈
      coordinateBoundaries triangleK ℤ 1 := by
  apply (mem_coordinateBoundaries_iff triangleK ℤ 1 _).mpr
  refine ⟨chainCoordinates triangleK ℤ 2 (Finsupp.single triangleFace 1), ?_⟩
  rw [boundaryMatrix_mulVec, coordinateCycleIncl_coe]
  rw [signedUnfilledCoord, cycleCoordinates_coe]
  rw [chainInclusionMatrix_mulVec]
  change chainCoordinates triangleK ℤ 1
      (boundary triangleK ℤ 1 (Finsupp.single triangleFace 1)) =
    chainCoordinates triangleK ℤ 1 (chainIncl ℤ unfilled_le_triangle 1 signedUnfilled)
  rw [signedUnfilled_includes_boundary]

private theorem signedUnfilled_naturality :
    coordinateCycleIncl ℤ unfilled_le_triangle 1 signedUnfilledCoord =
      cycleCoordinates triangleK ℤ 1
        (simplicialCycleIncl ℤ unfilled_le_triangle 1 signedUnfilledCycle) := by
  exact congrArg (fun f : simplicialCycles unfilledK ℤ 1 →ₗ[ℤ]
      coordinateCycles triangleK ℤ 1 => f signedUnfilledCycle)
    (cycleCoordinates_naturality ℤ unfilled_le_triangle 1)

private theorem signedUnfilled_included_actual_boundary :
    (simplicialCycleIncl ℤ unfilled_le_triangle 1 signedUnfilledCycle) ∈
      simplicialBoundaries triangleK ℤ 1 := by
  apply (mem_simplicialBoundaries_iff ℤ triangleK 1 _).mpr
  refine ⟨Finsupp.single triangleFace 1, ?_⟩
  rw [simplicialCycleIncl_coe]
  exact signedUnfilled_includes_boundary.symm

private theorem signedUnfilled_included_eq_boundary :
    coordinateCycleIncl ℤ unfilled_le_triangle 1 signedUnfilledCoord =
      coordinateBoundaryToCycles triangleK ℤ 1
        (chainCoordinates triangleK ℤ 2 (Finsupp.single triangleFace 1)) := by
  apply Subtype.ext
  rw [coordinateCycleIncl_coe, coordinateBoundaryToCycles_coe,
    boundaryMatrix_mulVec, signedUnfilledCoord, cycleCoordinates_coe,
    chainInclusionMatrix_mulVec]
  exact congrArg (chainCoordinates triangleK ℤ 1)
    signedUnfilled_includes_boundary

private theorem signedUnfilledCoord_kernel :
    (signedUnfilledCoord : Face unfilledK 1 → ℤ) ∈
      LinearMap.ker (Matrix.toLin' (boundaryMatrix unfilledK ℤ 0)) := by
  let x : Face triangleK 2 → ℤ :=
    chainCoordinates triangleK ℤ 2 (Finsupp.single triangleFace 1)
  have harray : boundaryMatrix triangleK ℤ 0 * boundaryMatrix triangleK ℤ 1 = 0 := by
    apply (Matrix.reindexLinearEquiv ℤ ℤ
      triangleVertexEquiv.symm triangleColumnEquiv.symm).injective
    change Matrix.reindex triangleVertexEquiv.symm triangleColumnEquiv.symm
      (boundaryMatrix triangleK ℤ 0 * boundaryMatrix triangleK ℤ 1) = 0
    exact triangle_actual_cancel_reindexed
  have hinc := congrArg Subtype.val signedUnfilled_included_eq_boundary
  change chainInclusionMatrix ℤ unfilled_le_triangle 1 *ᵥ
      (signedUnfilledCoord : Face unfilledK 1 → ℤ) =
    boundaryMatrix triangleK ℤ 1 *ᵥ x at hinc
  have hj : chainInclusionMatrix ℤ unfilled_le_triangle 0 *ᵥ
      (boundaryMatrix unfilledK ℤ 0 *ᵥ
        (signedUnfilledCoord : Face unfilledK 1 → ℤ)) = 0 := by
    calc
      _ = (chainInclusionMatrix ℤ unfilled_le_triangle 0 *
          boundaryMatrix unfilledK ℤ 0) *ᵥ
            (signedUnfilledCoord : Face unfilledK 1 → ℤ) :=
        Matrix.mulVec_mulVec _ _ _
      _ = (boundaryMatrix triangleK ℤ 0 *
          chainInclusionMatrix ℤ unfilled_le_triangle 1) *ᵥ
            (signedUnfilledCoord : Face unfilledK 1 → ℤ) := by
        rw [boundaryMatrix_chainInclusionMatrix]
      _ = boundaryMatrix triangleK ℤ 0 *ᵥ
          (chainInclusionMatrix ℤ unfilled_le_triangle 1 *ᵥ
            (signedUnfilledCoord : Face unfilledK 1 → ℤ)) :=
        (Matrix.mulVec_mulVec _ _ _).symm
      _ = boundaryMatrix triangleK ℤ 0 *ᵥ (boundaryMatrix triangleK ℤ 1 *ᵥ x) := by
        rw [hinc]
      _ = (boundaryMatrix triangleK ℤ 0 * boundaryMatrix triangleK ℤ 1) *ᵥ x :=
        Matrix.mulVec_mulVec _ _ _
      _ = 0 := by rw [harray]; exact Matrix.zero_mulVec x
  have hm : boundaryMatrix unfilledK ℤ 0 *ᵥ
      (signedUnfilledCoord : Face unfilledK 1 → ℤ) = 0 := by
    let c : Chain unfilledK ℤ 0 := (chainCoordinates unfilledK ℤ 0).symm
      (boundaryMatrix unfilledK ℤ 0 *ᵥ
        (signedUnfilledCoord : Face unfilledK 1 → ℤ))
    have hc := chainInclusionMatrix_mulVec ℤ unfilled_le_triangle 0 c
    change chainInclusionMatrix ℤ unfilled_le_triangle 0 *ᵥ
        (boundaryMatrix unfilledK ℤ 0 *ᵥ
          (signedUnfilledCoord : Face unfilledK 1 → ℤ)) =
        chainCoordinates triangleK ℤ 0 (chainIncl ℤ unfilled_le_triangle 0 c) at hc
    have hc0 : chainIncl ℤ unfilled_le_triangle 0 c = 0 :=
      (chainCoordinates triangleK ℤ 0).injective (by simpa only [map_zero] using hc.symm.trans hj)
    have c0 : c = 0 := (chainIncl_injective_fixture unfilled_le_triangle 0)
      (by simpa only [map_zero] using hc0)
    have hcoord := (chainCoordinates unfilledK ℤ 0).apply_symm_apply
      (boundaryMatrix unfilledK ℤ 0 *ᵥ
        (signedUnfilledCoord : Face unfilledK 1 → ℤ))
    calc
      boundaryMatrix unfilledK ℤ 0 *ᵥ
          (signedUnfilledCoord : Face unfilledK 1 → ℤ) =
        chainCoordinates unfilledK ℤ 0 c := hcoord.symm
      _ = 0 := by rw [c0, map_zero]
  let vec : Face unfilledK 1 → ℤ := signedUnfilledCoord
  have hker : vec ∈ LinearMap.ker (Matrix.toLin' (boundaryMatrix unfilledK ℤ 0)) := by
    simpa only [LinearMap.mem_ker, Matrix.toLin'_apply] using hm
  have hid := coordinateCycles_succ unfilledK ℤ 0
  have hcycle : vec ∈ coordinateCycles unfilledK ℤ 1 := by
    simpa only [hid] using hker
  simpa only [hid] using hcycle

private theorem signedUnfilled_included_inverse_actual :
    ((cycleCoordinates triangleK ℤ 1).symm
      (coordinateCycleIncl ℤ unfilled_le_triangle 1 signedUnfilledCoord) :
        Chain triangleK ℤ 1) =
      boundary triangleK ℤ 1 (Finsupp.single triangleFace 1) := by
  apply (chainCoordinates triangleK ℤ 1).injective
  have hcc := cycleCoordinates_coe triangleK ℤ 1
    ((cycleCoordinates triangleK ℤ 1).symm
      (coordinateCycleIncl ℤ unfilled_le_triangle 1 signedUnfilledCoord))
  rw [LinearEquiv.apply_symm_apply] at hcc
  rw [← hcc, signedUnfilled_included_eq_boundary,
    coordinateBoundaryToCycles_coe, boundaryMatrix_mulVec]

theorem signedUnfilled_included_ne_zero :
    coordinateCycleIncl ℤ unfilled_le_triangle 1 signedUnfilledCoord ≠ 0 := by
  intro hz
  have h := congrArg (fun z : coordinateCycles triangleK ℤ 1 =>
    (z : Face triangleK 1 → ℤ) triangleEdge01) hz
  rw [coordinateCycleIncl_coe, signedUnfilledCoord, cycleCoordinates_coe,
    chainInclusionMatrix_mulVec] at h
  change chainCoordinates triangleK ℤ 1
    (chainIncl ℤ unfilled_le_triangle 1 signedUnfilled) triangleEdge01 = 0 at h
  rw [signedUnfilled_includes_boundary, triangleFace_boundary_signed,
    chainCoordinates_apply] at h
  -- The same signed chain has coefficient one at e01 after inclusion.
  simp [triangleFace_boundary_signed, Finsupp.single_apply,
    triangleEdge01, triangleEdge02, triangleEdge12] at h
  have hneq1 : ({0, 2} : Finset (Fin 3)) ≠ {0, 1} := by decide
  have hneq2 : ({1, 2} : Finset (Fin 3)) ≠ {0, 1} := by decide
  simp [hneq1, hneq2] at h

theorem bottom_cycles_zero (n : ℕ) (z :
    coordinateCycles (⊥ : PreAbstractSimplicialComplex (Fin 3)) ℤ n) : z = 0 := by
  apply Subtype.ext
  funext σ
  exact isEmptyElim σ

private theorem bottom_boundaries_bot (n : ℕ) :
    coordinateBoundaries (⊥ : PreAbstractSimplicialComplex (Fin 3)) ℤ n = ⊥ := by
  apply le_antisymm _ bot_le
  intro z _
  change z = 0
  exact bottom_cycles_zero n z

private theorem singleton_cycles_top :
    coordinateCycles (Filtration.singletonFace (0 : Fin 3)) ℤ 0 = ⊤ :=
  coordinateCycles_zero _ _

private theorem singleton_edges_empty :
    IsEmpty (Face (Filtration.singletonFace (0 : Fin 3)) 1) := by
  refine ⟨fun σ => ?_⟩
  have h := (Filtration.mem_singletonFace_iff (0 : Fin 3) σ.1).mp σ.2.1
  have hc : σ.1.card = 2 := σ.2.2
  rw [h] at hc
  simp at hc

private theorem singleton_boundaries_bot :
    coordinateBoundaries (Filtration.singletonFace (0 : Fin 3)) ℤ 0 = ⊥ := by
  apply le_antisymm _ bot_le
  intro z hz
  obtain ⟨x, hx⟩ := (mem_coordinateBoundaries_iff _ ℤ 0 z).mp hz
  have hx0 : x = 0 := by
    funext σ
    exact isEmptyElim (singleton_edges_empty.false σ)
  subst x
  simp only [Matrix.mulVec_zero] at hx
  change z = 0
  exact Subtype.ext hx.symm

noncomputable def singletonCycle (a : ℤ) :
    simplicialCycles (Filtration.singletonFace (0 : Fin 3)) ℤ 0 :=
  ⟨Finsupp.single (singletonVertex 0) a,
    by rw [simplicialCycles_zero]; trivial⟩

private theorem singleton_cycle_coefficient (a : ℤ) :
    ((cycleCoordinates (Filtration.singletonFace (0 : Fin 3)) ℤ 0 (singletonCycle a) :
      Face (Filtration.singletonFace (0 : Fin 3)) 0 → ℤ) (singletonVertex 0)) = a := by
  rw [cycleCoordinates_coe]
  change chainCoordinates (Filtration.singletonFace (0 : Fin 3)) ℤ 0
    (Finsupp.single (singletonVertex 0) a) (singletonVertex 0) = a
  exact singleton_coordinate a

theorem singleton_one_not_boundary :
    (cycleCoordinates (Filtration.singletonFace (0 : Fin 3)) ℤ 0
      (singletonCycle 1)) ∉
      coordinateBoundaries (Filtration.singletonFace (0 : Fin 3)) ℤ 0 := by
  rw [singleton_boundaries_bot]
  intro hz
  have h := singleton_cycle_coefficient 1
  rw [hz] at h
  norm_num at h

private theorem edge_coordinate_input (a : ℤ) :
    (fun _ : Face edgeK 1 => a) =
      chainCoordinates edgeK ℤ 1 (Finsupp.single edge01 a) := by
  funext σ
  obtain ⟨i, rfl⟩ := edgeColumn_bijective.2 σ
  rw [chainCoordinates_apply]
  simp [edgeColumn]

theorem edge_boundary_scalar (a : ℤ) (i : Fin 2) :
    ((coordinateBoundaryToCycles edgeK ℤ 0 (fun _ => a) :
      coordinateCycles edgeK ℤ 0) : Face edgeK 0 → ℤ) (edgeVertex i) =
        if i = 0 then -a else a := by
  rw [coordinateBoundaryToCycles_coe, edge_coordinate_input,
    boundaryMatrix_mulVec]
  exact edge_scalar a i

private theorem edge_boundary_scalar_mem (a : ℤ) :
    coordinateBoundaryToCycles edgeK ℤ 0 (fun _ => a) ∈
      coordinateBoundaries edgeK ℤ 0 :=
  LinearMap.mem_range_self _ _

private theorem edge_boundary_scalar_actual (a : ℤ) :
    ((cycleCoordinates edgeK ℤ 0).symm
      (coordinateBoundaryToCycles edgeK ℤ 0 (fun _ => a)) : Chain edgeK ℤ 0) =
      boundary edgeK ℤ 0 (Finsupp.single edge01 a) := by
  apply (chainCoordinates edgeK ℤ 0).injective
  have hcc := cycleCoordinates_coe edgeK ℤ 0
    ((cycleCoordinates edgeK ℤ 0).symm
      (coordinateBoundaryToCycles edgeK ℤ 0 (fun _ => a)))
  rw [LinearEquiv.apply_symm_apply] at hcc
  calc
    chainCoordinates edgeK ℤ 0
        ((cycleCoordinates edgeK ℤ 0).symm
          (coordinateBoundaryToCycles edgeK ℤ 0 (fun _ => a)) : Chain edgeK ℤ 0) =
      (coordinateBoundaryToCycles edgeK ℤ 0 (fun _ => a) : Face edgeK 0 → ℤ) := hcc.symm
    _ = boundaryMatrix edgeK ℤ 0 *ᵥ (fun _ => a) :=
      coordinateBoundaryToCycles_coe edgeK ℤ 0 _
    _ = chainCoordinates edgeK ℤ 0
        (boundary edgeK ℤ 0 (Finsupp.single edge01 a)) := by
      rw [edge_coordinate_input]
      exact boundaryMatrix_mulVec edgeK ℤ 0 _

private theorem edge_degree1_cycles_zero (z : coordinateCycles edgeK ℤ 1) : z = 0 := by
  have hz : (z : Face edgeK 1 → ℤ) ∈
      LinearMap.ker (Matrix.toLin' (boundaryMatrix edgeK ℤ 0)) := by
    rw [← coordinateCycles_succ edgeK ℤ 0]
    exact z.property
  have hzero := LinearMap.mem_ker.mp hz
  have hcoeff : (z : Face edgeK 1 → ℤ) edge01 = 0 := by
    have h := congrFun hzero (edgeVertex 1)
    rw [Matrix.toLin'_apply] at h
    have hvec : (z : Face edgeK 1 → ℤ) =
        (fun _ : Face edgeK 1 => (z : Face edgeK 1 → ℤ) edge01) := by
      funext σ
      obtain ⟨i, rfl⟩ := edgeColumn_bijective.2 σ
      fin_cases i
      rfl
    rw [hvec, edge_coordinate_input, boundaryMatrix_mulVec] at h
    simpa [edge_scalar] using h
  apply Subtype.ext
  funext σ
  obtain ⟨i, rfl⟩ := edgeColumn_bijective.2 σ
  fin_cases i
  simpa [edgeColumn] using hcoeff

private theorem edge_degree1_boundaries_bot : coordinateBoundaries edgeK ℤ 1 = ⊥ := by
  apply le_antisymm _ bot_le
  intro z _
  change z = 0
  exact edge_degree1_cycles_zero z

private theorem edge_triangle_scalar_square (a : ℤ) :
    coordinateCycleIncl ℤ edge_le_triangle 0
        (coordinateBoundaryToCycles edgeK ℤ 0 (fun _ => a)) =
      coordinateBoundaryToCycles triangleK ℤ 0
        (Matrix.toLin' (chainInclusionMatrix ℤ edge_le_triangle 1) (fun _ => a)) := by
  exact congrArg (fun f : (Face edgeK 1 → ℤ) →ₗ[ℤ]
      coordinateCycles triangleK ℤ 0 => f (fun _ => a))
    (coordinateCycleIncl_boundaryToCycles ℤ edge_le_triangle 0)

private theorem singleton_edge_scalar (a : ℤ) (i : Fin 2) :
    ((coordinateCycleIncl ℤ singleton_le_edge 0
      (cycleCoordinates (Filtration.singletonFace (0 : Fin 3)) ℤ 0
        (singletonCycle a)) : coordinateCycles edgeK ℤ 0) :
        Face edgeK 0 → ℤ) (edgeVertex i) = if i = 0 then a else 0 := by
  rw [coordinateCycleIncl_coe, cycleCoordinates_coe,
    chainInclusionMatrix_mulVec]
  change chainCoordinates edgeK ℤ 0
    (chainIncl ℤ singleton_le_edge 0 (Finsupp.single (singletonVertex 0) a))
      (edgeVertex i) = if i = 0 then a else 0
  rw [chainIncl_single, chainCoordinates_apply]
  fin_cases i <;>
    (simp [faceIncl, edgeVertex, singletonVertex, Finsupp.single_apply]
     all_goals decide)

theorem singleton_edge_naturality (a : ℤ) :
    coordinateCycleIncl ℤ singleton_le_edge 0
      (cycleCoordinates (Filtration.singletonFace (0 : Fin 3)) ℤ 0
        (singletonCycle a)) =
    cycleCoordinates edgeK ℤ 0
      (simplicialCycleIncl ℤ singleton_le_edge 0 (singletonCycle a)) := by
  exact congrArg (fun f : simplicialCycles
      (Filtration.singletonFace (0 : Fin 3)) ℤ 0 →ₗ[ℤ]
        coordinateCycles edgeK ℤ 0 => f (singletonCycle a))
    (cycleCoordinates_naturality ℤ singleton_le_edge 0)

private theorem triangleEdge01_scalar (a : ℤ) (i : Fin 3) :
    chainCoordinates triangleK ℤ 0
      (boundary triangleK ℤ 0 (Finsupp.single triangleEdge01 a))
      (triangleVertex i) = if i = 0 then -a else if i = 1 then a else 0 := by
  rw [chainCoordinates_apply, boundary_single]
  fin_cases i <;>
    (simp [Fin.sum_univ_succ, triangleEdge01_del0, triangleEdge01_del1,
      triangleVertex, Finsupp.single_apply]
     all_goals decide)

private theorem edge_triangle_scalar_coords (a : ℤ) (i : Fin 3) :
    ((coordinateCycleIncl ℤ edge_le_triangle 0
      (coordinateBoundaryToCycles edgeK ℤ 0 (fun _ => a)) :
        coordinateCycles triangleK ℤ 0) : Face triangleK 0 → ℤ)
      (triangleVertex i) = if i = 0 then -a else if i = 1 then a else 0 := by
  rw [edge_triangle_scalar_square, coordinateBoundaryToCycles_coe]
  have hinc : Matrix.toLin' (chainInclusionMatrix ℤ edge_le_triangle 1)
      (fun _ : Face edgeK 1 => a) =
        chainCoordinates triangleK ℤ 1 (Finsupp.single triangleEdge01 a) := by
    rw [Matrix.toLin'_apply, edge_coordinate_input,
      chainInclusionMatrix_mulVec, chainIncl_single]
    congr 1
  rw [hinc, boundaryMatrix_mulVec]
  exact triangleEdge01_scalar a i

private theorem bottom_edge_incoming_square :
    (coordinateCycleIncl ℤ (bot_le : (⊥ : PreAbstractSimplicialComplex (Fin 3)) ≤ edgeK) 0).comp
      (coordinateBoundaryToCycles (⊥ : PreAbstractSimplicialComplex (Fin 3)) ℤ 0) =
    (coordinateBoundaryToCycles edgeK ℤ 0).comp
      (Matrix.toLin' (chainInclusionMatrix ℤ
        (bot_le : (⊥ : PreAbstractSimplicialComplex (Fin 3)) ≤ edgeK) 1)) := by
  exact coordinateCycleIncl_boundaryToCycles ℤ bot_le 0

private theorem bottom_edge_cycle_square :
    (coordinateCycleIncl ℤ (bot_le : (⊥ : PreAbstractSimplicialComplex (Fin 3)) ≤ edgeK) 0).comp
      (cycleCoordinates (⊥ : PreAbstractSimplicialComplex (Fin 3)) ℤ 0).toLinearMap =
    (cycleCoordinates edgeK ℤ 0).toLinearMap.comp
      (simplicialCycleIncl ℤ
        (bot_le : (⊥ : PreAbstractSimplicialComplex (Fin 3)) ≤ edgeK) 0) := by
  exact cycleCoordinates_naturality ℤ bot_le 0

private theorem zmod1_kernel :
    coordinateCycles triangleK (ZMod 1) 1 =
      LinearMap.ker (Matrix.toLin' (boundaryMatrix triangleK (ZMod 1) 0)) :=
  coordinateCycles_succ triangleK (ZMod 1) 0

private theorem zmod1_boundary_transport :
    (simplicialBoundaries triangleK (ZMod 1) 1).map
      (cycleCoordinates triangleK (ZMod 1) 1).toLinearMap =
      coordinateBoundaries triangleK (ZMod 1) 1 :=
  simplicialBoundaries_map_cycleCoordinates triangleK (ZMod 1) 1

private theorem zmod1_cycle_naturality :
    (coordinateCycleIncl (ZMod 1) edge_le_triangle 0).comp
      (cycleCoordinates edgeK (ZMod 1) 0).toLinearMap =
    (cycleCoordinates triangleK (ZMod 1) 0).toLinearMap.comp
      (simplicialCycleIncl (ZMod 1) edge_le_triangle 0) :=
  cycleCoordinates_naturality (ZMod 1) edge_le_triangle 0

private theorem finiteTotal_boundary_transport
    {A : PreAbstractSimplicialComplex V} [Finite (TotalFace A)]
    (S : Type v) [CommRing S] (n : ℕ) :
    (simplicialBoundaries A S n).map (cycleCoordinates A S n).toLinearMap =
      coordinateBoundaries A S n :=
  simplicialBoundaries_map_cycleCoordinates A S n

private theorem finiteTotal_cycle_naturality
    {A B : PreAbstractSimplicialComplex V}
    [Finite (TotalFace A)] [Finite (TotalFace B)]
    (S : Type v) [CommRing S] (h : A ≤ B) (n : ℕ) :
    (coordinateCycleIncl S h n).comp (cycleCoordinates A S n).toLinearMap =
      (cycleCoordinates B S n).toLinearMap.comp (simplicialCycleIncl S h n) :=
  cycleCoordinates_naturality S h n

private theorem finiteTotal_incoming_square
    {A B : PreAbstractSimplicialComplex V}
    [Finite (TotalFace A)] [Finite (TotalFace B)]
    (S : Type v) [CommRing S] (h : A ≤ B) (n : ℕ) :
    (coordinateCycleIncl S h n).comp (coordinateBoundaryToCycles A S n) =
      (coordinateBoundaryToCycles B S n).comp
        (Matrix.toLin' (chainInclusionMatrix S h (n + 1))) :=
  coordinateCycleIncl_boundaryToCycles S h n

end TheoryFixtures

end TDA.Simplicial.InternalFiniteCycleFixtures
