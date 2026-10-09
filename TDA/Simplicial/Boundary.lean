import TDA.Simplicial.Bridge
import Mathlib.Data.Finset.Sort
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Ordered simplicial boundary on actual faces

Faces are oriented by the fixed ambient linear order. Deleting an enumerated vertex
produces an actual face, and the signed deletion sum extends linearly to chains.
-/

universe u v

open scoped BigOperators

namespace TDA.Simplicial

variable {V : Type u} [LinearOrder V]
variable (K : PreAbstractSimplicialComplex V)

/-- Delete the vertex at position `i` from an actual face. -/
def deletedFace (n : ℕ) (s : Face K (n + 1)) (i : Fin (n + 2)) : Face K n := by
  have hv : s.1.orderEmbOfFin s.2.2 i ∈ s.1 :=
    Finset.orderEmbOfFin_mem s.1 s.2.2 i
  have hcard : (s.1.erase (s.1.orderEmbOfFin s.2.2 i)).card = n + 1 := by
    rw [Finset.card_erase_of_mem hv, s.2.2]
    omega
  have hnonempty : (s.1.erase (s.1.orderEmbOfFin s.2.2 i)).Nonempty :=
    Finset.card_pos.mp (by rw [hcard]; omega)
  have hmem : s.1.erase (s.1.orderEmbOfFin s.2.2 i) ∈ K :=
    (K.isRelLowerSet_faces s.2.1).2 (Finset.erase_subset _ _) hnonempty
  exact ⟨s.1.erase (s.1.orderEmbOfFin s.2.2 i), hmem, hcard⟩

/-- The increasing enumeration of the erased face is the original enumeration with
the deleted position skipped. -/
theorem enumerationAfterDeletion (n : ℕ) (s : Face K (n + 1)) (i : Fin (n + 2))
    (hc : (s.1.erase (s.1.orderEmbOfFin s.2.2 i)).card = n + 1)
    (j : Fin (n + 1)) :
    (s.1.erase (s.1.orderEmbOfFin s.2.2 i)).orderEmbOfFin hc j =
      s.1.orderEmbOfFin s.2.2 (i.succAbove j) := by
  let t := s.1.erase (s.1.orderEmbOfFin s.2.2 i)
  have hmem : ∀ j : Fin (n + 1),
      s.1.orderEmbOfFin s.2.2 (i.succAbove j) ∈ t := by
    intro j
    refine Finset.mem_erase.mpr ⟨?_, Finset.orderEmbOfFin_mem s.1 s.2.2 (i.succAbove j)⟩
    intro heq
    apply Fin.succAbove_ne i j
    exact (s.1.orderEmbOfFin s.2.2).injective heq
  have hmono : StrictMono (fun j : Fin (n + 1) =>
      s.1.orderEmbOfFin s.2.2 (i.succAbove j)) :=
    (s.1.orderEmbOfFin s.2.2).strictMono.comp (Fin.strictMono_succAbove i)
  have hunique : (fun j : Fin (n + 1) =>
      s.1.orderEmbOfFin s.2.2 (i.succAbove j)) = t.orderEmbOfFin hc :=
    Finset.orderEmbOfFin_unique hc hmem hmono
  simpa only [t] using (congrFun hunique j).symm

private theorem enumerationAfterDeletion_deletedFace (n : ℕ) (s : Face K (n + 1))
    (i : Fin (n + 2)) (j : Fin (n + 1)) :
    (deletedFace K n s i).1.orderEmbOfFin (deletedFace K n s i).2.2 j =
      s.1.orderEmbOfFin s.2.2 (i.succAbove j) := by
  exact enumerationAfterDeletion K n s i (deletedFace K n s i).2.2 j

variable (R : Type v) [Ring R]

/-- The signed boundary from degree `n+1` to degree `n`. -/
noncomputable def boundary (n : ℕ) :
    Chain K R (n + 1) →ₗ[R] Chain K R n :=
  Finsupp.linearCombination R (fun s : Face K (n + 1) =>
    ∑ i : Fin (n + 2),
      Finsupp.single (deletedFace K n s i) ((-1 : R) ^ (i : ℕ)))

/-- Boundary on a basis chain is its signed ordered deletion sum. -/
theorem boundary_single (n : ℕ) (s : Face K (n + 1)) (a : R) :
    boundary K R n (Finsupp.single s a) =
      a • (∑ i : Fin (n + 2),
        Finsupp.single (deletedFace K n s i) ((-1 : R) ^ (i : ℕ))) := by
  simp [boundary]

private abbrev triangleK : PreAbstractSimplicialComplex (Fin 3) := ⊤

private def triangleVertex (i : Fin 3) : Face triangleK 0 :=
  ⟨{i}, by change ({i} : Finset (Fin 3)).Nonempty; simp, by simp⟩

private def triangleEdge01 : Face triangleK 1 :=
  ⟨{0, 1}, by change ({0, 1} : Finset (Fin 3)).Nonempty; decide, by decide⟩

private def triangleEdge02 : Face triangleK 1 :=
  ⟨{0, 2}, by change ({0, 2} : Finset (Fin 3)).Nonempty; decide, by decide⟩

private def triangleEdge12 : Face triangleK 1 :=
  ⟨{1, 2}, by change ({1, 2} : Finset (Fin 3)).Nonempty; decide, by decide⟩

private def triangleFace : Face triangleK 2 :=
  ⟨{0, 1, 2}, by change ({0, 1, 2} : Finset (Fin 3)).Nonempty; decide, by decide⟩

private theorem triangleEdge01_as_compl :
    triangleEdge01.1 = ({(2 : Fin 3)}ᶜ : Finset (Fin 3)) := by
  ext x
  fin_cases x <;> decide

private theorem triangleEdge02_as_compl :
    triangleEdge02.1 = ({(1 : Fin 3)}ᶜ : Finset (Fin 3)) := by
  ext x
  fin_cases x <;> decide

private theorem triangleEdge12_as_compl :
    triangleEdge12.1 = ({(0 : Fin 3)}ᶜ : Finset (Fin 3)) := by
  ext x
  fin_cases x <;> decide

private theorem triangleEdge01_orderEmb :
    triangleEdge01.1.orderEmbOfFin triangleEdge01.2.2 =
      Fin.succAboveOrderEmb (2 : Fin 3) := by
  simp [triangleEdge01_as_compl]

private theorem triangleEdge02_orderEmb :
    triangleEdge02.1.orderEmbOfFin triangleEdge02.2.2 =
      Fin.succAboveOrderEmb (1 : Fin 3) := by
  simp [triangleEdge02_as_compl]

private theorem triangleEdge12_orderEmb :
    triangleEdge12.1.orderEmbOfFin triangleEdge12.2.2 =
      Fin.succAboveOrderEmb (0 : Fin 3) := by
  simp [triangleEdge12_as_compl]

private theorem triangleFace_orderEmb :
    triangleFace.1.orderEmbOfFin triangleFace.2.2 = (OrderIso.refl (Fin 3)).toOrderEmbedding := by
  symm
  apply Finset.orderEmbOfFin_unique'
  intro i
  fin_cases i <;> simp [triangleFace]

private theorem boundary_triangleEdge01 :
    boundary triangleK ℤ 0 (Finsupp.single triangleEdge01 1) =
      Finsupp.single (triangleVertex 1) 1 - Finsupp.single (triangleVertex 0) 1 := by
  rw [boundary_single]
  simp [deletedFace, triangleVertex,
    triangleEdge01_orderEmb, Fin.succAboveOrderEmb, Fin.succAbove]
  simp [triangleEdge01, Finset.erase_insert_of_ne, sub_eq_add_neg]

private theorem boundary_triangleEdge02 :
    boundary triangleK ℤ 0 (Finsupp.single triangleEdge02 1) =
      Finsupp.single (triangleVertex 2) 1 - Finsupp.single (triangleVertex 0) 1 := by
  rw [boundary_single]
  simp [deletedFace, triangleVertex,
    triangleEdge02_orderEmb, Fin.succAboveOrderEmb, Fin.succAbove]
  simp [triangleEdge02, Finset.erase_insert_of_ne, sub_eq_add_neg]

private theorem boundary_triangleEdge12 :
    boundary triangleK ℤ 0 (Finsupp.single triangleEdge12 1) =
      Finsupp.single (triangleVertex 2) 1 - Finsupp.single (triangleVertex 1) 1 := by
  rw [boundary_single]
  simp [deletedFace, triangleVertex,
    triangleEdge12_orderEmb, Fin.succAboveOrderEmb]
  simp [triangleEdge12, Finset.erase_insert_of_ne, sub_eq_add_neg]

private theorem boundary_triangleFace :
    boundary triangleK ℤ 1 (Finsupp.single triangleFace 1) =
      Finsupp.single triangleEdge12 1 - Finsupp.single triangleEdge02 1 +
        Finsupp.single triangleEdge01 1 := by
  rw [boundary_single]
  simp only [Fin.sum_univ_succ, deletedFace, triangleFace_orderEmb]
  simp [triangleFace, triangleEdge01, triangleEdge02, triangleEdge12,
    sub_eq_add_neg]
  abel

private theorem boundary_triangleEdge01_vertex1 :
    (boundary triangleK ℤ 0 (Finsupp.single triangleEdge01 1)) (triangleVertex 1) = 1 := by
  rw [boundary_triangleEdge01]
  simp [triangleVertex]

private theorem boundary_triangleEdge01_vertex0 :
    (boundary triangleK ℤ 0 (Finsupp.single triangleEdge01 1)) (triangleVertex 0) = -1 := by
  rw [boundary_triangleEdge01]
  simp [triangleVertex]

private theorem boundary_triangleEdge01_ne_zero :
    boundary triangleK ℤ 0 (Finsupp.single triangleEdge01 1) ≠ 0 := by
  intro h
  have hcoeff := congrArg (fun c : Chain triangleK ℤ 0 => c (triangleVertex 1)) h
  rw [boundary_triangleEdge01_vertex1] at hcoeff
  norm_num at hcoeff

private theorem boundary_triangle_squared :
    boundary triangleK ℤ 0
      (boundary triangleK ℤ 1 (Finsupp.single triangleFace 1)) = 0 := by
  rw [boundary_triangleFace]
  simp only [map_sub, map_add]
  rw [boundary_triangleEdge12, boundary_triangleEdge02, boundary_triangleEdge01]
  simp [triangleVertex]

private theorem boundary_bottom_zero (n : ℕ) :
    boundary (⊥ : PreAbstractSimplicialComplex (Fin 3)) ℤ n = 0 := by
  apply LinearMap.ext
  intro c
  exact emptyChain_eq_zero ℤ n (boundary (⊥ : PreAbstractSimplicialComplex (Fin 3)) ℤ n c)

private theorem boundary_singleton_zero (x : Fin 3) (n : ℕ) :
    boundary (Filtration.singletonFace x) ℤ n = 0 := by
  apply LinearMap.ext
  intro c
  rw [singletonHigherChain_eq_zero x ℤ n c]
  simp

end TDA.Simplicial
