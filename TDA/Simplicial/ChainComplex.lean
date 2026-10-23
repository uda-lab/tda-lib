import TDA.Simplicial.Boundary
import Mathlib.Data.Fin.Parity
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# The ordered face chain complex

The two ways to delete a pair of ordered vertices give the same face
with opposite coefficients. This proves that the signed boundary squares to zero.
-/

universe u v

namespace TDA.Simplicial

variable {V : Type u} [LinearOrder V]
variable (K : PreAbstractSimplicialComplex V)

private def swapDeletion (n : ℕ) (x : Fin (n + 2) × Fin (n + 1)) :
    Fin (n + 2) × Fin (n + 1) :=
  (x.1.succAbove x.2, x.2.predAbove x.1)

private theorem swapDeletion_involutive (n : ℕ)
    (x : Fin (n + 2) × Fin (n + 1)) :
    swapDeletion n (swapDeletion n x) = x := by
  rcases x with ⟨i, j⟩
  simp [swapDeletion, Fin.succAbove_succAbove_predAbove,
    Fin.predAbove_predAbove_succAbove]

private theorem swapDeletion_ne (n : ℕ)
    (x : Fin (n + 2) × Fin (n + 1)) : swapDeletion n x ≠ x := by
  rcases x with ⟨i, j⟩
  intro h
  have hi : i.succAbove j = i := congrArg Prod.fst h
  exact (Fin.succAbove_ne i j) hi

private theorem deletedFace_twice (n : ℕ) (s : Face K (n + 2))
    (i : Fin (n + 3)) (j : Fin (n + 2)) :
    deletedFace K n (deletedFace K (n + 1) s i) j =
      deletedFace K n (deletedFace K (n + 1) s (i.succAbove j))
        (j.predAbove i) := by
  have hleft :
      (deletedFace K (n + 1) s i).1.orderEmbOfFin
          (deletedFace K (n + 1) s i).2.2 j =
        s.1.orderEmbOfFin s.2.2 (i.succAbove j) := by
    exact enumerationAfterDeletion K (n + 1) s i
      (deletedFace K (n + 1) s i).2.2 j
  have hright :
      (deletedFace K (n + 1) s (i.succAbove j)).1.orderEmbOfFin
          (deletedFace K (n + 1) s (i.succAbove j)).2.2 (j.predAbove i) =
        s.1.orderEmbOfFin s.2.2 i := by
    calc
      _ = s.1.orderEmbOfFin s.2.2
          ((i.succAbove j).succAbove (j.predAbove i)) :=
        enumerationAfterDeletion K (n + 1) s (i.succAbove j)
          (deletedFace K (n + 1) s (i.succAbove j)).2.2 (j.predAbove i)
      _ = _ := by rw [Fin.succAbove_succAbove_predAbove]
  apply Subtype.ext
  change ((deletedFace K (n + 1) s i).1.erase
      ((deletedFace K (n + 1) s i).1.orderEmbOfFin
        (deletedFace K (n + 1) s i).2.2 j)) =
    ((deletedFace K (n + 1) s (i.succAbove j)).1.erase
      ((deletedFace K (n + 1) s (i.succAbove j)).1.orderEmbOfFin
        (deletedFace K (n + 1) s (i.succAbove j)).2.2 (j.predAbove i)))
  rw [hleft, hright]
  change (s.1.erase (s.1.orderEmbOfFin s.2.2 i)).erase
      (s.1.orderEmbOfFin s.2.2 (i.succAbove j)) =
    (s.1.erase (s.1.orderEmbOfFin s.2.2 (i.succAbove j))).erase
      (s.1.orderEmbOfFin s.2.2 i)
  ext x
  simp only [Finset.mem_erase]
  tauto

variable (R : Type v) [Ring R]

private noncomputable def doubleTerm (n : ℕ) (s : Face K (n + 2))
    (x : Fin (n + 3) × Fin (n + 2)) : Chain K R n :=
  Finsupp.single
    (deletedFace K n (deletedFace K (n + 1) s x.1) x.2)
    ((-1 : R) ^ (x.1 : ℕ) * (-1 : R) ^ (x.2 : ℕ))

private theorem doubleTerm_pair (n : ℕ) (s : Face K (n + 2))
    (x : Fin (n + 3) × Fin (n + 2)) :
    doubleTerm K R n s x + doubleTerm K R n s (swapDeletion (n + 1) x) = 0 := by
  rcases x with ⟨i, j⟩
  have hface := deletedFace_twice K n s i j
  dsimp only [doubleTerm, swapDeletion, Prod.fst, Prod.snd]
  rw [← hface]
  rw [← pow_add, ← pow_add, Fin.neg_one_pow_succAbove_add_predAbove]
  simp


private theorem boundary_on_signed_sum (n : ℕ) (s : Face K (n + 2)) :
    boundary K R n
      (∑ i : Fin (n + 3),
        Finsupp.single (deletedFace K (n + 1) s i) ((-1 : R) ^ (i : ℕ))) =
      ∑ x : Fin (n + 3) × Fin (n + 2), doubleTerm K R n s x := by
  rw [Fintype.sum_prod_type]
  simp only [map_sum, boundary_single, Finset.smul_sum, Finsupp.smul_single]
  rfl


private theorem double_sum_zero (n : ℕ) (s : Face K (n + 2)) :
    ∑ x : Fin (n + 3) × Fin (n + 2), doubleTerm K R n s x = 0 := by
  classical
  simpa using (Finset.sum_involution
    (s := (Finset.univ : Finset (Fin (n + 3) × Fin (n + 2))))
    (f := doubleTerm K R n s) (g := fun x _ => swapDeletion (n + 1) x)
    (fun x _ => doubleTerm_pair K R n s x)
    (fun x _ _ => swapDeletion_ne (n + 1) x)
    (fun _ _ => Finset.mem_univ _)
    (fun x _ => swapDeletion_involutive (n + 1) x))

/-- The signed boundary on ordered faces squares to zero. -/
theorem boundary_comp_boundary (n : ℕ) :
    (boundary K R n).comp (boundary K R (n + 1)) = 0 := by
  apply Finsupp.lhom_ext
  intro s a
  change boundary K R n (boundary K R (n + 1) (Finsupp.single s a)) = 0
  rw [boundary_single K R (n + 1) s a, map_smul,
    boundary_on_signed_sum K R n s, double_sum_zero K R n s]
  simp


open CategoryTheory Module

/-- The ordinary unaugmented chain complex on the ordered faces. -/
noncomputable def simplicialChainComplex : ChainComplex (ModuleCat R) ℕ :=
  ChainComplex.of (fun n => ModuleCat.of R (Chain K R n))
    (fun n => ModuleCat.ofHom (boundary K R n)) (by
      intro n
      apply ModuleCat.hom_ext
      exact boundary_comp_boundary K R n)

@[simp]
theorem simplicialChainComplex_X (n : ℕ) :
    (simplicialChainComplex K R).X n = ModuleCat.of R (Chain K R n) :=
  rfl

@[simp]
theorem simplicialChainComplex_d (n : ℕ) :
    (simplicialChainComplex K R).d (n + 1) n =
      ModuleCat.ofHom (boundary K R n) := by
  exact ChainComplex.of_d (fun q => ModuleCat.of R (Chain K R q))
    (fun q => ModuleCat.ofHom (boundary K R q)) n

@[simp]
theorem simplicialChainComplex_d_zero (j : ℕ) :
    (simplicialChainComplex K R).d 0 j = 0 := by
  exact ChainComplex.of_d_ne (fun q => ModuleCat.of R (Chain K R q))
    (fun q => ModuleCat.ofHom (boundary K R q)) (by omega)


section Fixtures

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

private theorem triangleFace_orderEmb :
    triangleFace.1.orderEmbOfFin triangleFace.2.2 =
      (OrderIso.refl (Fin 3)).toOrderEmbedding := by
  symm
  apply Finset.orderEmbOfFin_unique'
  intro i
  fin_cases i <;> simp [triangleFace]

private theorem triangle_boundary :
    boundary triangleK ℤ 1 (Finsupp.single triangleFace 1) =
      Finsupp.single triangleEdge12 1 - Finsupp.single triangleEdge02 1 +
        Finsupp.single triangleEdge01 1 := by
  rw [boundary_single]
  simp only [Fin.sum_univ_succ, deletedFace, triangleFace_orderEmb]
  simp [triangleFace, triangleEdge01, triangleEdge02, triangleEdge12,
    sub_eq_add_neg]
  abel

private theorem triangle_boundary_squared :
    boundary triangleK ℤ 0 (boundary triangleK ℤ 1
      (Finsupp.single triangleFace 1)) = 0 := by
  have h := congrArg
    (fun f : Chain triangleK ℤ 2 →ₗ[ℤ] Chain triangleK ℤ 0 =>
      f (Finsupp.single triangleFace 1))
    (boundary_comp_boundary triangleK ℤ 0)
  simpa using h

private theorem edge01_orderEmb :
    triangleEdge01.1.orderEmbOfFin triangleEdge01.2.2 =
      Fin.succAboveOrderEmb (2 : Fin 3) := by
  have heq : triangleEdge01.1 = ({(2 : Fin 3)}ᶜ : Finset (Fin 3)) := by
    ext x
    fin_cases x <;> decide
  simp [heq]

private theorem edge01_boundary :
    boundary triangleK ℤ 0 (Finsupp.single triangleEdge01 1) =
      Finsupp.single (triangleVertex 1) 1 -
        Finsupp.single (triangleVertex 0) 1 := by
  rw [boundary_single]
  simp [deletedFace, triangleVertex, edge01_orderEmb,
    Fin.succAboveOrderEmb, Fin.succAbove]
  simp [triangleEdge01, Finset.erase_insert_of_ne, sub_eq_add_neg]

private theorem edge01_boundary_nonzero :
    boundary triangleK ℤ 0 (Finsupp.single triangleEdge01 1) ≠ 0 := by
  intro h
  have hc := congrArg (fun c : Chain triangleK ℤ 0 => c (triangleVertex 1)) h
  rw [edge01_boundary] at hc
  simp [triangleVertex] at hc

private theorem packaged_edge01_nonzero :
    (simplicialChainComplex triangleK ℤ).d 1 0 ≠ 0 := by
  intro h
  have hlin : boundary triangleK ℤ 0 = 0 := by
    exact ModuleCat.hom_ext_iff.mp (by simpa using h)
  exact edge01_boundary_nonzero (by rw [hlin]; simp)

private abbrev tetraK : PreAbstractSimplicialComplex (Fin 4) := ⊤

private def tetrahedron : Face tetraK 3 :=
  ⟨{0, 1, 2, 3}, by change ({0, 1, 2, 3} : Finset (Fin 4)).Nonempty; decide,
    by decide⟩

private def triangle012 : Face tetraK 2 :=
  ⟨{0, 1, 2}, by change ({0, 1, 2} : Finset (Fin 4)).Nonempty; decide, by decide⟩
private def triangle013 : Face tetraK 2 :=
  ⟨{0, 1, 3}, by change ({0, 1, 3} : Finset (Fin 4)).Nonempty; decide, by decide⟩
private def triangle023 : Face tetraK 2 :=
  ⟨{0, 2, 3}, by change ({0, 2, 3} : Finset (Fin 4)).Nonempty; decide, by decide⟩
private def triangle123 : Face tetraK 2 :=
  ⟨{1, 2, 3}, by change ({1, 2, 3} : Finset (Fin 4)).Nonempty; decide, by decide⟩

private theorem tetrahedron_orderEmb :
    tetrahedron.1.orderEmbOfFin tetrahedron.2.2 =
      (OrderIso.refl (Fin 4)).toOrderEmbedding := by
  symm
  apply Finset.orderEmbOfFin_unique'
  intro i
  fin_cases i <;> simp [tetrahedron]

private theorem tetrahedron_boundary :
    boundary tetraK ℤ 2 (Finsupp.single tetrahedron 1) =
      Finsupp.single triangle123 1 - Finsupp.single triangle023 1 +
        Finsupp.single triangle013 1 - Finsupp.single triangle012 1 := by
  rw [boundary_single]
  simp only [Fin.sum_univ_succ, deletedFace, tetrahedron_orderEmb]
  simp [tetrahedron, triangle012, triangle013, triangle023, triangle123,
    sub_eq_add_neg]
  abel

private theorem tetrahedron_boundary_squared :
    boundary tetraK ℤ 1 (boundary tetraK ℤ 2 (Finsupp.single tetrahedron 1)) = 0 := by
  have h := congrArg
    (fun f : Chain tetraK ℤ 3 →ₗ[ℤ] Chain tetraK ℤ 1 =>
      f (Finsupp.single tetrahedron 1))
    (boundary_comp_boundary tetraK ℤ 1)
  simpa using h

private theorem bottom_complex_boundary_zero (n : ℕ) :
    (simplicialChainComplex (⊥ : PreAbstractSimplicialComplex (Fin 3)) ℤ).d
      (n + 1) n = 0 := by
  rw [simplicialChainComplex_d]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  exact emptyChain_eq_zero ℤ n
    (boundary (⊥ : PreAbstractSimplicialComplex (Fin 3)) ℤ n c)

private theorem singleton_complex_boundary_zero (x : Fin 3) (n : ℕ) :
    (simplicialChainComplex (Filtration.singletonFace x) ℤ).d
      (n + 1) n = 0 := by
  rw [simplicialChainComplex_d]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  rw [singletonHigherChain_eq_zero x ℤ n c]
  simp

private theorem charTwo_triangle_square :
    (boundary triangleK (ZMod 2) 0).comp (boundary triangleK (ZMod 2) 1) = 0 :=
  boundary_comp_boundary triangleK (ZMod 2) 0

private theorem matrixRing_square (n : ℕ) :
    (boundary triangleK (Matrix (Fin 2) (Fin 2) ℤ) n).comp
      (boundary triangleK (Matrix (Fin 2) (Fin 2) ℤ) (n + 1)) = 0 :=
  boundary_comp_boundary triangleK (Matrix (Fin 2) (Fin 2) ℤ) n

end Fixtures


end TDA.Simplicial
