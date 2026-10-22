import TDA.Simplicial.Inclusion
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! # Degreewise coordinates of simplicial chains

Rows of `boundaryMatrix K R n` are degree-`n` faces and columns are
degree-`n+1` faces. The matrix represents the existing signed `boundary`.
`chainInclusionMatrix` similarly represents the existing same-ambient `chainIncl`.
These noncomputable theory coordinates do not define a master matrix.
-/

universe u v

open scoped BigOperators Matrix
open Module

namespace TDA.Simplicial

variable {V : Type u} [LinearOrder V]

noncomputable def faceFintypeOfTotalFinite
    (K : PreAbstractSimplicialComplex V) [Finite (TotalFace K)]
    (n : ℕ) : Fintype (Face K n) :=
  Fintype.ofFinite _

noncomputable def chainCoordinates
    (K : PreAbstractSimplicialComplex V) (R : Type v) [CommRing R]
    (n : ℕ) [Finite (Face K n)] :
    Chain K R n ≃ₗ[R] (Face K n → R) :=
  (faceBasis K R n).equivFun

noncomputable def boundaryMatrix
    (K : PreAbstractSimplicialComplex V) (R : Type v) [CommRing R]
    (n : ℕ) [Fintype (Face K (n + 1))]
    [DecidableEq (Face K (n + 1))] [Finite (Face K n)] :
    Matrix (Face K n) (Face K (n + 1)) R :=
  LinearMap.toMatrix (faceBasis K R (n + 1)) (faceBasis K R n)
    (boundary K R n)

noncomputable def chainInclusionMatrix
    (R : Type v) [CommRing R]
    {K L : PreAbstractSimplicialComplex V} (h : K ≤ L)
    (n : ℕ) [Fintype (Face K n)] [DecidableEq (Face K n)]
    [Finite (Face L n)] : Matrix (Face L n) (Face K n) R :=
  LinearMap.toMatrix (faceBasis K R n) (faceBasis L R n)
    (chainIncl R h n)

variable (K : PreAbstractSimplicialComplex V) (R : Type v) [CommRing R]

theorem chainCoordinates_apply (n : ℕ) [Finite (Face K n)]
    (c : Chain K R n) (s : Face K n) :
    chainCoordinates K R n c s = c s := by
  rfl

theorem boundaryMatrix_apply (n : ℕ)
    [Fintype (Face K (n + 1))] [DecidableEq (Face K (n + 1))]
    [Finite (Face K n)] (τ : Face K n) (σ : Face K (n + 1)) :
    boundaryMatrix K R n τ σ =
      ∑ i : Fin (n + 2),
        if deletedFace K n σ i = τ then (-1 : R) ^ (i : ℕ) else 0 := by
  rw [boundaryMatrix, LinearMap.toMatrix_apply]
  simp only [faceBasis, Finsupp.coe_basisSingleOne, boundary_single, one_smul]
  simp [Finsupp.basisSingleOne_repr, Finsupp.single_apply]

private theorem deletedFace_injective (n : ℕ) (σ : Face K (n + 1)) :
    Function.Injective (deletedFace K n σ) := by
  intro i j hij
  by_contra hne
  let vi := σ.1.orderEmbOfFin σ.2.2 i
  let vj := σ.1.orderEmbOfFin σ.2.2 j
  have hvne : vi ≠ vj := fun h => hne ((σ.1.orderEmbOfFin σ.2.2).injective h)
  have hmem : vi ∈ (deletedFace K n σ j).1 := by
    change vi ∈ σ.1.erase vj
    exact Finset.mem_erase.mpr ⟨hvne, Finset.orderEmbOfFin_mem σ.1 σ.2.2 i⟩
  rw [← hij] at hmem
  have : vi ∈ σ.1.erase vi := hmem
  simpa using this

theorem boundaryMatrix_deletedFace (n : ℕ)
    [Fintype (Face K (n + 1))] [DecidableEq (Face K (n + 1))]
    [Finite (Face K n)] (σ : Face K (n + 1)) (i : Fin (n + 2)) :
    boundaryMatrix K R n (deletedFace K n σ i) σ =
      (-1 : R) ^ (i : ℕ) := by
  rw [boundaryMatrix_apply]
  classical
  simp only [(deletedFace_injective K n σ).eq_iff]
  simp

theorem boundaryMatrix_eq_zero_of_not_deletedFace (n : ℕ)
    [Fintype (Face K (n + 1))] [DecidableEq (Face K (n + 1))]
    [Finite (Face K n)] (τ : Face K n) (σ : Face K (n + 1))
    (hτ : ∀ i : Fin (n + 2), deletedFace K n σ i ≠ τ) :
    boundaryMatrix K R n τ σ = 0 := by
  rw [boundaryMatrix_apply]
  simp [hτ]

theorem boundaryMatrix_mulVec (n : ℕ)
    [Fintype (Face K (n + 1))] [DecidableEq (Face K (n + 1))]
    [Finite (Face K n)] (c : Chain K R (n + 1)) :
    boundaryMatrix K R n *ᵥ chainCoordinates K R (n + 1) c =
      chainCoordinates K R n (boundary K R n c) := by
  exact LinearMap.toMatrix_mulVec_repr (faceBasis K R (n + 1))
    (faceBasis K R n) (boundary K R n) c

theorem boundaryMatrix_toLin (n : ℕ)
    [Fintype (Face K (n + 1))] [DecidableEq (Face K (n + 1))]
    [Finite (Face K n)] :
    Matrix.toLin (faceBasis K R (n + 1)) (faceBasis K R n)
        (boundaryMatrix K R n) = boundary K R n := by
  exact Matrix.toLin_toMatrix (faceBasis K R (n + 1))
    (faceBasis K R n) (boundary K R n)

theorem boundaryMatrix_mul_boundaryMatrix (n : ℕ)
    [Fintype (Face K (n + 2))] [DecidableEq (Face K (n + 2))]
    [Fintype (Face K (n + 1))] [DecidableEq (Face K (n + 1))]
    [Finite (Face K n)] :
    boundaryMatrix K R n * boundaryMatrix K R (n + 1) = 0 := by
  have hc := LinearMap.toMatrix_comp (faceBasis K R (n + 2))
    (faceBasis K R (n + 1)) (faceBasis K R n)
    (boundary K R n) (boundary K R (n + 1))
  rw [boundary_comp_boundary K R n, map_zero] at hc
  simpa only [boundaryMatrix, Nat.add_assoc] using hc.symm

theorem simplicialChainComplex_d_zero_toMatrix (j : ℕ)
    [Fintype (Face K 0)] [DecidableEq (Face K 0)]
    [Finite (Face K j)] :
    LinearMap.toMatrix (faceBasis K R 0) (faceBasis K R j)
      ((simplicialChainComplex K R).d 0 j).hom = 0 := by
  rw [simplicialChainComplex_d_zero]
  rw [ModuleCat.hom_zero]
  exact map_zero (LinearMap.toMatrix (faceBasis K R 0) (faceBasis K R j))

section Inclusion

variable {K L : PreAbstractSimplicialComplex V}

theorem chainInclusionMatrix_apply (R : Type v) [CommRing R] (h : K ≤ L) (n : ℕ)
    [Fintype (Face K n)] [DecidableEq (Face K n)] [Finite (Face L n)]
    (τ : Face L n) (σ : Face K n) :
    chainInclusionMatrix R h n τ σ =
      if faceIncl h n σ = τ then 1 else 0 := by
  rw [chainInclusionMatrix, LinearMap.toMatrix_apply]
  simp only [faceBasis, Finsupp.coe_basisSingleOne, chainIncl_single]
  simp [Finsupp.basisSingleOne_repr, Finsupp.single_apply]

theorem chainInclusionMatrix_mulVec (R : Type v) [CommRing R] (h : K ≤ L) (n : ℕ)
    [Fintype (Face K n)] [DecidableEq (Face K n)] [Finite (Face L n)]
    (c : Chain K R n) :
    chainInclusionMatrix R h n *ᵥ chainCoordinates K R n c =
      chainCoordinates L R n (chainIncl R h n c) := by
  exact LinearMap.toMatrix_mulVec_repr (faceBasis K R n)
    (faceBasis L R n) (chainIncl R h n) c

theorem boundaryMatrix_chainInclusionMatrix (R : Type v) [CommRing R]
    (h : K ≤ L) (n : ℕ)
    [Fintype (Face K (n + 1))] [DecidableEq (Face K (n + 1))]
    [Fintype (Face K n)] [DecidableEq (Face K n)]
    [Fintype (Face L (n + 1))] [DecidableEq (Face L (n + 1))]
    [Finite (Face L n)] :
    boundaryMatrix L R n * chainInclusionMatrix R h (n + 1) =
      chainInclusionMatrix R h n * boundaryMatrix K R n := by
  have hleft := LinearMap.toMatrix_comp (faceBasis K R (n + 1))
    (faceBasis L R (n + 1)) (faceBasis L R n)
    (boundary L R n) (chainIncl R h (n + 1))
  have hright := LinearMap.toMatrix_comp (faceBasis K R (n + 1))
    (faceBasis K R n) (faceBasis L R n)
    (chainIncl R h n) (boundary K R n)
  rw [boundary_chainIncl R h n] at hleft
  exact (show boundaryMatrix L R n * chainInclusionMatrix R h (n + 1) =
    LinearMap.toMatrix (faceBasis K R (n + 1)) (faceBasis L R n)
      ((chainIncl R h n).comp (boundary K R n)) from hleft.symm).trans
    (by simpa only [boundaryMatrix, chainInclusionMatrix] using hright)

end Inclusion


-- Trust inventory for the definitions and private proof helper in this module.
#print axioms faceFintypeOfTotalFinite
#print axioms chainCoordinates
#print axioms boundaryMatrix
#print axioms chainInclusionMatrix
#print axioms deletedFace_injective
#print axioms boundaryMatrix._proof_1
#print axioms boundaryMatrix._proof_2
#print axioms boundaryMatrix.congr_simp
#print axioms boundaryMatrix.eq_1
#print axioms chainInclusionMatrix._proof_1
#print axioms chainInclusionMatrix.congr_simp
#print axioms chainInclusionMatrix.eq_1

end TDA.Simplicial
