import TDA.Simplicial.ChainComplex

/-!
# Naturality of actual simplicial chain inclusions

For subcomplexes in one ordered ambient vertex type, the actual signed deletion
boundary commutes with the canonical face and chain inclusions. These maps form
chain maps between the ordinary unaugmented complexes.
-/

universe u v

namespace TDA.Simplicial

open CategoryTheory Module

variable {V : Type u} [LinearOrder V]
variable {K L M : PreAbstractSimplicialComplex V}

/-- Inclusion preserves the face obtained by deleting an ordered vertex. -/
theorem faceIncl_deletedFace (h : K ≤ L) (n : ℕ)
    (s : Face K (n + 1)) (i : Fin (n + 2)) :
    faceIncl h n (deletedFace K n s i) =
      deletedFace L n (faceIncl h (n + 1) s) i := by
  apply Subtype.ext
  rfl

variable (R : Type v) [Ring R]

omit [LinearOrder V] in
/-- Inclusion transports a singleton chain to the corresponding face. -/
theorem chainIncl_single (h : K ≤ L) (n : ℕ)
    (s : Face K n) (a : R) :
    chainIncl R h n (Finsupp.single s a) =
      Finsupp.single (faceIncl h n s) a := by
  simp [chainIncl]

/-- The actual signed deletion boundary is natural for every same-ambient
subcomplex inclusion. The proof checks the arbitrary-coefficient singleton
chains and then uses linear extensionality; the coefficient stays a left
scalar throughout, so no commutativity of `R` is needed. -/
theorem boundary_chainIncl (h : K ≤ L) (n : ℕ) :
    (boundary L R n).comp (chainIncl R h (n + 1)) =
      (chainIncl R h n).comp (boundary K R n) := by
  apply Finsupp.lhom_ext
  intro s a
  change boundary L R n
      (chainIncl R h (n + 1) (Finsupp.single s a)) =
    chainIncl R h n (boundary K R n (Finsupp.single s a))
  rw [chainIncl_single, boundary_single, boundary_single, map_smul, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [chainIncl_single, faceIncl_deletedFace]

/-- The chain map induced by inclusion of actual faces. -/
noncomputable def simplicialChainIncl (h : K ≤ L) :
    simplicialChainComplex K R ⟶ simplicialChainComplex L R :=
  ChainComplex.ofHom (fun n => ModuleCat.ofHom (chainIncl R h n)) (by
    intro n
    apply ModuleCat.hom_ext
    simp only [simplicialChainComplex_d]
    exact boundary_chainIncl R h n)

/-- The degree-`n` component is the existing linear face inclusion. -/
@[simp]
theorem simplicialChainIncl_f (h : K ≤ L) (n : ℕ) :
    (simplicialChainIncl R h).f n = ModuleCat.ofHom (chainIncl R h n) := rfl

/-- Inclusion along equality is the identity chain map. -/
theorem simplicialChainIncl_id (K : PreAbstractSimplicialComplex V) :
    simplicialChainIncl R (le_refl K) = 𝟙 (simplicialChainComplex K R) := by
  apply HomologicalComplex.hom_ext
  intro n
  simp [simplicialChainIncl_f, chainIncl_id]

/-- Composable inclusions induce composable chain maps. -/
theorem simplicialChainIncl_comp (h : K ≤ L) (g : L ≤ M) :
    simplicialChainIncl R (h.trans g) =
      simplicialChainIncl R h ≫ simplicialChainIncl R g := by
  apply HomologicalComplex.hom_ext
  intro n
  simp only [simplicialChainIncl_f, HomologicalComplex.comp_f]
  apply ModuleCat.hom_ext
  change chainIncl R (h.trans g) n =
    (chainIncl R g n).comp (chainIncl R h n)
  exact chainIncl_comp R h g n

end TDA.Simplicial
