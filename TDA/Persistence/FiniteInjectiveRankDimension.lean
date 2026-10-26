import TDA.Persistence.FiniteInjectivePresentation
import TDA.Persistence.PrincipalDownsetRankDimension
import TDA.Persistence.FiniteRankProjectiveHomExact
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Mathlib.Algebra.Category.ModuleCat.Biproducts

/-!
# Hom dimension of finite injective presentations

The finite coordinate embedding of a pointwise finite-dimensional persistence
module places it inside a finite biproduct of principal-downset injectives.
The existing Hom functor preserves this biproduct, Ext dimension bounds are
closed under finite biproducts, and ordinary injectivity makes the mapped
embedding split. This transfers the principal-downset bound to every ordinary
injective pointwise finite-dimensional module, as in BOOS,
arXiv:2208.00300v3, Proposition 5.14. The proof uses the established finite
coordinate embedding and its retract for ordinary injectives; it proves the
uniform dimension inequality without a finite direct-sum classification of
injective modules.
-/

set_option autoImplicit false

universe u v w

namespace TDA.Persistence.FiniteInjectiveRankDimension

open CategoryTheory CategoryTheory.Limits
open FiniteInjectivePresentation
open PrincipalDownsetRankResolution
open TDA.Persistence.FiniteRankProjectiveEndAlgebra
open scoped Classical

variable {k : Type u} [Field k] {S : Type} [Lattice S] [Finite S]
  [OrderBot S] [OrderTop S]

noncomputable section

local instance : Fintype S := Fintype.ofFinite S

private instance : HasFiniteBiproducts (PModule.{u,0,u} k S) :=
  HasFiniteBiproducts.of_hasFiniteProducts

private abbrev H := FiniteRankProjectiveHomExact.homFunctor (k := k) (S := S)

/-- Ext dimension bounds pass to the actual finite categorical biproduct. The
proof uses Mathlib's additive Ext equivalence on the biproduct's bilimit bicone,
including the empty-family case. -/
theorem hasProjectiveDimensionLE_biproduct
    {C : Type u} [Category.{v} C] [Abelian C] [HasFiniteBiproducts C]
    {I : Type w} [Fintype I]
    (F : I → C) (d : ℕ)
    (hF : ∀ i, HasProjectiveDimensionLE (F i) d) :
    HasProjectiveDimensionLE (⨁ F) d := by
  letI := HasExt.standard C
  apply (hasProjectiveDimensionLT_iff (⨁ F) (d + 1)).2
  intro n hn Y e
  apply (Abelian.Ext.biproductAddEquiv (biproduct.isBilimit F) Y n).injective
  ext i
  letI : HasProjectiveDimensionLT (F i) (d + 1) := hF i
  have hzero := Abelian.Ext.eq_zero_of_hasProjectiveDimensionLT
    ((Abelian.Ext.mk₀ (biproduct.ι F i)).comp e (zero_add n)) (d + 1) (by omega)
  change (Abelian.Ext.mk₀ (biproduct.ι F i)).comp e (zero_add n) =
    (Abelian.Ext.mk₀ (biproduct.ι F i)).comp 0 (zero_add n)
  rw [hzero]
  simp

/-- The actual Hom functor sends a finite categorical biproduct to the finite
biproduct of the Hom modules. -/
def homBiproductIso {I : Type} [Fintype I]
    (F : I → PModule.{u,0,u} k S) :
    (H (k := k) (S := S)).obj (⨁ F) ≅
      ⨁ fun i => (H (k := k) (S := S)).obj (F i) := by
  let e := FiniteRankProjectiveHomProjective.homBiproductEquivPi
    (k := k) (S := S) F
  exact e.toModuleIso ≪≫
    (ModuleCat.biproductIsoPi (fun i => (H (k := k) (S := S)).obj (F i))).symm

/-- The finite Hom biproduct comparison has the expected coordinate law: its
projection at `i` is postcomposition with the categorical projection. -/
@[simp] theorem homBiproductIso_hom_π_apply {I : Type} [Fintype I]
    (F : I → PModule.{u,0,u} k S) (f : HookSum (k := k) (S := S) ⟶ ⨁ F)
    (i : I) :
    (((((homBiproductIso (k := k) (S := S) F).hom) ≫
      biproduct.π (fun i => (H (k := k) (S := S)).obj (F i)) i).hom) f) =
        f ≫ biproduct.π F i := by
  simp [homBiproductIso, Category.assoc,
    FiniteRankProjectiveHomProjective.homBiproductEquivPi_apply]

/-- The actual finite injective-presentation target has the indicated Hom
projective-dimension bound whenever every principal summand does. -/
theorem presentation_hasProjectiveDimensionLE
    (M : PModule.{u,0,u} k S) [∀ p, FiniteDimensional k (M.obj p)] (d : ℕ)
    (hcard : ∀ p : S, complementCard (S := S) p - 1 ≤ d) :
    HasProjectiveDimensionLE ((H (k := k) (S := S)).obj (module M)) d := by
  letI : Fintype (FiniteInjectivePresentation.Index (k := k) (P := S) M) :=
    FiniteInjectivePresentation.indexFintype (k := k) (P := S) M
  have hsum : HasProjectiveDimensionLE
      (⨁ fun i : FiniteInjectivePresentation.Index (k := k) (P := S) M =>
        (H (k := k) (S := S)).obj (FiniteInjectivePresentation.family M i)) d := by
    apply hasProjectiveDimensionLE_biproduct
      (C := ModuleCat (FiniteRankProjectiveHomProjective.HomScalars (k := k) (S := S)))
      (I := FiniteInjectivePresentation.Index (k := k) (P := S) M)
      (F := fun i : FiniteInjectivePresentation.Index (k := k) (P := S) M =>
        (H (k := k) (S := S)).obj (FiniteInjectivePresentation.family M i)) d
    intro i
    have hprincipal := PrincipalDownsetRankDimension.hasProjectiveDimensionLE
      (k := k) (S := S) i.1
    letI : HasProjectiveDimensionLT
        ((H (k := k) (S := S)).obj (PrincipalDownsetInjective.module i.1))
        (complementCard i.1 - 1 + 1) := hprincipal
    exact hasProjectiveDimensionLT_of_ge
      ((H (k := k) (S := S)).obj (PrincipalDownsetInjective.module i.1))
      (complementCard (S := S) i.1 - 1 + 1) (d + 1)
      (Nat.succ_le_succ (hcard i.1))
  let e := homBiproductIso (k := k) (S := S) (FiniteInjectivePresentation.family M)
  letI : HasProjectiveDimensionLT
      (⨁ fun i : FiniteInjectivePresentation.Index (k := k) (P := S) M =>
        (H (k := k) (S := S)).obj (FiniteInjectivePresentation.family M i)) (d + 1) := hsum
  exact hasProjectiveDimensionLT_of_iso e.symm (d + 1)

/-- Applying Hom to the actual coordinate embedding and retraction gives a
retract of the Hom module of the finite injective-presentation target. -/
def mapped_embedding_retraction_retract
    (M : PModule.{u,0,u} k S) [∀ p, FiniteDimensional k (M.obj p)]
    [Injective M] :
    Retract ((H (k := k) (S := S)).obj M)
      ((H (k := k) (S := S)).obj (FiniteInjectivePresentation.module M)) := by
  exact (show Retract M (module M) from
    ⟨embedding M, retraction M, embedding_retraction M⟩).map (H (k := k) (S := S))

/-- The mapped coordinate embedding and retraction split by the functorial
image of the presentation's splitting law. -/
@[reassoc (attr := simp)] theorem hom_embedding_retraction
    (M : PModule.{u,0,u} k S) [∀ p, FiniteDimensional k (M.obj p)]
    [Injective M] :
    (H (k := k) (S := S)).map (embedding M) ≫
      (H (k := k) (S := S)).map (retraction M) =
        𝟙 ((H (k := k) (S := S)).obj M) :=
  (mapped_embedding_retraction_retract (k := k) (S := S) M).retract

/-- Every ordinary injective pointwise finite-dimensional module satisfies the
same combinatorial Hom dimension bound as its principal-downset summands. -/
theorem hasProjectiveDimensionLE
    (M : PModule.{u,0,u} k S) [∀ p, FiniteDimensional k (M.obj p)]
    [Injective M] (d : ℕ) (hcard : ∀ p : S, complementCard (S := S) p - 1 ≤ d) :
    HasProjectiveDimensionLE ((H (k := k) (S := S)).obj M) d := by
  have htarget := presentation_hasProjectiveDimensionLE
    (k := k) (S := S) M d hcard
  letI : HasProjectiveDimensionLT
      ((H (k := k) (S := S)).obj (module M)) (d + 1) := htarget
  exact CategoryTheory.Retract.hasProjectiveDimensionLT
    (mapped_embedding_retraction_retract (k := k) (S := S) M) (d + 1)

/-- The maximum number of minimal complement generators over the finite
lattice. -/
noncomputable def maxComplementCard : ℕ :=
  Finset.univ.sup (fun p : S => complementCard p)

/-- Every principal downset's complement cardinality is bounded by the finite
maximum. -/
theorem complementCard_le_maxComplementCard (p : S) :
    complementCard p ≤ maxComplementCard (S := S) := by
  unfold maxComplementCard
  exact Finset.le_sup (Finset.mem_univ p)

/-- Every ordinary injective pointwise finite-dimensional module has Hom
projective dimension at most the maximum complement cardinality minus one. -/
theorem hasProjectiveDimensionLE_of_max
    (M : PModule.{u,0,u} k S) [∀ p, FiniteDimensional k (M.obj p)]
    [Injective M] :
    HasProjectiveDimensionLE ((H (k := k) (S := S)).obj M)
      (maxComplementCard (S := S) - 1) := by
  exact hasProjectiveDimensionLE (k := k) (S := S) M
    (maxComplementCard (S := S) - 1) (by
      intro p
      exact Nat.sub_le_sub_right (complementCard_le_maxComplementCard (S := S) p) 1)

/-- Every supplied certified minimal rank-projective resolution of an
ordinary injective pointwise finite-dimensional module vanishes above the
finite maximum bound, including all zero-padded terms. -/
theorem termAt_isZero_of_max
    (M : PModule.{u,0,u} k S) [∀ p, FiniteDimensional k (M.obj p)]
    [Injective M]
    (R : MinimalFiniteRankProjectiveResolution (k := k) (M := M))
    (j : ℕ) (hj : maxComplementCard (S := S) - 1 < j) :
    IsZero (R.termAt j) :=
  (FiniteRankProjectiveHomDimension.hasProjectiveDimensionLE_iff R _).mp
    (hasProjectiveDimensionLE_of_max (k := k) (S := S) M) j hj

end

end TDA.Persistence.FiniteInjectiveRankDimension
