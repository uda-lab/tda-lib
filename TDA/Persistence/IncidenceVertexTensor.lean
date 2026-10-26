import TDA.Persistence.FiniteRankProjectiveDiagonalIdealProjective
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Degree-zero vertex tensors for the interval-pair incidence algebra

For a strict interval-pair vertex, evaluation on the diagonal is a character of
the actual incidence algebra. Its rank-one coinvariants are presented as a
quotient of a left module by the character-balancing relations. This small
presentation has the balanced-bilinear universal property of the vertex
tensor, without introducing a noncommutative tensor-product foundation.

This is the degree-zero simple-tensor step corresponding to the tensor argument
in BOOS, arXiv:2208.00300v3, Lemma 5.6, and the simple-tensor identification in
Lemma 5.7, specialized to Notation 5.9's incidence algebra and diagonal ideal.
The statements here concern only these actual degree-zero coinvariants; they do
not assert higher-Tor vanishing or a global-dimension bound.
-/

set_option autoImplicit false

universe u v w

namespace TDA.Persistence.IncidenceVertexTensor

section Generic

variable {k : Type u} [Field k]
variable {R : Type v} [Ring R] [Algebra k R]
variable {N : Type w} [AddCommGroup N] [Module k N] [Module R N]
  [IsScalarTower k R N]

/-- The relations imposed by a one-dimensional right character on a left module. -/
def vertexRelation (χ : R →ₐ[k] k) : Submodule k N :=
  Submodule.span k (Set.range fun z : R × N => z.1 • z.2 - (χ z.1) • z.2)

/-- The rank-one character coinvariants of a left `R`-module. -/
abbrev VertexCoinvariants (χ : R →ₐ[k] k) :=
  N ⧸ vertexRelation (k := k) (R := R) (N := N) χ

variable (χ : R →ₐ[k] k)

/-- The right action on the one-dimensional character module. -/
def vertexRightAction (x : k) (a : R) : k := x * χ a

@[simp] theorem vertexRightAction_one (x : k) :
    vertexRightAction χ x 1 = x := by simp [vertexRightAction]

@[simp] theorem vertexRightAction_mul (x : k) (a b : R) :
    vertexRightAction χ (vertexRightAction χ x a) b =
      vertexRightAction χ x (a * b) := by
  simp [vertexRightAction, map_mul, mul_assoc]

omit [IsScalarTower k R N] in
/-- The relation quotient identifies the two sides of character balancing. -/
theorem vertexRelation_mkQ (a : R) (n : N) :
    (vertexRelation (k := k) (R := R) (N := N) χ).mkQ (a • n) =
      χ a • (vertexRelation (k := k) (R := R) (N := N) χ).mkQ n := by
  apply (Submodule.Quotient.eq (vertexRelation (k := k) (R := R) (N := N) χ)).2
  have hmem : a • n - (χ a) • n ∈ vertexRelation (k := k) (R := R) (N := N) χ :=
    Submodule.subset_span ⟨(a, n), rfl⟩
  exact hmem

/-- The pure element `x ⊗ n`, represented in character coinvariants. -/
def vertexPure (x : k) (n : N) :
    VertexCoinvariants (k := k) (R := R) (N := N) χ :=
  x • (vertexRelation (k := k) (R := R) (N := N) χ).mkQ n

/-- For each scalar, the pure-element map is linear in the module variable. -/
def vertexPureRight (x : k) :
    N →ₗ[k] VertexCoinvariants (k := k) (R := R) (N := N) χ where
  toFun n := vertexPure χ x n
  map_add' n m := by simp [vertexPure, smul_add]
  map_smul' c n := by simp [vertexPure, smul_smul, mul_comm]

/-- The rank-one pure map is a `k`-bilinear map `k × N → Q`. -/
def vertexPureBilinear :
    k →ₗ[k] N →ₗ[k] VertexCoinvariants (k := k) (R := R) (N := N) χ where
  toFun x := vertexPureRight χ x
  map_add' x y := by
    ext n
    simp [vertexPureRight, vertexPure, add_smul]
  map_smul' c x := by
    ext n
    simp [vertexPureRight, vertexPure, smul_smul, mul_comm]

@[simp] theorem vertexPureBilinear_apply (x : k) (n : N) :
    vertexPureBilinear χ x n = vertexPure χ x n := rfl

/-- The pure-element map is balanced for the right action `x • a = x * χ a`. -/
theorem vertexPure_balanced (x : k) (a : R) (n : N) :
    vertexPure χ (x * χ a) n = vertexPure χ x (a • n) := by
  change (x * χ a) • (vertexRelation (k := k) (R := R) (N := N) χ).mkQ n =
    x • (vertexRelation (k := k) (R := R) (N := N) χ).mkQ (a • n)
  rw [vertexRelation_mkQ]
  simp [smul_smul, mul_assoc]

/-- A `k`-bilinear map out of `k × N` is balanced when it respects the
character right action on `k` and the given left `R`-action on `N`. -/
def IsVertexBalanced {V : Type*} [AddCommGroup V] [Module k V]
    (f : k →ₗ[k] N →ₗ[k] V) : Prop :=
  ∀ (x : k) (a : R) (n : N), f (x * χ a) n = f x (a • n)

/-- The quotient map induced by a balanced bilinear map, evaluated at `1`. -/
noncomputable def vertexBalancedFactor {V : Type*} [AddCommGroup V] [Module k V]
    (f : k →ₗ[k] N →ₗ[k] V) (hbal : IsVertexBalanced χ f) :
    VertexCoinvariants (k := k) (R := R) (N := N) χ →ₗ[k] V := by
  let f₁ : N →ₗ[k] V := f 1
  have hrel : vertexRelation (k := k) (R := R) (N := N) χ ≤ LinearMap.ker f₁ := by
    apply Submodule.span_le.2
    rintro _ ⟨⟨a, n⟩, rfl⟩
    change f 1 (a • n - (χ a) • n) = 0
    rw [map_sub]
    have hbalance : f 1 (a • n) = f (χ a) n := by
      simpa using (hbal 1 a n).symm
    have hscalar : f (χ a) n = χ a • f 1 n := by
      have h := congrArg (fun g : N →ₗ[k] V => g n) (f.map_smul (χ a) (1 : k))
      simpa using h
    calc
      f 1 (a • n) - f 1 ((χ a) • n) = f (χ a) n - χ a • f 1 n := by
        rw [hbalance]
        simp [map_smul]
      _ = 0 := by rw [hscalar, sub_self]
  exact (vertexRelation (k := k) (R := R) (N := N) χ).liftQ f₁ hrel

/-- A balanced bilinear map factors through the vertex coinvariants with the
expected value on every pure element. -/
@[simp] theorem vertexBalancedFactor_pure {V : Type*} [AddCommGroup V] [Module k V]
    (f : k →ₗ[k] N →ₗ[k] V) (hbal : IsVertexBalanced χ f)
    (x : k) (n : N) :
    vertexBalancedFactor χ f hbal (vertexPure χ x n) = f x n := by
  let f₁ : N →ₗ[k] V := f 1
  change vertexBalancedFactor χ f hbal
      (x • (vertexRelation (k := k) (R := R) (N := N) χ).mkQ n) = f x n
  rw [map_smul]
  simp only [vertexBalancedFactor, Submodule.liftQ_apply, Submodule.mkQ_apply]
  have houter : f x n = x • f 1 n := by
    have h := congrArg (fun g : N →ₗ[k] V => g n) (f.map_smul x (1 : k))
    simpa using h
  exact houter.symm

/-- The vertex coinvariants represent all `A`-balanced `k`-bilinear maps:
factorization, computation on pure elements, and uniqueness. -/
theorem vertexBalanced_universal {V : Type*} [AddCommGroup V] [Module k V]
    (f : k →ₗ[k] N →ₗ[k] V) (hbal : IsVertexBalanced χ f) :
    ∃! F : VertexCoinvariants (k := k) (R := R) (N := N) χ →ₗ[k] V,
      ∀ x n, F (vertexPure χ x n) = f x n := by
  refine ⟨vertexBalancedFactor χ f hbal, ?_, ?_⟩
  · intro x n
    exact vertexBalancedFactor_pure χ f hbal x n
  · intro F hF
    apply LinearMap.ext
    intro q
    obtain ⟨n, rfl⟩ := (vertexRelation (k := k) (R := R) (N := N) χ).mkQ_surjective q
    calc
      F ((vertexRelation (k := k) (R := R) (N := N) χ).mkQ n) = f 1 n := by
        simpa [vertexPure] using hF 1 n
      _ = vertexBalancedFactor χ f hbal
          ((vertexRelation (k := k) (R := R) (N := N) χ).mkQ n) := by
        symm
        simpa [vertexPure] using vertexBalancedFactor_pure χ f hbal 1 n

end Generic

section Incidence

open TDA.Persistence.FiniteRankProjectiveEndAlgebra
open TDA.Persistence.FiniteRankProjectiveDiagonalIdealProjective

variable {k : Type u} [Field k] {S : Type} [Lattice S] [Finite S]

noncomputable section

local instance : Fintype S := Fintype.ofFinite S
local instance : DecidableLE S := Classical.decRel _
local instance : DecidableLT S := Classical.decRel _
local instance : DecidableEq S := Classical.decEq _
local instance : DecidableEq (WithTop S) := Classical.decEq _
local instance (p : Prop) : Decidable p := Classical.propDecidable p
local instance : Fintype (PairPoset S) :=
  Fintype.subtype (Finset.univ.filter fun ab : WithTop S × WithTop S => ab.1 ≤ ab.2)
    (by intro ab; simp)
local instance : DecidableLE (PairPoset S) := Classical.decRel _
local instance : DecidableLT (PairPoset S) := Classical.decRel _
local instance : LocallyFiniteOrder (PairPoset S) := Fintype.toLocallyFiniteOrder
local instance : DecidableEq (PairPoset S) := Classical.decEq _

abbrev Incidence := FiniteRankProjectiveEndAlgebra.Incidence (k := k) (S := S)
abbrev DiagonalIdeal :=
  FiniteRankProjectiveDiagonalIdealProjective.DiagonalIdeal (k := k) (S := S)
abbrev DiagonalQuotient := Incidence (k := k) (S := S) ⧸ DiagonalIdeal (k := k) (S := S)

local instance diagonalIdealTwoSided :
    (DiagonalIdeal (k := k) (S := S)).IsTwoSided :=
  diagonalIdeal_isTwoSided (k := k) (S := S)

/-- Evaluation at a strict interval-pair vertex. -/
def vertexCharacter (v : FiniteRankProjectiveEndAlgebra.StrictVertex S) :
    Incidence (k := k) (S := S) →ₐ[k] k where
  toFun f := f v.1 v.1
  map_one' := by
    simp [IncidenceAlgebra.one_apply]
  map_mul' f g := by
    classical
    rw [IncidenceAlgebra.mul_apply]
    have hIcc : Finset.Icc v.1 v.1 = {v.1} := Finset.Icc_self _
    rw [hIcc, Finset.sum_singleton]
  commutes' c := by
    rw [Algebra.algebraMap_eq_smul_one]
    simp [IncidenceAlgebra.constSMul_apply]
  map_zero' := by simp
  map_add' f g := by simp [IncidenceAlgebra.add_apply]

@[simp] theorem vertexCharacter_apply (v : FiniteRankProjectiveEndAlgebra.StrictVertex S)
    (f : Incidence (k := k) (S := S)) :
    vertexCharacter (k := k) (S := S) v f = f v.1 v.1 := rfl

@[simp] theorem vertexCharacter_one (v : FiniteRankProjectiveEndAlgebra.StrictVertex S) :
    vertexCharacter (k := k) (S := S) v (1 : Incidence (k := k) (S := S)) = 1 :=
  map_one (vertexCharacter (k := k) (S := S) v)

@[simp] theorem vertexCharacter_mul (v : FiniteRankProjectiveEndAlgebra.StrictVertex S)
    (f g : Incidence (k := k) (S := S)) :
    vertexCharacter (k := k) (S := S) v (f * g) =
      vertexCharacter (k := k) (S := S) v f * vertexCharacter (k := k) (S := S) v g :=
  map_mul (vertexCharacter (k := k) (S := S) v) f g

@[simp] theorem vertexCharacter_algebraMap (v : FiniteRankProjectiveEndAlgebra.StrictVertex S)
    (c : k) :
    vertexCharacter (k := k) (S := S) v (algebraMap k (Incidence (k := k) (S := S)) c) = c :=
  AlgHom.commutes (vertexCharacter (k := k) (S := S) v) c

@[simp] theorem vertexCharacter_delta (v : FiniteRankProjectiveEndAlgebra.StrictVertex S)
    (p q : PairPoset S) (hpq : p ≤ q) :
    vertexCharacter (k := k) (S := S) v (delta (k := k) (S := S) p q hpq) =
      if v.1 = p ∧ v.1 = q then 1 else 0 := by
  simp [vertexCharacter, delta_apply]

/-- The vertex character vanishes on the actual two-sided diagonal ideal. -/
theorem vertexCharacter_vanishes_on_diagonalIdeal
    (v : FiniteRankProjectiveEndAlgebra.StrictVertex S)
    (f : Incidence (k := k) (S := S))
    (hf : f ∈ DiagonalIdeal (k := k) (S := S)) :
    vertexCharacter (k := k) (S := S) v f = 0 := by
  change f v.1 v.1 = 0
  exact diagonalIdeal_coeff_zero_of_not_crosses (k := k) (S := S)
    ⟨f, hf⟩ v.1 v.1 (by
      intro hcross
      exact (not_le_of_gt v.property) hcross)

theorem vertexCharacter_zero_on_diagonalIdeal
    (v : FiniteRankProjectiveEndAlgebra.StrictVertex S)
    (f : DiagonalIdeal (k := k) (S := S)) :
    vertexCharacter (k := k) (S := S) v f.1 = 0 := by
  exact vertexCharacter_vanishes_on_diagonalIdeal (k := k) (S := S) v f.1 f.2

/-- The actual quotient of the incidence algebra by the diagonal ideal. -/
noncomputable def vertexQuotientCharacter
    (v : FiniteRankProjectiveEndAlgebra.StrictVertex S) :
    DiagonalQuotient (k := k) (S := S) →ₐ[k] k := by
  exact Ideal.Quotient.liftₐ (DiagonalIdeal (k := k) (S := S))
    (vertexCharacter (k := k) (S := S) v)
    (vertexCharacter_vanishes_on_diagonalIdeal (k := k) (S := S) v)

@[simp] theorem vertexQuotientCharacter_mk
    (v : FiniteRankProjectiveEndAlgebra.StrictVertex S)
    (f : Incidence (k := k) (S := S)) :
    vertexQuotientCharacter (k := k) (S := S) v
      (Ideal.Quotient.mk (DiagonalIdeal (k := k) (S := S)) f) =
        vertexCharacter (k := k) (S := S) v f := by
  have hcomp := Ideal.Quotient.liftₐ_comp
    (DiagonalIdeal (k := k) (S := S))
    (vertexCharacter (k := k) (S := S) v)
    (vertexCharacter_vanishes_on_diagonalIdeal (k := k) (S := S) v)
  have h := congrArg (fun F : Incidence (k := k) (S := S) →ₐ[k] k => F f) hcomp
  simpa [vertexQuotientCharacter, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk] using h

/-- The character coinvariants of the actual diagonal ideal. -/
abbrev DiagonalIdealVertexCoinvariants
    (v : FiniteRankProjectiveEndAlgebra.StrictVertex S) :=
  VertexCoinvariants (k := k) (R := Incidence (k := k) (S := S))
    (N := DiagonalIdeal (k := k) (S := S)) (vertexCharacter (k := k) (S := S) v)

/-- The character relations for the actual diagonal ideal as a left incidence
algebra module. -/
abbrev diagonalIdealVertexRelation
    (v : FiniteRankProjectiveEndAlgebra.StrictVertex S) :
    Submodule k (DiagonalIdeal (k := k) (S := S)) :=
  vertexRelation (k := k) (R := Incidence (k := k) (S := S))
    (N := DiagonalIdeal (k := k) (S := S)) (vertexCharacter (k := k) (S := S) v)

/-- A strict vertex character kills every crossing interval matrix unit in the
coinvariants of the actual diagonal ideal. The factorization uses the diagonal
floor `r` of the terminal vertex `q`. -/
theorem crossingDelta_killed_in_diagonalIdealVertexCoinvariants
    (v : FiniteRankProjectiveEndAlgebra.StrictVertex S)
    (p q : PairPoset S) (hpq : p ≤ q)
    (hcross : CrossesDiagonal (S := S) p q) :
    (diagonalIdealVertexRelation (k := k) (S := S) v).mkQ
      (⟨delta (k := k) (S := S) p q hpq,
        diagonalIdeal_mem_delta_of_cross (k := k) (S := S) p q hpq hcross⟩ :
          DiagonalIdeal (k := k) (S := S)) = 0 := by
  let r := diagonalFloor (S := S) q
  have hpr : p ≤ r :=
    (le_diagonalFloor_iff_crossesDiagonal (S := S) p q).2 hcross
  have hrq : r ≤ q := diagonalFloor_le (S := S) q
  have hrqCross : CrossesDiagonal (S := S) r q := by
    change r.val.2 ≤ q.val.1
    simp [r, diagonalFloor]
  let n : DiagonalIdeal (k := k) (S := S) :=
    ⟨delta (k := k) (S := S) r q hrq,
      diagonalIdeal_mem_delta_of_cross (k := k) (S := S) r q hrq hrqCross⟩
  have hfactor :
      (delta (k := k) (S := S) p r hpr) • n =
        ⟨delta (k := k) (S := S) p q hpq,
          diagonalIdeal_mem_delta_of_cross (k := k) (S := S) p q hpq hcross⟩ := by
    apply Subtype.ext
    change delta (k := k) (S := S) p r hpr * delta (k := k) (S := S) r q hrq =
      delta (k := k) (S := S) p q hpq
    rw [delta_mul]
    simp
  have hchar : vertexCharacter (k := k) (S := S) v
      (delta (k := k) (S := S) p r hpr) = 0 := by
    rw [vertexCharacter_delta]
    have hne : v.1 ≠ r := by
      intro h
      have hdiag : IsDiagonal (S := S) v.1 := by
        rw [h]
        exact diagonalFloor_isDiagonal (S := S) q
      exact (ne_of_lt v.property) hdiag
    simp [hne]
  rw [← hfactor, vertexRelation_mkQ, hchar]
  simp

/-- The actual vertex coinvariants of the diagonal ideal vanish, by its
crossing-delta spanning theorem and the preceding factorization. -/
theorem diagonalIdealVertexCoinvariants_mkQ_eq_zero
    (v : FiniteRankProjectiveEndAlgebra.StrictVertex S)
    (f : DiagonalIdeal (k := k) (S := S)) :
    (diagonalIdealVertexRelation (k := k) (S := S) v).mkQ f = 0 := by
  have hfspan : f.1 ∈ crossingDeltaSpan (k := k) (S := S) :=
    (mem_diagonalIdeal_iff_mem_crossingDeltaSpan (k := k) (S := S) f.1).1 f.2
  have hkill : ∀ hspan : f.1 ∈ crossingDeltaSpan (k := k) (S := S),
      ∀ hf : f.1 ∈ DiagonalIdeal (k := k) (S := S),
        (diagonalIdealVertexRelation (k := k) (S := S) v).mkQ
          (⟨f.1, hf⟩ : DiagonalIdeal (k := k) (S := S)) = 0 := by
    intro hspan
    refine Submodule.span_induction (s := Set.range fun c :
        {r : ComparablePair S // CrossesDiagonal (S := S) r.val.1 r.val.2} =>
          delta (k := k) (S := S) c.val.val.1 c.val.val.2 c.val.property)
      (p := fun g _ => ∀ hg : g ∈ DiagonalIdeal (k := k) (S := S),
        (diagonalIdealVertexRelation (k := k) (S := S) v).mkQ
          (⟨g, hg⟩ : DiagonalIdeal (k := k) (S := S)) = 0)
      ?mem ?zero ?add ?smul hfspan
    · rintro _ ⟨c, rfl⟩ _
      exact crossingDelta_killed_in_diagonalIdealVertexCoinvariants
        (k := k) (S := S) v c.val.val.1 c.val.val.2 c.val.property c.property
    · intro hg
      have hz : (⟨0, hg⟩ : DiagonalIdeal (k := k) (S := S)) = 0 := by
        apply Subtype.ext
        rfl
      rw [hz]
      simp
    · intro g h hgspan hhspan ihg ihh hsum
      have hgI := crossingDeltaSpan_le_diagonalIdeal (k := k) (S := S) g hgspan
      have hhI := crossingDeltaSpan_le_diagonalIdeal (k := k) (S := S) h hhspan
      have hsubtype : (⟨g + h, hsum⟩ : DiagonalIdeal (k := k) (S := S)) =
          (⟨g, hgI⟩ : DiagonalIdeal (k := k) (S := S)) + ⟨h, hhI⟩ := by
        apply Subtype.ext
        rfl
      rw [hsubtype, map_add, ihg hgI, ihh hhI]
      simp
    · intro c g hgspan ih hgI
      have hgI' := crossingDeltaSpan_le_diagonalIdeal (k := k) (S := S) g hgspan
      have hsubtype : (⟨c • g, hgI⟩ : DiagonalIdeal (k := k) (S := S)) =
          c • (⟨g, hgI'⟩ : DiagonalIdeal (k := k) (S := S)) := by
        apply Subtype.ext
        rfl
      rw [hsubtype, map_smul, ih hgI']
      simp
  exact hkill hfspan f.2

set_option maxHeartbeats 1000000 in
/-- Every element of the actual diagonal-ideal vertex tensor is zero. -/
theorem diagonalIdealVertexCoinvariants_eq_zero
    (v : FiniteRankProjectiveEndAlgebra.StrictVertex S)
    (x : DiagonalIdealVertexCoinvariants (k := k) (S := S) v) : x = 0 := by
  refine Quotient.inductionOn' x ?_
  intro f
  exact diagonalIdealVertexCoinvariants_mkQ_eq_zero (k := k) (S := S) v f

/-- The actual quotient carries its left incidence-algebra action through the
quotient projection. -/
instance diagonalQuotientLeftModule :
    Module (Incidence (k := k) (S := S)) (DiagonalQuotient (k := k) (S := S)) :=
  Module.compHom (DiagonalQuotient (k := k) (S := S))
    (Ideal.Quotient.mk (DiagonalIdeal (k := k) (S := S)))

instance diagonalQuotientIsScalarTower :
    IsScalarTower k (Incidence (k := k) (S := S)) (DiagonalQuotient (k := k) (S := S)) :=
  { smul_assoc := by
      intro c a b
      simp only [Algebra.smul_def]
      change Ideal.Quotient.mk (DiagonalIdeal (k := k) (S := S))
            ((algebraMap k (Incidence (k := k) (S := S)) c) * a) * b =
        algebraMap k (DiagonalQuotient (k := k) (S := S)) c *
          (Ideal.Quotient.mk (DiagonalIdeal (k := k) (S := S)) a * b)
      rw [map_mul, Ideal.Quotient.mk_algebraMap]
      simp [mul_assoc] }

/-- The character coinvariants of the actual incidence-algebra quotient. -/
abbrev DiagonalQuotientVertexCoinvariants
    (v : FiniteRankProjectiveEndAlgebra.StrictVertex S) :=
  VertexCoinvariants (k := k) (R := Incidence (k := k) (S := S))
    (N := DiagonalQuotient (k := k) (S := S))
    (vertexCharacter (k := k) (S := S) v)

/-- The relations used for the actual quotient module. -/
abbrev diagonalQuotientVertexRelation
    (v : FiniteRankProjectiveEndAlgebra.StrictVertex S) :
    Submodule k (DiagonalQuotient (k := k) (S := S)) :=
  vertexRelation (k := k) (R := Incidence (k := k) (S := S))
    (N := DiagonalQuotient (k := k) (S := S))
    (vertexCharacter (k := k) (S := S) v)

/-- The quotient character intertwines the actual projected action and the
strict-vertex character on the incidence algebra. -/
theorem vertexQuotientCharacter_smul
    (v : FiniteRankProjectiveEndAlgebra.StrictVertex S)
    (a : Incidence (k := k) (S := S)) (b : DiagonalQuotient (k := k) (S := S)) :
    vertexQuotientCharacter (k := k) (S := S) v (a • b) =
      vertexCharacter (k := k) (S := S) v a * vertexQuotientCharacter (k := k) (S := S) v b := by
  change vertexQuotientCharacter (k := k) (S := S) v
      (Ideal.Quotient.mk (DiagonalIdeal (k := k) (S := S)) a * b) = _
  rw [map_mul, vertexQuotientCharacter_mk]

/-- The descended character vanishes on the character-balancing relations
for the actual quotient module. -/
theorem diagonalQuotientVertexCharacter_balances
    (v : FiniteRankProjectiveEndAlgebra.StrictVertex S) :
    diagonalQuotientVertexRelation (k := k) (S := S) v ≤
      LinearMap.ker (vertexQuotientCharacter (k := k) (S := S) v).toLinearMap := by
  apply Submodule.span_le.2
  rintro _ ⟨⟨a, b⟩, rfl⟩
  change vertexQuotientCharacter (k := k) (S := S) v
      (a • b - (vertexCharacter (k := k) (S := S) v a) • b) = 0
  rw [map_sub, vertexQuotientCharacter_smul, map_smul]
  simp

/-- Evaluation by the descended character on the actual quotient module. -/
noncomputable def diagonalQuotientVertexTensorEvaluation
    (v : FiniteRankProjectiveEndAlgebra.StrictVertex S) :
    DiagonalQuotientVertexCoinvariants (k := k) (S := S) v →ₗ[k] k :=
  (diagonalQuotientVertexRelation (k := k) (S := S) v).liftQ
    (vertexQuotientCharacter (k := k) (S := S) v).toLinearMap
    (diagonalQuotientVertexCharacter_balances (k := k) (S := S) v)

@[simp] theorem diagonalQuotientVertexTensorEvaluation_mk
    (v : FiniteRankProjectiveEndAlgebra.StrictVertex S)
    (b : DiagonalQuotient (k := k) (S := S)) :
    diagonalQuotientVertexTensorEvaluation (k := k) (S := S) v
      ((diagonalQuotientVertexRelation (k := k) (S := S) v).mkQ b) =
        vertexQuotientCharacter (k := k) (S := S) v b := by
  change (diagonalQuotientVertexRelation (k := k) (S := S) v).liftQ
      (vertexQuotientCharacter (k := k) (S := S) v).toLinearMap
      (diagonalQuotientVertexCharacter_balances (k := k) (S := S) v)
      ((diagonalQuotientVertexRelation (k := k) (S := S) v).mkQ b) = _
  exact Submodule.liftQ_apply
    (diagonalQuotientVertexRelation (k := k) (S := S) v)
    (vertexQuotientCharacter (k := k) (S := S) v).toLinearMap b

/-- The class of the quotient unit. -/
def diagonalQuotientVertexTensorUnit
    (v : FiniteRankProjectiveEndAlgebra.StrictVertex S) :
    DiagonalQuotientVertexCoinvariants (k := k) (S := S) v :=
  (diagonalQuotientVertexRelation (k := k) (S := S) v).mkQ (1 : DiagonalQuotient (k := k) (S := S))

@[simp] theorem diagonalQuotientVertexTensorEvaluation_unit
    (v : FiniteRankProjectiveEndAlgebra.StrictVertex S) :
    diagonalQuotientVertexTensorEvaluation (k := k) (S := S) v
      (diagonalQuotientVertexTensorUnit (k := k) (S := S) v) = 1 := by
  rw [diagonalQuotientVertexTensorUnit, diagonalQuotientVertexTensorEvaluation_mk]
  exact map_one (vertexQuotientCharacter (k := k) (S := S) v)

/-- Each quotient-module class is its character coefficient times the unit
class. -/
theorem diagonalQuotientVertexTensor_reconstruct
    (v : FiniteRankProjectiveEndAlgebra.StrictVertex S)
    (x : DiagonalQuotientVertexCoinvariants (k := k) (S := S) v) :
    x = diagonalQuotientVertexTensorEvaluation (k := k) (S := S) v x •
      diagonalQuotientVertexTensorUnit (k := k) (S := S) v := by
  obtain ⟨b, rfl⟩ :=
    (diagonalQuotientVertexRelation (k := k) (S := S) v).mkQ_surjective x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
  have hsmul : (a • (1 : DiagonalQuotient (k := k) (S := S))) =
      Ideal.Quotient.mk (DiagonalIdeal (k := k) (S := S)) a := by
    change Ideal.Quotient.mk (DiagonalIdeal (k := k) (S := S)) a * 1 = _
    simp
  calc
    (diagonalQuotientVertexRelation (k := k) (S := S) v).mkQ
        (Ideal.Quotient.mk (DiagonalIdeal (k := k) (S := S)) a) =
      vertexCharacter (k := k) (S := S) v a •
        diagonalQuotientVertexTensorUnit (k := k) (S := S) v := by
          rw [← hsmul]
          exact vertexRelation_mkQ
            (χ := vertexCharacter (k := k) (S := S) v) a 1
    _ = diagonalQuotientVertexTensorEvaluation (k := k) (S := S) v
          ((diagonalQuotientVertexRelation (k := k) (S := S) v).mkQ
            (Ideal.Quotient.mk (DiagonalIdeal (k := k) (S := S)) a) ) •
          diagonalQuotientVertexTensorUnit (k := k) (S := S) v := by
            rw [diagonalQuotientVertexTensorEvaluation_mk, vertexQuotientCharacter_mk]

/-- The actual quotient vertex tensor is linearly equivalent to `k`. -/
noncomputable def diagonalQuotientVertexTensorEquiv
    (v : FiniteRankProjectiveEndAlgebra.StrictVertex S) :
    DiagonalQuotientVertexCoinvariants (k := k) (S := S) v ≃ₗ[k] k where
  toFun := diagonalQuotientVertexTensorEvaluation (k := k) (S := S) v
  invFun c := c • diagonalQuotientVertexTensorUnit (k := k) (S := S) v
  left_inv x := (diagonalQuotientVertexTensor_reconstruct (k := k) (S := S) v x).symm
  right_inv c := by simp
  map_add' := (diagonalQuotientVertexTensorEvaluation (k := k) (S := S) v).map_add'
  map_smul' := (diagonalQuotientVertexTensorEvaluation (k := k) (S := S) v).map_smul'

@[simp] theorem diagonalQuotientVertexTensorEquiv_mk
    (v : FiniteRankProjectiveEndAlgebra.StrictVertex S)
    (b : DiagonalQuotient (k := k) (S := S)) :
    diagonalQuotientVertexTensorEquiv (k := k) (S := S) v
      ((diagonalQuotientVertexRelation (k := k) (S := S) v).mkQ b) =
        vertexQuotientCharacter (k := k) (S := S) v b := by
  exact diagonalQuotientVertexTensorEvaluation_mk (k := k) (S := S) v b

@[simp] theorem diagonalQuotientVertexTensorEquiv_symm_apply (v :
    FiniteRankProjectiveEndAlgebra.StrictVertex S) (c : k) :
    (diagonalQuotientVertexTensorEquiv (k := k) (S := S) v).symm c =
      c • diagonalQuotientVertexTensorUnit (k := k) (S := S) v := rfl

/-- The class of the quotient unit survives in the actual tensor. -/
theorem diagonalQuotientVertexTensorUnit_ne_zero
    (v : FiniteRankProjectiveEndAlgebra.StrictVertex S) :
    diagonalQuotientVertexTensorUnit (k := k) (S := S) v ≠ 0 := by
  intro h
  have h' := congrArg (diagonalQuotientVertexTensorEvaluation (k := k) (S := S) v) h
  simpa using h'

/-- Evaluation on a right multiple obeys the character coefficient law. -/
theorem diagonalQuotientVertexTensorEvaluation_mul
    (v : FiniteRankProjectiveEndAlgebra.StrictVertex S)
    (b c : DiagonalQuotient (k := k) (S := S)) :
    diagonalQuotientVertexTensorEvaluation (k := k) (S := S) v
        ((diagonalQuotientVertexRelation (k := k) (S := S) v).mkQ (b * c)) =
      diagonalQuotientVertexTensorEvaluation (k := k) (S := S) v
        ((diagonalQuotientVertexRelation (k := k) (S := S) v).mkQ b) *
          vertexQuotientCharacter (k := k) (S := S) v c := by
  rw [diagonalQuotientVertexTensorEvaluation_mk,
    diagonalQuotientVertexTensorEvaluation_mk, map_mul]

end

end Incidence

end TDA.Persistence.IncidenceVertexTensor
