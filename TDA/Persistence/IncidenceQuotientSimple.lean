import TDA.Persistence.IncidenceVertexTor
import Mathlib.Algebra.Category.ModuleCat.Simple
import Mathlib.Algebra.Ring.Opposite
import Mathlib.Order.Preorder.Finite

/-!
# Simple modules over the right diagonal quotient

The right simple modules over the quotient of the interval-pair incidence algebra
by its diagonal ideal are the one-dimensional character modules at strict
interval pairs.  The proof uses the actual opposite quotient: finite matrix
idempotents select a maximal active vertex, and the opposite multiplication
order forces that vertex to act by its character on a nonzero vector.

The degree-zero comparison below is an isomorphism of `k`-modules.  The
left-derived object has no `C`-module structure asserted here.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence.IncidenceQuotientSimple

open CategoryTheory
open TDA.Persistence.FiniteRankProjectiveEndAlgebra
open TDA.Persistence.FiniteRankProjectiveDiagonalIdealProjective
open TDA.Persistence.IncidenceVertexTensor
open TDA.Persistence.IncidenceVertexTensorFunctor
open TDA.Persistence.IncidenceVertexTor

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
local instance : Fintype (ComparablePair S) := Fintype.ofFinite _

abbrev Incidence := FiniteRankProjectiveEndAlgebra.Incidence (k := k) (S := S)
abbrev DiagonalIdeal := FiniteRankProjectiveDiagonalIdealProjective.DiagonalIdeal
  (k := k) (S := S)
abbrev DiagonalQuotient := Incidence (k := k) (S := S) ⧸ DiagonalIdeal (k := k) (S := S)
abbrev RightQuotient := (DiagonalQuotient (k := k) (S := S))ᵐᵒᵖ

local instance diagonalIdealTwoSided :
    (DiagonalIdeal (k := k) (S := S)).IsTwoSided :=
  diagonalIdeal_isTwoSided (k := k) (S := S)

/-- The descended vertex character, read as a character of the actual right-module ring. -/
def rightVertexCharacter (v : StrictVertex S) : RightQuotient (k := k) (S := S) →+* k :=
  RingHom.fromOpposite
    (vertexQuotientCharacter (k := k) (S := S) v).toRingHom
    (fun _ _ => Commute.all _ _)

@[simp] theorem rightVertexCharacter_apply (v : StrictVertex S)
    (c : RightQuotient (k := k) (S := S)) :
    rightVertexCharacter (k := k) (S := S) v c =
      vertexQuotientCharacter (k := k) (S := S) v (MulOpposite.unop c) := rfl

@[simp] theorem rightVertexCharacter_algebraMap (v : StrictVertex S) (a : k) :
    rightVertexCharacter (k := k) (S := S) v
      (algebraMap k (RightQuotient (k := k) (S := S)) a) = a := by
  simp [rightVertexCharacter]

theorem rightVertexCharacter_surjective (v : StrictVertex S) :
    Function.Surjective (rightVertexCharacter (k := k) (S := S) v) := by
  intro a
  exact ⟨algebraMap k (RightQuotient (k := k) (S := S)) a,
    rightVertexCharacter_algebraMap (k := k) (S := S) v a⟩

/-- The quotient matrix unit in the opposite ring, with the right-module
multiplication convention. -/
def rightMatrixUnit (p q : PairPoset S) (hpq : p ≤ q) :
    RightQuotient (k := k) (S := S) :=
  MulOpposite.op (Ideal.Quotient.mk (DiagonalIdeal (k := k) (S := S))
    (delta (k := k) (S := S) p q hpq))

private theorem incidence_sum_apply {ι : Type} (s : Finset ι)
    (g : ι → Incidence (k := k) (S := S)) (a b : PairPoset S) :
    (∑ i ∈ s, g i) a b = ∑ i ∈ s, g i a b := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi, IncidenceAlgebra.add_apply, ih]

theorem incidence_sum_diagonal_delta :
    (∑ p : PairPoset S, delta (k := k) (S := S) p p le_rfl) =
      (1 : Incidence (k := k) (S := S)) := by
  classical
  ext a b hab
  rw [incidence_sum_apply]
  by_cases h : a = b
  · subst b
    simp [IncidenceAlgebra.one_apply, delta_apply]
  · rw [IncidenceAlgebra.one_apply]
    simp only [if_neg h]
    change (∑ p : PairPoset S, if a = p ∧ b = p then (1 : k) else 0) = 0
    apply Finset.sum_eq_zero
    intro p hp
    by_cases hap : a = p
    · subst p
      simp [h, eq_comm]
    · simp [hap]

@[simp] theorem rightMatrixUnit_diagonal_sum :
    (∑ p : PairPoset S,
      rightMatrixUnit (k := k) (S := S) p p le_rfl) = 1 := by
  classical
  simp only [rightMatrixUnit]
  rw [← Finset.op_sum, ← map_sum (Ideal.Quotient.mk (DiagonalIdeal (k := k) (S := S))),
    incidence_sum_diagonal_delta]
  simp

@[simp] theorem rightMatrixUnit_mul (p q r s : PairPoset S)
    (hpq : p ≤ q) (hrs : r ≤ s) :
    rightMatrixUnit (k := k) (S := S) p q hpq *
        rightMatrixUnit (k := k) (S := S) r s hrs =
      if h : s = p then
        rightMatrixUnit (k := k) (S := S) r q (by subst p; exact hrs.trans hpq)
      else 0 := by
  classical
  apply MulOpposite.unop_injective
  simp only [MulOpposite.unop_mul, rightMatrixUnit, MulOpposite.unop_op]
  rw [← map_mul, delta_mul]
  split_ifs <;> simp_all

@[simp] theorem rightVertexCharacter_rightMatrixUnit (v : StrictVertex S)
    (p q : PairPoset S) (hpq : p ≤ q) :
    rightVertexCharacter (k := k) (S := S) v
      (rightMatrixUnit (k := k) (S := S) p q hpq) =
        if v.1 = p ∧ v.1 = q then 1 else 0 := by
  simp [rightMatrixUnit, rightVertexCharacter, vertexQuotientCharacter_mk,
    vertexCharacter_delta]

/-- The actual restriction of the field module along the right vertex character. -/
abbrev RightVertexModule (v : StrictVertex S) : ModuleCat (RightQuotient (k := k) (S := S)) :=
  (ModuleCat.restrictScalars
    (rightVertexCharacter (k := k) (S := S) v)).obj (ModuleCat.of k k)

@[simp] theorem rightMatrixUnit_smul (v : StrictVertex S)
    (p q : PairPoset S) (hpq : p ≤ q) (t : RightVertexModule (k := k) (S := S) v) :
    rightMatrixUnit (k := k) (S := S) p q hpq • t =
      (if v.1 = p ∧ v.1 = q then t else 0) := by
  change rightVertexCharacter (k := k) (S := S) v
      (rightMatrixUnit (k := k) (S := S) p q hpq) • t = _
  simp [rightMatrixUnit, rightVertexCharacter, vertexQuotientCharacter_mk]

theorem rightVertexCharacter_matrixScalar (v : StrictVertex S)
    (p q : PairPoset S) (hpq : p ≤ q) (a : k) :
    rightVertexCharacter (k := k) (S := S) v
      (algebraMap k (RightQuotient (k := k) (S := S)) a *
        rightMatrixUnit (k := k) (S := S) p q hpq) =
      a * rightVertexCharacter (k := k) (S := S) v
        (rightMatrixUnit (k := k) (S := S) p q hpq) := by
  simp [map_mul]

/-- A diagonal matrix idempotent is killed by the actual quotient ideal. -/
theorem rightMatrixUnit_eq_zero_of_isDiagonal (p : PairPoset S)
    (hp : IsDiagonal (S := S) p) :
    rightMatrixUnit (k := k) (S := S) p p le_rfl = 0 := by
  change MulOpposite.op
    (Ideal.Quotient.mk (DiagonalIdeal (k := k) (S := S))
      (delta (k := k) (S := S) p p le_rfl)) = MulOpposite.op 0
  have hq : Ideal.Quotient.mk (DiagonalIdeal (k := k) (S := S))
      (delta (k := k) (S := S) p p le_rfl) = 0 := by
    rw [Ideal.Quotient.eq_zero_iff_mem]
    apply diagonalIdeal_mem_delta_of_cross (k := k) (S := S) p p le_rfl
    change p.val.2 ≤ p.val.1
    rw [hp]
  rw [hq]

local instance rightQuotientModuleK (M : ModuleCat (RightQuotient (k := k) (S := S))) :
    Module k M := Module.compHom M (algebraMap k (RightQuotient (k := k) (S := S)))

local instance rightQuotientScalarTower
    (M : ModuleCat (RightQuotient (k := k) (S := S))) :
    IsScalarTower k (RightQuotient (k := k) (S := S)) M :=
  IsScalarTower.of_compHom k (RightQuotient (k := k) (S := S)) M

theorem rightVertexModule_isSimpleModule (v : StrictVertex S) :
    IsSimpleModule (RightQuotient (k := k) (S := S))
      (RightVertexModule (k := k) (S := S) v) := by
  let χ := rightVertexCharacter (k := k) (S := S) v
  letI : RingHomSurjective χ := ⟨rightVertexCharacter_surjective (k := k) (S := S) v⟩
  letI : Module (RightQuotient (k := k) (S := S)) k := Module.compHom k χ
  let f : k →ₛₗ[χ] k :=
    { toFun := id
      map_add' := by intro a b; rfl
      map_smul' := by intro a b; rfl }
  have hf : Function.Bijective f := by
    constructor <;> intro a <;> simp [f]
  exact (LinearMap.isSimpleModule_iff_of_bijective f hf).2 inferInstance

instance rightVertexModule_isSimple (v : StrictVertex S) :
    Simple (RightVertexModule (k := k) (S := S) v) :=
  (simple_iff_isSimpleModule'
    (RightVertexModule (k := k) (S := S) v)).2
      (rightVertexModule_isSimpleModule (k := k) (S := S) v)

private def activeVertices (M : ModuleCat (RightQuotient (k := k) (S := S))) :
    Finset (PairPoset S) :=
  Finset.univ.filter fun p =>
    ∃ m : M, rightMatrixUnit (k := k) (S := S) p p le_rfl • m ≠ 0

private theorem rightMatrixUnit_smul_on_maximal_active
    (M : ModuleCat (RightQuotient (k := k) (S := S)))
    (p : PairPoset S)
    (hmax : Maximal (fun t : PairPoset S => t ∈ activeVertices (k := k) (S := S) M) p)
    (m : M) (r s : PairPoset S) (hrs : r ≤ s) :
    rightMatrixUnit (k := k) (S := S) r s hrs •
        (rightMatrixUnit (k := k) (S := S) p p le_rfl • m) =
      if r = p ∧ s = p then rightMatrixUnit (k := k) (S := S) p p le_rfl • m else 0 := by
  rw [smul_smul]
  rw [rightMatrixUnit_mul]
  by_cases hr : r = p
  · subst r
    by_cases hs : s = p
    · subst s
      simp
    · have hps : p < s := lt_of_le_of_ne hrs (Ne.symm hs)
      have hzero : rightMatrixUnit (k := k) (S := S) p s hrs • m = 0 := by
        by_contra hne
        have hfix : rightMatrixUnit (k := k) (S := S) s s le_rfl •
            (rightMatrixUnit (k := k) (S := S) p s hrs • m) =
              rightMatrixUnit (k := k) (S := S) p s hrs • m := by
          rw [smul_smul]
          rw [rightMatrixUnit_mul]
          simp
        have hsActive : s ∈ activeVertices (k := k) (S := S) M := by
          simp only [activeVertices, Finset.mem_filter, Finset.mem_univ, true_and]
          refine ⟨rightMatrixUnit (k := k) (S := S) p s hrs • m, ?_⟩
          simpa only [hfix] using hne
        have hsp : s ≤ p := hmax.2 hsActive (le_of_lt hps)
        exact (not_lt_of_ge hsp) hps
      simp [hs, hzero]
  · have hpr : p ≠ r := Ne.symm hr
    simp [hr, hpr]

/-- Two right vertex modules are isomorphic exactly when their strict vertices agree. -/
theorem rightVertexModule_iso_iff (v w : StrictVertex S) :
    Nonempty (RightVertexModule (k := k) (S := S) v ≅
      RightVertexModule (k := k) (S := S) w) ↔ v = w := by
  constructor
  · rintro ⟨i⟩
    by_contra hvw
    have hvertices : v.1 ≠ w.1 := by
      intro h
      exact hvw (Subtype.ext h)
    let e := rightMatrixUnit (k := k) (S := S) v.1 v.1 le_rfl
    letI : Module (RightQuotient (k := k) (S := S)) k :=
      (RightVertexModule (k := k) (S := S) v).isModule
    letI : Module (RightQuotient (k := k) (S := S))
        (↑(RightVertexModule (k := k) (S := S) w)) :=
      (RightVertexModule (k := k) (S := S) w).isModule
    have hsource : e • (1 : k) = 1 := by
      change rightVertexCharacter (k := k) (S := S) v e * 1 = 1
      rw [show rightVertexCharacter (k := k) (S := S) v e = 1 from by
        simpa [e] using rightVertexCharacter_rightMatrixUnit
          (k := k) (S := S) v v.1 v.1 le_rfl]
      simp
    let m : k := 1
    have hχ : rightVertexCharacter (k := k) (S := S) w e = 0 := by
      have hvertices' : w.1 ≠ v.1 := Ne.symm hvertices
      simpa [e, hvertices'] using rightVertexCharacter_rightMatrixUnit
        (k := k) (S := S) w v.1 v.1 le_rfl
    have hmap : i.hom.hom m = 0 := by
      calc
        i.hom.hom m = i.hom.hom (e • m) := by
          rw [hsource]
        _ = e • i.hom.hom m := i.hom.hom.map_smul e m
        _ = 0 := by
          change rightVertexCharacter (k := k) (S := S) w e • i.hom.hom m = 0
          rw [hχ]
          simp
    have hone : (1 : k) = 0 := by
      let i' := i.toLinearEquiv
      have hm : m = 0 := by
        have hmap' : i' m = 0 := by
          change i.hom.hom m = 0
          exact hmap
        have heq : i' m = i' 0 := by rw [hmap']; simp
        exact i'.injective heq
      calc
        1 = m := by simp [m]
        _ = 0 := hm
    exact one_ne_zero hone
  · intro h
    subst w
    exact ⟨Iso.refl _⟩

end

end TDA.Persistence.IncidenceQuotientSimple
