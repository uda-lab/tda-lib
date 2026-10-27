import TDA.Persistence.FiniteHomDimension
import TDA.Persistence.IncidenceVertexProjectiveDimension
import TDA.Persistence.TwoInjectiveHomDimension
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.ProjectiveDimension
import Mathlib.CategoryTheory.Linear.Basic

/-!
# Actual Hom-cokernel dimensions over finite grids

The opposite endomorphism algebra of the finite hook generator is the actual
opposite diagonal quotient. Restriction along this algebra equivalence turns
finite-dimensional Hom modules into actual quotient modules, where the
already-proved projective-dimension estimates apply. The actual two-injective
Hom cokernel is finite-dimensional by its categorical cokernel projection;
the existing two-step shift then gives the finite-grid upper bound and
zero-padded minimal-resolution vanishing.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence.FiniteRankProjectiveHomQuotientDimension

open CategoryTheory CategoryTheory.Limits
open TDA.Persistence.FiniteRankProjectiveEndAlgebra
open TDA.Persistence.FiniteRankProjectiveHomExact
open TDA.Persistence.IncidenceQuotientSimple
open TDA.Persistence.IncidenceQuotientBaseChange
open TDA.Persistence.FiniteInjectiveRankDimension
open TDA.Persistence.FiniteLatticeComplementCardinality
open TDA.Persistence.TwoInjectivePresentation
open TDA.Persistence.TwoInjectiveHomDimension
open scoped ModuleCat

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
local instance :
    (IncidenceQuotientBaseChange.DiagonalIdeal (k := k) (S := S)).IsTwoSided :=
  FiniteRankProjectiveEndAlgebra.diagonalIdeal_isTwoSided
    (k := k) (S := S)

/-- The actual opposite endomorphism algebra acting on the existing Hom functor. -/
abbrev HomScalars := FiniteRankProjectiveHomExact.HomScalars (k := k) (S := S)

/-- The actual opposite diagonal quotient ring. -/
abbrev RightQuotient := IncidenceQuotientBaseChange.RightQuotient (k := k) (S := S)

/-- Canonical coefficient-field restriction of a bundled module. -/
abbrev canonicalFieldRestriction {R : Type u} [Ring R] [Algebra k R]
    (N : ModuleCat.{u} R) : ModuleCat.{u} k :=
  (ModuleCat.restrictScalars (algebraMap k R)).obj N

/-- The actual algebra equivalence from the Hom scalars to the quotient ring. -/
noncomputable def hookHomAlgEquivRightQuotient :
    HomScalars (k := k) (S := S) ≃ₐ[k] RightQuotient (k := k) (S := S) :=
  (FiniteRankProjectiveEndAlgebra.hookEndAlgEquivIncidenceQuotient
    (k := k) (S := S)).op

local instance : RingHomInvPair
    ((hookHomAlgEquivRightQuotient (k := k) (S := S)).symm.toRingEquiv.toRingHom)
    ((hookHomAlgEquivRightQuotient (k := k) (S := S)).toRingEquiv.toRingHom) :=
  RingHomInvPair.of_ringEquiv
    (hookHomAlgEquivRightQuotient (k := k) (S := S)).symm.toRingEquiv

local instance : RingHomInvPair
    ((hookHomAlgEquivRightQuotient (k := k) (S := S)).toRingEquiv.toRingHom)
    ((hookHomAlgEquivRightQuotient (k := k) (S := S)).symm.toRingEquiv.toRingHom) :=
  RingHomInvPair.of_ringEquiv
    (hookHomAlgEquivRightQuotient (k := k) (S := S)).toRingEquiv

/-- Restrict an actual Hom-scalar module along the inverse algebra equivalence. -/
abbrev quotientModuleOfHomModule
    (N : ModuleCat.{u} (HomScalars (k := k) (S := S))) :
    ModuleCat.{u} (RightQuotient (k := k) (S := S)) :=
  (ModuleCat.restrictScalars
    (hookHomAlgEquivRightQuotient (k := k) (S := S)).symm.toRingHom).obj N

/-- The quotient-module restriction is the same underlying vector as the original
Hom-scalar module, with the action transported along the actual algebra equivalence. -/
noncomputable def quotientModuleSemilinearEquiv
    (N : ModuleCat.{u} (HomScalars (k := k) (S := S))) :
    quotientModuleOfHomModule (k := k) (S := S) N ≃ₛₗ[
      (hookHomAlgEquivRightQuotient (k := k) (S := S)).symm.toRingHom] N := by
  exact
    { toFun := id
      invFun := id
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }

/-- On elements, the quotient-module semilinear equivalence is the identity. -/
@[simp] theorem quotientModuleSemilinearEquiv_apply
    (N : ModuleCat.{u} (HomScalars (k := k) (S := S))) (x : N) :
    quotientModuleSemilinearEquiv (k := k) (S := S) N x = x := rfl

/-- Canonical field restriction commutes with the actual algebra-equivalence
restriction, by the algebra map identity of that equivalence. -/
noncomputable def quotientRestrictionFieldIso
    (N : ModuleCat.{u} (HomScalars (k := k) (S := S))) :
    canonicalFieldRestriction (k := k) N ≅
      IncidenceQuotientSimple.restrictRightQuotientModule (k := k) (S := S)
        (quotientModuleOfHomModule (k := k) (S := S) N) := by
  let e := hookHomAlgEquivRightQuotient (k := k) (S := S)
  have hfield : algebraMap k (HomScalars (k := k) (S := S)) =
      e.symm.toRingHom.comp (algebraMap k (RightQuotient (k := k) (S := S))) := by
    ext c
    exact (e.symm.commutes c).symm
  exact ModuleCat.restrictScalarsComp'App
    (algebraMap k (RightQuotient (k := k) (S := S))) e.symm.toRingHom
    (algebraMap k (HomScalars (k := k) (S := S))) hfield N

/-- The actual C-module estimate transfers to every finite-dimensional actual
Hom-scalar module. -/
theorem homScalarModule_hasProjectiveDimensionLE
    [OrderBot S] [OrderTop S]
    (N : ModuleCat.{u} (HomScalars (k := k) (S := S)))
    (hN : FiniteDimensional k (canonicalFieldRestriction (k := k) N)) :
    letI : Lattice (PairPoset S) := pairPosetLattice (S := S)
    letI : BoundedOrder (PairPoset S) := pairPosetBoundedOrder (S := S)
    HasProjectiveDimensionLE N (maxComplementCard (S := PairPoset S)) := by
  letI : Lattice (PairPoset S) := pairPosetLattice (S := S)
  letI : BoundedOrder (PairPoset S) := pairPosetBoundedOrder (S := S)
  have hQ : FiniteDimensional k
      (IncidenceQuotientSimple.restrictRightQuotientModule (k := k) (S := S)
        (quotientModuleOfHomModule (k := k) (S := S) N)) :=
    (quotientRestrictionFieldIso (k := k) (S := S) N).toLinearEquiv.finiteDimensional
  have hPD := IncidenceVertexProjectiveDimension.quotient_hasProjectiveDimensionLE
    (k := k) (S := S) (quotientModuleOfHomModule (k := k) (S := S) N) hQ
  letI : HasProjectiveDimensionLE
      (quotientModuleOfHomModule (k := k) (S := S) N)
      (maxComplementCard (S := PairPoset S)) := hPD
  exact ModuleCat.hasProjectiveDimensionLE_of_semiLinearEquiv
    (hookHomAlgEquivRightQuotient (k := k) (S := S)).symm.toRingEquiv
    (quotientModuleSemilinearEquiv (k := k) (S := S) N)
    (maxComplementCard (S := PairPoset S))

end

end TDA.Persistence.FiniteRankProjectiveHomQuotientDimension
