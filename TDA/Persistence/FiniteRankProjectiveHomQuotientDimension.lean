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
local instance : Fintype (HookTag (S := S)) := Fintype.ofFinite _
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

/-- Scalar multiplication in the canonical restricted module is the original
module action through the coefficient-field algebra map. -/
@[simp] theorem canonicalFieldRestriction_smul {R : Type u} [Ring R] [Algebra k R]
    (N : ModuleCat.{u} R) (c : k) (x : canonicalFieldRestriction (k := k) N) :
    c • x = (algebraMap k R c) • x := rfl

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

/-- Scalar compatibility of the quotient-module semilinear equivalence. -/
@[simp] theorem quotientModuleSemilinearEquiv_smul
    (N : ModuleCat.{u} (HomScalars (k := k) (S := S)))
    (c : RightQuotient (k := k) (S := S)) (x : quotientModuleOfHomModule (k := k) (S := S) N) :
    quotientModuleSemilinearEquiv (k := k) (S := S) N (c • x) =
      ((hookHomAlgEquivRightQuotient (k := k) (S := S)).symm c) •
        quotientModuleSemilinearEquiv (k := k) (S := S) N x :=
  map_smulₛₗ _ _ _

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

/-- The actual field-restriction comparison preserves every vector. -/
@[simp] theorem quotientRestrictionFieldIso_hom_apply
    (N : ModuleCat.{u} (HomScalars (k := k) (S := S))) (x : N) :
    (quotientRestrictionFieldIso (k := k) (S := S) N).hom x = x := rfl

/-- The inverse field-restriction comparison preserves every vector. -/
@[simp] theorem quotientRestrictionFieldIso_inv_apply
    (N : ModuleCat.{u} (HomScalars (k := k) (S := S))) (x : N) :
    (quotientRestrictionFieldIso (k := k) (S := S) N).inv x = x := rfl

/-- The field-restriction comparison is `k`-linear on actual elements. -/
@[simp] theorem quotientRestrictionFieldIso_hom_smul
    (N : ModuleCat.{u} (HomScalars (k := k) (S := S))) (c : k) (x : N) :
    (quotientRestrictionFieldIso (k := k) (S := S) N).hom (c • x) =
      c • (quotientRestrictionFieldIso (k := k) (S := S) N).hom x :=
  map_smul _ _ _

/-- The inverse field-restriction comparison is `k`-linear on actual elements. -/
@[simp] theorem quotientRestrictionFieldIso_inv_smul
    (N : ModuleCat.{u} (HomScalars (k := k) (S := S))) (c : k)
    (x : IncidenceQuotientSimple.restrictRightQuotientModule (k := k) (S := S)
      (quotientModuleOfHomModule (k := k) (S := S) N)) :
    (quotientRestrictionFieldIso (k := k) (S := S) N).inv (c • x) =
      c • (quotientRestrictionFieldIso (k := k) (S := S) N).inv x :=
  map_smul _ _ _

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

/-- The scalar action of the algebra map on the Hom-scalar module agrees with
the natural scalar action on persistence morphisms. -/
private theorem homScalar_action_eq (M : PModule.{u,0,u} k S) (c : k)
    (f : HookSum (k := k) (S := S) ⟶ M) :
    (algebraMap k (HomScalars (k := k) (S := S)) c) • f = c • f := by
  change MulOpposite.unop (algebraMap k (HomScalars (k := k) (S := S)) c) ≫ f = c • f
  have hscalar :
      MulOpposite.unop (algebraMap k (HomScalars (k := k) (S := S)) c) =
        c • (𝟙 (HookSum (k := k) (S := S))) := by
    change algebraMap k (End (HookSum (k := k) (S := S))) c = _
    simpa [Algebra.algebraMap_eq_smul_one]
  rw [hscalar, CategoryTheory.Linear.smul_comp]
  simp

/-- The canonical field restriction of the actual Hom-scalar module is
k-linearly equivalent to the natural persistence-morphism space. -/
noncomputable def homScalarFieldLinearEquiv (M : PModule.{u,0,u} k S) :
    canonicalFieldRestriction (k := k) ((homFunctor (k := k) (S := S)).obj M) ≃ₗ[k]
      (HookSum (k := k) (S := S) ⟶ M) where
  toFun := id
  invFun := id
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  map_add' := by intros; rfl
  map_smul' := by
    intro c f
    rw [canonicalFieldRestriction_smul]
    exact homScalar_action_eq (k := k) (S := S) M c f

/-- The scalar bridge preserves the underlying natural transformation. -/
@[simp] theorem homScalarFieldLinearEquiv_apply (M : PModule.{u,0,u} k S)
    (f : HookSum (k := k) (S := S) ⟶ M) :
    homScalarFieldLinearEquiv (k := k) (S := S) M f = f := rfl

/-- Its inverse also preserves the underlying natural transformation. -/
@[simp] theorem homScalarFieldLinearEquiv_symm_apply (M : PModule.{u,0,u} k S)
    (f : HookSum (k := k) (S := S) ⟶ M) :
    (homScalarFieldLinearEquiv (k := k) (S := S) M).symm f = f := rfl

/-- The natural-Hom and restricted-field scalar actions agree under the
identity-on-elements linear equivalence. -/
@[simp] theorem homScalarFieldLinearEquiv_smul (M : PModule.{u,0,u} k S)
    (c : k)
    (f : canonicalFieldRestriction (k := k)
      ((homFunctor (k := k) (S := S)).obj M)) :
    homScalarFieldLinearEquiv (k := k) (S := S) M (c • f) =
      c • homScalarFieldLinearEquiv (k := k) (S := S) M f :=
  map_smul _ _ _

private theorem hookSum_finiteDimensional (p : S) :
    FiniteDimensional k ((HookSum (k := k) (S := S)).obj p) := by
  haveI : ∀ t : HookTag (S := S),
      FiniteDimensional k ((hookFamily (k := k) (S := S) t).obj p) := by
    intro t
    cases t with
    | inl ab =>
        change FiniteDimensional k ((Hook.module (k := k) ab.val.1 ab.val.2).obj p)
        infer_instance
    | inr a =>
        change FiniteDimensional k ((HookInfinity.module (R := k) a).obj p)
        infer_instance
  exact FiniteBiproduct.finiteDimensional (hookFamily (k := k) (S := S)) p

/-- For every pointwise finite-dimensional persistence module, the actual Hom
module from the finite hook generator is finite-dimensional over the canonical
field restriction. -/
theorem homFunctor_obj_finiteDimensional (M : PModule.{u,0,u} k S)
    (hM : ∀ p, FiniteDimensional k (M.obj p)) :
    FiniteDimensional k
      (canonicalFieldRestriction (k := k) ((homFunctor (k := k) (S := S)).obj M)) := by
  have hHom : FiniteDimensional k (HookSum (k := k) (S := S) ⟶ M) :=
    FiniteHomDimension.finiteDimensional_hom (k := k)
      (HookSum (k := k) (S := S)) M hookSum_finiteDimensional hM
  letI : FiniteDimensional k (HookSum (k := k) (S := S) ⟶ M) := hHom
  exact (homScalarFieldLinearEquiv (k := k) (S := S) M).symm.finiteDimensional

/-- The actual cokernel of Hom applied to the two-injective differential is
finite-dimensional by its epic categorical cokernel projection. -/
theorem homCokernel_finiteDimensional
    [OrderBot S] [OrderTop S]
    (M : PModule.{u,0,u} k S)
    (hM : ∀ p, FiniteDimensional k (M.obj p)) :
    FiniteDimensional k
      (canonicalFieldRestriction (k := k)
        (homCokernel (k := k) (S := S) M)) := by
  letI : ∀ p, FiniteDimensional k (M.obj p) := hM
  have hQ : ∀ p, FiniteDimensional k ((TwoInjectivePresentation.quotient M).obj p) :=
    TwoInjectivePresentation.quotient_finiteDimensional M
  have hSecond : ∀ p, FiniteDimensional k ((secondInjective M).obj p) := by
    intro p
    letI : ∀ p, FiniteDimensional k ((TwoInjectivePresentation.quotient M).obj p) := hQ
    exact FiniteInjectivePresentation.finiteDimensional
      (TwoInjectivePresentation.quotient M) p
  have hDomain := homFunctor_obj_finiteDimensional (k := k) (S := S)
    (secondInjective M) hSecond
  letI : FiniteDimensional k
      (canonicalFieldRestriction (k := k) ((homFunctor (k := k) (S := S)).obj
        (secondInjective M))) := hDomain
  have hEpi : Epi (homCokernelProjection M) := inferInstance
  have hSurj : Function.Surjective (homCokernelProjection M).hom :=
    (ModuleCat.epi_iff_surjective _).mp hEpi
  have hSurj' : Function.Surjective
      (((ModuleCat.restrictScalars
        (algebraMap k (HomScalars (k := k) (S := S)))).map
        (homCokernelProjection M)).hom) := by
    change Function.Surjective (homCokernelProjection M).hom
    exact hSurj
  exact FiniteDimensional.of_surjective
    (((ModuleCat.restrictScalars
      (algebraMap k (HomScalars (k := k) (S := S)))).map
      (homCokernelProjection M)).hom) hSurj'

/-- For every pointwise finite-dimensional source module, the actual
two-injective Hom cokernel has the unconditional finite-lattice bound. -/
theorem homCokernel_hasProjectiveDimensionLE
    [OrderBot S] [OrderTop S]
    (M : PModule.{u,0,u} k S)
    (hM : ∀ p, FiniteDimensional k (M.obj p)) :
    letI : Lattice (PairPoset S) := pairPosetLattice (S := S)
    letI : BoundedOrder (PairPoset S) := pairPosetBoundedOrder (S := S)
    HasProjectiveDimensionLE (homCokernel (k := k) (S := S) M)
      (maxComplementCard (S := PairPoset S)) := by
  letI : Lattice (PairPoset S) := pairPosetLattice (S := S)
  letI : BoundedOrder (PairPoset S) := pairPosetBoundedOrder (S := S)
  letI : ∀ p, FiniteDimensional k (M.obj p) := hM
  have hK : FiniteDimensional k
      (canonicalFieldRestriction (k := k) (homCokernel (k := k) (S := S) M)) :=
    homCokernel_finiteDimensional (k := k) (S := S) M hM
  exact homScalarModule_hasProjectiveDimensionLE (k := k) (S := S)
    (homCokernel (k := k) (S := S) M) hK

/-- The actual two-injective Hom cokernel on a nonempty-factor coordinate grid
has ordinary projective dimension at most twice the number of coordinates. -/
theorem coordinateGrid_homCokernel_hasProjectiveDimensionLE
    {n : ℕ} (G : CoordinateGrid n) (hn : 1 ≤ n)
    (hG : ∀ i : Fin n, (G i).Nonempty)
    (M : PModule.{u,0,u} k G.Point)
    (hM : ∀ p, FiniteDimensional k (M.obj p)) :
    letI : BoundedOrder G.Point := coordinateGridBoundedOrder G hG
    HasProjectiveDimensionLE
      (homCokernel (k := k) (S := G.Point) M) (2 * n) := by
  letI : BoundedOrder G.Point := coordinateGridBoundedOrder G hG
  letI : Lattice (PairPoset G.Point) := pairPosetLattice (S := G.Point)
  letI : BoundedOrder (PairPoset G.Point) :=
    pairPosetBoundedOrder (S := G.Point)
  letI : ∀ p, FiniteDimensional k (M.obj p) := hM
  let K := homCokernel (k := k) (S := G.Point) M
  have hK : FiniteDimensional k (canonicalFieldRestriction (k := k) K) :=
    homCokernel_finiteDimensional (k := k) (S := G.Point) M hM
  letI : FiniteDimensional k (canonicalFieldRestriction (k := k) K) := hK
  have hQ : FiniteDimensional k
      (IncidenceQuotientSimple.restrictRightQuotientModule (k := k) (S := G.Point)
        (quotientModuleOfHomModule (k := k) (S := G.Point) K)) :=
    (quotientRestrictionFieldIso (k := k) (S := G.Point) K).toLinearEquiv.finiteDimensional
  have hPDQ := IncidenceVertexProjectiveDimension.coordinateGrid_rightQuotient_hasProjectiveDimensionLE
    (k := k) (G := G) hn hG (quotientModuleOfHomModule (k := k) (S := G.Point) K) hQ
  letI : HasProjectiveDimensionLE
      (quotientModuleOfHomModule (k := k) (S := G.Point) K) (2 * n) := hPDQ
  exact ModuleCat.hasProjectiveDimensionLE_of_semiLinearEquiv
    (hookHomAlgEquivRightQuotient (k := k) (S := G.Point)).symm.toRingEquiv
    (quotientModuleSemilinearEquiv (k := k) (S := G.Point) K) (2 * n)

/-- The actual Hom module on an `n`-coordinate grid has ordinary projective
dimension at most `2*n-2`. -/
theorem coordinateGrid_homFunctor_obj_hasProjectiveDimensionLE
    {n : ℕ} (G : CoordinateGrid n) (hn : 1 ≤ n)
    (hG : ∀ i : Fin n, (G i).Nonempty)
    (M : PModule.{u,0,u} k G.Point)
    (hM : ∀ p, FiniteDimensional k (M.obj p)) :
    letI : BoundedOrder G.Point := coordinateGridBoundedOrder G hG
    HasProjectiveDimensionLE ((homFunctor (k := k) (S := G.Point)).obj M)
      (2 * n - 2) := by
  letI : BoundedOrder G.Point := coordinateGridBoundedOrder G hG
  letI : ∀ p, FiniteDimensional k (M.obj p) := hM
  have hcount := maxComplementCard_coordinateGrid_le G hG
  have hD : maxComplementCard (S := G.Point) - 1 ≤ 2 * n - 2 := by omega
  have hK : HasProjectiveDimensionLE
      (homCokernel (k := k) (S := G.Point) M) ((2 * n - 2) + 2) := by
    have hK' := coordinateGrid_homCokernel_hasProjectiveDimensionLE
      (k := k) G hn hG M hM
    convert hK' using 1 <;> omega
  exact TwoInjectiveHomDimension.hom_hasProjectiveDimensionLE_of_actualCokernel
    (k := k) (S := G.Point) M (2 * n - 2) hD hK

/-- Every supplied certified minimal rank-projective resolution of a
pointwise-finite module on the grid has zero terms strictly above `2*n-2`. -/
theorem coordinateGrid_minimalResolution_termAt_isZero
    {n : ℕ} (G : CoordinateGrid n) (hn : 1 ≤ n)
    (hG : ∀ i : Fin n, (G i).Nonempty)
    (M : PModule.{u,0,u} k G.Point)
    (hM : ∀ p, FiniteDimensional k (M.obj p))
    (R : MinimalFiniteRankProjectiveResolution (k := k) (M := M)) :
    ∀ j, 2 * n - 2 < j → IsZero (R.termAt j) := by
  letI : BoundedOrder G.Point := coordinateGridBoundedOrder G hG
  letI : ∀ p, FiniteDimensional k (M.obj p) := hM
  have hcount := maxComplementCard_coordinateGrid_le G hG
  have hD : maxComplementCard (S := G.Point) - 1 ≤ 2 * n - 2 := by omega
  have hK : HasProjectiveDimensionLE
      (homCokernel (k := k) (S := G.Point) M) ((2 * n - 2) + 2) := by
    have hK' := coordinateGrid_homCokernel_hasProjectiveDimensionLE
      (k := k) G hn hG M hM
    convert hK' using 1 <;> omega
  exact TwoInjectiveHomDimension.minimalResolution_termAt_isZero_of_actualCokernel
    (k := k) (S := G.Point) M R (2 * n - 2) hD hK

end

end TDA.Persistence.FiniteRankProjectiveHomQuotientDimension
