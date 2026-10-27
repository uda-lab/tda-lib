import TDA.Persistence.IncidenceVertexRepresentation
import TDA.Persistence.GradedFree
import TDA.Persistence.FiniteRankProjectiveDiagonalIdealProjective
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Finsupp.Pi

/-!
# The regular incidence module as a graded free vertex representation

The vertex representation of the actual regular right-incidence module is the
graded free module with one generator born at each interval pair. This
identification supplies ordinary projectivity of the regular vertex module
and finite-dimensionality of the regular incidence module over its
coefficient field.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence.IncidenceRegularVertex

open CategoryTheory CategoryTheory.Limits
open TDA.Persistence.FiniteRankProjectiveEndAlgebra
open TDA.Persistence.IncidenceVertexRepresentation
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

abbrev RightIncidence := (FiniteRankProjectiveEndAlgebra.Incidence (k := k) (S := S))ᵐᵒᵖ
abbrev regular := IncidenceQuotientBaseChange.regularRightIncidenceModule (k := k) (S := S)

/-- One free generator at each actual interval-pair vertex. -/
abbrev generators : GradedFree.GradedGenerators ((FiniteRankProjectiveEndAlgebra.PairPoset S)) :=
  ⟨(FiniteRankProjectiveEndAlgebra.PairPoset S), id⟩

/-- The graded free persistence module on the interval-pair vertices. -/
abbrev freeVertexModule : PModule.{u,0,u} k (FiniteRankProjectiveEndAlgebra.PairPoset S) :=
  GradedFree.module (R := k) (generators (S := S))

-- On the regular module, use the actual restricted-scalars action already
-- carried by the vertex-fiber construction.
local instance : Module k (RightIncidence (k := k) (S := S)) :=
  (restrictedKModule (k := k) (S := S) (regular (k := k) (S := S))).isModule
local instance : SMul k (RightIncidence (k := k) (S := S)) :=
  (restrictedKModule (k := k) (S := S) (regular (k := k) (S := S))).isModule.toDistribMulAction.toDistribSMul.toSMul

private def regularCoefficients :
    restrictedKModule (k := k) (S := S) (regular (k := k) (S := S)) →ₗ[k]
      (FiniteRankProjectiveEndAlgebra.PairPoset S) →
        (FiniteRankProjectiveEndAlgebra.PairPoset S) → k where
  toFun r a b := (MulOpposite.unop (r : RightIncidence (k := k) (S := S)) :
    FiniteRankProjectiveEndAlgebra.Incidence (k := k) (S := S)) a b
  map_add' r s := by ext a b; rfl
  map_smul' c r := by
    ext a b
    have hscalar : c • r = algebraMap k (RightIncidence (k := k) (S := S)) c • r := rfl
    calc
      _ = (MulOpposite.unop
          (algebraMap k (RightIncidence (k := k) (S := S)) c *
            (r : RightIncidence (k := k) (S := S)))) a b :=
        congrArg (fun x : restrictedKModule (k := k) (S := S)
          (regular (k := k) (S := S)) => (MulOpposite.unop x) a b) hscalar
      _ = _ := by
        rw [MulOpposite.unop_mul, MulOpposite.algebraMap_apply, MulOpposite.unop_op,
          ← Algebra.commutes, ← Algebra.smul_def]
        rfl

private theorem regularCoefficients_injective : Function.Injective
    (regularCoefficients (k := k) (S := S)) := by
  intro x y h
  apply MulOpposite.unop_injective
  apply IncidenceAlgebra.ext
  intro a b hab
  exact congrFun (congrFun h a) b

/-- The actual regular right-incidence module is finite-dimensional over the
canonical restricted field scalars. -/
theorem regular_finiteDimensional :
    FiniteDimensional k
      (restrictedKModule (k := k) (S := S) (regular (k := k) (S := S))) := by
  letI : FiniteDimensional k
      ((FiniteRankProjectiveEndAlgebra.PairPoset S) →
        (FiniteRankProjectiveEndAlgebra.PairPoset S) → k) := inferInstance
  exact FiniteDimensional.of_injective (regularCoefficients (k := k) (S := S))
    (regularCoefficients_injective (k := k) (S := S))

private def columnAt (q : (FiniteRankProjectiveEndAlgebra.PairPoset S)) :
    restrictedKModule (k := k) (S := S) (regular (k := k) (S := S)) →ₗ[k]
      (FiniteRankProjectiveEndAlgebra.PairPoset S) → k where
  toFun r a := (MulOpposite.unop (r : RightIncidence (k := k) (S := S)) :
    FiniteRankProjectiveEndAlgebra.Incidence (k := k) (S := S)) a q
  map_add' r s := by ext a; rfl
  map_smul' c r := by
    ext a
    have hscalar : c • r = algebraMap k (RightIncidence (k := k) (S := S)) c • r :=
      rfl
    calc
      _ = (MulOpposite.unop
          (algebraMap k (RightIncidence (k := k) (S := S)) c *
            (r : RightIncidence (k := k) (S := S)))) a q :=
        congrArg (fun x : restrictedKModule (k := k) (S := S)
          (regular (k := k) (S := S)) => (MulOpposite.unop x) a q) hscalar
      _ = _ := by
        rw [MulOpposite.unop_mul, MulOpposite.algebraMap_apply, MulOpposite.unop_op,
          ← Algebra.commutes, ← Algebra.smul_def]
        rfl

private def columnFinsupp (q : (FiniteRankProjectiveEndAlgebra.PairPoset S)) :
    restrictedKModule (k := k) (S := S) (regular (k := k) (S := S)) →ₗ[k]
      (FiniteRankProjectiveEndAlgebra.PairPoset S) →₀ k :=
  (Finsupp.linearEquivFunOnFinite k k (FiniteRankProjectiveEndAlgebra.PairPoset S)).symm.toLinearMap.comp
    (columnAt (k := k) (S := S) q)

private theorem columnFinsupp_apply (q : (FiniteRankProjectiveEndAlgebra.PairPoset S))
    (r : restrictedKModule (k := k) (S := S) (regular (k := k) (S := S)))
    (a : (FiniteRankProjectiveEndAlgebra.PairPoset S)) :
    columnFinsupp (k := k) (S := S) q r a =
      (MulOpposite.unop (r : RightIncidence (k := k) (S := S)) :
        FiniteRankProjectiveEndAlgebra.Incidence (k := k) (S := S)) a q := by
  simp [columnFinsupp, columnAt]

private theorem columnFinsupp_supported (q : (FiniteRankProjectiveEndAlgebra.PairPoset S))
    (r : restrictedKModule (k := k) (S := S) (regular (k := k) (S := S))) :
    columnFinsupp (k := k) (S := S) q r ∈
      GradedFree.fiber (R := k) (generators (S := S)) q := by
  change columnFinsupp (k := k) (S := S) q r ∈
    Finsupp.supported k k {a : (FiniteRankProjectiveEndAlgebra.PairPoset S) | a ≤ q}
  rw [Finsupp.mem_supported']
  intro a ha
  change ((MulOpposite.unop (r : RightIncidence (k := k) (S := S)) :
    FiniteRankProjectiveEndAlgebra.Incidence (k := k) (S := S)) a q) = 0
  exact IncidenceAlgebra.apply_eq_zero_of_not_le ha _

private def columnMap (q : (FiniteRankProjectiveEndAlgebra.PairPoset S)) :
    vertexFiber (k := k) (S := S) (regular (k := k) (S := S)) q →ₗ[k]
      GradedFree.fiber (R := k) (generators (S := S)) q :=
  ((columnFinsupp (k := k) (S := S) q).codRestrict
    (GradedFree.fiber (R := k) (generators (S := S)) q)
    (columnFinsupp_supported (k := k) (S := S) q)).comp
      (vertexFiber (k := k) (S := S) (regular (k := k) (S := S)) q).subtype

private theorem columnMap_apply (q : (FiniteRankProjectiveEndAlgebra.PairPoset S))
    (x : vertexFiber (k := k) (S := S) (regular (k := k) (S := S)) q)
    (a : (FiniteRankProjectiveEndAlgebra.PairPoset S)) :
    ((columnMap (k := k) (S := S) q x :
      GradedFree.fiber (R := k) (generators (S := S)) q).val a) =
      (MulOpposite.unop (x.val : RightIncidence (k := k) (S := S)) :
        FiniteRankProjectiveEndAlgebra.Incidence (k := k) (S := S)) a q := by
  rfl

private theorem regular_fixed_eq_column
    (q : (FiniteRankProjectiveEndAlgebra.PairPoset S)) (x : vertexFiber (k := k) (S := S)
      (regular (k := k) (S := S)) q) :
    ((MulOpposite.unop (x : RightIncidence (k := k) (S := S)) :
      FiniteRankProjectiveEndAlgebra.Incidence (k := k) (S := S)) *
        FiniteRankProjectiveEndAlgebra.delta (k := k) (S := S) q q le_rfl) =
      MulOpposite.unop (x : RightIncidence (k := k) (S := S)) := by
  have hx := (mem_vertexFiber_iff (k := k) (S := S)
    (regular (k := k) (S := S)) q x).1 x.property
  change IncidenceQuotientBaseChange.rightIncidenceMatrixUnit
      (k := k) (S := S) q q le_rfl * x.val = x.val at hx
  have hu := congrArg MulOpposite.unop hx
  simpa [IncidenceQuotientBaseChange.rightIncidenceMatrixUnit,
    MulOpposite.unop_mul] using hu

private theorem regular_fixed_zero_off_column
    (q : (FiniteRankProjectiveEndAlgebra.PairPoset S)) (x : vertexFiber (k := k) (S := S)
      (regular (k := k) (S := S)) q) {a t : (FiniteRankProjectiveEndAlgebra.PairPoset S)} (ht : t ≠ q) :
    (MulOpposite.unop (x : RightIncidence (k := k) (S := S)) :
      FiniteRankProjectiveEndAlgebra.Incidence (k := k) (S := S)) a t = 0 := by
  have h := congrArg (fun f : FiniteRankProjectiveEndAlgebra.Incidence
    (k := k) (S := S) => f a t)
      (regular_fixed_eq_column (k := k) (S := S) q x)
  rw [FiniteRankProjectiveDiagonalIdealProjective.mul_delta_right_apply_column
    (hdq := le_rfl)] at h
  simpa [ht] using h.symm

private def columnNaturalTransformation :
    (IncidenceVertexRepresentation.vertexFunctor (k := k) (S := S)).obj
      (regular (k := k) (S := S)) ⟶ freeVertexModule (k := k) (S := S) where
  app q := ModuleCat.ofHom (columnMap (k := k) (S := S) q)
  naturality p q hpq := by
    apply ModuleCat.hom_ext
    change (columnMap (k := k) (S := S) q).comp
        (vertexStructureMap (k := k) (S := S) (regular (k := k) (S := S))
          (leOfHom hpq)) =
      (Submodule.inclusion (GradedFree.fiber_mono (R := k)
        (generators (S := S)) (leOfHom hpq))).comp
          (columnMap (k := k) (S := S) p)
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    apply Finsupp.ext
    intro a
    change (columnMap (k := k) (S := S) q
      (vertexStructureMap (k := k) (S := S) (regular (k := k) (S := S))
        (leOfHom hpq) x)).val a = (columnMap (k := k) (S := S) p x).val a
    rw [columnMap_apply, columnMap_apply]
    change (MulOpposite.unop
      (IncidenceQuotientBaseChange.rightIncidenceMatrixUnit (k := k) (S := S)
        p q (leOfHom hpq) * (x.val : RightIncidence (k := k) (S := S)))) a q = _
    rw [MulOpposite.unop_mul, IncidenceQuotientBaseChange.rightIncidenceMatrixUnit,
      MulOpposite.unop_op]
    simpa using FiniteRankProjectiveDiagonalIdealProjective.mul_delta_right_apply_column
      (k := k) (S := S) (MulOpposite.unop x.val) p q a q (leOfHom hpq)

private def alpha : freeVertexModule (k := k) (S := S) ⟶
    (IncidenceVertexRepresentation.vertexFunctor (k := k) (S := S)).obj
      (regular (k := k) (S := S)) :=
  GradedFree.lift (R := k) (generators (S := S))
    ((IncidenceVertexRepresentation.vertexFunctor (k := k) (S := S)).obj
      (regular (k := k) (S := S)))
    (fun p => (projectToVertexFiber (k := k) (S := S)
      (regular (k := k) (S := S)) p 1 :
      VertexSpace (k := k) (S := S) (regular (k := k) (S := S)) p))

private theorem columnMap_birth (p : (FiniteRankProjectiveEndAlgebra.PairPoset S)) :
    (columnNaturalTransformation (k := k) (S := S)).app p
      (projectToVertexFiber (k := k) (S := S)
        (regular (k := k) (S := S)) p 1) =
        GradedFree.birth (R := k) (generators (S := S)) p := by
  have hproj :
      (projectToVertexFiber (k := k) (S := S)
        (regular (k := k) (S := S)) p 1 : RightIncidence (k := k) (S := S)) =
        IncidenceQuotientBaseChange.rightIncidenceMatrixUnit (k := k) (S := S)
          p p le_rfl := by
    change IncidenceVertexRepresentation.diagonalProjector
      (k := k) (S := S) (regular (k := k) (S := S)) p 1 = _
    change IncidenceQuotientBaseChange.rightIncidenceMatrixUnit
      (k := k) (S := S) p p le_rfl • (1 : RightIncidence (k := k) (S := S)) = _
    simp
  change columnMap (k := k) (S := S) p
      (projectToVertexFiber (k := k) (S := S) (regular (k := k) (S := S)) p 1) = _
  apply Subtype.ext
  apply Finsupp.ext
  intro a
  calc
    _ = (MulOpposite.unop
        ((projectToVertexFiber (k := k) (S := S)
          (regular (k := k) (S := S)) p 1).val)) a p :=
      columnMap_apply (k := k) (S := S) p _ a
    _ = (FiniteRankProjectiveEndAlgebra.delta (k := k) (S := S) p p le_rfl) a p := by
      exact congrArg (fun r : RightIncidence (k := k) (S := S) =>
        (MulOpposite.unop r) a p) hproj
    _ = _ := by
      change (FiniteRankProjectiveEndAlgebra.delta (k := k) (S := S) p p le_rfl) a p =
        (Finsupp.single p (1 : k)) a
      simp [FiniteRankProjectiveEndAlgebra.delta_apply, Finsupp.single_apply, eq_comm]

private theorem alpha_column_id :
    alpha (k := k) (S := S) ≫ columnNaturalTransformation (k := k) (S := S) =
      𝟙 (freeVertexModule (k := k) (S := S)) := by
  calc
    alpha (k := k) (S := S) ≫ columnNaturalTransformation (k := k) (S := S) =
        GradedFree.lift (R := k) (generators (S := S))
          (freeVertexModule (k := k) (S := S))
          (fun p => GradedFree.birth (R := k) (generators (S := S)) p) := by
      apply GradedFree.lift_unique (R := k) (generators (S := S))
      intro p
      change (columnNaturalTransformation (k := k) (S := S)).app p
        ((alpha (k := k) (S := S)).app p
          (GradedFree.birth (R := k) (generators (S := S)) p)) = _
      have h := GradedFree.lift_birth (R := k) (generators (S := S))
        ((vertexFunctor (k := k) (S := S)).obj (regular (k := k) (S := S)))
        (fun p => projectToVertexFiber (k := k) (S := S)
          (regular (k := k) (S := S)) p 1) p
      exact (congrArg (fun x => (columnNaturalTransformation (k := k) (S := S)).app p x)
        h).trans (columnMap_birth (k := k) (S := S) p)
    _ = 𝟙 (freeVertexModule (k := k) (S := S)) := by
      symm
      apply GradedFree.lift_unique (R := k) (generators (S := S))
      intro p
      simp [GradedFree.lift_birth]

private theorem columnMap_injective (p : (FiniteRankProjectiveEndAlgebra.PairPoset S)) :
    Function.Injective (columnMap (k := k) (S := S) p) := by
  intro x y hxy
  apply Subtype.ext
  apply MulOpposite.unop_injective
  apply IncidenceAlgebra.ext
  intro a t hat
  by_cases ht : t = p
  · subst t
    have hcol := congrArg (fun z : (freeVertexModule (k := k) (S := S)).obj p =>
      z.val a) hxy
    exact (columnMap_apply (k := k) (S := S) p x a).symm.trans
      (hcol.trans (columnMap_apply (k := k) (S := S) p y a))
  · rw [regular_fixed_zero_off_column (k := k) (S := S) p x ht,
        regular_fixed_zero_off_column (k := k) (S := S) p y ht]

private theorem columnMap_surjective (p : (FiniteRankProjectiveEndAlgebra.PairPoset S)) :
    Function.Surjective (columnMap (k := k) (S := S) p) := by
  intro y
  refine ⟨(alpha (k := k) (S := S)).app p y, ?_⟩
  have h := congrArg (fun f => f.app p y) (alpha_column_id (k := k) (S := S))
  change (columnNaturalTransformation (k := k) (S := S)).app p
      ((alpha (k := k) (S := S)).app p y) = y at h
  exact h

/-- The actual vertex representation of the regular right-incidence module is
the graded free module with one generator born at each interval pair. -/
noncomputable def regularVertexIso :
    (IncidenceVertexRepresentation.vertexFunctor (k := k) (S := S)).obj
      (regular (k := k) (S := S)) ≅ freeVertexModule (k := k) (S := S) := by
  letI : ∀ p : (FiniteRankProjectiveEndAlgebra.PairPoset S), Mono ((columnNaturalTransformation (k := k) (S := S)).app p) :=
    fun p => (ModuleCat.mono_iff_injective _).mpr
      (columnMap_injective (k := k) (S := S) p)
  letI : ∀ p : (FiniteRankProjectiveEndAlgebra.PairPoset S), Epi ((columnNaturalTransformation (k := k) (S := S)).app p) :=
    fun p => (ModuleCat.epi_iff_surjective _).mpr
      (columnMap_surjective (k := k) (S := S) p)
  letI : ∀ p : (FiniteRankProjectiveEndAlgebra.PairPoset S), IsIso ((columnNaturalTransformation (k := k) (S := S)).app p) :=
    fun _ => isIso_of_mono_of_epi _
  letI : IsIso (columnNaturalTransformation (k := k) (S := S)) :=
    NatIso.isIso_of_isIso_app _
  exact asIso (columnNaturalTransformation (k := k) (S := S))

/-- The graded free vertex module is projective in the actual persistence-module category. -/
instance freeVertexModule_projective :
    Projective (freeVertexModule (k := k) (S := S)) where
  factors {E X} f e he := by
    letI : Epi e := he
    have hsurj : ∀ p : (FiniteRankProjectiveEndAlgebra.PairPoset S), Function.Surjective (e.app p) := fun p =>
      (ModuleCat.epi_iff_surjective _).mp
        ((NatTrans.epi_iff_epi_app e).mp inferInstance p)
    exact GradedFree.exists_lift_of_surjective (R := k) (generators (S := S))
      e hsurj f

/-- The vertex image of the actual regular right-incidence module is projective. -/
theorem regularVertex_projective :
    Projective ((IncidenceVertexRepresentation.vertexFunctor (k := k) (S := S)).obj
      (regular (k := k) (S := S))) := by
  exact Projective.of_iso (regularVertexIso (k := k) (S := S)).symm
    (freeVertexModule_projective (k := k) (S := S))

/-- The actual finite free right-incidence module of rank `n`. -/
abbrev finiteFreeModule (n : ℕ) : ModuleCat.{u} (RightIncidence (k := k) (S := S)) :=
  ModuleCat.of (RightIncidence (k := k) (S := S)) (Fin n → RightIncidence (k := k) (S := S))

/-- The ordinary finite free right-incidence module is projective. -/
instance finiteFreeModule_projective (n : ℕ) :
    Projective (finiteFreeModule (k := k) (S := S) n) := by
  exact ModuleCat.projective_of_free (Pi.basisFun (RightIncidence (k := k) (S := S)) (Fin n))

private def regularFamily (n : ℕ) : Fin n → ModuleCat.{u} (RightIncidence (k := k) (S := S)) :=
  fun _ => regular (k := k) (S := S)

private abbrev regularULiftFamily (n : ℕ) : ULift.{u} (Fin n) →
    ModuleCat.{u} (RightIncidence (k := k) (S := S)) :=
  fun _ => regular (k := k) (S := S)

/-- The vertex image of a finite free module is the finite biproduct of the
actual regular vertex modules. -/
noncomputable def finiteFreeVertexBiproductIso (n : ℕ) :
    (⨁ fun i : Fin n => (IncidenceVertexRepresentation.vertexFunctor (k := k) (S := S)).obj
      (regularFamily (k := k) (S := S) n i)) ≅
      (IncidenceVertexRepresentation.vertexFunctor (k := k) (S := S)).obj
        (finiteFreeModule (k := k) (S := S) n) := by
  exact ((IncidenceVertexRepresentation.vertexFunctor (k := k) (S := S)).mapBiproduct
      (regularFamily (k := k) (S := S) n)).symm ≪≫
    (IncidenceVertexRepresentation.vertexFunctor (k := k) (S := S)).mapIso
      (ModuleCat.biproductIsoPi (regularFamily (k := k) (S := S) n))

/-- Every finite free module has a projective vertex image. -/
theorem finiteFreeVertex_projective (n : ℕ) :
    Projective ((IncidenceVertexRepresentation.vertexFunctor (k := k) (S := S)).obj
      (finiteFreeModule (k := k) (S := S) n)) := by
  let fU : ULift.{u} (Fin n) → PModule.{u,0,u} k (FiniteRankProjectiveEndAlgebra.PairPoset S) :=
    fun i => (IncidenceVertexRepresentation.vertexFunctor (k := k) (S := S)).obj
      (regularULiftFamily (k := k) (S := S) n i)
  let f : Fin n → PModule.{u,0,u} k (FiniteRankProjectiveEndAlgebra.PairPoset S) :=
    fun i => (IncidenceVertexRepresentation.vertexFunctor (k := k) (S := S)).obj
      (regularFamily (k := k) (S := S) n i)
  letI : HasBiproduct fU := inferInstance
  letI : ∀ i : ULift.{u} (Fin n), Projective (fU i) := fun _ =>
    regularVertex_projective (k := k) (S := S)
  have hU : Projective (⨁ fU) :=
    CategoryTheory.Projective.instBiproduct fU
  have e : (⨁ fU) ≅ ⨁ f :=
    biproduct.whiskerEquiv (f := fU) (g := f) Equiv.ulift
      (fun i => Iso.refl (f i.down))
  have hF : Projective (⨁ f) := Projective.of_iso e hU
  exact Projective.of_iso (finiteFreeVertexBiproductIso (k := k) (S := S) n) hF

/-- The actual finite free right-incidence module is finite-dimensional over
the canonical restricted field scalars. -/
theorem finiteFreeModule_finiteDimensional (n : ℕ) :
    FiniteDimensional k
      (restrictedKModule (k := k) (S := S) (finiteFreeModule (k := k) (S := S) n)) := by
  let e : restrictedKModule (k := k) (S := S)
        (finiteFreeModule (k := k) (S := S) n) ≃ₗ[k]
      (Fin n → restrictedKModule (k := k) (S := S) (regular (k := k) (S := S))) := {
    toFun := fun x i => x i
    invFun := fun f i => f i
    left_inv := by intro x; rfl
    right_inv := by intro x; rfl
    map_add' := by intro x y; rfl
    map_smul' := by intro c x; ext i; rfl
  }
  letI : FiniteDimensional k
      (restrictedKModule (k := k) (S := S) (regular (k := k) (S := S))) :=
    regular_finiteDimensional (k := k) (S := S)
  haveI : FiniteDimensional k
      (Fin n → restrictedKModule (k := k) (S := S) (regular (k := k) (S := S))) := inferInstance
  exact e.finiteDimensional

/-- The vertex functor preserves actual epimorphisms. -/
instance vertexFunctor_preservesEpimorphisms :
    Functor.PreservesEpimorphisms
      (IncidenceVertexRepresentation.vertexFunctor (k := k) (S := S)) where
  preserves {M N} f hf := by
    apply (NatTrans.epi_iff_epi_app _).2
    intro p
    apply (ModuleCat.epi_iff_surjective _).2
    apply (IncidenceVertexRepresentation.rightIncidenceMap_surjective_iff_vertexFibers
      (k := k) (S := S) f).mp
    exact (ModuleCat.epi_iff_surjective _).mp hf

/-- Ordinary projectivity of a vertex representation reflects to its actual
right-incidence module, using full faithfulness and epimorphism preservation. -/
theorem projective_of_vertex_projective
    (M : ModuleCat.{u} (RightIncidence (k := k) (S := S)))
    (hM : Projective ((IncidenceVertexRepresentation.vertexFunctor (k := k) (S := S)).obj M)) :
    Projective M :=
  Functor.projective_of_map_projective
    (IncidenceVertexRepresentation.vertexFunctor (k := k) (S := S)) hM

end

end TDA.Persistence.IncidenceRegularVertex
