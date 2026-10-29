import TDA.Persistence.IncidenceQuotientBaseChange
import Mathlib.LinearAlgebra.Basis.Basic

/-!
# Examples for quotient base change

These examples exercise zero modules, regular projectives, actual restricted vertex modules,
the counit, the degree-zero derived comparison, and a nontrivial rational endomorphism.
-/

set_option autoImplicit false

namespace TDA.Persistence.IncidenceQuotientBaseChangeExamples

open CategoryTheory
open CategoryTheory.Limits
open TDA.Persistence.FiniteRankProjectiveEndAlgebra
open TDA.Persistence.FiniteRankProjectiveDiagonalIdealProjective
open TDA.Persistence.IncidenceQuotientSimple
open TDA.Persistence.IncidenceQuotientBaseChange

noncomputable section

local instance : Fintype Bool := Fintype.ofFinite Bool
local instance (p : Prop) : Decidable p := Classical.propDecidable p
local instance : Fintype (PairPoset Bool) :=
  Fintype.subtype (Finset.univ.filter fun ab : WithTop Bool × WithTop Bool => ab.1 ≤ ab.2)
    (by intro ab; simp)
local instance : DecidableLE (PairPoset Bool) := Classical.decRel _
local instance : DecidableLT (PairPoset Bool) := Classical.decRel _
local instance : LocallyFiniteOrder (PairPoset Bool) :=
  TDA.Persistence.FiniteRankProjectiveEndAlgebra.instLocallyFiniteOrderPairPoset
local instance : DecidableEq (PairPoset Bool) :=
  TDA.Persistence.FiniteRankProjectiveEndAlgebra.instDecidableEqPairPoset
local instance : Fintype (ComparablePair Bool) := Fintype.ofFinite _
local instance diagonalIdealTwoSidedBool {k : Type} [Field k] :
    (TDA.Persistence.FiniteRankProjectiveDiagonalIdealProjective.DiagonalIdeal
      (k := k) (S := Bool)).IsTwoSided :=
  diagonalIdeal_isTwoSided (k := k) (S := Bool)

private def boolStrictVertex : StrictVertex Bool :=
  ⟨⟨((false : WithTop Bool), (true : WithTop Bool)), by simp⟩, by simp⟩

/-- Extension of the zero module remains zero on underlying elements. -/
theorem zeroModule_extension_subsingleton {k : Type} [Field k] :
    ∀ x y : quotientModule (k := k) (S := Bool)
      (ModuleCat.of (RightIncidence (k := k) (S := Bool)) PUnit), x = y := by
  intro x y
  obtain ⟨m, rfl⟩ :=
    (relation (k := k) (S := Bool)
      (ModuleCat.of (RightIncidence (k := k) (S := Bool)) PUnit)).mkQ_surjective x
  obtain ⟨n, rfl⟩ :=
    (relation (k := k) (S := Bool)
      (ModuleCat.of (RightIncidence (k := k) (S := Bool)) PUnit)).mkQ_surjective y
  exact congrArg (fun a =>
    (relation (k := k) (S := Bool)
      (ModuleCat.of (RightIncidence (k := k) (S := Bool)) PUnit)).mkQ a)
      (Subsingleton.elim m n)

/-- The regular module is free, and hence projective, before quotient base change. -/
theorem bool_regularIncidence_projective {k : Type} [Field k] :
    Projective (regularRightIncidenceModule (k := k) (S := Bool)) := by
  exact ModuleCat.projective_of_free
    (Module.Basis.singleton Unit (RightIncidence (k := k) (S := Bool)))

/-- The quotient regular module is projective by projective transport and the regular isomorphism. -/
theorem bool_regularQuotient_projective {k : Type} [Field k] :
    Projective (regularRightQuotientModule (k := k) (S := Bool)) := by
  apply Projective.of_iso (regularExtensionIso (k := k) (S := Bool))
  exact Functor.projective_obj_of_projective (extensionFunctor (k := k) (S := Bool))
    (bool_regularIncidence_projective (k := k))

/-- The actual restricted Bool vertex is simple over every field. -/
theorem bool_restricted_vertex_is_simple {k : Type} [Field k] :
    IsSimpleModule (RightIncidence (k := k) (S := Bool))
      (RightVertexRestrictedModule (k := k) (S := Bool) boolStrictVertex) :=
  rightVertexRestrictedModule_isSimpleModule (k := k) (S := Bool) boolStrictVertex

/-- Base change of the restricted Bool vertex recovers the quotient vertex. -/
noncomputable def bool_vertex_basechange_iso {k : Type} [Field k] :
    (extensionFunctor (k := k) (S := Bool)).obj
      (RightVertexRestrictedModule (k := k) (S := Bool) boolStrictVertex) ≅
      RightVertexModule (k := k) (S := Bool) boolStrictVertex :=
  extensionRightVertexIso (k := k) (S := Bool) boolStrictVertex

/-- The canonical degree-zero derived comparison is an actual quotient-module isomorphism. -/
noncomputable def bool_vertex_derived_zero_iso {k : Type} [Field k] :
    (((extensionFunctor (k := k) (S := Bool)).leftDerived 0).obj
      (RightVertexRestrictedModule (k := k) (S := Bool) boolStrictVertex)) ≅
      RightVertexModule (k := k) (S := Bool) boolStrictVertex :=
  rightVertexExtensionDerivedZeroIso (k := k) (S := Bool) boolStrictVertex

local instance : Fintype Unit := Fintype.ofFinite Unit
local instance : Fintype (PairPoset Unit) :=
  Fintype.subtype (Finset.univ.filter fun ab : WithTop Unit × WithTop Unit => ab.1 ≤ ab.2)
    (by intro ab; simp)
local instance : DecidableLE (PairPoset Unit) := Classical.decRel _
local instance : DecidableLT (PairPoset Unit) := Classical.decRel _
local instance : LocallyFiniteOrder (PairPoset Unit) :=
  TDA.Persistence.FiniteRankProjectiveEndAlgebra.instLocallyFiniteOrderPairPoset
local instance : DecidableEq (PairPoset Unit) :=
  TDA.Persistence.FiniteRankProjectiveEndAlgebra.instDecidableEqPairPoset
local instance : Fintype (ComparablePair Unit) := Fintype.ofFinite _
local instance diagonalIdealTwoSidedUnit {k : Type} [Field k] :
    (TDA.Persistence.FiniteRankProjectiveDiagonalIdealProjective.DiagonalIdeal
      (k := k) (S := Unit)).IsTwoSided :=
  diagonalIdeal_isTwoSided (k := k) (S := Unit)

private def unitStrictVertex : StrictVertex Unit :=
  ⟨⟨((), ⊤), le_top⟩, by simp⟩

/-- The rational singleton vertex counit sends a class to its representative. -/
theorem rational_unit_counit_class
    (t : RightVertexModule (k := ℚ) (S := Unit) unitStrictVertex) :
    (extensionRightVertexIso (k := ℚ) (S := Unit) unitStrictVertex).hom
      ((relation (k := ℚ) (S := Unit)
        (RightVertexRestrictedModule (k := ℚ) (S := Unit) unitStrictVertex)).mkQ t) = t :=
  extensionRightVertexIso_hom_mkQ (k := ℚ) (S := Unit) unitStrictVertex t

/-- The rational singleton vertex has the canonical C-linear derived-zero comparison. -/
noncomputable def rational_unit_vertex_derived_zero_iso :
    (((extensionFunctor (k := ℚ) (S := Unit)).leftDerived 0).obj
      (RightVertexRestrictedModule (k := ℚ) (S := Unit) unitStrictVertex)) ≅
      RightVertexModule (k := ℚ) (S := Unit) unitStrictVertex :=
  rightVertexExtensionDerivedZeroIso (k := ℚ) (S := Unit) unitStrictVertex

local instance unitVertexModuleRational :
    Module ℚ (RightVertexModule (k := ℚ) (S := Unit) unitStrictVertex) := by
  exact Module.compHom (RightVertexModule (k := ℚ) (S := Unit) unitStrictVertex)
    (algebraMap ℚ (TDA.Persistence.IncidenceQuotientSimple.RightQuotient
      (k := ℚ) (S := Unit)))

local instance unitVertexModuleQuotient :
    Module (TDA.Persistence.IncidenceQuotientSimple.RightQuotient
      (k := ℚ) (S := Unit)) ℚ :=
  (RightVertexModule (k := ℚ) (S := Unit) unitStrictVertex).isModule

/-- Multiplication by two gives a concrete nontrivial map of the rational right vertex. -/
def rationalUnitDoubleLinearMap :
    RightVertexModule (k := ℚ) (S := Unit) unitStrictVertex →ₗ[
      TDA.Persistence.IncidenceQuotientBaseChange.RightQuotient (k := ℚ) (S := Unit)]
      RightVertexModule (k := ℚ) (S := Unit) unitStrictVertex where
  toFun := fun x => x + x
  map_add' := by intro x y; abel
  map_smul' := by
    intro c x
    simp [smul_add]

def rationalUnitDoubleMap :
    RightVertexModule (k := ℚ) (S := Unit) unitStrictVertex ⟶
      RightVertexModule (k := ℚ) (S := Unit) unitStrictVertex :=
  ModuleCat.ofHom rationalUnitDoubleLinearMap

@[simp] theorem rationalUnitDoubleMap_apply_one :
    rationalUnitDoubleMap.hom (1 : ℚ) = (2 : ℚ) := by
  change (1 : ℚ) + (1 : ℚ) = (2 : ℚ)
  norm_num

theorem rationalUnitDoubleMap_ne_identity :
    rationalUnitDoubleMap ≠ 𝟙 _ := by
  intro h
  have h1 := congrArg (fun f :
      RightVertexModule (k := ℚ) (S := Unit) unitStrictVertex ⟶
        RightVertexModule (k := ℚ) (S := Unit) unitStrictVertex => f.hom (1 : ℚ)) h
  rw [rationalUnitDoubleMap_apply_one] at h1
  change (2 : ℚ) = (1 : ℚ) at h1
  norm_num at h1

/-- The induced quotient-module map is natural with respect to this nontrivial endomorphism. -/
theorem rationalUnitDoubleMap_extension_naturality :
    (extensionFunctor (k := ℚ) (S := Unit)).map
        ((ModuleCat.restrictScalars (quotientHom (k := ℚ) (S := Unit))).map
          rationalUnitDoubleMap) ≫
      (extensionRightVertexIso (k := ℚ) (S := Unit) unitStrictVertex).hom =
    (extensionRightVertexIso (k := ℚ) (S := Unit) unitStrictVertex).hom ≫
      rationalUnitDoubleMap := by
  simpa [extensionRightVertexIso, Functor.comp_map] using
    (extensionRestrictionIso (k := ℚ) (S := Unit)).hom.naturality
      rationalUnitDoubleMap

end

end TDA.Persistence.IncidenceQuotientBaseChangeExamples
