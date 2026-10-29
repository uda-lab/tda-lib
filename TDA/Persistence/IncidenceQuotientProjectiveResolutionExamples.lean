import TDA.Persistence.IncidenceQuotientProjectiveResolution
import Mathlib.CategoryTheory.Abelian.Projective.Resolution

/-!
# Examples for quotient projective resolutions and dimension comparison

These consumers cover the zero object, the regular projective boundary, and an actual rational
strict vertex together with the augmentation and support-transport laws.
-/

set_option autoImplicit false

namespace TDA.Persistence.IncidenceQuotientProjectiveResolutionExamples

open CategoryTheory
open CategoryTheory.Limits
open TDA.Persistence.FiniteRankProjectiveEndAlgebra
open TDA.Persistence.FiniteRankProjectiveDiagonalIdealProjective
open TDA.Persistence.IncidenceQuotientSimple
open TDA.Persistence.IncidenceQuotientBaseChange
open TDA.Persistence.IncidenceQuotientColumnAction
open TDA.Persistence.IncidenceQuotientProjectiveResolution

noncomputable section

local instance : Fintype Unit := Fintype.ofFinite Unit
local instance (p : Prop) : Decidable p := Classical.propDecidable p
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

private abbrev unitVertexQuotient :=
  RightVertexModule (k := ℚ) (S := Unit) unitStrictVertex

private abbrev unitVertexRestricted :=
  RightVertexRestrictedModule (k := ℚ) (S := Unit) unitStrictVertex

private abbrev unitZeroQuotient :
    ModuleCat.{0} (TDA.Persistence.IncidenceQuotientBaseChange.RightQuotient
      (k := ℚ) (S := Unit)) :=
  ModuleCat.of (TDA.Persistence.IncidenceQuotientBaseChange.RightQuotient
    (k := ℚ) (S := Unit)) PUnit

private abbrev unitZeroRestricted :=
  (ModuleCat.restrictScalars (quotientHom (k := ℚ) (S := Unit))).obj unitZeroQuotient

/-- A concrete actual projective resolution of the rational strict vertex after restriction. -/
noncomputable def rational_unit_vertex_projectiveResolution :
    ProjectiveResolution unitVertexRestricted :=
  ProjectiveResolution.of unitVertexRestricted

/-- The corresponding actual augmented projective resolution over the quotient ring. -/
noncomputable def rational_unit_vertex_extendedProjectiveResolution :
    ProjectiveResolution unitVertexQuotient :=
  extensionProjectiveResolution (k := ℚ) (S := Unit) unitVertexQuotient
    rational_unit_vertex_projectiveResolution

/-- Both sides of the extended-natural comparison for the zero module are bottom. -/
theorem rational_unit_zero_projective_dimensions_are_bot :
    CategoryTheory.projectiveDimension unitZeroQuotient = ⊥ ∧
      CategoryTheory.projectiveDimension unitZeroRestricted = ⊥ := by
  have hzero : IsZero unitZeroQuotient :=
    ModuleCat.isZero_iff_subsingleton.mpr inferInstance
  have hrestricted : IsZero unitZeroRestricted :=
    Functor.map_isZero
      (ModuleCat.restrictScalars (quotientHom (k := ℚ) (S := Unit))) hzero
  exact ⟨(CategoryTheory.projectiveDimension_eq_bot_iff unitZeroQuotient).2 hzero,
    (CategoryTheory.projectiveDimension_eq_bot_iff unitZeroRestricted).2 hrestricted⟩

/-- The general dimension comparison specializes to the zero quotient module. -/
theorem rational_unit_zero_projectiveDimension_le_restriction :
    CategoryTheory.projectiveDimension unitZeroQuotient ≤
      CategoryTheory.projectiveDimension unitZeroRestricted :=
  projectiveDimension_le_restriction (k := ℚ) (S := Unit) unitZeroQuotient

/-- The regular right-incidence module is projective. -/
theorem rational_unit_regular_incidence_projective :
    Projective (regularRightIncidenceModule (k := ℚ) (S := Unit)) :=
  ModuleCat.projective_of_free
    (Module.Basis.singleton Unit (RightIncidence (k := ℚ) (S := Unit)))

/-- The projective-dimension transport theorem covers the degree-zero projective boundary. -/
theorem rational_unit_regular_extension_hasProjectiveDimensionLE_zero :
    HasProjectiveDimensionLE
      ((extensionFunctor (k := ℚ) (S := Unit)).obj
        (regularRightIncidenceModule (k := ℚ) (S := Unit))) 0 :=
  extension_hasProjectiveDimensionLE_of_assemble_injective
    (k := ℚ) (S := Unit) (regularRightIncidenceModule (k := ℚ) (S := Unit)) 0
    (assembleAction_projective_injective (k := ℚ) (S := Unit)
      (regularRightIncidenceModule (k := ℚ) (S := Unit)))
    ((projective_iff_hasProjectiveDimensionLE_zero
      (regularRightIncidenceModule (k := ℚ) (S := Unit))).mp
      rational_unit_regular_incidence_projective)

/-- For the actual rational strict vertex, quotient projective dimension is bounded by the
restricted incidence-module dimension. -/
theorem rational_unit_vertex_projectiveDimension_le_restriction :
    CategoryTheory.projectiveDimension unitVertexQuotient ≤
      CategoryTheory.projectiveDimension unitVertexRestricted :=
  projectiveDimension_le_restriction (k := ℚ) (S := Unit) unitVertexQuotient

/-- The augmented resolution's map on a representative class is the original augmentation. -/
theorem rational_unit_vertex_augmentation_class
    (x : rational_unit_vertex_projectiveResolution.complex.X 0) :
    (rational_unit_vertex_extendedProjectiveResolution.π.f 0).hom
        ((relation (k := ℚ) (S := Unit)
          (rational_unit_vertex_projectiveResolution.complex.X 0)).mkQ x) =
      (rational_unit_vertex_projectiveResolution.π.f 0).hom x :=
  extensionProjectiveResolution_augmentation_class
    (k := ℚ) (S := Unit) unitVertexQuotient
    rational_unit_vertex_projectiveResolution x

/-- A zero term in an actual restricted strict-vertex resolution stays zero after augmentation. -/
theorem rational_unit_vertex_resolution_zero_term
    (n : ℕ)
    (h : IsZero (rational_unit_vertex_projectiveResolution.complex.X n)) :
    IsZero (rational_unit_vertex_extendedProjectiveResolution.complex.X n) :=
  extensionProjectiveResolution_isZero_term
    (k := ℚ) (S := Unit) unitVertexQuotient
    rational_unit_vertex_projectiveResolution n h

/-- Any supplied termwise vanishing bound on a restricted strict-vertex resolution is transported
to its actual augmented quotient resolution. -/
theorem rational_unit_vertex_resolution_zero_above
    (d : ℕ)
    (h : ∀ n, d < n → IsZero
      (rational_unit_vertex_projectiveResolution.complex.X n)) :
    ∀ n, d < n → IsZero (rational_unit_vertex_extendedProjectiveResolution.complex.X n) :=
  extensionProjectiveResolution_isZero_above
    (k := ℚ) (S := Unit) unitVertexQuotient
    rational_unit_vertex_projectiveResolution d h

end

end TDA.Persistence.IncidenceQuotientProjectiveResolutionExamples
