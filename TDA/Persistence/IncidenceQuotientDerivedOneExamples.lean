import TDA.Persistence.IncidenceQuotientDerivedOne

/-!
# Examples for degree-one quotient-extension exactness

The fixtures specialize the all-module vanishing to the zero module and to an actual strict
vertex over the singleton lattice.
-/

set_option autoImplicit false

namespace TDA.Persistence.IncidenceQuotientDerivedOneExamples

open CategoryTheory
open CategoryTheory.Limits
open TDA.Persistence.FiniteRankProjectiveEndAlgebra
open TDA.Persistence.FiniteRankProjectiveDiagonalIdealProjective
open TDA.Persistence.IncidenceQuotientBaseChange
open TDA.Persistence.IncidenceQuotientDerivedOne

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

private def unitStrictVertex :
    TDA.Persistence.FiniteRankProjectiveEndAlgebra.StrictVertex Unit :=
  ⟨⟨((), ⊤), le_top⟩, by simp⟩

/-- The first left-derived extension of the singleton zero module is zero. -/
theorem rational_unit_zero_derived_one_isZero :
    IsZero (((extensionFunctor (k := ℚ) (S := Unit)).leftDerived 1).obj
      ((ModuleCat.restrictScalars (quotientHom (k := ℚ) (S := Unit))).obj
        (ModuleCat.of (RightQuotient (k := ℚ) (S := Unit)) PUnit))) :=
  extension_leftDerived_one_isZero_zero (k := ℚ) (S := Unit)

/-- The actual restricted singleton vertex has zero first derived quotient extension. -/
theorem rational_unit_vertex_derived_one_isZero :
    IsZero (((extensionFunctor (k := ℚ) (S := Unit)).leftDerived 1).obj
      (RightVertexRestrictedModule (k := ℚ) (S := Unit) unitStrictVertex)) :=
  rightVertexExtension_leftDerived_one_isZero (k := ℚ) (S := Unit) unitStrictVertex

end

end TDA.Persistence.IncidenceQuotientDerivedOneExamples
