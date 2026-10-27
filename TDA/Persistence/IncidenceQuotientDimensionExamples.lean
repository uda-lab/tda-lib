import TDA.Persistence.IncidenceQuotientDimension

/-!
# Examples for finite-length quotient dimensions

These examples apply the finite-length and finite-dimensional bounds to the actual strict-vertex
modules over `Bool` and `Unit`, include the zero module over arbitrary fields, and consume the
bound across a split short exact sequence.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence.IncidenceQuotientDimensionExamples

open CategoryTheory
open TDA.Persistence.FiniteRankProjectiveEndAlgebra
open TDA.Persistence.FiniteRankProjectiveDiagonalIdealProjective
open TDA.Persistence.IncidenceQuotientSimple
open TDA.Persistence.IncidenceQuotientDimension

noncomputable section

section Bool

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
local instance diagonalIdealTwoSidedBool {k : Type u} [Field k] :
    (TDA.Persistence.FiniteRankProjectiveDiagonalIdealProjective.DiagonalIdeal
      (k := k) (S := Bool)).IsTwoSided :=
  diagonalIdeal_isTwoSided (k := k) (S := Bool)

private def boolLowerStrictVertex : StrictVertex Bool :=
  ⟨⟨((false : WithTop Bool), (true : WithTop Bool)), by simp⟩, by simp⟩

private def boolUpperStrictVertex : StrictVertex Bool :=
  ⟨⟨((true : WithTop Bool), ⊤), le_top⟩, by simp⟩

theorem bool_zero_module_dimension_le_vertex_sup {k : Type u} [Field k] :
    projectiveDimension
        (ModuleCat.of (RightQuotient (k := k) (S := Bool)) (PUnit.{u + 1})) ≤
      ⨆ v : StrictVertex Bool,
        projectiveDimension (RightVertexModule (k := k) (S := Bool) v) := by
  apply projectiveDimension_le_iSup_vertex (k := k) (S := Bool)
  exact IsFiniteLength.of_subsingleton

/-- The arbitrary-field theorem applies directly to each genuine vertex module. -/
theorem bool_vertex_dimension_le_vertex_sup {k : Type u} [Field k]
    (v : StrictVertex Bool) :
    projectiveDimension (RightVertexModule (k := k) (S := Bool) v) ≤
      ⨆ w : StrictVertex Bool,
        projectiveDimension (RightVertexModule (k := k) (S := Bool) w) :=
  projectiveDimension_le_iSup_vertex (k := k) (S := Bool)
    (RightVertexModule (k := k) (S := Bool) v)
    (rightVertexModule_isFiniteLength (k := k) (S := Bool) v)

theorem rational_bool_vertex_finiteLength_from_dimension (v : StrictVertex Bool) :
    IsFiniteLength (RightQuotient (k := ℚ) (S := Bool))
      (RightVertexModule (k := ℚ) (S := Bool) v) :=
  isFiniteLength_of_finiteDimensional (k := ℚ) (S := Bool)
    (RightVertexModule (k := ℚ) (S := Bool) v)
    (rightVertexModule_finiteDimensional (k := ℚ) (S := Bool) v)

theorem bool_split_extension_has_common_bound {k : Type u} [Field k]
    (n : ℕ) (v w : StrictVertex Bool)
    (hvertex : ∀ x : StrictVertex Bool,
      HasProjectiveDimensionLT (RightVertexModule (k := k) (S := Bool) x) n) :
    HasProjectiveDimensionLT
      (RightVertexModule (k := k) (S := Bool) v ⊞
        RightVertexModule (k := k) (S := Bool) w) n := by
  exact (ShortComplex.Splitting.ofHasBinaryBiproduct
      (RightVertexModule (k := k) (S := Bool) v)
      (RightVertexModule (k := k) (S := Bool) w)).shortExact.hasProjectiveDimensionLT_X₂ n
    (hasProjectiveDimensionLT_of_vertex_bound (k := k) (S := Bool) n hvertex _
      (rightVertexModule_isFiniteLength (k := k) (S := Bool) v))
    (hasProjectiveDimensionLT_of_vertex_bound (k := k) (S := Bool) n hvertex _
      (rightVertexModule_isFiniteLength (k := k) (S := Bool) w))

theorem bool_finiteLength_uniform_bound_iff {k : Type u} [Field k] (d : ℕ) :
    (∀ M : ModuleCat.{u} (RightQuotient (k := k) (S := Bool)),
      IsFiniteLength (RightQuotient (k := k) (S := Bool)) M →
        HasProjectiveDimensionLE M d) ↔
    (∀ v : StrictVertex Bool,
      HasProjectiveDimensionLE (RightVertexModule (k := k) (S := Bool) v) d) :=
  finiteLength_uniform_projectiveDimensionLE_iff (k := k) (S := Bool) d

end Bool

section Unit

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
local instance diagonalIdealTwoSidedUnit {k : Type u} [Field k] :
    (TDA.Persistence.FiniteRankProjectiveDiagonalIdealProjective.DiagonalIdeal
      (k := k) (S := Unit)).IsTwoSided :=
  diagonalIdeal_isTwoSided (k := k) (S := Unit)

private def singletonStrictVertex : StrictVertex Unit :=
  ⟨⟨((), ⊤), le_top⟩, by simp⟩

theorem rational_singleton_vertex_dimension_le_vertex_sup :
    projectiveDimension
        (RightVertexModule (k := ℚ) (S := Unit) singletonStrictVertex) ≤
      ⨆ v : StrictVertex Unit,
        projectiveDimension (RightVertexModule (k := ℚ) (S := Unit) v) :=
  projectiveDimension_le_iSup_vertex (k := ℚ) (S := Unit)
    (RightVertexModule (k := ℚ) (S := Unit) singletonStrictVertex)
    (rightVertexModule_isFiniteLength (k := ℚ) (S := Unit) singletonStrictVertex)

theorem rational_singleton_vertex_finiteLength_from_dimension :
    IsFiniteLength (RightQuotient (k := ℚ) (S := Unit))
      (RightVertexModule (k := ℚ) (S := Unit) singletonStrictVertex) :=
  isFiniteLength_of_finiteDimensional (k := ℚ) (S := Unit)
    (RightVertexModule (k := ℚ) (S := Unit) singletonStrictVertex)
    (rightVertexModule_finiteDimensional (k := ℚ) (S := Unit) singletonStrictVertex)

end Unit

end

end TDA.Persistence.IncidenceQuotientDimensionExamples
