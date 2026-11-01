import TDA.Persistence.IncidenceQuotientSimple

/-!
# Examples for simple modules over the right diagonal quotient

These consumers distinguish strict vertices over `Bool`, treat the singleton lattice, and apply
the derived comparison and positive-degree vanishing over arbitrary fields.  The rational-field
instances give a concrete infinite-field specialization.
-/

set_option autoImplicit false

namespace TDA.Persistence.IncidenceQuotientSimpleExamples

open CategoryTheory
open CategoryTheory.Limits
open TDA.Persistence.FiniteRankProjectiveEndAlgebra
open TDA.Persistence.FiniteRankProjectiveDiagonalIdealProjective
open TDA.Persistence.IncidenceQuotientSimple
open TDA.Persistence.IncidenceVertexTensorFunctor
open TDA.Persistence.IncidenceVertexTor

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

private def boolLowerStrictVertex : StrictVertex Bool :=
  ⟨⟨((false : WithTop Bool), (true : WithTop Bool)), by simp⟩, by simp⟩

private def boolUpperStrictVertex : StrictVertex Bool :=
  ⟨⟨((true : WithTop Bool), ⊤), le_top⟩, by simp⟩

theorem bool_strict_vertices_distinct : boolLowerStrictVertex ≠ boolUpperStrictVertex := by
  intro h
  have hfirst := congrArg (fun v : StrictVertex Bool => v.1.val.1) h
  have hcoe : (false : WithTop Bool) = true := by
    simp [boolLowerStrictVertex, boolUpperStrictVertex] at hfirst
  cases (WithTop.coe_injective hcoe)

theorem bool_vertex_modules_not_isomorphic {k : Type} [Field k] :
    ¬ Nonempty (RightVertexModule (k := k) (S := Bool) boolLowerStrictVertex ≅
      RightVertexModule (k := k) (S := Bool) boolUpperStrictVertex) := by
  intro h
  exact bool_strict_vertices_distinct
    ((rightVertexModule_iso_iff (k := k) (S := Bool)
      boolLowerStrictVertex boolUpperStrictVertex).mp h)

/-- A rational-field specialization of the arbitrary-field classification theorem. -/
theorem rational_bool_vertex_classified :
    ∃! v : StrictVertex Bool,
      Nonempty (RightVertexModule (k := ℚ) (S := Bool) boolLowerStrictVertex ≅
        RightVertexModule (k := ℚ) (S := Bool) v) := by
  letI : IsSimpleModule (RightQuotient (k := ℚ) (S := Bool))
      (RightVertexModule (k := ℚ) (S := Bool) boolLowerStrictVertex) :=
    rightVertexModule_isSimpleModule (k := ℚ) (S := Bool) boolLowerStrictVertex
  exact simpleModule_existsUnique_vertex (k := ℚ) (S := Bool)
    (RightVertexModule (k := ℚ) (S := Bool) boolLowerStrictVertex)

theorem rationalField_infinite : Infinite ℚ := inferInstance

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

private def singletonStrictVertex : StrictVertex Unit :=
  ⟨⟨((), ⊤), le_top⟩, by simp⟩

theorem singleton_strictVertex_unique (v : StrictVertex Unit) :
    v = singletonStrictVertex := by
  rcases v with ⟨⟨⟨a, b⟩, hab⟩, hv⟩
  cases a with
  | top => cases b <;> simp at hv
  | coe a =>
      cases a
      cases b with
      | top => rfl
      | coe b => cases b; simp at hv

theorem singleton_strictVertex_subsingleton : Subsingleton (StrictVertex Unit) :=
  ⟨fun v w => (singleton_strictVertex_unique v).trans
    (singleton_strictVertex_unique w).symm⟩

theorem singleton_rational_vertex_classified :
    ∃! v : StrictVertex Unit,
      Nonempty (RightVertexModule (k := ℚ) (S := Unit) singletonStrictVertex ≅
        RightVertexModule (k := ℚ) (S := Unit) v) := by
  letI : IsSimpleModule (RightQuotient (k := ℚ) (S := Unit))
      (RightVertexModule (k := ℚ) (S := Unit) singletonStrictVertex) :=
    rightVertexModule_isSimpleModule (k := ℚ) (S := Unit) singletonStrictVertex
  exact simpleModule_existsUnique_vertex (k := ℚ) (S := Unit)
    (RightVertexModule (k := ℚ) (S := Unit) singletonStrictVertex)

theorem zeroModule_not_simple {k : Type} [Field k] :
    ¬ IsSimpleModule (RightQuotient (k := k) (S := Unit))
      (ModuleCat.of (RightQuotient (k := k) (S := Unit)) PUnit) := by
  intro h
  letI : Nontrivial PUnit := IsSimpleModule.nontrivial
    (RightQuotient (k := k) (S := Unit))
      (ModuleCat.of (RightQuotient (k := k) (S := Unit)) PUnit)
  obtain ⟨x, y, hxy⟩ := exists_pair_ne PUnit
  exact hxy (Subsingleton.elim x y)

theorem bool_lower_degree_zero_not_isZero {k : Type} [Field k] :
    ¬ IsZero (((vertexTensor (k := k) (S := Bool) boolLowerStrictVertex).leftDerived 0).obj
      (diagonalQuotientModule (k := k) (S := Bool))) :=
  diagonalQuotient_leftDerivedZero_not_isZero
    (k := k) (S := Bool) boolLowerStrictVertex

theorem bool_lower_degree_one_isZero {k : Type} [Field k] :
    IsZero (((vertexTensor (k := k) (S := Bool) boolLowerStrictVertex).leftDerived 1).obj
      (diagonalQuotientModule (k := k) (S := Bool))) :=
  diagonalQuotient_leftDerived_pos_isZero
    (k := k) (S := Bool) boolLowerStrictVertex 1 (Nat.zero_lt_succ 0)

theorem bool_lower_simple_positiveDerived_zero :
    ∃! v : StrictVertex Bool,
      Nonempty (RightVertexModule (k := ℚ) (S := Bool) boolLowerStrictVertex ≅
        RightVertexModule (k := ℚ) (S := Bool) v) ∧
      IsZero (((vertexTensor (k := ℚ) (S := Bool) v).leftDerived 1).obj
        (diagonalQuotientModule (k := ℚ) (S := Bool))) := by
  letI : IsSimpleModule (RightQuotient (k := ℚ) (S := Bool))
      (RightVertexModule (k := ℚ) (S := Bool) boolLowerStrictVertex) :=
    rightVertexModule_isSimpleModule (k := ℚ) (S := Bool) boolLowerStrictVertex
  exact simpleModule_existsUnique_vertex_positiveLeftDerived_isZero
    (k := ℚ) (S := Bool)
    (RightVertexModule (k := ℚ) (S := Bool) boolLowerStrictVertex) 1 (Nat.zero_lt_succ 0)

noncomputable def bool_lower_simple_degree_zero_comparison :
    restrictRightQuotientModule (k := ℚ) (S := Bool)
        (RightVertexModule (k := ℚ) (S := Bool) boolLowerStrictVertex) ≅
      (((vertexTensor (k := ℚ) (S := Bool) boolLowerStrictVertex).leftDerived 0).obj
        (diagonalQuotientModule (k := ℚ) (S := Bool))) := by
  exact leftDerivedZeroIso_of_rightVertexIso (k := ℚ) (S := Bool)
    (RightVertexModule (k := ℚ) (S := Bool) boolLowerStrictVertex)
    boolLowerStrictVertex (Iso.refl _)

end

end TDA.Persistence.IncidenceQuotientSimpleExamples
