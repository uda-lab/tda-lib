import TDA.Persistence.IncidenceQuotientSimpleExamples

/-!
# Client statements of the right diagonal quotient classification

Regression fixtures for #1148 (F-W2-3). Each statement is written as a client writes it: the file
opens no scope and declares no instance. The quotient ring structure of `RightQuotient` comes
from the global instance `IncidenceQuotientSimple.diagonalIdealTwoSided`. The last fixture names
the public example vertex `IncidenceQuotientSimpleExamples.boolLowerStrictVertex`.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence.IncidenceQuotientSimpleClientExamples

open CategoryTheory CategoryTheory.Limits
open TDA.Persistence.FiniteRankProjectiveEndAlgebra
open TDA.Persistence.IncidenceQuotientSimple

section Lattice

variable {k : Type u} [Field k] {S : Type} [Lattice S] [Finite S]

/-- Strict-vertex modules are isomorphic exactly at equal vertices, stated by a client. -/
theorem vertexModule_iso_iff (v w : StrictVertex S) :
    Nonempty (RightVertexModule (k := k) (S := S) v ≅ RightVertexModule (k := k) (S := S) w) ↔
      v = w :=
  rightVertexModule_iso_iff v w

/-- A simple right quotient module has a unique strict vertex, stated by a client. -/
theorem simple_existsUnique_vertex (M : ModuleCat (RightQuotient (k := k) (S := S)))
    [IsSimpleModule (RightQuotient (k := k) (S := S)) M] :
    ∃! v : StrictVertex S, Nonempty (M ≅ RightVertexModule (k := k) (S := S) v) :=
  simpleModule_existsUnique_vertex M

/-- The degree-zero comparison, applied by a client to its own isomorphism. -/
theorem degreeZero_iso_of_vertexIso (M : ModuleCat (RightQuotient (k := k) (S := S)))
    (v : StrictVertex S) (i : M ≅ RightVertexModule (k := k) (S := S) v) :
    Nonempty (restrictRightQuotientModule (k := k) (S := S) M ≅
      (((IncidenceVertexTensorFunctor.vertexTensor (k := k) (S := S) v).leftDerived 0).obj
        (IncidenceVertexTor.diagonalQuotientModule (k := k) (S := S)))) :=
  ⟨leftDerivedZeroIso_of_rightVertexIso M v i⟩

/-- The classification with the degree-zero comparison, stated by a client. -/
theorem simple_existsUnique_vertex_and_derivedZero
    (M : ModuleCat (RightQuotient (k := k) (S := S)))
    [IsSimpleModule (RightQuotient (k := k) (S := S)) M] :
    ∃! v : StrictVertex S,
      Nonempty (M ≅ RightVertexModule (k := k) (S := S) v) ∧
      Nonempty (restrictRightQuotientModule (k := k) (S := S) M ≅
        (((IncidenceVertexTensorFunctor.vertexTensor (k := k) (S := S) v).leftDerived 0).obj
          (IncidenceVertexTor.diagonalQuotientModule (k := k) (S := S)))) :=
  simpleModule_existsUnique_vertex_and_derivedZero M

/-- The classification with positive-degree vanishing, stated by a client. -/
theorem simple_existsUnique_vertex_positiveLeftDerived_isZero
    (M : ModuleCat (RightQuotient (k := k) (S := S)))
    [IsSimpleModule (RightQuotient (k := k) (S := S)) M] (n : ℕ) (hn : 0 < n) :
    ∃! v : StrictVertex S,
      Nonempty (M ≅ RightVertexModule (k := k) (S := S) v) ∧
      IsZero (((IncidenceVertexTensorFunctor.vertexTensor (k := k) (S := S) v).leftDerived n).obj
        (IncidenceVertexTor.diagonalQuotientModule (k := k) (S := S))) :=
  simpleModule_existsUnique_vertex_positiveLeftDerived_isZero M n hn

end Lattice

/-- The rational degree-zero comparison at the public lower vertex of `Bool`, stated by a
client. -/
theorem bool_lower_degreeZero :
    Nonempty (restrictRightQuotientModule (k := ℚ) (S := Bool)
        (RightVertexModule (k := ℚ) (S := Bool)
          IncidenceQuotientSimpleExamples.boolLowerStrictVertex) ≅
      (((IncidenceVertexTensorFunctor.vertexTensor (k := ℚ) (S := Bool)
          IncidenceQuotientSimpleExamples.boolLowerStrictVertex).leftDerived 0).obj
        (IncidenceVertexTor.diagonalQuotientModule (k := ℚ) (S := Bool)))) :=
  ⟨IncidenceQuotientSimpleExamples.bool_lower_simple_degree_zero_comparison⟩

end TDA.Persistence.IncidenceQuotientSimpleClientExamples
