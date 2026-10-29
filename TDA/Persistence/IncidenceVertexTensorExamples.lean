import TDA.Persistence.IncidenceVertexTensor
import TDA.Persistence.FiniteRankProjectiveDiagonalIdealProjectiveExamples

/-!
# Examples for degree-zero vertex tensors

The Bool and singleton fixtures exercise the actual incidence algebra, its
diagonal ideal and quotient, including the crossing-delta relation and the
surviving quotient-unit class.
-/

set_option autoImplicit false

namespace TDA.Persistence.IncidenceVertexTensorExamples

open TDA.Persistence.FiniteRankProjectiveEndAlgebra
open TDA.Persistence.FiniteRankProjectiveDiagonalIdealProjective
open TDA.Persistence.IncidenceVertexTensor

noncomputable section

local instance : Fintype Bool := Fintype.ofFinite Bool
local instance : DecidableLE Bool := Classical.decRel _
local instance : DecidableLT Bool := Classical.decRel _
local instance : DecidableEq Bool := Classical.decEq _
local instance : DecidableEq (WithTop Bool) := Classical.decEq _
local instance (p : Prop) : Decidable p := Classical.propDecidable p
local instance : Fintype (PairPoset Bool) :=
  Fintype.subtype (Finset.univ.filter fun ab : WithTop Bool × WithTop Bool => ab.1 ≤ ab.2)
    (by intro ab; simp)
local instance : DecidableLE (PairPoset Bool) := Classical.decRel _
local instance : DecidableLT (PairPoset Bool) := Classical.decRel _
local instance : LocallyFiniteOrder (PairPoset Bool) := Fintype.toLocallyFiniteOrder
local instance : DecidableEq (PairPoset Bool) := Classical.decEq _
local instance : Fintype (ComparablePair Bool) := Fintype.ofFinite _

private abbrev BoolPair := PairPoset Bool

private def crossingSource : BoolPair :=
  ⟨(false, true), by simp⟩

private def crossingTarget : BoolPair :=
  ⟨(true, ⊤), le_top⟩

private def diagonalVertex : BoolPair :=
  ⟨(true, true), le_rfl⟩

private theorem crossingSource_le_target : crossingSource ≤ crossingTarget := by
  change (false : WithTop Bool) ≤ true ∧ (true : WithTop Bool) ≤ ⊤
  exact ⟨WithTop.coe_le_coe.mpr (by simp), le_top⟩

private theorem crossingSource_crosses_target :
    CrossesDiagonal (S := Bool) crossingSource crossingTarget := by
  change (true : WithTop Bool) ≤ true
  exact le_rfl

private def crossingStrictVertex : StrictVertex Bool :=
  ⟨crossingTarget, by simp [crossingTarget]⟩

private def crossingDeltaIdeal (k : Type) [Field k] :
    IncidenceVertexTensor.DiagonalIdeal (k := k) (S := Bool) :=
  ⟨delta (k := k) (S := Bool) crossingSource crossingTarget crossingSource_le_target,
    diagonalIdeal_mem_delta_of_cross (k := k) (S := Bool) crossingSource crossingTarget
      crossingSource_le_target crossingSource_crosses_target⟩

example {k : Type} [Field k] :
    DiagonalQuotientVertexCoinvariants (k := k) (S := Bool) crossingStrictVertex ≃ₗ[k] k :=
  diagonalQuotientVertexTensorEquiv (k := k) (S := Bool) crossingStrictVertex

example : Infinite ℚ := inferInstance

example {k : Type} [Field k] :
    delta (k := k) (S := Bool) crossingSource crossingTarget crossingSource_le_target ≠ 0 := by
  intro h
  have hcoeff := congrArg
    (fun f : IncidenceVertexTensor.Incidence (k := k) (S := Bool) =>
      f crossingSource crossingTarget) h
  simpa [delta_apply] using hcoeff

example {k : Type} [Field k] :
    (diagonalIdealVertexRelation (k := k) (S := Bool) crossingStrictVertex).mkQ
      (crossingDeltaIdeal k) = 0 :=
  crossingDelta_killed_in_diagonalIdealVertexCoinvariants
    (k := k) (S := Bool) crossingStrictVertex crossingSource crossingTarget
    crossingSource_le_target crossingSource_crosses_target

example {k : Type} [Field k] (x : DiagonalIdealVertexCoinvariants
    (k := k) (S := Bool) crossingStrictVertex) : x = 0 :=
  diagonalIdealVertexCoinvariants_eq_zero (k := k) (S := Bool) crossingStrictVertex x

example {k : Type} [Field k] :
    diagonalQuotientVertexTensorUnit (k := k) (S := Bool) crossingStrictVertex ≠ 0 :=
  diagonalQuotientVertexTensorUnit_ne_zero (k := k) (S := Bool) crossingStrictVertex

example {k : Type} [Field k] :
    vertexCharacter (k := k) (S := Bool) crossingStrictVertex
      (delta (k := k) (S := Bool) crossingTarget crossingTarget le_rfl) = 1 := by
  simp [crossingStrictVertex, crossingTarget]

example {k : Type} [Field k] :
    vertexCharacter (k := k) (S := Bool) crossingStrictVertex
      (delta (k := k) (S := Bool) diagonalVertex diagonalVertex le_rfl) = 0 := by
  simp [crossingStrictVertex, crossingTarget, diagonalVertex]

example : diagonalFloor (S := Bool) crossingTarget = diagonalVertex := by
  apply Subtype.ext
  rfl

example : ¬ IsDiagonal (S := Bool) crossingTarget := by
  simp [IsDiagonal, crossingTarget]

local instance : Fintype Unit := Fintype.ofFinite Unit
local instance : DecidableLE Unit := Classical.decRel _
local instance : DecidableLT Unit := Classical.decRel _
local instance : DecidableEq Unit := Classical.decEq _
local instance : DecidableEq (WithTop Unit) := Classical.decEq _
local instance : Fintype (PairPoset Unit) :=
  Fintype.subtype (Finset.univ.filter fun ab : WithTop Unit × WithTop Unit => ab.1 ≤ ab.2)
    (by intro ab; simp)
local instance : DecidableLE (PairPoset Unit) := Classical.decRel _
local instance : DecidableLT (PairPoset Unit) := Classical.decRel _
local instance : LocallyFiniteOrder (PairPoset Unit) := Fintype.toLocallyFiniteOrder
local instance : DecidableEq (PairPoset Unit) := Classical.decEq _

private def singletonStrictVertex : StrictVertex Unit :=
  ⟨⟨((), ⊤), le_top⟩, by simp⟩

example {k : Type} [Field k] :
    DiagonalQuotientVertexCoinvariants (k := k) (S := Unit) singletonStrictVertex ≃ₗ[k] k :=
  diagonalQuotientVertexTensorEquiv (k := k) (S := Unit) singletonStrictVertex

example {k : Type} [Field k] (x : DiagonalIdealVertexCoinvariants
    (k := k) (S := Unit) singletonStrictVertex) : x = 0 :=
  diagonalIdealVertexCoinvariants_eq_zero (k := k) (S := Unit) singletonStrictVertex x

example {k : Type} [Field k] :
    diagonalQuotientVertexTensorUnit (k := k) (S := Unit) singletonStrictVertex ≠ 0 :=
  diagonalQuotientVertexTensorUnit_ne_zero (k := k) (S := Unit) singletonStrictVertex

end

end TDA.Persistence.IncidenceVertexTensorExamples
