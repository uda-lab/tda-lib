import TDA.Persistence.FiniteRankProjectiveDiagonalIdealProjective

/-!
# Examples for projectivity of the diagonal ideal

These examples exercise crossing and non-crossing coefficients, columns at
non-diagonal, diagonal, and top vertices, the singleton case, and the splitting
over an infinite field.
-/

set_option autoImplicit false

namespace TDA.Persistence.FiniteRankProjectiveDiagonalIdealProjectiveExamples

open TDA.Persistence.FiniteRankProjectiveEndAlgebra
open TDA.Persistence.FiniteRankProjectiveDiagonalIdealProjective

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

private def noncrossingSource : BoolPair :=
  ⟨(false, ⊤), le_top⟩

private def diagonalVertex : BoolPair :=
  ⟨(true, true), le_rfl⟩

private def topVertex : BoolPair :=
  ⟨(⊤, ⊤), le_rfl⟩

private theorem crossingSource_le_target : crossingSource ≤ crossingTarget := by
  change (false : WithTop Bool) ≤ true ∧ (true : WithTop Bool) ≤ ⊤
  exact ⟨WithTop.coe_le_coe.mpr (by simp), le_top⟩

private theorem crossingSource_crosses_target :
    CrossesDiagonal (S := Bool) crossingSource crossingTarget := by
  change (true : WithTop Bool) ≤ true
  exact le_rfl

private theorem noncrossingSource_le_target :
    noncrossingSource ≤ crossingTarget := by
  change (false : WithTop Bool) ≤ true ∧ (⊤ : WithTop Bool) ≤ ⊤
  exact ⟨WithTop.coe_le_coe.mpr (by simp), le_rfl⟩

private theorem noncrossingSource_does_not_cross_target :
    ¬ CrossesDiagonal (S := Bool) noncrossingSource crossingTarget := by
  simp [CrossesDiagonal, noncrossingSource, crossingTarget]

private def crossingDeltaIdeal (k : Type) [Field k] :
    DiagonalIdeal (k := k) (S := Bool) :=
  ⟨delta (k := k) (S := Bool) crossingSource crossingTarget
      crossingSource_le_target,
    diagonalIdeal_mem_delta_of_cross (k := k) (S := Bool)
      crossingSource crossingTarget crossingSource_le_target crossingSource_crosses_target⟩

example {k : Type} [Field k] :
    delta (k := k) (S := Bool) crossingSource crossingTarget
      crossingSource_le_target ∈ diagonalIdeal (k := k) (S := Bool) :=
  diagonalIdeal_mem_delta_of_cross (k := k) (S := Bool)
    crossingSource crossingTarget crossingSource_le_target crossingSource_crosses_target

example {k : Type} [Field k] :
    delta (k := k) (S := Bool) crossingSource crossingTarget
      crossingSource_le_target crossingSource crossingTarget = 1 := by
  simp [delta_apply]

example {k : Type} [Field k] (f : DiagonalIdeal (k := k) (S := Bool)) :
    f.1 noncrossingSource crossingTarget = 0 :=
  diagonalIdeal_coeff_zero_of_not_crosses (k := k) (S := Bool)
    f noncrossingSource crossingTarget noncrossingSource_does_not_cross_target

example : diagonalFloor (S := Bool) crossingTarget = diagonalVertex := by
  apply Subtype.ext
  rfl

example : ¬ IsDiagonal (S := Bool) crossingTarget := by
  simp [IsDiagonal, crossingTarget]

example : diagonalFloor (S := Bool) diagonalVertex = diagonalVertex := by
  apply Subtype.ext
  rfl

example : diagonalFloor (S := Bool) topVertex = topVertex := by
  apply Subtype.ext
  rfl

example {k : Type} [Field k] :
    (assembleColumns (k := k) (S := Bool)).comp
      (includeColumns (k := k) (S := Bool)) = LinearMap.id :=
  assembleColumns_comp_includeColumns (k := k) (S := Bool)

example : Infinite ℚ := inferInstance

example : Module.Projective (IncidenceAlgebra ℚ (PairPoset Bool))
    (DiagonalIdeal (k := ℚ) (S := Bool)) :=
  diagonalIdeal_projective (k := ℚ) (S := Bool)

example :
    (includeColumns (k := ℚ) (S := Bool) (crossingDeltaIdeal ℚ) crossingTarget)
      crossingSource (diagonalFloor (S := Bool) crossingTarget) = 1 := by
  simp [includeColumns_apply, crossingDeltaIdeal, delta_apply]

example :
    ((assembleColumns (k := ℚ) (S := Bool)
      (includeColumns (k := ℚ) (S := Bool) (crossingDeltaIdeal ℚ))).1
        crossingSource crossingTarget) = 1 := by
  have h := congrArg (fun f => f (crossingDeltaIdeal ℚ))
    (assembleColumns_comp_includeColumns (k := ℚ) (S := Bool))
  simpa [LinearMap.comp_apply, crossingDeltaIdeal, delta_apply] using
    congrArg (fun f : DiagonalIdeal (k := ℚ) (S := Bool) => f.1 crossingSource crossingTarget) h

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
local instance : Fintype (ComparablePair Unit) := Fintype.ofFinite _

private def singletonNonDiagonal : PairPoset Unit :=
  ⟨((), ⊤), le_top⟩

private theorem singletonNonDiagonal_does_not_cross :
    ¬ CrossesDiagonal (S := Unit) singletonNonDiagonal singletonNonDiagonal := by
  simp [CrossesDiagonal, singletonNonDiagonal]

example {k : Type} [Field k] (f : DiagonalIdeal (k := k) (S := Unit)) :
    f.1 singletonNonDiagonal singletonNonDiagonal = 0 :=
  diagonalIdeal_coeff_zero_of_not_crosses (k := k) (S := Unit)
    f singletonNonDiagonal singletonNonDiagonal singletonNonDiagonal_does_not_cross

example : Module.Projective (IncidenceAlgebra ℚ (PairPoset Unit))
    (DiagonalIdeal (k := ℚ) (S := Unit)) :=
  diagonalIdeal_projective (k := ℚ) (S := Unit)

end

end TDA.Persistence.FiniteRankProjectiveDiagonalIdealProjectiveExamples
