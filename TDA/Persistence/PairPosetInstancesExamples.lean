import TDA.Persistence.IncidenceQuotientDimension
import TDA.Persistence.IncidenceVertexProjectiveDimension
import TDA.Persistence.FiniteRankProjectiveDiagonalIdealProjective

/-!
# Canonical PairPoset instance consumers

These examples use the scoped canonical PairPoset data with the existing incidence,
quotient, and vertex-dimension APIs. Generic bounds retain their endpoint assumptions,
while the concrete cases use actual regular and quotient modules.
-/

set_option autoImplicit false
universe u
namespace TDA.Persistence.PairPosetInstancesExamples
open CategoryTheory
open TDA.Persistence.FiniteInjectiveRankDimension
open TDA.Persistence.FiniteRankProjectiveEndAlgebra
open TDA.Persistence.FiniteRankProjectiveDiagonalIdealProjective
open TDA.Persistence.IncidenceQuotientBaseChange
open TDA.Persistence.IncidenceVertexRepresentation
open TDA.Persistence.IncidenceRegularVertex
open TDA.Persistence.FiniteLatticeComplementCardinality
open scoped TDA.Persistence.FiniteRankProjectiveEndAlgebra.PairPoset ModuleCat
noncomputable section
variable {k : Type u} [Field k] {S : Type} [Lattice S] [Finite S]
example : Ring (IncidenceAlgebra k (PairPoset S)) := inferInstance
example : Algebra k (IncidenceAlgebra k (PairPoset S)) := inferInstance
example : End (HookSum (k := k) (S := S)) ≃ₐ[k]
    (IncidenceAlgebra k (PairPoset S)) ⧸ diagonalIdeal (k := k) (S := S) :=
  hookEndAlgEquivIncidenceQuotient
example : Module.Projective (IncidenceAlgebra k (PairPoset S)) (diagonalIdeal (k := k) (S := S)) :=
  diagonalIdeal_projective
example (M : ModuleCat.{u} ((IncidenceAlgebra k (PairPoset S))ᵐᵒᵖ))
    (hM : FiniteDimensional k (restrictedKModule (k := k) (S := S) M)) (d : ℕ)
    (hV : HasProjectiveDimensionLE ((vertexFunctor (k := k) (S := S)).obj M) d) :
    HasProjectiveDimensionLE M d :=
  TDA.Persistence.IncidenceVertexProjectiveDimension.hasProjectiveDimensionLE_of_vertex M hM d hV

/-- The incidence bound for a finite-dimensional actual right-incidence module
when `S` has endpoints. -/
theorem genericBound [OrderBot S] [OrderTop S]
    (M : ModuleCat.{u} ((IncidenceAlgebra k (PairPoset S))ᵐᵒᵖ))
    (hM : FiniteDimensional k (restrictedKModule (k := k) (S := S) M)) :
    letI : Lattice (PairPoset S) := pairPosetLattice (S := S)
    letI : BoundedOrder (PairPoset S) := pairPosetBoundedOrder (S := S)
    HasProjectiveDimensionLE M (maxComplementCard (S := PairPoset S)) :=
  TDA.Persistence.IncidenceVertexProjectiveDimension.hasProjectiveDimensionLE M hM

/-- The quotient bound for a finite-dimensional actual right-quotient module
when `S` has endpoints. -/
theorem genericQuotientBound [OrderBot S] [OrderTop S]
    (N : ModuleCat.{u} (RightQuotient (k := k) (S := S)))
    (hN : FiniteDimensional k (TDA.Persistence.IncidenceQuotientSimple.restrictRightQuotientModule (k := k) (S := S) N)) :
    letI : Lattice (PairPoset S) := pairPosetLattice (S := S)
    letI : BoundedOrder (PairPoset S) := pairPosetBoundedOrder (S := S)
    HasProjectiveDimensionLE N (maxComplementCard (S := PairPoset S)) :=
  TDA.Persistence.IncidenceVertexProjectiveDimension.quotient_hasProjectiveDimensionLE N hN

example : Projective (ModuleCat.of (IncidenceAlgebra k (PairPoset S)) (diagonalIdeal (k := k) (S := S))) :=
  diagonalIdeal_projective_object
example : Ring ((IncidenceAlgebra k (PairPoset S)) ⧸ diagonalIdeal (k := k) (S := S)) := inferInstance
example : Algebra k ((IncidenceAlgebra k (PairPoset S)) ⧸ diagonalIdeal (k := k) (S := S)) := inferInstance

/-- The actual regular incidence module has projective dimension at most zero. -/
theorem regularPDZero :
    HasProjectiveDimensionLE (regularRightIncidenceModule (k := k) (S := S)) 0 :=
  TDA.Persistence.IncidenceVertexProjectiveDimension.hasProjectiveDimensionLE_of_vertex _
    (regular_finiteDimensional (k := k) (S := S)) 0
    ((projective_iff_hasProjectiveDimensionLE_zero _).mp (regularVertex_projective (k := k) (S := S)))

/-- A diagonal matrix unit is idempotent in the actual incidence algebra. -/
theorem deltaIdempotent (p : PairPoset S) :
    delta (k := k) p p le_rfl * delta (k := k) p p le_rfl = delta (k := k) p p le_rfl := by
  simpa using delta_mul (k := k) p p p p le_rfl le_rfl

/-- A diagonal matrix unit is nonzero in the actual incidence algebra. -/
theorem deltaNonzero (p : PairPoset S) : delta (k := k) p p le_rfl ≠ 0 := by
  intro h
  have hcoeff := congrArg (fun f : IncidenceAlgebra k (PairPoset S) => f p p) h
  have : (1 : k) = 0 := by simpa using hcoeff
  exact one_ne_zero this

/-- The actual regular incidence module is nonzero for every field and finite lattice. -/
theorem regularNonzero :
    ¬ CategoryTheory.Limits.IsZero (regularRightIncidenceModule (k := k) (S := S)) := by
  intro hz
  have hsub := ModuleCat.subsingleton_of_isZero hz
  let p : PairPoset S := ⟨(⊤, ⊤), le_rfl⟩
  have h : (MulOpposite.op (delta (k := k) p p le_rfl) : TDA.Persistence.IncidenceQuotientBaseChange.RightIncidence (k := k) (S := S)) = 0 := hsub.elim _ _
  exact deltaNonzero p (congrArg MulOpposite.unop h)

-- The native Bool and Fin 2 finite instances also support these regular modules.
example : HasProjectiveDimensionLE (regularRightIncidenceModule (k := ℚ) (S := Bool)) 0 := regularPDZero
example : ¬ CategoryTheory.Limits.IsZero (regularRightIncidenceModule (k := ℚ) (S := Bool)) := regularNonzero
example : HasProjectiveDimensionLE (regularRightIncidenceModule (k := ZMod 2) (S := Bool)) 0 := regularPDZero
example : ¬ CategoryTheory.Limits.IsZero (regularRightIncidenceModule (k := ZMod 2) (S := Bool)) := regularNonzero
example : HasProjectiveDimensionLE (regularRightIncidenceModule (k := ℚ) (S := Fin 2)) 0 := regularPDZero
example : ¬ CategoryTheory.Limits.IsZero (regularRightIncidenceModule (k := ℚ) (S := Fin 2)) := regularNonzero
example : HasProjectiveDimensionLE (regularRightIncidenceModule (k := ZMod 2) (S := Fin 2)) 0 := regularPDZero
example : ¬ CategoryTheory.Limits.IsZero (regularRightIncidenceModule (k := ZMod 2) (S := Fin 2)) := regularNonzero
example : HasProjectiveDimensionLE (regularRightIncidenceModule (k := ℚ) (S := Fin 0)) 0 := regularPDZero
example : ¬ CategoryTheory.Limits.IsZero (regularRightIncidenceModule (k := ℚ) (S := Fin 0)) := regularNonzero
example : HasProjectiveDimensionLE (regularRightIncidenceModule (k := ℚ) (S := Fin 1)) 0 := regularPDZero
example : ¬ CategoryTheory.Limits.IsZero (regularRightIncidenceModule (k := ℚ) (S := Fin 1)) := regularNonzero
example : HasProjectiveDimensionLE (regularRightIncidenceModule (k := ZMod 2) (S := Fin 2))
    (letI : Lattice (PairPoset (Fin 2)) := pairPosetLattice
     letI : BoundedOrder (PairPoset (Fin 2)) := pairPosetBoundedOrder
     maxComplementCard (S := PairPoset (Fin 2))) := genericBound _ (regular_finiteDimensional (k := ZMod 2) (S := Fin 2))

example : (inferInstance : Fintype (PairPoset Bool)) = pairPosetFintype := rfl
example : (inferInstance : LocallyFiniteOrder (PairPoset (Fin 2))) = pairPosetLocallyFiniteOrder := rfl
example : (inferInstance : DecidableEq (PairPoset Bool)) = pairPosetDecidableEq := rfl
example (p : PairPoset Bool) : delta (k := ℚ) p p le_rfl * delta (k := ℚ) p p le_rfl = delta (k := ℚ) p p le_rfl := deltaIdempotent p
example (p : PairPoset (Fin 2)) : delta (k := ZMod 2) p p le_rfl * delta (k := ZMod 2) p p le_rfl = delta (k := ZMod 2) p p le_rfl := deltaIdempotent p
example (p : PairPoset Bool) : delta (k := ℚ) p p le_rfl ≠ 0 := deltaNonzero p
example (p : PairPoset (Fin 2)) : delta (k := ZMod 2) p p le_rfl ≠ 0 := deltaNonzero p
example : FiniteDimensional ℚ (TDA.Persistence.FiniteRankProjectiveEndAlgebra.Incidence (k := ℚ) (S := Bool)) := incidence_finiteDimensional
example : FiniteDimensional (ZMod 2) (TDA.Persistence.FiniteRankProjectiveEndAlgebra.Incidence (k := ZMod 2) (S := Fin 2)) := incidence_finiteDimensional

-- The characteristic-two strict quotient case.
/-- The strict vertex in `Fin 2` used for the characteristic-two quotient example. -/
def finTwoStrictVertex : StrictVertex (Fin 2) := ⟨⟨((0 : Fin 2), (1 : Fin 2)), by decide⟩, by decide⟩

/-- The actual strict `Fin 2` quotient vertex module is nonzero over `ZMod 2`. -/
theorem finTwoQuotientNonzero :
    ¬ Limits.IsZero (TDA.Persistence.IncidenceQuotientSimple.RightVertexModule (k := ZMod 2) finTwoStrictVertex) := by
  intro hz
  have hsub := ModuleCat.subsingleton_of_isZero hz
  change Subsingleton (ZMod 2) at hsub
  have h : (1 : ZMod 2) = 0 := hsub.elim 1 0
  exact one_ne_zero h

/-- The quotient bound after deriving finite dimensionality of the actual
strict vertex module. -/
theorem finTwoQuotientBound :
    letI : Lattice (PairPoset (Fin 2)) := pairPosetLattice
    letI : BoundedOrder (PairPoset (Fin 2)) := pairPosetBoundedOrder
    HasProjectiveDimensionLE
      (TDA.Persistence.IncidenceQuotientSimple.RightVertexModule (k := ZMod 2) finTwoStrictVertex)
      (maxComplementCard (S := PairPoset (Fin 2))) :=
  genericQuotientBound _ (TDA.Persistence.IncidenceQuotientDimension.rightVertexModule_finiteDimensional finTwoStrictVertex)
end
end TDA.Persistence.PairPosetInstancesExamples

namespace ScopeIsolation
example {S : Type} [Lattice S] [Finite S] : True := by
  fail_if_success have : LocallyFiniteOrder (TDA.Persistence.FiniteRankProjectiveEndAlgebra.PairPoset S) := inferInstance
  trivial
end ScopeIsolation
namespace NativeBase
private abbrev boolNative : Fintype Bool := inferInstance
private abbrev finTwoNative : Fintype (Fin 2) := inferInstance
open scoped TDA.Persistence.FiniteRankProjectiveEndAlgebra.PairPoset
example : (inferInstance : Fintype Bool) = boolNative := rfl
example : (inferInstance : Fintype (Fin 2)) = finTwoNative := rfl
end NativeBase

namespace SeparateBoolBounds
noncomputable section
local instance : Fintype Bool := Fintype.ofFinite Bool
local instance : DecidableLE Bool := Classical.decRel _
local instance : DecidableLT Bool := Classical.decRel _
local instance : DecidableEq Bool := Classical.decEq _
local instance : DecidableEq (WithTop Bool) := Classical.decEq _
local instance (p : Prop) : Decidable p := Classical.propDecidable p
local instance oldBot : OrderBot Bool := Fintype.toOrderBot Bool
local instance oldTop : OrderTop Bool := Fintype.toOrderTop Bool
example : oldBot = (letI : Fintype Bool := Fintype.ofFinite Bool; Fintype.toOrderBot Bool) := rfl
example : oldTop = (letI : Fintype Bool := Fintype.ofFinite Bool; Fintype.toOrderTop Bool) := rfl
end
end SeparateBoolBounds
