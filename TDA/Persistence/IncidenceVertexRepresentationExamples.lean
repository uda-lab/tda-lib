import TDA.Persistence.IncidenceVertexRepresentation
import TDA.Persistence.IncidenceRegularVertex

/-!
# Examples for actual incidence-module vertex representations

These fixtures use a genuine off-diagonal matrix-unit transition in the regular
right-incidence module, recover an actual nonidentity module map from its vertex
natural transformation, and check exactness and coefficient-field dimension on
all fibers.
-/

set_option autoImplicit false

namespace TDA.Persistence.IncidenceVertexRepresentationExamples

open CategoryTheory
open TDA.Persistence.FiniteRankProjectiveEndAlgebra
open TDA.Persistence.IncidenceVertexRepresentation

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
local instance : LocallyFiniteOrder (PairPoset Bool) :=
  TDA.Persistence.FiniteRankProjectiveEndAlgebra.instLocallyFiniteOrderPairPoset
local instance : DecidableEq (PairPoset Bool) :=
  TDA.Persistence.FiniteRankProjectiveEndAlgebra.instDecidableEqPairPoset
local instance : Fintype (ComparablePair Bool) := Fintype.ofFinite _

private def boolSource : PairPoset Bool :=
  ⟨((false : Bool), (false : Bool)), by simp⟩

private def boolTarget : PairPoset Bool :=
  ⟨((false : Bool), (true : Bool)), by simp⟩

private theorem boolSource_le_target : boolSource ≤ boolTarget := by
  change (false : WithTop Bool) ≤ (false : WithTop Bool) ∧
    (false : WithTop Bool) ≤ (true : WithTop Bool)
  exact ⟨le_rfl, (WithTop.coe_lt_coe.mpr Bool.false_lt_true).le⟩

private def boolTargetStrict : StrictVertex Bool :=
  ⟨boolTarget, by
    change (false : WithTop Bool) < (true : WithTop Bool)
    exact WithTop.coe_lt_coe.mpr Bool.false_lt_true⟩

private abbrev boolRegular (k : Type) [Field k] :=
  IncidenceQuotientBaseChange.regularRightIncidenceModule (k := k) (S := Bool)

/-- The regular module's diagonal matrix unit belongs to its source fiber. -/
noncomputable def boolRegularSourceUnit (k : Type) [Field k] :
    vertexFiber (k := k) (S := Bool) (boolRegular k) boolSource := by
  refine ⟨IncidenceQuotientBaseChange.rightIncidenceMatrixUnit (k := k) (S := Bool)
    boolSource boolSource le_rfl, ?_⟩
  apply (mem_vertexFiber_iff (k := k) (S := Bool)
    (boolRegular k) boolSource
    (IncidenceQuotientBaseChange.rightIncidenceMatrixUnit (k := k) (S := Bool)
      boolSource boolSource le_rfl)).2
  change IncidenceQuotientBaseChange.rightIncidenceMatrixUnit (k := k) (S := Bool)
      boolSource boolSource le_rfl *
    IncidenceQuotientBaseChange.rightIncidenceMatrixUnit (k := k) (S := Bool)
      boolSource boolSource le_rfl = _
  simp [rightIncidenceMatrixUnit_mul]

/-- The actual off-diagonal transition sends the regular diagonal unit to its matrix unit. -/
theorem boolRegular_transition_value {k : Type} [Field k] :
    (vertexStructureMap (k := k) (S := Bool) (boolRegular k)
      boolSource_le_target (boolRegularSourceUnit k) : boolRegular k) =
      IncidenceQuotientBaseChange.rightIncidenceMatrixUnit (k := k) (S := Bool)
        boolSource boolTarget boolSource_le_target := by
  rw [vertexStructureMap_val]
  change IncidenceQuotientBaseChange.rightIncidenceMatrixUnit (k := k) (S := Bool)
      boolSource boolTarget boolSource_le_target *
    IncidenceQuotientBaseChange.rightIncidenceMatrixUnit (k := k) (S := Bool)
      boolSource boolSource le_rfl = _
  simp [rightIncidenceMatrixUnit_mul]

/-- This off-diagonal matrix unit is nonzero over every field. -/
theorem boolRegular_transition_nonzero {k : Type} [Field k] :
    IncidenceQuotientBaseChange.rightIncidenceMatrixUnit (k := k) (S := Bool)
      boolSource boolTarget boolSource_le_target ≠ 0 := by
  intro h
  have hcoeff := congrArg
    (fun a : RightIncidence (k := k) (S := Bool) =>
      (MulOpposite.unop a : FiniteRankProjectiveEndAlgebra.Incidence (k := k) (S := Bool)) boolSource boolTarget) h
  simp [IncidenceQuotientBaseChange.rightIncidenceMatrixUnit,
    FiniteRankProjectiveEndAlgebra.delta_apply] at hcoeff

/-- Every fixed fiber of the actual zero module is a subsingleton. -/
theorem boolZero_fibers_subsingleton {k : Type} [Field k] :
    ∀ p : PairPoset Bool,
      Subsingleton (vertexFiber (k := k) (S := Bool)
        (ModuleCat.of (RightIncidence (k := k) (S := Bool)) PUnit) p) := by
  intro p
  constructor
  intro x y
  apply Subtype.ext
  exact Subsingleton.elim _ _

/-- The actual regular module is finite-dimensional by its incidence-function embedding. -/
theorem boolRegular_finiteDimensional {k : Type} [Field k] :
    FiniteDimensional k (restrictedKModule (k := k) (S := Bool) (boolRegular k)) := by
  change FiniteDimensional k (RightIncidence (k := k) (S := Bool))
  have hfd : FiniteDimensional k
      (FiniteRankProjectiveEndAlgebra.Incidence (k := k) (S := Bool)) := by
    letI : FiniteDimensional k
        (PairPoset Bool → PairPoset Bool → k) := by infer_instance
    exact FiniteDimensional.of_injective
      (IncidenceRegularVertex.incidenceToFunctions (k := k) (S := Bool))
      (IncidenceRegularVertex.incidenceToFunctions_injective (k := k) (S := Bool))
  letI := hfd
  exact (MulOpposite.opLinearEquiv k :
    FiniteRankProjectiveEndAlgebra.Incidence (k := k) (S := Bool) ≃ₗ[k]
      RightIncidence (k := k) (S := Bool)).finiteDimensional

private def boolRegularDoubleEnd : boolRegular ℚ ⟶ boolRegular ℚ :=
  ModuleCat.ofHom (LinearMap.mulRight (RightIncidence (k := ℚ) (S := Bool)) 2)

/-- Multiplication by two is an actual nonidentity endomorphism of the regular module. -/
theorem boolRegularDoubleEnd_ne_identity : boolRegularDoubleEnd ≠ 𝟙 _ := by
  intro h
  have hval : (2 : RightIncidence (k := ℚ) (S := Bool)) = 1 := by
    have hh := congrArg
      (fun f : RightIncidence (k := ℚ) (S := Bool) →ₗ[RightIncidence (k := ℚ) (S := Bool)]
        RightIncidence (k := ℚ) (S := Bool) => f 1)
      (congrArg ModuleCat.Hom.hom h)
    simpa [boolRegularDoubleEnd, LinearMap.mulRight_apply] using hh
  have hone : (1 : RightIncidence (k := ℚ) (S := Bool)) ≠ 0 := by
    intro hzero
    have hcoeff := congrArg
      (fun a : RightIncidence (k := ℚ) (S := Bool) =>
        (MulOpposite.unop a : FiniteRankProjectiveEndAlgebra.Incidence
          (k := ℚ) (S := Bool)) boolSource boolSource) hzero
    have hcoeff' : (1 : ℚ) = 0 := by
      simpa [IncidenceAlgebra.one_apply, IncidenceAlgebra.zero_apply] using hcoeff
    exact one_ne_zero hcoeff'
  letI : Nontrivial (RightIncidence (k := ℚ) (S := Bool)) := ⟨⟨1, 0, hone⟩⟩
  have hzero : (1 : RightIncidence (k := ℚ) (S := Bool)) = 0 := by
    calc
      (1 : RightIncidence (k := ℚ) (S := Bool)) = 2 - 1 := by norm_num
      _ = 1 - 1 := by rw [hval]
      _ = 0 := sub_self _
  exact one_ne_zero hzero

/-- Full faithfulness recovers a nonidentity regular-module morphism exactly. -/
theorem boolRegularDoubleEnd_recovered :
    (vertexFunctorHomEquiv (k := ℚ) (S := Bool)
      (boolRegular ℚ) (boolRegular ℚ)).symm
        ((vertexFunctor (k := ℚ) (S := Bool)).map boolRegularDoubleEnd) =
      boolRegularDoubleEnd := by
  exact (vertexFunctorHomEquiv (k := ℚ) (S := Bool)
    (boolRegular ℚ) (boolRegular ℚ)).symm_apply_apply _

private abbrev boolRegularProduct :=
  ModuleCat.of (RightIncidence (k := ℚ) (S := Bool))
    (RightIncidence (k := ℚ) (S := Bool) × RightIncidence (k := ℚ) (S := Bool))

private def boolSplitInclusion : boolRegular ℚ ⟶ boolRegularProduct :=
  ModuleCat.ofHom (LinearMap.inl (RightIncidence (k := ℚ) (S := Bool))
    (RightIncidence (k := ℚ) (S := Bool)) (RightIncidence (k := ℚ) (S := Bool)))

private def boolSplitProjection : boolRegularProduct ⟶ boolRegular ℚ :=
  ModuleCat.ofHom (LinearMap.snd (RightIncidence (k := ℚ) (S := Bool))
    (RightIncidence (k := ℚ) (S := Bool)) (RightIncidence (k := ℚ) (S := Bool)))

private theorem boolSplit_comp_eq_zero : boolSplitInclusion ≫ boolSplitProjection = 0 := by
  apply ModuleCat.hom_ext
  ext x
  simp [boolSplitInclusion, boolSplitProjection, LinearMap.inl_apply, LinearMap.snd_apply]

private def boolSplitShortComplex : ShortComplex (ModuleCat (RightIncidence (k := ℚ) (S := Bool))) :=
  ShortComplex.mk boolSplitInclusion boolSplitProjection boolSplit_comp_eq_zero

private theorem boolSplitShortComplex_shortExact : boolSplitShortComplex.ShortExact := by
  let R := RightIncidence (k := ℚ) (S := Bool)
  have hrange : LinearMap.range (LinearMap.inl R R R) =
      LinearMap.ker (LinearMap.snd R R R) := by
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      rw [LinearMap.mem_ker]
      simp [LinearMap.inl_apply, LinearMap.snd_apply]
    · intro hz
      rw [LinearMap.mem_ker] at hz
      rcases z with ⟨x, y⟩
      change y = 0 at hz
      refine ⟨x, ?_⟩
      simp [hz]
  let C := boolSplitShortComplex
  have hexact : C.Exact := by
    apply (ShortComplex.moduleCat_exact_iff_range_eq_ker C).2
    change LinearMap.range (LinearMap.inl R R R) =
      LinearMap.ker (LinearMap.snd R R R)
    exact hrange
  letI : Mono C.f := (ModuleCat.mono_iff_injective C.f).2 (by
    change Function.Injective (LinearMap.inl R R R)
    exact LinearMap.inl_injective)
  letI : Epi C.g := (ModuleCat.epi_iff_surjective C.g).2 (by
    change Function.Surjective (LinearMap.snd R R R)
    exact LinearMap.snd_surjective)
  exact ⟨hexact⟩

/-- The split regular-module row remains short exact on every vertex fiber. -/
theorem boolSplitShortComplex_vertexPointwise :
    IsPointwiseShortExact
      ((vertexFunctor (k := ℚ) (S := Bool)).map boolSplitInclusion)
      ((vertexFunctor (k := ℚ) (S := Bool)).map boolSplitProjection) :=
  (rightIncidenceShortExact_iff_vertexPointwise (k := ℚ) (S := Bool)
    boolSplitInclusion boolSplitProjection boolSplit_comp_eq_zero).mp
      boolSplitShortComplex_shortExact

end

end TDA.Persistence.IncidenceVertexRepresentationExamples
