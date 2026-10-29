import TDA.Persistence.OrdinaryFiniteLatticeDimension
import TDA.Persistence.FiniteRankProjectiveResolutionExamples
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects

/-!
# Examples for ordinary finite-lattice dimension

The fixtures distinguish zero and nonzero hooks, the top and a proper
principal downset, and actual rational grid and interval-pair representations.
The padded zero resolution supplies a valid loose recorded-length bound only.
-/

set_option autoImplicit false

namespace TDA.Persistence.OrdinaryFiniteLatticeDimensionExamples

open CategoryTheory
open CategoryTheory.Limits
open TDA.Persistence
open TDA.Persistence.OrdinaryFiniteLatticeDimension
open TDA.Persistence.FiniteRankProjectiveResolutionExamples
open TDA.Persistence.FiniteInjectiveRankDimension
open TDA.Persistence.FiniteLatticeComplementCardinality
open TDA.Persistence.FiniteRankProjectiveEndAlgebra
open TDA.Persistence.PrincipalDownsetRankResolution
open scoped ZeroObject TDA.Persistence

/-- The equal-endpoint rational hook is the zero object. -/
theorem bool_equalEndpointHook_isZero :
    IsZero (Hook.module (k := ℚ) false false : PModule ℚ Bool) :=
  HookCokernel.hook_isZero false

/-- The equal-endpoint hook has ordinary projective dimension at most zero. -/
theorem bool_equalEndpointHook_hasProjectiveDimensionLE_zero :
    HasProjectiveDimensionLE (Hook.module (k := ℚ) false false : PModule ℚ Bool) 0 := by
  letI : HasProjectiveDimensionLT
      (Hook.module (k := ℚ) false false : PModule ℚ Bool) 0 :=
    bool_equalEndpointHook_isZero.hasProjectiveDimensionLT_zero
  exact hasProjectiveDimensionLT_of_ge _ 0 1 (by omega)

/-- A finite hook with distinct rational endpoints satisfies the proved one-step bound. -/
theorem bool_nonzeroFiniteHook_hasProjectiveDimensionLE_one :
    HasProjectiveDimensionLE (Hook.module (k := ℚ) false true : PModule ℚ Bool) 1 :=
  finiteHook_hasProjectiveDimensionLE_one (k := ℚ) (by decide)

/-- The distinguished birth vector witnesses that the finite hook is nonzero. -/
theorem bool_nonzeroFiniteHook_not_isZero :
    ¬ IsZero (Hook.module (k := ℚ) false true : PModule ℚ Bool) := by
  intro hzero
  have hsub : Subsingleton ((Hook.module (k := ℚ) false true : PModule ℚ Bool).obj false) :=
    ModuleCat.subsingleton_of_isZero (hzero.obj false)
  let x : ((Hook.module (k := ℚ) false true : PModule ℚ Bool).obj false) :=
    SupportInterval.one (Hook.support false true)
    (Hook.birth_mem (show false < true by decide))
  have hx : x = 0 := hsub.elim _ _
  have hval := congrArg Subtype.val hx
  simp [x, SupportInterval.one] at hval

/-- The top principal downset has ordinary dimension zero. -/
theorem bool_topPrincipalDownset_hasProjectiveDimensionLE_zero :
    HasProjectiveDimensionLE (PrincipalDownsetInjective.module (k := ℚ) (true : Bool)) 0 := by
  have hcard : complementCard (S := Bool) true = 0 :=
    (complementCard_eq_zero_iff (S := Bool) true).mpr rfl
  simpa [hcard] using
    (principalDownset_hasProjectiveDimensionLE (k := ℚ) (S := Bool) true)

/-- The proper bottom principal downset has the complement-count bound. -/
theorem bool_bottomPrincipalDownset_hasProjectiveDimensionLE :
    HasProjectiveDimensionLE (PrincipalDownsetInjective.module (k := ℚ) (false : Bool))
      (complementCard (S := Bool) false) :=
  principalDownset_hasProjectiveDimensionLE (k := ℚ) (S := Bool) false

/-- The zero rational representation is covered by the unconditional lattice theorem. -/
theorem bool_zero_hasProjectiveDimensionLE_max :
    HasProjectiveDimensionLE (0 : PModule.{0,0,0} ℚ Bool)
      (maxComplementCard (S := Bool)) :=
  OrdinaryFiniteLatticeDimension.hasProjectiveDimensionLE (k := ℚ) (S := Bool)
    (0 : PModule.{0,0,0} ℚ Bool)

/-- The old supplied two-term resolution of zero only yields the loose bound
by its recorded term count. -/
theorem paddedZeroResolution_hasProjectiveDimensionLE_two :
    HasProjectiveDimensionLE zeroModule 2 := by
  simpa [contractibleZeroResolution] using
    finiteRankProjectiveResolution_hasProjectiveDimensionLE (k := ℚ)
      (S := Fin 2) contractibleZeroResolution

noncomputable def rationalSingletonGrid : CoordinateGrid 1 := fun _ => {0}

noncomputable def rationalSingletonGridPoint : rationalSingletonGrid.Point :=
  fun _ => ⟨0, by simp [rationalSingletonGrid]⟩

noncomputable def rationalGridHook : PModule ℚ rationalSingletonGrid.Point :=
  HookInfinity.module (R := ℚ) rationalSingletonGridPoint

private theorem hookInfinity_finiteDimensional {P : Type} [Preorder P]
    (p q : P) :
    FiniteDimensional ℚ ((HookInfinity.module (R := ℚ) p).obj q) := by
  by_cases hp : p ≤ q
  · exact LinearEquiv.finiteDimensional
      (HookInfinity.fiberEquivOfLe (R := ℚ) hp).symm
  · haveI : Subsingleton ((HookInfinity.module (R := ℚ) p).obj q) := ⟨fun x y =>
      (HookInfinity.fiber_eq_zero_of_not_le (R := ℚ) hp x).trans
        (HookInfinity.fiber_eq_zero_of_not_le (R := ℚ) hp y).symm⟩
    exact FiniteDimensional.of_rank_eq_zero (by simp)

/-- A nonzero rational principal upset on the actual one-coordinate grid
satisfies the grid dimension bound. -/
theorem rationalGridHook_hasProjectiveDimensionLE_one :
    letI : BoundedOrder rationalSingletonGrid.Point :=
      coordinateGridBoundedOrder rationalSingletonGrid (by intro i; exact ⟨0, by simp [rationalSingletonGrid]⟩)
    HasProjectiveDimensionLE rationalGridHook 1 := by
  letI : BoundedOrder rationalSingletonGrid.Point :=
    coordinateGridBoundedOrder rationalSingletonGrid (by
      intro i
      exact ⟨0, by simp [rationalSingletonGrid]⟩)
  have hfd : ∀ p, FiniteDimensional ℚ (rationalGridHook.obj p) := by
    intro p
    exact hookInfinity_finiteDimensional rationalSingletonGridPoint p
  letI : ∀ p, FiniteDimensional ℚ (rationalGridHook.obj p) := hfd
  exact hasProjectiveDimensionLE_coordinateGrid (k := ℚ) rationalSingletonGrid
    (by intro i; exact ⟨0, by simp [rationalSingletonGrid]⟩) rationalGridHook

/-- A nonzero rational principal upset on the actual interval-pair poset of
the one-coordinate grid satisfies the `2n` bound. -/
theorem rationalPairGridHook_hasProjectiveDimensionLE_two :
    letI : BoundedOrder rationalSingletonGrid.Point :=
      coordinateGridBoundedOrder rationalSingletonGrid (by intro i; exact ⟨0, by simp [rationalSingletonGrid]⟩)
    letI : Lattice (PairPoset rationalSingletonGrid.Point) :=
      pairPosetLattice (S := rationalSingletonGrid.Point)
    letI : BoundedOrder (PairPoset rationalSingletonGrid.Point) :=
      pairPosetBoundedOrder (S := rationalSingletonGrid.Point)
    HasProjectiveDimensionLE
      (HookInfinity.module (R := ℚ)
        (⟨(⊥, ⊥), le_rfl⟩ : PairPoset rationalSingletonGrid.Point)) 2 := by
  letI : BoundedOrder rationalSingletonGrid.Point :=
    coordinateGridBoundedOrder rationalSingletonGrid (by
      intro i
      exact ⟨0, by simp [rationalSingletonGrid]⟩)
  letI : Lattice (PairPoset rationalSingletonGrid.Point) :=
    pairPosetLattice (S := rationalSingletonGrid.Point)
  letI : BoundedOrder (PairPoset rationalSingletonGrid.Point) :=
    pairPosetBoundedOrder (S := rationalSingletonGrid.Point)
  let p : PairPoset rationalSingletonGrid.Point := ⟨(⊥, ⊥), le_rfl⟩
  let M : PModule ℚ (PairPoset rationalSingletonGrid.Point) :=
    HookInfinity.module (R := ℚ) p
  letI : ∀ q, FiniteDimensional ℚ (M.obj q) := by
    intro q
    exact hookInfinity_finiteDimensional p q
  exact hasProjectiveDimensionLE_pairCoordinateGrid (k := ℚ)
    rationalSingletonGrid (by omega)
    (by intro i; exact ⟨0, by simp [rationalSingletonGrid]⟩) M

end TDA.Persistence.OrdinaryFiniteLatticeDimensionExamples
