import TDA.Persistence.FiniteRankProjectiveHomQuotientDimension
import TDA.Persistence.TwoInjectiveHomDimensionExamples

/-!
# Examples for actual Hom-cokernel dimensions

These examples use the infinite coefficient field `ℚ`, an actual nonzero
hook-generator Hom map, the actual cokernel of the two-injective differential,
zero and repeated-fiber modules, and one- and two-coordinate grids. The
resolution statements quantify over every supplied certificate and use
`termAt`, so terminal zero padding does not alter their scope.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence.FiniteRankProjectiveHomQuotientDimensionExamples

open CategoryTheory CategoryTheory.Limits
open TDA.Persistence.FiniteRankProjectiveEndAlgebra
open TDA.Persistence.FiniteRankProjectiveHomExact
open TDA.Persistence.IncidenceQuotientSimple
open TDA.Persistence.TwoInjectiveHomDimension
open TDA.Persistence.FiniteRankProjectiveHomQuotientDimension
open TDA.Persistence.FiniteLatticeComplementCardinality
open TDA.Persistence.FiniteInjectiveRankDimension
open scoped TDA.Persistence ModuleCat ZeroObject

noncomputable section

/-- The reused nonzero pointwise-finite source module over the infinite field
of rational numbers. -/
abbrev rationalSource := TwoInjectiveHomDimensionExamples.scalarLine

private theorem rationalSource_finiteDimensional (p : Fin 2) :
    FiniteDimensional ℚ (rationalSource.obj p) := by
  change FiniteDimensional ℚ ℚ
  infer_instance

/-- The actual two-injective Hom cokernel of the nonzero rational source has
the proved finite-lattice bound. -/
theorem rationalSource_actualCokernel_bound :
    letI : Lattice (PairPoset (Fin 2)) := pairPosetLattice (S := Fin 2)
    letI : BoundedOrder (PairPoset (Fin 2)) := pairPosetBoundedOrder (S := Fin 2)
    HasProjectiveDimensionLE (homCokernel rationalSource)
      (maxComplementCard (S := PairPoset (Fin 2))) := by
  exact homCokernel_hasProjectiveDimensionLE (k := ℚ) (S := Fin 2)
    rationalSource rationalSource_finiteDimensional

private instance : Fintype (HookTag (S := Fin 2)) := Fintype.ofFinite _

private abbrev rationalHookSum := HookSum (k := ℚ) (S := Fin 2)

private abbrev rationalHookTag : HookTag (S := Fin 2) := Sum.inr (0 : Fin 2)

/-- A nonzero actual morphism from the finite hook generator to the rational
source, obtained from the existing infinite-hook birth map. -/
private noncomputable def rationalHookMap : rationalHookSum ⟶ rationalSource :=
  biproduct.π (hookFamily (k := ℚ) (S := Fin 2)) rationalHookTag ≫
    HookInfinity.fromBirth (R := ℚ) 0 rationalSource (1 : ℚ)

private theorem rationalHookMap_nonzero : rationalHookMap ≠ 0 := by
  intro hzero
  let x : rationalHookSum.obj 0 :=
    (biproduct.ι (hookFamily (k := ℚ) (S := Fin 2)) rationalHookTag).app 0
      (HookInfinity.birth (R := ℚ) (0 : Fin 2))
  have hx : (rationalHookMap.app 0).hom x = (1 : ℚ) := by
    change ((HookInfinity.fromBirth (R := ℚ) 0 rationalSource (1 : ℚ)).app 0).hom
      (((biproduct.ι (hookFamily (k := ℚ) (S := Fin 2)) rationalHookTag ≫
        biproduct.π (hookFamily (k := ℚ) (S := Fin 2)) rationalHookTag).app 0).hom
          (HookInfinity.birth (R := ℚ) (0 : Fin 2))) = (1 : ℚ)
    rw [biproduct.ι_π_self]
    change ((HookInfinity.fromBirth (R := ℚ) 0 rationalSource (1 : ℚ)).app 0).hom
      (HookInfinity.birth (R := ℚ) (0 : Fin 2)) = (1 : ℚ)
    exact HookInfinity.fromBirth_birth _ _ _
  have hval : (rationalHookMap.app 0).hom x = 0 := by
    have h := congrArg (fun f : rationalHookSum ⟶ rationalSource => (f.app 0).hom x) hzero
    simpa using h
  rw [hx] at hval
  exact (by norm_num : (1 : ℚ) ≠ 0) hval

/-- Multiplying that actual Hom map by a nonzero rational remains nonzero
under the canonical-field/natural-Hom linear equivalence. -/
theorem rational_nonzeroHom_scalar_witness :
    let e := homScalarFieldLinearEquiv (k := ℚ) (S := Fin 2) rationalSource
    e ((7 : ℚ) • e.symm rationalHookMap) ≠ 0 := by
  dsimp only
  rw [map_smul, LinearEquiv.apply_symm_apply]
  exact smul_ne_zero (by norm_num) rationalHookMap_nonzero

/-- A singleton-factor one-coordinate real grid. -/
def singletonGrid : CoordinateGrid 1 := fun _ => {0}

private theorem singletonGrid_nonempty :
    ∀ i : Fin 1, (singletonGrid i).Nonempty := by
  intro i
  simp [singletonGrid]

/-- A nonzero one-dimensional module on that grid. -/
abbrev singletonGridModule : PModule ℚ singletonGrid.Point :=
  (Functor.const singletonGrid.Point).obj (ModuleCat.of ℚ ℚ)

private theorem singletonGridModule_finiteDimensional (p : singletonGrid.Point) :
    FiniteDimensional ℚ (singletonGridModule.obj p) := by
  change FiniteDimensional ℚ ℚ
  infer_instance

/-- The n=1 consumer has degree bound zero, with strict vanishing above zero. -/
theorem singletonGrid_Hom_projective :
    letI : BoundedOrder singletonGrid.Point :=
      coordinateGridBoundedOrder singletonGrid singletonGrid_nonempty
    HasProjectiveDimensionLE
      ((homFunctor (k := ℚ) (S := singletonGrid.Point)).obj singletonGridModule) 0 := by
  simpa using coordinateGrid_homFunctor_obj_hasProjectiveDimensionLE
    (k := ℚ) singletonGrid (by omega) singletonGrid_nonempty
    singletonGridModule singletonGridModule_finiteDimensional

/-- Every supplied certified minimal resolution on the one-coordinate grid
vanishes in degrees strictly above the degree-zero boundary. -/
theorem singletonGrid_terms_vanish_strictly_above_zero
    (R : MinimalFiniteRankProjectiveResolution (k := ℚ) (M := singletonGridModule)) :
    ∀ j, 0 < j → IsZero (R.termAt j) := by
  simpa using coordinateGrid_minimalResolution_termAt_isZero
    (k := ℚ) singletonGrid (by omega) singletonGrid_nonempty
    singletonGridModule singletonGridModule_finiteDimensional R

/-- A nonempty two-coordinate square grid. -/
def squareGrid : CoordinateGrid 2 := fun _ => {0, 1}

private theorem squareGrid_nonempty :
    ∀ i : Fin 2, (squareGrid i).Nonempty := by
  intro i
  simp [squareGrid]

/-- A nonzero rational module on the square grid. -/
abbrev squareGridModule : PModule ℚ squareGrid.Point :=
  (Functor.const squareGrid.Point).obj (ModuleCat.of ℚ ℚ)

private theorem squareGridModule_finiteDimensional (p : squareGrid.Point) :
    FiniteDimensional ℚ (squareGridModule.obj p) := by
  change FiniteDimensional ℚ ℚ
  infer_instance

/-- The actual Hom module on the two-coordinate grid satisfies the `2*n-2`
bound. -/
theorem squareGrid_Hom_projectiveDimension_le_two :
    letI : BoundedOrder squareGrid.Point :=
      coordinateGridBoundedOrder squareGrid squareGrid_nonempty
    HasProjectiveDimensionLE
      ((homFunctor (k := ℚ) (S := squareGrid.Point)).obj squareGridModule) 2 := by
  simpa using coordinateGrid_homFunctor_obj_hasProjectiveDimensionLE
    (k := ℚ) squareGrid (by omega) squareGrid_nonempty
    squareGridModule squareGridModule_finiteDimensional

/-- The actual two-injective Hom cokernel on the square grid has bound `2*n`. -/
theorem squareGrid_actualCokernel_projectiveDimension_le_four :
    letI : ∀ p, FiniteDimensional ℚ (squareGridModule.obj p) :=
      squareGridModule_finiteDimensional
    letI : BoundedOrder squareGrid.Point :=
      coordinateGridBoundedOrder squareGrid squareGrid_nonempty
    HasProjectiveDimensionLE (homCokernel squareGridModule) 4 := by
  simpa using coordinateGrid_homCokernel_hasProjectiveDimensionLE
    (k := ℚ) squareGrid (by omega) squareGrid_nonempty
    squareGridModule squareGridModule_finiteDimensional

/-- Every supplied certified minimal resolution on the square grid vanishes
strictly above degree two, independently of terminal zero padding. -/
theorem squareGrid_terms_vanish_strictly_above_two
    (R : MinimalFiniteRankProjectiveResolution (k := ℚ) (M := squareGridModule)) :
    ∀ j, 2 < j → IsZero (R.termAt j) :=
  coordinateGrid_minimalResolution_termAt_isZero
    (k := ℚ) squareGrid (by omega) squareGrid_nonempty
    squareGridModule squareGridModule_finiteDimensional R

/-- A constant repeated two-dimensional fiber on the one-coordinate grid. -/
abbrev repeatedGridModule : PModule ℚ singletonGrid.Point :=
  (Functor.const singletonGrid.Point).obj (ModuleCat.of ℚ (ℚ × ℚ))

private theorem repeatedGridModule_finiteDimensional (p : singletonGrid.Point) :
    FiniteDimensional ℚ (repeatedGridModule.obj p) := by
  change FiniteDimensional ℚ (ℚ × ℚ)
  infer_instance

/-- The fixture really retains two repeated rational fiber coordinates. -/
theorem repeatedGridModule_fiber_finrank :
    ∀ p : singletonGrid.Point, Module.finrank ℚ (repeatedGridModule.obj p) = 2 := by
  intro p
  change Module.finrank ℚ (ℚ × ℚ) = 2
  simp [Module.finrank_prod]

/-- Repeated fibers still satisfy the actual degree-zero grid Hom bound. -/
theorem repeatedGridModule_Hom_projective :
    letI : BoundedOrder singletonGrid.Point :=
      coordinateGridBoundedOrder singletonGrid singletonGrid_nonempty
    HasProjectiveDimensionLE
      ((homFunctor (k := ℚ) (S := singletonGrid.Point)).obj repeatedGridModule) 0 := by
  simpa using coordinateGrid_homFunctor_obj_hasProjectiveDimensionLE
    (k := ℚ) singletonGrid (by omega) singletonGrid_nonempty
    repeatedGridModule repeatedGridModule_finiteDimensional

/-- The zero persistence module is an actual consumer of the cokernel bound. -/
abbrev zeroGridModule : PModule ℚ singletonGrid.Point := 0

private theorem zeroGridModule_finiteDimensional (p : singletonGrid.Point) :
    FiniteDimensional ℚ (zeroGridModule.obj p) := by
  change FiniteDimensional ℚ ((0 : PModule ℚ singletonGrid.Point).obj p)
  infer_instance

/-- The actual Hom module of the zero object has the degree-zero grid bound. -/
theorem zeroGridModule_Hom_projective :
    letI : BoundedOrder singletonGrid.Point :=
      coordinateGridBoundedOrder singletonGrid singletonGrid_nonempty
    HasProjectiveDimensionLE
      ((homFunctor (k := ℚ) (S := singletonGrid.Point)).obj zeroGridModule) 0 := by
  simpa using coordinateGrid_homFunctor_obj_hasProjectiveDimensionLE
    (k := ℚ) singletonGrid (by omega) singletonGrid_nonempty
    zeroGridModule zeroGridModule_finiteDimensional

/-- The actual cokernel of Hom applied to the zero source also satisfies the
grid `2*n` estimate. -/
theorem zeroGridModule_actualCokernel_bound :
    letI : ∀ p, FiniteDimensional ℚ (zeroGridModule.obj p) :=
      zeroGridModule_finiteDimensional
    letI : BoundedOrder singletonGrid.Point :=
      coordinateGridBoundedOrder singletonGrid singletonGrid_nonempty
    HasProjectiveDimensionLE (homCokernel zeroGridModule) 2 := by
  simpa using coordinateGrid_homCokernel_hasProjectiveDimensionLE
    (k := ℚ) singletonGrid (by omega) singletonGrid_nonempty
    zeroGridModule zeroGridModule_finiteDimensional

end

end TDA.Persistence.FiniteRankProjectiveHomQuotientDimensionExamples
