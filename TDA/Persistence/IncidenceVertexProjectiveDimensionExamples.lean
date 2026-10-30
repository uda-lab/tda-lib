import TDA.Persistence.IncidenceVertexProjectiveDimension
import TDA.Persistence.IncidenceQuotientDimension
import TDA.Persistence.IncidenceVertexRepresentationExamples
import TDA.Persistence.FiniteGridComplementCardinalityExamples
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects

/-!
# Examples for actual incidence-module projective dimensions

These fixtures include zero and rank-zero boundaries, the nonzero regular
vertex image, an actual nonzero quotient vertex module, the canonical quotient
scalar-restriction identification, and actual incidence and quotient modules
on one- and two-coordinate grids.
-/

set_option autoImplicit false

namespace TDA.Persistence.IncidenceVertexProjectiveDimensionExamples

open CategoryTheory CategoryTheory.Limits
open PrincipalDownsetRankResolution
open TDA.Persistence.FiniteInjectiveRankDimension
open TDA.Persistence.FiniteRankProjectiveEndAlgebra
open TDA.Persistence.FiniteRankProjectiveDiagonalIdealProjective
open TDA.Persistence.FiniteLatticeComplementCardinality
open TDA.Persistence.IncidenceVertexRepresentation
open TDA.Persistence.IncidenceRegularVertex
open TDA.Persistence.IncidenceQuotientSimple
open TDA.Persistence.IncidenceQuotientBaseChange
open TDA.Persistence.IncidenceQuotientDimension
open TDA.Persistence.IncidenceVertexProjectiveDimension
open TDA.Persistence.FiniteLatticeComplementCardinality.Examples
open scoped ModuleCat

noncomputable section

open scoped TDA.Persistence.FiniteRankProjectiveEndAlgebra.PairPoset

local instance : OrderBot Bool :=
  letI : Fintype Bool := Fintype.ofFinite Bool
  Fintype.toOrderBot Bool
local instance : OrderTop Bool :=
  letI : Fintype Bool := Fintype.ofFinite Bool
  Fintype.toOrderTop Bool
local instance : Lattice (FiniteRankProjectiveEndAlgebra.PairPoset Bool) := pairPosetLattice (S := Bool)
local instance : BoundedOrder (FiniteRankProjectiveEndAlgebra.PairPoset Bool) := pairPosetBoundedOrder (S := Bool)

/-- The canonical two-sidedness proof for the Bool diagonal ideal. -/
abbrev boolDiagonalIdealTwoSided :
    (IncidenceQuotientSimple.DiagonalIdeal (k := ℚ) (S := Bool)).IsTwoSided :=
  TDA.Persistence.FiniteRankProjectiveEndAlgebra.diagonalIdealIsTwoSided
    (k := ℚ) (S := Bool)

private abbrev boolZeroRightIncidence :
    ModuleCat.{0} (IncidenceQuotientBaseChange.RightIncidence (k := ℚ) (S := Bool)) :=
  ModuleCat.of (IncidenceQuotientBaseChange.RightIncidence (k := ℚ) (S := Bool)) PUnit

private theorem boolZeroRightIncidence_finiteDimensional :
    FiniteDimensional ℚ
      (restrictedKModule (k := ℚ) (S := Bool) boolZeroRightIncidence) := by
  letI : Subsingleton (restrictedKModule (k := ℚ) (S := Bool) boolZeroRightIncidence) := inferInstance
  exact FiniteDimensional.of_rank_eq_zero (by simp)

/-- The actual zero incidence module satisfies the unconditional complement bound. -/
theorem bool_zero_rightIncidence_bound :
    letI : Lattice (FiniteRankProjectiveEndAlgebra.PairPoset Bool) := pairPosetLattice (S := Bool)
    letI : BoundedOrder (FiniteRankProjectiveEndAlgebra.PairPoset Bool) := pairPosetBoundedOrder (S := Bool)
    HasProjectiveDimensionLE boolZeroRightIncidence
      (maxComplementCard (S := FiniteRankProjectiveEndAlgebra.PairPoset Bool)) := by
  letI : Lattice (FiniteRankProjectiveEndAlgebra.PairPoset Bool) := pairPosetLattice (S := Bool)
  letI : BoundedOrder (FiniteRankProjectiveEndAlgebra.PairPoset Bool) := pairPosetBoundedOrder (S := Bool)
  exact hasProjectiveDimensionLE (k := ℚ) (S := Bool) boolZeroRightIncidence
    boolZeroRightIncidence_finiteDimensional

private abbrev boolRegular := regularRightIncidenceModule (k := ℚ) (S := Bool)

/-- The actual Bool regular module is free of rank one and projective. -/
theorem bool_regular_module_projective : Projective boolRegular :=
  ModuleCat.projective_of_free
    (Module.Basis.singleton Unit (IncidenceQuotientBaseChange.RightIncidence (k := ℚ) (S := Bool)))

/-- The regular module has a nonzero projective vertex image from its actual
graded-free decomposition. -/
theorem bool_regular_vertex_projective :
    Projective ((vertexFunctor (k := ℚ) (S := Bool)).obj boolRegular) :=
  regularVertex_projective (k := ℚ) (S := Bool)

private def boolBirthGrade : FiniteRankProjectiveEndAlgebra.PairPoset Bool :=
  ⟨((false : WithTop Bool), (false : WithTop Bool)), by simp⟩

/-- The public regular-vertex coefficient and birth laws identify the
diagonal projector's coefficient with the corresponding free birth value. -/
theorem bool_regularVertexIso_birth_coefficient :
    (((regularVertexIso (k := ℚ) (S := Bool)).hom.app boolBirthGrade
      (projectToVertexFiber (k := ℚ) (S := Bool) boolRegular boolBirthGrade 1) :
      (freeVertexModule (k := ℚ) (S := Bool)).obj boolBirthGrade).val boolBirthGrade) = 1 := by
  calc
    _ = (MulOpposite.unop
        ((projectToVertexFiber (k := ℚ) (S := Bool) boolRegular boolBirthGrade 1).val :
          IncidenceQuotientBaseChange.RightIncidence (k := ℚ) (S := Bool)) :
        FiniteRankProjectiveEndAlgebra.Incidence (k := ℚ) (S := Bool))
          boolBirthGrade boolBirthGrade :=
      regularVertexIso_hom_coefficient (k := ℚ) (S := Bool)
        boolBirthGrade boolBirthGrade _
    _ = ((GradedFree.birth (R := ℚ) (generators (S := Bool))
        boolBirthGrade : (freeVertexModule (k := ℚ) (S := Bool)).obj boolBirthGrade).val
          boolBirthGrade) := by
      exact (regularVertexIso_hom_coefficient (k := ℚ) (S := Bool)
        boolBirthGrade boolBirthGrade _).symm.trans
          (congrArg (fun z : (freeVertexModule (k := ℚ) (S := Bool)).obj boolBirthGrade =>
            z.val boolBirthGrade)
            (regularVertexIso_hom_birth (k := ℚ) (S := Bool) boolBirthGrade))
    _ = 1 := by simp [GradedFree.birth, GradedFree.generator]

/-- The regular module's actual ordinary projective-dimension comparison is
exercised at degree zero using its proved finite-dimensionality and projective
vertex image. -/
theorem bool_regular_hasProjectiveDimensionLE_zero :
    HasProjectiveDimensionLE boolRegular 0 := by
  have hV : HasProjectiveDimensionLE
      ((vertexFunctor (k := ℚ) (S := Bool)).obj boolRegular) 0 :=
    (projective_iff_hasProjectiveDimensionLE_zero
      ((vertexFunctor (k := ℚ) (S := Bool)).obj boolRegular)).mp
      bool_regular_vertex_projective
  exact hasProjectiveDimensionLE_of_vertex (k := ℚ) (S := Bool) boolRegular
    (regular_finiteDimensional (k := ℚ) (S := Bool)) 0
    hV

/-- The regular vertex image is nonzero because its actual graded-free
decomposition contains the birth vector. -/
theorem bool_regular_vertex_not_isZero :
    ¬ IsZero ((vertexFunctor (k := ℚ) (S := Bool)).obj boolRegular) := by
  intro hz
  have hfree : IsZero (freeVertexModule (k := ℚ) (S := Bool)) :=
    IsZero.of_iso hz (regularVertexIso (k := ℚ) (S := Bool)).symm
  have hsub : Subsingleton ((freeVertexModule (k := ℚ) (S := Bool)).obj boolBirthGrade) :=
    ModuleCat.subsingleton_of_isZero (hfree.obj boolBirthGrade)
  have hzero := hsub.elim
    (GradedFree.birth (R := ℚ) (generators (S := Bool)) boolBirthGrade) 0
  have hval := congrArg
    (fun x : (freeVertexModule (k := ℚ) (S := Bool)).obj boolBirthGrade => x.val) hzero
  have hcoeff := congrArg
    (fun f : FiniteRankProjectiveEndAlgebra.PairPoset Bool →₀ ℚ => f boolBirthGrade) hval
  change (Finsupp.single boolBirthGrade (1 : ℚ)) boolBirthGrade =
    (0 : FiniteRankProjectiveEndAlgebra.PairPoset Bool →₀ ℚ) boolBirthGrade at hcoeff
  have hcontradiction : (1 : ℚ) = 0 := by simpa using hcoeff
  norm_num at hcontradiction

/-- The rank-zero finite-free incidence module is projective, giving the
zero-degree base case. -/
theorem bool_free_zero_projective :
    Projective (finiteFreeModule (k := ℚ) (S := Bool) 0) :=
  finiteFreeModule_projective (k := ℚ) (S := Bool) 0

private def boolLowerStrictVertex : StrictVertex Bool :=
  ⟨⟨((false : WithTop Bool), (true : WithTop Bool)), by simp⟩, by simp⟩

private abbrev boolLowerQuotientVertex :=
  IncidenceQuotientSimple.RightVertexModule (k := ℚ) (S := Bool) boolLowerStrictVertex

/-- The strict quotient vertex module is an actual nonzero object. -/
theorem bool_lower_quotient_vertex_not_isZero : ¬ IsZero boolLowerQuotientVertex := by
  intro hz
  have hsub : Subsingleton boolLowerQuotientVertex :=
    ModuleCat.subsingleton_of_isZero hz
  change Subsingleton ℚ at hsub
  have hzero : (1 : ℚ) = 0 := hsub.elim 1 0
  norm_num at hzero

/-- The actual nonzero finite-dimensional strict quotient vertex module satisfies
the unconditional complement-count bound. -/
theorem bool_lower_quotient_vertex_dimension_bound :
    letI : Lattice (FiniteRankProjectiveEndAlgebra.PairPoset Bool) := pairPosetLattice (S := Bool)
    letI : BoundedOrder (FiniteRankProjectiveEndAlgebra.PairPoset Bool) := pairPosetBoundedOrder (S := Bool)
    HasProjectiveDimensionLE boolLowerQuotientVertex
      (maxComplementCard (S := FiniteRankProjectiveEndAlgebra.PairPoset Bool)) := by
  letI : Lattice (FiniteRankProjectiveEndAlgebra.PairPoset Bool) := pairPosetLattice (S := Bool)
  letI : BoundedOrder (FiniteRankProjectiveEndAlgebra.PairPoset Bool) := pairPosetBoundedOrder (S := Bool)
  exact quotient_hasProjectiveDimensionLE (k := ℚ) (S := Bool)
    boolLowerQuotientVertex
    (rightVertexModule_finiteDimensional (k := ℚ) (S := Bool) boolLowerStrictVertex)

/-- The canonical quotient scalar-restriction isomorphism is the identity on
vectors; its linearity follows from actual quotient-character compatibility. -/
theorem bool_quotientRestrictionIso_hom_apply
    (x : restrictRightQuotientModule (k := ℚ) (S := Bool) boolLowerQuotientVertex) :
    (quotientRestrictionIso (k := ℚ) (S := Bool) boolLowerQuotientVertex).hom x = x := by
  rfl

private theorem singletonGrid_nonempty :
    ∀ i : Fin 1, (singletonGrid i).Nonempty := by
  intro i
  simp [singletonGrid]

private theorem squareGrid_nonempty :
    ∀ i : Fin 2, (squareGrid i).Nonempty := by
  intro i
  simp [squareGrid]

local instance : BoundedOrder squareGrid.Point := coordinateGridBoundedOrder squareGrid squareGrid_nonempty
local instance : Lattice (FiniteRankProjectiveEndAlgebra.PairPoset squareGrid.Point) := pairPosetLattice (S := squareGrid.Point)
local instance : BoundedOrder (FiniteRankProjectiveEndAlgebra.PairPoset squareGrid.Point) := pairPosetBoundedOrder (S := squareGrid.Point)

/-- The canonical two-sidedness proof for the square-grid diagonal ideal. -/
abbrev squareGridDiagonalIdealTwoSided :
    (IncidenceQuotientSimple.DiagonalIdeal (k := ℚ) (S := squareGrid.Point)).IsTwoSided :=
  TDA.Persistence.FiniteRankProjectiveEndAlgebra.diagonalIdealIsTwoSided
    (k := ℚ) (S := squareGrid.Point)

local instance : BoundedOrder singletonGrid.Point := coordinateGridBoundedOrder singletonGrid singletonGrid_nonempty
local instance : Lattice (FiniteRankProjectiveEndAlgebra.PairPoset singletonGrid.Point) := pairPosetLattice (S := singletonGrid.Point)
local instance : BoundedOrder (FiniteRankProjectiveEndAlgebra.PairPoset singletonGrid.Point) := pairPosetBoundedOrder (S := singletonGrid.Point)

/-- The canonical two-sidedness proof for the singleton-grid diagonal ideal. -/
abbrev singletonGridDiagonalIdealTwoSided :
    (IncidenceQuotientSimple.DiagonalIdeal (k := ℚ) (S := singletonGrid.Point)).IsTwoSided :=
  TDA.Persistence.FiniteRankProjectiveEndAlgebra.diagonalIdealIsTwoSided
    (k := ℚ) (S := singletonGrid.Point)

private abbrev singletonGridZeroR :
    ModuleCat.{0} (IncidenceQuotientBaseChange.RightIncidence (k := ℚ) (S := singletonGrid.Point)) :=
  ModuleCat.of (IncidenceQuotientBaseChange.RightIncidence (k := ℚ) (S := singletonGrid.Point)) PUnit

private theorem singletonGridZeroR_finiteDimensional :
    FiniteDimensional ℚ (restrictedKModule (k := ℚ) (S := singletonGrid.Point) singletonGridZeroR) := by
  letI : Subsingleton (restrictedKModule (k := ℚ) (S := singletonGrid.Point) singletonGridZeroR) := inferInstance
  exact FiniteDimensional.of_rank_eq_zero (by simp)

private abbrev singletonGridZeroC :
    ModuleCat.{0} (IncidenceQuotientSimple.RightQuotient (k := ℚ) (S := singletonGrid.Point)) :=
  ModuleCat.of (IncidenceQuotientSimple.RightQuotient (k := ℚ) (S := singletonGrid.Point)) PUnit

private theorem singletonGridZeroC_finiteDimensional :
    FiniteDimensional ℚ (restrictRightQuotientModule (k := ℚ) (S := singletonGrid.Point)
      singletonGridZeroC) := by
  letI : Subsingleton PUnit := inferInstance
  change FiniteDimensional ℚ PUnit
  exact FiniteDimensional.of_injective (0 : PUnit →ₗ[ℚ] ℚ)
    (fun x y _ => Subsingleton.elim x y)

/-- The actual incidence zero module on a one-coordinate grid satisfies 2*n. -/
theorem rational_singleton_grid_zero_rightIncidence_bound :
    letI : BoundedOrder singletonGrid.Point :=
      coordinateGridBoundedOrder singletonGrid singletonGrid_nonempty
    HasProjectiveDimensionLE singletonGridZeroR 2 := by
  letI : BoundedOrder singletonGrid.Point :=
    coordinateGridBoundedOrder singletonGrid singletonGrid_nonempty
  exact coordinateGrid_rightIncidence_hasProjectiveDimensionLE (k := ℚ) (n := 1)
    singletonGrid (by norm_num) singletonGrid_nonempty singletonGridZeroR
    singletonGridZeroR_finiteDimensional

/-- The actual quotient zero module on a one-coordinate grid satisfies 2*n. -/
theorem rational_singleton_grid_zero_rightQuotient_bound :
    letI : BoundedOrder singletonGrid.Point :=
      coordinateGridBoundedOrder singletonGrid singletonGrid_nonempty
    HasProjectiveDimensionLE singletonGridZeroC 2 := by
  letI : BoundedOrder singletonGrid.Point :=
    coordinateGridBoundedOrder singletonGrid singletonGrid_nonempty
  exact coordinateGrid_rightQuotient_hasProjectiveDimensionLE (k := ℚ) (n := 1)
    singletonGrid (by norm_num) singletonGrid_nonempty singletonGridZeroC
    singletonGridZeroC_finiteDimensional

private abbrev squareGridZeroR :
    ModuleCat.{0} (IncidenceQuotientBaseChange.RightIncidence (k := ℚ) (S := squareGrid.Point)) :=
  ModuleCat.of (IncidenceQuotientBaseChange.RightIncidence (k := ℚ) (S := squareGrid.Point)) PUnit

private theorem squareGridZeroR_finiteDimensional :
    FiniteDimensional ℚ (restrictedKModule (k := ℚ) (S := squareGrid.Point) squareGridZeroR) := by
  letI : Subsingleton (restrictedKModule (k := ℚ) (S := squareGrid.Point) squareGridZeroR) := inferInstance
  exact FiniteDimensional.of_rank_eq_zero (by simp)

private abbrev squareGridZeroC :
    ModuleCat.{0} (IncidenceQuotientSimple.RightQuotient (k := ℚ) (S := squareGrid.Point)) :=
  ModuleCat.of (IncidenceQuotientSimple.RightQuotient (k := ℚ) (S := squareGrid.Point)) PUnit

private theorem squareGridZeroC_finiteDimensional :
    FiniteDimensional ℚ (restrictRightQuotientModule (k := ℚ) (S := squareGrid.Point)
      squareGridZeroC) := by
  letI : Subsingleton PUnit := inferInstance
  change FiniteDimensional ℚ PUnit
  exact FiniteDimensional.of_injective (0 : PUnit →ₗ[ℚ] ℚ)
    (fun x y _ => Subsingleton.elim x y)

/-- The actual incidence zero module on a two-coordinate grid satisfies 2*n. -/
theorem rational_square_grid_zero_rightIncidence_bound :
    letI : BoundedOrder squareGrid.Point :=
      coordinateGridBoundedOrder squareGrid squareGrid_nonempty
    HasProjectiveDimensionLE squareGridZeroR 4 := by
  letI : BoundedOrder squareGrid.Point :=
    coordinateGridBoundedOrder squareGrid squareGrid_nonempty
  exact coordinateGrid_rightIncidence_hasProjectiveDimensionLE (k := ℚ) (n := 2)
    squareGrid (by norm_num) squareGrid_nonempty squareGridZeroR
    squareGridZeroR_finiteDimensional

/-- The actual quotient zero module on a two-coordinate grid satisfies 2*n. -/
theorem rational_square_grid_zero_rightQuotient_bound :
    letI : BoundedOrder squareGrid.Point :=
      coordinateGridBoundedOrder squareGrid squareGrid_nonempty
    HasProjectiveDimensionLE squareGridZeroC 4 := by
  letI : BoundedOrder squareGrid.Point :=
    coordinateGridBoundedOrder squareGrid squareGrid_nonempty
  exact coordinateGrid_rightQuotient_hasProjectiveDimensionLE (k := ℚ) (n := 2)
    squareGrid (by norm_num) squareGrid_nonempty squareGridZeroC
    squareGridZeroC_finiteDimensional

end

end TDA.Persistence.IncidenceVertexProjectiveDimensionExamples
