import TDA.Persistence.IncidenceRegularVertex
import TDA.Persistence.IncidenceQuotientProjectiveResolution
import TDA.Persistence.OrdinaryFiniteLatticeDimension
import TDA.Persistence.FiniteLatticeComplementCardinality
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.CategoryTheory.Abelian.Projective.Dimension

/-!
# Ordinary projective dimensions of finite-dimensional incidence modules

Finite-dimensional actual right-incidence modules admit genuine finite-free
covers. Their kernels remain finite-dimensional over the coefficient field,
so the regular-module vertex decomposition gives an induction comparing
ordinary projective dimensions. The representation bound then yields the
unconditional finite-lattice bound for actual incidence modules and their
actual diagonal-quotient modules.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence.IncidenceVertexProjectiveDimension

open CategoryTheory CategoryTheory.Limits
open TDA.Persistence.FiniteRankProjectiveEndAlgebra
open TDA.Persistence.FiniteInjectiveRankDimension
open TDA.Persistence.FiniteLatticeComplementCardinality
open TDA.Persistence.IncidenceVertexRepresentation
open TDA.Persistence.IncidenceRegularVertex
open TDA.Persistence.IncidenceQuotientSimple
open TDA.Persistence.IncidenceQuotientBaseChange
open TDA.Persistence.IncidenceQuotientProjectiveResolution
open scoped ModuleCat

variable {k : Type u} [Field k] {S : Type} [Lattice S] [Finite S]

noncomputable section

local instance : Fintype S := Fintype.ofFinite S
local instance : DecidableLE S := Classical.decRel _
local instance : DecidableLT S := Classical.decRel _
local instance : DecidableEq S := Classical.decEq _
local instance : DecidableEq (WithTop S) := Classical.decEq _
local instance (p : Prop) : Decidable p := Classical.propDecidable p
local instance : Fintype (PairPoset S) :=
  Fintype.subtype (Finset.univ.filter fun ab : WithTop S × WithTop S => ab.1 ≤ ab.2)
    (by intro ab; simp)
local instance : DecidableLE (PairPoset S) := Classical.decRel _
local instance : DecidableLT (PairPoset S) := Classical.decRel _
local instance : LocallyFiniteOrder (PairPoset S) := Fintype.toLocallyFiniteOrder
local instance : DecidableEq (PairPoset S) := Classical.decEq _
local instance : Fintype (ComparablePair S) := Fintype.ofFinite _
local instance diagonalIdealTwoSided :
    (IncidenceQuotientSimple.DiagonalIdeal (k := k) (S := S)).IsTwoSided :=
  diagonalIdeal_isTwoSided (k := k) (S := S)

private abbrev V := vertexFunctor (k := k) (S := S)

private theorem fd_of_injective
    {X Y : ModuleCat.{u} (IncidenceQuotientBaseChange.RightIncidence (k := k) (S := S))}
    (i : X ⟶ Y) (hi : Function.Injective i.hom)
    (hY : FiniteDimensional k (restrictedKModule (k := k) (S := S) Y)) :
    FiniteDimensional k (restrictedKModule (k := k) (S := S) X) := by
  letI := hY
  exact FiniteDimensional.of_injective (i.hom.restrictScalars k) hi

private theorem restricted_finite_of_restrictScalars_finite
    (M : ModuleCat.{u} (IncidenceQuotientBaseChange.RightIncidence (k := k) (S := S)))
    (hM : FiniteDimensional k (restrictedKModule (k := k) (S := S) M)) :
    Module.Finite (IncidenceQuotientBaseChange.RightIncidence (k := k) (S := S)) M := by
  letI : FiniteDimensional k M := hM
  exact Module.Finite.of_restrictScalars_finite k (IncidenceQuotientBaseChange.RightIncidence (k := k) (S := S)) M

/-- If the actual vertex representation of a finite-dimensional right-incidence
module has projective dimension at most `d`, then the module itself has the
same ordinary projective-dimension bound. -/
theorem hasProjectiveDimensionLE_of_vertex
    (M : ModuleCat.{u} (IncidenceQuotientBaseChange.RightIncidence (k := k) (S := S)))
    (hM : FiniteDimensional k (restrictedKModule (k := k) (S := S) M))
    (d : ℕ)
    (hV : HasProjectiveDimensionLE ((V (k := k) (S := S)).obj M) d) :
    HasProjectiveDimensionLE M d := by
  induction d generalizing M with
  | zero =>
      apply (projective_iff_hasProjectiveDimensionLE_zero M).mp
      exact projective_of_vertex_projective (k := k) (S := S) M
        ((projective_iff_hasProjectiveDimensionLE_zero _).mpr hV)
  | succ d ih =>
      letI : Module.Finite (IncidenceQuotientBaseChange.RightIncidence (k := k) (S := S)) M :=
        restricted_finite_of_restrictScalars_finite (k := k) (S := S) M hM
      obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' (IncidenceQuotientBaseChange.RightIncidence (k := k) (S := S)) M
      let F : ModuleCat (IncidenceQuotientBaseChange.RightIncidence (k := k) (S := S)) := finiteFreeModule (k := k) (S := S) n
      let sf := LinearMap.shortComplexKer f
      have hsf : sf.ShortExact := LinearMap.shortExact_shortComplexKer hf
      let hcomp : sf.f ≫ sf.g = 0 := sf.zero
      let targetRow : ShortComplex (PModule.{u,0,u} k (PairPoset S)) :=
        ShortComplex.mk ((V (k := k) (S := S)).map sf.f)
          ((V (k := k) (S := S)).map sf.g) (by
            rw [← Functor.map_comp, hcomp]
            simp)
      have hpoint : IsPointwiseShortExact
          ((V (k := k) (S := S)).map sf.f)
          ((V (k := k) (S := S)).map sf.g) :=
        (rightIncidenceShortExact_iff_vertexPointwise (k := k) (S := S)
          sf.f sf.g hcomp).mp hsf
      have htarget : targetRow.ShortExact := hpoint.shortExact
      have hmiddleProj : Projective ((V (k := k) (S := S)).obj F) := by
        exact finiteFreeVertex_projective (k := k) (S := S) n
      have hmiddle : HasProjectiveDimensionLT ((V (k := k) (S := S)).obj F) (d + 1) :=
        hasProjectiveDimensionLT_of_ge _ 1 (d + 1) (by omega)
      let K : ModuleCat (IncidenceQuotientBaseChange.RightIncidence (k := k) (S := S)) :=
        ModuleCat.of (IncidenceQuotientBaseChange.RightIncidence (k := k) (S := S)) (LinearMap.ker f)
      let inclusion : K ⟶ F := ModuleCat.ofHom (LinearMap.ker f).subtype
      have hFfd := finiteFreeModule_finiteDimensional (k := k) (S := S) n
      have hKfd := fd_of_injective (k := k) (S := S) inclusion
        (LinearMap.ker f).injective_subtype hFfd
      have hVK : HasProjectiveDimensionLE ((V (k := k) (S := S)).obj K) d := by
        have hVK' : HasProjectiveDimensionLT ((V (k := k) (S := S)).obj K) (d + 1) :=
          htarget.hasProjectiveDimensionLT_X₁ (d + 1) hmiddle hV
        exact hVK'
      have hK : HasProjectiveDimensionLE K d :=
        ih K hKfd hVK
      have hfree : HasProjectiveDimensionLT F (d + 2) := by
        have hproj : Projective F := finiteFreeModule_projective (k := k) (S := S) n
        have h₁ : HasProjectiveDimensionLT F 1 :=
          projective_iff_hasProjectiveDimensionLT_one.mp hproj
        exact hasProjectiveDimensionLT_of_ge _ 1 (d + 2) (by omega)
      have htargetM : HasProjectiveDimensionLT M (d + 2) := by
        have hK' : HasProjectiveDimensionLT K (d + 1) := hK
        exact hsf.hasProjectiveDimensionLT_X₃ (d + 1) hK' hfree
      exact htargetM

/-- The actual quotient map preserves the canonical coefficient-field action. -/
theorem quotientHom_comp_algebraMap :
    algebraMap k (IncidenceQuotientBaseChange.RightQuotient (k := k) (S := S)) =
      (quotientHom (k := k) (S := S)).comp
        (algebraMap k (IncidenceQuotientBaseChange.RightIncidence (k := k) (S := S))) := by
  ext c
  simp [quotientHom]

/-- The two actual canonical restricted field modules agree through the quotient map. -/
noncomputable def quotientRestrictionIso
    (N : ModuleCat.{u} (IncidenceQuotientBaseChange.RightQuotient (k := k) (S := S))) :
    restrictRightQuotientModule (k := k) (S := S) N ≅
      restrictedKModule (k := k) (S := S)
        ((ModuleCat.restrictScalars (quotientHom (k := k) (S := S))).obj N) := by
  exact (ModuleCat.restrictScalarsComp'App
    (algebraMap k (IncidenceQuotientBaseChange.RightIncidence (k := k) (S := S)))
    (quotientHom (k := k) (S := S))
    (algebraMap k (IncidenceQuotientBaseChange.RightQuotient (k := k) (S := S)))
    (quotientHom_comp_algebraMap (k := k) (S := S)) N).symm

/-- Every finite-dimensional actual right-incidence module has projective
dimension at most the maximum minimal-complement cardinality of the actual
interval-pair poset. -/
theorem hasProjectiveDimensionLE
    [OrderBot S] [OrderTop S]
    (M : ModuleCat.{u} (IncidenceQuotientBaseChange.RightIncidence (k := k) (S := S)))
    (hM : FiniteDimensional k (restrictedKModule (k := k) (S := S) M)) :
    letI : Lattice (PairPoset S) := pairPosetLattice (S := S)
    letI : BoundedOrder (PairPoset S) := pairPosetBoundedOrder (S := S)
    HasProjectiveDimensionLE M (maxComplementCard (S := PairPoset S)) := by
  letI : Lattice (PairPoset S) := pairPosetLattice (S := S)
  letI : BoundedOrder (PairPoset S) := pairPosetBoundedOrder (S := S)
  have hpfd : ∀ p : PairPoset S,
      FiniteDimensional k (((V (k := k) (S := S)).obj M).obj p) := by
    intro p
    exact (finiteDimensional_iff_vertexFibers (k := k) (S := S) M).mp hM p
  letI : ∀ p : PairPoset S,
      FiniteDimensional k (((V (k := k) (S := S)).obj M).obj p) := hpfd
  have hV := OrdinaryFiniteLatticeDimension.hasProjectiveDimensionLE (k := k)
    ((V (k := k) (S := S)).obj M)
  exact hasProjectiveDimensionLE_of_vertex (k := k) (S := S) M hM _ hV

/-- Finite-dimensional actual right modules over the diagonal quotient satisfy
the same unconditional bound, via the proved quotient extension comparison. -/
theorem quotient_hasProjectiveDimensionLE
    [OrderBot S] [OrderTop S]
    (N : ModuleCat.{u} (IncidenceQuotientBaseChange.RightQuotient (k := k) (S := S)))
    (hN : FiniteDimensional k (restrictRightQuotientModule (k := k) (S := S) N)) :
    letI : Lattice (PairPoset S) := pairPosetLattice (S := S)
    letI : BoundedOrder (PairPoset S) := pairPosetBoundedOrder (S := S)
    HasProjectiveDimensionLE N (maxComplementCard (S := PairPoset S)) := by
  letI : Lattice (PairPoset S) := pairPosetLattice (S := S)
  letI : BoundedOrder (PairPoset S) := pairPosetBoundedOrder (S := S)
  letI : FiniteDimensional k (restrictRightQuotientModule (k := k) (S := S) N) := hN
  have hRes : FiniteDimensional k (restrictedKModule (k := k) (S := S)
      ((ModuleCat.restrictScalars (quotientHom (k := k) (S := S))).obj N)) :=
    (quotientRestrictionIso (k := k) (S := S) N).toLinearEquiv.finiteDimensional
  have hR := hasProjectiveDimensionLE (k := k) (S := S)
    ((ModuleCat.restrictScalars (quotientHom (k := k) (S := S))).obj N) hRes
  exact extension_hasProjectiveDimensionLE_restricted (k := k) (S := S) N _ hR

/-- The actual right-incidence module on a positive-dimensional coordinate grid
has ordinary projective dimension at most twice the number of coordinates. -/
theorem coordinateGrid_rightIncidence_hasProjectiveDimensionLE
    {n : ℕ} (G : CoordinateGrid n) (hn : 1 ≤ n)
    (hG : ∀ i : Fin n, (G i).Nonempty)
    (M : ModuleCat.{u} (IncidenceQuotientBaseChange.RightIncidence
      (k := k) (S := G.Point)))
    (hM : FiniteDimensional k (restrictedKModule (k := k) (S := G.Point) M)) :
    letI : BoundedOrder G.Point := coordinateGridBoundedOrder G hG
    HasProjectiveDimensionLE M (2 * n) := by
  letI : BoundedOrder G.Point := coordinateGridBoundedOrder G hG
  letI : Lattice (PairPoset G.Point) := pairPosetLattice (S := G.Point)
  letI : BoundedOrder (PairPoset G.Point) := pairPosetBoundedOrder (S := G.Point)
  have hcount := maxComplementCard_pair_coordinateGrid_le G hn hG
  letI : HasProjectiveDimensionLT M
      (maxComplementCard (S := PairPoset G.Point) + 1) :=
    hasProjectiveDimensionLE (k := k) (S := G.Point) M hM
  exact hasProjectiveDimensionLT_of_ge M _ _ (Nat.succ_le_succ hcount)

/-- The actual right-quotient module on a positive-dimensional coordinate grid
has ordinary projective dimension at most twice the number of coordinates. -/
theorem coordinateGrid_rightQuotient_hasProjectiveDimensionLE
    {n : ℕ} (G : CoordinateGrid n) (hn : 1 ≤ n)
    (hG : ∀ i : Fin n, (G i).Nonempty)
    (N : ModuleCat.{u} (IncidenceQuotientBaseChange.RightQuotient
      (k := k) (S := G.Point)))
    (hN : FiniteDimensional k (restrictRightQuotientModule (k := k) (S := G.Point) N)) :
    letI : BoundedOrder G.Point := coordinateGridBoundedOrder G hG
    HasProjectiveDimensionLE N (2 * n) := by
  letI : BoundedOrder G.Point := coordinateGridBoundedOrder G hG
  letI : Lattice (PairPoset G.Point) := pairPosetLattice (S := G.Point)
  letI : BoundedOrder (PairPoset G.Point) := pairPosetBoundedOrder (S := G.Point)
  have hcount := maxComplementCard_pair_coordinateGrid_le G hn hG
  letI : HasProjectiveDimensionLT N
      (maxComplementCard (S := PairPoset G.Point) + 1) :=
    quotient_hasProjectiveDimensionLE (k := k) (S := G.Point) N hN
  exact hasProjectiveDimensionLT_of_ge N _ _ (Nat.succ_le_succ hcount)

end

end TDA.Persistence.IncidenceVertexProjectiveDimension
