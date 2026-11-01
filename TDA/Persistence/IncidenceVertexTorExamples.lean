import TDA.Persistence.IncidenceVertexTor
import TDA.Persistence.IncidenceRegularVertex
import TDA.Persistence.IncidenceQuotientProjectiveResolution
import Mathlib.Data.ZMod.Basic

/-!
# Examples for derived incidence-algebra vertex tensors

These examples instantiate the actual quotient resolution at strict vertices of `Bool` and `Unit`.
They are valid over every field; `ℚ` is included as a concrete infinite coefficient field.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence.IncidenceVertexTorExamples

open CategoryTheory
open CategoryTheory.Limits
open TDA.Persistence.FiniteRankProjectiveEndAlgebra
open TDA.Persistence.IncidenceVertexTensorFunctor
open TDA.Persistence.IncidenceVertexTor

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

private def boolStrictVertex : StrictVertex Bool :=
  ⟨⟨(true, ⊤), le_top⟩, by simp⟩

theorem bool_degree_one_leftDerived_isZero {k : Type} [Field k] :
    IsZero (((vertexTensor (k := k) (S := Bool) boolStrictVertex).leftDerived 1).obj
      (diagonalQuotientModule (k := k) (S := Bool))) :=
  diagonalQuotient_leftDerived_pos_isZero (k := k) (S := Bool) boolStrictVertex 1
    (Nat.zero_lt_succ 0)

theorem bool_degree_three_leftDerived_isZero {k : Type} [Field k] :
    IsZero (((vertexTensor (k := k) (S := Bool) boolStrictVertex).leftDerived 3).obj
      (diagonalQuotientModule (k := k) (S := Bool))) :=
  diagonalQuotient_leftDerived_pos_isZero (k := k) (S := Bool) boolStrictVertex 3
    (Nat.zero_lt_succ 2)

theorem bool_degree_zero_leftDerived_not_isZero {k : Type} [Field k] :
    ¬ IsZero (((vertexTensor (k := k) (S := Bool) boolStrictVertex).leftDerived 0).obj
      (diagonalQuotientModule (k := k) (S := Bool))) :=
  diagonalQuotient_leftDerivedZero_not_isZero (k := k) (S := Bool) boolStrictVertex

theorem bool_degree_zero_unit_law {k : Type} [Field k] :
    (diagonalQuotient_leftDerivedZeroIso (k := k) (S := Bool) boolStrictVertex).hom
      (((Functor.leftDerivedZeroIsoSelf
        (vertexTensor (k := k) (S := Bool) boolStrictVertex)).app
        (diagonalQuotientModule (k := k) (S := Bool))).inv.hom
        (mk (k := k) (S := Bool) boolStrictVertex
          (diagonalQuotientModule (k := k) (S := Bool)) 1)) = (1 : k) :=
  diagonalQuotient_leftDerivedZeroIso_hom_unit
    (k := k) (S := Bool) boolStrictVertex

local instance : Fintype Unit := Fintype.ofFinite Unit
local instance : DecidableLE Unit := Classical.decRel _
local instance : DecidableLT Unit := Classical.decRel _
local instance : DecidableEq Unit := Classical.decEq _
local instance : DecidableEq (WithTop Unit) := Classical.decEq _
local instance (p : Prop) : Decidable p := Classical.propDecidable p
local instance : Fintype (PairPoset Unit) :=
  Fintype.subtype (Finset.univ.filter fun ab : WithTop Unit × WithTop Unit => ab.1 ≤ ab.2)
    (by intro ab; simp)
local instance : DecidableLE (PairPoset Unit) := Classical.decRel _
local instance : DecidableLT (PairPoset Unit) := Classical.decRel _
local instance : LocallyFiniteOrder (PairPoset Unit) := Fintype.toLocallyFiniteOrder
local instance : DecidableEq (PairPoset Unit) := Classical.decEq _
local instance : Fintype (ComparablePair Unit) := Fintype.ofFinite _

private def singletonStrictVertex : StrictVertex Unit :=
  ⟨⟨((), ⊤), le_top⟩, by simp⟩

theorem singleton_degree_one_leftDerived_isZero {k : Type} [Field k] :
    IsZero (((vertexTensor (k := k) (S := Unit) singletonStrictVertex).leftDerived 1).obj
      (diagonalQuotientModule (k := k) (S := Unit))) :=
  diagonalQuotient_leftDerived_pos_isZero (k := k) (S := Unit) singletonStrictVertex 1
    (Nat.zero_lt_succ 0)

theorem singleton_degree_two_leftDerived_isZero {k : Type} [Field k] :
    IsZero (((vertexTensor (k := k) (S := Unit) singletonStrictVertex).leftDerived 2).obj
      (diagonalQuotientModule (k := k) (S := Unit))) :=
  diagonalQuotient_leftDerived_pos_isZero (k := k) (S := Unit) singletonStrictVertex 2
    (Nat.zero_lt_succ 1)

theorem singleton_degree_zero_leftDerived_not_isZero {k : Type} [Field k] :
    ¬ IsZero (((vertexTensor (k := k) (S := Unit) singletonStrictVertex).leftDerived 0).obj
      (diagonalQuotientModule (k := k) (S := Unit))) :=
  diagonalQuotient_leftDerivedZero_not_isZero (k := k) (S := Unit) singletonStrictVertex

theorem singleton_degree_zero_unit_law {k : Type} [Field k] :
    (diagonalQuotient_leftDerivedZeroIso (k := k) (S := Unit) singletonStrictVertex).hom
      (((Functor.leftDerivedZeroIsoSelf
        (vertexTensor (k := k) (S := Unit) singletonStrictVertex)).app
        (diagonalQuotientModule (k := k) (S := Unit))).inv.hom
        (mk (k := k) (S := Unit) singletonStrictVertex
          (diagonalQuotientModule (k := k) (S := Unit)) 1)) = (1 : k) :=
  diagonalQuotient_leftDerivedZeroIso_hom_unit
    (k := k) (S := Unit) singletonStrictVertex

theorem rationalField_infinite : Infinite ℚ := inferInstance

end

end TDA.Persistence.IncidenceVertexTorExamples

namespace TDA.Persistence.IncidenceVertexTorExamples.PublicInterface

open CategoryTheory CategoryTheory.Limits
open TDA.Persistence
open TDA.Persistence.FiniteRankProjectiveEndAlgebra
open TDA.Persistence.IncidenceVertexTensor
open TDA.Persistence.IncidenceVertexTensorFunctor
open TDA.Persistence.IncidenceVertexTor
open TDA.Persistence.IncidenceRegularVertex
open TDA.Persistence.IncidenceQuotientBaseChange
open TDA.Persistence.IncidenceQuotientColumnAction
open TDA.Persistence.IncidenceQuotientProjectiveResolution
open scoped TDA.Persistence.FiniteRankProjectiveEndAlgebra.PairPoset

noncomputable section

variable {k : Type u} [Field k] {S : Type} [Lattice S] [Finite S]

/-- The bundled left-module coinvariants expose their actual scalar transport to the
natural quotient-field action. -/
def coinvariantsTransport_publicType (v : StrictVertex S) :
    coinvariants (k := k) (S := S) v (diagonalQuotientModule (k := k) (S := S)) ≃ₗ[k]
      DiagonalQuotientVertexCoinvariants (k := k) (S := S) v :=
  diagonalQuotientVertexCoinvariantsEquiv (k := k) (S := S) v

/-- The public transport sends each quotient representative to its natural quotient class. -/
theorem coinvariantsTransport_representative (v : StrictVertex S)
    (b : IncidenceVertexTor.DiagonalQuotient (k := k) (S := S)) :
    diagonalQuotientVertexCoinvariantsEquiv (k := k) (S := S) v
      (mk (k := k) (S := S) v (diagonalQuotientModule (k := k) (S := S)) b) =
      (diagonalQuotientVertexRelation (k := k) (S := S) v).mkQ b :=
  diagonalQuotientVertexCoinvariantsEquiv_mkQ (k := k) (S := S) v b

/-- The public family consists of regular right-incidence modules. -/
def regularFamily_publicType (n : ℕ) :
    Fin n → ModuleCat.{u} (IncidenceRegularVertex.RightIncidence (k := k) (S := S)) :=
  regularFamily (k := k) (S := S) n

/-- The regular family has its original constant value. -/
theorem regularFamily_value (n : ℕ) (i : Fin n) :
    regularFamily (k := k) (S := S) n i = IncidenceRegularVertex.regular (k := k) (S := S) := rfl

/-- The existing finite-free vertex map is the biproduct of the public regular family. -/
def finiteFreeVertexBiproductIso_public (n : ℕ) :
    (⨁ fun i : Fin n => (IncidenceVertexRepresentation.vertexFunctor (k := k) (S := S)).obj
      (regularFamily (k := k) (S := S) n i)) ≅
      (IncidenceVertexRepresentation.vertexFunctor (k := k) (S := S)).obj
        (finiteFreeModule (k := k) (S := S) n) :=
  finiteFreeVertexBiproductIso (k := k) (S := S) n

/-- The regular-vertex isomorphism remains natural on every interval-pair map. -/
theorem regularVertexIso_naturality_public (p q : PairPoset S) (f : p ⟶ q) :
    ((IncidenceVertexRepresentation.vertexFunctor (k := k) (S := S)).obj
      (regular (k := k) (S := S))).map f ≫
      (regularVertexIso (k := k) (S := S)).hom.app q =
    (regularVertexIso (k := k) (S := S)).hom.app p ≫
      (freeVertexModule (k := k) (S := S)).map f :=
  (regularVertexIso (k := k) (S := S)).hom.naturality f

variable (N : ModuleCat.{u} (IncidenceQuotientProjectiveResolution.C (k := k) (S := S)))
  (P : ProjectiveResolution
    ((ModuleCat.restrictScalars (quotientHom (k := k) (S := S))).obj N))

/-- Extension acts on an actual projective resolution of the restricted quotient module. -/
def extensionProjectiveResolution_publicHeader : ProjectiveResolution N :=
  extensionProjectiveResolution (k := k) (S := S) N P

/-- The resolution terms are the actual extension-functor images. -/
theorem extensionResolution_term_publicHeader (n : ℕ) :
    (extensionProjectiveResolution (k := k) (S := S) N P).complex.X n =
      (extensionFunctor (k := k) (S := S)).obj (P.complex.X n) :=
  extensionProjectiveResolution_complex_X (k := k) (S := S) N P n

/-- The resolution differentials are the actual extension-functor maps. -/
theorem extensionResolution_differential_publicHeader (i j : ℕ) :
    (extensionProjectiveResolution (k := k) (S := S) N P).complex.d i j =
      (extensionFunctor (k := k) (S := S)).map (P.complex.d i j) :=
  extensionProjectiveResolution_complex_d (k := k) (S := S) N P i j

/-- The augmentation is extension of the original augmentation followed by the quotient counit. -/
theorem extensionResolution_augmentation_publicHeader :
    (extensionProjectiveResolution (k := k) (S := S) N P).π.f 0 =
      (extensionFunctor (k := k) (S := S)).map (P.π.f 0) ≫
        (extensionRestrictionIso (k := k) (S := S)).hom.app N :=
  extensionProjectiveResolution_augmentation (k := k) (S := S) N P

/-- The extended augmentation acts on the actual quotient representative class. -/
theorem extensionResolution_augmentationClass_publicHeader (x : P.complex.X 0) :
    ((extensionProjectiveResolution (k := k) (S := S) N P).π.f 0).hom
        ((relation (k := k) (S := S) (P.complex.X 0)).mkQ x) =
      (P.π.f 0).hom x :=
  extensionProjectiveResolution_augmentation_class (k := k) (S := S) N P x

/-- Extension preserves each supplied zero term of an actual restricted-module resolution. -/
theorem extensionResolution_zeroTerm_publicHeader (n : ℕ) (h : IsZero (P.complex.X n)) :
    IsZero ((extensionProjectiveResolution (k := k) (S := S) N P).complex.X n) :=
  extensionProjectiveResolution_isZero_term (k := k) (S := S) N P n h

/-- Extension preserves any supplied vanishing-above-degree condition on the resolution. -/
theorem extensionResolution_zeroAbove_publicHeader (d : ℕ)
    (h : ∀ n, d < n → IsZero (P.complex.X n)) :
    ∀ n, d < n →
      IsZero ((extensionProjectiveResolution (k := k) (S := S) N P).complex.X n) :=
  extensionProjectiveResolution_isZero_above (k := k) (S := S) N P d h

variable (T : ShortComplex
    (ModuleCat.{u} (IncidenceQuotientProjectiveResolution.R (k := k) (S := S))))

/-- Extension preserves a short exact row with the stated injective assembly map. -/
theorem extensionShortExact_publicHeader (hT : T.ShortExact)
    (hτ : Function.Injective (assembleAction (k := k) (S := S) T.X₃)) :
    (T.map (extensionFunctor (k := k) (S := S))).ShortExact :=
  extension_map_shortExact_of_assemble_injective (k := k) (S := S) T hT hτ

variable (M : ModuleCat.{u} (IncidenceQuotientProjectiveResolution.R (k := k) (S := S)))

/-- The projective-dimension bound is transported with its assembly-injectivity hypothesis. -/
theorem extensionProjectiveDimensionLE_publicHeader (d : ℕ) :
    Function.Injective (assembleAction (k := k) (S := S) M) →
      HasProjectiveDimensionLE M d →
        HasProjectiveDimensionLE ((extensionFunctor (k := k) (S := S)).obj M) d :=
  extension_hasProjectiveDimensionLE_of_assemble_injective (k := k) (S := S) M d

/-- Restricted quotient modules have the existing injective assembly map. -/
theorem restrictedAssembly_injective_publicHeader :
    Function.Injective (assembleAction (k := k) (S := S)
      ((ModuleCat.restrictScalars (quotientHom (k := k) (S := S))).obj N)) :=
  assembleAction_restrict_injective (k := k) (S := S) N

/-- A dimension bound on the restricted module gives the same bound on the quotient module. -/
theorem restrictedProjectiveDimensionLE_publicHeader (d : ℕ)
    (hN : HasProjectiveDimensionLE
      ((ModuleCat.restrictScalars (quotientHom (k := k) (S := S))).obj N) d) :
    HasProjectiveDimensionLE N d :=
  extension_hasProjectiveDimensionLE_restricted (k := k) (S := S) N d hN

/-- The strict projective-dimension bound is transported with assembly injectivity. -/
theorem extensionProjectiveDimensionLT_publicHeader (n : ℕ)
    (hτ : Function.Injective (assembleAction (k := k) (S := S) M))
    (hM : HasProjectiveDimensionLT M n) :
    HasProjectiveDimensionLT ((extensionFunctor (k := k) (S := S)).obj M) n :=
  extension_hasProjectiveDimensionLT_of_assemble_injective (k := k) (S := S) M n hτ hM

/-- The extended projective dimension is bounded by the original one under assembly injectivity. -/
theorem extensionProjectiveDimension_le_publicHeader
    (hτ : Function.Injective (assembleAction (k := k) (S := S) M)) :
    CategoryTheory.projectiveDimension ((extensionFunctor (k := k) (S := S)).obj M) ≤
      CategoryTheory.projectiveDimension M :=
  extension_projectiveDimension_le_of_assemble_injective (k := k) (S := S) M hτ

/-- Quotient projective dimension is bounded by the dimension after restriction. -/
theorem projectiveDimension_le_restriction_publicHeader :
    CategoryTheory.projectiveDimension N ≤
      CategoryTheory.projectiveDimension
        ((ModuleCat.restrictScalars (quotientHom (k := k) (S := S))).obj N) :=
  projectiveDimension_le_restriction (k := k) (S := S) N

/-- The strict matrix idempotent gives a nameable quotient class at every actual strict vertex. -/
def strictVertexIdempotent (v : StrictVertex S) :
    IncidenceVertexTor.DiagonalQuotient (k := k) (S := S) :=
  Ideal.Quotient.mk (IncidenceVertexTor.DiagonalIdeal (k := k) (S := S))
    (delta (k := k) (S := S) v.1 v.1 le_rfl)

/-- Evaluation of the strict matrix idempotent at its own vertex is one. -/
theorem strictVertexIdempotent_evaluation (v : StrictVertex S) :
    vertexQuotientCharacter (k := k) (S := S) v
      (strictVertexIdempotent (k := k) v) = 1 := by
  simp [strictVertexIdempotent]

/-- The public representative law also computes scalar transport for the idempotent class. -/
theorem strictVertexIdempotent_scalar_transport (v : StrictVertex S) (c : k) :
    diagonalQuotientVertexCoinvariantsEquiv (k := k) (S := S) v
      (mk (k := k) (S := S) v (diagonalQuotientModule (k := k) (S := S))
        (c • strictVertexIdempotent (k := k) v)) =
      c • (diagonalQuotientVertexRelation (k := k) (S := S) v).mkQ
        (strictVertexIdempotent (k := k) v) := by
  rw [diagonalQuotientVertexCoinvariantsEquiv_mkQ]
  exact (diagonalQuotientVertexRelation (k := k) (S := S) v).mkQ.map_smul c _

/-- A nonzero scalar multiple of the strict idempotent class stays nonzero in coinvariants. -/
theorem strictVertexIdempotent_coinvariant_nonzero (v : StrictVertex S) (c : k) (hc : c ≠ 0) :
    mk (k := k) (S := S) v (diagonalQuotientModule (k := k) (S := S))
      (c • strictVertexIdempotent (k := k) v) ≠ 0 := by
  intro h
  have h' := congrArg (diagonalQuotientVertexCoinvariantsIso (k := k) (S := S) v).hom h
  rw [diagonalQuotientVertexCoinvariantsIso_hom_mkQ] at h'
  apply hc
  simpa [map_smul, strictVertexIdempotent_evaluation] using h'

/-- The interior strict vertex of the two-element chain. -/
def finTwoInteriorStrictVertex : StrictVertex (Fin 2) :=
  ⟨⟨((0 : Fin 2), (1 : Fin 2)), by decide⟩, by decide⟩

/-- The strict vertex from the old element of `Unit` to its added top element. -/
def singletonTopStrictVertex : StrictVertex Unit :=
  ⟨⟨((), ⊤), le_top⟩, by simp⟩

/-- Over `ℚ`, scalar two transports through the actual interior-vertex equivalence. -/
theorem rationalFinTwo_scalar_transport :
    diagonalQuotientVertexCoinvariantsEquiv (k := ℚ) (S := Fin 2) finTwoInteriorStrictVertex
      (mk (k := ℚ) (S := Fin 2) finTwoInteriorStrictVertex
        (diagonalQuotientModule (k := ℚ) (S := Fin 2))
        ((2 : ℚ) • strictVertexIdempotent (k := ℚ) finTwoInteriorStrictVertex)) =
      (2 : ℚ) • (diagonalQuotientVertexRelation (k := ℚ) (S := Fin 2)
        finTwoInteriorStrictVertex).mkQ
        (strictVertexIdempotent (k := ℚ) finTwoInteriorStrictVertex) :=
  strictVertexIdempotent_scalar_transport finTwoInteriorStrictVertex 2

/-- Over `ZMod 2`, scalar one transports at the old-element/new-top vertex. -/
theorem zmodTwoSingleton_scalar_transport :
    diagonalQuotientVertexCoinvariantsEquiv (k := ZMod 2) (S := Unit) singletonTopStrictVertex
      (mk (k := ZMod 2) (S := Unit) singletonTopStrictVertex
        (diagonalQuotientModule (k := ZMod 2) (S := Unit))
        ((1 : ZMod 2) • strictVertexIdempotent (k := ZMod 2) singletonTopStrictVertex)) =
      (1 : ZMod 2) • (diagonalQuotientVertexRelation (k := ZMod 2) (S := Unit)
        singletonTopStrictVertex).mkQ
        (strictVertexIdempotent (k := ZMod 2) singletonTopStrictVertex) :=
  strictVertexIdempotent_scalar_transport singletonTopStrictVertex 1

/-- The rational interior-vertex coinvariant class of twice the idempotent is nonzero. -/
theorem rationalFinTwo_scalar_class_nonzero :
    mk (k := ℚ) (S := Fin 2) finTwoInteriorStrictVertex
      (diagonalQuotientModule (k := ℚ) (S := Fin 2))
      ((2 : ℚ) • strictVertexIdempotent (k := ℚ) finTwoInteriorStrictVertex) ≠ 0 :=
  strictVertexIdempotent_coinvariant_nonzero finTwoInteriorStrictVertex 2 (by norm_num)

/-- The unit scalar gives a nonzero class over `ZMod 2` at the singleton top vertex. -/
theorem zmodTwoSingleton_scalar_class_nonzero :
    mk (k := ZMod 2) (S := Unit) singletonTopStrictVertex
      (diagonalQuotientModule (k := ZMod 2) (S := Unit))
      ((1 : ZMod 2) • strictVertexIdempotent (k := ZMod 2) singletonTopStrictVertex) ≠ 0 :=
  strictVertexIdempotent_coinvariant_nonzero singletonTopStrictVertex 1 one_ne_zero

/-- Positive first derived Tor vanishes for the rational interior vertex. -/
theorem rationalFinTwo_positiveTor_isZero :
    IsZero (((vertexTensor (k := ℚ) (S := Fin 2) finTwoInteriorStrictVertex).leftDerived 1).obj
      (diagonalQuotientModule (k := ℚ) (S := Fin 2))) :=
  diagonalQuotient_leftDerived_pos_isZero finTwoInteriorStrictVertex 1 (by omega)

/-- Positive second derived Tor vanishes over `ZMod 2` at the singleton top vertex. -/
theorem zmodTwoSingleton_positiveTor_isZero :
    IsZero (((vertexTensor (k := ZMod 2) (S := Unit) singletonTopStrictVertex).leftDerived 2).obj
      (diagonalQuotientModule (k := ZMod 2) (S := Unit))) :=
  diagonalQuotient_leftDerived_pos_isZero singletonTopStrictVertex 2 (by omega)

/-- The rational degree-zero comparison sends the quotient unit to one. -/
theorem rationalFinTwo_degreeZero_unit :
    (diagonalQuotient_leftDerivedZeroIso (k := ℚ) (S := Fin 2) finTwoInteriorStrictVertex).hom
      (((Functor.leftDerivedZeroIsoSelf
        (vertexTensor (k := ℚ) (S := Fin 2) finTwoInteriorStrictVertex)).app
        (diagonalQuotientModule (k := ℚ) (S := Fin 2))).inv.hom
        (mk (k := ℚ) (S := Fin 2) finTwoInteriorStrictVertex
          (diagonalQuotientModule (k := ℚ) (S := Fin 2)) 1)) = (1 : ℚ) :=
  diagonalQuotient_leftDerivedZeroIso_hom_unit finTwoInteriorStrictVertex

/-- The `ZMod 2` degree-zero derived object at the singleton top vertex is nonzero. -/
theorem zmodTwoSingleton_degreeZero_nonzero :
    ¬ IsZero (((vertexTensor (k := ZMod 2) (S := Unit) singletonTopStrictVertex).leftDerived 0).obj
      (diagonalQuotientModule (k := ZMod 2) (S := Unit))) :=
  diagonalQuotient_leftDerivedZero_not_isZero singletonTopStrictVertex

/-- The actual projective resolution has a representative whose extended augmentation is one. -/
theorem extensionAugmentation_has_unit_representative (v : StrictVertex S) :
    ∃ x : (ProjectiveResolution.of
          (RightVertexRestrictedModule (k := k) (S := S) v)).complex.X 0,
      ((extensionProjectiveResolution (k := k) (S := S)
        (IncidenceQuotientSimple.RightVertexModule (k := k) (S := S) v)
        (ProjectiveResolution.of (RightVertexRestrictedModule (k := k) (S := S) v))).π.f 0).hom
          ((IncidenceQuotientBaseChange.relation (k := k) (S := S)
            ((ProjectiveResolution.of
              (RightVertexRestrictedModule (k := k) (S := S) v)).complex.X 0)).mkQ x) =
        (1 : k) := by
  let P := ProjectiveResolution.of (RightVertexRestrictedModule (k := k) (S := S) v)
  obtain ⟨x, hx⟩ := (ModuleCat.epi_iff_surjective (P.π.f 0)).mp inferInstance (1 : k)
  refine ⟨x, ?_⟩
  rw [extensionProjectiveResolution_augmentation_class]
  exact hx

/-- The rank-zero regular right module is zero. -/
theorem finiteFree_zero_isZero : IsZero (finiteFreeModule (k := k) (S := S) 0) :=
  ModuleCat.isZero_iff_subsingleton.mpr inferInstance

/-- The rank-zero vertex image is zero. -/
theorem finiteFree_zero_vertex_isZero :
    IsZero ((IncidenceVertexRepresentation.vertexFunctor (k := k) (S := S)).obj
      (finiteFreeModule (k := k) (S := S) 0)) :=
  Functor.map_isZero _ (finiteFree_zero_isZero (k := k) (S := S))

/-- The actual empty biproduct of regular vertex modules is zero. -/
theorem regularFamily_empty_biproduct_isZero :
    IsZero (⨁ fun i : Fin 0 =>
      (IncidenceVertexRepresentation.vertexFunctor (k := k) (S := S)).obj
        (regularFamily (k := k) (S := S) 0 i)) :=
  IsZero.of_iso (finiteFree_zero_vertex_isZero (k := k) (S := S))
    (finiteFreeVertexBiproductIso (k := k) (S := S) 0)

/-- A rank-two finite-free vertex image is nonzero for every finite lattice and field. -/
theorem finiteFree_two_vertex_nonzero : ¬ IsZero
    ((IncidenceVertexRepresentation.vertexFunctor (k := k) (S := S)).obj
      (finiteFreeModule (k := k) (S := S) 2)) := by
  intro h
  let M := finiteFreeModule (k := k) (S := S) 2
  let V := IncidenceVertexRepresentation.vertexFunctor (k := k) (S := S)
  have hm : (𝟙 M : M ⟶ M) = 0 := by
    apply V.map_injective
    exact h.eq_of_src _ _
  let p : PairPoset S := ⟨(⊤, ⊤), le_rfl⟩
  have hv := congrArg (fun f : M ⟶ M => f.hom (fun _ => 1) 0) hm
  change (1 : IncidenceRegularVertex.RightIncidence (k := k) (S := S)) = 0 at hv
  have hc := congrArg (fun a : IncidenceRegularVertex.RightIncidence (k := k) (S := S) =>
    (MulOpposite.unop a) p p) hv
  apply one_ne_zero (α := k)
  simpa [IncidenceAlgebra.one_apply] using hc

/-- The rank-two biproduct of the actual regular vertex modules is nonzero. -/
theorem regularFamily_two_biproduct_nonzero :
    ¬ IsZero (⨁ fun i : Fin 2 =>
      (IncidenceVertexRepresentation.vertexFunctor (k := k) (S := S)).obj
        (regularFamily (k := k) (S := S) 2 i)) := by
  intro h
  exact finiteFree_two_vertex_nonzero (k := k) (S := S)
    (IsZero.of_iso h (finiteFreeVertexBiproductIso (k := k) (S := S) 2).symm)

/-- The empty finite chain has no strict interval-pair vertex. -/
theorem finZero_has_no_strict_vertex : IsEmpty (StrictVertex (Fin 0)) := by
  constructor
  rintro ⟨⟨⟨a, b⟩, hab⟩, hlt⟩
  cases a with
  | top => exact (not_lt_of_ge le_top) hlt
  | coe a => exact Fin.elim0 a

/-- The regular-family API remains valid at rank zero over the empty finite chain. -/
def finZero_regularFamily_publicType :
    Fin 0 → ModuleCat.{u} (IncidenceRegularVertex.RightIncidence (k := k) (S := Fin 0)) :=
  regularFamily (k := k) (S := Fin 0) 0

/-- The rank-two vertex image remains nonzero even when the underlying lattice is empty. -/
theorem finZero_finiteFree_two_vertex_nonzero :
    ¬ IsZero ((IncidenceVertexRepresentation.vertexFunctor (k := k) (S := Fin 0)).obj
      (finiteFreeModule (k := k) (S := Fin 0) 2)) :=
  finiteFree_two_vertex_nonzero (k := k) (S := Fin 0)

end

end TDA.Persistence.IncidenceVertexTorExamples.PublicInterface
