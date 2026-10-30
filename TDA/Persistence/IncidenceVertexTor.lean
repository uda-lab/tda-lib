import TDA.Persistence.IncidenceVertexTensorFunctor
import Mathlib.CategoryTheory.Abelian.Projective.Resolution
import Mathlib.LinearAlgebra.Basis.Basic

/-!
# Left-derived vertex tensor and the diagonal quotient resolution

The actual coinvariant functor is right exact by its character-restriction adjunction.  This file
connects it to Mathlib's left-derived functors using the actual two-term ideal row
`0 → I → A → A/I → 0`.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence.IncidenceVertexTor

open CategoryTheory
open CategoryTheory.Limits
open TDA.Persistence.FiniteRankProjectiveEndAlgebra
open TDA.Persistence.FiniteRankProjectiveDiagonalIdealProjective
open TDA.Persistence.IncidenceVertexTensor
open TDA.Persistence.IncidenceVertexTensorFunctor

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

local instance restrictedScalars
    (M : ModuleCat (FiniteRankProjectiveEndAlgebra.Incidence (k := k) (S := S))) :
    Module k M :=
  restrictedScalarsStructure (k := k) (S := S) M

local instance scalarTower
    (M : ModuleCat (FiniteRankProjectiveEndAlgebra.Incidence (k := k) (S := S))) :
    IsScalarTower k (FiniteRankProjectiveEndAlgebra.Incidence (k := k) (S := S)) M :=
  restrictedScalarsTower (k := k) (S := S) M

abbrev Incidence := FiniteRankProjectiveEndAlgebra.Incidence (k := k) (S := S)
abbrev DiagonalIdeal := FiniteRankProjectiveDiagonalIdealProjective.DiagonalIdeal
  (k := k) (S := S)
abbrev DiagonalQuotient := Incidence (k := k) (S := S) ⧸ DiagonalIdeal (k := k) (S := S)

local instance diagonalIdealTwoSided :
    (DiagonalIdeal (k := k) (S := S)).IsTwoSided :=
  diagonalIdeal_isTwoSided (k := k) (S := S)

/-- The actual diagonal ideal as a left incidence-algebra module. -/
abbrev diagonalIdealModule : ModuleCat (Incidence (k := k) (S := S)) :=
  ModuleCat.of (Incidence (k := k) (S := S)) (DiagonalIdeal (k := k) (S := S))

/-- The regular left module of the actual incidence algebra. -/
abbrev regularModule : ModuleCat (Incidence (k := k) (S := S)) :=
  ModuleCat.of (Incidence (k := k) (S := S)) (Incidence (k := k) (S := S))

/-- The actual quotient as a left incidence-algebra module. -/
abbrev diagonalQuotientModule : ModuleCat (Incidence (k := k) (S := S)) :=
  ModuleCat.of (Incidence (k := k) (S := S)) (DiagonalQuotient (k := k) (S := S))

/-- The zero left module used for all positive resolution degrees after degree one. -/
def zeroModule : ModuleCat (Incidence (k := k) (S := S)) :=
  ModuleCat.of (Incidence (k := k) (S := S)) PUnit

theorem zeroModule_isZero : IsZero (zeroModule (k := k) (S := S)) :=
  ModuleCat.isZero_of_subsingleton (ModuleCat.of (Incidence (k := k) (S := S)) PUnit)

/-- The inclusion of the actual diagonal ideal. -/
def diagonalIdealInclusion : diagonalIdealModule (k := k) (S := S) ⟶
    regularModule (k := k) (S := S) :=
  ModuleCat.ofHom (DiagonalIdeal (k := k) (S := S)).subtype

/-- The actual quotient projection, with its induced left action. -/
def diagonalQuotientProjection : regularModule (k := k) (S := S) ⟶
    diagonalQuotientModule (k := k) (S := S) :=
  ModuleCat.ofHom (DiagonalIdeal (k := k) (S := S)).mkQ

/-- The augmentation is the quotient map on elements of the regular module. -/
@[simp] theorem diagonalQuotientProjection_apply (a : Incidence (k := k) (S := S)) :
    (diagonalQuotientProjection (k := k) (S := S)).hom a =
      (DiagonalIdeal (k := k) (S := S)).mkQ a := rfl

/-- The actual ideal row `I → A → A/I`. -/
def diagonalIdealQuotientRow : ShortComplex (ModuleCat (Incidence (k := k) (S := S))) :=
  ShortComplex.mk (diagonalIdealInclusion (k := k) (S := S))
    (diagonalQuotientProjection (k := k) (S := S)) (by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      change ((DiagonalIdeal (k := k) (S := S)).mkQ.comp
        (DiagonalIdeal (k := k) (S := S)).subtype) x = 0
      exact Function.Exact.apply_apply_eq_zero
        (LinearMap.exact_subtype_mkQ (DiagonalIdeal (k := k) (S := S))) x)

/-- The ideal row is the actual short exact sequence of the diagonal ideal, incidence algebra,
and quotient. -/
theorem diagonalIdealQuotientRow_shortExact :
    (diagonalIdealQuotientRow (k := k) (S := S)).ShortExact := by
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · apply (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).2
    exact LinearMap.exact_subtype_mkQ (DiagonalIdeal (k := k) (S := S))
  · exact (ModuleCat.mono_iff_injective (diagonalIdealInclusion (k := k) (S := S))).2
      (DiagonalIdeal (k := k) (S := S)).injective_subtype
  · exact (ModuleCat.epi_iff_surjective (diagonalQuotientProjection (k := k) (S := S))).2
      (Submodule.mkQ_surjective _)

/-- The actual inclusion and quotient maps form the degree-zero exact row. -/
@[simp] theorem diagonalIdealQuotientRow_f_comp_g :
    (diagonalIdealQuotientRow (k := k) (S := S)).f ≫
      (diagonalIdealQuotientRow (k := k) (S := S)).g = 0 :=
  (diagonalIdealQuotientRow (k := k) (S := S)).zero

/-- The regular left module is free on one generator, hence projective. -/
theorem regularModule_projective : Projective (regularModule (k := k) (S := S)) := by
  exact ModuleCat.projective_of_free
    (Module.Basis.singleton Unit (Incidence (k := k) (S := S)))

/-- The actual diagonal ideal is projective by the proved split-column projectivity result. -/
theorem diagonalIdealModule_projective :
    Projective (diagonalIdealModule (k := k) (S := S)) :=
  diagonalIdeal_projective_object (k := k) (S := S)

/-- The two-term complex with `A` in degree zero, `I` in degree one, and zero terms afterward. -/
abbrev diagonalQuotientResolutionComplex : ChainComplex
    (ModuleCat (Incidence (k := k) (S := S))) ℕ :=
  ChainComplex.of
    (fun n => match n with
      | 0 => regularModule (k := k) (S := S)
      | 1 => diagonalIdealModule (k := k) (S := S)
      | _ => zeroModule (k := k) (S := S))
    (fun n => match n with
      | 0 => diagonalIdealInclusion (k := k) (S := S)
      | _ => 0)
    (by intro n; cases n <;> simp)

@[simp] theorem diagonalQuotientResolutionComplex_term_zero :
    (diagonalQuotientResolutionComplex (k := k) (S := S)).X 0 =
      regularModule (k := k) (S := S) := rfl

@[simp] theorem diagonalQuotientResolutionComplex_term_one :
    (diagonalQuotientResolutionComplex (k := k) (S := S)).X 1 =
      diagonalIdealModule (k := k) (S := S) := rfl

@[simp] theorem diagonalQuotientResolutionComplex_term_two_and_above (n : ℕ) :
    (diagonalQuotientResolutionComplex (k := k) (S := S)).X (n + 2) =
      zeroModule (k := k) (S := S) := rfl

@[simp] theorem diagonalQuotientResolutionComplex_differential_one :
    (diagonalQuotientResolutionComplex (k := k) (S := S)).d 1 0 =
      diagonalIdealInclusion (k := k) (S := S) := by
  change ChainComplex.of.d
    (fun n => match n with
      | 0 => regularModule (k := k) (S := S)
      | 1 => diagonalIdealModule (k := k) (S := S)
      | _ => zeroModule (k := k) (S := S))
    (fun n => match n with
      | 0 => diagonalIdealInclusion (k := k) (S := S)
      | _ => 0) 1 0 = _
  exact (ChainComplex.of_d
    (fun n => match n with
      | 0 => regularModule (k := k) (S := S)
      | 1 => diagonalIdealModule (k := k) (S := S)
      | _ => zeroModule (k := k) (S := S))
    (fun n => match n with
      | 0 => diagonalIdealInclusion (k := k) (S := S)
      | _ => 0) 0)

@[simp] theorem diagonalQuotientResolutionComplex_differential_two_and_above (n : ℕ) :
    (diagonalQuotientResolutionComplex (k := k) (S := S)).d (n + 2) (n + 1) = 0 := by
  cases n <;> rfl

/-- The concrete projective resolution of the actual diagonal quotient. -/
noncomputable def diagonalQuotientProjectiveResolution :
    ProjectiveResolution (diagonalQuotientModule (k := k) (S := S)) where
  complex := diagonalQuotientResolutionComplex (k := k) (S := S)
  projective n := by
    cases n with
    | zero => exact regularModule_projective (k := k) (S := S)
    | succ n =>
      cases n with
      | zero => exact diagonalIdealModule_projective (k := k) (S := S)
      | succ n => exact (zeroModule_isZero (k := k) (S := S)).projective
  π := (ChainComplex.toSingle₀Equiv _ _).symm ⟨
    diagonalQuotientProjection (k := k) (S := S), by
      rw [diagonalQuotientResolutionComplex_differential_one]
      exact (diagonalIdealQuotientRow (k := k) (S := S)).zero⟩
  quasiIso := by
    constructor
    intro n
    cases n with
    | zero =>
      rw [ChainComplex.quasiIsoAt₀_iff,
        ShortComplex.quasiIso_iff_of_zeros' _
          (by
            change ChainComplex.of.d
              (fun n => match n with
                | 0 => regularModule (k := k) (S := S)
                | 1 => diagonalIdealModule (k := k) (S := S)
                | _ => zeroModule (k := k) (S := S))
              (fun n => match n with
                | 0 => diagonalIdealInclusion (k := k) (S := S)
                | _ => 0) 0 0 = 0
            simp [ChainComplex.of.d])
          (by rfl) (by rfl)]
      · dsimp
        refine (ShortComplex.exact_and_epi_g_iff_of_iso ?_).2
          ⟨(diagonalIdealQuotientRow_shortExact (k := k) (S := S)).exact, by
            rw [ModuleCat.epi_iff_surjective]
            exact Submodule.mkQ_surjective _⟩
        exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
          (by
            change 𝟙 (diagonalIdealModule (k := k) (S := S)) ≫
                diagonalIdealInclusion (k := k) (S := S) =
              diagonalIdealInclusion (k := k) (S := S) ≫
                𝟙 (regularModule (k := k) (S := S))
            simp)
          (by
            change 𝟙 (regularModule (k := k) (S := S)) ≫
                diagonalQuotientProjection (k := k) (S := S) =
              ((ChainComplex.toSingle₀Equiv
                (diagonalQuotientResolutionComplex (k := k) (S := S))
                (diagonalQuotientModule (k := k) (S := S))).symm
                ⟨diagonalQuotientProjection (k := k) (S := S), by
                  rw [diagonalQuotientResolutionComplex_differential_one]
                  exact (diagonalIdealQuotientRow (k := k) (S := S)).zero⟩).f 0 ≫
                𝟙 (diagonalQuotientModule (k := k) (S := S))
            rw [ChainComplex.toSingle₀Equiv_symm_apply_f_zero]
            simp)
    | succ n =>
      rw [quasiIsoAt_iff_exactAt']
      · cases n with
        | zero =>
          rw [HomologicalComplex.exactAt_iff' _ 2 1 0 (by simp) (by simp)]
          rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
          change Function.Exact
            (0 : PUnit →ₗ[Incidence (k := k) (S := S)]
              DiagonalIdeal (k := k) (S := S))
            (DiagonalIdeal (k := k) (S := S)).subtype
          exact (LinearMap.exact_zero_iff_injective
            (R := Incidence (k := k) (S := S))
            (M := DiagonalIdeal (k := k) (S := S))
            (N := Incidence (k := k) (S := S)) PUnit
            (DiagonalIdeal (k := k) (S := S)).subtype).2
            (DiagonalIdeal (k := k) (S := S)).injective_subtype
        | succ n =>
          apply HomologicalComplex.ExactAt.of_isZero
          exact zeroModule_isZero (k := k) (S := S)
      · apply ChainComplex.exactAt_succ_single_obj

/-- The chain augmentation at degree zero is exactly the actual quotient projection. -/
@[simp] theorem diagonalQuotientProjectiveResolution_augmentation :
    (diagonalQuotientProjectiveResolution (k := k) (S := S)).π.f 0 =
      diagonalQuotientProjection (k := k) (S := S) := by
  change ((ChainComplex.toSingle₀Equiv
    (diagonalQuotientResolutionComplex (k := k) (S := S))
    (diagonalQuotientModule (k := k) (S := S))).symm
      ⟨diagonalQuotientProjection (k := k) (S := S), by
        rw [diagonalQuotientResolutionComplex_differential_one]
        exact (diagonalIdealQuotientRow (k := k) (S := S)).zero⟩).f 0 = _
  exact ChainComplex.toSingle₀Equiv_symm_apply_f_zero _ _

variable (v : StrictVertex S)

private def diagonalIdealVertexCoinvariantsEquiv :=
  coinvariantsEquiv (k := k) (S := S) v
    (M := diagonalIdealModule (k := k) (S := S))
    (N := DiagonalIdeal (k := k) (S := S))
    ({ toFun := fun x => x
       invFun := fun x => x
       left_inv := fun _ => rfl
       right_inv := fun _ => rfl
       map_add' := fun _ _ => rfl } :
      ↑(diagonalIdealModule (k := k) (S := S)) ≃+ DiagonalIdeal (k := k) (S := S))
    (fun c x => by
      apply Subtype.ext
      change algebraMap k (Incidence (k := k) (S := S)) c * x.val = c • x.val
      exact (Algebra.smul_def c x.val).symm)
    (fun _ _ => rfl)

/-- The actual scalar transport between the bundled left-module coinvariants and the natural
quotient-field action on the diagonal quotient coinvariants. -/
noncomputable def diagonalQuotientVertexCoinvariantsEquiv (v : StrictVertex S) :
    coinvariants (k := k) (S := S) v
        (diagonalQuotientModule (k := k) (S := S)) ≃ₗ[k]
      DiagonalQuotientVertexCoinvariants (k := k) (S := S) v :=
  coinvariantsEquiv (k := k) (S := S) v
    (M := diagonalQuotientModule (k := k) (S := S))
    (N := DiagonalQuotient (k := k) (S := S))
    ({ toFun := fun b => b
       invFun := fun b => b
       left_inv := fun _ => rfl
       right_inv := fun _ => rfl
       map_add' := fun _ _ => rfl } :
      ↑(diagonalQuotientModule (k := k) (S := S)) ≃+ DiagonalQuotient (k := k) (S := S))
    (fun c b => by
      change (Ideal.Quotient.mk (DiagonalIdeal (k := k) (S := S))
          (algebraMap k (Incidence (k := k) (S := S)) c)) * b = c • b
      rw [Ideal.Quotient.mk_algebraMap, Algebra.smul_def])
    (fun _ _ => rfl)

/-- The scalar-transport equivalence preserves the representative `b` of a diagonal quotient
class. -/
@[simp] theorem diagonalQuotientVertexCoinvariantsEquiv_mkQ
    (b : DiagonalQuotient (k := k) (S := S)) :
    diagonalQuotientVertexCoinvariantsEquiv (k := k) (S := S) v
      (mk (k := k) (S := S) v
        (diagonalQuotientModule (k := k) (S := S)) b) =
      (vertexRelation (k := k) (R := Incidence (k := k) (S := S))
        (N := DiagonalQuotient (k := k) (S := S))
        (vertexCharacter (k := k) (S := S) v)).mkQ b := by
  simpa [diagonalQuotientVertexCoinvariantsEquiv, mk] using
    (coinvariantsEquiv_mkQ (k := k) (S := S) (v := v)
      (M := diagonalQuotientModule (k := k) (S := S))
      (N := DiagonalQuotient (k := k) (S := S))
      ({ toFun := fun b => b
         invFun := fun b => b
         left_inv := fun _ => rfl
         right_inv := fun _ => rfl
         map_add' := fun _ _ => rfl } :
        ↑(diagonalQuotientModule (k := k) (S := S)) ≃+ DiagonalQuotient (k := k) (S := S))
      (fun c b => by
        change (Ideal.Quotient.mk (DiagonalIdeal (k := k) (S := S))
            (algebraMap k (Incidence (k := k) (S := S)) c)) * b = c • b
        rw [Ideal.Quotient.mk_algebraMap, Algebra.smul_def])
      (fun _ _ => rfl) b)

/-- The actual projective resolution after applying the character-coinvariant functor. -/
abbrev mappedDiagonalQuotientResolution : ChainComplex (ModuleCat k) ℕ :=
  ((vertexTensor (k := k) (S := S) v).mapHomologicalComplex (ComplexShape.down ℕ)).obj
    (diagonalQuotientProjectiveResolution (k := k) (S := S)).complex

set_option maxHeartbeats 1000000 in
/-- The degree-one term of the mapped resolution is zero by the ideal character-coinvariant
calculation. -/
theorem mappedResolution_term_one_isZero :
    IsZero ((mappedDiagonalQuotientResolution (k := k) (S := S) v).X 1) := by
  change IsZero (coinvariants (k := k) (S := S) v
    (diagonalIdealModule (k := k) (S := S)))
  apply ModuleCat.isZero_iff_subsingleton.mpr
  constructor
  intro x y
  apply (diagonalIdealVertexCoinvariantsEquiv (k := k) (S := S) v).injective
  exact (diagonalIdealVertexCoinvariants_eq_zero (k := k) (S := S) v _).trans
    (diagonalIdealVertexCoinvariants_eq_zero (k := k) (S := S) v _).symm

/-- Every term of the mapped resolution from degree two onward is zero because `F_v` is additive
and hence sends the actual zero module to zero. -/
theorem mappedResolution_term_isZero_of_two_le (n : ℕ) (hn : 2 ≤ n) :
    IsZero ((mappedDiagonalQuotientResolution (k := k) (S := S) v).X n) := by
  cases n with
  | zero => omega
  | succ n =>
    cases n with
    | zero => omega
    | succ n =>
      change IsZero ((vertexTensor (k := k) (S := S) v).obj
        (zeroModule (k := k) (S := S)))
      exact (vertexTensor (k := k) (S := S) v).map_isZero
        (zeroModule_isZero (k := k) (S := S))

/-- The mapped complex is exact at every positive degree since its positive terms are zero. -/
theorem mappedResolution_exactAt_pos (n : ℕ) (hn : 0 < n) :
    (mappedDiagonalQuotientResolution (k := k) (S := S) v).ExactAt n := by
  cases n with
  | zero => omega
  | succ n =>
    apply HomologicalComplex.ExactAt.of_isZero
    cases n with
    | zero => exact mappedResolution_term_one_isZero (k := k) (S := S) v
    | succ n =>
      apply mappedResolution_term_isZero_of_two_le (k := k) (S := S) v (n + 2)
      omega

/-- Positive homology of the actual mapped projective resolution vanishes. -/
theorem mappedResolution_homology_pos_isZero (n : ℕ) (hn : 0 < n) :
    IsZero ((HomologicalComplex.homologyFunctor (ModuleCat k) (ComplexShape.down ℕ) n).obj
      (mappedDiagonalQuotientResolution (k := k) (S := S) v)) := by
  change IsZero ((mappedDiagonalQuotientResolution (k := k) (S := S) v).homology n)
  rw [← HomologicalComplex.exactAt_iff_isZero_homology]
  exact mappedResolution_exactAt_pos (k := k) (S := S) v n hn

/-- Every positive left-derived vertex tensor of the actual diagonal quotient is zero, including
degree one. -/
theorem diagonalQuotient_leftDerived_pos_isZero (n : ℕ) (hn : 0 < n) :
    IsZero (((vertexTensor (k := k) (S := S) v).leftDerived n).obj
      (diagonalQuotientModule (k := k) (S := S))) := by
  refine IsZero.of_iso ?_
    ((diagonalQuotientProjectiveResolution (k := k) (S := S)).isoLeftDerivedObj
      (vertexTensor (k := k) (S := S) v) n)
  exact mappedResolution_homology_pos_isZero (k := k) (S := S) v n hn

/-- The actual quotient tensor is canonically isomorphic to the ground-field module. -/
noncomputable def diagonalQuotientVertexCoinvariantsIso :
    (vertexTensor (k := k) (S := S) v).obj
      (diagonalQuotientModule (k := k) (S := S)) ≅ ModuleCat.of k k :=
  ((diagonalQuotientVertexCoinvariantsEquiv (k := k) (S := S) v).trans
    (diagonalQuotientVertexTensorEquiv (k := k) (S := S) v)).toModuleIso

/-- The quotient coinvariants isomorphism evaluates every representative by the actual vertex
character. -/
@[simp] theorem diagonalQuotientVertexCoinvariantsIso_hom_mkQ
    (b : DiagonalQuotient (k := k) (S := S)) :
    (diagonalQuotientVertexCoinvariantsIso (k := k) (S := S) v).hom
      (mk (k := k) (S := S) v
        (diagonalQuotientModule (k := k) (S := S)) b) =
      vertexQuotientCharacter (k := k) (S := S) v b := by
  change diagonalQuotientVertexTensorEquiv (k := k) (S := S) v
    (diagonalQuotientVertexCoinvariantsEquiv (k := k) (S := S) v
      (mk (k := k) (S := S) v (diagonalQuotientModule (k := k) (S := S)) b)) = _
  rw [diagonalQuotientVertexCoinvariantsEquiv_mkQ]
  exact diagonalQuotientVertexTensorEquiv_mk (k := k) (S := S) v b

/-- The canonical degree-zero derived comparison followed by the quotient coinvariant
equivalence identifies degree zero with `k`. -/
noncomputable def diagonalQuotient_leftDerivedZeroIso :
    (((vertexTensor (k := k) (S := S) v).leftDerived 0).obj
      (diagonalQuotientModule (k := k) (S := S))) ≅ ModuleCat.of k k :=
  (Functor.leftDerivedZeroIsoSelf (vertexTensor (k := k) (S := S) v)).app
      (diagonalQuotientModule (k := k) (S := S)) ≪≫
    diagonalQuotientVertexCoinvariantsIso (k := k) (S := S) v

/-- The degree-zero derived comparison sends the actual coinvariant class of the quotient unit to
`1 : k`. -/
@[simp] theorem diagonalQuotient_leftDerivedZeroIso_hom_unit :
    (diagonalQuotient_leftDerivedZeroIso (k := k) (S := S) v).hom
      (((Functor.leftDerivedZeroIsoSelf (vertexTensor (k := k) (S := S) v)).app
        (diagonalQuotientModule (k := k) (S := S))).inv.hom
        (mk (k := k) (S := S) v
          (diagonalQuotientModule (k := k) (S := S))
          (1 : DiagonalQuotient (k := k) (S := S)))) =
      (1 : k) := by
  let η := (Functor.leftDerivedZeroIsoSelf (vertexTensor (k := k) (S := S) v)).app
    (diagonalQuotientModule (k := k) (S := S))
  change (diagonalQuotientVertexCoinvariantsIso (k := k) (S := S) v).hom
    (η.hom (η.inv.hom
      (mk (k := k) (S := S) v (diagonalQuotientModule (k := k) (S := S))
        (1 : DiagonalQuotient (k := k) (S := S))))) = (1 : k)
  rw [Iso.inv_hom_id_apply]
  simpa using diagonalQuotientVertexCoinvariantsIso_hom_mkQ (k := k) (S := S) v 1

/-- The degree-zero left-derived quotient tensor is not zero. -/
theorem diagonalQuotient_leftDerivedZero_not_isZero :
    ¬ IsZero (((vertexTensor (k := k) (S := S) v).leftDerived 0).obj
      (diagonalQuotientModule (k := k) (S := S))) := by
  intro h
  have hk : IsZero (ModuleCat.of k k) := IsZero.of_iso h
    (diagonalQuotient_leftDerivedZeroIso (k := k) (S := S) v).symm
  have hs : Subsingleton k := ModuleCat.isZero_iff_subsingleton.mp hk
  exact one_ne_zero (hs.elim 1 0)

end

end TDA.Persistence.IncidenceVertexTor
