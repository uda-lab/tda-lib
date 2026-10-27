import TDA.Persistence.IncidenceQuotientColumnAction
import Mathlib.CategoryTheory.Abelian.Projective.Resolution

/-!
# Higher derived extension for the incidence quotient

The fixed diagonal-floor columns detect the actual quotient relations on every module, and their
assembly is injective on projectives. This gives exactness in degrees at least two after applying
the actual quotient-extension functor.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence.IncidenceQuotientDerived

open CategoryTheory
open CategoryTheory.Limits
open TDA.Persistence.FiniteRankProjectiveEndAlgebra
open TDA.Persistence.IncidenceQuotientBaseChange
open TDA.Persistence.IncidenceQuotientColumnAction
open TDA.Persistence.IncidenceQuotientDerivedOne

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
    (DiagonalIdeal (k := k) (S := S)).IsTwoSided :=
  diagonalIdeal_isTwoSided (k := k) (S := S)

abbrev R := RightIncidence (k := k) (S := S)
abbrev C := RightQuotient (k := k) (S := S)

/-- The actual quotient-extension of every projective resolution is exact at each degree at
least two. -/
theorem extensionMappedResolution_exactAt_add_two
    (M : ModuleCat.{u} (R (k := k) (S := S))) (P : ProjectiveResolution M) (m : ℕ) :
    (TDA.Persistence.IncidenceQuotientDerivedOne.extensionMappedResolution
      (k := k) (S := S) P).ExactAt (m + 2) := by
  classical
  let E := TDA.Persistence.IncidenceQuotientBaseChange.extensionFunctor
    (k := k) (S := S)
  let K := P.complex
  let d₁ := K.d (m + 3) (m + 2)
  let d₂ := K.d (m + 2) (m + 1)
  let d₃ := K.d (m + 1) m
  let U := ShortComplex.mk d₁ d₂ (K.d_comp_d (m + 3) (m + 2) (m + 1))
  have hU : U.Exact := P.exact_succ (m + 1)
  let T := ShortComplex.mk d₂ d₃ (K.d_comp_d (m + 2) (m + 1) m)
  have hT : T.Exact := P.exact_succ m
  let GT := T.map (columnAction (k := k) (S := S))
  have hGT : GT.Exact := columnAction_map_exact (k := k) (S := S) T hT
  change (TDA.Persistence.IncidenceQuotientDerivedOne.extensionMappedResolution
    (k := k) (S := S) P).ExactAt (m + 2)
  rw [HomologicalComplex.exactAt_iff' _ (m + 3) (m + 2) (m + 1) (by simp) (by simp)]
  change (U.map E).Exact
  apply (ShortComplex.moduleCat_exact_iff _).2
  intro z hz
  change (E.map d₂).hom z = 0 at hz
  let Q₂ := relation (k := k) (S := S) (K.X (m + 2))
  let Q₁ := relation (k := k) (S := S) (K.X (m + 1))
  let Q₃ := relation (k := k) (S := S) (K.X (m + 3))
  have hEMap : E.map d₂ = extensionMap (k := k) (S := S) d₂ := rfl
  obtain ⟨y, hy⟩ := Q₂.mkQ_surjective z
  have hExtensionCycle :
      (extensionMap (k := k) (S := S) d₂).hom (Q₂.mkQ y) = 0 := by
    rw [← hEMap, hy]
    exact hz
  have hqzero : Q₁.mkQ (d₂.hom y) = 0 := by
    have hh := hExtensionCycle
    rw [extensionMap_mkQ] at hh
    change Q₁.mkQ (d₂.hom y) = 0 at hh
    exact hh
  have hrel : d₂.hom y ∈ Q₁ := (Submodule.Quotient.mk_eq_zero Q₁).mp hqzero
  have hrange : (d₂.hom y) ∈
      (assembleAction (k := k) (S := S) (K.X (m + 1))).range := by
    rw [assembleAction_range_eq_relation (k := k) (S := S) (K.X (m + 1))]
    exact hrel
  obtain ⟨x, hx⟩ := hrange
  have hxCycleG : ((columnAction (k := k) (S := S)).map T.g) x = 0 := by
    have hsum : assembleAction (k := k) (S := S) (K.X m)
        (((columnAction (k := k) (S := S)).map T.g) x) = 0 := by
      calc
        assembleAction (k := k) (S := S) (K.X m)
            (((columnAction (k := k) (S := S)).map T.g) x) =
            d₃.hom (assembleAction (k := k) (S := S) (K.X (m + 1)) x) :=
          assembleAction_natural (k := k) (S := S) T.g x
        _ = d₃.hom (d₂.hom y) := by rw [hx]
        _ = 0 := by
          simpa [T, d₂, d₃] using T.zero_apply y
    letI : Projective (K.X m) := P.projective m
    apply (assembleAction_projective_injective (k := k) (S := S) (K.X m))
    calc
      assembleAction (k := k) (S := S) (K.X m)
          (((columnAction (k := k) (S := S)).map T.g) x) = 0 := hsum
      _ = assembleAction (k := k) (S := S) (K.X m) 0 := by
        exact (assembleAction (k := k) (S := S) (K.X m)).map_zero.symm
  have hxCycle : GT.g x = 0 := by
    change ((columnAction (k := k) (S := S)).map T.g) x = 0
    exact hxCycleG
  have hGFunction := (ShortComplex.ab_exact_iff GT).mp hGT
  obtain ⟨w, hw⟩ := hGFunction x hxCycle
  have hτw : d₂.hom (assembleAction (k := k) (S := S) (K.X (m + 2)) w) =
      assembleAction (k := k) (S := S) (K.X (m + 1)) x := by
    change (columnAction (k := k) (S := S)).map T.f w = x at hw
    calc
      d₂.hom (assembleAction (k := k) (S := S) (K.X (m + 2)) w) =
          assembleAction (k := k) (S := S) (K.X (m + 1))
            ((columnAction (k := k) (S := S)).map T.f w) :=
        (assembleAction_natural (k := k) (S := S) T.f w).symm
      _ = assembleAction (k := k) (S := S) (K.X (m + 1)) x := by rw [hw]
  have hyCycle : d₂.hom (y - assembleAction (k := k) (S := S)
      (K.X (m + 2)) w) = 0 := by
    rw [map_sub, ← hx, hτw]
    simp
  have hUFunction := (ShortComplex.moduleCat_exact_iff U).mp hU
  obtain ⟨v, hv⟩ := hUFunction (y - assembleAction (k := k) (S := S)
    (K.X (m + 2)) w) hyCycle
  refine ⟨Q₃.mkQ v, ?_⟩
  change Q₂.mkQ (d₁.hom v) = z
  change (extensionMap (k := k) (S := S) d₁).hom (Q₃.mkQ v) = z
  rw [extensionMap_mkQ]
  change d₁.hom v = y - assembleAction (k := k) (S := S) (K.X (m + 2)) w at hv
  rw [hv]
  have hτwRel : assembleAction (k := k) (S := S) (K.X (m + 2)) w ∈ Q₂ := by
    have hr : assembleAction (k := k) (S := S) (K.X (m + 2)) w ∈
        (assembleAction (k := k) (S := S) (K.X (m + 2))).range := ⟨w, rfl⟩
    rw [assembleAction_range_eq_relation] at hr
    exact hr
  have hmkW : Q₂.mkQ (assembleAction (k := k) (S := S) (K.X (m + 2)) w) = 0 :=
    (Submodule.Quotient.mk_eq_zero Q₂).2 hτwRel
  rw [map_sub, hmkW, sub_zero, hy]

/-- Exactness of the mapped resolution at any specified degree at least two. -/
theorem extensionMappedResolution_exactAt
    (M : ModuleCat.{u} (R (k := k) (S := S))) (P : ProjectiveResolution M)
    (n : ℕ) (hn : 2 ≤ n) :
    (TDA.Persistence.IncidenceQuotientDerivedOne.extensionMappedResolution
      (k := k) (S := S) P).ExactAt n := by
  have h := extensionMappedResolution_exactAt_add_two (k := k) (S := S) M P (n - 2)
  simpa [Nat.sub_add_cancel hn] using h

/-- The actual higher left-derived quotient extension vanishes on every right-incidence module.
This theorem is restricted to positive degrees at least two. -/
theorem extension_leftDerived_isZero_atLeastTwo
    (M : ModuleCat.{u} (R (k := k) (S := S))) (n : ℕ) (hn : 2 ≤ n) :
    IsZero (((TDA.Persistence.IncidenceQuotientBaseChange.extensionFunctor
      (k := k) (S := S)).leftDerived n).obj M) := by
  let E := TDA.Persistence.IncidenceQuotientBaseChange.extensionFunctor
    (k := k) (S := S)
  let P := ProjectiveResolution.of M
  let D := (E.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex
  have hExact := extensionMappedResolution_exactAt (k := k) (S := S) M P n hn
  have hHomology : IsZero (D.homology n) := by
    rw [← HomologicalComplex.exactAt_iff_isZero_homology]
    exact hExact
  exact IsZero.of_iso hHomology (P.isoLeftDerivedObj E n)

/-- On a restricted quotient module, exactness holds in every positive degree: #715 supplies
degree one and the projective-column argument supplies all degrees at least two. -/
theorem extensionMappedResolution_exactAt_positive_restricted
    (N : ModuleCat.{u} (C (k := k) (S := S)))
    (P : ProjectiveResolution
      ((ModuleCat.restrictScalars (quotientHom (k := k) (S := S))).obj N))
    (n : ℕ) (hn : 0 < n) :
    (TDA.Persistence.IncidenceQuotientDerivedOne.extensionMappedResolution
      (k := k) (S := S) P).ExactAt n := by
  cases n with
  | zero => omega
  | succ n =>
    cases n with
    | zero =>
      simpa using extensionMappedResolution_exactAt_one (k := k) (S := S) N P
    | succ m =>
      simpa using extensionMappedResolution_exactAt_add_two (k := k) (S := S)
        ((ModuleCat.restrictScalars (quotientHom (k := k) (S := S))).obj N) P m

/-- Every positive left-derived quotient extension vanishes on a restricted quotient module. -/
theorem extension_leftDerived_positive_isZero
    (N : ModuleCat.{u} (C (k := k) (S := S))) (n : ℕ) (hn : 0 < n) :
    IsZero (((TDA.Persistence.IncidenceQuotientBaseChange.extensionFunctor
      (k := k) (S := S)).leftDerived n).obj
      ((ModuleCat.restrictScalars (quotientHom (k := k) (S := S))).obj N)) := by
  let E := TDA.Persistence.IncidenceQuotientBaseChange.extensionFunctor
    (k := k) (S := S)
  let M := (ModuleCat.restrictScalars (quotientHom (k := k) (S := S))).obj N
  let P := ProjectiveResolution.of M
  let D := (E.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex
  have hExact := extensionMappedResolution_exactAt_positive_restricted
    (k := k) (S := S) N P n hn
  have hHomology : IsZero (D.homology n) := by
    rw [← HomologicalComplex.exactAt_iff_isZero_homology]
    exact hExact
  exact IsZero.of_iso hHomology (P.isoLeftDerivedObj E n)

/-- Positive derived quotient extension vanishes on every actual strict-vertex module. -/
theorem rightVertexExtension_leftDerived_positive_isZero
    (v : TDA.Persistence.FiniteRankProjectiveEndAlgebra.StrictVertex S)
    (n : ℕ) (hn : 0 < n) :
    IsZero (((TDA.Persistence.IncidenceQuotientBaseChange.extensionFunctor
      (k := k) (S := S)).leftDerived n).obj
      (RightVertexRestrictedModule (k := k) (S := S) v)) :=
  extension_leftDerived_positive_isZero (k := k) (S := S)
    (TDA.Persistence.IncidenceQuotientSimple.RightVertexModule (k := k) (S := S) v) n hn

end

end TDA.Persistence.IncidenceQuotientDerived
