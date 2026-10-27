import TDA.Persistence.IncidenceQuotientDerived
import Mathlib.CategoryTheory.Abelian.Projective.Dimension

/-!
# Quotient projective resolutions and dimension comparison

Every projective resolution of a restricted quotient module extends to an augmented projective
resolution of the quotient module. The actual quotient extension also does not increase projective
dimension on restricted modules.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence.IncidenceQuotientProjectiveResolution

open CategoryTheory
open CategoryTheory.Limits
open TDA.Persistence.FiniteRankProjectiveEndAlgebra
open TDA.Persistence.IncidenceQuotientBaseChange
open TDA.Persistence.IncidenceQuotientDerivedOne
open TDA.Persistence.IncidenceQuotientColumnAction
open TDA.Persistence.IncidenceQuotientDerived

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

private abbrev E := extensionFunctor (k := k) (S := S)
private abbrev Res := ModuleCat.restrictScalars (quotientHom (k := k) (S := S))

private abbrev quotientCounitAt (N : ModuleCat.{u} (C (k := k) (S := S))) :
    (E (k := k) (S := S)).obj ((Res (k := k) (S := S)).obj N) ≅ N :=
  (extensionRestrictionIso (k := k) (S := S)).app N

/-- Extend an actual projective resolution of a restricted quotient module and augment it by the
canonical quotient counit. -/
noncomputable def extensionProjectiveResolution
    (N : ModuleCat.{u} (C (k := k) (S := S)))
    (P : ProjectiveResolution ((Res (k := k) (S := S)).obj N)) :
    ProjectiveResolution N where
  complex := extensionMappedResolution (k := k) (S := S) P
  projective n :=
    Functor.projective_obj_of_projective (E (k := k) (S := S)) (P.projective n)
  π := by
    let p₀ : P.complex.X 0 ⟶ (Res (k := k) (S := S)).obj N := P.π.f 0
    refine (ChainComplex.toSingle₀Equiv _ _).symm ⟨
    (E (k := k) (S := S)).map p₀ ≫
      (quotientCounitAt (k := k) (S := S) N).hom,
    by
      change (E (k := k) (S := S)).map (P.complex.d 1 0) ≫
          ((E (k := k) (S := S)).map p₀ ≫
            (extensionRestrictionIso (k := k) (S := S)).hom.app N) = 0
      have hp₀ : P.complex.d 1 0 ≫ p₀ = 0 := P.complex_d_comp_π_f_zero
      rw [← Category.assoc, ← Functor.map_comp, hp₀]
      simp⟩
  quasiIso := ⟨fun n => by
    cases n with
    | zero =>
      rw [ChainComplex.quasiIsoAt₀_iff,
        ShortComplex.quasiIso_iff_of_zeros' _
          (by simp [extensionMappedResolution] <;> rfl)
          (by simp <;> rfl) (by simp <;> rfl)]
      let p₀ : P.complex.X 0 ⟶ (Res (k := k) (S := S)).obj N := P.π.f 0
      let T := ShortComplex.mk (P.complex.d 1 0) p₀ (by
        change P.complex.d 1 0 ≫ P.π.f 0 = 0
        exact P.complex_d_comp_π_f_zero)
      have hTE : (T.map (E (k := k) (S := S))).Exact ∧
          Epi ((T.map (E (k := k) (S := S))).g) := by
        rw [ShortComplex.exact_and_epi_g_iff_g_is_cokernel]
        exact ⟨CokernelCofork.mapIsColimit _ P.isColimitCokernelCofork
          (E (k := k) (S := S))⟩
      let TE := T.map (E (k := k) (S := S))
      let ε : TE.X₃ ≅ N := by
        change (E (k := k) (S := S)).obj ((Res (k := k) (S := S)).obj N) ≅ N
        exact quotientCounitAt (k := k) (S := S) N
      let Tε := ShortComplex.mk TE.f (TE.g ≫ ε.hom) (by
          calc
            TE.f ≫ (TE.g ≫ ε.hom) = (TE.f ≫ TE.g) ≫ ε.hom :=
                    (Category.assoc _ _ _).symm
            _ = 0 := by rw [TE.zero, zero_comp])
      have hIso : TE ≅ Tε :=
        ShortComplex.isoMk (Iso.refl _) (Iso.refl _) ε
          (by rfl) (by rfl)
      change Tε.Exact ∧ Epi Tε.g
      exact (ShortComplex.exact_and_epi_g_iff_of_iso hIso).1 hTE
    | succ n =>
      rw [quasiIsoAt_iff_exactAt']
      · exact extensionMappedResolution_exactAt_positive_restricted
          (k := k) (S := S) N P (n + 1) (by omega)
      · exact ChainComplex.exactAt_succ_single_obj _ _⟩

@[simp] theorem extensionProjectiveResolution_complex_X
    (N : ModuleCat.{u} (C (k := k) (S := S)))
    (P : ProjectiveResolution ((Res (k := k) (S := S)).obj N)) (n : ℕ) :
    (extensionProjectiveResolution (k := k) (S := S) N P).complex.X n =
      (E (k := k) (S := S)).obj (P.complex.X n) := rfl

@[simp] theorem extensionProjectiveResolution_complex_d
    (N : ModuleCat.{u} (C (k := k) (S := S)))
    (P : ProjectiveResolution ((Res (k := k) (S := S)).obj N)) (i j : ℕ) :
    (extensionProjectiveResolution (k := k) (S := S) N P).complex.d i j =
      (E (k := k) (S := S)).map (P.complex.d i j) := rfl

@[simp] theorem extensionProjectiveResolution_augmentation
    (N : ModuleCat.{u} (C (k := k) (S := S)))
    (P : ProjectiveResolution ((Res (k := k) (S := S)).obj N)) :
    (extensionProjectiveResolution (k := k) (S := S) N P).π.f 0 =
      (E (k := k) (S := S)).map (P.π.f 0) ≫
        (extensionRestrictionIso (k := k) (S := S)).hom.app N := by
  exact ChainComplex.toSingle₀Equiv_symm_apply_f_zero _ _

@[simp] theorem extensionProjectiveResolution_augmentation_class
    (N : ModuleCat.{u} (C (k := k) (S := S)))
    (P : ProjectiveResolution ((Res (k := k) (S := S)).obj N)) (x : P.complex.X 0) :
    ((extensionProjectiveResolution (k := k) (S := S) N P).π.f 0).hom
        ((relation (k := k) (S := S) (P.complex.X 0)).mkQ x) =
      (P.π.f 0).hom x := by
  let p₀ : P.complex.X 0 ⟶ (Res (k := k) (S := S)).obj N := P.π.f 0
  rw [extensionProjectiveResolution_augmentation]
  change (quotientCounitAt (k := k) (S := S) N).hom
      ((extensionMap (k := k) (S := S) p₀).hom
        ((relation (k := k) (S := S) (P.complex.X 0)).mkQ x)) = _
  rw [extensionMap_mkQ]
  exact extensionRestrictionIso_hom_mkQ (k := k) (S := S) N (p₀.hom x)

/-- Extension transports a zero term of an actual restricted-module resolution. -/
theorem extensionProjectiveResolution_isZero_term
    (N : ModuleCat.{u} (C (k := k) (S := S)))
    (P : ProjectiveResolution ((Res (k := k) (S := S)).obj N)) (n : ℕ)
    (h : IsZero (P.complex.X n)) :
    IsZero ((extensionProjectiveResolution (k := k) (S := S) N P).complex.X n) := by
  change IsZero ((E (k := k) (S := S)).obj (P.complex.X n))
  exact Functor.map_isZero (E (k := k) (S := S)) h

/-- Extension transports any supplied vanishing-above-degree condition on an actual resolution. -/
theorem extensionProjectiveResolution_isZero_above
    (N : ModuleCat.{u} (C (k := k) (S := S)))
    (P : ProjectiveResolution ((Res (k := k) (S := S)).obj N)) (d : ℕ)
    (h : ∀ n, d < n → IsZero (P.complex.X n)) :
    ∀ n, d < n →
      IsZero ((extensionProjectiveResolution (k := k) (S := S) N P).complex.X n) := by
  intro n hn
  exact extensionProjectiveResolution_isZero_term (k := k) (S := S) N P n (h n hn)

/-- Extension carries a short exact row to a short exact row whenever the assembly map on its
right endpoint is injective. -/
theorem extension_map_shortExact_of_assemble_injective
    (T : ShortComplex (ModuleCat.{u} (R (k := k) (S := S)))) (hT : T.ShortExact)
    (hτ : Function.Injective (assembleAction (k := k) (S := S) T.X₃)) :
    (T.map (E (k := k) (S := S))).ShortExact := by
  classical
  let E := E (k := k) (S := S)
  let QX := relation (k := k) (S := S) T.X₁
  let QY := relation (k := k) (S := S) T.X₂
  have hf_inj : Function.Injective T.f.hom := hT.moduleCat_injective_f
  have hmono : Mono ((T.map E).f) := (ModuleCat.mono_iff_injective _).mpr (by
    intro x y hxy
    obtain ⟨x₀, rfl⟩ := QX.mkQ_surjective x
    obtain ⟨y₀, rfl⟩ := QX.mkQ_surjective y
    have hquot : QY.mkQ (T.f.hom x₀) = QY.mkQ (T.f.hom y₀) := by
      change (extensionMap (k := k) (S := S) T.f).hom (QX.mkQ x₀) =
        (extensionMap (k := k) (S := S) T.f).hom (QX.mkQ y₀) at hxy
      rw [extensionMap_mkQ] at hxy
      exact hxy
    have hdiff : T.f.hom (x₀ - y₀) ∈ QY := by
      have h := (Submodule.Quotient.eq QY).1 hquot
      simpa only [map_sub] using h
    have hrange : T.f.hom (x₀ - y₀) ∈
        (assembleAction (k := k) (S := S) T.X₂).range := by
      rw [assembleAction_range_eq_relation]
      exact hdiff
    obtain ⟨w, hw⟩ := hrange
    have hgf : T.g.hom (T.f.hom (x₀ - y₀)) = 0 := by
      have h := congrArg (fun g : T.X₁ ⟶ T.X₃ => g.hom (x₀ - y₀)) T.zero
      simpa using h
    have hnatural := assembleAction_natural (k := k) (S := S) T.g w
    rw [hw, hgf] at hnatural
    let v : ColumnObject (k := k) (S := S) T.X₃ := fun q =>
      ⟨T.g.hom (w q), by
        change columnProjector (k := k) (S := S) q • T.g.hom (w q) = T.g.hom (w q)
        rw [← T.g.hom.map_smul]
        exact congrArg T.g.hom (w q).property⟩
    have hassemble : assembleAction (k := k) (S := S) T.X₃ v = 0 := by
      change assembleAction (k := k) (S := S) T.X₃ v = 0 at hnatural
      exact hnatural
    have hvzero : v = 0 := by
      apply hτ
      rw [map_zero]
      exact hassemble
    have hcolzero :
        (((columnAction (k := k) (S := S)).map T.g).hom w :
          ColumnObject (k := k) (S := S) T.X₃) = 0 := by
      change (((columnAction (k := k) (S := S)).map T.g).hom w :
        ColumnObject (k := k) (S := S) T.X₃) = 0
      funext q
      apply Subtype.ext
      have hq := congrArg (fun z : ColumnObject (k := k) (S := S) T.X₃ =>
        (z q : T.X₃)) hvzero
      exact hq
    have hGexact := columnAction_map_exact (k := k) (S := S) T hT.exact
    obtain ⟨u, hu⟩ := (ShortComplex.ab_exact_iff _).mp hGexact w hcolzero
    let u' : ColumnObject (k := k) (S := S) T.X₁ := u
    have hu' : (columnAction (k := k) (S := S)).map T.f u' = w := by
      change (columnAction (k := k) (S := S)).map T.f u = w at hu
      exact hu
    have hnatural' := assembleAction_natural (k := k) (S := S) T.f u'
    change assembleAction (k := k) (S := S) T.X₂
      ((columnAction (k := k) (S := S)).map T.f u) = _ at hnatural'
    rw [hu'] at hnatural'
    have hfd : T.f.hom (x₀ - y₀) =
        T.f.hom (assembleAction (k := k) (S := S) T.X₁ u) := hw.symm.trans hnatural'
    have hd : x₀ - y₀ = assembleAction (k := k) (S := S) T.X₁ u :=
      hf_inj hfd
    have hrel : x₀ - y₀ ∈ QX := by
      have hrange : x₀ - y₀ ∈
          (relation (k := k) (S := S) T.X₁).toAddSubgroup := by
        rw [← assembleAction_range_eq_relation]
        exact ⟨u, hd.symm⟩
      exact hrange
    exact (Submodule.Quotient.eq QX).2 hrel)
  have hright : (T.map E).Exact ∧ Epi ((T.map E).g) :=
    (T.map E).exact_and_epi_g_iff_g_is_cokernel |>.2
      ⟨CokernelCofork.mapIsColimit _ hT.gIsCokernel E⟩
  exact { exact := hright.1, mono_f := hmono, epi_g := hright.2 }

/-- Assembly is injective on a kernel in a short exact row with projective middle term. -/
theorem assembleAction_injective_of_shortExact_projective_middle
    (T : ShortComplex (ModuleCat.{u} (R (k := k) (S := S)))) (hT : T.ShortExact)
    [Projective T.X₂] :
    Function.Injective (assembleAction (k := k) (S := S) T.X₁) := by
  have hG := columnAction_map_shortExact (k := k) (S := S) T hT
  have hGmono : Function.Injective ((columnAction (k := k) (S := S)).map T.f).hom :=
    (AddCommGrpCat.mono_iff_injective _).mp hG.mono_f
  have hτP := assembleAction_projective_injective (k := k) (S := S) T.X₂
  intro x y hxy
  have hτmap :
      assembleAction (k := k) (S := S) T.X₂
          (((columnAction (k := k) (S := S)).map T.f).hom x) =
        assembleAction (k := k) (S := S) T.X₂
          (((columnAction (k := k) (S := S)).map T.f).hom y) := by
    calc
      _ = T.f.hom (assembleAction (k := k) (S := S) T.X₁ x) :=
        assembleAction_natural (k := k) (S := S) T.f x
      _ = T.f.hom (assembleAction (k := k) (S := S) T.X₁ y) := by rw [hxy]
      _ = _ := (assembleAction_natural (k := k) (S := S) T.f y).symm
  exact hGmono (hτP hτmap)

/-- A finite projective-dimension bound passes through extension whenever the source assembly map
is injective. -/
theorem extension_hasProjectiveDimensionLE_of_assemble_injective
    (M : ModuleCat.{u} (R (k := k) (S := S))) (d : ℕ) :
    Function.Injective (assembleAction (k := k) (S := S) M) →
      HasProjectiveDimensionLE M d →
        HasProjectiveDimensionLE ((E (k := k) (S := S)).obj M) d := by
  induction d generalizing M with
  | zero =>
      intro hτ hM
      have hP : Projective M := (projective_iff_hasProjectiveDimensionLE_zero M).2 hM
      exact (projective_iff_hasProjectiveDimensionLE_zero ((E (k := k) (S := S)).obj M)).1
        (Functor.projective_obj_of_projective (E (k := k) (S := S)) hP)
  | succ d ih =>
      intro hτ hM
      let P := Projective.over M
      let π := Projective.π M
      let T := ShortComplex.mk (kernel.ι π) π (by simp)
      have hT : T.ShortExact := {
        exact := ShortComplex.exact_kernel π
        mono_f := inferInstance
        epi_g := Projective.π_epi M
      }
      have hKτ := assembleAction_injective_of_shortExact_projective_middle
        (k := k) (S := S) T hT
      have hK : HasProjectiveDimensionLE T.X₁ d :=
        (hT.hasProjectiveDimensionLT_X₃_iff d (by infer_instance)).mp hM
      have hEK := ih T.X₁ hKτ hK
      have hET := extension_map_shortExact_of_assemble_injective
        (k := k) (S := S) T hT hτ
      have hEP : Projective ((E (k := k) (S := S)).obj T.X₂) :=
        Functor.projective_obj_of_projective (E (k := k) (S := S)) (by infer_instance)
      exact (hET.hasProjectiveDimensionLT_X₃_iff d hEP).mpr hEK

/-- Restricted quotient modules have injective assembly, since their fixed-column object is zero. -/
theorem assembleAction_restrict_injective
    (N : ModuleCat.{u} (C (k := k) (S := S))) :
    Function.Injective
      (assembleAction (k := k) (S := S) ((Res (k := k) (S := S)).obj N)) := by
  have hzero := columnAction_restrict_isZero (k := k) (S := S) N
  haveI : Subsingleton (ColumnObject (k := k) (S := S)
      ((Res (k := k) (S := S)).obj N)) := by
    change Subsingleton ((columnAction (k := k) (S := S)).obj
      ((Res (k := k) (S := S)).obj N))
    exact AddCommGrpCat.subsingleton_of_isZero hzero
  intro x y hxy
  exact Subsingleton.elim _ _

/-- Quotient extension does not increase finite projective-dimension bounds on restricted modules. -/
theorem extension_hasProjectiveDimensionLE_restricted
    (N : ModuleCat.{u} (C (k := k) (S := S))) (d : ℕ)
    (hN : HasProjectiveDimensionLE ((Res (k := k) (S := S)).obj N) d) :
    HasProjectiveDimensionLE N d := by
  have hE := extension_hasProjectiveDimensionLE_of_assemble_injective
    (k := k) (S := S) ((Res (k := k) (S := S)).obj N) d
    (assembleAction_restrict_injective (k := k) (S := S) N) hN
  letI : HasProjectiveDimensionLT
      ((E (k := k) (S := S)).obj ((Res (k := k) (S := S)).obj N)) (d + 1) := hE
  exact hasProjectiveDimensionLT_of_iso (quotientCounitAt (k := k) (S := S) N) (d + 1)

/-- Strict projective-dimension bounds pass through extension for any module with injective
assembly. -/
theorem extension_hasProjectiveDimensionLT_of_assemble_injective
    (M : ModuleCat.{u} (R (k := k) (S := S))) (n : ℕ)
    (hτ : Function.Injective (assembleAction (k := k) (S := S) M))
    (hM : HasProjectiveDimensionLT M n) :
    HasProjectiveDimensionLT ((E (k := k) (S := S)).obj M) n := by
  cases n with
  | zero =>
      have hzero : IsZero M :=
        (hasProjectiveDimensionLT_zero_iff_isZero (X := M)).mp hM
      exact (hasProjectiveDimensionLT_zero_iff_isZero
          (X := (E (k := k) (S := S)).obj M)).mpr
        (Functor.map_isZero (E (k := k) (S := S)) hzero)
  | succ n =>
      exact extension_hasProjectiveDimensionLE_of_assemble_injective
        (k := k) (S := S) M n hτ hM

/-- Quotient extension lowers projective dimension in the extended naturals for any module with
injective assembly. -/
theorem extension_projectiveDimension_le_of_assemble_injective
    (M : ModuleCat.{u} (R (k := k) (S := S)))
    (hτ : Function.Injective (assembleAction (k := k) (S := S) M)) :
    CategoryTheory.projectiveDimension ((E (k := k) (S := S)).obj M) ≤
      CategoryTheory.projectiveDimension M := by
  unfold CategoryTheory.projectiveDimension
  apply sInf_le_sInf_of_subset_insert_top
  intro n hn
  simp only [Set.mem_ofPred_eq, not_top_lt, IsEmpty.forall_iff, implies_true,
    Set.insert_eq_of_mem] at hn ⊢
  intro i hi
  exact extension_hasProjectiveDimensionLT_of_assemble_injective
    (k := k) (S := S) M i hτ (hn i hi)

/-- For an actual quotient module, extension never increases projective dimension, including the
zero-object and infinite-dimension cases. -/
theorem projectiveDimension_le_restriction
    (N : ModuleCat.{u} (C (k := k) (S := S))) :
    CategoryTheory.projectiveDimension N ≤
      CategoryTheory.projectiveDimension ((Res (k := k) (S := S)).obj N) := by
  calc
    CategoryTheory.projectiveDimension N =
        CategoryTheory.projectiveDimension
          ((E (k := k) (S := S)).obj ((Res (k := k) (S := S)).obj N)) :=
      (projectiveDimension_eq_of_iso (quotientCounitAt (k := k) (S := S) N)).symm
    _ ≤ CategoryTheory.projectiveDimension ((Res (k := k) (S := S)).obj N) :=
      extension_projectiveDimension_le_of_assemble_injective (k := k) (S := S)
        _ (assembleAction_restrict_injective (k := k) (S := S) N)

end

end TDA.Persistence.IncidenceQuotientProjectiveResolution

