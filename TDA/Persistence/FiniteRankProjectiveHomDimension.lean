import TDA.Persistence.FiniteRankProjectiveHomCover
import TDA.Persistence.FiniteRankProjectiveResolutionUniqueness
import Mathlib.CategoryTheory.Abelian.Projective.Dimension

/-!
# Projective dimension detected by minimal resolution terms

For a finite lattice, the hook-generator Hom functor sends each row of a
certified minimal rank-projective resolution to a short exact sequence with
projective middle term and right-minimal quotient. Ext dimension shifting
then identifies ordinary projective-dimension bounds with vanishing above
the corresponding degree. The terms are extended by zero, so terminal zero
padding does not affect the comparison.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence.FiniteRankProjectiveHomDimension

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject
open FiniteRankProjectiveHomExact FiniteRankProjectiveHomCover

noncomputable section

private theorem source_zero_of_rightMinimal
    {C : Type*} [Category* C] [Abelian C] {A B : C} (g : A ⟶ B)
    (hmin : ∀ t : End A, t ≫ g = g → IsIso t) (hB : IsZero B) : IsZero A := by
  have h : IsIso (0 : End A) := hmin 0 (by simp [hB.eq_zero_of_tgt g])
  have := h
  exact IsZero.of_mono_eq_zero (0 : End A) rfl

private theorem row_projective_iff_kernel_zero
    {C : Type*} [Category* C] [Abelian C] {Q : ShortComplex C}
    (hQ : Q.ShortExact) (hP : Projective Q.X₂)
    (hmin : ∀ t : End Q.X₂, t ≫ Q.g = Q.g → IsIso t) :
    HasProjectiveDimensionLT Q.X₃ 1 ↔ IsZero Q.X₁ := by
  have := hQ.mono_f
  have := hQ.epi_g
  have := hP
  constructor
  · intro h
    have := h
    let s := Projective.factorThru (𝟙 Q.X₃) Q.g
    have hs : s ≫ Q.g = 𝟙 Q.X₃ := Projective.factorThru_comp _ _
    have ht : IsIso (Q.g ≫ s) := hmin _ (by simp [Category.assoc, hs])
    have := ht
    have : Mono Q.g := mono_of_mono Q.g s
    exact IsZero.of_mono_eq_zero Q.f ((cancel_mono Q.g).mp (by simp [Q.zero]))
  · intro h
    exact hQ.hasProjectiveDimensionLT_X₃ 0 h.hasProjectiveDimensionLT_zero inferInstance

private theorem finite_rows_dimension_iff
    {C : Type*} [Category* C] [Abelian C] (n : ℕ)
    (K : Fin (n + 1) → C) (P : Fin n → C)
    (f : ∀ i, K i.succ ⟶ P i) (g : ∀ i, P i ⟶ K i.castSucc)
    (w : ∀ i, f i ≫ g i = 0)
    (hex : ∀ i, (ShortComplex.mk (f i) (g i) (w i)).ShortExact)
    (hproj : ∀ i, Projective (P i))
    (hmin : ∀ i, ∀ t : End (P i), t ≫ g i = g i → IsIso t)
    (hlast : IsZero (K (Fin.last n))) (d : ℕ) :
    HasProjectiveDimensionLT (K 0) d ↔ ∀ j, d ≤ j.val → IsZero (P j) := by
  induction n generalizing d with
  | zero =>
    have hzero : IsZero (K 0) := hlast
    constructor
    · intro _ j; exact Fin.elim0 j
    · intro _
      have := hzero.hasProjectiveDimensionLT_zero
      exact hasProjectiveDimensionLT_of_ge (K 0) 0 d (Nat.zero_le _)
  | succ n ih =>
    have tail := ih (fun i => K i.succ) (fun i => P i.succ)
      (fun i => f i.succ) (fun i => g i.succ) (fun i => w i.succ)
      (fun i => hex i.succ) (fun i => hproj i.succ) (fun i => hmin i.succ) hlast
    have hrow := hex 0
    have : Mono (f 0) := hrow.mono_f
    have : Epi (g 0) := hrow.epi_g
    cases d with
    | zero =>
      rw [hasProjectiveDimensionLT_zero_iff_isZero]
      constructor
      · intro h j _
        have hP : IsZero (P 0) := source_zero_of_rightMinimal (g 0) (hmin 0) h
        have hK : IsZero (K (Fin.succ 0)) := IsZero.of_mono (f 0) hP
        have htail := (tail 0).mp hK.hasProjectiveDimensionLT_zero
        refine Fin.cases hP (fun i => htail i (Nat.zero_le _)) j
      · intro h
        have hz := IsZero.of_epi (g 0) (h 0 (Nat.zero_le _))
        simpa only [Fin.castSucc_zero] using hz
    | succ d =>
      cases d with
      | zero =>
        have h := row_projective_iff_kernel_zero hrow (hproj 0) (hmin 0)
        dsimp only [ShortComplex.mk] at h
        simp only [Fin.castSucc_zero] at h
        rw [h, ← hasProjectiveDimensionLT_zero_iff_isZero, tail 0]
        simp only [Fin.forall_fin_succ, Fin.val_zero, Fin.val_succ]
        simp
      | succ d =>
        have h := hrow.hasProjectiveDimensionLT_X₃_iff d (hproj 0)
        dsimp only [ShortComplex.mk] at h
        simp only [Fin.castSucc_zero] at h
        rw [h, tail (d + 1)]
        simp only [Fin.forall_fin_succ, Fin.val_zero, Fin.val_succ]
        simp

variable {k : Type u} [Field k] {S : Type} [Lattice S] [Finite S]

private abbrev F := homFunctor (k := k) (S := S)

private instance : (F (k := k) (S := S)).PreservesZeroMorphisms where
  map_zero M N := by
    apply ModuleCat.hom_ext
    ext g
    simp

/-- The hook-generator Hom functor detects zero persistence modules. -/
theorem isZero_hom_obj_iff (M : PModule.{u,0,u} k S) :
    IsZero ((homFunctor (k := k) (S := S)).obj M) ↔ IsZero M := by
  constructor
  · intro h
    rw [IsZero.iff_id_eq_zero] at h ⊢
    apply (F (k := k) (S := S)).map_injective
    change (F (k := k) (S := S)).map (𝟙 M) = (F (k := k) (S := S)).map 0
    rw [(F (k := k) (S := S)).map_id, (F (k := k) (S := S)).map_zero]
    exact h
  · exact (F (k := k) (S := S)).map_isZero

/-- The finite rows of every supplied certified minimal resolution compute
the ordinary Ext-based projective-dimension bound after applying Hom. -/
theorem hasProjectiveDimensionLE_iff_recorded_terms
    {M : PModule.{u,0,u} k S}
    (R : MinimalFiniteRankProjectiveResolution (k := k) (M := M)) (d : ℕ) :
    HasProjectiveDimensionLE ((homFunctor (k := k) (S := S)).obj M) d ↔
      ∀ j : Fin R.resolution.length, d < j.val → IsZero (R.resolution.term j) := by
  let Q := R.resolution
  have h := finite_rows_dimension_iff Q.length
    (fun i => (F (k := k) (S := S)).obj (Q.kernel i))
    (fun i => (F (k := k) (S := S)).obj (Q.term i))
    (fun i => (F (k := k) (S := S)).map (Q.inclusion i))
    (fun i => (F (k := k) (S := S)).map (Q.quotient i))
    (fun i => (homShortComplex (Q.row_rank_exact i).toIsPointwiseShortExact).zero)
    (fun i => homFunctor_map_shortExact (Q.row_rank_exact i))
    (fun i => by
      have := (minimalResolution_row_homCover R i).1
      infer_instance)
    (fun i => (minimalResolution_row_homCover R i).2.2)
    ((isZero_hom_obj_iff _).mpr
      (IsZero.of_iso (isZero_zero _) Q.terminal_iso)) (d + 1)
  have e := (F (k := k) (S := S)).mapIso Q.initial_iso
  have hdim : HasProjectiveDimensionLE ((F (k := k) (S := S)).obj M) d ↔
      HasProjectiveDimensionLT ((F (k := k) (S := S)).obj (Q.kernel 0)) (d + 1) :=
    ⟨fun h => by have := h; exact hasProjectiveDimensionLT_of_iso e.symm _,
      fun h => by have := h; exact hasProjectiveDimensionLT_of_iso e _⟩
  rw [hdim, h]
  simp only [Nat.succ_le_iff]
  constructor
  · intro hz j hj
    exact (isZero_hom_obj_iff _).mp (hz j hj)
  · intro hz j hj
    exact (isZero_hom_obj_iff _).mpr (hz j hj)

/-- An ordinary projective-dimension bound is equivalent to vanishing of
all higher zero-padded terms of any certified minimal resolution. -/
theorem hasProjectiveDimensionLE_iff
    {M : PModule.{u,0,u} k S}
    (R : MinimalFiniteRankProjectiveResolution (k := k) (M := M)) (d : ℕ) :
    HasProjectiveDimensionLE ((homFunctor (k := k) (S := S)).obj M) d ↔
      ∀ j, d < j → IsZero (R.termAt j) := by
  rw [hasProjectiveDimensionLE_iff_recorded_terms R d]
  constructor
  · intro h j hj
    by_cases hlen : j < R.resolution.length
    · rw [R.termAt_eq hlen]
      exact h ⟨j, hlen⟩ hj
    · rw [R.termAt_eq_zero (Nat.le_of_not_gt hlen)]
      exact isZero_zero _
  · intro h j hj
    simpa only [R.termAt_eq j.isLt] using h j.val hj

/-- Mathlib's ordinary projective dimension has the same degree bound as
the zero-padded terms of a certified minimal rank-projective resolution. -/
theorem projectiveDimension_le_iff
    {M : PModule.{u,0,u} k S}
    (R : MinimalFiniteRankProjectiveResolution (k := k) (M := M)) (d : ℕ) :
    projectiveDimension ((homFunctor (k := k) (S := S)).obj M) ≤ d ↔
      ∀ j, d < j → IsZero (R.termAt j) := by
  rw [CategoryTheory.projectiveDimension_le_iff, hasProjectiveDimensionLE_iff R d]

end

end TDA.Persistence.FiniteRankProjectiveHomDimension
