import TDA.Persistence.FiniteRankProjectiveHomDimension
import TDA.Persistence.FiniteRankProjectiveResolutionUniquenessExamples

/-!
# Degree-zero and padding examples for hook Hom projective dimension

The zero module has projective dimension bottom, whereas a nonzero
principal-upset hook has projective dimension zero. An explicitly padded
minimal resolution of zero exercises recorded terms in positive degrees.
-/

set_option autoImplicit false

namespace TDA.Persistence.FiniteRankProjectiveHomDimensionExamples

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject
open FiniteRankProjectiveHomExact FiniteRankProjectiveHomDimension
open FiniteRankProjectiveResolutionUniquenessExamples

noncomputable section

private abbrev F := homFunctor (k := ℚ) (S := Fin 2)
private abbrev H := HookInfinity.module (R := ℚ) (0 : Fin 2)
private abbrev Z := (0 : PModule.{0,0,0} ℚ (Fin 2))

/-- The zero Hom module has Mathlib projective dimension bottom. -/
theorem zero_projectiveDimension : projectiveDimension (F.obj Z) = ⊥ := by
  exact (projectiveDimension_eq_bot_iff _).mpr
    ((isZero_hom_obj_iff Z).mpr (isZero_zero _))

/-- A nonzero principal-upset hook has ordinary Hom projective dimension zero. -/
theorem principalHook_projectiveDimension : projectiveDimension (F.obj H) = 0 := by
  apply (projectiveDimension_eq_zero_iff _).mpr
  constructor
  · apply (projective_iff_hasProjectiveDimensionLE_zero (F.obj H)).mpr
    exact (hasProjectiveDimensionLE_iff principalHookMinimalResolution 0).mpr
      (fun j hj => principalHook_positive_terms_are_zero principalHookMinimalResolution hj)
  · intro h
    have hz := (isZero_hom_obj_iff H).mp h
    have hId := hz.eq_of_src (𝟙 H) 0
    have hb := congrArg (fun f : H ⟶ H =>
      (f.app 0).hom (HookInfinity.birth (R := ℚ) (0 : Fin 2))) hId
    exact HookInfinity.birth_ne_zero (k := ℚ) (0 : Fin 2) (by simpa using hb)

/-- The degree-one term at the end of the one-term hook resolution vanishes
by the public dimension comparison. -/
theorem principalHook_padding_boundary :
    IsZero (principalHookMinimalResolution.termAt 1) := by
  have hd : projectiveDimension (F.obj H) ≤ (0 : ℕ) := by
    rw [principalHook_projectiveDimension]
    rfl
  exact (FiniteRankProjectiveHomDimension.projectiveDimension_le_iff
    principalHookMinimalResolution 0).mp hd 1 (by decide)

private theorem zero_row : IsRankExact (0 : Z ⟶ Z) (𝟙 Z) := by
  have : ∀ p, Subsingleton (Z.obj p) := fun p =>
    ModuleCat.subsingleton_of_isZero (Functor.zero_obj p)
  have hs : IsPointwiseShortExact (0 : Z ⟶ Z) (𝟙 Z) := by
    constructor
    · intro p x y _
      exact (ModuleCat.subsingleton_of_isZero (Functor.zero_obj p)).elim x y
    · intro p x
      exact ⟨x, rfl⟩
    · intro p
      simp
      exact top_unique (by
        intro x _
        change x = 0
        exact Subsingleton.elim _ _)
  exact hs.rankExact_of_section (𝟙 Z) (by simp)

/-- A minimal resolution consisting of any prescribed number of zero terms. -/
def paddedZeroMinimalResolution (m : ℕ) :
    MinimalFiniteRankProjectiveResolution (k := ℚ) (M := Z) where
  resolution := {
    length := m
    kernel := fun _ => Z
    term := fun _ => Z
    inclusion := fun _ => 0
    quotient := fun _ => 𝟙 Z
    row_rank_exact := fun _ => zero_row
    initial_iso := Iso.refl Z
    terminal_iso := Iso.refl Z
    term_rank_projective := fun _ =>
      FiniteRankProjectiveResolutionKanExamples.zero_identity_isRankProjectiveCover.term_rank_projective
  }
  quotient_is_cover := fun _ =>
    FiniteRankProjectiveResolutionKanExamples.zero_identity_isRankProjectiveCover

/-- A degree-one bound applies to a three-term minimal resolution with
terminal zero padding, including its recorded degree-two term. -/
theorem paddedZero_higher_degree :
    (paddedZeroMinimalResolution 3).resolution.length = 3 ∧
      IsZero ((paddedZeroMinimalResolution 3).termAt 2) := by
  refine ⟨rfl, ?_⟩
  have hd : projectiveDimension (F.obj Z) ≤ (1 : ℕ) := by
    rw [zero_projectiveDimension]
    exact bot_le
  exact (FiniteRankProjectiveHomDimension.projectiveDimension_le_iff
    (paddedZeroMinimalResolution 3) 1).mp hd 2 (by decide)

end

end TDA.Persistence.FiniteRankProjectiveHomDimensionExamples
