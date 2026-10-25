import TDA.Persistence.FiniteRankProjectiveResolutionUniqueness
import TDA.Persistence.FiniteRankProjectiveResolutionExamples
import TDA.Persistence.FiniteRankProjectiveResolutionKanExamples

/-!
# Examples of minimal-resolution uniqueness

The principal-upset hook is itself projective, so its identity is a certified
one-term minimal resolution. Uniqueness then forces the positive-degree terms
of every minimal resolution of that module to vanish.
-/

set_option autoImplicit false

namespace TDA.Persistence.FiniteRankProjectiveResolutionUniquenessExamples

open CategoryTheory
open CategoryTheory.Limits
open scoped ZeroObject

private noncomputable abbrev principalHook : PModule.{0,0,0} ℚ (Fin 2) :=
  HookInfinity.module (R := ℚ) (0 : Fin 2)

/-- The one-term identity resolution of a principal-upset hook, with its
quotient row certified as a minimal rank-projective cover. -/
noncomputable def principalHookMinimalResolution :
    MinimalFiniteRankProjectiveResolution (k := ℚ) (M := principalHook) where
  resolution := FiniteRankProjectiveResolutionExamples.oneTermHookResolution
  quotient_is_cover := by
    intro i
    have hlen : FiniteRankProjectiveResolutionExamples.oneTermHookResolution.length = 1 := rfl
    have hi : i = ⟨0, by rw [hlen]; omega⟩ := by
      apply Fin.ext
      have hval : i.val < 1 := by simpa only [hlen] using i.isLt
      omega
    subst i
    change IsRankProjectiveCover (𝟙 principalHook)
    exact TDA.Persistence.FiniteRankProjectiveResolutionKanExamples.principalUpset_identity_isRankProjectiveCover 0

/-- Since the principal-upset module is already projective, every certified
minimal finite resolution has zero terms in positive degree. -/
theorem principalHook_positive_terms_are_zero
    (R : MinimalFiniteRankProjectiveResolution (k := ℚ) (M := principalHook))
    {j : ℕ} (hj : 0 < j) : IsZero (R.termAt j) := by
  obtain ⟨e⟩ := R.termAt_nonempty_iso principalHookMinimalResolution j
  have hzero : principalHookMinimalResolution.termAt j =
      (0 : PModule.{0,0,0} ℚ (Fin 2)) := by
    apply principalHookMinimalResolution.termAt_eq_zero
    rw [show principalHookMinimalResolution.resolution.length = 1 by rfl]
    omega
  exact IsZero.of_iso (isZero_zero _) (e.trans (eqToIso hzero))

end TDA.Persistence.FiniteRankProjectiveResolutionUniquenessExamples
