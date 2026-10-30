import TDA.Persistence.FiniteRankProjectiveResolutionHookBetti
import TDA.Persistence.FiniteRankProjectiveResolution

/-!
# Examples for resolution hook multisets

The principal upset is already a projective hook. Its identity resolution
therefore has no positive-degree hook occurrences, and uniqueness transfers
that vanishing to every certified minimal resolution.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence.FiniteRankProjectiveResolutionHookBettiExamples

open CategoryTheory
open CategoryTheory.Limits
open scoped ZeroObject

private noncomputable abbrev principalHook : PModule.{0,0,0} ℚ (Fin 2 → ℝ) :=
  HookInfinity.module (R := ℚ) (0 : Fin 2 → ℝ)

private theorem principalHook_finitelyPresented :
    GradedFree.FinitelyPresented (R := ℚ) (P := Fin 2 → ℝ) principalHook :=
  GradedFree.free_finitelyPresented (R := ℚ) (P := Fin 2 → ℝ)
    (HookInfinity.generators (P := Fin 2 → ℝ) (0 : Fin 2 → ℝ))

private theorem principalHook_identity_isRankProjectiveCover :
    IsRankProjectiveCover (𝟙 principalHook) := by
  apply IsRankProjectiveCover.of_identity
  · intro p
    infer_instance
  · exact HookInfinity.isRankProjective (i := (0 : Fin 2 → ℝ))

private noncomputable def principalHookFiniteResolution :
    FiniteRankProjectiveResolution principalHook :=
  FiniteRankProjectiveResolution.ofRankProjective principalHook
    (by intro p; infer_instance)
    (HookInfinity.isRankProjective (i := (0 : Fin 2 → ℝ)))

/-- The identity quotient gives the one-term minimal resolution of this free
principal-upset hook. -/
noncomputable def principalHookIdentityMinimalResolution :
    MinimalFiniteRankProjectiveResolution (k := ℚ) (M := principalHook) where
  resolution := principalHookFiniteResolution
  quotient_is_cover := by
    intro i
    have hlen : principalHookFiniteResolution.length = 1 := rfl
    have hi : i = ⟨0, by rw [hlen]; omega⟩ := by
      apply Fin.ext
      have hval : i.val < 1 := by simpa only [hlen] using i.isLt
      omega
    subst i
    change IsRankProjectiveCover (𝟙 principalHook)
    exact principalHook_identity_isRankProjectiveCover

/-- Since a principal upset is projective, every certified minimal resolution
has zero positive-degree terms and therefore no positive-degree hook tags. -/
theorem principalHook_positive_degree_terms_have_empty_hook_multiset
    (R : MinimalFiniteRankProjectiveResolution (k := ℚ) (M := principalHook))
    {j : ℕ} (hj : 0 < j) :
    R.hookBettiMultiset (k := ℚ) (n := 2) (by omega) principalHook
      principalHook_finitelyPresented j = 0 := by
  apply R.hookBettiMultiset_eq_zero_of_term_isZero
    (k := ℚ) (n := 2) (by omega) principalHook principalHook_finitelyPresented
  obtain ⟨e⟩ := R.termAt_nonempty_iso principalHookIdentityMinimalResolution j
  have hzero : principalHookIdentityMinimalResolution.termAt j =
      (0 : PModule.{0,0,0} ℚ (Fin 2 → ℝ)) := by
    apply principalHookIdentityMinimalResolution.termAt_eq_zero
    change 1 ≤ j
    omega
  exact IsZero.of_iso (isZero_zero _) (e.trans (eqToIso hzero))

end TDA.Persistence.FiniteRankProjectiveResolutionHookBettiExamples
