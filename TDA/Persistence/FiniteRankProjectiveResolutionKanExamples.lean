import TDA.Persistence.FiniteRankProjectiveResolutionKan

/-!
# Examples for finite-presentable rank-projective resolutions

The main theorem consumes only finite presentation. A principal upset is a
nonzero free, hence finitely presented, module and provides a direct downstream
application of that interface.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence.FiniteRankProjectiveResolutionKanExamples

open CategoryTheory

variable {k : Type u} [Field k] {n : ℕ}

/-- A nonzero principal-upset free module has a finite rank-projective
resolution by the finite-presentation existence theorem. -/
theorem principalUpset_has_finiteRankProjectiveResolution
    (hn : 0 < n) (a : Fin n → ℝ) :
    Nonempty (FiniteRankProjectiveResolution
      (HookInfinity.module (R := k) a)) := by
  apply FiniteRankProjectiveResolution.finitelyPresented_exists_finiteRankProjectiveResolution
    hn
  exact GradedFree.free_finitelyPresented (R := k) (P := Fin n → ℝ)
    (HookInfinity.generators (P := Fin n → ℝ) a)

end TDA.Persistence.FiniteRankProjectiveResolutionKanExamples
