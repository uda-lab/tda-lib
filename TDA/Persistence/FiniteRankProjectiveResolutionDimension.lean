import TDA.Persistence.FiniteRankProjectiveResolutionKan
import TDA.Persistence.FiniteRankProjectiveResolutionUniqueness
import TDA.Persistence.FiniteRankProjectiveHomQuotientDimension

/-!
# The real-coordinate minimal-resolution degree bound

An original finite presentation reconstructs its module from a nonempty
finite coordinate grid. The finite-grid Hom-cokernel theorem bounds every
certified minimal resolution on that grid. The actual left Kan extension
transfers the certified rows and their zero-padded terms, and the existing
termwise uniqueness theorem transfers the vanishing to every minimal
resolution of the original module.

This proves only the upper degree bound. It is not a bound on the stored
resolution length, a sharpness result, or the final signed-stability theorem.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

variable {k : Type u} [Field k] {n : ℕ}

namespace CoordinateGrid

/-- The zero-padded terms of a transferred minimal resolution are the actual
Kan images of the zero-padded grid terms. In the recorded range this is the
term identity; beyond it, both terms are zero objects. -/
noncomputable def lanMinimalFiniteRankProjectiveResolutionObj_termAtIso
    (G : CoordinateGrid n) {A : PModule.{u,0,u} k G.Point}
    (R : MinimalFiniteRankProjectiveResolution (k := k) (M := A)) (j : ℕ) :
    (G.lanMinimalFiniteRankProjectiveResolutionObj R).termAt j ≅
      G.lan.obj (R.termAt j) := by
  let S := G.lanMinimalFiniteRankProjectiveResolutionObj R
  by_cases hj : j < R.resolution.length
  · have hS : j < S.resolution.length := by
      simpa [S, CoordinateGrid.lanMinimalFiniteRankProjectiveResolutionObj,
        CoordinateGrid.lanFiniteRankProjectiveResolution] using hj
    have hterm : S.termAt j = G.lan.obj (R.termAt j) := by
      rw [S.termAt_eq hS, R.termAt_eq hj]
      rfl
    exact eqToIso hterm
  · have hlen : R.resolution.length ≤ j := Nat.le_of_not_gt hj
    have hleft : IsZero (S.termAt j) := by
      rw [S.termAt_eq_zero hlen]
      exact isZero_zero _
    have hright : IsZero (G.lan.obj (R.termAt j)) := by
      rw [R.termAt_eq_zero hlen]
      exact Functor.map_isZero G.lan (isZero_zero _)
    exact hleft.iso hright

end CoordinateGrid

namespace FiniteRankProjectiveResolution

/-- The original finite-presentation hypothesis alone yields one certified
minimal resolution of a real-coordinate module whose zero-padded terms
vanish strictly above `2*n-2`. The finite presentation supplies both the
finite-dimensional grid fibers and nonempty coordinate factors; the bound is
the existing arbitrary-field finite-grid result transported through the
actual left Kan extension. -/
theorem finitelyPresented_exists_minimalFiniteRankProjectiveResolution_with_bound
    (hn : 1 ≤ n) (M : PModule.{u,0,u} k (Fin n → ℝ))
    (hM : GradedFree.FinitelyPresented.{u,0,0}
      (R := k) (P := Fin n → ℝ) M) :
    ∃ R : MinimalFiniteRankProjectiveResolution (k := k) (M := M),
      ∀ j, 2 * n - 2 < j → IsZero (R.termAt j) := by
  classical
  obtain ⟨G, A, hA, hG, ⟨e⟩⟩ :=
    GradedFree.finitelyPresented_exists_pfd_nonempty_finiteGridKan M hM
  obtain ⟨R⟩ :=
    FiniteRankProjectiveResolution.exists_minimalFiniteRankProjectiveResolution_of_pfd_finitePoset
      A hA
  let R' := G.lanMinimalFiniteRankProjectiveResolutionObj R
  let Rreal : MinimalFiniteRankProjectiveResolution (k := k) (M := M) := {
    resolution := R'.resolution.ofIso e
    quotient_is_cover := fun i => R'.quotient_is_cover i
  }
  have hGrid :=
    FiniteRankProjectiveHomQuotientDimension.coordinateGrid_minimalResolution_termAt_isZero
      G hn hG A hA R
  refine ⟨Rreal, ?_⟩
  intro j hj
  change IsZero (R'.termAt j)
  exact IsZero.of_iso (Functor.map_isZero G.lan (hGrid j hj))
    (G.lanMinimalFiniteRankProjectiveResolutionObj_termAtIso R j)

/-- Every supplied certified minimal resolution of an originally finitely
presented real-coordinate module has zero terms strictly above `2*n-2`.
This uses the separately proved existence witness and the existing
zero-padded termwise uniqueness theorem, so the conclusion is independent of
the chosen resolution and of any terminal zero padding in its stored length. -/
theorem finitelyPresented_minimalFiniteRankProjectiveResolution_termAt_isZero
    (hn : 1 ≤ n) (M : PModule.{u,0,u} k (Fin n → ℝ))
    (hM : GradedFree.FinitelyPresented.{u,0,0}
      (R := k) (P := Fin n → ℝ) M)
    (R : MinimalFiniteRankProjectiveResolution (k := k) (M := M)) :
    ∀ j, 2 * n - 2 < j → IsZero (R.termAt j) := by
  obtain ⟨S, hS⟩ :=
    FiniteRankProjectiveResolution.finitelyPresented_exists_minimalFiniteRankProjectiveResolution_with_bound
      hn M hM
  intro j hj
  obtain ⟨e⟩ := R.termAt_nonempty_iso S j
  exact IsZero.of_iso (hS j hj) e

end FiniteRankProjectiveResolution

end TDA.Persistence
