import TDA.Persistence.RankResolutionDegreeTwoFinite
import Mathlib.Tactic

/-!
# The real-coordinate degree-two witness

The finite-grid witness is regarded as its actual left Kan extension. Its
original finite presentation is derived from the finite grid, and the concrete
minimal rank-projective resolution transfers through that same Kan functor.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence.RankResolutionDegreeTwo

open CategoryTheory CategoryTheory.Limits
open scoped TDA.Persistence ZeroObject

variable {k : Type u} [Field k]

noncomputable section

/-- The actual real-coordinate module obtained by left Kan extension of the
finite L-shaped support module. -/
abbrev realModule : PModule.{u,0,u} k (Fin 2 → ℝ) :=
  grid.lan.obj (finiteModule (k := k))

/-- The real module has an original finite presentation, derived from the
finite-grid fibers and the existing finite-grid Kan preservation theorem. -/
theorem realModule_finitelyPresented :
    GradedFree.FinitelyPresented.{u,0,0} (R := k) (P := Fin 2 → ℝ)
      (realModule (k := k)) := by
  have hfd : ∀ p : grid.Point, FiniteDimensional k ((finiteModule (k := k)).obj p) := by
    intro p
    infer_instance
  exact GradedFree.finitelyPresented_lan_of_finiteGrid grid
    (GradedFree.pfd_finitelyPresented_of_finite_poset
      (finiteModule (k := k)) hfd)

/-- The birth grade of the real second hook is `(1,1)`. -/
abbrev realSecondBirth : Fin 2 → ℝ := fun _ => 1

/-- The death grade of the real second hook is `(2,2)`. -/
abbrev realSecondDeath : Fin 2 → ℝ := fun _ => 2

/-- The actual real hook H((1,1),(2,2)); its support is the hook support
`birth ≤ p ∧ ¬ death ≤ p`. -/
abbrev realSecondHook : PModule.{u,0,u} k (Fin 2 → ℝ) :=
  Hook.module (k := k) realSecondBirth realSecondDeath

/-- The actual minimal resolution obtained by applying the grid's left Kan
extension to the literal finite minimal resolution. -/
noncomputable def realMinimalResolution :
    MinimalFiniteRankProjectiveResolution (k := k) (M := realModule (k := k)) :=
  grid.lanMinimalFiniteRankProjectiveResolutionObj
    (finiteMinimalResolution (k := k))

/-- The second term of the actual real minimal resolution is the real hook
with birth `(1,1)` and death `(2,2)`. -/
noncomputable def realMinimalResolution_termAt_two_iso :
    (realMinimalResolution (k := k)).termAt 2 ≅ realSecondHook (k := k) := by
  have hendpoints :
      Hook.module (k := k) (grid.embedding c) (grid.embedding h) =
        realSecondHook (k := k) := by
    rw [grid_embedding_c, grid_embedding_h]
  exact
    (grid.lanMinimalFiniteRankProjectiveResolutionObj_termAtIso
      (finiteMinimalResolution (k := k)) 2).trans
      ((grid.lan.mapIso
        (eqToIso (finiteMinimalResolution_termAt_two (k := k)))).trans
        ((grid.hookLanIso c h).trans (eqToIso hendpoints)))

/-- The embedded endpoints are strictly ordered, so the real hook has a
canonical nonzero birth unit. -/
theorem realSecondHook_birth_lt_death :
    realSecondBirth < realSecondDeath := by
  rw [lt_iff_le_not_ge]
  constructor
  · intro i
    norm_num
  · intro h
    have h0 := h 0
    norm_num at h0

/-- The real second hook is nonzero at its birth grade. -/
theorem realSecondHook_not_isZero : ¬ IsZero (realSecondHook (k := k)) := by
  intro hz
  have he := congrArg (fun α : End (realSecondHook (k := k)) =>
      ((α.app realSecondBirth).hom
        (SupportInterval.one (Hook.support realSecondBirth realSecondDeath)
          (Hook.birth_mem realSecondHook_birth_lt_death)) : k))
    (hz.eq_of_src (𝟙 (realSecondHook (k := k))) 0)
  exact (one_ne_zero : (1 : k) ≠ 0) (by
    simpa [SupportInterval.one] using he)

/-- Every certified minimal real resolution has a genuine nonzero second term,
regardless of its recorded terminal zero padding. -/
theorem realMinimalResolution_second_term_nonzero
    (R : MinimalFiniteRankProjectiveResolution (k := k)
      (M := realModule (k := k))) :
    ¬ IsZero (R.termAt 2) := by
  intro hz
  obtain ⟨e⟩ := R.termAt_nonempty_iso (realMinimalResolution (k := k)) 2
  have hzero := IsZero.of_iso hz e.symm
  exact realSecondHook_not_isZero (IsZero.of_iso hzero
    (realMinimalResolution_termAt_two_iso (k := k)).symm)

/-- Every certified minimal real resolution vanishes strictly above degree two,
independently of any terminal zero padding in the supplied resolution. -/
theorem realMinimalResolution_terms_vanish_above_two
    (R : MinimalFiniteRankProjectiveResolution (k := k)
      (M := realModule (k := k))) (j : ℕ) (hj : 2 < j) :
    IsZero (R.termAt j) := by
  obtain ⟨e⟩ := R.termAt_nonempty_iso (realMinimalResolution (k := k)) j
  have hS : IsZero ((realMinimalResolution (k := k)).termAt j) := by
    rw [(realMinimalResolution (k := k)).termAt_eq_zero (by
      change 3 ≤ j
      omega)]
    exact isZero_zero _
  exact IsZero.of_iso hS e

/-- The field alone supplies the concrete real-coordinate minimal resolution
and proves its exact degree-two rank-projective resolution degree. -/
theorem exists_realMinimalResolution_degree_two :
    ∃ R : MinimalFiniteRankProjectiveResolution (k := k)
        (M := realModule (k := k)),
      ¬ IsZero (R.termAt 2) ∧ ∀ j, 2 < j → IsZero (R.termAt j) :=
  ⟨realMinimalResolution (k := k),
    realMinimalResolution_second_term_nonzero (realMinimalResolution (k := k)),
    fun j hj => realMinimalResolution_terms_vanish_above_two
      (realMinimalResolution (k := k)) j hj⟩

end

end TDA.Persistence.RankResolutionDegreeTwo
