import TDA.Persistence.FiniteObservation
import TDA.Persistence.RealIntervalExamples

/-!
# Examples of pointwise finite interval families

These examples include an infinite family of convex real supports with finite
overlap at every parameter and the zero behavior of an empty family.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace TDA.Persistence.LocalFiniteExamples

open CategoryTheory CategoryTheory.Limits

/-- Compatibility name for the pointwise finite-overlap criterion in
`FiniteObservation.locallyFinite_family_finiteDimensional`. -/
theorem locallyFinite_family_finiteDimensional {k : Type*} [Field k] {J : Type}
    (S : J → Set ℝ) (hS : ∀ j, (S j).OrdConnected)
    (hlocal : ∀ t : ℝ, {j : J | t ∈ S j}.Finite) (t : ℝ) :
    FiniteDimensional k ((AlgebraicFamily.familyModule
      (fun j => SupportInterval.module (k := k) (S j) (hS j))).obj t) :=
  FiniteObservation.locallyFinite_family_finiteDimensional S hS hlocal t

private theorem accumulatingOrdConnected (n : ℕ) :
    (RealIntervalExamples.accumulatingInterval n).OrdConnected := by
  change (Set.Ioc (RealIntervalExamples.endpoint (n + 1))
    (RealIntervalExamples.endpoint n)).OrdConnected
  exact Set.ordConnected_Ioc

/-- An infinite family of interval supports accumulating at zero, with finite
overlap at every real parameter and finite-dimensional fibers. -/
noncomputable def accumulatingFamily : PModule ℚ ℝ :=
  AlgebraicFamily.familyModule (fun n : ℕ => SupportInterval.module (k := ℚ)
    (RealIntervalExamples.accumulatingInterval n) (accumulatingOrdConnected n))

theorem accumulatingFamily_finiteDimensional (t : ℝ) :
    FiniteDimensional ℚ (accumulatingFamily.obj t) := by
  exact FiniteObservation.locallyFinite_family_finiteDimensional
    RealIntervalExamples.accumulatingInterval
    accumulatingOrdConnected
    RealIntervalExamples.activeIndices_finite t

/-- Every occurrence contributes a nonzero fiber at its selected point. -/
theorem accumulatingFamily_nonzero_at_endpoint (n : ℕ) :
    ∃ y : accumulatingFamily.obj (RealIntervalExamples.endpoint n), y ≠ 0 := by
  let F : ℕ → PModule ℚ ℝ := fun j => SupportInterval.module (k := ℚ)
    (RealIntervalExamples.accumulatingInterval j) (accumulatingOrdConnected j)
  let x : (F n).obj (RealIntervalExamples.endpoint n) :=
    SupportInterval.one (k := ℚ) (RealIntervalExamples.accumulatingInterval n)
      (RealIntervalExamples.occurrence_point_lies_in_interval n)
  let y : accumulatingFamily.obj (RealIntervalExamples.endpoint n) :=
    ((AlgebraicFamily.inclusion F n).app (RealIntervalExamples.endpoint n)).hom x
  refine ⟨y, ?_⟩
  intro hy
  have hx : x ≠ 0 := by
    intro he
    have hv := congrArg (fun z : SupportInterval.fiber (k := ℚ)
      (RealIntervalExamples.accumulatingInterval n)
      (RealIntervalExamples.endpoint n) => (z : ℚ)) he
    simp [x, SupportInterval.one] at hv
  have hc := congrArg (DirectSum.component ℚ ℕ
    (fun j => (F j).obj (RealIntervalExamples.endpoint n)) n) hy
  change DirectSum.component ℚ ℕ
    (fun j => (F j).obj (RealIntervalExamples.endpoint n)) n
      (((AlgebraicFamily.inclusion F n).app
        (RealIntervalExamples.endpoint n)).hom x) = 0 at hc
  rw [AlgebraicFamily.inclusion_apply_self] at hc
  exact hx hc

/-- The empty occurrence family is the zero persistence module itself. -/
theorem emptyFamily_isZero :
    IsZero (AlgebraicFamily.familyModule RealIntervalExamples.emptyFamily) := by
  apply Functor.isZero
  intro t
  rw [ModuleCat.isZero_iff_subsingleton]
  exact RealIntervalExamples.empty_family_fiber_is_subsingleton t

end TDA.Persistence.LocalFiniteExamples
