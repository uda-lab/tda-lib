import TDA.Reeb.Components
import TDA.Reeb.Interval

/-!
# Interval restriction of the path-component functor

The path-component functor `C_f : Opens ℝ ⥤ Type u` of a continuous `f : C(X, ℝ)` restricts
along the inclusion `toOpensFunctor : OpenInterval ⥤ Opens ℝ` of the interval category. The
restriction `intervalComponents f = toOpensFunctor ⋙ componentFunctor f` sends an open interval
`I` to the path components of the inverse-image subspace `{x // f x ∈ I}` and an inclusion of
intervals to the map induced on representatives: the path-component pre-cosheaf over open
intervals of de Silva–Munch–Patel (Example 3.3 and §3.4). The empty interval has no components.
This is a precosheaf on the interval category; no cosheaf condition is stated here. See
`docs/math/reeb-perturbation.md`.
-/

open Set CategoryTheory
open scoped NNReal

universe u

namespace TDA.Reeb

open OpenInterval

section IntervalComponents

variable {X : Type u} [TopologicalSpace X]

/-- The interval restriction `C_f|Int = toOpensFunctor ⋙ C_f` of the path-component functor. -/
def intervalComponents (f : C(X, ℝ)) : OpenInterval ⥤ Type u :=
  toOpensFunctor ⋙ componentFunctor f

theorem intervalComponents_obj (f : C(X, ℝ)) (I : OpenInterval) :
    (intervalComponents f).obj I = ZerothHomotopy {x : X // f x ∈ I} := rfl

@[simp]
theorem intervalComponents_map_mk (f : C(X, ℝ)) {I J : OpenInterval} (i : I ⟶ J)
    (x : {x : X // f x ∈ toOpens I}) :
    (intervalComponents f).map i (ZerothHomotopy.mk x) =
      ZerothHomotopy.mk
        (⟨x.1, OpenInterval.le_iff_subset.1 (leOfHom i) x.2⟩ : {x : X // f x ∈ toOpens J}) :=
  rfl

/-- The empty interval has no components. -/
instance intervalComponents_obj_bot_isEmpty (f : C(X, ℝ)) :
    IsEmpty ((intervalComponents f).obj ⊥) :=
  ⟨fun c => by
    induction c using ZerothHomotopy.rec with
    | mk x => exact x.2⟩

end IntervalComponents

end TDA.Reeb
