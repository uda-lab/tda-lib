import TDA.Topology.PathCover
import TDA.Reeb.Components

/-!
# Component language of the path-local cover lemma

Two point-form facts about the open-set path-component functor `componentFunctor f`; the second
is the component-language consequence of `TDA.Topology.reflTransGen_preimage`:

* `componentFunctor_mk_eq_iff_joined`: two points of `f ⁻¹ W` have the same class in
  `(componentFunctor f).obj W` exactly when they are joined inside `f ⁻¹ W`. Pinned mathlib has
  no `ZerothHomotopy.exact`; the forward direction is `Quotient.exact`, the backward direction
  `ZerothHomotopy.sound` applied to `Joined.somePath`.
* `componentFunctor_reflTransGen_of_mk_eq`: if two points have the same class over `W` and the
  opens `U i` cover `W`, they are linked by a finite chain of points of `f ⁻¹ W` in which each
  link has equal classes over a single `U i`. `U i ≤ W` is not needed.

This is the step a gluing argument uses to show that a value defined locally on classes over
the members is constant on classes over `W`. The overlap relation on local classes and the
coequalizer form of gluing are not part of this module. See `docs/math/reeb-components.md`.
-/

namespace TDA.Reeb

universe u v

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y] {ι : Sort*}

/-- Equality of classes in `(componentFunctor f).obj W` is joinedness inside `f ⁻¹ W`. -/
theorem componentFunctor_mk_eq_iff_joined (f : C(X, Y)) (W : TopologicalSpace.Opens Y)
    (a b : {x : X // f x ∈ W}) :
    (ZerothHomotopy.mk a : (componentFunctor f).obj W) = ZerothHomotopy.mk b ↔ Joined a b :=
  ⟨fun h => Quotient.exact h, fun h => ZerothHomotopy.sound h.somePath⟩

/-- Point-form component consequence of the path-local cover lemma: if `a` and `b` have the same
class over `W` and the opens `U i` cover `W`, then they are linked by a finite chain in which
each link has equal classes over a single `U i`. `U i ≤ W` is not needed. -/
theorem componentFunctor_reflTransGen_of_mk_eq (f : C(X, Y)) {W : TopologicalSpace.Opens Y}
    (U : ι → TopologicalSpace.Opens Y) (hcov : W ≤ ⨆ i, U i) {a b : {x : X // f x ∈ W}}
    (h : (ZerothHomotopy.mk a : (componentFunctor f).obj W) = ZerothHomotopy.mk b) :
    Relation.ReflTransGen
      (fun a b : {x : X // f x ∈ W} => ∃ i, ∃ (ha : f a.1 ∈ U i) (hb : f b.1 ∈ U i),
        (ZerothHomotopy.mk ⟨a.1, ha⟩ : (componentFunctor f).obj (U i)) =
          ZerothHomotopy.mk ⟨b.1, hb⟩) a b := by
  refine Relation.ReflTransGen.mono ?_ a b
    (TDA.Topology.reflTransGen_preimage f U hcov
      ((componentFunctor_mk_eq_iff_joined f W a b).1 h))
  rintro c d ⟨i, hc, hd, hJ⟩
  exact ⟨i, hc, hd, (componentFunctor_mk_eq_iff_joined f (U i) _ _).2 hJ⟩

end TDA.Reeb
