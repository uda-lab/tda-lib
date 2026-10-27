import TDA.Persistence.FinitePresentationLifting

/-!
# Enlarging finite presentation index universes

Finite presentations over a module whose values live in `Type u` may be
given with finite generator and relation carriers in `Type 0`. This file
reindexes those finite carriers by `ULift` so that the presentation has
carriers in `Type u`, without changing the presented module.
-/

set_option autoImplicit false

universe u v

namespace TDA.Persistence

open CategoryTheory CategoryTheory.Limits

namespace GradedFree

variable {R : Type u} [Ring R] {P : Type v} [Preorder P]

/-- Lift the carrier universe of a graded generator family while retaining
each grade. -/
def GradedGenerators.liftIndexUniverse (W : GradedGenerators.{v,0} P) :
    GradedGenerators.{v,u} P where
  Carrier := ULift.{u} W.Carrier
  grade := fun g => W.grade g.down

/-- The lifted and original free modules are naturally isomorphic, by the
existing free-module lifting map and its values on birth generators. -/
noncomputable def GradedGenerators.liftIndexUniverseIso
    (W : GradedGenerators.{v,0} P) :
    module (R := R) W.liftIndexUniverse ≅ module (R := R) W := by
  let W' := W.liftIndexUniverse
  let toOld : module (R := R) W' ⟶ module (R := R) W :=
    lift (R := R) W' (module (R := R) W) (fun g => birth (R := R) W g.down)
  let toLifted : module (R := R) W ⟶ module (R := R) W' :=
    lift (R := R) W (module (R := R) W')
      (fun g => birth (R := R) W' (ULift.up g))
  refine ⟨toOld, toLifted, ?_, ?_⟩
  · apply hom_ext_birth (R := R) W'
    intro g
    cases g with
    | up g =>
      have hOld : (toOld.app (W'.grade (ULift.up g)))
          (birth (R := R) W' (ULift.up g)) = birth (R := R) W g := by
        dsimp [toOld]
        exact lift_birth (R := R) W' (module (R := R) W)
          (fun g => birth (R := R) W g.down) (ULift.up g)
      have hLifted : (toLifted.app (W'.grade (ULift.up g)))
          (birth (R := R) W g) = birth (R := R) W' (ULift.up g) := by
        dsimp [toLifted]
        exact lift_birth (R := R) W (module (R := R) W')
          (fun g => birth (R := R) W' (ULift.up g)) g
      change (toLifted.app (W'.grade (ULift.up g)))
        ((toOld.app (W'.grade (ULift.up g)))
          (birth (R := R) W' (ULift.up g))) = _
      rw [hOld, hLifted, NatTrans.id_app, ModuleCat.id_apply]
  · apply hom_ext_birth (R := R) W
    intro g
    have hLifted : (toLifted.app (W.grade g)) (birth (R := R) W g) =
        birth (R := R) W' (ULift.up g) := by
      dsimp [toLifted]
      exact lift_birth (R := R) W (module (R := R) W')
        (fun g => birth (R := R) W' (ULift.up g)) g
    have hOld : (toOld.app (W.grade g))
        (birth (R := R) W' (ULift.up g)) = birth (R := R) W g := by
      dsimp [toOld]
      exact lift_birth (R := R) W' (module (R := R) W)
        (fun g => birth (R := R) W g.down) (ULift.up g)
    change (toOld.app (W.grade g))
      ((toLifted.app (W.grade g)) (birth (R := R) W g)) = _
    rw [hLifted, hOld]
    rw [NatTrans.id_app, ModuleCat.id_apply]

/-- A finite presentation can be reindexed into a larger generator-carrier
universe. The displayed cokernel isomorphism is transported by `cokernel.mapIso`.
-/
noncomputable def Presentation.liftIndexUniverse
    (D : Presentation.{u,v,0} (R := R) (P := P)) :
    Presentation.{u,v,u} (R := R) (P := P) where
  generators := D.generators.liftIndexUniverse
  relations := D.relations.liftIndexUniverse
  relationMap := D.relations.liftIndexUniverseIso.hom ≫ D.relationMap ≫
    D.generators.liftIndexUniverseIso.inv

/-- The lifted presentation presents the same module. -/
noncomputable def Presentation.liftIndexUniversePresentedIso
    (D : Presentation.{u,v,0} (R := R) (P := P)) :
    (D.liftIndexUniverse).presented ≅ D.presented := by
  let D' := D.liftIndexUniverse
  change cokernel D'.relationMap ≅ cokernel D.relationMap
  apply cokernel.mapIso (f := D'.relationMap) D.relationMap
    D.relations.liftIndexUniverseIso D.generators.liftIndexUniverseIso
  simp [D', Presentation.liftIndexUniverse, Category.assoc]

/-- Original finite presentations with index carriers in `Type 0` can be
used by APIs requiring carriers in the module universe. -/
theorem finitelyPresented_liftIndexUniverse
    (M : PModule.{u,v,u} R P)
    (hM : FinitelyPresented.{u,v,0} (R := R) (P := P) M) :
    FinitelyPresented.{u,v,u} (R := R) (P := P) M := by
  obtain ⟨D, hD, ⟨e⟩⟩ := hM
  haveI : Finite D.generators.Carrier := hD.1
  haveI : Finite D.relations.Carrier := hD.2
  refine ⟨D.liftIndexUniverse, ?_, ⟨D.liftIndexUniversePresentedIso.trans e⟩⟩
  · change Finite (D.generators.liftIndexUniverse.Carrier) ∧
      Finite (D.relations.liftIndexUniverse.Carrier)
    exact ⟨Finite.of_injective ULift.down ULift.down_injective,
      Finite.of_injective ULift.down ULift.down_injective⟩

end GradedFree

end TDA.Persistence
