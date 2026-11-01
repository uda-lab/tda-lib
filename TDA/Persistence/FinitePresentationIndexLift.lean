import TDA.Persistence.FinitePresentationLifting

/-!
# Enlarging finite presentation index universes

Finite presentations over a module whose values live in `Type u` may be
given with finite generator and relation carriers in `Type 0`. This file
reindexes those finite carriers by `ULift` so that the presentation has
carriers in `Type u`, without changing the presented module. Conversely,
finite carriers in `Type u` are reindexed by `Fin`, so the two universe
choices for finite presentations of such a module are interchangeable.
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

/-- Reindex a finite graded generator family with carrier in `Type u` by
`Fin (Nat.card W.Carrier)`, a carrier in `Type 0`, retaining each grade. -/
noncomputable def GradedGenerators.lowerFiniteIndexUniverse
    (W : GradedGenerators.{v,u} P) [Finite W.Carrier] :
    GradedGenerators.{v,0} P where
  Carrier := Fin (Nat.card W.Carrier)
  grade := fun i => W.grade ((Finite.equivFin W.Carrier).symm i)

/-- The reindexed and original free modules are naturally isomorphic, by the
free-module lifting maps exchanging birth generators along `Finite.equivFin`. -/
noncomputable def GradedGenerators.lowerFiniteIndexUniverseIso
    (W : GradedGenerators.{v,u} P) [Finite W.Carrier] :
    module (R := R) W.lowerFiniteIndexUniverse ≅ module (R := R) W := by
  let e := Finite.equivFin W.Carrier
  let W' := W.lowerFiniteIndexUniverse
  have hgrade : ∀ g : W.Carrier, W'.grade (e g) ≤ W.grade g := fun g =>
    (congrArg W.grade (e.symm_apply_apply g)).le
  let toOld : module (R := R) W' ⟶ module (R := R) W :=
    lift (R := R) W' (module (R := R) W) (fun i => birth (R := R) W (e.symm i))
  let toLow : module (R := R) W ⟶ module (R := R) W' :=
    lift (R := R) W (module (R := R) W')
      (fun g => generator (R := R) W' (e g) (hgrade g))
  have hOld : ∀ i : W'.Carrier, (toOld.app (W'.grade i))
      (birth (R := R) W' i) = birth (R := R) W (e.symm i) := fun i =>
    lift_birth (R := R) W' (module (R := R) W)
      (fun i => birth (R := R) W (e.symm i)) i
  have hLow : ∀ i : W'.Carrier, (toLow.app (W'.grade i))
      (birth (R := R) W (e.symm i)) = birth (R := R) W' i := by
    intro i
    have hlift := lift_birth (R := R) W (module (R := R) W')
      (fun g => generator (R := R) W' (e g) (hgrade g)) (e.symm i)
    have hgen : ∀ (j : W'.Carrier) (hj : j = i)
        (h : W'.grade j ≤ W'.grade i),
        generator (R := R) W' j h = birth (R := R) W' i := by
      rintro j rfl h
      rfl
    exact hlift.trans (hgen _ (e.apply_symm_apply i) _)
  refine ⟨toOld, toLow, ?_, ?_⟩
  · apply hom_ext_birth (R := R) W'
    intro i
    change (toLow.app (W'.grade i)) ((toOld.app (W'.grade i))
      (birth (R := R) W' i)) = _
    rw [hOld, hLow, NatTrans.id_app, ModuleCat.id_apply]
  · apply hom_ext_birth (R := R) W
    intro g
    obtain ⟨i, rfl⟩ := e.symm.surjective g
    have h := congrArg (fun x => (toOld.app (W'.grade i)) x) (hLow i)
    exact h.trans (hOld i)

/-- Finite presentations with index carriers in the module universe `Type u`
can be reindexed to carriers in `Type 0`. Together with
`finitelyPresented_liftIndexUniverse`, the two universe choices for finite
presentations of a module in `PModule.{u,v,u}` are equivalent. -/
theorem finitelyPresented_lowerIndexUniverse
    (M : PModule.{u,v,u} R P)
    (hM : FinitelyPresented.{u,v,u} (R := R) (P := P) M) :
    FinitelyPresented.{u,v,0} (R := R) (P := P) M := by
  obtain ⟨D, hD, ⟨e⟩⟩ := hM
  have : Finite D.generators.Carrier := hD.1
  have : Finite D.relations.Carrier := hD.2
  let D' : Presentation.{u,v,0} (R := R) (P := P) :=
    { generators := D.generators.lowerFiniteIndexUniverse
      relations := D.relations.lowerFiniteIndexUniverse
      relationMap := D.relations.lowerFiniteIndexUniverseIso.hom ≫
        D.relationMap ≫ D.generators.lowerFiniteIndexUniverseIso.inv }
  have eD : D'.presented ≅ D.presented := by
    change cokernel D'.relationMap ≅ cokernel D.relationMap
    apply cokernel.mapIso (f := D'.relationMap) D.relationMap
      D.relations.lowerFiniteIndexUniverseIso
      D.generators.lowerFiniteIndexUniverseIso
    simp [D', Category.assoc]
  refine ⟨D', ?_, ⟨eD.trans e⟩⟩
  exact ⟨inferInstanceAs (Finite (Fin _)), inferInstanceAs (Finite (Fin _))⟩

end GradedFree

end TDA.Persistence
