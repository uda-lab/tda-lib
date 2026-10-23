import TDA.Persistence.GradedFree

/-!
# Disjoint unions of graded free modules

A free module on a disjoint union of graded families has the coproduct
universal property. The maps and their laws are stated through generators,
which also makes them usable when defining homogeneous relations.
-/

set_option autoImplicit false

universe u v w

namespace TDA.Persistence.GradedFree

open CategoryTheory

variable {R : Type u} [Ring R] {P : Type v} [Preorder P]

/-- Disjoint union, retaining each generator's grade. -/
def GradedGenerators.sum (W V : GradedGenerators.{v,w} P) : GradedGenerators.{v,w} P where
  Carrier := Sum W.Carrier V.Carrier
  grade := Sum.elim W.grade V.grade

variable (W V : GradedGenerators.{v,w} P)

/-- Include the first free family in the free module on the union. -/
noncomputable def sumInl : module (R := R) W ⟶ module (W.sum V) :=
  lift W (module (W.sum V)) (fun g => birth (W.sum V) (Sum.inl g))

/-- Include the second free family in the free module on the union. -/
noncomputable def sumInr : module (R := R) V ⟶ module (W.sum V) :=
  lift V (module (W.sum V)) (fun g => birth (W.sum V) (Sum.inr g))

@[simp] theorem sumInl_birth (g : W.Carrier) :
    (sumInl (R := R) W V).app (W.grade g) (birth W g) =
      birth (W.sum V) (Sum.inl g) :=
  lift_birth W (module (W.sum V)) _ g

@[simp] theorem sumInr_birth (g : V.Carrier) :
    (sumInr (R := R) W V).app (V.grade g) (birth V g) =
      birth (W.sum V) (Sum.inr g) :=
  lift_birth V (module (W.sum V)) _ g

/-- A pair of maps out of free families extends uniquely across their union. -/
noncomputable def sumDesc {M : PModule.{u,v,max u w} R P}
    (f : module (R := R) W ⟶ M) (g : module (R := R) V ⟶ M) :
    module (R := R) (W.sum V) ⟶ M :=
  lift (W.sum V) M (fun z => match z with
    | .inl x => f.app (W.grade x) (birth W x)
    | .inr y => g.app (V.grade y) (birth V y))

@[simp] theorem sumDesc_birth_inl {M : PModule.{u,v,max u w} R P}
    (f : module (R := R) W ⟶ M) (g : module (R := R) V ⟶ M)
    (x : W.Carrier) :
    (sumDesc W V f g).app (W.grade x) (birth (W.sum V) (Sum.inl x)) =
      f.app (W.grade x) (birth W x) :=
  lift_birth (W.sum V) M _ (Sum.inl x)

@[simp] theorem sumDesc_birth_inr {M : PModule.{u,v,max u w} R P}
    (f : module (R := R) W ⟶ M) (g : module (R := R) V ⟶ M)
    (y : V.Carrier) :
    (sumDesc W V f g).app (V.grade y) (birth (W.sum V) (Sum.inr y)) =
      g.app (V.grade y) (birth V y) :=
  lift_birth (W.sum V) M _ (Sum.inr y)

@[simp] theorem sumInl_sumDesc {M : PModule.{u,v,max u w} R P}
    (f : module (R := R) W ⟶ M) (g : module (R := R) V ⟶ M) :
    sumInl W V ≫ sumDesc W V f g = f := by
  have hleft := lift_unique W M (fun x => f.app (W.grade x) (birth W x))
    (sumInl W V ≫ sumDesc W V f g) (by intro x; simp)
  exact hleft.trans
    (lift_unique W M (fun x => f.app (W.grade x) (birth W x)) f (fun _ => rfl)).symm

@[simp] theorem sumInr_sumDesc {M : PModule.{u,v,max u w} R P}
    (f : module (R := R) W ⟶ M) (g : module (R := R) V ⟶ M) :
    sumInr W V ≫ sumDesc W V f g = g := by
  have hright := lift_unique V M (fun y => g.app (V.grade y) (birth V y))
    (sumInr W V ≫ sumDesc W V f g) (by intro y; simp)
  exact hright.trans
    (lift_unique V M (fun y => g.app (V.grade y) (birth V y)) g (fun _ => rfl)).symm

/-- The inclusion maps jointly determine a map out of a union-free module. -/
theorem sumDesc_unique {M : PModule.{u,v,max u w} R P}
    (h : module (R := R) (W.sum V) ⟶ M) :
    sumDesc W V (sumInl W V ≫ h) (sumInr W V ≫ h) = h := by
  let s := fun z : (W.sum V).Carrier =>
    h.app ((W.sum V).grade z) (birth (W.sum V) z)
  have hdesc := lift_unique (W.sum V) M s
    (sumDesc W V (sumInl W V ≫ h) (sumInr W V ≫ h)) (by
      intro z
      cases z with
      | inl x =>
        change (sumDesc W V (sumInl W V ≫ h) (sumInr W V ≫ h)).app
          (W.grade x) (birth (W.sum V) (Sum.inl x)) =
            h.app (W.grade x) (birth (W.sum V) (Sum.inl x))
        rw [sumDesc_birth_inl]
        change h.app (W.grade x) ((sumInl W V).app (W.grade x) (birth W x)) = _
        rw [sumInl_birth]
      | inr y =>
        change (sumDesc W V (sumInl W V ≫ h) (sumInr W V ≫ h)).app
          (V.grade y) (birth (W.sum V) (Sum.inr y)) =
            h.app (V.grade y) (birth (W.sum V) (Sum.inr y))
        rw [sumDesc_birth_inr]
        change h.app (V.grade y) ((sumInr W V).app (V.grade y) (birth V y)) = _
        rw [sumInr_birth])
  exact hdesc.trans (lift_unique (W.sum V) M s h (fun _ => rfl)).symm

/-- Equality of maps out of the sum-free module reduces to both families. -/
theorem sumHom_ext {M : PModule.{u,v,max u w} R P}
    {f g : module (R := R) (W.sum V) ⟶ M}
    (hW : sumInl W V ≫ f = sumInl W V ≫ g)
    (hV : sumInr W V ≫ f = sumInr W V ≫ g) : f = g := by
  calc
    f = sumDesc W V (sumInl W V ≫ f) (sumInr W V ≫ f) :=
      (sumDesc_unique W V f).symm
    _ = sumDesc W V (sumInl W V ≫ g) (sumInr W V ≫ g) := by rw [hW, hV]
    _ = g := sumDesc_unique W V g

/-- Hom maps from the union-free module are exactly pairs of Hom maps from
its two summands. -/
noncomputable def sumHomEquiv (M : PModule.{u,v,max u w} R P) :
    (module (R := R) (W.sum V) ⟶ M) ≃
      ((module (R := R) W ⟶ M) × (module (R := R) V ⟶ M)) where
  toFun h := (sumInl W V ≫ h, sumInr W V ≫ h)
  invFun p := sumDesc W V p.1 p.2
  left_inv := sumDesc_unique W V
  right_inv := by
    intro p
    cases p
    simp

end TDA.Persistence.GradedFree
