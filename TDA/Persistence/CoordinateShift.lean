import TDA.Persistence.RealCoordinates
import Mathlib.Data.NNReal.Basic

/-!
# Diagonal shifts of real-coordinate persistence modules

The shift by a finite nonnegative parameter evaluates a module at
`a + ε · 1`. Canonical isomorphisms identify zero and successive shifts;
transitions are the original structure maps. The coefficient ring and the
module-carrier universe are independent, and `n = 0` is allowed.
-/

set_option autoImplicit false

universe u w

namespace TDA.Persistence

open CategoryTheory
open scoped TDA.Persistence NNReal

namespace CoordinateShift

variable {R : Type u} [Ring R] {n : ℕ}

/-- Translate every real coordinate by the same nonnegative parameter. -/
def translation (ε : ℝ≥0) : (Fin n → ℝ) →o (Fin n → ℝ) where
  toFun a := fun i => a i + (ε : ℝ)
  monotone' a b h i := by
    change a i + (ε : ℝ) ≤ b i + (ε : ℝ)
    exact add_le_add (h i) le_rfl

@[simp] theorem translation_apply (ε : ℝ≥0) (a : Fin n → ℝ) (i : Fin n) :
    translation ε a i = a i + (ε : ℝ) := rfl

/-- The diagonal shift functor, including its action on natural transformations. -/
def shift (ε : ℝ≥0) :
    PModule.{u,0,w} R (Fin n → ℝ) ⥤ PModule.{u,0,w} R (Fin n → ℝ) where
  obj M := reindex (translation ε) M
  map f := reindexNatTrans (translation ε) f

@[simp] theorem shift_obj (ε : ℝ≥0) (M : PModule.{u,0,w} R (Fin n → ℝ))
    (a : Fin n → ℝ) : ((shift ε).obj M).obj a = M.obj (translation ε a) := rfl

@[simp] theorem shift_map_app (ε : ℝ≥0)
    {M N : PModule.{u,0,w} R (Fin n → ℝ)} (f : M ⟶ N) (a : Fin n → ℝ) :
    ((shift ε).map f).app a = f.app (translation ε a) := rfl

theorem shift_structureMap (ε : ℝ≥0) (M : PModule.{u,0,w} R (Fin n → ℝ))
    {a b : Fin n → ℝ} (h : a ≤ b) :
    structureMap ((shift ε).obj M) h = structureMap M ((translation ε).monotone' h) := rfl

private def reindexIso {a b : (Fin n → ℝ) →o (Fin n → ℝ)}
    (h : ∀ p, a p = b p) (M : PModule.{u,0,w} R (Fin n → ℝ)) :
    reindex a M ≅ reindex b M :=
  Functor.isoWhiskerRight
    (NatIso.ofComponents (fun p => eqToIso (h p)) (by intros; apply Subsingleton.elim)) M

/-- The zero shift is canonically the original module. -/
def zeroIso (M : PModule.{u,0,w} R (Fin n → ℝ)) : (shift 0).obj M ≅ M :=
  reindexIso (a := translation 0) (b := OrderHom.id) (fun p => by
    funext i
    simp) M

/-- Two successive shifts agree with translation by their sum. -/
def compIso (ε δ : ℝ≥0) (M : PModule.{u,0,w} R (Fin n → ℝ)) :
    (shift ε).obj ((shift δ).obj M) ≅ (shift (ε + δ)).obj M :=
  reindexIso (a := (translation δ).comp (translation ε))
    (b := translation (ε + δ)) (fun p => by
      funext i
      simp [add_assoc]) M

@[simp] theorem zeroIso_hom_app (M : PModule.{u,0,w} R (Fin n → ℝ))
    (a : Fin n → ℝ) :
    (zeroIso M).hom.app a = M.map (eqToHom (show translation 0 a = a by
      funext i; simp)) := rfl

@[simp] theorem zeroIso_inv_app (M : PModule.{u,0,w} R (Fin n → ℝ))
    (a : Fin n → ℝ) :
    (zeroIso M).inv.app a = M.map (eqToHom (show translation 0 a = a by
      funext i; simp).symm) := rfl

@[simp] theorem compIso_hom_app (ε δ : ℝ≥0)
    (M : PModule.{u,0,w} R (Fin n → ℝ)) (a : Fin n → ℝ) :
    (compIso ε δ M).hom.app a = M.map (eqToHom
      (show translation δ (translation ε a) = translation (ε + δ) a by
        funext i; simp [add_assoc])) := rfl

/-- The zero-shift identification is natural in the module. -/
@[reassoc] theorem zeroIso_naturality
    {M N : PModule.{u,0,w} R (Fin n → ℝ)} (f : M ⟶ N) :
    (shift 0).map f ≫ (zeroIso N).hom = (zeroIso M).hom ≫ f := by
  apply NatTrans.ext
  funext a
  exact (f.naturality (eqToHom (show translation 0 a = a by funext i; simp))).symm

@[reassoc] theorem zeroIso_inv_naturality
    {M N : PModule.{u,0,w} R (Fin n → ℝ)} (f : M ⟶ N) :
    (zeroIso M).inv ≫ (shift 0).map f = f ≫ (zeroIso N).inv := by
  apply NatTrans.ext
  funext a
  exact f.naturality (eqToHom (show translation 0 a = a by funext i; simp).symm)

/-- Shift composition identification is natural in the module. -/
theorem compIso_naturality (ε δ : ℝ≥0)
    {M N : PModule.{u,0,w} R (Fin n → ℝ)} (f : M ⟶ N) :
    (shift ε).map ((shift δ).map f) ≫ (compIso ε δ N).hom =
      (compIso ε δ M).hom ≫ (shift (ε + δ)).map f := by
  apply NatTrans.ext
  funext a
  exact (f.naturality _).symm

/-- Transport equal shift parameters without choosing an arbitrary comparison. -/
def congrIso {ε δ : ℝ≥0} (h : ε = δ)
    (M : PModule.{u,0,w} R (Fin n → ℝ)) :
    (shift ε).obj M ≅ (shift δ).obj M :=
  reindexIso (fun p => congrArg (fun e : ℝ≥0 => translation e p) h) M

@[simp] theorem congrIso_hom_app {ε δ : ℝ≥0} (h : ε = δ)
    (M : PModule.{u,0,w} R (Fin n → ℝ)) (a : Fin n → ℝ) :
    (congrIso h M).hom.app a =
      M.map (eqToHom (congrArg (fun e : ℝ≥0 => translation e a) h)) := rfl

@[simp] theorem congrIso_refl (ε : ℝ≥0)
    (M : PModule.{u,0,w} R (Fin n → ℝ)) :
    congrIso (rfl : ε = ε) M = Iso.refl _ := by
  apply Iso.ext
  apply NatTrans.ext
  funext a
  exact M.map_id _

/-- Left unit coherence for shift composition. -/
@[reassoc] theorem compIso_zero_left (ε : ℝ≥0)
    (M : PModule.{u,0,w} R (Fin n → ℝ)) :
    (compIso 0 ε M).hom ≫ (congrIso (zero_add ε) M).hom =
      (zeroIso ((shift ε).obj M)).hom := by
  apply NatTrans.ext
  funext a
  change M.map _ ≫ M.map _ = M.map _
  rw [← M.map_comp]
  congr 1

/-- Right unit coherence for shift composition. -/
theorem compIso_zero_right (ε : ℝ≥0)
    (M : PModule.{u,0,w} R (Fin n → ℝ)) :
    (compIso ε 0 M).hom ≫ (congrIso (add_zero ε) M).hom =
      (shift ε).map (zeroIso M).hom := by
  apply NatTrans.ext
  funext a
  change M.map _ ≫ M.map _ = M.map _
  rw [← M.map_comp]
  congr 1

/-- The two parenthesizations of three shifts agree. -/
theorem compIso_assoc (ε δ γ : ℝ≥0)
    (M : PModule.{u,0,w} R (Fin n → ℝ)) :
    (compIso ε δ ((shift γ).obj M)).hom ≫ (compIso (ε + δ) γ M).hom =
      (shift ε).map (compIso δ γ M).hom ≫ (compIso ε (δ + γ) M).hom ≫
        (congrIso (add_assoc ε δ γ).symm M).hom := by
  apply NatTrans.ext
  funext a
  change M.map _ ≫ M.map _ = M.map _ ≫ M.map _ ≫ M.map _
  erw [← M.map_comp, ← M.map_comp, ← M.map_comp]
  congr 1

/-- The transition is the natural transformation of forward structure maps. -/
def transition (ε : ℝ≥0) (M : PModule.{u,0,w} R (Fin n → ℝ)) :
    M ⟶ (shift ε).obj M where
  app a := structureMap M (show a ≤ translation ε a from fun i => by
    change a i ≤ a i + (ε : ℝ)
    exact le_add_of_nonneg_right ε.coe_nonneg)
  naturality _ _ f := by
    change M.map f ≫ M.map _ = M.map _ ≫ M.map _
    rw [← M.map_comp, ← M.map_comp]
    congr 1

@[simp] theorem transition_app (ε : ℝ≥0)
    (M : PModule.{u,0,w} R (Fin n → ℝ)) (a : Fin n → ℝ) :
    (transition ε M).app a = structureMap M
      (show a ≤ translation ε a from fun i => by
        change a i ≤ a i + (ε : ℝ)
        exact le_add_of_nonneg_right ε.coe_nonneg) := rfl

theorem transition_naturality (ε : ℝ≥0)
    {M N : PModule.{u,0,w} R (Fin n → ℝ)} (f : M ⟶ N) :
    f ≫ transition ε N = transition ε M ≫ (shift ε).map f := by
  apply NatTrans.ext
  funext a
  change f.app a ≫ N.map _ = M.map _ ≫ f.app (translation ε a)
  exact (f.naturality _).symm

/-- Increasing the parameter gives the structure maps between shifted indices. -/
def shiftLE {ε δ : ℝ≥0} (h : ε ≤ δ)
    (M : PModule.{u,0,w} R (Fin n → ℝ)) :
    (shift ε).obj M ⟶ (shift δ).obj M where
  app a := structureMap M (show translation ε a ≤ translation δ a from fun i => by
    change a i + (ε : ℝ) ≤ a i + (δ : ℝ)
    exact add_le_add le_rfl h)
  naturality _ _ f := by
    change M.map _ ≫ M.map _ = M.map _ ≫ M.map _
    rw [← M.map_comp, ← M.map_comp]
    congr 1

@[simp] theorem shiftLE_app {ε δ : ℝ≥0} (h : ε ≤ δ)
    (M : PModule.{u,0,w} R (Fin n → ℝ)) (a : Fin n → ℝ) :
    (shiftLE h M).app a = structureMap M
      (show translation ε a ≤ translation δ a from fun i => by
        change a i + (ε : ℝ) ≤ a i + (δ : ℝ)
        exact add_le_add le_rfl h) := rfl

/-- At zero, the transition followed by the canonical unit is the identity. -/
theorem transition_zero (M : PModule.{u,0,w} R (Fin n → ℝ)) :
    transition 0 M ≫ (zeroIso M).hom = 𝟙 M := by
  apply NatTrans.ext
  funext a
  change M.map _ ≫ M.map _ = 𝟙 _
  erw [← M.map_comp]
  exact (congrArg M.map (Subsingleton.elim _ (𝟙 a))).trans (M.map_id a)

theorem transition_zero_eq (M : PModule.{u,0,w} R (Fin n → ℝ)) :
    transition 0 M = (zeroIso M).inv := by
  apply (cancel_mono (zeroIso M).hom).mp
  rw [transition_zero, Iso.inv_hom_id]

theorem transition_congr {ε δ : ℝ≥0} (h : ε = δ)
    (M : PModule.{u,0,w} R (Fin n → ℝ)) :
    transition ε M ≫ (congrIso h M).hom = transition δ M := by
  cases h
  simp only [congrIso_refl, Iso.refl_hom, Category.comp_id]

/-- Successive transitions equal the transition by the sum. -/
theorem transition_add (ε δ : ℝ≥0)
    (M : PModule.{u,0,w} R (Fin n → ℝ)) :
    transition ε M ≫ (shift ε).map (transition δ M) ≫
      (compIso ε δ M).hom = transition (ε + δ) M := by
  apply NatTrans.ext
  funext a
  change M.map _ ≫ M.map _ ≫ M.map _ = M.map _
  erw [← M.map_comp, ← M.map_comp]
  congr 1

end CoordinateShift
end TDA.Persistence
