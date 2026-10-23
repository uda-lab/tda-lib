import TDA.Persistence.GradedFree
import TDA.Persistence.CoordinateShift

/-!
# Shifting graded free persistence modules

Shifting grades by `σ` means subtracting `σ` from every coordinate. Thus a
positive `ε` gives the free module evaluated `ε` later, while `W(-ε)` has
grades increased by `ε`. This is the sign convention of Lesnick §4.1.5.
-/

set_option autoImplicit false

universe u w

namespace TDA.Persistence.GradedFree

open CategoryTheory
open scoped TDA.Persistence NNReal

variable {R : Type u} [Ring R] {n : ℕ}

/-- Shift a graded family by subtracting `σ` from each birth coordinate. -/
def GradedGenerators.shiftGrade (W : GradedGenerators.{0,w} (Fin n → ℝ))
    (σ : ℝ) : GradedGenerators.{0,w} (Fin n → ℝ) where
  Carrier := W.Carrier
  grade g := fun i => W.grade g i - σ

@[simp] theorem GradedGenerators.shiftGrade_grade
    (W : GradedGenerators.{0,w} (Fin n → ℝ)) (σ : ℝ)
    (g : W.Carrier) (i : Fin n) : (W.shiftGrade σ).grade g i = W.grade g i - σ := rfl

/-- `W(-ε)` is born `ε` later, as required by the cross-presentation convention. -/
@[simp] theorem GradedGenerators.shiftGrade_neg_grade
    (W : GradedGenerators.{0,w} (Fin n → ℝ)) (ε : ℝ≥0)
    (g : W.Carrier) (i : Fin n) :
    (W.shiftGrade (-(ε : ℝ))).grade g i = W.grade g i + (ε : ℝ) := by
  simp [GradedGenerators.shiftGrade_grade]

/-- At grade `a`, the shifted free fiber and the old fiber at `a + ε` have
exactly the same supported finitely supported functions. -/
theorem fiber_shiftGrade_eq (W : GradedGenerators.{0,w} (Fin n → ℝ))
    (ε : ℝ≥0) (a : Fin n → ℝ) :
    fiber (R := R) (W.shiftGrade (ε : ℝ)) a =
      fiber (R := R) W (CoordinateShift.translation ε a) := by
  unfold fiber
  congr 1
  ext g
  change (∀ i, W.grade g i - (ε : ℝ) ≤ a i) ↔
    (∀ i, W.grade g i ≤ a i + (ε : ℝ))
  simp only [sub_le_iff_le_add]

/-- The shifted free module is naturally isomorphic to shifting the free
module itself. Each component is inclusion along equality of support. -/
noncomputable def shiftIso (ε : ℝ≥0) (W : GradedGenerators.{0,w} (Fin n → ℝ)) :
    module (R := R) (W.shiftGrade (ε : ℝ)) ≅
      (CoordinateShift.shift ε).obj (module (R := R) W) where
  hom := {
    app a := ModuleCat.ofHom (Submodule.inclusion (fiber_shiftGrade_eq (R := R) W ε a).le)
    naturality a b f := by
      apply ModuleCat.hom_ext
      rfl }
  inv := {
    app a := ModuleCat.ofHom (Submodule.inclusion (fiber_shiftGrade_eq (R := R) W ε a).ge)
    naturality a b f := by
      apply ModuleCat.hom_ext
      rfl }
  hom_inv_id := by
    apply NatTrans.ext
    funext a
    apply ModuleCat.hom_ext
    rfl
  inv_hom_id := by
    apply NatTrans.ext
    funext a
    apply ModuleCat.hom_ext
    rfl

/-- The free-shift identification leaves the underlying basis combination intact. -/
@[simp] theorem shiftIso_hom_val (W : GradedGenerators.{0,w} (Fin n → ℝ))
    (ε : ℝ≥0) (a : Fin n → ℝ)
    (x : (module (R := R) (W.shiftGrade (ε : ℝ))).obj a) :
    (((shiftIso (R := R) ε W).hom.app a).hom x :
      fiber (R := R) W (CoordinateShift.translation ε a)).val = x.val := rfl

/-- The free-shift isomorphism sends each available basis vector to the
corresponding basis vector of the translated fiber. -/
theorem shiftIso_generator (W : GradedGenerators.{0,w} (Fin n → ℝ))
    (ε : ℝ≥0) (a : Fin n → ℝ) (g : W.Carrier)
    (h : (W.shiftGrade (ε : ℝ)).grade g ≤ a) :
    ((shiftIso (R := R) ε W).hom.app a).hom
        (generator (R := R) (W.shiftGrade (ε : ℝ)) g h) =
      generator (R := R) W g (by
        intro i
        exact (sub_le_iff_le_add).mp (h i)) := by
  apply Subtype.ext
  rfl

/-- The standard transition of a free module is inclusion on supported combinations. -/
@[simp] theorem transition_val (W : GradedGenerators.{0,w} (Fin n → ℝ))
    (ε : ℝ≥0) (a : Fin n → ℝ) (x : (module (R := R) W).obj a) :
    (((CoordinateShift.transition ε (module (R := R) W)).app a).hom x :
      fiber (R := R) W (CoordinateShift.translation ε a)).val = x.val := rfl

/-- Delaying every birth by `ε` gives a submodule of the original free module
at each fixed grade. This is the standard inclusion for `W(-ε)`. -/
theorem delayed_fiber_le (W : GradedGenerators.{0,w} (Fin n → ℝ))
    (ε : ℝ≥0) (a : Fin n → ℝ) :
    fiber (R := R) (W.shiftGrade (-(ε : ℝ))) a ≤ fiber (R := R) W a := by
  intro x hx g hg i
  have h : W.grade g i + (ε : ℝ) ≤ a i := by
    simpa only [GradedGenerators.shiftGrade_neg_grade] using hx hg i
  exact (le_add_of_nonneg_right ε.coe_nonneg).trans h

/-- The canonical natural inclusion of the delayed family `W(-ε)` into `W`. -/
noncomputable def delayedInclusion (ε : ℝ≥0) (W : GradedGenerators.{0,w} (Fin n → ℝ)) :
    module (R := R) (W.shiftGrade (-(ε : ℝ))) ⟶ module (R := R) W where
  app a := ModuleCat.ofHom (Submodule.inclusion (delayed_fiber_le (R := R) W ε a))
  naturality a b f := by
    apply ModuleCat.hom_ext
    rfl

/-- The delayed inclusion retains the same basis vector at its later birth. -/
@[simp] theorem delayedInclusion_birth_val
    (W : GradedGenerators.{0,w} (Fin n → ℝ)) (ε : ℝ≥0)
    (g : W.Carrier) :
    (((delayedInclusion (R := R) ε W).app
      ((W.shiftGrade (-(ε : ℝ))).grade g)).hom
        (birth (R := R) (W.shiftGrade (-(ε : ℝ))) g) :
      fiber (R := R) W ((W.shiftGrade (-(ε : ℝ))).grade g)).val =
        Finsupp.single g 1 := rfl

/-- Delaying births does not change the basis vector used by the inclusion. -/
theorem delayedInclusion_generator
    (W : GradedGenerators.{0,w} (Fin n → ℝ)) (ε : ℝ≥0)
    (a : Fin n → ℝ) (g : W.Carrier)
    (h : (W.shiftGrade (-(ε : ℝ))).grade g ≤ a) :
    ((delayedInclusion (R := R) ε W).app a).hom
        (generator (R := R) (W.shiftGrade (-(ε : ℝ))) g h) =
      generator (R := R) W g (by
        intro i
        have hi : W.grade g i + (ε : ℝ) ≤ a i := by
          simpa only [GradedGenerators.shiftGrade_neg_grade] using h i
        exact (le_add_of_nonneg_right ε.coe_nonneg).trans hi) := by
  apply Subtype.ext
  rfl

end TDA.Persistence.GradedFree
