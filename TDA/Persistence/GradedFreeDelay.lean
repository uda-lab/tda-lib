import TDA.Persistence.CrossPresentation

/-!
# Free modules with delayed births

The free module on `W` is the shift by `ε` of the free module whose births
are delayed by `ε`. This canonical identification relates maps defined at
the original births to maps defined at the delayed births.
-/

set_option autoImplicit false

universe u w

namespace TDA.Persistence.GradedFree

open CategoryTheory
open scoped TDA.Persistence NNReal

variable {R : Type u} [Ring R] {n : ℕ}

private theorem delayed_shift_fiber_eq (ε : ℝ≥0)
    (W : GradedGenerators.{0,w} (Fin n → ℝ)) (a : Fin n → ℝ) :
    fiber (R := R) W a =
      fiber (R := R) (W.shiftGrade (-(ε : ℝ))) (CoordinateShift.translation ε a) := by
  unfold fiber
  congr 1
  ext g
  change (∀ i, W.grade g i ≤ a i) ↔
    (∀ i, W.grade g i - -(ε : ℝ) ≤ a i + (ε : ℝ))
  simp

/-- Delaying births and then shifting the free module recovers the original. -/
noncomputable def delayedShiftIso (ε : ℝ≥0)
    (W : GradedGenerators.{0,w} (Fin n → ℝ)) :
    module (R := R) W ≅
      (CoordinateShift.shift ε).obj (module (W.shiftGrade (-(ε : ℝ)))) where
  hom := {
    app a := ModuleCat.ofHom (Submodule.inclusion (delayed_shift_fiber_eq ε W a).le)
    naturality a b f := by apply ModuleCat.hom_ext; rfl }
  inv := {
    app a := ModuleCat.ofHom (Submodule.inclusion (delayed_shift_fiber_eq ε W a).ge)
    naturality a b f := by apply ModuleCat.hom_ext; rfl }
  hom_inv_id := by apply NatTrans.ext; funext a; apply ModuleCat.hom_ext; rfl
  inv_hom_id := by apply NatTrans.ext; funext a; apply ModuleCat.hom_ext; rfl

/-- The delayed birth map recovers the supplied shifted map under the canonical
free-shift identification. -/
theorem delayedShiftIso_delaySource (ε : ℝ≥0)
    (W : GradedGenerators.{0,w} (Fin n → ℝ))
    (M : PModule.{u,0,max u w} R (Fin n → ℝ))
    (f : module (R := R) W ⟶ (CoordinateShift.shift ε).obj M) :
    (delayedShiftIso (R := R) ε W).hom ≫
      (CoordinateShift.shift ε).map (delaySource ε W M f) = f := by
  apply hom_ext_birth W
  intro g
  let t := W.grade g
  let d := (W.shiftGrade (-(ε : ℝ))).grade g
  have e : d = CoordinateShift.translation ε t := by funext i; simp [d, t]
  have hx : (delayedShiftIso (R := R) ε W).hom.app t (birth W g) =
      (module (R := R) (W.shiftGrade (-(ε : ℝ)))).map (eqToHom e)
        (birth (W.shiftGrade (-(ε : ℝ))) g) := by apply Subtype.ext; rfl
  change (delaySource ε W M f).app (CoordinateShift.translation ε t)
    ((delayedShiftIso (R := R) ε W).hom.app t (birth W g)) = f.app t (birth W g)
  rw [hx]
  have hn := (delaySource ε W M f).naturality (eqToHom e)
  have hv := congrArg (fun q => q (birth (W.shiftGrade (-(ε : ℝ))) g)) hn
  change (delaySource ε W M f).app (CoordinateShift.translation ε t)
      ((module (R := R) (W.shiftGrade (-(ε : ℝ)))).map (eqToHom e)
        (birth (W.shiftGrade (-(ε : ℝ))) g)) =
    M.map (eqToHom e) ((delaySource ε W M f).app d
      (birth (W.shiftGrade (-(ε : ℝ))) g)) at hv
  rw [hv, delaySource_birth]
  change M.map (eqToHom e) (M.map (eqToHom e.symm) (f.app t (birth W g))) = _
  calc
    _ = M.map (eqToHom e.symm ≫ eqToHom e) (f.app t (birth W g)) := by
      rw [Functor.map_comp]
      rfl
    _ = _ := by simp

private theorem shift_map_injective (ε : ℝ≥0)
    {M N : PModule.{u,0,w} R (Fin n → ℝ)} :
    Function.Injective (fun f : M ⟶ N => (CoordinateShift.shift ε).map f) := by
  intro f g h
  apply NatTrans.ext
  funext a
  obtain ⟨b, hb⟩ : ∃ b, CoordinateShift.translation ε b = a :=
    ⟨fun i => a i - (ε : ℝ), by funext i; simp⟩
  subst a
  exact congrArg (fun q => q.app b) h

/-- Maps from a delayed free family agree when their shifted maps agree. -/
theorem delayedShiftIso_postcomp_injective (ε : ℝ≥0)
    (W : GradedGenerators.{0,w} (Fin n → ℝ))
    (M : PModule.{u,0,max u w} R (Fin n → ℝ)) :
    Function.Injective (fun f : module (R := R) (W.shiftGrade (-(ε : ℝ))) ⟶ M =>
      (delayedShiftIso ε W).hom ≫ (CoordinateShift.shift ε).map f) := by
  intro f g h
  exact shift_map_injective ε ((cancel_epi (delayedShiftIso (R := R) ε W).hom).mp h)

/-- A delayed free generator can advance into the shifted original free module. -/
noncomputable def delayedAdvance (ε : ℝ≥0)
    (W : GradedGenerators.{0,w} (Fin n → ℝ)) :
    module (R := R) (W.shiftGrade (-(ε : ℝ))) ⟶
      (CoordinateShift.shift ε).obj (module W) :=
  delayedInclusion ε W ≫ CoordinateShift.transition ε (module W)

/-- The canonical free maps compose to the double transition. -/
theorem delayedShiftIso_advance (ε : ℝ≥0)
    (W : GradedGenerators.{0,w} (Fin n → ℝ)) :
    (delayedShiftIso (R := R) ε W).hom ≫
      (CoordinateShift.shift ε).map (delayedAdvance ε W) ≫
      (CoordinateShift.compIso ε ε (module W)).hom =
        CoordinateShift.transition (ε + ε) (module W) := by
  apply NatTrans.ext
  funext a
  apply ModuleCat.hom_ext
  rfl

theorem sumInl_crossFreeLR (ε : ℝ≥0)
    (W V : GradedGenerators.{0,w} (Fin n → ℝ)) :
    sumInl W (V.shiftGrade (-(ε : ℝ))) ≫ crossFreeLR (R := R) ε W V =
      (delayedShiftIso ε W).hom ≫
        (CoordinateShift.shift ε).map (sumInl (W.shiftGrade (-(ε : ℝ))) V) := by
  apply hom_ext_birth W
  intro g
  change (crossFreeLR (R := R) ε W V).app (W.grade g)
      ((sumInl W (V.shiftGrade (-(ε : ℝ)))).app (W.grade g) (birth W g)) =
    (sumInl (W.shiftGrade (-(ε : ℝ))) V).app
      (CoordinateShift.translation ε (W.grade g))
      ((delayedShiftIso ε W).hom.app (W.grade g) (birth W g))
  rw [sumInl_birth]
  have hx : (delayedShiftIso (R := R) ε W).hom.app (W.grade g) (birth W g) =
      generator (W.shiftGrade (-(ε : ℝ))) g (by intro i; simp) := by
    apply Subtype.ext
    rfl
  rw [hx]
  exact (sumInl_generator (R := R) (W.shiftGrade (-(ε : ℝ))) V g
    (by intro i; simp)).symm

theorem sumInr_crossFreeLR (ε : ℝ≥0)
    (W V : GradedGenerators.{0,w} (Fin n → ℝ)) :
    sumInr W (V.shiftGrade (-(ε : ℝ))) ≫ crossFreeLR (R := R) ε W V =
      delayedAdvance ε V ≫
        (CoordinateShift.shift ε).map (sumInr (W.shiftGrade (-(ε : ℝ))) V) := by
  apply hom_ext_birth (V.shiftGrade (-(ε : ℝ)))
  intro g
  let a := (V.shiftGrade (-(ε : ℝ))).grade g
  change (crossFreeLR (R := R) ε W V).app a
      ((sumInr W (V.shiftGrade (-(ε : ℝ)))).app a
        (birth (V.shiftGrade (-(ε : ℝ))) g)) =
    (sumInr (W.shiftGrade (-(ε : ℝ))) V).app (CoordinateShift.translation ε a)
      ((delayedAdvance ε V).app a (birth (V.shiftGrade (-(ε : ℝ))) g))
  rw [sumInr_birth]
  have hx : (delayedAdvance (R := R) ε V).app a
      (birth (V.shiftGrade (-(ε : ℝ))) g) =
      generator V g (by
        intro i
        change V.grade g i ≤ (V.grade g i - -(ε : ℝ)) + (ε : ℝ)
        linarith [ε.coe_nonneg]) := by apply Subtype.ext; rfl
  rw [hx]
  exact (sumInr_generator (R := R) (W.shiftGrade (-(ε : ℝ))) V g
    (by intro i; change V.grade g i ≤ (V.grade g i - -(ε : ℝ)) + (ε : ℝ)
        linarith [ε.coe_nonneg])).symm

theorem sumInl_crossFreeRL (ε : ℝ≥0)
    (W V : GradedGenerators.{0,w} (Fin n → ℝ)) :
    sumInl (W.shiftGrade (-(ε : ℝ))) V ≫ crossFreeRL (R := R) ε W V =
      delayedAdvance ε W ≫
        (CoordinateShift.shift ε).map (sumInl W (V.shiftGrade (-(ε : ℝ)))) := by
  apply hom_ext_birth (W.shiftGrade (-(ε : ℝ)))
  intro g
  let a := (W.shiftGrade (-(ε : ℝ))).grade g
  change (crossFreeRL (R := R) ε W V).app a
      ((sumInl (W.shiftGrade (-(ε : ℝ))) V).app a
        (birth (W.shiftGrade (-(ε : ℝ))) g)) =
    (sumInl W (V.shiftGrade (-(ε : ℝ)))).app (CoordinateShift.translation ε a)
      ((delayedAdvance ε W).app a (birth (W.shiftGrade (-(ε : ℝ))) g))
  rw [sumInl_birth]
  have hx : (delayedAdvance (R := R) ε W).app a
      (birth (W.shiftGrade (-(ε : ℝ))) g) =
      generator W g (by
        intro i
        change W.grade g i ≤ (W.grade g i - -(ε : ℝ)) + (ε : ℝ)
        linarith [ε.coe_nonneg]) := by apply Subtype.ext; rfl
  rw [hx]
  exact (sumInl_generator (R := R) W (V.shiftGrade (-(ε : ℝ))) g
    (by intro i; change W.grade g i ≤ (W.grade g i - -(ε : ℝ)) + (ε : ℝ)
        linarith [ε.coe_nonneg])).symm

theorem sumInr_crossFreeRL (ε : ℝ≥0)
    (W V : GradedGenerators.{0,w} (Fin n → ℝ)) :
    sumInr (W.shiftGrade (-(ε : ℝ))) V ≫ crossFreeRL (R := R) ε W V =
      (delayedShiftIso ε V).hom ≫
        (CoordinateShift.shift ε).map (sumInr W (V.shiftGrade (-(ε : ℝ)))) := by
  apply hom_ext_birth V
  intro g
  change (crossFreeRL (R := R) ε W V).app (V.grade g)
      ((sumInr (W.shiftGrade (-(ε : ℝ))) V).app (V.grade g) (birth V g)) =
    (sumInr W (V.shiftGrade (-(ε : ℝ)))).app
      (CoordinateShift.translation ε (V.grade g))
      ((delayedShiftIso ε V).hom.app (V.grade g) (birth V g))
  rw [sumInr_birth]
  have hx : (delayedShiftIso (R := R) ε V).hom.app (V.grade g) (birth V g) =
      generator (V.shiftGrade (-(ε : ℝ))) g (by intro i; simp) := by
    apply Subtype.ext
    rfl
  rw [hx]
  exact (sumInr_generator (R := R) W (V.shiftGrade (-(ε : ℝ))) g
    (by intro i; simp)).symm

/-- The double-shift interleaving law makes the corresponding delayed graph
relation redundant after composition with the other interleaving map. -/
theorem delaySource_comp_interleaving {ε : ℝ≥0}
    {M N : PModule.{u,0,max u w} R (Fin n → ℝ)}
    (i : CoordinateInterleaving ε M N)
    (W : GradedGenerators.{0,w} (Fin n → ℝ)) (b : module (R := R) W ⟶ N) :
    delaySource ε W M (b ≫ i.ψ) ≫ i.φ =
      delayedAdvance ε W ≫ (CoordinateShift.shift ε).map b := by
  apply delayedShiftIso_postcomp_injective ε W ((CoordinateShift.shift ε).obj N)
  apply (cancel_mono (CoordinateShift.compIso ε ε N).hom).mp
  calc
    _ = b ≫ (i.ψ ≫ (CoordinateShift.shift ε).map i.φ ≫
        (CoordinateShift.compIso ε ε N).hom) := by
      simp only [Functor.map_comp, ← Category.assoc, delayedShiftIso_delaySource]
    _ = b ≫ CoordinateShift.transition (ε + ε) N := by rw [i.ψ_φ]
    _ = CoordinateShift.transition (ε + ε) (module W) ≫
        (CoordinateShift.shift (ε + ε)).map b :=
      CoordinateShift.transition_naturality (ε + ε) b
    _ = (delayedShiftIso ε W).hom ≫
        (CoordinateShift.shift ε).map (delayedAdvance ε W) ≫
        (CoordinateShift.compIso ε ε (module W)).hom ≫
        (CoordinateShift.shift (ε + ε)).map b := by
      rw [← delayedShiftIso_advance ε W]
      simp only [Category.assoc]
    _ = _ := by
      simp only [Functor.map_comp, Category.assoc, CoordinateShift.compIso_naturality]

/-- A delayed relation vanishes after a map exactly when its original shifted
relation vanishes after the shifted map. -/
theorem delaySource_comp_zero_iff (ε : ℝ≥0)
    (W : GradedGenerators.{0,w} (Fin n → ℝ))
    {M N : PModule.{u,0,max u w} R (Fin n → ℝ)}
    (f : module (R := R) W ⟶ (CoordinateShift.shift ε).obj M) (ρ : M ⟶ N) :
    delaySource ε W M f ≫ ρ = 0 ↔ f ≫ (CoordinateShift.shift ε).map ρ = 0 := by
  constructor
  · exact delaySource_comp_zero ε W f ρ
  · intro h
    apply delayedShiftIso_postcomp_injective ε W N
    dsimp only
    have hz : (delayedShiftIso (R := R) ε W).hom ≫
        (CoordinateShift.shift ε).map
          (0 : module (R := R) (W.shiftGrade (-(ε : ℝ))) ⟶ N) = 0 := by
      apply NatTrans.ext
      funext a
      rfl
    rw [hz]
    simpa only [Functor.map_comp, ← Category.assoc, delayedShiftIso_delaySource] using h

end TDA.Persistence.GradedFree
