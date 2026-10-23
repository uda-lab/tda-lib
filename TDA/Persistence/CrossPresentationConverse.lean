import TDA.Persistence.GradedFreeDelay
import TDA.Persistence.FinitePresentationRedundant

/-!
# Constructing cross-presentations from interleavings

The interleaving maps assign values to delayed generators. Free lifts of
these values give homogeneous graph relations. The two interleaving laws
make the opposite delayed graph relations redundant in the quotients.
-/

set_option autoImplicit false

universe u w

namespace TDA.Persistence.GradedFree

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
open scoped TDA.Persistence NNReal


variable {R : Type u} [Ring R] {n : ℕ} {ε : ℝ≥0}
  {M N : PModule.{u,0,max u w} R (Fin n → ℝ)}

private noncomputable abbrev collapseLeft
    (i : CoordinateInterleaving ε M N)
    (W V : GradedGenerators.{0,w} (Fin n → ℝ))
    (a : module (R := R) W ⟶ M) (b : module (R := R) V ⟶ N) :
    module (R := R) (crossLeft ε W V) ⟶ M :=
  sumDesc W (V.shiftGrade (-(ε : ℝ))) a (delaySource ε V M (b ≫ i.ψ))

private noncomputable abbrev collapseRight
    (i : CoordinateInterleaving ε M N)
    (W V : GradedGenerators.{0,w} (Fin n → ℝ))
    (a : module (R := R) W ⟶ M) (b : module (R := R) V ⟶ N) :
    module (R := R) (crossRight ε W V) ⟶ N :=
  sumDesc (W.shiftGrade (-(ε : ℝ))) V (delaySource ε W N (a ≫ i.φ)) b

private theorem crossFreeLR_collapse
    (i : CoordinateInterleaving ε M N)
    (W V : GradedGenerators.{0,w} (Fin n → ℝ))
    (a : module (R := R) W ⟶ M) (b : module (R := R) V ⟶ N) :
    crossFreeLR ε W V ≫ (CoordinateShift.shift ε).map (collapseRight i W V a b) =
      collapseLeft i W V a b ≫ i.φ := by
  apply sumHom_ext W (V.shiftGrade (-(ε : ℝ)))
  · have ht : sumInl (W.shiftGrade (-(ε : ℝ))) V ≫ collapseRight i W V a b = delaySource ε W N (a ≫ i.φ) := sumInl_sumDesc _ _ _ _
    have hs : sumInl W (V.shiftGrade (-(ε : ℝ))) ≫ collapseLeft i W V a b =
        a := sumInl_sumDesc _ _ _ _
    calc
      _ = (sumInl W (V.shiftGrade (-(ε : ℝ))) ≫ crossFreeLR ε W V) ≫
          (CoordinateShift.shift ε).map (collapseRight i W V a b) :=
        (Category.assoc _ _ _).symm
      _ = ((delayedShiftIso ε W).hom ≫ (CoordinateShift.shift ε).map (sumInl (W.shiftGrade (-(ε : ℝ))) V)) ≫
          (CoordinateShift.shift ε).map (collapseRight i W V a b) :=
        congrArg (· ≫ (CoordinateShift.shift ε).map (collapseRight i W V a b))
          (sumInl_crossFreeLR (R := R) ε W V)
      _ = (delayedShiftIso ε W).hom ≫ (CoordinateShift.shift ε).map
          (sumInl (W.shiftGrade (-(ε : ℝ))) V ≫ collapseRight i W V a b) :=
        (Category.assoc _ _ _).trans
          (congrArg ((delayedShiftIso ε W).hom ≫ ·) ((CoordinateShift.shift ε).map_comp _ _).symm)
      _ = (delayedShiftIso ε W).hom ≫ (CoordinateShift.shift ε).map (delaySource ε W N (a ≫ i.φ)) :=
        congrArg (fun f => (delayedShiftIso ε W).hom ≫ (CoordinateShift.shift ε).map f) ht
      _ = a ≫ i.φ := delayedShiftIso_delaySource ε W N (a ≫ i.φ)
      _ = _ := (congrArg (· ≫ i.φ) hs).symm.trans (Category.assoc _ _ _)
  · have ht : sumInr (W.shiftGrade (-(ε : ℝ))) V ≫ collapseRight i W V a b = b := sumInr_sumDesc _ _ _ _
    have hs : sumInr W (V.shiftGrade (-(ε : ℝ))) ≫ collapseLeft i W V a b =
        delaySource ε V M (b ≫ i.ψ) := sumInr_sumDesc _ _ _ _
    calc
      _ = (sumInr W (V.shiftGrade (-(ε : ℝ))) ≫ crossFreeLR ε W V) ≫
          (CoordinateShift.shift ε).map (collapseRight i W V a b) :=
        (Category.assoc _ _ _).symm
      _ = (delayedAdvance ε V ≫ (CoordinateShift.shift ε).map (sumInr (W.shiftGrade (-(ε : ℝ))) V)) ≫
          (CoordinateShift.shift ε).map (collapseRight i W V a b) :=
        congrArg (· ≫ (CoordinateShift.shift ε).map (collapseRight i W V a b))
          (sumInr_crossFreeLR (R := R) ε W V)
      _ = delayedAdvance ε V ≫ (CoordinateShift.shift ε).map
          (sumInr (W.shiftGrade (-(ε : ℝ))) V ≫ collapseRight i W V a b) :=
        (Category.assoc _ _ _).trans
          (congrArg (delayedAdvance ε V ≫ ·) ((CoordinateShift.shift ε).map_comp _ _).symm)
      _ = delayedAdvance ε V ≫ (CoordinateShift.shift ε).map (b) :=
        congrArg (fun f => delayedAdvance ε V ≫ (CoordinateShift.shift ε).map f) ht
      _ = delaySource ε V M (b ≫ i.ψ) ≫ i.φ := (delaySource_comp_interleaving i V b).symm
      _ = _ := (congrArg (· ≫ i.φ) hs).symm.trans (Category.assoc _ _ _)
private theorem crossFreeRL_collapse
    (i : CoordinateInterleaving ε M N)
    (W V : GradedGenerators.{0,w} (Fin n → ℝ))
    (a : module (R := R) W ⟶ M) (b : module (R := R) V ⟶ N) :
    crossFreeRL ε W V ≫ (CoordinateShift.shift ε).map (collapseLeft i W V a b) =
      collapseRight i W V a b ≫ i.ψ := by
  apply sumHom_ext (W.shiftGrade (-(ε : ℝ))) V
  · have ht : sumInl W (V.shiftGrade (-(ε : ℝ))) ≫ collapseLeft i W V a b = a := sumInl_sumDesc _ _ _ _
    have hs : sumInl (W.shiftGrade (-(ε : ℝ))) V ≫ collapseRight i W V a b =
        delaySource ε W N (a ≫ i.φ) := sumInl_sumDesc _ _ _ _
    calc
      _ = (sumInl (W.shiftGrade (-(ε : ℝ))) V ≫ crossFreeRL ε W V) ≫
          (CoordinateShift.shift ε).map (collapseLeft i W V a b) :=
        (Category.assoc _ _ _).symm
      _ = (delayedAdvance ε W ≫ (CoordinateShift.shift ε).map (sumInl W (V.shiftGrade (-(ε : ℝ))))) ≫
          (CoordinateShift.shift ε).map (collapseLeft i W V a b) :=
        congrArg (· ≫ (CoordinateShift.shift ε).map (collapseLeft i W V a b))
          (sumInl_crossFreeRL (R := R) ε W V)
      _ = delayedAdvance ε W ≫ (CoordinateShift.shift ε).map
          (sumInl W (V.shiftGrade (-(ε : ℝ))) ≫ collapseLeft i W V a b) :=
        (Category.assoc _ _ _).trans
          (congrArg (delayedAdvance ε W ≫ ·) ((CoordinateShift.shift ε).map_comp _ _).symm)
      _ = delayedAdvance ε W ≫ (CoordinateShift.shift ε).map (a) :=
        congrArg (fun f => delayedAdvance ε W ≫ (CoordinateShift.shift ε).map f) ht
      _ = delaySource ε W N (a ≫ i.φ) ≫ i.ψ := (delaySource_comp_interleaving i.symm W a).symm
      _ = _ := (congrArg (· ≫ i.ψ) hs).symm.trans (Category.assoc _ _ _)
  · have ht : sumInr W (V.shiftGrade (-(ε : ℝ))) ≫ collapseLeft i W V a b = delaySource ε V M (b ≫ i.ψ) := sumInr_sumDesc _ _ _ _
    have hs : sumInr (W.shiftGrade (-(ε : ℝ))) V ≫ collapseRight i W V a b =
        b := sumInr_sumDesc _ _ _ _
    calc
      _ = (sumInr (W.shiftGrade (-(ε : ℝ))) V ≫ crossFreeRL ε W V) ≫
          (CoordinateShift.shift ε).map (collapseLeft i W V a b) :=
        (Category.assoc _ _ _).symm
      _ = ((delayedShiftIso ε V).hom ≫ (CoordinateShift.shift ε).map (sumInr W (V.shiftGrade (-(ε : ℝ))))) ≫
          (CoordinateShift.shift ε).map (collapseLeft i W V a b) :=
        congrArg (· ≫ (CoordinateShift.shift ε).map (collapseLeft i W V a b))
          (sumInr_crossFreeRL (R := R) ε W V)
      _ = (delayedShiftIso ε V).hom ≫ (CoordinateShift.shift ε).map
          (sumInr W (V.shiftGrade (-(ε : ℝ))) ≫ collapseLeft i W V a b) :=
        (Category.assoc _ _ _).trans
          (congrArg ((delayedShiftIso ε V).hom ≫ ·) ((CoordinateShift.shift ε).map_comp _ _).symm)
      _ = (delayedShiftIso ε V).hom ≫ (CoordinateShift.shift ε).map (delaySource ε V M (b ≫ i.ψ)) :=
        congrArg (fun f => (delayedShiftIso ε V).hom ≫ (CoordinateShift.shift ε).map f) ht
      _ = b ≫ i.ψ := delayedShiftIso_delaySource ε V M (b ≫ i.ψ)
      _ = _ := (congrArg (· ≫ i.ψ) hs).symm.trans (Category.assoc _ _ _)

private theorem sumDesc_comp_zero
    (W V : GradedGenerators.{0,w} (Fin n → ℝ))
    {A B : PModule.{u,0,max u w} R (Fin n → ℝ)}
    (f : module (R := R) W ⟶ A) (g : module (R := R) V ⟶ A) (ρ : A ⟶ B)
    (hf : f ≫ ρ = 0) (hg : g ≫ ρ = 0) : sumDesc W V f g ≫ ρ = 0 := by
  apply sumHom_ext W V
  · exact (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ ρ) (sumInl_sumDesc W V f g)).trans
        (hf.trans (by simp)))
  · exact (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ ρ) (sumInr_sumDesc W V f g)).trans
        (hg.trans (by simp)))

private noncomputable def quotientIsoOfMutualDescent
    (P Q : Presentation.{u,0,w} (R := R) (P := Fin n → ℝ))
    (e : module (R := R) P.generators ≅ module Q.generators)
    (hP : P.relationMap ≫ e.hom ≫ Q.cover = 0)
    (hQ : Q.relationMap ≫ e.inv ≫ P.cover = 0) : P.presented ≅ Q.presented where
  hom := P.desc (e.hom ≫ Q.cover) hP
  inv := Q.desc (e.inv ≫ P.cover) hQ
  hom_inv_id := by
    have : Epi P.cover := by change Epi (cokernel.π P.relationMap); infer_instance
    apply (cancel_epi P.cover).mp
    calc
      _ = (e.hom ≫ Q.cover) ≫ Q.desc (e.inv ≫ P.cover) hQ :=
        (Category.assoc _ _ _).symm.trans
          (congrArg (· ≫ Q.desc (e.inv ≫ P.cover) hQ) (P.cover_desc _ _))
      _ = e.hom ≫ (e.inv ≫ P.cover) :=
        (Category.assoc _ _ _).trans (congrArg (e.hom ≫ ·) (Q.cover_desc _ _))
      _ = P.cover ≫ 𝟙 P.presented := by simp
  inv_hom_id := by
    have : Epi Q.cover := by change Epi (cokernel.π Q.relationMap); infer_instance
    apply (cancel_epi Q.cover).mp
    calc
      _ = (e.inv ≫ P.cover) ≫ P.desc (e.hom ≫ Q.cover) hP :=
        (Category.assoc _ _ _).symm.trans
          (congrArg (· ≫ P.desc (e.hom ≫ Q.cover) hP) (Q.cover_desc _ _))
      _ = e.inv ≫ (e.hom ≫ Q.cover) :=
        (Category.assoc _ _ _).trans (congrArg (e.inv ≫ ·) (P.cover_desc _ _))
      _ = Q.cover ≫ 𝟙 Q.presented := by simp

/-- All four primitive generator and relation families are finite. -/
def CrossData.IsFinite (C : CrossData.{u,w} (R := R) (n := n) ε) : Prop :=
  Finite C.W₁.Carrier ∧ Finite C.W₂.Carrier ∧ Finite C.Y₁.Carrier ∧ Finite C.Y₂.Carrier

namespace Presentation

variable (D E : Presentation.{u,0,w} (R := R) (P := Fin n → ℝ))
  (i : CoordinateInterleaving ε D.presented E.presented)

private noncomputable abbrev leftValues :=
  delaySource ε E.generators D.presented (E.cover ≫ i.ψ)

private noncomputable abbrev rightValues :=
  delaySource ε D.generators E.presented (D.cover ≫ i.φ)

private noncomputable abbrev leftChosen :=
  fun v : (E.generators.shiftGrade (-(ε : ℝ))).Carrier =>
    (leftValues D E i).app ((E.generators.shiftGrade (-(ε : ℝ))).grade v)
      (birth (E.generators.shiftGrade (-(ε : ℝ))) v)

private noncomputable abbrev rightChosen :=
  fun v : (D.generators.shiftGrade (-(ε : ℝ))).Carrier =>
    (rightValues D E i).app ((D.generators.shiftGrade (-(ε : ℝ))).grade v)
      (birth (D.generators.shiftGrade (-(ε : ℝ))) v)

private noncomputable abbrev leftAugmented :=
  D.adjoinRedundant (E.generators.shiftGrade (-(ε : ℝ))) (leftChosen D E i)

private noncomputable abbrev rightAugmented :=
  E.adjoinRedundant (D.generators.shiftGrade (-(ε : ℝ))) (rightChosen D E i)

/-- The shared primitive relations consist of the old relations and the graph
relations identifying each delayed generator with a free lift of its image. -/
noncomputable def crossData : CrossData.{u,w} (R := R) (n := n) ε where
  W₁ := D.generators
  W₂ := E.generators
  Y₁ := (leftAugmented D E i).relations
  Y₂ := (rightAugmented D E i).relations
  r₁ := (leftAugmented D E i).relationMap
  r₂ := (rightAugmented D E i).relationMap ≫
    (sumCommIso (R := R) E.generators (D.generators.shiftGrade (-(ε : ℝ)))).hom

private theorem chosenMap_eq
    (P : Presentation.{u,0,w} (R := R) (P := Fin n → ℝ))
    (V : GradedGenerators.{0,w} (Fin n → ℝ)) (f : module (R := R) V ⟶ P.presented) :
    P.chosenMap V (fun v => f.app (V.grade v) (birth V v)) = f :=
  (lift_unique V P.presented _ f (fun _ => rfl)).symm

private theorem leftCollapse_eq :
    D.adjoinCollapse (E.generators.shiftGrade (-(ε : ℝ))) (leftChosen D E i) =
      collapseLeft i D.generators E.generators D.cover E.cover := by
  exact congrArg
    (sumDesc D.generators (E.generators.shiftGrade (-(ε : ℝ))) D.cover)
    (chosenMap_eq D (E.generators.shiftGrade (-(ε : ℝ))) (leftValues D E i))

private theorem rightCollapse_eq :
    (sumCommIso (R := R) E.generators (D.generators.shiftGrade (-(ε : ℝ)))).inv ≫
      E.adjoinCollapse (D.generators.shiftGrade (-(ε : ℝ))) (rightChosen D E i) =
        collapseRight i D.generators E.generators D.cover E.cover := by
  apply sumHom_ext (D.generators.shiftGrade (-(ε : ℝ))) E.generators
  · calc
      _ = sumInr E.generators (D.generators.shiftGrade (-(ε : ℝ))) ≫
          E.adjoinCollapse (D.generators.shiftGrade (-(ε : ℝ))) (rightChosen D E i) := by
        simp only [← Category.assoc, sumCommIso, sumInl_sumDesc]
      _ = rightValues D E i :=
        (E.sumInr_adjoinCollapse _ _).trans (chosenMap_eq E _ _)
      _ = _ := (sumInl_sumDesc _ _ _ _).symm
  · calc
      _ = sumInl E.generators (D.generators.shiftGrade (-(ε : ℝ))) ≫
          E.adjoinCollapse (D.generators.shiftGrade (-(ε : ℝ))) (rightChosen D E i) := by
        simp only [← Category.assoc, sumCommIso, sumInr_sumDesc]
      _ = E.cover := E.sumInl_adjoinCollapse _ _
      _ = _ := (sumInr_sumDesc _ _ _ _).symm

private theorem primitiveLeft_vanish :
    (D.crossData E i).r₁ ≫
      collapseLeft i D.generators E.generators D.cover E.cover = 0 := by
  change (leftAugmented D E i).relationMap ≫
    collapseLeft i D.generators E.generators D.cover E.cover = 0
  rw [← leftCollapse_eq]
  exact D.adjoinRelation_collapse _ _

private theorem primitiveRight_vanish :
    (D.crossData E i).r₂ ≫
      collapseRight i D.generators E.generators D.cover E.cover = 0 := by
  change ((rightAugmented D E i).relationMap ≫
      (sumCommIso (R := R) E.generators (D.generators.shiftGrade (-(ε : ℝ)))).hom) ≫
    collapseRight i D.generators E.generators D.cover E.cover = 0
  have hR :
      (sumCommIso (R := R) E.generators (D.generators.shiftGrade (-(ε : ℝ)))).hom ≫
        collapseRight i D.generators E.generators D.cover E.cover =
      E.adjoinCollapse (D.generators.shiftGrade (-(ε : ℝ))) (rightChosen D E i) := by
    calc
      _ = (sumCommIso (R := R) E.generators (D.generators.shiftGrade (-(ε : ℝ)))).hom ≫
          ((sumCommIso (R := R) E.generators (D.generators.shiftGrade (-(ε : ℝ)))).inv ≫
            E.adjoinCollapse (D.generators.shiftGrade (-(ε : ℝ))) (rightChosen D E i)) :=
        congrArg ((sumCommIso (R := R) E.generators
          (D.generators.shiftGrade (-(ε : ℝ)))).hom ≫ ·) (rightCollapse_eq D E i).symm
      _ = _ := by simp only [Iso.hom_inv_id_assoc]
  exact (Category.assoc _ _ _).trans
    ((congrArg ((rightAugmented D E i).relationMap ≫ ·) hR).trans
      (E.adjoinRelation_collapse _ _))

private theorem allLeft_vanish :
    (D.crossData E i).leftPresentation.relationMap ≫
      collapseLeft i D.generators E.generators D.cover E.cover = 0 := by
  apply sumDesc_comp_zero
  · exact primitiveLeft_vanish D E i
  · apply (delaySource_comp_zero_iff ε (D.crossData E i).Y₂
      ((D.crossData E i).r₂ ≫ crossFreeRL ε D.generators E.generators)
      (collapseLeft i D.generators E.generators D.cover E.cover)).mpr
    calc
      _ = (D.crossData E i).r₂ ≫
          (collapseRight i D.generators E.generators D.cover E.cover ≫ i.ψ) :=
        congrArg ((D.crossData E i).r₂ ≫ ·)
          (crossFreeRL_collapse i D.generators E.generators D.cover E.cover)
      _ = ((D.crossData E i).r₂ ≫
          collapseRight i D.generators E.generators D.cover E.cover) ≫ i.ψ :=
        (Category.assoc _ _ _).symm
      _ = 0 := by rw [primitiveRight_vanish]; simp

private theorem allRight_vanish :
    (D.crossData E i).rightPresentation.relationMap ≫
      collapseRight i D.generators E.generators D.cover E.cover = 0 := by
  apply sumDesc_comp_zero
  · apply (delaySource_comp_zero_iff ε (D.crossData E i).Y₁
      ((D.crossData E i).r₁ ≫ crossFreeLR ε D.generators E.generators)
      (collapseRight i D.generators E.generators D.cover E.cover)).mpr
    calc
      _ = (D.crossData E i).r₁ ≫
          (collapseLeft i D.generators E.generators D.cover E.cover ≫ i.φ) :=
        congrArg ((D.crossData E i).r₁ ≫ ·)
          (crossFreeLR_collapse i D.generators E.generators D.cover E.cover)
      _ = ((D.crossData E i).r₁ ≫
          collapseLeft i D.generators E.generators D.cover E.cover) ≫ i.φ :=
        (Category.assoc _ _ _).symm
      _ = 0 := by rw [primitiveLeft_vanish]; simp
  · exact primitiveRight_vanish D E i

/-- The first constructed cross-presentation is naturally isomorphic to the
original first presented module. The delayed opposite relations are proved
redundant from the interleaving, rather than assumed to vanish. -/
noncomputable def crossDataLeftIso :
    (D.crossData E i).leftPresentation.presented ≅ D.presented := by
  let P := leftAugmented D E i
  let Q := (D.crossData E i).leftPresentation
  let e := D.adjoinRedundantIso (E.generators.shiftGrade (-(ε : ℝ))) (leftChosen D E i)
  have hp : P.relationMap ≫ (𝟙 (module (R := R) P.generators)) ≫ Q.cover = 0 := by
    exact (congrArg (P.relationMap ≫ ·) (Category.id_comp Q.cover)).trans
      (D.crossData E i).primitive_left_vanish
  have hq0 : Q.relationMap ≫ P.cover = 0 := by
    apply (cancel_mono e.hom).mp
    calc
      _ = Q.relationMap ≫ (P.cover ≫ e.hom) := Category.assoc _ _ _
      _ = Q.relationMap ≫
          D.adjoinCollapse (E.generators.shiftGrade (-(ε : ℝ))) (leftChosen D E i) :=
        congrArg (Q.relationMap ≫ ·) (D.adjoinCover_forget _ _)
      _ = Q.relationMap ≫ collapseLeft i D.generators E.generators D.cover E.cover :=
        congrArg (Q.relationMap ≫ ·) (leftCollapse_eq D E i)
      _ = 0 := allLeft_vanish D E i
      _ = (0 : module (R := R) Q.relations ⟶ P.presented) ≫ e.hom := by simp
  have hq : Q.relationMap ≫ (𝟙 (module (R := R) P.generators)) ≫ P.cover = 0 :=
    (congrArg (Q.relationMap ≫ ·) (Category.id_comp P.cover)).trans hq0
  exact (quotientIsoOfMutualDescent P Q (Iso.refl _) hp hq).symm ≪≫ e

/-- The second constructed cross-presentation is naturally isomorphic to the
original second presented module. -/
noncomputable def crossDataRightIso :
    (D.crossData E i).rightPresentation.presented ≅ E.presented := by
  let P := rightAugmented D E i
  let Q := (D.crossData E i).rightPresentation
  let a := sumCommIso (R := R) E.generators (D.generators.shiftGrade (-(ε : ℝ)))
  let e := E.adjoinRedundantIso (D.generators.shiftGrade (-(ε : ℝ))) (rightChosen D E i)
  have hp : P.relationMap ≫ a.hom ≫ Q.cover = 0 :=
    (Category.assoc _ _ _).symm.trans (D.crossData E i).primitive_right_vanish
  have hq : Q.relationMap ≫ a.inv ≫ P.cover = 0 := by
    apply (cancel_mono e.hom).mp
    calc
      _ = Q.relationMap ≫ (a.inv ≫ (P.cover ≫ e.hom)) :=
        (Category.assoc _ _ _).trans (congrArg (Q.relationMap ≫ ·) (Category.assoc _ _ _))
      _ = Q.relationMap ≫ (a.inv ≫
          E.adjoinCollapse (D.generators.shiftGrade (-(ε : ℝ))) (rightChosen D E i)) :=
        congrArg (fun f => Q.relationMap ≫ (a.inv ≫ f)) (E.adjoinCover_forget _ _)
      _ = Q.relationMap ≫ collapseRight i D.generators E.generators D.cover E.cover :=
        congrArg (Q.relationMap ≫ ·) (rightCollapse_eq D E i)
      _ = 0 := allRight_vanish D E i
      _ = (0 : module (R := R) Q.relations ⟶ P.presented) ≫ e.hom := by simp
  exact (quotientIsoOfMutualDescent P Q a hp hq).symm ≪≫ e

/-- Finite original presentations yield finite shared cross-presentation data. -/
theorem crossData_isFinite (hD : D.IsFinite) (hE : E.IsFinite) :
    (D.crossData E i).IsFinite := by
  classical
  let : Finite D.generators.Carrier := hD.1
  let : Finite E.generators.Carrier := hE.1
  let : Finite D.relations.Carrier := hD.2
  let : Finite E.relations.Carrier := hE.2
  let : Fintype D.generators.Carrier := Fintype.ofFinite _
  let : Fintype E.generators.Carrier := Fintype.ofFinite _
  let : Fintype D.relations.Carrier := Fintype.ofFinite _
  let : Fintype E.relations.Carrier := Fintype.ofFinite _
  change Finite D.generators.Carrier ∧ Finite E.generators.Carrier ∧
    Finite (D.relations.Carrier ⊕ E.generators.Carrier) ∧
    Finite (E.relations.Carrier ⊕ D.generators.Carrier)
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩

end Presentation

/-- Every interleaving between finitely presented real-coordinate modules
admits finite shared cross-presentations. -/
theorem finitelyPresented_exists_crossPresentation
    (hM : FinitelyPresented (R := R) (P := Fin n → ℝ) M)
    (hN : FinitelyPresented (R := R) (P := Fin n → ℝ) N)
    (i : CoordinateInterleaving ε M N) :
    ∃ C : CrossData.{u,w} (R := R) (n := n) ε, C.IsFinite ∧
      Nonempty (C.leftPresentation.presented ≅ M) ∧
      Nonempty (C.rightPresentation.presented ≅ N) := by
  obtain ⟨D, hD, ⟨eD⟩⟩ := hM
  obtain ⟨E, hE, ⟨eE⟩⟩ := hN
  let j := i.congr eD.symm eE.symm
  exact ⟨D.crossData E j, D.crossData_isFinite E j hD hE,
    ⟨D.crossDataLeftIso E j ≪≫ eD⟩, ⟨D.crossDataRightIso E j ≪≫ eE⟩⟩

/-- Finite-presentation characterization of the actual diagonal interleaving
relation by finite simultaneous shifted generator-and-relation presentations.
This is the finite-presentation part of Lesnick Theorem 4.4, over any ring and
including dimension zero. -/
theorem finitelyPresented_interleaving_iff_crossPresentation
    (hM : FinitelyPresented (R := R) (P := Fin n → ℝ) M)
    (hN : FinitelyPresented (R := R) (P := Fin n → ℝ) N) :
    Nonempty (CoordinateInterleaving ε M N) ↔
      ∃ C : CrossData.{u,w} (R := R) (n := n) ε, C.IsFinite ∧
        Nonempty (C.leftPresentation.presented ≅ M) ∧
        Nonempty (C.rightPresentation.presented ≅ N) := by
  constructor
  · rintro ⟨i⟩
    exact finitelyPresented_exists_crossPresentation hM hN i
  · rintro ⟨C, _, ⟨eM⟩, ⟨eN⟩⟩
    exact ⟨C.interleavingOfIso eM eN⟩

end TDA.Persistence.GradedFree
