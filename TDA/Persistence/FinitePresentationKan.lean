import TDA.Persistence.FinitePresentationLifting
import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction

/-!
# Kan reconstruction from presentation grades

An order embedding containing all generator and relation grades of a
presentation determines its quotient as a left Kan extension. The usual
Kan comparison is invertible on the embedded grades. Presentation lifting
then constructs its section, and Kan uniqueness proves the other inverse
law. Thus the comparison is an actual natural isomorphism, without a
constructibility or extension assumption.
-/

set_option autoImplicit false

universe u w

namespace TDA.Persistence.GradedFree.Presentation

open CategoryTheory CategoryTheory.Limits

variable {R : Type u} [Ring R] {P Q : Type} [Preorder P] [Preorder Q]
    (D : GradedFree.Presentation.{u,0,w} (R := R) (P := P)) (e : Q ↪o P)

/-- The functor of the given order embedding; Mathlib supplies full faithfulness. -/
abbrev embeddingFunctor : Q ⥤ P := e.monotone.functor

/-- The actual chosen Mathlib left Kan extension of the restricted presented module. -/
noncomputable abbrev restrictionLan : PModule.{u,0,max u w} R P :=
  (embeddingFunctor e).leftKanExtension ((embeddingFunctor e) ⋙ D.presented)

/-- The canonical comparison from the chosen Kan extension to the original quotient. -/
noncomputable def kanComparison : D.restrictionLan e ⟶ D.presented :=
  (D.restrictionLan e).descOfIsLeftKanExtension
    ((embeddingFunctor e).leftKanExtensionUnit ((embeddingFunctor e) ⋙ D.presented))
    D.presented (𝟙 _)

/-- The comparison extends identity on the restricted module. -/
theorem kanComparison_fac :
    (embeddingFunctor e).leftKanExtensionUnit ((embeddingFunctor e) ⋙ D.presented) ≫
      (embeddingFunctor e).whiskerLeft (D.kanComparison e) = 𝟙 _ :=
  Functor.descOfIsLeftKanExtension_fac _ _ _ _

private instance comparison_app_isIso (q : Q) : IsIso ((D.kanComparison e).app (e q)) := by
  let j := embeddingFunctor e
  let F := j ⋙ D.presented
  let η := j.leftKanExtensionUnit F
  have hη : IsIso (η.app q) :=
    (Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit j F (j.obj q)).isIso_hom_app
  have he := NatTrans.congr_app (D.kanComparison_fac e) q
  change η.app q ≫ (D.kanComparison e).app (e q) = 𝟙 _ at he
  have htotal : IsIso (η.app q ≫ (D.kanComparison e).app (e q)) := by
    rw [he]
    exact inferInstanceAs (IsIso (𝟙 (D.presented.obj (e q))))
  exact IsIso.of_isIso_comp_left (η.app q) ((D.kanComparison e).app (e q))

private theorem comparison_surjective (a : P) (ha : a ∈ Set.range e) :
    Function.Surjective ((D.kanComparison e).app a).hom := by
  obtain ⟨q, rfl⟩ := ha
  exact (ModuleCat.epi_iff_surjective _).mp inferInstance

private theorem comparison_injective (a : P) (ha : a ∈ Set.range e) :
    Function.Injective ((D.kanComparison e).app a).hom := by
  obtain ⟨q, rfl⟩ := ha
  exact (ModuleCat.mono_iff_injective _).mp inferInstance

variable
    (hG : ∀ g : D.generators.Carrier, D.generators.grade g ∈ Set.range e)
    (hY : ∀ y : D.relations.Carrier, D.relations.grade y ∈ Set.range e)

private noncomputable def comparisonSection : D.presented ⟶ D.restrictionLan e :=
  Classical.choose (D.exists_lift_of_birth_surjective_relation_injective
    (D.kanComparison e) (fun g => comparison_surjective D e _ (hG g))
    (fun y => comparison_injective D e _ (hY y)) (𝟙 _))

private theorem section_comparison :
    comparisonSection D e hG hY ≫ D.kanComparison e = 𝟙 _ :=
  Classical.choose_spec (D.exists_lift_of_birth_surjective_relation_injective
    (D.kanComparison e) (fun g => comparison_surjective D e _ (hG g))
    (fun y => comparison_injective D e _ (hY y)) (𝟙 _))

private theorem comparison_section :
    D.kanComparison e ≫ comparisonSection D e hG hY = 𝟙 _ := by
  let η := (embeddingFunctor e).leftKanExtensionUnit ((embeddingFunctor e) ⋙ D.presented)
  apply Functor.hom_ext_of_isLeftKanExtension (D.restrictionLan e) η
  apply NatTrans.ext
  funext q
  apply (cancel_mono ((D.kanComparison e).app (e q))).mp
  have he := NatTrans.congr_app (section_comparison D e hG hY) (e q)
  change (comparisonSection D e hG hY).app (e q) ≫ (D.kanComparison e).app (e q) = 𝟙 _ at he
  let u : D.presented.obj (e q) ⟶ (D.restrictionLan e).obj (e q) := η.app q
  change (u ≫ ((D.kanComparison e).app (e q) ≫
      (comparisonSection D e hG hY).app (e q))) ≫ (D.kanComparison e).app (e q) =
    (u ≫ 𝟙 ((D.restrictionLan e).obj (e q))) ≫ (D.kanComparison e).app (e q)
  simp only [Category.assoc, he, Category.comp_id]

/-- If the embedding contains every presentation grade, its canonical Kan
comparison is an isomorphism; the inverse is constructed by presentation lifting. -/
noncomputable def kanIso : D.restrictionLan e ≅ D.presented where
  hom := D.kanComparison e
  inv := comparisonSection D e hG hY
  hom_inv_id := comparison_section D e hG hY
  inv_hom_id := section_comparison D e hG hY

/-- The comparison underlying the reconstruction is the canonical Kan comparison. -/
theorem kanIso_hom : (D.kanIso e hG hY).hom = D.kanComparison e := rfl

include hG hY in
/-- The presented module satisfies Mathlib's left-Kan universal property for
identity on its restriction, with no caller-supplied extension property. -/
theorem isLeftKanExtension : D.presented.IsLeftKanExtension
    (𝟙 ((embeddingFunctor e) ⋙ D.presented)) :=
  Functor.isLeftKanExtension_of_iso (D.kanIso e hG hY)
    ((embeddingFunctor e).leftKanExtensionUnit ((embeddingFunctor e) ⋙ D.presented))
    (𝟙 _) (D.kanComparison_fac e)

/-- On the embedded grades, the inverse reconstruction is the original Kan unit. -/
theorem kanIso_inv_restrict :
    (embeddingFunctor e).whiskerLeft (D.kanIso e hG hY).inv =
      (embeddingFunctor e).leftKanExtensionUnit ((embeddingFunctor e) ⋙ D.presented) := by
  apply NatTrans.ext
  funext q
  change (D.kanIso e hG hY).inv.app (e q) = _
  apply (cancel_mono ((D.kanComparison e).app (e q))).mp
  have h₁ := NatTrans.congr_app (D.kanIso e hG hY).inv_hom_id (e q)
  have h₂ := NatTrans.congr_app (D.kanComparison_fac e) q
  exact h₁.trans h₂.symm

/-- Restricting maps out of the presented module is a bijection onto all
natural maps on the embedded grades. -/
noncomputable def restrictionHomEquiv (N : PModule.{u,0,max u w} R P) :
    (D.presented ⟶ N) ≃ ((embeddingFunctor e) ⋙ D.presented ⟶ (embeddingFunctor e) ⋙ N) := by
  let := D.isLeftKanExtension e hG hY
  exact D.presented.homEquivOfIsLeftKanExtension (𝟙 _) N

/-- The forward bijection is ordinary restriction of the given natural map. -/
theorem restrictionHomEquiv_apply (N : PModule.{u,0,max u w} R P) (f : D.presented ⟶ N) :
    D.restrictionHomEquiv e hG hY N f = (embeddingFunctor e).whiskerLeft f := by
  change (𝟙 ((embeddingFunctor e) ⋙ D.presented)) ≫
    (embeddingFunctor e).whiskerLeft f = (embeddingFunctor e).whiskerLeft f
  exact Category.id_comp _

/-- The constructed extension restricts to its given natural map. -/
theorem restrictionHomEquiv_symm_restrict (N : PModule.{u,0,max u w} R P)
    (α : (embeddingFunctor e) ⋙ D.presented ⟶ (embeddingFunctor e) ⋙ N) :
    (embeddingFunctor e).whiskerLeft ((D.restrictionHomEquiv e hG hY N).symm α) = α := by
  rw [← restrictionHomEquiv_apply]
  exact (D.restrictionHomEquiv e hG hY N).apply_symm_apply α

/-- Any map extending the same restricted data is the constructed extension. -/
theorem restrictionHomEquiv_symm_unique (N : PModule.{u,0,max u w} R P)
    (α : (embeddingFunctor e) ⋙ D.presented ⟶ (embeddingFunctor e) ⋙ N)
    (f : D.presented ⟶ N) (hf : (embeddingFunctor e).whiskerLeft f = α) :
    f = (D.restrictionHomEquiv e hG hY N).symm α := by
  apply (D.restrictionHomEquiv e hG hY N).injective
  rw [restrictionHomEquiv_apply, hf, Equiv.apply_symm_apply]

end TDA.Persistence.GradedFree.Presentation
