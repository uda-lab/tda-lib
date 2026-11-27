import TDA.Sheaf.BandCompositionLaws

/-!
# Unit laws of the composition isomorphism of the band functors

`TDA.Sheaf.BandComposition` constructs `TComp k ha hb : T k a ⋙ T k b ≅ T k (a + b)` for `0 ≤ a`,
`0 ≤ b`, and `TDA.Sheaf.BandCompositionLaws` the variant `TCompOfEq k ha hb h : T k a ⋙ T k b ≅ T k c`
along `h : a + b = c`. This file proves that `T0Iso k : T k 0 ≅ 𝟭` is a two-sided unit for it.

* **Transported counit.** `TCompCounitNT k a b : T k a ⋙ (pr₂₃ ≫ p b)⁻¹ ⟶ (pr₁₂ ≫ p a)⁻¹` is the
  natural transformation with components `TCompCounit k a b` (`TCompCounitNT_app`); it is
  `transportCounit` along `pr₁₂` (`TCompCounitNT_eq`). `TComp_hom_TCompRestr`: `TComp` followed by
  `TCompRestr` is the restriction along `pr₂₃` whiskered by `T k a`, followed by `R(pr₂₃ ≫ q b)_*`
  of `TCompCounitNT`.
* **Left unit.** `whiskerRight_T0Iso_inv_TCompCounitNT` (on `Z 0 b`, where `x = y`) and
  `whiskerRight_T0Iso_inv_TComp_hom`; with them, for `0 ≤ b`,
  `TCompOfEq_zero_left_hom : (TCompOfEq k le_rfl hb (zero_add b)).hom =
    whiskerRight (T0Iso k).hom (T k b) ≫ (leftUnitor (T k b)).hom`.
* **Right unit.** `pr₁₂_q_add_zero` (on `Z a 0`, where `y = z`) and
  `whiskerLeft_T0Iso_inv_TComp_hom`; with them, for `0 ≤ a`,
  `TCompOfEq_zero_right_hom : (TCompOfEq k ha le_rfl (add_zero a)).hom =
    whiskerLeft (T k a) (T0Iso k).hom ≫ (rightUnitor (T k a)).hom`.
* **Augmentation.** `restr_eqToHom` (radius maps along `c = c'`) and, for `0 ≤ a`, `0 ≤ b`,
  `hcomp_aug_TComp_hom : (aug k ha ◫ aug k hb) ≫ (leftUnitor (𝟭 _)).hom =
    (TComp k ha hb).hom ≫ aug k (add_nonneg ha hb)`.
* **Bounded derived category.** `compIsoB_TCompOfEq_zero_left_hom` and
  `compIsoB_TCompOfEq_zero_right_hom`: the unit laws for the restrictions `compIsoB k (TCompOfEq …)`
  to `Dᵇ(Sh(ℝ; k))`, with `T0IsoB`. `hcomp_augB_TCompB_hom` is the augmentation law
  with `augB` and `TCompB`.

All statements are equations of natural transformations; the component computations are the
general lemmas on transported counits of `TDA.Sheaf.BaseChangeRestriction`. Derived categories are
instance arguments: on the real line, on every band `D a`, on every `Z a b`, on the point and on
every compact interval `[u, v]`.
-/

noncomputable section
open CategoryTheory Limits TopologicalSpace

namespace TDA.Sheaf.BandConvolution

/-- The left unit triangle for abstract whiskerings: if `whiskerRight α G ≫ γ = λ ≫ δ`, then
`whiskerRight α F ≫ whiskerLeft K β ≫ α⁻¹ ≫ whiskerRight γ H = λ ≫ β ≫ whiskerRight δ H`. -/
private lemma whiskerRight_whiskerLeft_unit_abs {C D Y : Type*} [Category* C] [Category* D]
    [Category* Y] {F : C ⥤ D} {G : C ⥤ Y} {H : Y ⥤ D} {K : C ⥤ C} {Q : C ⥤ Y} (α : 𝟭 C ⟶ K)
    (β : F ⟶ G ⋙ H) (γ : K ⋙ G ⟶ Q) (δ : G ⟶ Q)
    (h : Functor.whiskerRight α G ≫ γ = (Functor.leftUnitor G).hom ≫ δ) :
    Functor.whiskerRight α F ≫ Functor.whiskerLeft K β ≫ (Functor.associator K G H).inv ≫
        Functor.whiskerRight γ H =
      (Functor.leftUnitor F).hom ≫ β ≫ Functor.whiskerRight δ H := by
  ext X
  have e := congr_app h X
  have n := β.naturality (α.app X)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.leftUnitor_hom_app,
    Functor.id_obj] at e
  simp only [Functor.comp_map] at n
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_inv_app, Functor.leftUnitor_hom_app, Functor.id_obj, Functor.comp_obj,
    Category.id_comp, reassoc_of% n, ← Functor.map_comp, e]

/-- `whiskerLeft` of an identification of functors is an identification. -/
private lemma whiskerLeft_eqToHom_abs {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (F : C ⥤ D) {G H : D ⥤ E} (h : G = H) :
    Functor.whiskerLeft F (eqToHom h) = eqToHom (congrArg (F ⋙ ·) h) := by
  subst h
  simp

/-- `whiskerRight` of an identification of functors is an identification. -/
private lemma whiskerRight_eqToHom_abs {C D E : Type*} [Category* C] [Category* D] [Category* E]
    {F G : C ⥤ D} (h : F = G) (H : D ⥤ E) :
    Functor.whiskerRight (eqToHom h) H = eqToHom (congrArg (· ⋙ H) h) := by
  subst h
  simp

/-- For `α : F ⟶ 𝟭`, `(α ◫ α) ≫ λ = whiskerRight α F ≫ λ ≫ α`. -/
private lemma hcomp_self_leftUnitor_abs {C : Type*} [Category* C] {F : C ⥤ C} (α : F ⟶ 𝟭 C) :
    (α ◫ α) ≫ (Functor.leftUnitor (𝟭 C)).hom =
      Functor.whiskerRight α F ≫ (Functor.leftUnitor F).hom ≫ α := by
  ext X
  simp [α.naturality]

private lemma hcomp_leftUnitor {C : Type*} [Category* C] {F G : C ⥤ C}
    (α : F ⟶ 𝟭 C) (β : G ⟶ 𝟭 C) :
    (α ◫ β) ≫ (Functor.leftUnitor (𝟭 C)).hom =
      Functor.whiskerLeft F β ≫ (Functor.rightUnitor F).hom ≫ α := by
  ext X
  simp

/-- On `Z a 0`, where `y = z`, `pr₁₂ a 0 ≫ q a = pr₂₃ a 0 ≫ q 0`. -/
lemma pr₁₂_q_add_zero (a : ℝ) : pr₁₂ a 0 ≫ q a = pr₂₃ a 0 ≫ q 0 :=
  TopCat.ext fun w => dist_le_zero.1 w.2.2

variable (k : Type) [Ring k] [HasDerivedCategory (realLine.Sheaf (ModuleCat.{0} k))]
  [∀ a : ℝ, HasDerivedCategory ((D a).Sheaf (ModuleCat.{0} k))]
  [∀ a b : ℝ, HasDerivedCategory ((Z a b).Sheaf (ModuleCat.{0} k))]

/-- **The transported counit as a natural transformation**
`T k a ⋙ (pr₂₃ ≫ p b)⁻¹ ⟶ (pr₁₂ ≫ p a)⁻¹`: `transportCounit` along `pr₁₂` of the counit of
`q a`, with source written through the central square `pr₁₂ ≫ q a = pr₂₃ ≫ p b`. Its components
are `TCompCounit k a b` (`TCompCounitNT_app`). -/
def TCompCounitNT (a b : ℝ) :
    T k a ⋙ pullbackPlus k (pr₂₃ a b ≫ p b) ⟶ pullbackPlus k (pr₁₂ a b ≫ p a) :=
  transportCounit k (pr₁₂ a b) (p a) (q a)

/-- The components of `TCompCounitNT` are the transported counits `TCompCounit`. -/
lemma TCompCounitNT_app (a b : ℝ) (M : DerivedCategory.Plus (realLine.Sheaf (ModuleCat.{0} k))) :
    (TCompCounitNT k a b).app M = TCompCounit k a b M := by
  rw [TCompCounitNT, transportCounit_app, TCompCounit_eq]

/-- `TCompCounitNT` is `transportCounit` along `pr₁₂` after the identification
`(pr₂₃ ≫ p b)⁻¹ = (pr₁₂ ≫ q a)⁻¹` of the central square. -/
lemma TCompCounitNT_eq (a b : ℝ) :
    TCompCounitNT k a b = Functor.whiskerLeft (T k a)
      (eqToHom (congrArg (pullbackPlus k) (pr₁₂_q a b).symm)) ≫
        transportCounit k (pr₁₂ a b) (p a) (q a) := by
  rw [whiskerLeft_eqToHom_abs]
  exact (Category.id_comp _).symm

/-- **The unit against the transported counit.** On `Z 0 b`, `(pr₂₃ ≫ p b)⁻¹` of the inverse of
`T0Iso k`, followed by `TCompCounitNT k 0 b`, is the identification
`(pr₁₂ ≫ q 0)⁻¹ = (pr₁₂ ≫ p 0)⁻¹` along `p 0 = q 0`. -/
lemma whiskerRight_T0Iso_inv_TCompCounitNT (b : ℝ) :
    Functor.whiskerRight (T0Iso k).inv (pullbackPlus k (pr₂₃ 0 b ≫ p b)) ≫ TCompCounitNT k 0 b =
      (Functor.leftUnitor _).hom ≫
        eqToHom (congrArg (fun r => pullbackPlus k (pr₁₂ 0 b ≫ r)) p_zero_eq_q_zero.symm) := by
  rw [T0Iso_eq_corrUnitIso, TCompCounitNT]
  exact whiskerRight_corrUnitIso_inv_transportCounit k (pr₁₂ 0 b) p_zero_eq_q_zero

variable [HasDerivedCategory (pt.Sheaf (ModuleCat.{0} k))]
  [∀ u v : ℝ, HasDerivedCategory ((TopCat.of (Set.Icc u v)).Sheaf (ModuleCat.{0} k))]

/-- **The composition isomorphism through a restriction and a counit**, as natural
transformations: `TComp` followed by `TCompRestr` is the restriction along `pr₂₃` whiskered by
`T k a`, followed by `R(pr₂₃ ≫ q b)_*` of `TCompCounitNT` (`TComp_hom_app_TCompRestr_eq`). -/
lemma TComp_hom_TCompRestr {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (TComp k ha hb).hom ≫ TCompRestr k a b =
      Functor.whiskerLeft (T k a) (corrRestr k (pr₂₃ a b) (p b) (q b)) ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (TCompCounitNT k a b) (pushforwardPlus k (pr₂₃ a b ≫ q b)) := by
  refine NatTrans.ext (funext fun M => ?_)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_inv_app, Category.id_comp, TCompCounitNT_app]
  exact TComp_hom_app_TCompRestr_eq k ha hb M

/-- **The left unit law, inverse form.** For `0 ≤ b`, the inverse of `T0Iso` whiskered by `T k b`,
followed by `TComp` at `(0, b)`, is the left unitor followed by `T k b = T k (0 + b)`. -/
theorem whiskerRight_T0Iso_inv_TComp_hom {b : ℝ} (hb : 0 ≤ b) :
    Functor.whiskerRight (T0Iso k).inv (T k b) ≫ (TComp k le_rfl hb).hom =
      (Functor.leftUnitor (T k b)).hom ≫ eqToHom (congrArg (T k) (zero_add b).symm) := by
  have := isIso_TCompRestr k (le_refl (0 : ℝ)) hb
  rw [← cancel_mono (TCompRestr k 0 b), Category.assoc, TComp_hom_TCompRestr, Category.assoc,
    eqToHom_TCompRestr_zero_add]
  exact whiskerRight_whiskerLeft_unit_abs _ _ _ _ (whiskerRight_T0Iso_inv_TCompCounitNT k b)

/-- **The left unit law.** For `0 ≤ b`, `TCompOfEq` at `(0, b)` along `0 + b = b` is `T0Iso`
whiskered by `T k b`, followed by the left unitor. -/
theorem TCompOfEq_zero_left_hom {b : ℝ} (hb : 0 ≤ b) :
    (TCompOfEq k le_rfl hb (zero_add b)).hom =
      Functor.whiskerRight (T0Iso k).hom (T k b) ≫ (Functor.leftUnitor (T k b)).hom := by
  have e : (TComp k le_rfl hb).hom = Functor.whiskerRight (T0Iso k).hom (T k b) ≫
      (Functor.leftUnitor (T k b)).hom ≫ eqToHom (congrArg (T k) (zero_add b).symm) := by
    rw [← whiskerRight_T0Iso_inv_TComp_hom k hb, ← Category.assoc, ← Functor.whiskerRight_comp,
      Iso.hom_inv_id, Functor.whiskerRight_id', Category.id_comp]
  rw [TCompOfEq_hom, e, Category.assoc, Category.assoc, eqToHom_trans, eqToHom_refl,
    Category.comp_id]

omit [∀ a : ℝ, HasDerivedCategory ((D a).Sheaf (ModuleCat.{0} k))]
  [HasDerivedCategory (pt.Sheaf (ModuleCat.{0} k))]
  [∀ u v : ℝ, HasDerivedCategory ((TopCat.of (Set.Icc u v)).Sheaf (ModuleCat.{0} k))] in
/-- The identifications along `pr₁₃Of (add_zero a) = pr₁₂ a 0` after the restriction along
`pr₁₂ a 0`: the identification `R(pr₁₂ ≫ q a)_* = R(pr₂₃ ≫ q 0)_*`. -/
private lemma eqToHom_pr₁₃Of_add_zero (a : ℝ) :
    Functor.whiskerRight (eqToHom (congrArg (fun r => pullbackPlus k (r ≫ p a))
        (pr₁₃Of_add_zero a).symm)) (pushforwardPlus k (pr₁₂ a 0 ≫ q a)) ≫
      Functor.whiskerLeft (pullbackPlus k (pr₁₃Of (add_zero a) ≫ p a))
        (eqToHom (congrArg (fun r => pushforwardPlus k (r ≫ q a)) (pr₁₃Of_add_zero a).symm)) =
    Functor.whiskerLeft (pullbackPlus k (pr₁₂ a 0 ≫ p a))
      (eqToHom (congrArg (pushforwardPlus k) (pr₁₂_q_add_zero a))) := by
  rw [whiskerLeft_eqToHom_abs, whiskerLeft_eqToHom_abs, whiskerRight_eqToHom_abs, eqToHom_trans]
  rfl

/-- **The right unit law, inverse form.** For `0 ≤ a`, `T k a` whiskered with the inverse of
`T0Iso`, followed by `TComp` at `(a, 0)`, is the right unitor followed by
`T k a = T k (a + 0)`. -/
theorem whiskerLeft_T0Iso_inv_TComp_hom {a : ℝ} (ha : 0 ≤ a) :
    Functor.whiskerLeft (T k a) (T0Iso k).inv ≫ (TComp k ha le_rfl).hom =
      (Functor.rightUnitor (T k a)).hom ≫ eqToHom (congrArg (T k) (add_zero a).symm) := by
  have := isIso_TCompRestr k ha (le_refl (0 : ℝ))
  rw [← cancel_mono (TCompRestr k a 0)]
  conv_rhs => rw [Category.assoc, eqToHom_TCompRestr k (add_zero a),
    corrRestr_eq_of_eq k (pr₁₃Of_add_zero a), eqToHom_pr₁₃Of_add_zero]
  rw [Category.assoc, TComp_hom_TCompRestr]
  exact corrUnitIso_corrRestr_transportCounit k (pr₁₂ a 0) (p a) (q a) (pr₂₃ a 0)
    p_zero_eq_q_zero (pr₁₂_q a 0).symm (pr₁₂_q_add_zero a) _ (TCompCounitNT_eq k a 0) _ rfl

/-- **The right unit law.** For `0 ≤ a`, `TCompOfEq` at `(a, 0)` along `a + 0 = a` is `T k a`
whiskered with `T0Iso`, followed by the right unitor. -/
theorem TCompOfEq_zero_right_hom {a : ℝ} (ha : 0 ≤ a) :
    (TCompOfEq k ha le_rfl (add_zero a)).hom =
      Functor.whiskerLeft (T k a) (T0Iso k).hom ≫ (Functor.rightUnitor (T k a)).hom := by
  have e : (TComp k ha le_rfl).hom = Functor.whiskerLeft (T k a) (T0Iso k).hom ≫
      (Functor.rightUnitor (T k a)).hom ≫ eqToHom (congrArg (T k) (add_zero a).symm) := by
    rw [← whiskerLeft_T0Iso_inv_TComp_hom k ha, ← Category.assoc, ← Functor.whiskerLeft_comp,
      Iso.hom_inv_id, Functor.whiskerLeft_id', Category.id_comp]
  rw [TCompOfEq_hom, e, Category.assoc, Category.assoc, eqToHom_trans, eqToHom_refl,
    Category.comp_id]

omit [∀ a b : ℝ, HasDerivedCategory ((Z a b).Sheaf (ModuleCat.{0} k))]
  [HasDerivedCategory (pt.Sheaf (ModuleCat.{0} k))]
  [∀ u v : ℝ, HasDerivedCategory ((TopCat.of (Set.Icc u v)).Sheaf (ModuleCat.{0} k))] in
/-- The radius map `T_d ⟶ T_c` followed by `T k c = T k c'` is the radius map of `c' ≤ d`. -/
lemma restr_eqToHom {c c' d : ℝ} (h : c ≤ d) (e : c = c') :
    restr k h ≫ eqToHom (congrArg (T k) e) = restr k (e ▸ h) := by
  subst e
  rw [eqToHom_refl, Category.comp_id]

/-- **The augmentation law.** For `0 ≤ a`, `0 ≤ b`, the horizontal composite of the augmentations
`T_a ⟶ 𝟭` and `T_b ⟶ 𝟭`, followed by `𝟭 ⋙ 𝟭 = 𝟭`, is `TComp` followed by the augmentation
`T_{a+b} ⟶ 𝟭`. -/
theorem hcomp_aug_TComp_hom {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (aug k ha ◫ aug k hb) ≫ (Functor.leftUnitor (𝟭 _)).hom =
      (TComp k ha hb).hom ≫ aug k (add_nonneg ha hb) := by
  have h₀ := TCompOfEq_zero_left_hom k (le_refl (0 : ℝ))
  rw [TCompOfEq_hom] at h₀
  have hr := hcomp_restr_TComp_hom k (le_refl (0 : ℝ)) (le_refl (0 : ℝ)) ha hb
  rw [aug, aug, NatTrans.exchange, Category.assoc, hcomp_self_leftUnitor_abs,
    ← Category.assoc (Functor.whiskerRight _ _), ← h₀, ← Category.assoc, ← Category.assoc, hr,
    Category.assoc, Category.assoc, ← Category.assoc (restr k _),
    restr_eqToHom k _ (zero_add (0 : ℝ)), aug]

section bounded

/-- Whiskering a left whiskering on the right is a left whiskering of a right whiskering. -/
private lemma whiskerRight_whiskerLeft_abs {B C D E : Type*} [Category* B] [Category* C]
    [Category* D] [Category* E] (F : B ⥤ C) {G H : C ⥤ D} (α : G ⟶ H) (K : D ⥤ E) :
    Functor.whiskerRight (Functor.whiskerLeft F α) K =
      Functor.whiskerLeft F (Functor.whiskerRight α K) :=
  rfl

/-- **The left unit law on `Dᵇ`.** For `0 ≤ b`, the restriction of `TCompOfEq` at `(0, b)` along
`0 + b = b` to `Dᵇ(Sh(ℝ; k))` is `T0IsoB` whiskered by `TB k b`, followed by the left unitor. -/
theorem compIsoB_TCompOfEq_zero_left_hom {b : ℝ} (hb : 0 ≤ b) :
    (compIsoB k (TCompOfEq k le_rfl hb (zero_add b))).hom =
      Functor.whiskerRight (T0IsoB k).hom (TB k b) ≫ (Functor.leftUnitor (TB k b)).hom := by
  apply eq_of_whiskerRight_boundedToPlus
  rw [whiskerRight_compIsoB_hom, TCompOfEq_zero_left_hom, Functor.whiskerRight_comp,
    Functor.whiskerLeft_comp, whiskerRight_whiskerRight_restrictBounded, whiskerRight_T0IsoB_hom]
  rfl

/-- **The right unit law on `Dᵇ`.** For `0 ≤ a`, the restriction of `TCompOfEq` at `(a, 0)` along
`a + 0 = a` to `Dᵇ(Sh(ℝ; k))` is `TB k a` whiskered with `T0IsoB`, followed by the right
unitor. -/
theorem compIsoB_TCompOfEq_zero_right_hom {a : ℝ} (ha : 0 ≤ a) :
    (compIsoB k (TCompOfEq k ha le_rfl (add_zero a))).hom =
      Functor.whiskerLeft (TB k a) (T0IsoB k).hom ≫ (Functor.rightUnitor (TB k a)).hom := by
  apply eq_of_whiskerRight_boundedToPlus
  rw [whiskerRight_compIsoB_hom, TCompOfEq_zero_right_hom, Functor.whiskerRight_comp,
    Functor.whiskerLeft_comp, whiskerRight_whiskerLeft_abs, whiskerRight_T0IsoB_hom]
  exact congrArg₂ (· ≫ ·)
    (whiskerLeft_restrictBounded_whiskerLeft (T k a) (preservesBounded_T k a) (T0Iso k).hom).symm
    rfl

/-- The horizontal composite of the bounded augmentations agrees with the augmentation
of the sum through the bounded composition isomorphism. -/
theorem hcomp_augB_TCompB_hom {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (augB k ha ◫ augB k hb) ≫ (Functor.leftUnitor (𝟭 _)).hom =
      (TCompB k ha hb).hom ≫ augB k (add_nonneg ha hb) := by
  rw [hcomp_leftUnitor (augB k ha) (augB k hb)]
  apply eq_of_whiskerRight_boundedToPlus
  simp only [Functor.whiskerRight_comp, whiskerRight_TCompB_hom, whiskerRight_whiskerLeft_abs,
    whiskerRight_augB]
  have e := congrArg (Functor.whiskerLeft (boundedToPlus _)) (hcomp_aug_TComp_hom k ha hb)
  simp only [hcomp_leftUnitor (aug k ha) (aug k hb), Functor.whiskerLeft_comp] at e
  have h := whiskerLeft_restrictBounded_whiskerLeft (T k a) (preservesBounded_T k a) (aug k hb)
  exact (congrArg₂ (· ≫ ·) h rfl).trans e

end bounded

end TDA.Sheaf.BandConvolution
