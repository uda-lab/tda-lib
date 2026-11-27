import TDA.Sheaf.BandComposition
import TDA.Sheaf.BaseChangeRestriction

/-!
# Laws of the composition isomorphism of the band functors

`TDA.Sheaf.BandComposition` constructs `TComp k ha hb : T k a ⋙ T k b ≅ T k (a + b)` for `0 ≤ a`,
`0 ≤ b` on `Z a b = {(x, y, z) | dist x y ≤ a ∧ dist y z ≤ b}`. This file proves its compatibility
with the radius maps `restr` and records it on the bounded derived category.

* **Decomposition.** `TComp_hom_app_TCompRestr_eq`: `TComp` followed by the restriction
  `TCompRestr` along `pr₁₃` is the restriction `corrRestr` along `pr₂₃` at `T_a M`, followed by
  `R(pr₂₃ ≫ q b)_*` of the transported counit `TCompCounit k a b M` (the counit of `q a`
  transported along `pr₁₂`, `TCompCounit_eq`).
* **Radius maps.** `inclZ ha hb : Z a b ⟶ Z a' b'` for `a ≤ a'`, `b ≤ b'`;
  `restr_TCompRestr`: the radius map followed by `TCompRestr k a b` is `TCompRestr k a' b'`
  followed by the restriction along `inclZ`. With this, for `0 ≤ a ≤ a'`, `0 ≤ b ≤ b'`:
  - `whiskerRight_restr_TComp_hom`:
    `whiskerRight (restr k h) (T k b) ≫ (TComp k ha hb).hom =
      (TComp k (ha.trans h) hb).hom ≫ restr k (add_le_add h (le_refl b))`;
  - `whiskerLeft_restr_TComp_hom`:
    `whiskerLeft (T k a) (restr k h) ≫ (TComp k ha hb).hom =
      (TComp k ha (hb.trans h)).hom ≫ restr k (add_le_add (le_refl a) h)`;
  - `hcomp_restr_TComp_hom`:
    `(restr k h₁ ◫ restr k h₂) ≫ (TComp k ha hb).hom =
      (TComp k (ha.trans h₁) (hb.trans h₂)).hom ≫ restr k (add_le_add h₁ h₂)`.
* **Radii along equalities.** `pr₁₃Of h : Z a b ⟶ D c` for `a + b = c` (`pr₁₃Of_zero_add`,
  `pr₁₃Of_add_zero`), `eqToHom_TCompRestr`, and `TCompOfEq k ha hb h : T k a ⋙ T k b ≅ T k c`
  (`TCompOfEq_rfl`, `TCompOfEq_hom`). At `a = 0`: `T0Iso_eq_corrUnitIso`,
  `T0Iso_inv_TCompCounit` (the inverse of `T0Iso` against the transported counit is the
  identification along `p 0 = q 0`) and `eqToHom_TCompRestr_zero_add` (`TCompRestr k 0 b` is the
  restriction along `pr₂₃ 0 b`, since `x = y` on `Z 0 b`).

Derived categories are instance arguments: on the real line, on every band `D a`, on every
`Z a b`, on the point and on every compact interval `[u, v]`.
-/

noncomputable section
open CategoryTheory Limits TopologicalSpace

namespace TDA.Sheaf.BandConvolution

/-- The closed inclusion `Z a b ⟶ Z a' b'` for `a ≤ a'`, `b ≤ b'`. -/
def inclZ {a a' b b' : ℝ} (ha : a ≤ a') (hb : b ≤ b') : Z a b ⟶ Z a' b' :=
  TopCat.ofHom ⟨fun w => ⟨w.1, w.2.1.trans ha, w.2.2.trans hb⟩, by fun_prop⟩

/-- A composite of four morphisms, rewritten along a naturality square `nat`, a factorisation `hφ`
and a square `tr` whose left edge `ch` is a retraction of `ci₀`. -/
private lemma comp_four_eq {C : Type*} [Category* C] {A A' B B' E F : C} (r' : A ⟶ A')
    (ci : A' ⟶ B') (ci₀ : A ⟶ B) (Lr : B ⟶ B') (e : B' ⟶ E) (c : E ⟶ F) (ch : B ⟶ A)
    (Ψ : A ⟶ F) (Lφ : B ⟶ E) (nat : r' ≫ ci = ci₀ ≫ Lr) (hφ : Lr ≫ e = Lφ)
    (tr : ch ≫ Ψ = Lφ ≫ c) (hc : ci₀ ≫ ch = 𝟙 A) : r' ≫ ci ≫ e ≫ c = Ψ := by
  rw [reassoc_of% nat, reassoc_of% hφ, ← tr, reassoc_of% hc]

/-- The projection `(x, y, z) ↦ (x, z)` from `Z a b` to `D c` for `a + b = c`. -/
def pr₁₃Of {a b c : ℝ} (h : a + b = c) : Z a b ⟶ D c :=
  TopCat.ofHom ⟨fun w => ⟨(w.1.1, w.1.2.2), by
      rw [mem_band, ← h]
      exact dist_le_add_of_mem_bandChain w⟩, by fun_prop⟩

/-- On `Z 0 b`, where `x = y`, `pr₁₃Of (zero_add b)` is `pr₂₃ 0 b`. -/
lemma pr₁₃Of_zero_add (b : ℝ) : pr₁₃Of (zero_add b) = pr₂₃ 0 b :=
  TopCat.ext fun w => Subtype.ext (Prod.ext (dist_le_zero.1 w.2.1) rfl)

/-- On `Z a 0`, where `y = z`, `pr₁₃Of (add_zero a)` is `pr₁₂ a 0`. -/
lemma pr₁₃Of_add_zero (a : ℝ) : pr₁₃Of (add_zero a) = pr₁₂ a 0 :=
  TopCat.ext fun w => Subtype.ext (Prod.ext rfl (dist_le_zero.1 w.2.2).symm)

variable (k : Type) [Ring k] [HasDerivedCategory (realLine.Sheaf (ModuleCat.{0} k))]
  [∀ a : ℝ, HasDerivedCategory ((D a).Sheaf (ModuleCat.{0} k))]
  [∀ a b : ℝ, HasDerivedCategory ((Z a b).Sheaf (ModuleCat.{0} k))]

/-- **The transported counit.** `(pr₂₃ ≫ p b)⁻¹ T_a M = (pr₁₂ ≫ q a)⁻¹ R(q a)_* (p a)⁻¹ M ⟶
(pr₁₂ ≫ p a)⁻¹ M`: through `pr₂₃⁻¹ (p b)⁻¹ ≅ pr₁₂⁻¹ (q a)⁻¹` (the central square), `pr₁₂⁻¹` of the
derived counit of `q a` at `(p a)⁻¹ M`, then `pr₁₂⁻¹ (p a)⁻¹ ≅ (pr₁₂ ≫ p a)⁻¹`. -/
def TCompCounit (a b : ℝ) (M : DerivedCategory.Plus (realLine.Sheaf (ModuleCat.{0} k))) :
    (pullbackPlus k (pr₂₃ a b ≫ p b)).obj ((T k a).obj M) ⟶
      (pullbackPlus k (pr₁₂ a b ≫ p a)).obj M :=
  (pullbackPlusCompIso k (pr₂₃ a b) (p b)).inv.app ((T k a).obj M) ≫
    (pullbackPlusSquare k (pr₁₂_q a b)).app ((T k a).obj M) ≫
    (pullbackPlus k (pr₁₂ a b)).map ((derivedCounit k (q a)).app ((pullbackPlus k (p a)).obj M)) ≫
    (pullbackPlusCompIso k (pr₁₂ a b) (p a)).hom.app M

/-- `TCompCounit` through `(pr₁₂ ≫ q a)⁻¹ ≅ pr₁₂⁻¹ (q a)⁻¹`, using that the central square
`pr₁₂ ≫ q a = pr₂₃ ≫ p b` holds definitionally. -/
lemma TCompCounit_eq (a b : ℝ) (M : DerivedCategory.Plus (realLine.Sheaf (ModuleCat.{0} k))) :
    TCompCounit k a b M =
      (pullbackPlusCompIso k (pr₁₂ a b) (q a)).inv.app ((T k a).obj M) ≫
        (pullbackPlus k (pr₁₂ a b)).map ((derivedCounit k (q a)).app ((pullbackPlus k (p a)).obj M)) ≫
        (pullbackPlusCompIso k (pr₁₂ a b) (p a)).hom.app M := by
  have e₁ : TCompCounit k a b M =
      (eqToHom (congrArg (pullbackPlus k) (pr₁₂_q a b).symm)).app ((T k a).obj M) ≫
        (pullbackPlusCompIso k (pr₁₂ a b) (q a)).inv.app ((T k a).obj M) ≫
        (pullbackPlus k (pr₁₂ a b)).map ((derivedCounit k (q a)).app ((pullbackPlus k (p a)).obj M)) ≫
        (pullbackPlusCompIso k (pr₁₂ a b) (p a)).hom.app M := by
    simp only [TCompCounit, pullbackPlusSquare, NatTrans.comp_app, Category.assoc,
      Iso.inv_hom_id_app_assoc]
  exact e₁.trans (Category.id_comp _)

variable [HasDerivedCategory (pt.Sheaf (ModuleCat.{0} k))]
  [∀ u v : ℝ, HasDerivedCategory ((TopCat.of (Set.Icc u v)).Sheaf (ModuleCat.{0} k))]

/-- **The composition isomorphism through a restriction and a counit.** At `M`,
`TComp` followed by the restriction `TCompRestr` along `pr₁₃` is the restriction `corrRestr` along
`pr₂₃` of `T_b` at `T_a M`, followed by `R(pr₂₃ ≫ q b)_*` of the transported counit
`TCompCounit`: the base change of the central square is its unit part. -/
@[reassoc]
lemma TComp_hom_app_TCompRestr_eq {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (M : DerivedCategory.Plus (realLine.Sheaf (ModuleCat.{0} k))) :
    (TComp k ha hb).hom.app M ≫ (TCompRestr k a b).app M =
      (corrRestr k (pr₂₃ a b) (p b) (q b)).app ((T k a).obj M) ≫
        (pushforwardPlus k (pr₂₃ a b ≫ q b)).map (TCompCounit k a b M) := by
  have n := (pushforwardPlusCompIso k (pr₂₃ a b) (q b)).inv.naturality
    ((pullbackPlusSquare k (pr₁₂_q a b)).app ((T k a).obj M) ≫
      (pullbackPlus k (pr₁₂ a b)).map ((derivedCounit k (q a)).app ((pullbackPlus k (p a)).obj M)))
  simp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj, Functor.map_comp,
    Category.assoc] at n
  simp only [TComp_hom_app_TCompRestr, baseChange_app, corrRestr_app, TCompCounit,
    Functor.map_comp, Category.assoc, Functor.comp_obj, reassoc_of% n]
  simp only [← Functor.map_comp, Iso.hom_inv_id_app_assoc]

omit [HasDerivedCategory (pt.Sheaf (ModuleCat.{0} k))]
  [∀ u v : ℝ, HasDerivedCategory ((TopCat.of (Set.Icc u v)).Sheaf (ModuleCat.{0} k))] in
/-- **The restriction along `pr₁₃` against the radius maps.** For `a ≤ a'`, `b ≤ b'` the radius
map `T_{a'+b'} ⟶ T_{a+b}` followed by `TCompRestr k a b` is `TCompRestr k a' b'` followed by the
restriction along the inclusion `inclZ : Z a b ⟶ Z a' b'` (both are the restriction along
`pr₁₃ ≫ incl = inclZ ≫ pr₁₃`, by `corrRestr_comp`). -/
lemma restr_TCompRestr {a a' b b' : ℝ} (ha : a ≤ a') (hb : b ≤ b') :
    restr k (add_le_add ha hb) ≫ TCompRestr k a b =
      TCompRestr k a' b' ≫
        corrRestr k (inclZ ha hb) (pr₁₂ a' b' ≫ p a') (pr₂₃ a' b' ≫ q b') :=
  (corrRestr_comp k (pr₁₃ a b) (incl (add_le_add ha hb)) (p _) (q _)).trans
    (corrRestr_comp k (inclZ ha hb) (pr₁₃ a' b') (p _) (q _)).symm

omit [HasDerivedCategory (pt.Sheaf (ModuleCat.{0} k))]
  [∀ u v : ℝ, HasDerivedCategory ((TopCat.of (Set.Icc u v)).Sheaf (ModuleCat.{0} k))] in
/-- The radius map of `T_b` followed by the restriction along `pr₂₃ a b`. -/
private lemma restr_corrRestr_pr₂₃ (a : ℝ) {b b' : ℝ} (hb : b ≤ b') :
    restr k hb ≫ corrRestr k (pr₂₃ a b) (p b) (q b) =
      corrRestr k (pr₂₃ a b') (p b') (q b') ≫
        corrRestr k (inclZ (le_refl a) hb) (pr₂₃ a b' ≫ p b') (pr₂₃ a b' ≫ q b') :=
  (corrRestr_comp k (pr₂₃ a b) (incl hb) (p _) (q _)).trans
    (corrRestr_comp k (inclZ (le_refl a) hb) (pr₂₃ a b') (p _) (q _)).symm

omit [HasDerivedCategory (pt.Sheaf (ModuleCat.{0} k))]
  [∀ u v : ℝ, HasDerivedCategory ((TopCat.of (Set.Icc u v)).Sheaf (ModuleCat.{0} k))] in
/-- The restriction along `pr₂₃ a b = inclZ ≫ pr₂₃ a' b`. -/
private lemma corrRestr_pr₂₃_inclZ {a a' : ℝ} (ha : a ≤ a') (b : ℝ) :
    corrRestr k (pr₂₃ a b) (p b) (q b) =
      corrRestr k (pr₂₃ a' b) (p b) (q b) ≫
        corrRestr k (inclZ ha (le_refl b)) (pr₂₃ a' b ≫ p b) (pr₂₃ a' b ≫ q b) :=
  (corrRestr_comp k (inclZ ha (le_refl b)) (pr₂₃ a' b) (p _) (q _)).symm

omit [HasDerivedCategory (pt.Sheaf (ModuleCat.{0} k))]
  [∀ u v : ℝ, HasDerivedCategory ((TopCat.of (Set.Icc u v)).Sheaf (ModuleCat.{0} k))] in
/-- The transported counits on `Z a b` and `Z a b'` along `inclZ`. -/
private lemma TCompCounit_inclZ_right (a : ℝ) {b b' : ℝ} (hb : b ≤ b')
    (M : DerivedCategory.Plus (realLine.Sheaf (ModuleCat.{0} k))) :
    (pullbackPlusCompIso k (inclZ (le_refl a) hb) (pr₂₃ a b' ≫ p b')).hom.app ((T k a).obj M) ≫
        TCompCounit k a b M =
      (pullbackPlus k (inclZ (le_refl a) hb)).map (TCompCounit k a b' M) ≫
        (pullbackPlusCompIso k (inclZ (le_refl a) hb) (pr₁₂ a b' ≫ p a)).hom.app M := by
  rw [TCompCounit_eq, TCompCounit_eq]
  exact pullbackPlusCompIso_transport k (inclZ (le_refl a) hb) (pr₁₂ a b') (q a) (p a) ((T k a).obj M) M
    ((derivedCounit k (q a)).app ((pullbackPlus k (p a)).obj M))

omit [HasDerivedCategory (pt.Sheaf (ModuleCat.{0} k))]
  [∀ u v : ℝ, HasDerivedCategory ((TopCat.of (Set.Icc u v)).Sheaf (ModuleCat.{0} k))] in
/-- The restriction along `inclZ : Z a b ⟶ Z a b'` against the transported counits. -/
private lemma corrRestr_TCompCounit_right (a : ℝ) {b b' : ℝ} (h : b ≤ b')
    (M : DerivedCategory.Plus (realLine.Sheaf (ModuleCat.{0} k))) :
    (corrRestr k (inclZ (le_refl a) h) (pr₂₃ a b' ≫ p b') (pr₂₃ a b' ≫ q b')).app
        ((T k a).obj M) ≫ (pushforwardPlus k (pr₂₃ a b ≫ q b)).map (TCompCounit k a b M) =
      (pushforwardPlus k (pr₂₃ a b' ≫ q b')).map (TCompCounit k a b' M) ≫
        (corrRestr k (inclZ (le_refl a) h) (pr₁₂ a b' ≫ p a) (pr₂₃ a b' ≫ q b')).app M :=
  corrRestr_app_comp_map k (inclZ (le_refl a) h) (pr₂₃ a b' ≫ p b') (pr₁₂ a b' ≫ p a)
    (pr₂₃ a b' ≫ q b') ((T k a).obj M) M (TCompCounit k a b' M) (TCompCounit k a b M)
    (TCompCounit_inclZ_right k a h M)

/-- **The composition isomorphism is natural in the second radius.** For `0 ≤ a`, `0 ≤ b ≤ b'`,
`T_a` of the radius map `T_{b'} ⟶ T_b` followed by `TComp k ha hb` is `TComp` at `(a, b')` followed by
the radius map `T_{a+b'} ⟶ T_{a+b}`. -/
theorem whiskerLeft_restr_TComp_hom {a b b' : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : b ≤ b') :
    Functor.whiskerLeft (T k a) (restr k h) ≫ (TComp k ha hb).hom =
      (TComp k ha (hb.trans h)).hom ≫ restr k (add_le_add (le_refl a) h) := by
  have := isIso_TCompRestr k ha hb
  refine NatTrans.ext (funext fun M => ?_)
  rw [← cancel_mono ((TCompRestr k a b).app M)]
  have hr := congr_app (restr_TCompRestr k (le_refl a) h) M
  have hc := congr_app (restr_corrRestr_pr₂₃ k a h) ((T k a).obj M)
  simp only [NatTrans.comp_app] at hr hc
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Category.assoc]
  exact (congrArg (fun x => (restr k h).app ((T k a).obj M) ≫ x)
      (TComp_hom_app_TCompRestr_eq k ha hb M)).trans <|
    (Category.assoc _ _ _).symm.trans <|
    (congrArg (fun x => x ≫ (pushforwardPlus k (pr₂₃ a b ≫ q b)).map (TCompCounit k a b M)) hc).trans <|
    (Category.assoc _ _ _).trans <|
    (congrArg (fun x => (corrRestr k (pr₂₃ a b') (p b') (q b')).app ((T k a).obj M) ≫ x)
      (corrRestr_TCompCounit_right k a h M)).trans <|
    (Category.assoc _ _ _).symm.trans <|
    (congrArg (fun x => x ≫ (corrRestr k (inclZ (le_refl a) h) (pr₁₂ a b' ≫ p a)
      (pr₂₃ a b' ≫ q b')).app M) (TComp_hom_app_TCompRestr_eq k ha (hb.trans h) M).symm).trans <|
    (Category.assoc _ _ _).trans <|
    congrArg (fun x => (TComp k ha (hb.trans h)).hom.app M ≫ x) hr.symm

omit [HasDerivedCategory (pt.Sheaf (ModuleCat.{0} k))]
  [∀ u v : ℝ, HasDerivedCategory ((TopCat.of (Set.Icc u v)).Sheaf (ModuleCat.{0} k))] in
/-- `(pr₂₃ ≫ p b)⁻¹` of the radius map of `T_a`, followed by the transported counit of `Z a b`, is
the transport along `pr₁₂ ≫ incl` of the counit of `q a'` (`corrRestr_counit`). -/
private lemma TCompCounit_restr_left {a a' : ℝ} (h : a ≤ a') (b : ℝ)
    (M : DerivedCategory.Plus (realLine.Sheaf (ModuleCat.{0} k))) :
    (pullbackPlus k (pr₂₃ a b ≫ p b)).map ((restr k h).app M) ≫ TCompCounit k a b M =
      (pullbackPlusCompIso k (pr₁₂ a b ≫ incl h) (q a')).inv.app ((T k a').obj M) ≫
        (pullbackPlus k (pr₁₂ a b ≫ incl h)).map
          ((derivedCounit k (q a')).app ((pullbackPlus k (p a')).obj M)) ≫
        (pullbackPlusCompIso k (pr₁₂ a b ≫ incl h) (p a')).hom.app M := by
  have nat := (pullbackPlusCompIso k (pr₁₂ a b) (q a)).inv.naturality ((restr k h).app M)
  have cnt := corrRestr_counit k (incl h) (p a') (q a') M
  have tr := pullbackPlusCompIso_transport k (pr₁₂ a b) (incl h) (q a') (p a') ((T k a').obj M) M
    ((derivedCounit k (q a')).app ((pullbackPlus k (p a')).obj M))
  rw [TCompCounit_eq]
  exact comp_four_eq _ _ _ _ _ _ _ _ _ nat
    ((CategoryTheory.Functor.map_comp _ _ _).symm.trans
      (congrArg (pullbackPlus k (pr₁₂ a b)).map cnt)) tr
    (Iso.inv_hom_id_app (pullbackPlusCompIso k (pr₁₂ a b) (q a)) ((T k a').obj M))

omit [HasDerivedCategory (pt.Sheaf (ModuleCat.{0} k))]
  [∀ u v : ℝ, HasDerivedCategory ((TopCat.of (Set.Icc u v)).Sheaf (ModuleCat.{0} k))] in
/-- The transported counits on `Z a b` and `Z a' b` along `inclZ`, with the radius map of `T_a`. -/
private lemma TCompCounit_inclZ_left {a a' : ℝ} (h : a ≤ a') (b : ℝ)
    (M : DerivedCategory.Plus (realLine.Sheaf (ModuleCat.{0} k))) :
    (pullbackPlusCompIso k (inclZ h (le_refl b)) (pr₂₃ a' b ≫ p b)).hom.app ((T k a').obj M) ≫
        (pullbackPlus k (pr₂₃ a b ≫ p b)).map ((restr k h).app M) ≫ TCompCounit k a b M =
      (pullbackPlus k (inclZ h (le_refl b))).map (TCompCounit k a' b M) ≫
        (pullbackPlusCompIso k (inclZ h (le_refl b)) (pr₁₂ a' b ≫ p a')).hom.app M := by
  exact (congrArg (fun x =>
      (pullbackPlusCompIso k (inclZ h (le_refl b)) (pr₂₃ a' b ≫ p b)).hom.app ((T k a').obj M) ≫ x)
      (TCompCounit_restr_left k h b M)).trans <|
    (pullbackPlusCompIso_transport k (inclZ h (le_refl b)) (pr₁₂ a' b) (q a') (p a')
      ((T k a').obj M) M ((derivedCounit k (q a')).app ((pullbackPlus k (p a')).obj M))).trans <|
    (congrArg (fun x => (pullbackPlus k (inclZ h (le_refl b))).map x ≫
      (pullbackPlusCompIso k (inclZ h (le_refl b)) (pr₁₂ a' b ≫ p a')).hom.app M)
      (TCompCounit_eq k a' b M)).symm

omit [HasDerivedCategory (pt.Sheaf (ModuleCat.{0} k))]
  [∀ u v : ℝ, HasDerivedCategory ((TopCat.of (Set.Icc u v)).Sheaf (ModuleCat.{0} k))] in
/-- The restriction along `inclZ : Z a b ⟶ Z a' b` against the transported counits. -/
private lemma corrRestr_TCompCounit_left {a a' : ℝ} (h : a ≤ a') (b : ℝ)
    (M : DerivedCategory.Plus (realLine.Sheaf (ModuleCat.{0} k))) :
    (corrRestr k (inclZ h (le_refl b)) (pr₂₃ a' b ≫ p b) (pr₂₃ a' b ≫ q b)).app
        ((T k a').obj M) ≫ (pushforwardPlus k (pr₂₃ a b ≫ q b)).map
          ((pullbackPlus k (pr₂₃ a b ≫ p b)).map ((restr k h).app M) ≫ TCompCounit k a b M) =
      (pushforwardPlus k (pr₂₃ a' b ≫ q b)).map (TCompCounit k a' b M) ≫
        (corrRestr k (inclZ h (le_refl b)) (pr₁₂ a' b ≫ p a') (pr₂₃ a' b ≫ q b)).app M :=
  corrRestr_app_comp_map k (inclZ h (le_refl b)) (pr₂₃ a' b ≫ p b) (pr₁₂ a' b ≫ p a')
    (pr₂₃ a' b ≫ q b) ((T k a').obj M) M (TCompCounit k a' b M)
    ((pullbackPlus k (pr₂₃ a b ≫ p b)).map ((restr k h).app M) ≫ TCompCounit k a b M)
    (TCompCounit_inclZ_left k h b M)

/-- **The composition isomorphism is natural in the first radius.** For `0 ≤ a ≤ a'`, `0 ≤ b`, the
radius map `T_{a'} ⟶ T_a` whiskered by `T_b`, followed by `TComp k ha hb`, is `TComp` at `(a', b)`
followed by the radius map `T_{a'+b} ⟶ T_{a+b}`. -/
theorem whiskerRight_restr_TComp_hom {a a' b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ≤ a') :
    Functor.whiskerRight (restr k h) (T k b) ≫ (TComp k ha hb).hom =
      (TComp k (ha.trans h) hb).hom ≫ restr k (add_le_add h (le_refl b)) := by
  have := isIso_TCompRestr k ha hb
  refine NatTrans.ext (funext fun M => ?_)
  rw [← cancel_mono ((TCompRestr k a b).app M)]
  have hr := congr_app (restr_TCompRestr k h (le_refl b)) M
  have hc := congr_app (corrRestr_pr₂₃_inclZ k h b) ((T k a').obj M)
  have nat := (corrRestr k (pr₂₃ a b) (p b) (q b)).naturality ((restr k h).app M)
  simp only [NatTrans.comp_app] at hr hc
  simp only [Functor.comp_map] at nat
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Category.assoc]
  refine (congrArg (fun x => (T k b).map ((restr k h).app M) ≫ x)
    (TComp_hom_app_TCompRestr_eq k ha hb M)).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (fun x => x ≫ (pushforwardPlus k (pr₂₃ a b ≫ q b)).map (TCompCounit k a b M))
    nat).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (fun x => (corrRestr k (pr₂₃ a b) (p b) (q b)).app ((T k a').obj M) ≫ x)
    (CategoryTheory.Functor.map_comp (pushforwardPlus k (pr₂₃ a b ≫ q b)) _ _).symm).trans ?_
  refine (congrArg (fun x => x ≫ (pushforwardPlus k (pr₂₃ a b ≫ q b)).map
    ((pullbackPlus k (pr₂₃ a b ≫ p b)).map ((restr k h).app M) ≫ TCompCounit k a b M)) hc).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (fun x => (corrRestr k (pr₂₃ a' b) (p b) (q b)).app ((T k a').obj M) ≫ x)
    (corrRestr_TCompCounit_left k h b M)).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (fun x => x ≫ (corrRestr k (inclZ h (le_refl b)) (pr₁₂ a' b ≫ p a')
    (pr₂₃ a' b ≫ q b)).app M) (TComp_hom_app_TCompRestr_eq k (ha.trans h) hb M).symm).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  exact congrArg (fun x => (TComp k (ha.trans h) hb).hom.app M ≫ x) hr.symm

/-- **The composition isomorphism is natural in both radii.** For `0 ≤ a ≤ a'`, `0 ≤ b ≤ b'`, the
horizontal composite `restr ◫ restr : T_{a'} ⋙ T_{b'} ⟶ T_a ⋙ T_b` followed by `TComp k ha hb` is
`TComp` at `(a', b')` followed by the radius map `T_{a'+b'} ⟶ T_{a+b}`. -/
theorem hcomp_restr_TComp_hom {a a' b b' : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h₁ : a ≤ a')
    (h₂ : b ≤ b') :
    (restr k h₁ ◫ restr k h₂) ≫ (TComp k ha hb).hom =
      (TComp k (ha.trans h₁) (hb.trans h₂)).hom ≫ restr k (add_le_add h₁ h₂) := by
  have e : restr k h₁ ◫ restr k h₂ =
      Functor.whiskerLeft (T k a') (restr k h₂) ≫ Functor.whiskerRight (restr k h₁) (T k b) := by
    ext M
    rfl
  rw [e, Category.assoc, whiskerRight_restr_TComp_hom, ← Category.assoc,
    whiskerLeft_restr_TComp_hom, Category.assoc, restr_trans]

omit [HasDerivedCategory (pt.Sheaf (ModuleCat.{0} k))]
  [∀ u v : ℝ, HasDerivedCategory ((TopCat.of (Set.Icc u v)).Sheaf (ModuleCat.{0} k))] in
/-- **`TCompRestr` along `a + b = c`.** The identification `T_c = T_{a+b}` followed by
`TCompRestr k a b` is the restriction along `pr₁₃Of h : Z a b ⟶ D c`, `(x, y, z) ↦ (x, z)`. -/
lemma eqToHom_TCompRestr {a b c : ℝ} (h : a + b = c) :
    eqToHom (congrArg (T k) h.symm) ≫ TCompRestr k a b = corrRestr k (pr₁₃Of h) (p c) (q c) := by
  subst h
  rw [eqToHom_refl, Category.id_comp]
  rfl

omit [∀ a b : ℝ, HasDerivedCategory ((Z a b).Sheaf (ModuleCat.{0} k))]
  [HasDerivedCategory (pt.Sheaf (ModuleCat.{0} k))]
  [∀ u v : ℝ, HasDerivedCategory ((TopCat.of (Set.Icc u v)).Sheaf (ModuleCat.{0} k))] in
/-- `T0Iso` is the unit isomorphism of the correspondence `(p 0, q 0)` with equal legs. -/
lemma T0Iso_eq_corrUnitIso : T0Iso k = corrUnitIso k p_zero_eq_q_zero := rfl

omit [HasDerivedCategory (pt.Sheaf (ModuleCat.{0} k))]
  [∀ u v : ℝ, HasDerivedCategory ((TopCat.of (Set.Icc u v)).Sheaf (ModuleCat.{0} k))] in
/-- **The unit against the transported counit.** On `Z 0 b`, `(pr₂₃ ≫ p b)⁻¹` of the inverse of
`T0Iso` followed by the transported counit `TCompCounit k 0 b` is the identification
`(pr₁₂ ≫ q 0)⁻¹ M = (pr₁₂ ≫ p 0)⁻¹ M` along `p 0 = q 0`. -/
lemma T0Iso_inv_TCompCounit (b : ℝ)
    (M : DerivedCategory.Plus (realLine.Sheaf (ModuleCat.{0} k))) :
    (pullbackPlus k (pr₂₃ 0 b ≫ p b)).map ((T0Iso k).inv.app M) ≫ TCompCounit k 0 b M =
      eqToHom (congrArg (fun r => (pullbackPlus k (pr₁₂ 0 b ≫ r)).obj M)
        p_zero_eq_q_zero.symm) := by
  rw [TCompCounit_eq, T0Iso_eq_corrUnitIso]
  exact pullbackPlus_map_corrUnitIso_inv_app_transport k (pr₁₂ 0 b) p_zero_eq_q_zero M

omit [HasDerivedCategory (pt.Sheaf (ModuleCat.{0} k))]
  [∀ u v : ℝ, HasDerivedCategory ((TopCat.of (Set.Icc u v)).Sheaf (ModuleCat.{0} k))] in
/-- **`TCompRestr` at `a = 0`.** Since `x = y` on `Z 0 b`, the identification `T_b = T_{0+b}`
followed by `TCompRestr k 0 b` is the restriction along `pr₂₃ 0 b` followed by the identification
`(pr₂₃ ≫ p b)⁻¹ = (pr₁₃Of (zero_add b) ≫ p b)⁻¹` (`pr₁₃Of_zero_add`). -/
lemma eqToHom_TCompRestr_zero_add (b : ℝ) :
    eqToHom (congrArg (T k) (zero_add b).symm) ≫ TCompRestr k 0 b =
      corrRestr k (pr₂₃ 0 b) (p b) (q b) ≫
        Functor.whiskerRight (eqToHom (congrArg (fun r => pullbackPlus k (r ≫ p b))
          (pr₁₃Of_zero_add b).symm)) (pushforwardPlus k (pr₂₃ 0 b ≫ q b)) := by
  have e : eqToHom (congrArg (fun r => pushforwardPlus k (r ≫ q b)) (pr₁₃Of_zero_add b).symm) =
      𝟙 (pushforwardPlus k (pr₂₃ 0 b ≫ q b)) := rfl
  have e' : Functor.whiskerLeft (pullbackPlus k (pr₁₃Of (zero_add b) ≫ p b))
      (eqToHom (congrArg (fun r => pushforwardPlus k (r ≫ q b)) (pr₁₃Of_zero_add b).symm)) =
      𝟙 (pullbackPlus k (pr₁₃Of (zero_add b) ≫ p b) ⋙ pushforwardPlus k (pr₂₃ 0 b ≫ q b)) :=
    (congrArg (Functor.whiskerLeft (pullbackPlus k (pr₁₃Of (zero_add b) ≫ p b))) e).trans
      (Functor.whiskerLeft_id' _)
  rw [eqToHom_TCompRestr k (zero_add b), corrRestr_eq_of_eq k (pr₁₃Of_zero_add b), e']
  exact congrArg (fun x => corrRestr k (pr₂₃ 0 b) (p b) (q b) ≫ x) (Category.comp_id _)

/-- `TComp` followed by the identification `T k (a + b) = T k c` along `a + b = c`. -/
def TCompOfEq {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a + b = c) : T k a ⋙ T k b ≅ T k c :=
  TComp k ha hb ≪≫ eqToIso (congrArg (T k) h)

/-- `TCompOfEq` along `rfl` is `TComp`. -/
@[simp]
lemma TCompOfEq_rfl {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    TCompOfEq k ha hb (rfl : a + b = a + b) = TComp k ha hb := by
  rw [TCompOfEq, eqToIso_refl, Iso.trans_refl]

/-- The underlying morphism of `TCompOfEq`. -/
lemma TCompOfEq_hom {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a + b = c) :
    (TCompOfEq k ha hb h).hom = (TComp k ha hb).hom ≫ eqToHom (congrArg (T k) h) :=
  rfl

end TDA.Sheaf.BandConvolution
