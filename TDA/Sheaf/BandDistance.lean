import TDA.Sheaf.BandCompositionAssociativity
import Mathlib.Basic.ENNReal.Operations

/-!
# Extended distance for real-band convolution

A finite-radius witness uses the composition isomorphism and augmentation of the
real-band functors. Witnesses enlarge along the radius maps and compose by adding radii.
The extended distance is the infimum of radii admitting a witness.
-/

noncomputable section

open CategoryTheory
open scoped NNReal ENNReal

namespace TDA.Sheaf.BandConvolution

variable (k : Type) [Ring k]
  [HasDerivedCategory (realLine.Sheaf (ModuleCat k))]
  [∀ a : ℝ, HasDerivedCategory ((D a).Sheaf (ModuleCat k))]
  [∀ a b : ℝ, HasDerivedCategory ((Z a b).Sheaf (ModuleCat k))]
  [HasDerivedCategory (pt.Sheaf (ModuleCat k))]
  [∀ u v : ℝ, HasDerivedCategory ((TopCat.of (Set.Icc u v)).Sheaf (ModuleCat k))]

local notation "D⁺[" k "]" => DerivedCategory.Plus (realLine.Sheaf (ModuleCat k))

/-- The two maps of a band witness compose to the augmentations at twice the radius. -/
structure Witness {ε : ℝ} (hε : 0 ≤ ε) (F G : D⁺[k]) where
  hom : (T k ε).obj F ⟶ G
  inv : (T k ε).obj G ⟶ F
  hom_inv : (TComp k hε hε).inv.app F ≫
    (T k ε).map hom ≫ inv = (aug k (add_nonneg hε hε)).app F
  inv_hom : (TComp k hε hε).inv.app G ≫
    (T k ε).map inv ≫ hom = (aug k (add_nonneg hε hε)).app G

variable {k}
variable {F G H : D⁺[k]} {ε δ : ℝ} {hε : 0 ≤ ε} {hδ : 0 ≤ δ}

namespace Witness

/-- Exchange the two objects of a witness. -/
def symm (w : Witness k hε F G) : Witness k hε G F :=
  ⟨w.inv, w.hom, w.inv_hom, w.hom_inv⟩

end Witness

-- Compose two maps indexed by radii, with the target radius named by an equality.
private def bandCompose {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a + b = c)
    (f : (T k a).obj F ⟶ G) (g : (T k b).obj G ⟶ H) : (T k c).obj F ⟶ H :=
  (TCompOfEq k ha hb h).inv.app F ≫ (T k b).map f ≫ g

private theorem sum_nonneg {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : a + b = c) : 0 ≤ c := h ▸ add_nonneg ha hb

private theorem bandCompose_assoc {a b c d e r : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hd : a + b = d) (he : b + c = e) (hr : d + c = r)
    {I : D⁺[k]} (f : (T k a).obj F ⟶ G) (g : (T k b).obj G ⟶ H)
    (l : (T k c).obj H ⟶ I) :
    bandCompose (sum_nonneg ha hb hd) hc hr (bandCompose ha hb hd f g) l =
      bandCompose ha (sum_nonneg hb hc he) (by rw [← hr, ← hd, ← he, add_assoc])
        f (bandCompose hb hc he g l) := by
  subst d
  subst e
  subst r
  have h := NatTrans.congr_app (TComp_assoc_hom k ha hb hc) F
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Category.id_comp, Functor.comp_obj] at h
  simp only [bandCompose, TCompOfEq_rfl, Functor.map_comp, Category.assoc]
  have hn : (T k (b + c)).map f ≫ (TComp k hb hc).inv.app G =
      (TComp k hb hc).inv.app ((T k a).obj F) ≫ (T k c).map ((T k b).map f) :=
    (TComp k hb hc).inv.naturality f
  have hn' := congrArg (fun m => m ≫ (T k c).map g ≫ l) hn
  simp only [Category.assoc] at hn'
  erw [hn']
  let m := (T k c).map ((TComp k ha hb).hom.app F) ≫
    (TComp k (add_nonneg ha hb) hc).hom.app F
  apply (cancel_epi m).mp
  have hm : m = (TComp k hb hc).hom.app ((T k a).obj F) ≫
      (TCompOfEq k ha (add_nonneg hb hc) (add_assoc a b c).symm).hom.app F := h
  conv_rhs => rw [hm]
  simp only [m, Category.assoc, Iso.hom_inv_id_app_assoc, ← Functor.map_comp_assoc]

private theorem bandCompose_restr {a b a' b' : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    {c c' : ℝ} (e : a + b = c) (e' : a' + b' = c')
    (h : a ≤ a') (h' : b ≤ b') (f : (T k a).obj F ⟶ G) (g : (T k b).obj G ⟶ H) :
    bandCompose (ha.trans h) (hb.trans h') e' ((restr k h).app F ≫ f)
      ((restr k h').app G ≫ g) =
        (restr k (show c ≤ c' by rw [← e, ← e']; exact add_le_add h h')).app F ≫
          bandCompose ha hb e f g := by
  subst c
  subst c'
  have he := NatTrans.congr_app (hcomp_restr_TComp_hom k ha hb h h') F
  simp only [NatTrans.comp_app, NatTrans.hcomp_app, Category.assoc] at he
  apply (cancel_epi ((TComp k (ha.trans h) (hb.trans h')).hom.app F)).mp
  simp only [bandCompose, TCompOfEq_rfl, Category.assoc, Iso.hom_inv_id_app_assoc,
    Functor.map_comp]
  rw [(restr k h').naturality_assoc f, (restr k h').naturality_assoc ((restr k h).app F),
    ← reassoc_of% he, Iso.hom_inv_id_app_assoc]
  rfl

private theorem bandCompose_aug_left {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (e : a + b = c)
    (g : (T k b).obj F ⟶ G) :
    bandCompose ha hb e ((aug k ha).app F) g =
      (restr k (show b ≤ c by linarith)).app F ≫ g := by
  subst c
  have h := NatTrans.congr_app
    (whiskerRight_restr_TComp_hom k (le_refl (0 : ℝ)) hb ha) F
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.comp_obj] at h
  have hzero := NatTrans.congr_app (TCompOfEq_zero_left_hom k hb) F
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.leftUnitor_hom_app,
    Functor.id_obj] at hzero
  erw [Category.comp_id] at hzero
  have hr := NatTrans.congr_app
    (restr_eqToHom k (add_le_add ha (le_refl b)) (zero_add b)) F
  simp only [NatTrans.comp_app] at hr
  apply (cancel_epi ((TComp k ha hb).hom.app F)).mp
  simp only [bandCompose, TCompOfEq_rfl, Category.assoc, Iso.hom_inv_id_app_assoc,
    aug, NatTrans.comp_app, Functor.map_comp]
  rw [← hzero, TCompOfEq_hom, NatTrans.comp_app]
  simp only [Category.assoc]
  erw [reassoc_of% h, reassoc_of% hr]


private theorem bandCompose_aug_right {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (e : a + b = c)
    (f : (T k a).obj F ⟶ G) :
    bandCompose ha hb e f ((aug k hb).app G) =
      (restr k (show a ≤ c by linarith)).app F ≫ f := by
  subst c
  have h := NatTrans.congr_app
    (whiskerLeft_restr_TComp_hom k ha (le_refl (0 : ℝ)) hb) F
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.comp_obj] at h
  have hzero := NatTrans.congr_app (TCompOfEq_zero_right_hom k ha) F
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.rightUnitor_hom_app] at hzero
  have hunit := hzero.trans (Category.comp_id _)
  have hr := NatTrans.congr_app
    (restr_eqToHom k (add_le_add (le_refl a) hb) (add_zero a)) F
  simp only [NatTrans.comp_app] at hr
  have hf : (T k b).map f ≫ (aug k hb).app G = (aug k hb).app ((T k a).obj F) ≫ f :=
    (aug k hb).naturality f
  apply (cancel_epi ((TComp k ha hb).hom.app F)).mp
  simp only [bandCompose, TCompOfEq_rfl, Iso.hom_inv_id_app_assoc, hf]
  rw [aug, NatTrans.comp_app, ← hunit, TCompOfEq_hom, NatTrans.comp_app]
  simp only [Category.assoc]
  erw [reassoc_of% h, reassoc_of% hr]

private theorem convolution_witness_inv_hom (F : D⁺[k]) (hε : 0 ≤ ε) :
    (TComp k hε hε).inv.app ((T k ε).obj F) ≫
      (T k ε).map ((TComp k hε hε).hom.app F ≫ (aug k (add_nonneg hε hε)).app F) =
        (aug k (add_nonneg hε hε)).app ((T k ε).obj F) := by
  let h₂ := add_nonneg hε hε
  let μ := TComp k hε hε
  let L := TComp k h₂ hε
  let R := TCompOfEq k hε h₂ (add_assoc ε ε ε).symm
  let Y := (T k ε).obj F
  have hr : ε ≤ ε + ε + ε := (le_add_of_nonneg_right hε).trans (le_add_of_nonneg_right hε)
  have hl : L.inv.app F ≫ (T k ε).map ((aug k h₂).app F) = (restr k hr).app F := by
    have hh := bandCompose_aug_left (F := F) h₂ hε rfl (𝟙 Y)
    simp only [bandCompose, TCompOfEq_rfl] at hh
    erw [Category.comp_id, Category.comp_id] at hh
    exact hh
  have hright : R.inv.app F ≫ (aug k h₂).app Y = (restr k hr).app F := by
    have hh := bandCompose_aug_right (F := F) hε h₂ (add_assoc ε ε ε).symm (𝟙 Y)
    simp only [bandCompose] at hh
    erw [(T k (ε + ε)).map_id Y, Category.id_comp, Category.comp_id] at hh
    exact hh
  have h := NatTrans.congr_app (TComp_assoc_hom k hε hε hε) F
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Category.id_comp, Functor.comp_obj] at h
  have ha : R.inv.app F ≫ μ.inv.app Y ≫ (T k ε).map (μ.hom.app F) = L.inv.app F := by
    let e := (T k ε).mapIso (μ.app F) ≪≫ L.app F
    apply (cancel_epi e.hom).mp
    change ((T k ε).map (μ.hom.app F) ≫ L.hom.app F) ≫ _ =
      ((T k ε).map (μ.hom.app F) ≫ L.hom.app F) ≫ _
    have he : (T k ε).map (μ.hom.app F) ≫ L.hom.app F = μ.hom.app Y ≫ R.hom.app F := h
    conv_lhs => rw [he]
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
    erw [L.hom_inv_id_app F, Category.comp_id]
  apply (cancel_epi (R.inv.app F)).mp
  rw [(T k ε).map_comp]
  let u := μ.inv.app Y
  let v := (T k ε).map (μ.hom.app F)
  let w := (T k ε).map ((aug k h₂).app F)
  let r := R.inv.app F
  change r ≫ u ≫ v ≫ w = _
  calc
    r ≫ u ≫ v ≫ w = r ≫ (u ≫ v) ≫ w :=
      congrArg (r ≫ ·) (Category.assoc u v w).symm
    _ = (r ≫ u ≫ v) ≫ w := (Category.assoc r (u ≫ v) w).symm
    _ = L.inv.app F ≫ w := congrArg (· ≫ w) ha
    _ = _ := hl.trans hright.symm

namespace Witness

/-- An object and its convolution at a nonnegative radius admit a witness at that radius. -/
def toConvolution (F : D⁺[k]) (hε : 0 ≤ ε) : Witness k hε F ((T k ε).obj F) where
  hom := 𝟙 _
  inv := (TComp k hε hε).hom.app F ≫ (aug k (add_nonneg hε hε)).app F
  hom_inv := by
    erw [(T k ε).map_id, Category.id_comp, (TComp k hε hε).inv_hom_id_app_assoc F]
  inv_hom := by
    erw [Category.comp_id]
    exact convolution_witness_inv_hom F hε

private def convolveMap {r : ℝ} (hr : 0 ≤ r) (f : (T k ε).obj F ⟶ G) :
    (T k ε).obj ((T k r).obj F) ⟶ (T k r).obj G :=
  (TComp k hr hε).hom.app F ≫ bandCompose hε hr (add_comm ε r) f (𝟙 _)

private theorem convolveMap_comp_id {r : ℝ} (hr : 0 ≤ r) (f : (T k ε).obj F ⟶ G) :
    bandCompose hr hε rfl (𝟙 ((T k r).obj F)) (convolveMap (hε := hε) hr f) =
      bandCompose hε hr (add_comm ε r) f (𝟙 _) := by
  let A := (T k ε).obj ((T k r).obj F)
  let e : A ≅ (T k (r + ε)).obj F := (TComp k hr hε).app F
  let u := bandCompose hε hr (add_comm ε r) f (𝟙 ((T k r).obj G))
  simp only [bandCompose, TCompOfEq_rfl, convolveMap]
  rw [(T k ε).map_id]
  change e.inv ≫ 𝟙 A ≫ e.hom ≫ u = u
  exact (congrArg (e.inv ≫ ·) (Category.id_comp (e.hom ≫ u))).trans
    (Iso.inv_hom_id_assoc e u)

private theorem convolveMap_equation {r : ℝ} (hr : 0 ≤ r) (w : Witness k hε F G) :
    bandCompose hε hε rfl (convolveMap (hε := hε) hr w.hom)
      (convolveMap (hε := hε) hr w.inv) =
      (aug k (add_nonneg hε hε)).app ((T k r).obj F) := by
  let iF := 𝟙 ((T k r).obj F)
  let iG := 𝟙 ((T k r).obj G)
  let f := convolveMap (hε := hε) hr w.hom
  let g := convolveMap (hε := hε) hr w.inv
  let h₂ := add_nonneg hε hε
  let e : r + ε + ε = r + (ε + ε) := add_assoc _ _ _
  let e' : ε + (r + ε) = r + (ε + ε) := by ring
  let e'' : ε + ε + r = r + (ε + ε) := add_comm _ _
  have h : bandCompose hr h₂ rfl iF (bandCompose hε hε rfl f g) =
      bandCompose hr h₂ rfl iF ((aug k h₂).app ((T k r).obj F)) := by
    calc
      _ = bandCompose (add_nonneg hr hε) hε e (bandCompose hr hε rfl iF f) g :=
        (bandCompose_assoc hr hε hε rfl rfl e iF f g).symm
      _ = bandCompose (add_nonneg hr hε) hε e
          (bandCompose hε hr (add_comm ε r) w.hom iG) g := by
            exact congrArg (fun u => bandCompose (add_nonneg hr hε) hε e u g)
              (convolveMap_comp_id (hε := hε) hr w.hom)
      _ = bandCompose hε (add_nonneg hr hε) e' w.hom (bandCompose hr hε rfl iG g) :=
        bandCompose_assoc hε hr hε (add_comm ε r) rfl e w.hom iG g
      _ = bandCompose hε (add_nonneg hr hε) e' w.hom
          (bandCompose hε hr (add_comm ε r) w.inv iF) := by
            exact congrArg (bandCompose hε (add_nonneg hr hε) e' w.hom)
              (convolveMap_comp_id (hε := hε) hr w.inv)
      _ = bandCompose h₂ hr e'' (bandCompose hε hε rfl w.hom w.inv) iF :=
        (bandCompose_assoc hε hε hr rfl (add_comm ε r) e'' w.hom w.inv iF).symm
      _ = _ := by
        have hw : bandCompose hε hε rfl w.hom w.inv = (aug k h₂).app F := by
          simpa only [bandCompose, TCompOfEq_rfl] using w.hom_inv
        rw [hw, bandCompose_aug_left h₂ hr e'' iF, bandCompose_aug_right hr h₂ rfl iF]
  let A := (T k (ε + ε)).obj ((T k r).obj F)
  let e₀ : A ≅ (T k (r + (ε + ε))).obj F := (TComp k hr h₂).app F
  let u : A ⟶ (T k r).obj F :=
    (TComp k hε hε).inv.app ((T k r).obj F) ≫ (T k ε).map f ≫ g
  let v := (aug k h₂).app ((T k r).obj F)
  simp only [bandCompose, TCompOfEq_rfl] at h ⊢
  change e₀.inv ≫ (T k (ε + ε)).map iF ≫ u = e₀.inv ≫ (T k (ε + ε)).map iF ≫ v at h
  rw [show (T k (ε + ε)).map iF = 𝟙 A from (T k (ε + ε)).map_id _] at h
  have he (a : A ⟶ (T k r).obj F) : e₀.inv ≫ 𝟙 A ≫ a = e₀.inv ≫ a :=
    congrArg (e₀.inv ≫ ·) (Category.id_comp a)
  exact (cancel_epi e₀.inv).mp ((he u).symm.trans (h.trans (he v)))

/-- Convolving both objects by the same nonnegative radius preserves a witness radius. -/
def convolve {r : ℝ} (w : Witness k hε F G) (hr : 0 ≤ r) :
    Witness k hε ((T k r).obj F) ((T k r).obj G) where
  hom := convolveMap (hε := hε) hr w.hom
  inv := convolveMap (hε := hε) hr w.inv
  hom_inv := by simpa only [bandCompose, TCompOfEq_rfl] using convolveMap_equation hr w
  inv_hom := by
    simpa only [bandCompose, TCompOfEq_rfl, Witness.symm] using convolveMap_equation hr w.symm

private theorem commute_witness_equation {C : Type*} [Category C] (U S : C ⥤ C)
    (e : S ⋙ U ≅ U ⋙ S) (η : U ⟶ 𝟭 C)
    (comm : ∀ X, η.app (S.obj X) = e.hom.app X ≫ S.map (η.app X))
    {X Y : C} (f : U.obj X ⟶ Y) (g : U.obj Y ⟶ X)
    (h : U.map f ≫ g = η.app (U.obj X) ≫ η.app X) :
    U.map (e.hom.app X ≫ S.map f) ≫ e.hom.app Y ≫ S.map g =
      η.app (U.obj (S.obj X)) ≫ η.app (S.obj X) := by
  have nat : U.map (S.map f) ≫ e.hom.app Y = e.hom.app (U.obj X) ≫ S.map (U.map f) :=
    e.hom.naturality f
  rw [U.map_comp]
  simp only [Category.assoc]
  have hn : U.map (e.hom.app X) ≫ η.app (S.obj (U.obj X)) =
      η.app (U.obj (S.obj X)) ≫ e.hom.app X := η.naturality (e.hom.app X)
  rw [reassoc_of% nat, ← S.map_comp, h, S.map_comp, ← reassoc_of% comm (U.obj X),
    reassoc_of% hn, ← comm X]

private theorem shift_equation (w : Witness k hε F G) (d : ℤ) :
    (TComp k hε hε).inv.app ((shiftFunctor D⁺[k] d).obj F) ≫
      (T k ε).map (((T k ε).commShiftIso d).hom.app F ≫
        (shiftFunctor D⁺[k] d).map w.hom) ≫
      (((T k ε).commShiftIso d).hom.app G ≫ (shiftFunctor D⁺[k] d).map w.inv) =
    (aug k (add_nonneg hε hε)).app ((shiftFunctor D⁺[k] d).obj F) := by
  let U := T k ε
  let S := shiftFunctor D⁺[k] d
  let e := U.commShiftIso d
  let η := aug k hε
  let μ := TComp k hε hε
  have unit (X : D⁺[k]) :
      μ.hom.app X ≫ (aug k (add_nonneg hε hε)).app X = η.app (U.obj X) ≫ η.app X := by
    have h := (NatTrans.congr_app (hcomp_aug_TComp_hom k hε hε) X).symm
    simp only [NatTrans.comp_app, NatTrans.hcomp_app, Functor.leftUnitor_hom_app,
      Functor.id_map] at h
    exact h.trans (Category.comp_id _)
  have h : U.map w.hom ≫ w.inv = η.app (U.obj F) ≫ η.app F := by
    rw [← unit F, ← w.hom_inv, Iso.hom_inv_id_app_assoc]
  have comm (X : D⁺[k]) : η.app (S.obj X) = e.hom.app X ≫ S.map (η.app X) := by
    have ht := η.shift_app_comm d X
    rw [Functor.commShiftIso_id_hom_app] at ht
    exact (ht.trans (Category.comp_id _)).symm
  apply (cancel_epi (μ.hom.app (S.obj F))).mp
  rw [Iso.hom_inv_id_app_assoc, unit (S.obj F)]
  exact commute_witness_equation U S e η comm w.hom w.inv h

/-- An integer cohomological shift of both objects preserves a witness radius. -/
def shift (w : Witness k hε F G) (d : ℤ) :
    Witness k hε ((shiftFunctor D⁺[k] d).obj F) ((shiftFunctor D⁺[k] d).obj G) where
  hom := ((T k ε).commShiftIso d).hom.app F ≫ (shiftFunctor D⁺[k] d).map w.hom
  inv := ((T k ε).commShiftIso d).hom.app G ≫ (shiftFunctor D⁺[k] d).map w.inv
  hom_inv := shift_equation w d
  inv_hom := shift_equation w.symm d

/-- Enlarge a witness by precomposing both maps with the radius restriction. -/
def mono (w : Witness k hε F G) (h : ε ≤ δ) : Witness k hδ F G := by
  have eqn {X Y : D⁺[k]} (f : (T k ε).obj X ⟶ Y) (g : (T k ε).obj Y ⟶ X)
      (he : bandCompose hε hε rfl f g =
        (aug k (add_nonneg hε hε)).app X) :
      bandCompose hδ hδ rfl ((restr k h).app X ≫ f)
        ((restr k h).app Y ≫ g) =
          (aug k (add_nonneg hδ hδ)).app X := by
    refine (bandCompose_restr hε hε rfl rfl h h f g).trans ?_
    rw [he]
    exact NatTrans.congr_app (restr_comp_aug k (add_le_add h h)
      (add_nonneg hε hε)) X
  refine ⟨(restr k h).app F ≫ w.hom, (restr k h).app G ≫ w.inv, ?_, ?_⟩
  · simpa only [bandCompose, TCompOfEq_rfl] using eqn w.hom w.inv
      (by simpa only [bandCompose, TCompOfEq_rfl] using w.hom_inv)
  · simpa only [bandCompose, TCompOfEq_rfl] using eqn w.inv w.hom
      (by simpa only [bandCompose, TCompOfEq_rfl] using w.inv_hom)

private theorem trans_equation {s : ℝ} (w : Witness k hε F G) (v : Witness k hδ G H)
    (e : ε + δ = s) (e' : δ + ε = s) :
    bandCompose (sum_nonneg hε hδ e)
        (sum_nonneg hδ hε e') rfl
        (bandCompose hε hδ e w.hom v.hom)
        (bandCompose hδ hε e' v.inv w.inv) =
      (aug k (add_nonneg (sum_nonneg hε hδ e)
        (sum_nonneg hε hδ e))).app F := by
  let ha := hε
  let hb := hδ
  let hs : δ + s = δ + s := rfl
  let ht : δ + δ + ε = δ + s := by rw [add_assoc, e']
  let hr : ε + (δ + s) = s + s := by rw [← add_assoc, e]
  calc
    _ = bandCompose ha (add_nonneg hb (sum_nonneg hb ha e')) hr w.hom
          (bandCompose hb (sum_nonneg hb ha e') hs v.hom
            (bandCompose hb ha e' v.inv w.inv)) :=
      bandCompose_assoc ha hb (sum_nonneg hb ha e') e hs rfl _ _ _
    _ = bandCompose ha (sum_nonneg (add_nonneg hb hb) ha ht) hr w.hom
          (bandCompose (add_nonneg hb hb) ha ht
            (bandCompose hb hb rfl v.hom v.inv) w.inv) := by
      rw [bandCompose_assoc hb hb ha rfl e' ht]
    _ = _ := by
      have hv : bandCompose hb hb rfl v.hom v.inv =
          (aug k (add_nonneg hb hb)).app G := by
        simpa only [bandCompose, TCompOfEq_rfl] using v.hom_inv
      rw [hv, bandCompose_aug_left (add_nonneg hb hb) ha ht]
      have hd : ε ≤ δ + s := by linarith
      have h := bandCompose_restr ha ha rfl hr (le_refl ε) hd w.hom w.inv
      rw [restr_refl, NatTrans.id_app, Category.id_comp] at h
      rw [h]
      have hw : bandCompose ha ha rfl w.hom w.inv =
          (aug k (add_nonneg ha ha)).app F := by
        simpa only [bandCompose, TCompOfEq_rfl] using w.hom_inv
      rw [hw]
      exact NatTrans.congr_app (restr_comp_aug k _ (add_nonneg ha ha)) F

/-- Compose witnesses at radii `ε` and `δ` to obtain a witness at `ε + δ`. -/
def trans (w : Witness k hε F G) (v : Witness k hδ G H) : Witness k (add_nonneg hε hδ) F H where
  hom := bandCompose hε hδ rfl w.hom v.hom
  inv := bandCompose hδ hε (add_comm _ _) v.inv w.inv
  hom_inv := by
    simpa only [bandCompose, TCompOfEq_rfl] using trans_equation w v rfl (add_comm _ _)
  inv_hom := by
    simpa only [bandCompose, TCompOfEq_rfl, symm] using
      trans_equation v.symm w.symm (add_comm _ _) rfl

end Witness

private theorem zero_aug_comparison (F : D⁺[k]) :
    (TComp k le_rfl le_rfl).hom.app F ≫
        (aug k (add_nonneg (le_refl (0 : ℝ)) (le_refl (0 : ℝ)))).app F =
      (T0Iso k).hom.app ((T k 0).obj F) ≫ (T0Iso k).hom.app F := by
  have h := (NatTrans.congr_app (hcomp_aug_TComp_hom k
    (le_refl (0 : ℝ)) (le_refl (0 : ℝ))) F).symm
  simp only [NatTrans.comp_app, NatTrans.hcomp_app, Functor.id_map,
    Functor.leftUnitor_hom_app, Functor.id_obj, aug_zero] at h
  exact h.trans (Category.comp_id _)

private theorem zero_equation (f : (T k 0).obj F ⟶ G) (g : (T k 0).obj G ⟶ F) :
    (TComp k le_rfl le_rfl).inv.app F ≫ (T k 0).map f ≫ g =
      (aug k (add_nonneg (le_refl (0 : ℝ)) (le_refl (0 : ℝ)))).app F ↔
    ((T0Iso k).inv.app F ≫ f) ≫ ((T0Iso k).inv.app G ≫ g) = 𝟙 F := by
  let e := T0Iso k
  let μ := TComp k (le_refl (0 : ℝ)) (le_refl (0 : ℝ))
  let c := e.inv.app F ≫ e.inv.app ((T k 0).obj F) ≫ μ.hom.app F
  have hn : e.inv.app ((T k 0).obj F) ≫ (T k 0).map f = f ≫ e.inv.app G :=
    (e.inv.naturality f).symm
  have hleft :
      c ≫ (μ.inv.app F ≫ (T k 0).map f ≫ g) =
        (e.inv.app F ≫ f) ≫ (e.inv.app G ≫ g) := by
    dsimp only [c]
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
    have hn' := congrArg (fun u => u ≫ g) hn
    simp only [Category.assoc] at hn'
    exact congrArg (fun u => e.inv.app F ≫ u) hn'
  have hright : c ≫ (aug k (add_nonneg (le_refl (0 : ℝ)) (le_refl (0 : ℝ)))).app F =
      𝟙 F := by
    dsimp only [c]
    rw [Category.assoc, Category.assoc, zero_aug_comparison]
    change e.inv.app F ≫ e.inv.app ((T k 0).obj F) ≫ e.hom.app ((T k 0).obj F) ≫
      e.hom.app F = _
    rw [Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app]
    rfl
  have hc : IsIso c := by dsimp only [c]; infer_instance
  exact (cancel_epi c).symm.trans (by rw [hleft, hright])

namespace Witness

/-- A zero-radius witness gives an isomorphism by the zero-band unit. -/
def iso (w : Witness k (le_refl (0 : ℝ)) F G) : F ≅ G where
  hom := (T0Iso k).inv.app F ≫ w.hom
  inv := (T0Iso k).inv.app G ≫ w.inv
  hom_inv_id := (zero_equation w.hom w.inv).mp w.hom_inv
  inv_hom_id := (zero_equation w.inv w.hom).mp w.inv_hom

/-- An isomorphism gives a zero-radius witness. -/
def ofIso (e : F ≅ G) : Witness k (le_refl (0 : ℝ)) F G where
  hom := (T0Iso k).hom.app F ≫ e.hom
  inv := (T0Iso k).hom.app G ≫ e.inv
  hom_inv := (zero_equation _ _).mpr (by simp)
  inv_hom := (zero_equation _ _).mpr (by simp)

/-- A zero-radius witness exists exactly when the two objects are isomorphic. -/
theorem nonempty_zero_iff : Nonempty (Witness k (le_refl (0 : ℝ)) F G) ↔ Nonempty (F ≅ G) :=
  ⟨fun ⟨w⟩ => ⟨w.iso⟩, fun ⟨e⟩ => ⟨ofIso e⟩⟩

end Witness

/-- Infimum in the extended nonnegative reals of finite radii admitting a band witness. -/
def distance (F G : D⁺[k]) : ℝ≥0∞ :=
  ⨅ (ε : ℝ≥0) (_ : Nonempty (Witness k ε.coe_nonneg F G)), (ε : ℝ≥0∞)

/-- A witness bounds the band distance by its radius. -/
theorem Witness.distance_le (w : Witness k hε F G) :
    distance F G ≤ ENNReal.ofReal ε := by
  rw [ENNReal.ofReal_eq_coe_nnreal hε]
  exact iInf₂_le (⟨ε, hε⟩ : ℝ≥0) (show Nonempty (Witness k hε F G) from ⟨w⟩)

/-- Lower bounds on the distance are exactly the common lower bounds on witness radii. -/
theorem le_distance_iff {r : ℝ≥0∞} :
    r ≤ distance F G ↔ ∀ ε : ℝ≥0, Nonempty (Witness k ε.coe_nonneg F G) → r ≤ ε :=
  le_iInf₂_iff

/-- A strict upper bound on the distance gives a witness below that bound. -/
theorem distance_lt_iff {r : ℝ≥0∞} :
    distance F G < r ↔ ∃ ε : ℝ≥0, (ε : ℝ≥0∞) < r ∧ Nonempty (Witness k ε.coe_nonneg F G) := by
  simp only [distance, iInf_lt_iff, exists_prop]
  exact exists_congr fun _ => and_comm

/-- Infinite distance means there is no witness at any finite radius. -/
theorem distance_eq_top_iff :
    distance F G = ⊤ ↔ ∀ ε : ℝ≥0, IsEmpty (Witness k ε.coe_nonneg F G) := by
  simp only [distance, iInf_eq_top, ENNReal.coe_ne_top, imp_false, not_nonempty_iff]

/-- A zero-radius witness implies zero distance. -/
theorem Witness.distance_eq_zero (w : Witness k (le_refl (0 : ℝ)) F G) : distance F G = 0 :=
  nonpos_iff_eq_zero.1 (by simpa using w.distance_le)

/-- The distance from an object to itself is zero. -/
@[simp] theorem distance_self (F : D⁺[k]) : distance F F = 0 :=
  (Witness.ofIso (Iso.refl F)).distance_eq_zero

/-- The band distance is symmetric. -/
theorem distance_comm (F G : D⁺[k]) : distance F G = distance G F :=
  le_antisymm (le_distance_iff.2 fun _ ⟨w⟩ => by
      simpa [ENNReal.ofReal_coe_nnreal] using w.symm.distance_le)
    (le_distance_iff.2 fun _ ⟨w⟩ => by
      simpa [ENNReal.ofReal_coe_nnreal] using w.symm.distance_le)

/-- The band distance satisfies the extended triangle inequality. -/
theorem distance_triangle (F G H : D⁺[k]) : distance F H ≤ distance F G + distance G H := by
  apply ENNReal.le_iInf₂_add_iInf₂
  intro ε h δ h'
  obtain ⟨w⟩ := h
  obtain ⟨v⟩ := h'
  simpa only [ENNReal.ofReal_add ε.coe_nonneg δ.coe_nonneg, ENNReal.ofReal_coe_nnreal]
    using (w.trans v).distance_le

/-- The band distance is invariant under isomorphism in both arguments. -/
theorem distance_congr {F' G' : D⁺[k]} (e : F ≅ F') (i : G ≅ G') :
    distance F G = distance F' G' := by
  have h₁ := (Witness.ofIso e).distance_eq_zero
  have h₂ := (Witness.ofIso i).distance_eq_zero
  have h₃ := (Witness.ofIso e.symm).distance_eq_zero
  have h₄ := (Witness.ofIso i.symm).distance_eq_zero
  apply le_antisymm
  · calc
      distance F G ≤ distance F F' + distance F' G := distance_triangle _ _ _
      _ ≤ distance F F' + (distance F' G' + distance G' G) :=
        add_le_add_right (distance_triangle _ _ _) _
      _ = distance F' G' := by rw [h₁, h₄, zero_add, add_zero]
  · calc
      distance F' G' ≤ distance F' F + distance F G' := distance_triangle _ _ _
      _ ≤ distance F' F + (distance F G + distance G G') :=
        add_le_add_right (distance_triangle _ _ _) _
      _ = distance F G := by rw [h₃, h₂, zero_add, add_zero]

/-- Zero distance is equivalent to witnesses at every strictly positive radius. -/
theorem distance_eq_zero_iff :
    distance F G = 0 ↔ ∀ ε : ℝ≥0, 0 < ε → Nonempty (Witness k ε.coe_nonneg F G) := by
  constructor
  · intro h ε hε
    obtain ⟨δ, hδ, ⟨w⟩⟩ := distance_lt_iff.1 (h.trans_lt (ENNReal.coe_pos.2 hε))
    exact ⟨w.mono (hδ := ε.coe_nonneg) (ENNReal.coe_lt_coe.1 hδ).le⟩
  · intro h
    refine nonpos_iff_eq_zero.1 (ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_)
    obtain ⟨w⟩ := h ε hε
    simpa only [ENNReal.ofReal_coe_nnreal, zero_add] using w.distance_le

end TDA.Sheaf.BandConvolution
