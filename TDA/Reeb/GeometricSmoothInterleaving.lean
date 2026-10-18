import TDA.Reeb.GeometricEnlargement

/-!
# Geometric smoothing of interleavings

This module proves the commutation, transport, smoothing, and distance-shift laws for geometric
interleavings of graph objects. These are library statements proved from the merged facts already
present in the library, not assertions attributed to a numbered source result. The mathematical
conventions and the equivalence used here are documented in
`docs/math/reeb-geometric-interleaving-equivalence.md`.
-/

open Set Topology CategoryTheory
open scoped NNReal ENNReal

universe u v

namespace TDA.Reeb

noncomputable section

namespace Interleaving

open OpenInterval

variable {C : Type u} [Category.{v} C]

/-! ### Transport on the left -/

/-- Transport an `ε`-interleaving along an isomorphism of its first precosheaf argument. -/
def isoLeft {ε : ℝ≥0} {F F' G : OpenInterval ⥤ C} (j : Interleaving ε F G) (e : F ≅ F') :
    Interleaving ε F' G := (j.symm.isoRight e).symm

/-- The first component of `Interleaving.isoLeft`. -/
theorem isoLeft_φ {ε : ℝ≥0} {F F' G : OpenInterval ⥤ C} (j : Interleaving ε F G)
    (e : F ≅ F') :
    (j.isoLeft e).φ = e.inv ≫ j.φ :=
  rfl

/-- The second component of `Interleaving.isoLeft`. -/
theorem isoLeft_ψ {ε : ℝ≥0} {F F' G : OpenInterval ⥤ C} (j : Interleaving ε F G)
    (e : F ≅ F') :
    (j.isoLeft e).ψ = j.ψ ≫ (smoothing ε).map e.hom :=
  rfl


/-! ### Precosheaf coherence used for the geometric laws -/

private theorem inv_comp_eq_of_comp_hom {D : Type*} [Category D] {X X' Y Y' : D}
    (e : X ≅ X') (e' : Y ≅ Y') (m : X ⟶ Y) (z : X' ⟶ Y') (h : m ≫ e'.hom = e.hom ≫ z) :
    e.inv ≫ m = z ≫ e'.inv := by
  rw [Iso.eq_comp_inv, Category.assoc, h, Iso.inv_hom_id_assoc]

private theorem comp_comp_eq_of_section {D : Type*} [Category D] {X₂ X₃ W W' V : D}
    (u : X₃ ⟶ X₂) (v : X₂ ⟶ X₃) (huv : u ≫ v = 𝟙 _) (x : X₃ ⟶ W) (y₁ : X₂ ⟶ V)
    (y₂ : V ⟶ W') (s : W' ≅ W) (h : v ≫ x = y₁ ≫ y₂ ≫ s.hom) :
    u ≫ y₁ ≫ y₂ = x ≫ s.inv := by
  rw [Iso.eq_comp_inv, Category.assoc, Category.assoc, ← h, ← Category.assoc, huv,
    Category.id_comp]

private theorem smoothing_map_smoothingMap_comp_commIso {ε δ : ℝ≥0} (h : ε ≤ δ) (η : ℝ≥0)
    (F : OpenInterval ⥤ C) :
    (smoothing η).map ((smoothingMap h).app F) ≫ (smoothingCommIso δ η).hom.app F =
      (smoothingCommIso ε η).hom.app F ≫ (smoothingMap h).app ((smoothing η).obj F) := by
  ext I
  simp only [NatTrans.comp_app, smoothingMap_app_app, smoothingCommIso_hom_app_app]
  interval_coherence

private theorem enlargement_comm_coherence {ε δ : ℝ≥0} (h : ε ≤ δ) (η : ℝ≥0)
    {X Y F Z : OpenInterval ⥤ C} (p : X ⟶ (smoothing η).obj Y) (q : Y ⟶ (smoothing ε).obj F)
    (r : (smoothing η).obj F ⟶ Z) :
    p ≫ (smoothing η).map (q ≫ (smoothingMap h).app F) ≫ (smoothingCommIso δ η).hom.app F ≫
        (smoothing δ).map r =
      (p ≫ (smoothing η).map q ≫ (smoothingCommIso ε η).hom.app F ≫ (smoothing ε).map r) ≫
        (smoothingMap h).app Z := by
  have hL : ∀ {W : OpenInterval ⥤ C} (k : (smoothing δ).obj ((smoothing η).obj F) ⟶ W),
      (smoothing η).map ((smoothingMap h).app F) ≫ (smoothingCommIso δ η).hom.app F ≫ k =
        (smoothingCommIso ε η).hom.app F ≫ (smoothingMap h).app ((smoothing η).obj F) ≫ k := by
    intro W k
    rw [← Category.assoc, smoothing_map_smoothingMap_comp_commIso h η F, Category.assoc]
  rw [(smoothing η).map_comp, Category.assoc, Category.assoc, hL,
    ← (smoothingMap h).naturality r]
  repeat rw [Category.assoc]

private theorem smoothingCommIso_add_coherence (ε η η' : ℝ≥0) (F : OpenInterval ⥤ C) :
    (smoothingCompIso η η').inv.app ((smoothing ε).obj F) ≫
        (smoothing η).map ((smoothingCommIso ε η').hom.app F) ≫
          (smoothingCommIso ε η).hom.app ((smoothing η').obj F) ≫
            (smoothing ε).map ((smoothingCompIso η η').hom.app F) =
      (smoothingCommIso ε (η + η')).hom.app F := by
  ext I
  simp only [NatTrans.comp_app, smoothingCompIso_inv_app_app, smoothingCompIso_hom_app_app,
    smoothingCommIso_hom_app_app]
  interval_coherence

private theorem smooth_add_coherence {ε η η' : ℝ≥0}
    {Y Y₁ Y₂ Y₃ F F₁ F₂ F₃ : OpenInterval ⥤ C} (q : Y ⟶ (smoothing ε).obj F)
    (a₁ : Y₁ ≅ (smoothing η').obj Y) (a₂ : Y₂ ≅ (smoothing η).obj Y₁)
    (a₃ : Y₃ ≅ (smoothing (η + η')).obj Y)
    (b₁ : F₁ ≅ (smoothing η').obj F) (b₂ : F₂ ≅ (smoothing η).obj F₁)
    (b₃ : F₃ ≅ (smoothing (η + η')).obj F) (g : Y₃ ⟶ Y₂) (m : F₂ ⟶ F₃)
    (hg : g ≫ a₂.hom ≫ (smoothing η).map a₁.hom =
      a₃.hom ≫ (smoothingCompIso η η').inv.app Y)
    (hm : b₂.inv ≫ m =
      (smoothing η).map b₁.hom ≫ (smoothingCompIso η η').hom.app F ≫ b₃.inv) :
    g ≫ (a₂.hom ≫ (smoothing η).map (a₁.hom ≫ (smoothing η').map q ≫
          (smoothingCommIso ε η').hom.app F ≫ (smoothing ε).map b₁.inv) ≫
        (smoothingCommIso ε η).hom.app F₁ ≫ (smoothing ε).map b₂.inv) ≫ (smoothing ε).map m =
      a₃.hom ≫ (smoothing (η + η')).map q ≫ (smoothingCommIso ε (η + η')).hom.app F ≫
        (smoothing ε).map b₃.inv := by
  have hn₁ : ∀ {W : OpenInterval ⥤ C}
      (k : (smoothing ε).obj ((smoothing η).obj ((smoothing η').obj F)) ⟶ W),
      (smoothingCommIso ε η).hom.app F₁ ≫ (smoothing ε).map ((smoothing η).map b₁.hom) ≫ k =
        (smoothing η).map ((smoothing ε).map b₁.hom) ≫
          (smoothingCommIso ε η).hom.app ((smoothing η').obj F) ≫ k := by
    intro W k
    have nat : (smoothing η).map ((smoothing ε).map b₁.hom) ≫
        (smoothingCommIso ε η).hom.app ((smoothing η').obj F) =
          (smoothingCommIso ε η).hom.app F₁ ≫ (smoothing ε).map ((smoothing η).map b₁.hom) :=
      (smoothingCommIso ε η).hom.naturality b₁.hom
    rw [← Category.assoc, ← nat, Category.assoc]
  have hn₂ : ∀ {W : OpenInterval ⥤ C}
      (k : (smoothing η).obj ((smoothing η').obj ((smoothing ε).obj F)) ⟶ W),
      (smoothingCompIso η η').inv.app Y ≫ (smoothing η).map ((smoothing η').map q) ≫ k =
        (smoothing (η + η')).map q ≫ (smoothingCompIso η η').inv.app ((smoothing ε).obj F) ≫
          k := by
    intro W k
    have nat : (smoothingCompIso η η').inv.app Y ≫ (smoothing η).map ((smoothing η').map q) =
        (smoothing (η + η')).map q ≫ (smoothingCompIso η η').inv.app ((smoothing ε).obj F) :=
      ((smoothingCompIso η η').inv.naturality q).symm
    rw [← Category.assoc, nat, Category.assoc]
  have hb : ∀ {W : OpenInterval ⥤ C}
      (k : (smoothing η).obj ((smoothing ε).obj ((smoothing η').obj F)) ⟶ W),
      (smoothing η).map (a₁.hom ≫ (smoothing η').map q ≫
          (smoothingCommIso ε η').hom.app F ≫ (smoothing ε).map b₁.inv) ≫
          (smoothing η).map ((smoothing ε).map b₁.hom) ≫ k =
        (smoothing η).map a₁.hom ≫ (smoothing η).map ((smoothing η').map q) ≫
          (smoothing η).map ((smoothingCommIso ε η').hom.app F) ≫ k := by
    intro W k
    rw [← Category.assoc, ← (smoothing η).map_comp, Category.assoc, Category.assoc,
      Category.assoc, ← (smoothing ε).map_comp, Iso.inv_hom_id, (smoothing ε).map_id]
    erw [Category.comp_id]
    rw [(smoothing η).map_comp, (smoothing η).map_comp, Category.assoc, Category.assoc]
  have hg' : ∀ {W : OpenInterval ⥤ C} (k : (smoothing η).obj ((smoothing η').obj Y) ⟶ W),
      g ≫ a₂.hom ≫ (smoothing η).map a₁.hom ≫ k =
        a₃.hom ≫ (smoothingCompIso η η').inv.app Y ≫ k := by
    intro W k
    rw [← Category.assoc, ← Category.assoc, ← Category.assoc, Category.assoc g, hg,
      Category.assoc]
  have hc : ∀ {W : OpenInterval ⥤ C}
      (k : (smoothing ε).obj ((smoothing (η + η')).obj F) ⟶ W),
      (smoothingCompIso η η').inv.app ((smoothing ε).obj F) ≫
        (smoothing η).map ((smoothingCommIso ε η').hom.app F) ≫
          (smoothingCommIso ε η).hom.app ((smoothing η').obj F) ≫
            (smoothing ε).map ((smoothingCompIso η η').hom.app F) ≫ k =
        (smoothingCommIso ε (η + η')).hom.app F ≫ k := by
    intro W k
    rw [← smoothingCommIso_add_coherence ε η η' F]
    repeat rw [Category.assoc]
  rw [Category.assoc, Category.assoc, Category.assoc, ← (smoothing ε).map_comp b₂.inv m, hm,
    (smoothing ε).map_comp, (smoothing ε).map_comp, hn₁, hb, hg', hn₂, hc]

end Interleaving

namespace RGraph

open OpenInterval

variable {ε δ η : ℝ≥0} {A B D : RGraphCat}

/-! ### Parameter equalities and commutation -/

/-- The homomorphisms of parameter-equality isomorphisms compose along equality proofs. -/
theorem geometricSmoothingEqIso_hom_comp_hom {ε δ γ : ℝ≥0} (h : ε = δ) (h' : δ = γ) :
    (geometricSmoothingEqIso h).hom ≫ (geometricSmoothingEqIso h').hom =
      (geometricSmoothingEqIso (h.trans h')).hom := by
  rw [geometricSmoothingEqIso_hom_eq, geometricSmoothingEqIso_hom_eq,
    geometricSmoothingEqIso_hom_eq]
  exact geometricEnlargement_comp h.le h'.le

/-- The geometric smoothing isomorphism that commutes two smoothing parameters. -/
def geometricSmoothingCommIso (ε δ : ℝ≥0) :
    geometricSmoothing ε ⋙ geometricSmoothing δ ≅ geometricSmoothing δ ⋙ geometricSmoothing ε :=
  geometricSmoothingCompIso δ ε ≪≫ geometricSmoothingEqIso (add_comm δ ε) ≪≫
    (geometricSmoothingCompIso ε δ).symm

/-- The component formula for the homomorphism of the geometric commutation isomorphism. -/
theorem geometricSmoothingCommIso_hom_app (ε δ : ℝ≥0) (B : RGraphCat) :
    (geometricSmoothingCommIso ε δ).hom.app B =
      (geometricSmoothingCompIso δ ε).hom.app B ≫
        (geometricSmoothingEqIso (add_comm δ ε)).hom.app B ≫
          (geometricSmoothingCompIso ε δ).inv.app B :=
  rfl

/-- The geometric commutation isomorphism at zero is induced by the zero isomorphism. -/
theorem geometricSmoothingCommIso_zero_hom_app (ε : ℝ≥0) (B : RGraphCat) :
    (geometricSmoothingCommIso ε 0).hom.app B =
      geometricSmoothingZeroIso.hom.app ((geometricSmoothing ε).obj B) ≫
        (geometricSmoothing ε).map (geometricSmoothingZeroIso.inv.app B) := by
  have hsplit :
      (geometricSmoothingEqIso (add_comm 0 ε)).hom =
        (geometricSmoothingEqIso (zero_add ε)).hom ≫
          (geometricSmoothingEqIso (add_zero ε)).inv := by
    have hsymm :
        (geometricSmoothingEqIso (add_zero ε).symm).hom =
          (geometricSmoothingEqIso (add_zero ε)).inv := by
      ext A
      rfl
    rw [← hsymm]
    exact (geometricSmoothingEqIso_hom_comp_hom (zero_add ε) (add_zero ε).symm).symm
  have hleft :
      geometricSmoothingZeroIso.hom.app ((geometricSmoothing ε).obj B) =
        (geometricSmoothingCompIso 0 ε).hom.app B ≫
          (geometricSmoothingEqIso (zero_add ε)).hom.app B :=
    ((congrArg (fun e => e.hom.app B) (geometricSmoothingCompIso_zero_left ε)).trans
      (Category.comp_id _)).symm
  have hright_inv :
      (geometricSmoothingEqIso (add_zero ε)).inv.app B ≫
          (geometricSmoothingCompIso ε 0).inv.app B =
        (geometricSmoothing ε).map (geometricSmoothingZeroIso.inv.app B) := by
    have h := congrArg (fun e => e.inv.app B) (geometricSmoothingCompIso_zero_right ε)
    simpa only [Iso.trans_inv, NatTrans.comp_app, Functor.leftUnitor_inv_app,
      Functor.isoWhiskerRight_inv, Functor.whiskerRight_app, Category.id_comp] using h
  rw [geometricSmoothingCommIso_hom_app, hsplit]
  calc
    (geometricSmoothingCompIso 0 ε).hom.app B ≫
          (geometricSmoothingEqIso (zero_add ε)).hom.app B ≫
          ((geometricSmoothingEqIso (add_zero ε)).inv.app B ≫
            (geometricSmoothingCompIso ε 0).inv.app B) =
        geometricSmoothingZeroIso.hom.app ((geometricSmoothing ε).obj B) ≫
          ((geometricSmoothingEqIso (add_zero ε)).inv.app B ≫
            (geometricSmoothingCompIso ε 0).inv.app B) := by
      rw [hleft]
      simp only [Category.assoc]
    _ = geometricSmoothingZeroIso.hom.app ((geometricSmoothing ε).obj B) ≫
          (geometricSmoothing ε).map (geometricSmoothingZeroIso.inv.app B) := by
      rw [hright_inv]

private theorem geometricSmoothingPrecosheafIso_component_hom (ε : ℝ≥0) (A : RGraphCat) :
    ((geometricSmoothingPrecosheafIso ε).app A).hom =
      ((geometricSmoothingComparisonIso ε).hom.app A).hom :=
  rfl

private theorem geometricSmoothingPrecosheafIso_component_inv (ε : ℝ≥0) (A : RGraphCat) :
    ((geometricSmoothingPrecosheafIso ε).app A).inv =
      ((geometricSmoothingComparisonIso ε).inv.app A).hom :=
  rfl

private theorem cosheafShiftMap_id (η : ℝ≥0) (Z : RGraphCat) :
    cosheafShiftMap (𝟙 ((geometricSmoothing η).obj Z)) =
      ((geometricSmoothingPrecosheafIso η).app Z).hom := by
  unfold cosheafShiftMap
  rw [CategoryTheory.Functor.map_id, ObjectProperty.FullSubcategory.id_hom]
  exact Category.id_comp _

/-! ### The shifted commutation map -/

/-- The shifted map of a smoothed graph morphism followed by geometric commutation. -/
theorem cosheafShiftMap_geometricSmoothing_map_comp_commIso {ε : ℝ≥0} (η : ℝ≥0)
    {X Y : RGraphCat} (f : X ⟶ (geometricSmoothing ε).obj Y) :
    cosheafShiftMap ((geometricSmoothing η).map f ≫
        (geometricSmoothingCommIso ε η).hom.app Y) =
      ((geometricSmoothingPrecosheafIso η).app X).hom ≫
        (smoothing η).map (cosheafShiftMap f) ≫
          (smoothingCommIso ε η).hom.app (cosheafFunctor.obj Y).obj ≫
            (smoothing ε).map ((geometricSmoothingPrecosheafIso η).app Y).inv := by
  have hid : ∀ Z : RGraphCat, cosheafShiftMap (ε := η) (B := Z)
      (𝟙 ((geometricSmoothing η).obj Z)) = ((geometricSmoothingPrecosheafIso η).app Z).hom := by
    intro Z
    unfold cosheafShiftMap
    rw [CategoryTheory.Functor.map_id, ObjectProperty.FullSubcategory.id_hom]
    exact Category.id_comp _
  have h1 := cosheafShiftMap_comp' (ε := η) (δ := ε) (𝟙 ((geometricSmoothing η).obj X)) f
  rw [Category.id_comp, hid] at h1
  have h2 := cosheafShiftMap_comp_geometricEnlargement (add_comm η ε).le
    ((geometricSmoothing η).map f ≫ (geometricSmoothingCompIso η ε).hom.app Y)
  rw [h1] at h2
  let eP : (cosheafFunctor.obj ((geometricSmoothing η).obj Y)).obj ≅
      (smoothing η).obj (cosheafFunctor.obj Y).obj := (geometricSmoothingPrecosheafIso η).app Y
  have hidY : cosheafShiftMap (ε := η) (B := Y) (𝟙 ((geometricSmoothing η).obj Y)) = eP.hom :=
    hid Y
  have h3 := cosheafShiftMap_comp' (ε := ε) (δ := η)
    ((geometricSmoothing η).map f ≫ (geometricSmoothingCommIso ε η).hom.app Y)
    (𝟙 ((geometricSmoothing η).obj Y))
  rw [CategoryTheory.Functor.map_id, Category.id_comp, hidY] at h3
  have hg : ((geometricSmoothing η).map f ≫ (geometricSmoothingCommIso ε η).hom.app Y) ≫
      (geometricSmoothingCompIso ε η).hom.app Y =
        ((geometricSmoothing η).map f ≫ (geometricSmoothingCompIso η ε).hom.app Y) ≫
          (geometricEnlargement (add_comm η ε).le).app Y := by
    rw [geometricSmoothingCommIso_hom_app, geometricSmoothingEqIso_hom_eq]
    simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  rw [Category.assoc, ← Category.assoc _ _ ((geometricSmoothingCompIso ε η).hom.app Y)] at h3
  rw [hg, h2] at h3
  have key : ∀ k : (cosheafFunctor.obj ((geometricSmoothing η).obj X)).obj ⟶
      (smoothing ε).obj (cosheafFunctor.obj ((geometricSmoothing η).obj Y)).obj,
      k = (k ≫ (smoothing ε).map eP.hom ≫
        (smoothingCompIso ε η).hom.app (cosheafFunctor.obj Y).obj) ≫
          (smoothingCompIso ε η).inv.app (cosheafFunctor.obj Y).obj ≫
            (smoothing ε).map eP.inv := fun k => by
    rw [Category.assoc, Category.assoc, Iso.hom_inv_id_app_assoc,
      ← CategoryTheory.Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id,
      Category.comp_id]
  rw [key (cosheafShiftMap _), ← h3]
  ext I
  rfl

/-! ### Enlargement and commutation -/

/-- Geometric enlargement commutes with smoothing and the geometric commutation isomorphism. -/
theorem geometricSmoothing_map_geometricEnlargement_comp_commIso {ε δ : ℝ≥0} (h : ε ≤ δ)
    (η : ℝ≥0) (B : RGraphCat) :
    (geometricSmoothing η).map ((geometricEnlargement h).app B) ≫
        (geometricSmoothingCommIso δ η).hom.app B =
      (geometricSmoothingCommIso ε η).hom.app B ≫
        (geometricEnlargement h).app ((geometricSmoothing η).obj B) := by
  apply cosheafShiftMap_injective δ ((geometricSmoothing η).obj ((geometricSmoothing ε).obj B))
    ((geometricSmoothing η).obj B)
  rw [cosheafShiftMap_geometricSmoothing_map_comp_commIso η
    ((geometricEnlargement h).app B)]
  rw [cosheafShiftMap_comp_geometricEnlargement h]
  have hcomm :
      cosheafShiftMap ((geometricSmoothingCommIso ε η).hom.app B) =
        ((geometricSmoothingPrecosheafIso η).app ((geometricSmoothing ε).obj B)).hom ≫
          (smoothing η).map (cosheafShiftMap (𝟙 ((geometricSmoothing ε).obj B))) ≫
            (smoothingCommIso ε η).hom.app (cosheafFunctor.obj B).obj ≫
              (smoothing ε).map ((geometricSmoothingPrecosheafIso η).app B).inv := by
    have h' := cosheafShiftMap_geometricSmoothing_map_comp_commIso (ε := ε) η
      (𝟙 ((geometricSmoothing ε).obj B))
    have hmap : (geometricSmoothing η).map
        (𝟙 ((geometricSmoothing ε).obj B)) = 𝟙 _ :=
      (geometricSmoothing η).map_id _
    rw [hmap, Category.id_comp] at h'
    exact h'
  rw [hcomm]
  have hid :
      cosheafShiftMap ((geometricEnlargement h).app B) =
        ((geometricSmoothingPrecosheafIso ε).app B).hom ≫
          (smoothingMap h).app (cosheafFunctor.obj B).obj := by
    unfold cosheafShiftMap
    rw [geometricSmoothingPrecosheafIso_component_hom]
    exact cosheafFunctor_map_geometricEnlargement_app h B
  rw [hid, cosheafShiftMap_id]
  exact Interleaving.enlargement_comm_coherence h η _ _ _

private theorem cosheafShiftMap_precomp {ε : ℝ≥0} {A B D : RGraphCat}
    (g : A ⟶ B) (φ : B ⟶ (geometricSmoothing ε).obj D) :
    cosheafShiftMap (g ≫ φ) = (cosheafFunctor.map g).hom ≫ cosheafShiftMap φ := by
  have e1 : (cosheafFunctor.map (g ≫ φ)).hom =
      (cosheafFunctor.map g).hom ≫ (cosheafFunctor.map φ).hom := by
    rw [CategoryTheory.Functor.map_comp]
    rfl
  exact (congrArg (· ≫ ((geometricSmoothingComparisonIso ε).hom.app D).hom) e1).trans
    (Category.assoc _ _ _)

private theorem cosheafShiftMap_comp_map {ε : ℝ≥0} {A B D : RGraphCat}
    (φ : A ⟶ (geometricSmoothing ε).obj B) (g : B ⟶ D) :
    cosheafShiftMap (φ ≫ (geometricSmoothing ε).map g) =
      cosheafShiftMap φ ≫ (smoothing ε).map (cosheafFunctor.map g).hom := by
  have e1 : (cosheafFunctor.map (φ ≫ (geometricSmoothing ε).map g)).hom =
      (cosheafFunctor.map φ).hom ≫ (cosheafFunctor.map ((geometricSmoothing ε).map g)).hom := by
    rw [CategoryTheory.Functor.map_comp]
    rfl
  have hnat :
      (cosheafFunctor.map ((geometricSmoothing ε).map g)).hom ≫
          ((geometricSmoothingComparisonIso ε).hom.app D).hom =
        ((geometricSmoothingComparisonIso ε).hom.app B).hom ≫
          (smoothing ε).map (cosheafFunctor.map g).hom :=
    congrArg (fun k => k.hom) ((geometricSmoothingComparisonIso ε).hom.naturality g)
  refine (congrArg (· ≫ ((geometricSmoothingComparisonIso ε).hom.app D).hom) e1).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg ((cosheafFunctor.map φ).hom ≫ ·) hnat).trans ?_
  exact (Category.assoc _ _ _).symm

private theorem cosheafShiftMap_geometricSmoothingCommIso (ε θ : ℝ≥0) (B : RGraphCat) :
    cosheafShiftMap ((geometricSmoothingCommIso ε θ).hom.app B) =
      ((geometricSmoothingPrecosheafIso θ).app ((geometricSmoothing ε).obj B)).hom ≫
        (smoothing θ).map ((geometricSmoothingPrecosheafIso ε).app B).hom ≫
          (smoothingCommIso ε θ).hom.app (cosheafFunctor.obj B).obj ≫
            (smoothing ε).map ((geometricSmoothingPrecosheafIso θ).app B).inv := by
  have h' := cosheafShiftMap_geometricSmoothing_map_comp_commIso (ε := ε) θ
    (𝟙 ((geometricSmoothing ε).obj B))
  have hmap : (geometricSmoothing θ).map (𝟙 ((geometricSmoothing ε).obj B)) = 𝟙 _ :=
    (geometricSmoothing θ).map_id _
  rw [hmap, Category.id_comp, cosheafShiftMap_id] at h'
  exact h'

/-- Commuting `ε` past `η` and then past `η'` is commuting `ε` past `η + η'`. -/
private theorem geometricSmoothingCommIso_add (ε η η' : ℝ≥0) (B : RGraphCat) :
    (geometricSmoothingCompIso η η').inv.app ((geometricSmoothing ε).obj B) ≫
        (geometricSmoothing η).map ((geometricSmoothingCommIso ε η').hom.app B) ≫
          (geometricSmoothingCommIso ε η).hom.app ((geometricSmoothing η').obj B) ≫
            (geometricSmoothing ε).map ((geometricSmoothingCompIso η η').hom.app B) =
      (geometricSmoothingCommIso ε (η + η')).hom.app B := by
  have hm := Interleaving.inv_comp_eq_of_comp_hom
    ((geometricSmoothingPrecosheafIso η).app ((geometricSmoothing η').obj B))
    ((geometricSmoothingPrecosheafIso (η + η')).app B)
    (cosheafFunctor.map ((geometricSmoothingCompIso η η').hom.app B)).hom _
    (cosheafFunctor_map_geometricSmoothingCompIso_hom_app η η' B)
  have huv : (cosheafFunctor.map ((geometricSmoothingCompIso η η').inv.app
        ((geometricSmoothing ε).obj B))).hom ≫
      (cosheafFunctor.map ((geometricSmoothingCompIso η η').hom.app
        ((geometricSmoothing ε).obj B))).hom = 𝟙 _ := by
    rw [← ObjectProperty.FullSubcategory.comp_hom, ← CategoryTheory.Functor.map_comp,
      Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
    rfl
  have hg := Interleaving.comp_comp_eq_of_section _ _ huv
    ((geometricSmoothingPrecosheafIso (η + η')).app ((geometricSmoothing ε).obj B)).hom _ _
    ((smoothingCompIso η η').app (cosheafFunctor.obj ((geometricSmoothing ε).obj B)).obj)
    (cosheafFunctor_map_geometricSmoothingCompIso_hom_app η η' ((geometricSmoothing ε).obj B))
  apply cosheafShiftMap_injective ε _ _
  rw [cosheafShiftMap_precomp,
    ← Category.assoc ((geometricSmoothing η).map ((geometricSmoothingCommIso ε η').hom.app B)),
    cosheafShiftMap_comp_map, cosheafShiftMap_geometricSmoothing_map_comp_commIso,
    cosheafShiftMap_geometricSmoothingCommIso, cosheafShiftMap_geometricSmoothingCommIso]
  exact Interleaving.smooth_add_coherence _ _ _ _ _ _ _ _ _ hg hm

/-! ### Smoothing witnesses -/

namespace GeometricInterleaving

/-- Smooth a geometric interleaving in the graph-object arguments, preserving its witness
parameter. -/
def smooth (i : GeometricInterleaving ε A B) (η : ℝ≥0) :
    GeometricInterleaving ε ((geometricSmoothing η).obj A) ((geometricSmoothing η).obj B) :=
  ofCosheaf (((i.toCosheaf.smooth η).isoLeft ((geometricSmoothingPrecosheafIso η).app A).symm)
    |>.isoRight ((geometricSmoothingPrecosheafIso η).app B).symm)

/-- The precosheaf interleaving underlying a smoothed geometric interleaving. -/
theorem smooth_toCosheaf (i : GeometricInterleaving ε A B) (η : ℝ≥0) :
    (i.smooth η).toCosheaf =
    ((i.toCosheaf.smooth η).isoLeft ((geometricSmoothingPrecosheafIso η).app A).symm).isoRight
      ((geometricSmoothingPrecosheafIso η).app B).symm :=
  toCosheaf_ofCosheaf _

/-- The first component of a smoothed geometric interleaving. -/
theorem smooth_φ (i : GeometricInterleaving ε A B) (η : ℝ≥0) :
    (i.smooth η).φ =
      (geometricSmoothing η).map i.φ ≫ (geometricSmoothingCommIso ε η).hom.app B := by
  apply cosheafShiftMap_injective ε ((geometricSmoothing η).obj A)
    ((geometricSmoothing η).obj B)
  rw [← toCosheaf_φ (i.smooth η), smooth_toCosheaf]
  change
    ((geometricSmoothingPrecosheafIso η).app A).hom ≫
        (smoothing η).map i.toCosheaf.φ ≫
          (smoothingCommIso ε η).hom.app (cosheafFunctor.obj B).obj ≫
            (smoothing ε).map ((geometricSmoothingPrecosheafIso η).app B).inv =
      cosheafShiftMap ((geometricSmoothing η).map i.φ ≫
        (geometricSmoothingCommIso ε η).hom.app B)
  rw [toCosheaf_φ]
  exact (cosheafShiftMap_geometricSmoothing_map_comp_commIso η i.φ).symm

/-- The second component of a smoothed geometric interleaving. -/
theorem smooth_ψ (i : GeometricInterleaving ε A B) (η : ℝ≥0) :
    (i.smooth η).ψ =
      (geometricSmoothing η).map i.ψ ≫ (geometricSmoothingCommIso ε η).hom.app A := by
  apply cosheafShiftMap_injective ε ((geometricSmoothing η).obj B)
    ((geometricSmoothing η).obj A)
  rw [← toCosheaf_ψ (i.smooth η), smooth_toCosheaf]
  change
    ((geometricSmoothingPrecosheafIso η).app B).hom ≫
        (smoothing η).map i.toCosheaf.ψ ≫
          (smoothingCommIso ε η).hom.app (cosheafFunctor.obj A).obj ≫
            (smoothing ε).map ((geometricSmoothingPrecosheafIso η).app A).inv =
      cosheafShiftMap ((geometricSmoothing η).map i.ψ ≫
        (geometricSmoothingCommIso ε η).hom.app A)
  rw [toCosheaf_ψ]
  exact (cosheafShiftMap_geometricSmoothing_map_comp_commIso η i.ψ).symm

/-- Smoothing a witness at zero recovers its first component after the zero isomorphisms. -/
theorem smooth_zero_φ (i : GeometricInterleaving ε A B) :
    geometricSmoothingZeroIso.inv.app A ≫ (i.smooth 0).φ ≫
        (geometricSmoothing ε).map (geometricSmoothingZeroIso.hom.app B) = i.φ := by
  rw [smooth_φ, geometricSmoothingCommIso_zero_hom_app]
  simp only [Category.assoc]
  erw [geometricSmoothingZeroIso.hom.naturality_assoc i.φ]
  rw [Iso.inv_hom_id_app_assoc, ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id]
  exact Category.comp_id _

/-- Smoothing a witness at zero recovers its second component after the zero isomorphisms. -/
theorem smooth_zero_ψ (i : GeometricInterleaving ε A B) :
    geometricSmoothingZeroIso.inv.app B ≫ (i.smooth 0).ψ ≫
        (geometricSmoothing ε).map (geometricSmoothingZeroIso.hom.app A) = i.ψ := by
  rw [smooth_ψ, geometricSmoothingCommIso_zero_hom_app]
  simp only [Category.assoc]
  erw [geometricSmoothingZeroIso.hom.naturality_assoc i.ψ]
  rw [Iso.inv_hom_id_app_assoc, ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id]
  exact Category.comp_id _

/-- Smoothing twice is compatible with the geometric smoothing composition isomorphism. -/
theorem smooth_add_φ (i : GeometricInterleaving ε A B) (η η' : ℝ≥0) :
    (geometricSmoothingCompIso η η').inv.app A ≫ ((i.smooth η').smooth η).φ ≫
        (geometricSmoothing ε).map ((geometricSmoothingCompIso η η').hom.app B) =
      (i.smooth (η + η')).φ := by
  rw [smooth_φ, smooth_φ, smooth_φ, CategoryTheory.Functor.map_comp]
  have hn : (geometricSmoothingCompIso η η').inv.app A ≫
      (geometricSmoothing η).map ((geometricSmoothing η').map i.φ) =
        (geometricSmoothing (η + η')).map i.φ ≫
          (geometricSmoothingCompIso η η').inv.app ((geometricSmoothing ε).obj B) :=
    ((geometricSmoothingCompIso η η').inv.naturality i.φ).symm
  rw [← geometricSmoothingCommIso_add ε η η' B]
  simp only [Category.assoc]
  rw [← Category.assoc ((geometricSmoothingCompIso η η').inv.app A), hn, Category.assoc]

/-- The second component is the same additivity law with the graph arguments exchanged. -/
theorem smooth_add_ψ (i : GeometricInterleaving ε A B) (η η' : ℝ≥0) :
    (geometricSmoothingCompIso η η').inv.app B ≫ ((i.smooth η').smooth η).ψ ≫
        (geometricSmoothing ε).map ((geometricSmoothingCompIso η η').hom.app A) =
      (i.smooth (η + η')).ψ := by
  rw [smooth_ψ, smooth_ψ, smooth_ψ, CategoryTheory.Functor.map_comp]
  have hn : (geometricSmoothingCompIso η η').inv.app B ≫
      (geometricSmoothing η).map ((geometricSmoothing η').map i.ψ) =
        (geometricSmoothing (η + η')).map i.ψ ≫
          (geometricSmoothingCompIso η η').inv.app ((geometricSmoothing ε).obj A) :=
    ((geometricSmoothingCompIso η η').inv.naturality i.ψ).symm
  rw [← geometricSmoothingCommIso_add ε η η' A]
  simp only [Category.assoc]
  rw [← Category.assoc ((geometricSmoothingCompIso η η').inv.app B), hn, Category.assoc]

/-- Smoothing commutes with enlargement of the witness parameter. -/
theorem smooth_mono (i : GeometricInterleaving ε A B) {δ : ℝ≥0} (h : ε ≤ δ) (η : ℝ≥0) :
    (i.mono h).smooth η = (i.smooth η).mono h := by
  apply GeometricInterleaving.ext
  · rw [smooth_φ, mono_φ, CategoryTheory.Functor.map_comp,
      mono_φ, smooth_φ]
    simp only [Category.assoc]
    rw [geometricSmoothing_map_geometricEnlargement_comp_commIso h]
  · rw [smooth_ψ, mono_ψ, CategoryTheory.Functor.map_comp,
      mono_ψ, smooth_ψ]
    simp only [Category.assoc]
    rw [geometricSmoothing_map_geometricEnlargement_comp_commIso h]

end GeometricInterleaving

/-! ### Distance consequences -/

/-- Smoothing preserves nonemptiness of geometric interleaving witnesses. -/
theorem nonempty_smooth (η : ℝ≥0) :
    Nonempty (GeometricInterleaving ε A B) →
      Nonempty (GeometricInterleaving ε ((geometricSmoothing η).obj A)
        ((geometricSmoothing η).obj B))
  | ⟨i⟩ => ⟨i.smooth η⟩

namespace GeometricInterleaving

/-- A smoothed geometric witness bounds the distance between the smoothed graph objects. -/
theorem geometricInterleavingDistance_smooth_le (i : GeometricInterleaving ε A B) (η : ℝ≥0) :
    geometricInterleavingDistance ((geometricSmoothing η).obj A)
      ((geometricSmoothing η).obj B) ≤ ε :=
  (i.smooth η).geometricInterleavingDistance_le

end GeometricInterleaving

/-- Smoothing the left graph object changes geometric distance by at most the smoothing parameter,
in the upper direction. -/
theorem geometricInterleavingDistance_geometricSmoothing_left_le (η : ℝ≥0) (A C : RGraphCat) :
    geometricInterleavingDistance ((geometricSmoothing η).obj A) C ≤
      geometricInterleavingDistance A C + η := by
  calc
    geometricInterleavingDistance ((geometricSmoothing η).obj A) C ≤
        geometricInterleavingDistance ((geometricSmoothing η).obj A) A +
          geometricInterleavingDistance A C :=
      geometricInterleavingDistance_triangle _ _ _
    _ = geometricInterleavingDistance A ((geometricSmoothing η).obj A) +
          geometricInterleavingDistance A C := by
      rw [geometricInterleavingDistance_comm]
    _ ≤ η + geometricInterleavingDistance A C :=
      add_le_add_left (geometricInterleavingDistance_geometricSmoothing_self_le η A) _
    _ = geometricInterleavingDistance A C + η := add_comm _ _

/-- Smoothing the left graph object changes geometric distance by at most the smoothing parameter,
in the lower direction. -/
theorem geometricInterleavingDistance_le_geometricSmoothing_left (η : ℝ≥0) (A C : RGraphCat) :
    geometricInterleavingDistance A C ≤
      geometricInterleavingDistance ((geometricSmoothing η).obj A) C + η := by
  calc
    geometricInterleavingDistance A C ≤
        geometricInterleavingDistance A ((geometricSmoothing η).obj A) +
          geometricInterleavingDistance ((geometricSmoothing η).obj A) C :=
      geometricInterleavingDistance_triangle _ _ _
    _ ≤ η + geometricInterleavingDistance ((geometricSmoothing η).obj A) C :=
      add_le_add_left (geometricInterleavingDistance_geometricSmoothing_self_le η A) _
    _ = geometricInterleavingDistance ((geometricSmoothing η).obj A) C + η := add_comm _ _

/-- Smoothing the right graph object changes geometric distance by at most the smoothing parameter,
in the upper direction. -/
theorem geometricInterleavingDistance_geometricSmoothing_right_le (η : ℝ≥0) (A C : RGraphCat) :
    geometricInterleavingDistance C ((geometricSmoothing η).obj A) ≤
      geometricInterleavingDistance C A + η := by
  rw [geometricInterleavingDistance_comm C ((geometricSmoothing η).obj A),
    geometricInterleavingDistance_comm C A]
  exact geometricInterleavingDistance_geometricSmoothing_left_le η A C

/-- Smoothing the right graph object changes geometric distance by at most the smoothing parameter,
in the lower direction. -/
theorem geometricInterleavingDistance_le_geometricSmoothing_right (η : ℝ≥0) (A C : RGraphCat) :
    geometricInterleavingDistance C A ≤
      geometricInterleavingDistance C ((geometricSmoothing η).obj A) + η := by
  rw [geometricInterleavingDistance_comm C A,
    geometricInterleavingDistance_comm C ((geometricSmoothing η).obj A)]
  exact geometricInterleavingDistance_le_geometricSmoothing_left η A C

end RGraph

end

end TDA.Reeb
