import TDA.Sheaf.Alexandrov
import TDA.Sheaf.PresheafRestriction
import TDA.Persistence.CoordinateInterleavingDistance
import Mathlib.Topology.Sheaves.Functors
import Mathlib.Algebra.Category.ModuleCat.Limits

/-!
# Coordinate Alexandrov translations and sheaf interleavings

Let `X := upperSpace (Fin n → ℝ) = TopCat.of (Topology.WithUpperSet (Fin n → ℝ))`, the product
order on `Fin n → ℝ` with its upper Alexandrov topology (the open sets are the upper sets). Every
`n` is allowed, including `n = 0`. For `ε : ℝ≥0`:

* `translate ε : X ⟶ X` is the diagonal translation `x ↦ x - ε · 1`, that is
  `(translate ε x)_i = x_i - ε`, continuous by `WithUpperSet.map` of the monotone map
  `downTranslation ε`. Its preimage of an open `U` is the image of `U` under
  `CoordinateShift.translation ε` (`coe_map_translate`); a principal open `↑a` goes to
  `↑(CoordinateShift.translation ε a)` (`map_translate_principalOpen`). Inclusions and
  equalities of preimages are proved coordinatewise.
* `sheafShift C ε := TopCat.Sheaf.pushforward C (translate ε)`, so that
  `(sheafShift C ε F)(U) = F(U + ε · 1)` and the action on morphisms is Mathlib's pushforward map.
* `sheafShiftLE`, `sheafTransition`, `sheafZeroIso`, `sheafCompIso` and `sheafCongrIso` are the
  order maps for `ε ≤ δ`, the transition `F ⟶ sheafShift C ε F`, and the zero, addition and
  equal-parameter natural isomorphisms. Each component is a restriction of `F` along an
  inclusion or equality of preimage opens, and every coherence law is the equality of the
  corresponding restrictions.
* `coordinateSections C : X.Sheaf C ⥤ ((Fin n → ℝ) ⥤ C)` is the principal-sections functor `Γ`
  of `TDA.Sheaf.Alexandrov` read on `Fin n → ℝ`, the inverse of
  `upperSetEquivalence (Fin n → ℝ) C`.
* `shiftComparison R ε : sheafShift ε ⋙ Γ ≅ Γ ⋙ CoordinateShift.shift ε` for `ModuleCat.{0} R`;
  it carries `sheafShiftLE`, `sheafTransition`, `sheafZeroIso` and `sheafCompIso` to
  `CoordinateShift.shiftLE`, `CoordinateShift.transition`, `CoordinateShift.zeroIso` and
  `CoordinateShift.compIso`.
* `SheafInterleaving ε F G` has arrows `F ⟶ sheafShift ε G`, `G ⟶ sheafShift ε F` and the two
  double-shift equations, in the orientation of `CoordinateInterleaving`;
  `SheafInterleaving.equivCoordinateInterleaving` identifies it with
  `CoordinateInterleaving ε (Γ F) (Γ G)` for `ModuleCat.{0} R`,
  `SheafInterleaving.equivUpperSet` with `CoordinateInterleaving ε M N` for the sheaves attached
  to modules `M` and `N`, and `sheafInterleavingDistance_eq` identifies the extended-infimum
  sheaf distance with `coordinateInterleavingDistance`.

The construction concerns the upper Alexandrov topology of the product order only, not the
Euclidean one.
-/

set_option autoImplicit false

universe u v w

open CategoryTheory Limits Opposite TopologicalSpace Topology TopCat
open TDA.Persistence
open scoped NNReal ENNReal

namespace TDA.Sheaf.AlexandrovCoordinateTranslation

open TDA.Sheaf.Alexandrov

noncomputable section

variable {n : ℕ}

/-! ## Diagonal translations of the coordinate Alexandrov space -/

/-- The monotone diagonal translation `a ↦ a - ε · 1` of `Fin n → ℝ`: `(a - ε · 1)_i = a_i - ε`. -/
def downTranslation (ε : ℝ≥0) : (Fin n → ℝ) →o (Fin n → ℝ) :=
  ⟨fun a i => a i - (ε : ℝ), fun _ _ h i => sub_le_sub_right (h i) _⟩

@[simp]
theorem downTranslation_apply (ε : ℝ≥0) (a : Fin n → ℝ) (i : Fin n) :
    downTranslation ε a i = a i - (ε : ℝ) :=
  rfl

/-- `downTranslation ε` undoes `CoordinateShift.translation ε`. -/
@[simp]
theorem downTranslation_translation (ε : ℝ≥0) (a : Fin n → ℝ) :
    downTranslation ε (CoordinateShift.translation ε a) = a :=
  funext fun i => add_sub_cancel_right (a i) (ε : ℝ)

/-- `CoordinateShift.translation ε` undoes `downTranslation ε`. -/
@[simp]
theorem translation_downTranslation (ε : ℝ≥0) (a : Fin n → ℝ) :
    CoordinateShift.translation ε (downTranslation ε a) = a :=
  funext fun i => sub_add_cancel (a i) (ε : ℝ)

/-- The continuous map `x ↦ x - ε · 1` of the coordinate Alexandrov space, `WithUpperSet.map`
of the monotone translation `downTranslation ε`. -/
def translate (ε : ℝ≥0) : upperSpace (Fin n → ℝ) ⟶ upperSpace (Fin n → ℝ) :=
  TopCat.ofHom (WithUpperSet.map (downTranslation ε))

@[simp]
theorem translate_apply (ε : ℝ≥0) (x : WithUpperSet (Fin n → ℝ)) :
    translate ε x =
      WithUpperSet.toUpperSet (downTranslation ε (WithUpperSet.ofUpperSet (α := Fin n → ℝ) x)) :=
  rfl

/-- Translation by zero is the identity point by point. -/
theorem translate_zero_apply (x : WithUpperSet (Fin n → ℝ)) : translate 0 x = x := by
  rw [translate_apply]
  have h : downTranslation 0 (WithUpperSet.ofUpperSet (α := Fin n → ℝ) x) =
      WithUpperSet.ofUpperSet (α := Fin n → ℝ) x :=
    funext fun i => by simp
  rw [h]
  rfl

/-- Translating by `δ` and then by `ε` is translating by `ε + δ`. -/
theorem translate_translate_apply (ε δ : ℝ≥0) (x : WithUpperSet (Fin n → ℝ)) :
    translate ε (translate δ x) = translate (ε + δ) x := by
  change WithUpperSet.toUpperSet (downTranslation ε (downTranslation δ
      (WithUpperSet.ofUpperSet (α := Fin n → ℝ) x))) =
    WithUpperSet.toUpperSet (downTranslation (ε + δ) (WithUpperSet.ofUpperSet (α := Fin n → ℝ) x))
  congr 1
  funext i
  simp only [downTranslation_apply, NNReal.coe_add]
  ring

/-- Every open set of the coordinate Alexandrov space is an upper set. -/
theorem isUpperSet_opens (U : Opens (upperSpace (Fin n → ℝ))) :
    IsUpperSet (U : Set (WithUpperSet (Fin n → ℝ))) :=
  Topology.IsUpperSet.isOpen_iff_isUpperSet.mp U.isOpen

/-- Membership in the preimage of `U` under `x ↦ x - ε · 1`. -/
theorem mem_map_translate (ε : ℝ≥0) (U : Opens (upperSpace (Fin n → ℝ)))
    (x : WithUpperSet (Fin n → ℝ)) :
    x ∈ (Opens.map (translate ε)).obj U ↔
      WithUpperSet.toUpperSet (downTranslation ε (WithUpperSet.ofUpperSet (α := Fin n → ℝ) x)) ∈
        U :=
  Iff.rfl

/-- The preimage of an open `U` under `x ↦ x - ε · 1` is the translate `U + ε · 1`, the image of
`U` under `CoordinateShift.translation ε`. -/
theorem coe_map_translate (ε : ℝ≥0) (U : Opens (upperSpace (Fin n → ℝ))) :
    ((Opens.map (translate ε)).obj U : Set (WithUpperSet (Fin n → ℝ))) =
      WithUpperSet.map (CoordinateShift.translation ε) '' (U : Set (WithUpperSet (Fin n → ℝ))) := by
  ext x
  constructor
  · intro hx
    refine ⟨translate ε x, hx, ?_⟩
    change WithUpperSet.toUpperSet (CoordinateShift.translation ε
      (downTranslation ε (WithUpperSet.ofUpperSet (α := Fin n → ℝ) x))) = x
    rw [translation_downTranslation]
    rfl
  · rintro ⟨y, hy, rfl⟩
    change WithUpperSet.toUpperSet (downTranslation ε
      (CoordinateShift.translation ε (WithUpperSet.ofUpperSet (α := Fin n → ℝ) y))) ∈ U
    rw [downTranslation_translation]
    exact hy

/-- The principal open `↑a` pulls back to `↑(a + ε · 1)`, coordinatewise:
`a_i ≤ x_i - ε ↔ a_i + ε ≤ x_i`. -/
theorem map_translate_principalOpen (ε : ℝ≥0) (a : Fin n → ℝ) :
    (Opens.map (translate ε)).obj
        (_root_.Alexandrov.principalOpen (X := upperSpace (Fin n → ℝ))
          (WithUpperSet.toUpperSet a)) =
      _root_.Alexandrov.principalOpen (X := upperSpace (Fin n → ℝ))
        (WithUpperSet.toUpperSet (CoordinateShift.translation ε a)) := by
  ext x
  change (∀ i, a i ≤ WithUpperSet.ofUpperSet (α := Fin n → ℝ) x i - (ε : ℝ)) ↔
    ∀ i, a i + (ε : ℝ) ≤ WithUpperSet.ofUpperSet (α := Fin n → ℝ) x i
  exact forall_congr' fun _ => le_sub_iff_add_le

/-- For `ε ≤ δ`, the translate `U + δ · 1` is contained in `U + ε · 1`. -/
theorem map_translate_antitone {ε δ : ℝ≥0} (h : ε ≤ δ) (U : Opens (upperSpace (Fin n → ℝ))) :
    (Opens.map (translate δ)).obj U ≤ (Opens.map (translate ε)).obj U := by
  intro x hx
  exact isUpperSet_opens U
    (show downTranslation δ (WithUpperSet.ofUpperSet (α := Fin n → ℝ) x) ≤
        downTranslation ε (WithUpperSet.ofUpperSet (α := Fin n → ℝ) x) from
      fun _ => sub_le_sub_left (NNReal.coe_le_coe.mpr h) _) hx

/-- The translate `U + ε · 1` is contained in `U`. -/
theorem map_translate_le (ε : ℝ≥0) (U : Opens (upperSpace (Fin n → ℝ))) :
    (Opens.map (translate ε)).obj U ≤ U := by
  intro x hx
  exact isUpperSet_opens U
    (show downTranslation ε (WithUpperSet.ofUpperSet (α := Fin n → ℝ) x) ≤
        WithUpperSet.ofUpperSet (α := Fin n → ℝ) x from
      fun _ => sub_le_self _ ε.coe_nonneg) hx

/-- Translation by zero fixes every open. -/
theorem map_translate_zero (U : Opens (upperSpace (Fin n → ℝ))) :
    (Opens.map (translate 0)).obj U = U := by
  ext x
  change translate 0 x ∈ U ↔ x ∈ U
  rw [translate_zero_apply]

/-- Translating by `ε` and then by `δ` is translating by `ε + δ`:
`(U + ε · 1) + δ · 1 = U + (ε + δ) · 1`. -/
theorem map_translate_comp (ε δ : ℝ≥0) (U : Opens (upperSpace (Fin n → ℝ))) :
    (Opens.map (translate δ)).obj ((Opens.map (translate ε)).obj U) =
      (Opens.map (translate (ε + δ))).obj U := by
  ext x
  change translate ε (translate δ x) ∈ U ↔ translate (ε + δ) x ∈ U
  rw [translate_translate_apply]

/-! ## The sheaf shift -/

section Shift

variable (C : Type u) [Category.{v} C]

/-- The sheaf shift `S ε`: pushforward along `x ↦ x - ε · 1`. Its value on an open `U` is the
value of `F` on `U + ε · 1`. -/
def sheafShift (ε : ℝ≥0) :
    (upperSpace (Fin n → ℝ)).Sheaf C ⥤ (upperSpace (Fin n → ℝ)).Sheaf C :=
  TopCat.Sheaf.pushforward C (translate ε)

variable {C}

/-- The shifted sheaf has the pushforward presheaf. -/
theorem sheafShift_obj_presheaf (ε : ℝ≥0) (F : (upperSpace (Fin n → ℝ)).Sheaf C) :
    ((sheafShift C ε).obj F).presheaf = (Opens.map (translate ε)).op ⋙ F.presheaf :=
  rfl

/-- `(S ε F)(U) = F(U + ε · 1)`, with `U + ε · 1` the preimage of `U` under `x ↦ x - ε · 1`. -/
theorem sheafShift_obj_presheaf_obj (ε : ℝ≥0) (F : (upperSpace (Fin n → ℝ)).Sheaf C)
    (U : Opens (upperSpace (Fin n → ℝ))) :
    ((sheafShift C ε).obj F).presheaf.obj (op U) =
      F.presheaf.obj (op ((Opens.map (translate ε)).obj U)) :=
  rfl

/-- On principal opens, `(S ε F)(↑a) = F(↑(a + ε · 1))`. -/
theorem sheafShift_obj_presheaf_obj_principalOpen (ε : ℝ≥0)
    (F : (upperSpace (Fin n → ℝ)).Sheaf C) (a : Fin n → ℝ) :
    ((sheafShift C ε).obj F).presheaf.obj
        (op (_root_.Alexandrov.principalOpen (X := upperSpace (Fin n → ℝ))
          (WithUpperSet.toUpperSet a))) =
      F.presheaf.obj (op (_root_.Alexandrov.principalOpen (X := upperSpace (Fin n → ℝ))
        (WithUpperSet.toUpperSet (CoordinateShift.translation ε a)))) := by
  rw [sheafShift_obj_presheaf_obj, map_translate_principalOpen]

/-- The restriction maps of the shifted sheaf are restrictions of `F` between translates. -/
theorem sheafShift_obj_presheaf_map (ε : ℝ≥0) (F : (upperSpace (Fin n → ℝ)).Sheaf C)
    {U V : (Opens (upperSpace (Fin n → ℝ)))ᵒᵖ} (f : U ⟶ V) :
    ((sheafShift C ε).obj F).presheaf.map f =
      F.presheaf.map ((Opens.map (translate ε)).op.map f) :=
  rfl

/-- The shift acts on morphisms by Mathlib's pushforward map: the component on `U` is the
component on `U + ε · 1`. -/
@[simp]
theorem sheafShift_map_hom_app (ε : ℝ≥0) {F G : (upperSpace (Fin n → ℝ)).Sheaf C} (φ : F ⟶ G)
    (U : Opens (upperSpace (Fin n → ℝ))) :
    ((sheafShift C ε).map φ).hom.app (op U) =
      φ.hom.app (op ((Opens.map (translate ε)).obj U)) :=
  rfl

/-- The shift of a morphism is `TopCat.Sheaf.pushforward_map`. -/
theorem sheafShift_map_hom (ε : ℝ≥0) {F G : (upperSpace (Fin n → ℝ)).Sheaf C} (φ : F ⟶ G) :
    ((sheafShift C ε).map φ).hom = (TopCat.Presheaf.pushforward C (translate ε)).map φ.hom :=
  TopCat.Sheaf.pushforward_map (translate ε) φ

variable (C)

/-- The order map `S ε ⟶ S δ` for `ε ≤ δ`: restriction along `U + δ · 1 ⊆ U + ε · 1`. -/
def sheafShiftLE {ε δ : ℝ≥0} (h : ε ≤ δ) : sheafShift (n := n) C ε ⟶ sheafShift C δ where
  app F := ObjectProperty.homMk
    { app := fun U => F.presheaf.map (homOfLE (map_translate_antitone h U.unop)).op
      naturality := fun U V f => by
        change F.presheaf.map _ ≫ F.presheaf.map _ = F.presheaf.map _ ≫ F.presheaf.map _
        rw [← F.presheaf.map_comp, ← F.presheaf.map_comp]
        exact presheaf_map_eq _ _ _ }
  naturality F G φ := by
    apply CategoryTheory.Sheaf.hom_ext
    ext U
    exact (φ.hom.naturality _).symm

/-- The transition `F ⟶ S ε F`: restriction along `U + ε · 1 ⊆ U`. -/
def sheafTransition (ε : ℝ≥0) : 𝟭 ((upperSpace (Fin n → ℝ)).Sheaf C) ⟶ sheafShift C ε where
  app F := ObjectProperty.homMk
    { app := fun U => F.presheaf.map (homOfLE (map_translate_le ε U.unop)).op
      naturality := fun U V f => by
        change F.presheaf.map _ ≫ F.presheaf.map _ = F.presheaf.map _ ≫ F.presheaf.map _
        rw [← F.presheaf.map_comp, ← F.presheaf.map_comp]
        exact presheaf_map_eq _ _ _ }
  naturality F G φ := by
    apply CategoryTheory.Sheaf.hom_ext
    ext U
    exact (φ.hom.naturality _).symm

/-- The zero natural isomorphism `S 0 ≅ 𝟭`, by the equality `U + 0 · 1 = U`. -/
def sheafZeroIso : sheafShift C 0 ≅ 𝟭 ((upperSpace (Fin n → ℝ)).Sheaf C) :=
  NatIso.ofComponents
    (fun F => ObjectProperty.isoMk _ (NatIso.ofComponents
      (fun U => restrictIso F.presheaf (map_translate_zero U.unop))
      (fun {U V} f => by
        change F.presheaf.map _ ≫ F.presheaf.map _ = F.presheaf.map _ ≫ F.presheaf.map _
        rw [← F.presheaf.map_comp, ← F.presheaf.map_comp]
        exact presheaf_map_eq _ _ _)))
    (fun {F G} φ => by
      apply CategoryTheory.Sheaf.hom_ext
      ext U
      exact (φ.hom.naturality _).symm)

/-- The addition natural isomorphism `S δ ⋙ S ε ≅ S (ε + δ)`, whose component at `F` is
`S ε (S δ F) ≅ S (ε + δ) F`, by `(U + ε · 1) + δ · 1 = U + (ε + δ) · 1`. -/
def sheafCompIso (ε δ : ℝ≥0) :
    sheafShift (n := n) C δ ⋙ sheafShift C ε ≅ sheafShift C (ε + δ) :=
  NatIso.ofComponents
    (fun F => ObjectProperty.isoMk _ (NatIso.ofComponents
      (fun U => restrictIso F.presheaf (map_translate_comp ε δ U.unop))
      (fun {U V} f => by
        change F.presheaf.map _ ≫ F.presheaf.map _ = F.presheaf.map _ ≫ F.presheaf.map _
        rw [← F.presheaf.map_comp, ← F.presheaf.map_comp]
        exact presheaf_map_eq _ _ _)))
    (fun {F G} φ => by
      apply CategoryTheory.Sheaf.hom_ext
      ext U
      exact (φ.hom.naturality _).symm)

/-- Equal parameters give the natural isomorphism `S ε ≅ S δ` along
`U + ε · 1 = U + δ · 1`. -/
def sheafCongrIso {ε δ : ℝ≥0} (h : ε = δ) : sheafShift (n := n) C ε ≅ sheafShift C δ :=
  NatIso.ofComponents
    (fun F => ObjectProperty.isoMk _ (NatIso.ofComponents
      (fun U => restrictIso F.presheaf
        (congrArg (fun e => (Opens.map (translate e)).obj U.unop) h))
      (fun {U V} f => by
        change F.presheaf.map _ ≫ F.presheaf.map _ = F.presheaf.map _ ≫ F.presheaf.map _
        rw [← F.presheaf.map_comp, ← F.presheaf.map_comp]
        exact presheaf_map_eq _ _ _)))
    (fun {F G} φ => by
      apply CategoryTheory.Sheaf.hom_ext
      ext U
      exact (φ.hom.naturality _).symm)

variable {C}

@[simp]
theorem sheafShiftLE_app_hom_app {ε δ : ℝ≥0} (h : ε ≤ δ) (F : (upperSpace (Fin n → ℝ)).Sheaf C)
    (U : Opens (upperSpace (Fin n → ℝ))) :
    ((sheafShiftLE C h).app F).hom.app (op U) =
      F.presheaf.map (homOfLE (map_translate_antitone h U)).op :=
  rfl

@[simp]
theorem sheafTransition_app_hom_app (ε : ℝ≥0) (F : (upperSpace (Fin n → ℝ)).Sheaf C)
    (U : Opens (upperSpace (Fin n → ℝ))) :
    ((sheafTransition C ε).app F).hom.app (op U) =
      F.presheaf.map (homOfLE (map_translate_le ε U)).op :=
  rfl

@[simp]
theorem sheafZeroIso_hom_app_hom_app (F : (upperSpace (Fin n → ℝ)).Sheaf C)
    (U : Opens (upperSpace (Fin n → ℝ))) :
    ((sheafZeroIso C).hom.app F).hom.app (op U) =
      F.presheaf.map (homOfLE (map_translate_zero U).ge).op :=
  rfl

@[simp]
theorem sheafZeroIso_inv_app_hom_app (F : (upperSpace (Fin n → ℝ)).Sheaf C)
    (U : Opens (upperSpace (Fin n → ℝ))) :
    ((sheafZeroIso C).inv.app F).hom.app (op U) =
      F.presheaf.map (homOfLE (map_translate_zero U).le).op :=
  rfl

@[simp]
theorem sheafCompIso_hom_app_hom_app (ε δ : ℝ≥0) (F : (upperSpace (Fin n → ℝ)).Sheaf C)
    (U : Opens (upperSpace (Fin n → ℝ))) :
    ((sheafCompIso C ε δ).hom.app F).hom.app (op U) =
      F.presheaf.map (homOfLE (map_translate_comp ε δ U).ge).op :=
  rfl

@[simp]
theorem sheafCompIso_inv_app_hom_app (ε δ : ℝ≥0) (F : (upperSpace (Fin n → ℝ)).Sheaf C)
    (U : Opens (upperSpace (Fin n → ℝ))) :
    ((sheafCompIso C ε δ).inv.app F).hom.app (op U) =
      F.presheaf.map (homOfLE (map_translate_comp ε δ U).le).op :=
  rfl

@[simp]
theorem sheafCongrIso_hom_app_hom_app {ε δ : ℝ≥0} (h : ε = δ)
    (F : (upperSpace (Fin n → ℝ)).Sheaf C) (U : Opens (upperSpace (Fin n → ℝ))) :
    ((sheafCongrIso C h).hom.app F).hom.app (op U) =
      F.presheaf.map
        (homOfLE (congrArg (fun e => (Opens.map (translate e)).obj U) h).ge).op :=
  rfl

/-! ### Coherence

Every law below is the equality of two composites of restrictions of `F` between the same
opens. -/

/-- The order map for `ε ≤ ε` is the identity. -/
theorem sheafShiftLE_refl (ε : ℝ≥0) :
    sheafShiftLE C (le_refl ε) = 𝟙 (sheafShift (n := n) C ε) := by
  apply NatTrans.ext
  funext F
  apply CategoryTheory.Sheaf.hom_ext
  ext U
  exact (presheaf_map_eq _ _ _).trans (F.presheaf.map_id _)

/-- Order maps compose. -/
theorem sheafShiftLE_comp {ε δ γ : ℝ≥0} (h : ε ≤ δ) (h' : δ ≤ γ) :
    sheafShiftLE (n := n) C h ≫ sheafShiftLE C h' = sheafShiftLE C (h.trans h') := by
  apply NatTrans.ext
  funext F
  apply CategoryTheory.Sheaf.hom_ext
  ext U
  exact (F.presheaf.map_comp _ _).symm.trans (presheaf_map_eq _ _ _)

/-- The transition followed by an order map is the transition of the larger parameter. -/
theorem sheafTransition_comp_shiftLE {ε δ : ℝ≥0} (h : ε ≤ δ) :
    sheafTransition (n := n) C ε ≫ sheafShiftLE C h = sheafTransition C δ := by
  apply NatTrans.ext
  funext F
  apply CategoryTheory.Sheaf.hom_ext
  ext U
  exact (F.presheaf.map_comp _ _).symm.trans (presheaf_map_eq _ _ _)

/-- At zero, the transition followed by the zero isomorphism is the identity. -/
theorem sheafTransition_zero (F : (upperSpace (Fin n → ℝ)).Sheaf C) :
    (sheafTransition C 0).app F ≫ (sheafZeroIso C).hom.app F = 𝟙 F := by
  apply CategoryTheory.Sheaf.hom_ext
  ext U
  exact (F.presheaf.map_comp _ _).symm.trans
    ((presheaf_map_eq _ _ _).trans (F.presheaf.map_id _))

/-- The zero transition is the inverse zero isomorphism. -/
theorem sheafTransition_zero_eq (F : (upperSpace (Fin n → ℝ)).Sheaf C) :
    (sheafTransition C 0).app F = (sheafZeroIso C).inv.app F := by
  rw [← cancel_mono ((sheafZeroIso C).hom.app F), sheafTransition_zero, Iso.inv_hom_id_app]
  rfl

/-- Two transitions compose to the transition by the sum. -/
theorem sheafTransition_add (ε δ : ℝ≥0) (F : (upperSpace (Fin n → ℝ)).Sheaf C) :
    (sheafTransition C ε).app F ≫ (sheafShift C ε).map ((sheafTransition C δ).app F) ≫
        (sheafCompIso C ε δ).hom.app F =
      (sheafTransition C (ε + δ)).app F := by
  apply CategoryTheory.Sheaf.hom_ext
  ext U
  change F.presheaf.map _ ≫ F.presheaf.map _ ≫ F.presheaf.map _ = F.presheaf.map _
  rw [← F.presheaf.map_comp, ← F.presheaf.map_comp]
  exact presheaf_map_eq _ _ _

/-- Transitions respect equal parameters. -/
theorem sheafTransition_congr {ε δ : ℝ≥0} (h : ε = δ) (F : (upperSpace (Fin n → ℝ)).Sheaf C) :
    (sheafTransition C ε).app F ≫ (sheafCongrIso C h).hom.app F =
      (sheafTransition C δ).app F := by
  apply CategoryTheory.Sheaf.hom_ext
  ext U
  exact (F.presheaf.map_comp _ _).symm.trans (presheaf_map_eq _ _ _)

/-- Reflexive parameter transport is the identity. -/
theorem sheafCongrIso_refl (ε : ℝ≥0) :
    sheafCongrIso (n := n) C (rfl : ε = ε) = Iso.refl _ := by
  apply Iso.ext
  apply NatTrans.ext
  funext F
  apply CategoryTheory.Sheaf.hom_ext
  ext U
  exact (presheaf_map_eq _ _ _).trans (F.presheaf.map_id _)

/-- Left unit law of the addition isomorphism. -/
theorem sheafCompIso_zero_left (ε : ℝ≥0) (F : (upperSpace (Fin n → ℝ)).Sheaf C) :
    (sheafCompIso C 0 ε).hom.app F ≫ (sheafCongrIso C (zero_add ε)).hom.app F =
      (sheafZeroIso C).hom.app ((sheafShift C ε).obj F) := by
  apply CategoryTheory.Sheaf.hom_ext
  ext U
  exact (F.presheaf.map_comp _ _).symm.trans (presheaf_map_eq _ _ _)

/-- Right unit law of the addition isomorphism. -/
theorem sheafCompIso_zero_right (ε : ℝ≥0) (F : (upperSpace (Fin n → ℝ)).Sheaf C) :
    (sheafCompIso C ε 0).hom.app F ≫ (sheafCongrIso C (add_zero ε)).hom.app F =
      (sheafShift C ε).map ((sheafZeroIso C).hom.app F) := by
  apply CategoryTheory.Sheaf.hom_ext
  ext U
  exact (F.presheaf.map_comp _ _).symm.trans (presheaf_map_eq _ _ _)

/-- Associativity of the addition isomorphism. -/
theorem sheafCompIso_assoc (ε δ γ : ℝ≥0) (F : (upperSpace (Fin n → ℝ)).Sheaf C) :
    (sheafCompIso C ε δ).hom.app ((sheafShift C γ).obj F) ≫
        (sheafCompIso C (ε + δ) γ).hom.app F =
      (sheafShift C ε).map ((sheafCompIso C δ γ).hom.app F) ≫
        (sheafCompIso C ε (δ + γ)).hom.app F ≫
          (sheafCongrIso C (add_assoc ε δ γ).symm).hom.app F := by
  apply CategoryTheory.Sheaf.hom_ext
  ext U
  change F.presheaf.map _ ≫ F.presheaf.map _ = F.presheaf.map _ ≫ F.presheaf.map _ ≫
    F.presheaf.map _
  rw [← F.presheaf.map_comp, ← F.presheaf.map_comp, ← F.presheaf.map_comp]
  exact presheaf_map_eq _ _ _

end Shift

/-! ## Principal sections on the coordinate space -/

section Sections

variable (C : Type u) [Category.{0} C]

/-- The principal-sections functor `Γ` read on `Fin n → ℝ`: `Γ(F)(a) = F(↑a)`, and for `a ≤ b`
the map `Γ(F)(a) ⟶ Γ(F)(b)` is the restriction along `↑b ⊆ ↑a`. -/
def coordinateSections : (upperSpace (Fin n → ℝ)).Sheaf C ⥤ ((Fin n → ℝ) ⥤ C) :=
  principalSections (upperSpace (Fin n → ℝ)) C ⋙
    (Functor.whiskeringLeft (Fin n → ℝ) (upperSpace (Fin n → ℝ)) C).obj
      (WithUpperSet.toUpperSetOrderIso (α := Fin n → ℝ)).monotone.functor

variable {C}

@[simp]
theorem coordinateSections_obj_obj (F : (upperSpace (Fin n → ℝ)).Sheaf C) (a : Fin n → ℝ) :
    ((coordinateSections C).obj F).obj a =
      F.presheaf.obj
        (op (_root_.Alexandrov.principalOpen (X := upperSpace (Fin n → ℝ))
          (WithUpperSet.toUpperSet a))) :=
  rfl

@[simp]
theorem coordinateSections_obj_map (F : (upperSpace (Fin n → ℝ)).Sheaf C) {a b : Fin n → ℝ}
    (f : a ⟶ b) :
    ((coordinateSections C).obj F).map f =
      F.presheaf.map (homOfLE (_root_.Alexandrov.principalOpen_le (X := upperSpace (Fin n → ℝ))
        (x := WithUpperSet.toUpperSet a) (y := WithUpperSet.toUpperSet b) (leOfHom f))).op :=
  rfl

@[simp]
theorem coordinateSections_map_app {F G : (upperSpace (Fin n → ℝ)).Sheaf C} (φ : F ⟶ G)
    (a : Fin n → ℝ) :
    ((coordinateSections C).map φ).app a =
      φ.hom.app
        (op (_root_.Alexandrov.principalOpen (X := upperSpace (Fin n → ℝ))
          (WithUpperSet.toUpperSet a))) :=
  rfl

variable [HasLimits C]

/-- `Γ` is the inverse functor of `upperSetEquivalence (Fin n → ℝ) C`. -/
theorem coordinateSections_eq :
    coordinateSections (n := n) C = (upperSetEquivalence (Fin n → ℝ) C).inverse :=
  rfl

/-- `Γ` is fully faithful on actual sheaves, as the inverse of
`upperSetEquivalence (Fin n → ℝ) C`. -/
def coordinateSectionsFullyFaithful : (coordinateSections (n := n) C).FullyFaithful :=
  (upperSetEquivalence (Fin n → ℝ) C).fullyFaithfulInverse

instance coordinateSections_full : (coordinateSections (n := n) C).Full :=
  coordinateSectionsFullyFaithful.full

instance coordinateSections_faithful : (coordinateSections (n := n) C).Faithful :=
  coordinateSectionsFullyFaithful.faithful

end Sections

/-! ## Comparison with the coordinate shift -/

section Comparison

variable (R : Type u) [Ring R]

/-- The comparison `S ε ⋙ Γ ≅ Γ ⋙ CoordinateShift.shift ε`: at `F` and `a`, the restriction
along the equality `↑a + ε · 1 = ↑(a + ε · 1)` of opens. -/
def shiftComparison (ε : ℝ≥0) :
    sheafShift (n := n) (ModuleCat.{0} R) ε ⋙ coordinateSections (ModuleCat.{0} R) ≅
      coordinateSections (ModuleCat.{0} R) ⋙ CoordinateShift.shift ε :=
  NatIso.ofComponents
    (fun F => NatIso.ofComponents
      (fun a => restrictIso F.presheaf (map_translate_principalOpen ε a))
      (fun {a b} f => presheaf_map_comp_map_eq F.presheaf _ _ _ _))
    (fun {F G} φ => by
      apply NatTrans.ext
      funext a
      exact (φ.hom.naturality _).symm)

variable {R}

@[simp]
theorem shiftComparison_hom_app_app (ε : ℝ≥0)
    (F : (upperSpace (Fin n → ℝ)).Sheaf (ModuleCat.{0} R)) (a : Fin n → ℝ) :
    ((shiftComparison R ε).hom.app F).app a =
      F.presheaf.map (homOfLE (map_translate_principalOpen ε a).ge).op :=
  rfl

@[simp]
theorem shiftComparison_inv_app_app (ε : ℝ≥0)
    (F : (upperSpace (Fin n → ℝ)).Sheaf (ModuleCat.{0} R)) (a : Fin n → ℝ) :
    ((shiftComparison R ε).inv.app F).app a =
      F.presheaf.map (homOfLE (map_translate_principalOpen ε a).le).op :=
  rfl

/-- Naturality of the comparison in the sheaf. -/
@[reassoc]
theorem shiftComparison_hom_naturality (ε : ℝ≥0)
    {F G : (upperSpace (Fin n → ℝ)).Sheaf (ModuleCat.{0} R)} (φ : F ⟶ G) :
    (coordinateSections _).map ((sheafShift _ ε).map φ) ≫ (shiftComparison R ε).hom.app G =
      (shiftComparison R ε).hom.app F ≫
        (CoordinateShift.shift ε).map ((coordinateSections _).map φ) :=
  (shiftComparison R ε).hom.naturality φ

/-- The comparison carries the sheaf order map to `CoordinateShift.shiftLE`. -/
@[reassoc]
theorem shiftComparison_shiftLE {ε δ : ℝ≥0} (h : ε ≤ δ)
    (F : (upperSpace (Fin n → ℝ)).Sheaf (ModuleCat.{0} R)) :
    (coordinateSections _).map ((sheafShiftLE _ h).app F) ≫ (shiftComparison R δ).hom.app F =
      (shiftComparison R ε).hom.app F ≫
        CoordinateShift.shiftLE h ((coordinateSections _).obj F) := by
  apply NatTrans.ext
  funext a
  exact presheaf_map_comp_map_eq F.presheaf _ _ _ _

/-- The comparison carries the sheaf transition to `CoordinateShift.transition`. -/
@[reassoc]
theorem shiftComparison_transition (ε : ℝ≥0)
    (F : (upperSpace (Fin n → ℝ)).Sheaf (ModuleCat.{0} R)) :
    (coordinateSections _).map ((sheafTransition _ ε).app F) ≫ (shiftComparison R ε).hom.app F =
      CoordinateShift.transition ε ((coordinateSections _).obj F) := by
  apply NatTrans.ext
  funext a
  exact presheaf_map_comp_map F.presheaf _ _ _

/-- The comparison carries the sheaf zero isomorphism to `CoordinateShift.zeroIso`. -/
theorem shiftComparison_zeroIso (F : (upperSpace (Fin n → ℝ)).Sheaf (ModuleCat.{0} R)) :
    (coordinateSections _).map ((sheafZeroIso _).hom.app F) =
      (shiftComparison R 0).hom.app F ≫
        (CoordinateShift.zeroIso ((coordinateSections _).obj F)).hom := by
  apply NatTrans.ext
  funext a
  exact (presheaf_map_comp_map F.presheaf _ _ _).symm

/-- The comparison carries the sheaf addition isomorphism to `CoordinateShift.compIso`. -/
@[reassoc]
theorem shiftComparison_compIso (ε δ : ℝ≥0)
    (F : (upperSpace (Fin n → ℝ)).Sheaf (ModuleCat.{0} R)) :
    (coordinateSections _).map ((sheafCompIso _ ε δ).hom.app F) ≫
        (shiftComparison R (ε + δ)).hom.app F =
      (shiftComparison R ε).hom.app ((sheafShift _ δ).obj F) ≫
        (CoordinateShift.shift ε).map ((shiftComparison R δ).hom.app F) ≫
          (CoordinateShift.compIso ε δ ((coordinateSections _).obj F)).hom := by
  apply NatTrans.ext
  funext a
  exact presheaf_map_comp_map_eq_comp F.presheaf _ _ _ _ _

end Comparison

/-! ## Sheaf interleavings -/

section Interleaving

variable {C : Type u} [Category.{v} C]

/-- A sheaf `ε`-interleaving on the coordinate Alexandrov space, in the orientation of
`CoordinateInterleaving`: arrows `F ⟶ S ε G` and `G ⟶ S ε F` whose two double-shift composites,
through the addition isomorphism, are the transitions by `ε + ε`. -/
structure SheafInterleaving (ε : ℝ≥0) (F G : (upperSpace (Fin n → ℝ)).Sheaf C) where
  /-- The arrow from the first sheaf to the shifted second sheaf. -/
  φ : F ⟶ (sheafShift C ε).obj G
  /-- The arrow from the second sheaf to the shifted first sheaf. -/
  ψ : G ⟶ (sheafShift C ε).obj F
  /-- The first composite is the double-shift transition. -/
  φ_ψ : φ ≫ (sheafShift C ε).map ψ ≫ (sheafCompIso C ε ε).hom.app F =
    (sheafTransition C (ε + ε)).app F
  /-- The second composite is the double-shift transition. -/
  ψ_φ : ψ ≫ (sheafShift C ε).map φ ≫ (sheafCompIso C ε ε).hom.app G =
    (sheafTransition C (ε + ε)).app G

namespace SheafInterleaving

variable {ε : ℝ≥0} {F G : (upperSpace (Fin n → ℝ)).Sheaf C}

/-- Two sheaf witnesses agree when their two arrows agree. -/
@[ext]
theorem ext {i j : SheafInterleaving ε F G} (hφ : i.φ = j.φ) (hψ : i.ψ = j.ψ) : i = j := by
  cases i; cases j; cases hφ; cases hψ; rfl

/-- Interchange the two arrows. -/
def symm (i : SheafInterleaving ε F G) : SheafInterleaving ε G F :=
  ⟨i.ψ, i.φ, i.ψ_φ, i.φ_ψ⟩

/-- A sheaf is interleaved with itself by its transitions. -/
def refl (ε : ℝ≥0) (F : (upperSpace (Fin n → ℝ)).Sheaf C) : SheafInterleaving ε F F :=
  ⟨(sheafTransition C ε).app F, (sheafTransition C ε).app F, sheafTransition_add ε ε F,
    sheafTransition_add ε ε F⟩

end SheafInterleaving

/-- The extended-infimum interleaving distance of sheaves on the coordinate Alexandrov space. -/
def sheafInterleavingDistance (F G : (upperSpace (Fin n → ℝ)).Sheaf C) : ℝ≥0∞ :=
  ⨅ (ε : ℝ≥0) (_ : Nonempty (SheafInterleaving ε F G)), (ε : ℝ≥0∞)

end Interleaving

/-! ## Sheaf and module witnesses -/

section Witnesses

variable {R : Type u} [Ring R]
variable {ε : ℝ≥0} {F G : (upperSpace (Fin n → ℝ)).Sheaf (ModuleCat.{0} R)}

/-- Under `Γ` and the comparison, the sheaf double-shift composite becomes the module one. -/
theorem coordinateSections_map_doubleShift (f : F ⟶ (sheafShift _ ε).obj G)
    (g : G ⟶ (sheafShift _ ε).obj F) :
    (coordinateSections _).map (f ≫ (sheafShift _ ε).map g ≫ (sheafCompIso _ ε ε).hom.app F) ≫
        (shiftComparison R (ε + ε)).hom.app F =
      ((coordinateSections _).map f ≫ (shiftComparison R ε).hom.app G) ≫
        (CoordinateShift.shift ε).map
          ((coordinateSections _).map g ≫ (shiftComparison R ε).hom.app F) ≫
          (CoordinateShift.compIso ε ε ((coordinateSections _).obj F)).hom := by
  simp only [Functor.map_comp, Category.assoc]
  rw [shiftComparison_compIso, shiftComparison_hom_naturality_assoc]

/-- A pair of sheaf arrows satisfies the sheaf double-shift equation exactly when its image
under `Γ` and the comparison satisfies the module equation. -/
theorem doubleShift_iff (f : F ⟶ (sheafShift _ ε).obj G) (g : G ⟶ (sheafShift _ ε).obj F) :
    f ≫ (sheafShift _ ε).map g ≫ (sheafCompIso _ ε ε).hom.app F =
        (sheafTransition _ (ε + ε)).app F ↔
      ((coordinateSections _).map f ≫ (shiftComparison R ε).hom.app G) ≫
          (CoordinateShift.shift ε).map
            ((coordinateSections _).map g ≫ (shiftComparison R ε).hom.app F) ≫
            (CoordinateShift.compIso ε ε ((coordinateSections _).obj F)).hom =
        CoordinateShift.transition (ε + ε) ((coordinateSections _).obj F) := by
  rw [← coordinateSections_map_doubleShift, ← shiftComparison_transition]
  constructor
  · intro h
    rw [h]
  · intro h
    exact coordinateSectionsFullyFaithful.map_injective ((cancel_mono _).mp h)

/-- `Γ` of the lift of a module arrow, followed by the comparison, is the module arrow. -/
theorem map_preimage_comp_shiftComparison
    (a : (coordinateSections _).obj F ⟶
      (CoordinateShift.shift ε).obj ((coordinateSections _).obj G)) :
    (coordinateSections _).map (coordinateSectionsFullyFaithful.preimage
        (a ≫ (shiftComparison R ε).inv.app G)) ≫ (shiftComparison R ε).hom.app G = a := by
  rw [Functor.FullyFaithful.map_preimage, Category.assoc, Iso.inv_hom_id_app]
  exact Category.comp_id _

namespace SheafInterleaving

/-- The module witness of a sheaf witness: apply `Γ`, then the comparison. -/
def toCoordinateInterleaving (i : SheafInterleaving ε F G) :
    CoordinateInterleaving ε ((coordinateSections _).obj F) ((coordinateSections _).obj G) where
  φ := (coordinateSections _).map i.φ ≫ (shiftComparison R ε).hom.app G
  ψ := (coordinateSections _).map i.ψ ≫ (shiftComparison R ε).hom.app F
  φ_ψ := (doubleShift_iff i.φ i.ψ).mp i.φ_ψ
  ψ_φ := (doubleShift_iff i.ψ i.φ).mp i.ψ_φ

/-- The sheaf witness of a module witness: compose with the inverse comparison and lift along
the fully faithful `Γ`. -/
def ofCoordinateInterleaving
    (j : CoordinateInterleaving ε ((coordinateSections _).obj F)
      ((coordinateSections _).obj G)) :
    SheafInterleaving ε F G where
  φ := coordinateSectionsFullyFaithful.preimage (j.φ ≫ (shiftComparison R ε).inv.app G)
  ψ := coordinateSectionsFullyFaithful.preimage (j.ψ ≫ (shiftComparison R ε).inv.app F)
  φ_ψ := (doubleShift_iff _ _).mpr (by
    rw [map_preimage_comp_shiftComparison, map_preimage_comp_shiftComparison]
    exact j.φ_ψ)
  ψ_φ := (doubleShift_iff _ _).mpr (by
    rw [map_preimage_comp_shiftComparison, map_preimage_comp_shiftComparison]
    exact j.ψ_φ)

/-- Sheaf `ε`-interleavings of `F` and `G` are equivalent to coordinate `ε`-interleavings of
their principal sections. -/
def equivCoordinateInterleaving :
    SheafInterleaving ε F G ≃
      CoordinateInterleaving ε ((coordinateSections _).obj F) ((coordinateSections _).obj G)
    where
  toFun := toCoordinateInterleaving
  invFun := ofCoordinateInterleaving
  left_inv i := by
    apply SheafInterleaving.ext
    · apply coordinateSectionsFullyFaithful.map_injective
      change (coordinateSections _).map (coordinateSectionsFullyFaithful.preimage
        (((coordinateSections _).map i.φ ≫ (shiftComparison R ε).hom.app G) ≫
          (shiftComparison R ε).inv.app G)) = _
      rw [Functor.FullyFaithful.map_preimage, Category.assoc, Iso.hom_inv_id_app]
      exact Category.comp_id _
    · apply coordinateSectionsFullyFaithful.map_injective
      change (coordinateSections _).map (coordinateSectionsFullyFaithful.preimage
        (((coordinateSections _).map i.ψ ≫ (shiftComparison R ε).hom.app F) ≫
          (shiftComparison R ε).inv.app F)) = _
      rw [Functor.FullyFaithful.map_preimage, Category.assoc, Iso.hom_inv_id_app]
      exact Category.comp_id _
  right_inv j := CoordinateInterleaving.ext (map_preimage_comp_shiftComparison j.φ)
    (map_preimage_comp_shiftComparison j.ψ)

@[simp]
theorem equivCoordinateInterleaving_apply_φ (i : SheafInterleaving ε F G) :
    (equivCoordinateInterleaving i).φ =
      (coordinateSections _).map i.φ ≫ (shiftComparison R ε).hom.app G :=
  rfl

@[simp]
theorem equivCoordinateInterleaving_apply_ψ (i : SheafInterleaving ε F G) :
    (equivCoordinateInterleaving i).ψ =
      (coordinateSections _).map i.ψ ≫ (shiftComparison R ε).hom.app F :=
  rfl

/-- At a grade `a`, the first module arrow is the sheaf arrow over `↑a` followed by the
restriction along `↑a + ε · 1 = ↑(a + ε · 1)`. -/
theorem equivCoordinateInterleaving_apply_φ_app (i : SheafInterleaving ε F G) (a : Fin n → ℝ) :
    (equivCoordinateInterleaving i).φ.app a =
      i.φ.hom.app (op (_root_.Alexandrov.principalOpen (X := upperSpace (Fin n → ℝ))
          (WithUpperSet.toUpperSet a))) ≫
        G.presheaf.map (homOfLE (map_translate_principalOpen ε a).ge).op :=
  rfl

/-- At a grade `a`, the second module arrow is the sheaf arrow over `↑a` followed by the
restriction along `↑a + ε · 1 = ↑(a + ε · 1)`. -/
theorem equivCoordinateInterleaving_apply_ψ_app (i : SheafInterleaving ε F G) (a : Fin n → ℝ) :
    (equivCoordinateInterleaving i).ψ.app a =
      i.ψ.hom.app (op (_root_.Alexandrov.principalOpen (X := upperSpace (Fin n → ℝ))
          (WithUpperSet.toUpperSet a))) ≫
        F.presheaf.map (homOfLE (map_translate_principalOpen ε a).ge).op :=
  rfl

/-- The first arrow of the inverse image, read through `Γ` and the comparison, is the first
module arrow. -/
theorem map_equivCoordinateInterleaving_symm_φ
    (j : CoordinateInterleaving ε ((coordinateSections _).obj F)
      ((coordinateSections _).obj G)) :
    (coordinateSections _).map (equivCoordinateInterleaving.symm j).φ ≫
        (shiftComparison R ε).hom.app G = j.φ :=
  map_preimage_comp_shiftComparison j.φ

/-- The second arrow of the inverse image, read through `Γ` and the comparison, is the second
module arrow. -/
theorem map_equivCoordinateInterleaving_symm_ψ
    (j : CoordinateInterleaving ε ((coordinateSections _).obj F)
      ((coordinateSections _).obj G)) :
    (coordinateSections _).map (equivCoordinateInterleaving.symm j).ψ ≫
        (shiftComparison R ε).hom.app F = j.ψ :=
  map_preimage_comp_shiftComparison j.ψ

/-- At `ε = 0`, sheaf witnesses are equivalent to actual isomorphisms of sheaves. -/
def zeroEquivIso : SheafInterleaving 0 F G ≃ (F ≅ G) :=
  equivCoordinateInterleaving.trans
    (CoordinateInterleaving.zeroEquivIso.trans coordinateSectionsFullyFaithful.isoEquiv.symm)

/-- The isomorphism of a zero witness is its first arrow followed by the zero isomorphism. -/
theorem zeroEquivIso_apply_hom (i : SheafInterleaving 0 F G) :
    (zeroEquivIso i).hom = i.φ ≫ (sheafZeroIso _).hom.app G := by
  apply coordinateSectionsFullyFaithful.map_injective
  change (coordinateSections _).map (coordinateSectionsFullyFaithful.preimage
    (((coordinateSections _).map i.φ ≫ (shiftComparison R 0).hom.app G) ≫
      (CoordinateShift.zeroIso ((coordinateSections _).obj G)).hom)) = _
  rw [Functor.FullyFaithful.map_preimage, Functor.map_comp, shiftComparison_zeroIso,
    Category.assoc]

/-- The inverse of the isomorphism of a zero witness is its second arrow followed by the zero
isomorphism. -/
theorem zeroEquivIso_apply_inv (i : SheafInterleaving 0 F G) :
    (zeroEquivIso i).inv = i.ψ ≫ (sheafZeroIso _).hom.app F := by
  apply coordinateSectionsFullyFaithful.map_injective
  change (coordinateSections _).map (coordinateSectionsFullyFaithful.preimage
    (((coordinateSections _).map i.ψ ≫ (shiftComparison R 0).hom.app F) ≫
      (CoordinateShift.zeroIso ((coordinateSections _).obj F)).hom)) = _
  rw [Functor.FullyFaithful.map_preimage, Functor.map_comp, shiftComparison_zeroIso,
    Category.assoc]

end SheafInterleaving

/-- A sheaf witness exists exactly when a module witness exists for the principal sections. -/
theorem nonempty_sheafInterleaving_iff :
    Nonempty (SheafInterleaving ε F G) ↔
      Nonempty (CoordinateInterleaving ε ((coordinateSections _).obj F)
        ((coordinateSections _).obj G)) :=
  SheafInterleaving.equivCoordinateInterleaving.nonempty_congr

/-- Transport along isomorphisms and back along their inverses is the identity. -/
theorem _root_.TDA.Persistence.CoordinateInterleaving.congr_congr_symm
    {M N M' N' : PModule.{u,0,w} R (Fin n → ℝ)}
    (j : CoordinateInterleaving ε M N) (e : M ≅ M') (d : N ≅ N') :
    (j.congr e d).congr e.symm d.symm = j := by
  apply CoordinateInterleaving.ext
  · change e.symm.inv ≫ (e.inv ≫ j.φ ≫ (CoordinateShift.shift ε).map d.hom) ≫
      (CoordinateShift.shift ε).map d.symm.hom = j.φ
    simp only [Iso.symm_inv, Iso.symm_hom, Category.assoc, ← Functor.map_comp,
      Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.comp_id, Iso.hom_inv_id_assoc]
  · change d.symm.inv ≫ (d.inv ≫ j.ψ ≫ (CoordinateShift.shift ε).map e.hom) ≫
      (CoordinateShift.shift ε).map e.symm.hom = j.ψ
    simp only [Iso.symm_inv, Iso.symm_hom, Category.assoc, ← Functor.map_comp,
      Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.comp_id, Iso.hom_inv_id_assoc]

/-- Transport along inverse isomorphisms and back along the isomorphisms is the identity. -/
theorem _root_.TDA.Persistence.CoordinateInterleaving.congr_symm_congr
    {M N M' N' : PModule.{u,0,w} R (Fin n → ℝ)}
    (j : CoordinateInterleaving ε M N) (e : M' ≅ M) (d : N' ≅ N) :
    (j.congr e.symm d.symm).congr e d = j := by
  apply CoordinateInterleaving.ext
  · change e.inv ≫ (e.symm.inv ≫ j.φ ≫ (CoordinateShift.shift ε).map d.symm.hom) ≫
      (CoordinateShift.shift ε).map d.hom = j.φ
    simp only [Iso.symm_inv, Iso.symm_hom, Category.assoc, ← Functor.map_comp,
      Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.comp_id, Iso.inv_hom_id_assoc]
  · change d.inv ≫ (d.symm.inv ≫ j.ψ ≫ (CoordinateShift.shift ε).map e.symm.hom) ≫
      (CoordinateShift.shift ε).map e.hom = j.ψ
    simp only [Iso.symm_inv, Iso.symm_hom, Category.assoc, ← Functor.map_comp,
      Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.comp_id, Iso.inv_hom_id_assoc]

namespace SheafInterleaving

/-- For the sheaves attached to modules `M` and `N`, sheaf `ε`-interleavings are equivalent to
coordinate `ε`-interleavings of `M` and `N`: `equivCoordinateInterleaving`, followed by transport
along the unit of `upperSetEquivalence`. -/
def equivUpperSet (M N : PModule.{u,0,0} R (Fin n → ℝ)) :
    SheafInterleaving ε ((upperSetEquivalence (Fin n → ℝ) (ModuleCat.{0} R)).functor.obj M)
        ((upperSetEquivalence (Fin n → ℝ) (ModuleCat.{0} R)).functor.obj N) ≃
      CoordinateInterleaving ε M N where
  toFun i := (equivCoordinateInterleaving i).congr
    ((upperSetEquivalence (Fin n → ℝ) _).unitIso.app M).symm
    ((upperSetEquivalence (Fin n → ℝ) _).unitIso.app N).symm
  invFun j := equivCoordinateInterleaving.symm (j.congr
    ((upperSetEquivalence (Fin n → ℝ) _).unitIso.app M)
    ((upperSetEquivalence (Fin n → ℝ) _).unitIso.app N))
  left_inv _ :=
    (congrArg equivCoordinateInterleaving.symm
      (CoordinateInterleaving.congr_symm_congr _ _ _)).trans
      (Equiv.symm_apply_apply _ _)
  right_inv j :=
    (congrArg (fun k => CoordinateInterleaving.congr k _ _) (Equiv.apply_symm_apply _ _)).trans
      (CoordinateInterleaving.congr_congr_symm j _ _)

/-- At a grade `a`, the first arrow of `equivUpperSet i` is the sheaf arrow over `↑a`, conjugated
by the unit of `upperSetEquivalence` and the restriction along `↑a + ε · 1 = ↑(a + ε · 1)`. -/
theorem equivUpperSet_apply_φ_app (M N : PModule.{u,0,0} R (Fin n → ℝ))
    (i : SheafInterleaving ε ((upperSetEquivalence (Fin n → ℝ) (ModuleCat.{0} R)).functor.obj M)
      ((upperSetEquivalence (Fin n → ℝ) (ModuleCat.{0} R)).functor.obj N)) (a : Fin n → ℝ) :
    (equivUpperSet M N i).φ.app a =
      ((upperSetEquivalence (Fin n → ℝ) _).unitIso.app M).hom.app a ≫
        i.φ.hom.app (op (_root_.Alexandrov.principalOpen (X := upperSpace (Fin n → ℝ))
          (WithUpperSet.toUpperSet a))) ≫
        ((upperSetEquivalence (Fin n → ℝ) _).functor.obj N).presheaf.map
          (homOfLE (map_translate_principalOpen ε a).ge).op ≫
        ((upperSetEquivalence (Fin n → ℝ) _).unitIso.app N).inv.app
          (CoordinateShift.translation ε a) := by
  exact congrArg (((upperSetEquivalence (Fin n → ℝ) _).unitIso.app M).hom.app a ≫ ·)
    (Category.assoc _ _ _)

/-- At a grade `a`, the second arrow of `equivUpperSet i` is the sheaf arrow over `↑a`,
conjugated by the unit of `upperSetEquivalence` and the restriction along
`↑a + ε · 1 = ↑(a + ε · 1)`. -/
theorem equivUpperSet_apply_ψ_app (M N : PModule.{u,0,0} R (Fin n → ℝ))
    (i : SheafInterleaving ε ((upperSetEquivalence (Fin n → ℝ) (ModuleCat.{0} R)).functor.obj M)
      ((upperSetEquivalence (Fin n → ℝ) (ModuleCat.{0} R)).functor.obj N)) (a : Fin n → ℝ) :
    (equivUpperSet M N i).ψ.app a =
      ((upperSetEquivalence (Fin n → ℝ) _).unitIso.app N).hom.app a ≫
        i.ψ.hom.app (op (_root_.Alexandrov.principalOpen (X := upperSpace (Fin n → ℝ))
          (WithUpperSet.toUpperSet a))) ≫
        ((upperSetEquivalence (Fin n → ℝ) _).functor.obj M).presheaf.map
          (homOfLE (map_translate_principalOpen ε a).ge).op ≫
        ((upperSetEquivalence (Fin n → ℝ) _).unitIso.app M).inv.app
          (CoordinateShift.translation ε a) := by
  exact congrArg (((upperSetEquivalence (Fin n → ℝ) _).unitIso.app N).hom.app a ≫ ·)
    (Category.assoc _ _ _)

end SheafInterleaving

/-- For the sheaves attached to modules `M` and `N`, a sheaf witness exists exactly when a
coordinate witness for `M` and `N` exists. -/
theorem nonempty_sheafInterleaving_upperSet_iff (M N : PModule.{u,0,0} R (Fin n → ℝ)) :
    Nonempty (SheafInterleaving ε
        ((upperSetEquivalence (Fin n → ℝ) (ModuleCat.{0} R)).functor.obj M)
        ((upperSetEquivalence (Fin n → ℝ) (ModuleCat.{0} R)).functor.obj N)) ↔
      Nonempty (CoordinateInterleaving ε M N) :=
  (SheafInterleaving.equivUpperSet M N).nonempty_congr

/-- The sheaf interleaving distance is the coordinate interleaving distance of the principal
sections, since the two witness sets of radii agree. -/
theorem sheafInterleavingDistance_eq (F G : (upperSpace (Fin n → ℝ)).Sheaf (ModuleCat.{0} R)) :
    sheafInterleavingDistance F G =
      coordinateInterleavingDistance ((coordinateSections _).obj F)
        ((coordinateSections _).obj G) :=
  iInf_congr fun _ => iInf_congr_Prop nonempty_sheafInterleaving_iff fun _ => rfl

/-- On the sheaves attached to modules, the sheaf distance is the coordinate distance. -/
theorem sheafInterleavingDistance_upperSet (M N : PModule.{u,0,0} R (Fin n → ℝ)) :
    sheafInterleavingDistance
        ((upperSetEquivalence (Fin n → ℝ) (ModuleCat.{0} R)).functor.obj M)
        ((upperSetEquivalence (Fin n → ℝ) (ModuleCat.{0} R)).functor.obj N) =
      coordinateInterleavingDistance M N :=
  iInf_congr fun _ => iInf_congr_Prop (nonempty_sheafInterleaving_upperSet_iff M N) fun _ => rfl

theorem sheafInterleavingDistance_self (F : (upperSpace (Fin n → ℝ)).Sheaf (ModuleCat.{0} R)) :
    sheafInterleavingDistance F F = 0 := by
  rw [sheafInterleavingDistance_eq, coordinateInterleavingDistance_self]

theorem sheafInterleavingDistance_comm
    (F G : (upperSpace (Fin n → ℝ)).Sheaf (ModuleCat.{0} R)) :
    sheafInterleavingDistance F G = sheafInterleavingDistance G F := by
  rw [sheafInterleavingDistance_eq, sheafInterleavingDistance_eq,
    coordinateInterleavingDistance_comm]

/-- The triangle inequality, transported from `coordinateInterleavingDistance_triangle`. -/
theorem sheafInterleavingDistance_triangle
    (F G H : (upperSpace (Fin n → ℝ)).Sheaf (ModuleCat.{0} R)) :
    sheafInterleavingDistance F H ≤
      sheafInterleavingDistance F G + sheafInterleavingDistance G H := by
  rw [sheafInterleavingDistance_eq, sheafInterleavingDistance_eq, sheafInterleavingDistance_eq]
  exact coordinateInterleavingDistance_triangle _ _ _

end Witnesses

end

end TDA.Sheaf.AlexandrovCoordinateTranslation
