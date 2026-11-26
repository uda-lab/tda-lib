import TDA.Sheaf.Alexandrov
import TDA.Persistence.RealInterleavingDistance
import Mathlib.Topology.Sheaves.Functors
import Mathlib.Algebra.Category.ModuleCat.Limits

/-!
# Real Alexandrov translations and sheaf interleavings

Let `X := upperSpace ℝ = TopCat.of (Topology.WithUpperSet ℝ)`, the real line with its upper
Alexandrov topology (the open sets are the upper sets). For `ε : ℝ≥0`:

* `translate ε : X ⟶ X` is `x ↦ x - ε`, continuous by `WithUpperSet.map` of the monotone map
  `downTranslation ε`. Its preimage of an open `U` is `U + ε` (`coe_map_translate`); a principal
  open `↑t` goes to `↑(t + ε)` (`map_translate_principalOpen`).
* `sheafShift C ε := TopCat.Sheaf.pushforward C (translate ε)`, so that
  `(sheafShift C ε F)(U) = F(U + ε)` and the action on morphisms is Mathlib's pushforward map.
* `sheafShiftLE`, `sheafTransition`, `sheafZeroIso`, `sheafCompIso` and `sheafCongrIso` are the
  order maps for `ε ≤ δ`, the transition `F ⟶ sheafShift C ε F`, and the zero, addition and
  equal-parameter natural isomorphisms. Each component is a restriction of `F` along an
  inclusion or equality of preimage opens, and every coherence law is the equality of the
  corresponding restrictions.
* `realSections C : X.Sheaf C ⥤ (ℝ ⥤ C)` is the principal-sections functor `Γ` of
  `TDA.Sheaf.Alexandrov` read on `ℝ`, the inverse of `upperSetEquivalence ℝ C`.
* `shiftComparison R ε : sheafShift ε ⋙ Γ ≅ Γ ⋙ RealShift.shift ε` for `ModuleCat.{0} R`; it
  carries `sheafShiftLE`, `sheafTransition`, `sheafZeroIso` and `sheafCompIso` to
  `RealShift.shiftLE`, `RealShift.transition`, `RealShift.zeroIso` and `RealShift.compIso`.
* `SheafInterleaving ε F G` has arrows `F ⟶ sheafShift ε G`, `G ⟶ sheafShift ε F` and the two
  double-shift equations, in the orientation of `RealInterleaving`;
  `SheafInterleaving.equivRealInterleaving` identifies it with
  `RealInterleaving ε (Γ F) (Γ G)` for `ModuleCat.{0} R`, and
  `sheafInterleavingDistance_eq` identifies the extended-infimum sheaf distance with
  `realInterleavingDistance`.

The construction concerns the upper Alexandrov topology of `ℝ` only, not the Euclidean one.
-/

set_option autoImplicit false

universe u v

open CategoryTheory Limits Opposite TopologicalSpace Topology TopCat
open TDA.Persistence
open scoped NNReal ENNReal

namespace TDA.Sheaf.AlexandrovTranslation

open TDA.Sheaf.Alexandrov

noncomputable section

/-! ## Translations of the upper Alexandrov line -/

/-- The monotone translation `t ↦ t - ε` of `ℝ`. -/
def downTranslation (ε : ℝ≥0) : ℝ →o ℝ :=
  ⟨fun t => t - (ε : ℝ), fun _ _ h => sub_le_sub_right h _⟩

@[simp]
theorem downTranslation_apply (ε : ℝ≥0) (t : ℝ) : downTranslation ε t = t - (ε : ℝ) :=
  rfl

/-- The continuous map `x ↦ x - ε` of the upper Alexandrov line, `WithUpperSet.map` of the
monotone translation `downTranslation ε`. -/
def translate (ε : ℝ≥0) : upperSpace ℝ ⟶ upperSpace ℝ :=
  TopCat.ofHom (WithUpperSet.map (downTranslation ε))

@[simp]
theorem translate_apply (ε : ℝ≥0) (x : WithUpperSet ℝ) :
    translate ε x = WithUpperSet.toUpperSet (WithUpperSet.ofUpperSet (α := ℝ) x - (ε : ℝ)) :=
  rfl

/-- Every open set of the upper Alexandrov line is an upper set. -/
theorem isUpperSet_opens (U : Opens (upperSpace ℝ)) :
    IsUpperSet (U : Set (WithUpperSet ℝ)) :=
  Topology.IsUpperSet.isOpen_iff_isUpperSet.mp U.isOpen

/-- Membership in the preimage of `U` under `x ↦ x - ε`. -/
theorem mem_map_translate (ε : ℝ≥0) (U : Opens (upperSpace ℝ)) (x : WithUpperSet ℝ) :
    x ∈ (Opens.map (translate ε)).obj U ↔
      WithUpperSet.toUpperSet (WithUpperSet.ofUpperSet (α := ℝ) x - (ε : ℝ)) ∈ U :=
  Iff.rfl

/-- The preimage of an open `U` under `x ↦ x - ε` is the translate `U + ε`, the image of `U`
under `t ↦ t + ε`. -/
theorem coe_map_translate (ε : ℝ≥0) (U : Opens (upperSpace ℝ)) :
    ((Opens.map (translate ε)).obj U : Set (WithUpperSet ℝ)) =
      WithUpperSet.map (RealShift.translation ε) '' (U : Set (WithUpperSet ℝ)) := by
  ext x
  constructor
  · intro hx
    refine ⟨_, hx, ?_⟩
    change WithUpperSet.toUpperSet (WithUpperSet.ofUpperSet (α := ℝ) x - (ε : ℝ) + (ε : ℝ)) = x
    rw [sub_add_cancel]
    rfl
  · rintro ⟨y, hy, rfl⟩
    change WithUpperSet.toUpperSet (WithUpperSet.ofUpperSet (α := ℝ) y + (ε : ℝ) - (ε : ℝ)) ∈ U
    rw [add_sub_cancel_right]
    exact hy

/-- The principal open `↑t` pulls back to `↑(t + ε)`. -/
theorem map_translate_principalOpen (ε : ℝ≥0) (t : ℝ) :
    (Opens.map (translate ε)).obj
        (_root_.Alexandrov.principalOpen (X := upperSpace ℝ) (WithUpperSet.toUpperSet t)) =
      _root_.Alexandrov.principalOpen (X := upperSpace ℝ)
        (WithUpperSet.toUpperSet (t + (ε : ℝ))) := by
  ext x
  change t ≤ WithUpperSet.ofUpperSet (α := ℝ) x - (ε : ℝ) ↔
    t + (ε : ℝ) ≤ WithUpperSet.ofUpperSet (α := ℝ) x
  exact le_sub_iff_add_le

/-- For `ε ≤ δ`, the translate `U + δ` is contained in `U + ε`. -/
theorem map_translate_antitone {ε δ : ℝ≥0} (h : ε ≤ δ) (U : Opens (upperSpace ℝ)) :
    (Opens.map (translate δ)).obj U ≤ (Opens.map (translate ε)).obj U := by
  intro x hx
  exact isUpperSet_opens U
    (show WithUpperSet.ofUpperSet (α := ℝ) x - (δ : ℝ) ≤
        WithUpperSet.ofUpperSet (α := ℝ) x - (ε : ℝ) from
      sub_le_sub_left (NNReal.coe_le_coe.mpr h) _) hx

/-- The translate `U + ε` is contained in `U`. -/
theorem map_translate_le (ε : ℝ≥0) (U : Opens (upperSpace ℝ)) :
    (Opens.map (translate ε)).obj U ≤ U := by
  intro x hx
  exact isUpperSet_opens U
    (show WithUpperSet.ofUpperSet (α := ℝ) x - (ε : ℝ) ≤ WithUpperSet.ofUpperSet (α := ℝ) x from
      sub_le_self _ ε.coe_nonneg) hx

/-- Translation by zero fixes every open. -/
theorem map_translate_zero (U : Opens (upperSpace ℝ)) :
    (Opens.map (translate 0)).obj U = U := by
  ext x
  change WithUpperSet.toUpperSet (WithUpperSet.ofUpperSet (α := ℝ) x - ((0 : ℝ≥0) : ℝ)) ∈ U ↔ x ∈ U
  rw [NNReal.coe_zero, sub_zero]
  exact Iff.rfl

/-- Translating by `ε` and then by `δ` is translating by `ε + δ`: `(U + ε) + δ = U + (ε + δ)`. -/
theorem map_translate_comp (ε δ : ℝ≥0) (U : Opens (upperSpace ℝ)) :
    (Opens.map (translate δ)).obj ((Opens.map (translate ε)).obj U) =
      (Opens.map (translate (ε + δ))).obj U := by
  ext x
  change WithUpperSet.toUpperSet (WithUpperSet.ofUpperSet (α := ℝ) x - (δ : ℝ) - (ε : ℝ)) ∈ U ↔
    WithUpperSet.toUpperSet (WithUpperSet.ofUpperSet (α := ℝ) x - ((ε + δ : ℝ≥0) : ℝ)) ∈ U
  rw [NNReal.coe_add, sub_sub, add_comm (δ : ℝ)]

/-! ## Restrictions along inclusions of opens -/

section Restriction

variable {C : Type u} [Category.{v} C]

/-- Any two restrictions of a presheaf between the same opens agree. -/
private theorem presheaf_map_eq (P : (Opens (upperSpace ℝ))ᵒᵖ ⥤ C)
    {U V : (Opens (upperSpace ℝ))ᵒᵖ}
    (f g : U ⟶ V) : P.map f = P.map g :=
  congrArg P.map (Quiver.Hom.unop_inj (Subsingleton.elim _ _))

/-- A composite of two restrictions is the restriction between the outer opens. -/
private theorem presheaf_map_comp_map (P : (Opens (upperSpace ℝ))ᵒᵖ ⥤ C)
    {U V W : (Opens (upperSpace ℝ))ᵒᵖ} (f : U ⟶ V) (g : V ⟶ W) (h : U ⟶ W) :
    P.map f ≫ P.map g = P.map h :=
  (P.map_comp f g).symm.trans (presheaf_map_eq P _ _)

/-- Two composites of two restrictions between the same opens agree. -/
private theorem presheaf_map_comp_map_eq (P : (Opens (upperSpace ℝ))ᵒᵖ ⥤ C)
    {U V V' W : (Opens (upperSpace ℝ))ᵒᵖ} (f : U ⟶ V) (g : V ⟶ W) (f' : U ⟶ V')
    (g' : V' ⟶ W) : P.map f ≫ P.map g = P.map f' ≫ P.map g' :=
  (presheaf_map_comp_map P f g (f' ≫ g')).trans (P.map_comp f' g')

/-- A composite of two restrictions agrees with a composite of three between the same opens. -/
private theorem presheaf_map_comp_map_eq_comp (P : (Opens (upperSpace ℝ))ᵒᵖ ⥤ C)
    {U V V' V'' W : (Opens (upperSpace ℝ))ᵒᵖ} (f : U ⟶ V) (g : V ⟶ W) (f' : U ⟶ V')
    (g' : V' ⟶ V'') (h' : V'' ⟶ W) : P.map f ≫ P.map g = P.map f' ≫ P.map g' ≫ P.map h' := by
  rw [presheaf_map_comp_map P f g (f' ≫ g' ≫ h'), P.map_comp, P.map_comp]

/-- The restriction of a presheaf along an equality of opens, as an isomorphism. -/
@[simps]
def restrictIso (P : (Opens (upperSpace ℝ))ᵒᵖ ⥤ C) {U V : Opens (upperSpace ℝ)} (h : U = V) :
    P.obj (op U) ≅ P.obj (op V) where
  hom := P.map (homOfLE h.ge).op
  inv := P.map (homOfLE h.le).op
  hom_inv_id := by rw [← P.map_comp, ← P.map_id]; exact presheaf_map_eq P _ _
  inv_hom_id := by rw [← P.map_comp, ← P.map_id]; exact presheaf_map_eq P _ _

end Restriction

/-! ## The sheaf shift -/

section Shift

variable (C : Type u) [Category.{v} C]

/-- The sheaf shift `S ε`: pushforward along `x ↦ x - ε`. Its value on an open `U` is the
value of `F` on `U + ε`. -/
def sheafShift (ε : ℝ≥0) : (upperSpace ℝ).Sheaf C ⥤ (upperSpace ℝ).Sheaf C :=
  TopCat.Sheaf.pushforward C (translate ε)

variable {C}

/-- The shifted sheaf has the pushforward presheaf. -/
theorem sheafShift_obj_presheaf (ε : ℝ≥0) (F : (upperSpace ℝ).Sheaf C) :
    ((sheafShift C ε).obj F).presheaf = (Opens.map (translate ε)).op ⋙ F.presheaf :=
  rfl

/-- `(S ε F)(U) = F(U + ε)`, with `U + ε` the preimage of `U` under `x ↦ x - ε`. -/
theorem sheafShift_obj_presheaf_obj (ε : ℝ≥0) (F : (upperSpace ℝ).Sheaf C)
    (U : Opens (upperSpace ℝ)) :
    ((sheafShift C ε).obj F).presheaf.obj (op U) =
      F.presheaf.obj (op ((Opens.map (translate ε)).obj U)) :=
  rfl

/-- On principal opens, `(S ε F)(↑t) = F(↑(t + ε))`. -/
theorem sheafShift_obj_presheaf_obj_principalOpen (ε : ℝ≥0) (F : (upperSpace ℝ).Sheaf C)
    (t : ℝ) :
    ((sheafShift C ε).obj F).presheaf.obj
        (op (_root_.Alexandrov.principalOpen (X := upperSpace ℝ) (WithUpperSet.toUpperSet t))) =
      F.presheaf.obj (op (_root_.Alexandrov.principalOpen (X := upperSpace ℝ)
        (WithUpperSet.toUpperSet (t + (ε : ℝ))))) := by
  rw [sheafShift_obj_presheaf_obj, map_translate_principalOpen]

/-- The restriction maps of the shifted sheaf are restrictions of `F` between translates. -/
theorem sheafShift_obj_presheaf_map (ε : ℝ≥0) (F : (upperSpace ℝ).Sheaf C)
    {U V : (Opens (upperSpace ℝ))ᵒᵖ} (f : U ⟶ V) :
    ((sheafShift C ε).obj F).presheaf.map f =
      F.presheaf.map ((Opens.map (translate ε)).op.map f) :=
  rfl

/-- The shift acts on morphisms by Mathlib's pushforward map: the component on `U` is the
component on `U + ε`. -/
@[simp]
theorem sheafShift_map_hom_app (ε : ℝ≥0) {F G : (upperSpace ℝ).Sheaf C} (φ : F ⟶ G)
    (U : Opens (upperSpace ℝ)) :
    ((sheafShift C ε).map φ).hom.app (op U) =
      φ.hom.app (op ((Opens.map (translate ε)).obj U)) :=
  rfl

/-- The shift of a morphism is `TopCat.Sheaf.pushforward_map`. -/
theorem sheafShift_map_hom (ε : ℝ≥0) {F G : (upperSpace ℝ).Sheaf C} (φ : F ⟶ G) :
    ((sheafShift C ε).map φ).hom = (TopCat.Presheaf.pushforward C (translate ε)).map φ.hom :=
  TopCat.Sheaf.pushforward_map (translate ε) φ

variable (C)

/-- The order map `S ε ⟶ S δ` for `ε ≤ δ`: restriction along `U + δ ⊆ U + ε`. -/
def sheafShiftLE {ε δ : ℝ≥0} (h : ε ≤ δ) : sheafShift C ε ⟶ sheafShift C δ where
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

/-- The transition `F ⟶ S ε F`: restriction along `U + ε ⊆ U`. -/
def sheafTransition (ε : ℝ≥0) : 𝟭 ((upperSpace ℝ).Sheaf C) ⟶ sheafShift C ε where
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

/-- The zero natural isomorphism `S 0 ≅ 𝟭`, by the equality `U + 0 = U`. -/
def sheafZeroIso : sheafShift C 0 ≅ 𝟭 ((upperSpace ℝ).Sheaf C) :=
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
`S ε (S δ F) ≅ S (ε + δ) F`, by the equality `(U + ε) + δ = U + (ε + δ)`. -/
def sheafCompIso (ε δ : ℝ≥0) : sheafShift C δ ⋙ sheafShift C ε ≅ sheafShift C (ε + δ) :=
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

/-- Equal parameters give the natural isomorphism `S ε ≅ S δ` along `U + ε = U + δ`. -/
def sheafCongrIso {ε δ : ℝ≥0} (h : ε = δ) : sheafShift C ε ≅ sheafShift C δ :=
  NatIso.ofComponents
    (fun F => ObjectProperty.isoMk _ (NatIso.ofComponents
      (fun U => restrictIso F.presheaf
        (congrArg (fun a => (Opens.map (translate a)).obj U.unop) h))
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
theorem sheafShiftLE_app_hom_app {ε δ : ℝ≥0} (h : ε ≤ δ) (F : (upperSpace ℝ).Sheaf C)
    (U : Opens (upperSpace ℝ)) :
    ((sheafShiftLE C h).app F).hom.app (op U) =
      F.presheaf.map (homOfLE (map_translate_antitone h U)).op :=
  rfl

@[simp]
theorem sheafTransition_app_hom_app (ε : ℝ≥0) (F : (upperSpace ℝ).Sheaf C)
    (U : Opens (upperSpace ℝ)) :
    ((sheafTransition C ε).app F).hom.app (op U) =
      F.presheaf.map (homOfLE (map_translate_le ε U)).op :=
  rfl

@[simp]
theorem sheafZeroIso_hom_app_hom_app (F : (upperSpace ℝ).Sheaf C) (U : Opens (upperSpace ℝ)) :
    ((sheafZeroIso C).hom.app F).hom.app (op U) =
      F.presheaf.map (homOfLE (map_translate_zero U).ge).op :=
  rfl

@[simp]
theorem sheafZeroIso_inv_app_hom_app (F : (upperSpace ℝ).Sheaf C) (U : Opens (upperSpace ℝ)) :
    ((sheafZeroIso C).inv.app F).hom.app (op U) =
      F.presheaf.map (homOfLE (map_translate_zero U).le).op :=
  rfl

@[simp]
theorem sheafCompIso_hom_app_hom_app (ε δ : ℝ≥0) (F : (upperSpace ℝ).Sheaf C)
    (U : Opens (upperSpace ℝ)) :
    ((sheafCompIso C ε δ).hom.app F).hom.app (op U) =
      F.presheaf.map (homOfLE (map_translate_comp ε δ U).ge).op :=
  rfl

@[simp]
theorem sheafCompIso_inv_app_hom_app (ε δ : ℝ≥0) (F : (upperSpace ℝ).Sheaf C)
    (U : Opens (upperSpace ℝ)) :
    ((sheafCompIso C ε δ).inv.app F).hom.app (op U) =
      F.presheaf.map (homOfLE (map_translate_comp ε δ U).le).op :=
  rfl

@[simp]
theorem sheafCongrIso_hom_app_hom_app {ε δ : ℝ≥0} (h : ε = δ) (F : (upperSpace ℝ).Sheaf C)
    (U : Opens (upperSpace ℝ)) :
    ((sheafCongrIso C h).hom.app F).hom.app (op U) =
      F.presheaf.map
        (homOfLE (congrArg (fun a => (Opens.map (translate a)).obj U) h).ge).op :=
  rfl

/-! ### Coherence

Every law below is the equality of two composites of restrictions of `F` between the same
opens. -/

/-- The order map for `ε ≤ ε` is the identity. -/
theorem sheafShiftLE_refl (ε : ℝ≥0) : sheafShiftLE C (le_refl ε) = 𝟙 (sheafShift C ε) := by
  apply NatTrans.ext
  funext F
  apply CategoryTheory.Sheaf.hom_ext
  ext U
  exact (presheaf_map_eq _ _ _).trans (F.presheaf.map_id _)

/-- Order maps compose. -/
theorem sheafShiftLE_comp {ε δ γ : ℝ≥0} (h : ε ≤ δ) (h' : δ ≤ γ) :
    sheafShiftLE C h ≫ sheafShiftLE C h' = sheafShiftLE C (h.trans h') := by
  apply NatTrans.ext
  funext F
  apply CategoryTheory.Sheaf.hom_ext
  ext U
  exact (F.presheaf.map_comp _ _).symm.trans (presheaf_map_eq _ _ _)

/-- The transition followed by an order map is the transition of the larger parameter. -/
theorem sheafTransition_comp_shiftLE {ε δ : ℝ≥0} (h : ε ≤ δ) :
    sheafTransition C ε ≫ sheafShiftLE C h = sheafTransition C δ := by
  apply NatTrans.ext
  funext F
  apply CategoryTheory.Sheaf.hom_ext
  ext U
  exact (F.presheaf.map_comp _ _).symm.trans (presheaf_map_eq _ _ _)

/-- At zero, the transition followed by the zero isomorphism is the identity. -/
theorem sheafTransition_zero (F : (upperSpace ℝ).Sheaf C) :
    (sheafTransition C 0).app F ≫ (sheafZeroIso C).hom.app F = 𝟙 F := by
  apply CategoryTheory.Sheaf.hom_ext
  ext U
  exact (F.presheaf.map_comp _ _).symm.trans
    ((presheaf_map_eq _ _ _).trans (F.presheaf.map_id _))

/-- The zero transition is the inverse zero isomorphism. -/
theorem sheafTransition_zero_eq (F : (upperSpace ℝ).Sheaf C) :
    (sheafTransition C 0).app F = (sheafZeroIso C).inv.app F := by
  rw [← cancel_mono ((sheafZeroIso C).hom.app F), sheafTransition_zero, Iso.inv_hom_id_app]
  rfl

/-- Two transitions compose to the transition by the sum. -/
theorem sheafTransition_add (ε δ : ℝ≥0) (F : (upperSpace ℝ).Sheaf C) :
    (sheafTransition C ε).app F ≫ (sheafShift C ε).map ((sheafTransition C δ).app F) ≫
        (sheafCompIso C ε δ).hom.app F =
      (sheafTransition C (ε + δ)).app F := by
  apply CategoryTheory.Sheaf.hom_ext
  ext U
  change F.presheaf.map _ ≫ F.presheaf.map _ ≫ F.presheaf.map _ = F.presheaf.map _
  rw [← F.presheaf.map_comp, ← F.presheaf.map_comp]
  exact presheaf_map_eq _ _ _

/-- Transitions respect equal parameters. -/
theorem sheafTransition_congr {ε δ : ℝ≥0} (h : ε = δ) (F : (upperSpace ℝ).Sheaf C) :
    (sheafTransition C ε).app F ≫ (sheafCongrIso C h).hom.app F =
      (sheafTransition C δ).app F := by
  apply CategoryTheory.Sheaf.hom_ext
  ext U
  exact (F.presheaf.map_comp _ _).symm.trans (presheaf_map_eq _ _ _)

/-- Reflexive parameter transport is the identity. -/
theorem sheafCongrIso_refl (ε : ℝ≥0) : sheafCongrIso C (rfl : ε = ε) = Iso.refl _ := by
  apply Iso.ext
  apply NatTrans.ext
  funext F
  apply CategoryTheory.Sheaf.hom_ext
  ext U
  exact (presheaf_map_eq _ _ _).trans (F.presheaf.map_id _)

/-- Left unit law of the addition isomorphism. -/
theorem sheafCompIso_zero_left (ε : ℝ≥0) (F : (upperSpace ℝ).Sheaf C) :
    (sheafCompIso C 0 ε).hom.app F ≫ (sheafCongrIso C (zero_add ε)).hom.app F =
      (sheafZeroIso C).hom.app ((sheafShift C ε).obj F) := by
  apply CategoryTheory.Sheaf.hom_ext
  ext U
  exact (F.presheaf.map_comp _ _).symm.trans (presheaf_map_eq _ _ _)

/-- Right unit law of the addition isomorphism. -/
theorem sheafCompIso_zero_right (ε : ℝ≥0) (F : (upperSpace ℝ).Sheaf C) :
    (sheafCompIso C ε 0).hom.app F ≫ (sheafCongrIso C (add_zero ε)).hom.app F =
      (sheafShift C ε).map ((sheafZeroIso C).hom.app F) := by
  apply CategoryTheory.Sheaf.hom_ext
  ext U
  exact (F.presheaf.map_comp _ _).symm.trans (presheaf_map_eq _ _ _)

/-- Associativity of the addition isomorphism. -/
theorem sheafCompIso_assoc (ε δ γ : ℝ≥0) (F : (upperSpace ℝ).Sheaf C) :
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

/-! ## Principal sections on the real line -/

section Sections

variable (C : Type u) [Category.{0} C]

/-- The principal-sections functor `Γ` read on `ℝ`: `Γ(F)(t) = F(↑t)`, and for `s ≤ t` the
map `Γ(F)(s) ⟶ Γ(F)(t)` is the restriction along `↑t ⊆ ↑s`. -/
def realSections : (upperSpace ℝ).Sheaf C ⥤ (ℝ ⥤ C) :=
  principalSections (upperSpace ℝ) C ⋙
    (Functor.whiskeringLeft ℝ (upperSpace ℝ) C).obj
      (WithUpperSet.toUpperSetOrderIso (α := ℝ)).monotone.functor

variable {C}

@[simp]
theorem realSections_obj_obj (F : (upperSpace ℝ).Sheaf C) (t : ℝ) :
    ((realSections C).obj F).obj t =
      F.presheaf.obj
        (op (_root_.Alexandrov.principalOpen (X := upperSpace ℝ) (WithUpperSet.toUpperSet t))) :=
  rfl

@[simp]
theorem realSections_obj_map (F : (upperSpace ℝ).Sheaf C) {s t : ℝ} (f : s ⟶ t) :
    ((realSections C).obj F).map f =
      F.presheaf.map (homOfLE (_root_.Alexandrov.principalOpen_le (X := upperSpace ℝ)
        (x := WithUpperSet.toUpperSet s) (y := WithUpperSet.toUpperSet t) (leOfHom f))).op :=
  rfl

@[simp]
theorem realSections_map_app {F G : (upperSpace ℝ).Sheaf C} (φ : F ⟶ G) (t : ℝ) :
    ((realSections C).map φ).app t =
      φ.hom.app
        (op (_root_.Alexandrov.principalOpen (X := upperSpace ℝ) (WithUpperSet.toUpperSet t))) :=
  rfl

variable [HasLimits C]

/-- `Γ` is the inverse functor of `upperSetEquivalence ℝ C`. -/
theorem realSections_eq : realSections C = (upperSetEquivalence ℝ C).inverse :=
  rfl

/-- `Γ` is fully faithful on actual sheaves, as the inverse of `upperSetEquivalence ℝ C`. -/
def realSectionsFullyFaithful : (realSections C).FullyFaithful :=
  (upperSetEquivalence ℝ C).fullyFaithfulInverse

instance realSections_full : (realSections C).Full :=
  realSectionsFullyFaithful.full

instance realSections_faithful : (realSections C).Faithful :=
  realSectionsFullyFaithful.faithful

end Sections

/-! ## Comparison with the real shift -/

section Comparison

variable (R : Type u) [Ring R]

/-- The comparison `S ε ⋙ Γ ≅ Γ ⋙ RealShift.shift ε`: at `F` and `t`, the restriction along
the equality `↑t + ε = ↑(t + ε)` of opens. -/
def shiftComparison (ε : ℝ≥0) :
    sheafShift (ModuleCat.{0} R) ε ⋙ realSections (ModuleCat.{0} R) ≅
      realSections (ModuleCat.{0} R) ⋙ RealShift.shift ε :=
  NatIso.ofComponents
    (fun F => NatIso.ofComponents
      (fun t => restrictIso F.presheaf (map_translate_principalOpen ε t))
      (fun {s t} f => presheaf_map_comp_map_eq F.presheaf _ _ _ _))
    (fun {F G} φ => by
      apply NatTrans.ext
      funext t
      exact (φ.hom.naturality _).symm)

variable {R}

@[simp]
theorem shiftComparison_hom_app_app (ε : ℝ≥0) (F : (upperSpace ℝ).Sheaf (ModuleCat.{0} R))
    (t : ℝ) :
    ((shiftComparison R ε).hom.app F).app t =
      F.presheaf.map (homOfLE (map_translate_principalOpen ε t).ge).op :=
  rfl

@[simp]
theorem shiftComparison_inv_app_app (ε : ℝ≥0) (F : (upperSpace ℝ).Sheaf (ModuleCat.{0} R))
    (t : ℝ) :
    ((shiftComparison R ε).inv.app F).app t =
      F.presheaf.map (homOfLE (map_translate_principalOpen ε t).le).op :=
  rfl

/-- Naturality of the comparison in the sheaf. -/
@[reassoc]
theorem shiftComparison_hom_naturality (ε : ℝ≥0) {F G : (upperSpace ℝ).Sheaf (ModuleCat.{0} R)}
    (φ : F ⟶ G) :
    (realSections _).map ((sheafShift _ ε).map φ) ≫ (shiftComparison R ε).hom.app G =
      (shiftComparison R ε).hom.app F ≫ (RealShift.shift ε).map ((realSections _).map φ) :=
  (shiftComparison R ε).hom.naturality φ

/-- The comparison carries the sheaf order map to `RealShift.shiftLE`. -/
@[reassoc]
theorem shiftComparison_shiftLE {ε δ : ℝ≥0} (h : ε ≤ δ)
    (F : (upperSpace ℝ).Sheaf (ModuleCat.{0} R)) :
    (realSections _).map ((sheafShiftLE _ h).app F) ≫ (shiftComparison R δ).hom.app F =
      (shiftComparison R ε).hom.app F ≫ RealShift.shiftLE h ((realSections _).obj F) := by
  apply NatTrans.ext
  funext t
  exact presheaf_map_comp_map_eq F.presheaf _ _ _ _

/-- The comparison carries the sheaf transition to `RealShift.transition`. -/
@[reassoc]
theorem shiftComparison_transition (ε : ℝ≥0) (F : (upperSpace ℝ).Sheaf (ModuleCat.{0} R)) :
    (realSections _).map ((sheafTransition _ ε).app F) ≫ (shiftComparison R ε).hom.app F =
      RealShift.transition ε ((realSections _).obj F) := by
  apply NatTrans.ext
  funext t
  exact presheaf_map_comp_map F.presheaf _ _ _

/-- The comparison carries the sheaf zero isomorphism to `RealShift.zeroIso`. -/
theorem shiftComparison_zeroIso (F : (upperSpace ℝ).Sheaf (ModuleCat.{0} R)) :
    (realSections _).map ((sheafZeroIso _).hom.app F) =
      (shiftComparison R 0).hom.app F ≫ (RealShift.zeroIso ((realSections _).obj F)).hom := by
  apply NatTrans.ext
  funext t
  exact (presheaf_map_comp_map F.presheaf _ _ _).symm

/-- The comparison carries the sheaf addition isomorphism to `RealShift.compIso`. -/
@[reassoc]
theorem shiftComparison_compIso (ε δ : ℝ≥0) (F : (upperSpace ℝ).Sheaf (ModuleCat.{0} R)) :
    (realSections _).map ((sheafCompIso _ ε δ).hom.app F) ≫
        (shiftComparison R (ε + δ)).hom.app F =
      (shiftComparison R ε).hom.app ((sheafShift _ δ).obj F) ≫
        (RealShift.shift ε).map ((shiftComparison R δ).hom.app F) ≫
          (RealShift.compIso ε δ ((realSections _).obj F)).hom := by
  apply NatTrans.ext
  funext t
  exact presheaf_map_comp_map_eq_comp F.presheaf _ _ _ _ _

end Comparison

/-! ## Sheaf interleavings -/

section Interleaving

variable {C : Type u} [Category.{v} C]

/-- A sheaf `ε`-interleaving on the upper Alexandrov line, in the orientation of
`RealInterleaving`: arrows `F ⟶ S ε G` and `G ⟶ S ε F` whose two double-shift composites,
through the addition isomorphism, are the transitions by `ε + ε`. -/
structure SheafInterleaving (ε : ℝ≥0) (F G : (upperSpace ℝ).Sheaf C) where
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

variable {ε : ℝ≥0} {F G : (upperSpace ℝ).Sheaf C}

/-- Two sheaf witnesses agree when their two arrows agree. -/
@[ext]
theorem ext {i j : SheafInterleaving ε F G} (hφ : i.φ = j.φ) (hψ : i.ψ = j.ψ) : i = j := by
  cases i; cases j; cases hφ; cases hψ; rfl

/-- Interchange the two arrows. -/
def symm (i : SheafInterleaving ε F G) : SheafInterleaving ε G F :=
  ⟨i.ψ, i.φ, i.ψ_φ, i.φ_ψ⟩

/-- A sheaf is interleaved with itself by its transitions. -/
def refl (ε : ℝ≥0) (F : (upperSpace ℝ).Sheaf C) : SheafInterleaving ε F F :=
  ⟨(sheafTransition C ε).app F, (sheafTransition C ε).app F, sheafTransition_add ε ε F,
    sheafTransition_add ε ε F⟩

end SheafInterleaving

/-- The extended-infimum interleaving distance of sheaves on the upper Alexandrov line. -/
def sheafInterleavingDistance (F G : (upperSpace ℝ).Sheaf C) : ℝ≥0∞ :=
  ⨅ (ε : ℝ≥0) (_ : Nonempty (SheafInterleaving ε F G)), (ε : ℝ≥0∞)

end Interleaving

/-! ## Sheaf and module witnesses -/

section Witnesses

variable {R : Type u} [Ring R]
variable {ε : ℝ≥0} {F G : (upperSpace ℝ).Sheaf (ModuleCat.{0} R)}

/-- Under `Γ` and the comparison, the sheaf double-shift composite becomes the module one. -/
theorem realSections_map_doubleShift (f : F ⟶ (sheafShift _ ε).obj G)
    (g : G ⟶ (sheafShift _ ε).obj F) :
    (realSections _).map (f ≫ (sheafShift _ ε).map g ≫ (sheafCompIso _ ε ε).hom.app F) ≫
        (shiftComparison R (ε + ε)).hom.app F =
      ((realSections _).map f ≫ (shiftComparison R ε).hom.app G) ≫
        (RealShift.shift ε).map ((realSections _).map g ≫ (shiftComparison R ε).hom.app F) ≫
          (RealShift.compIso ε ε ((realSections _).obj F)).hom := by
  simp only [Functor.map_comp, Category.assoc]
  rw [shiftComparison_compIso, shiftComparison_hom_naturality_assoc]

/-- A pair of sheaf arrows satisfies the sheaf double-shift equation exactly when its image
under `Γ` and the comparison satisfies the module equation. -/
theorem doubleShift_iff (f : F ⟶ (sheafShift _ ε).obj G) (g : G ⟶ (sheafShift _ ε).obj F) :
    f ≫ (sheafShift _ ε).map g ≫ (sheafCompIso _ ε ε).hom.app F =
        (sheafTransition _ (ε + ε)).app F ↔
      ((realSections _).map f ≫ (shiftComparison R ε).hom.app G) ≫
          (RealShift.shift ε).map ((realSections _).map g ≫ (shiftComparison R ε).hom.app F) ≫
            (RealShift.compIso ε ε ((realSections _).obj F)).hom =
        RealShift.transition (ε + ε) ((realSections _).obj F) := by
  rw [← realSections_map_doubleShift, ← shiftComparison_transition]
  constructor
  · intro h
    rw [h]
  · intro h
    exact realSectionsFullyFaithful.map_injective ((cancel_mono _).mp h)

/-- `Γ` of the lift of a module arrow, followed by the comparison, is the module arrow. -/
theorem map_preimage_comp_shiftComparison
    (a : (realSections _).obj F ⟶ (RealShift.shift ε).obj ((realSections _).obj G)) :
    (realSections _).map (realSectionsFullyFaithful.preimage
        (a ≫ (shiftComparison R ε).inv.app G)) ≫ (shiftComparison R ε).hom.app G = a := by
  rw [Functor.FullyFaithful.map_preimage, Category.assoc, Iso.inv_hom_id_app]
  exact Category.comp_id _

namespace SheafInterleaving

/-- The module witness of a sheaf witness: apply `Γ`, then the comparison. -/
def toRealInterleaving (i : SheafInterleaving ε F G) :
    RealInterleaving ε ((realSections _).obj F) ((realSections _).obj G) where
  φ := (realSections _).map i.φ ≫ (shiftComparison R ε).hom.app G
  ψ := (realSections _).map i.ψ ≫ (shiftComparison R ε).hom.app F
  φ_ψ := (doubleShift_iff i.φ i.ψ).mp i.φ_ψ
  ψ_φ := (doubleShift_iff i.ψ i.φ).mp i.ψ_φ

/-- The sheaf witness of a module witness: compose with the inverse comparison and lift along
the fully faithful `Γ`. -/
def ofRealInterleaving (j : RealInterleaving ε ((realSections _).obj F) ((realSections _).obj G)) :
    SheafInterleaving ε F G where
  φ := realSectionsFullyFaithful.preimage (j.φ ≫ (shiftComparison R ε).inv.app G)
  ψ := realSectionsFullyFaithful.preimage (j.ψ ≫ (shiftComparison R ε).inv.app F)
  φ_ψ := (doubleShift_iff _ _).mpr (by
    rw [map_preimage_comp_shiftComparison, map_preimage_comp_shiftComparison]
    exact j.φ_ψ)
  ψ_φ := (doubleShift_iff _ _).mpr (by
    rw [map_preimage_comp_shiftComparison, map_preimage_comp_shiftComparison]
    exact j.ψ_φ)

/-- Sheaf `ε`-interleavings of `F` and `G` are equivalent to real `ε`-interleavings of their
principal sections. -/
def equivRealInterleaving :
    SheafInterleaving ε F G ≃ RealInterleaving ε ((realSections _).obj F) ((realSections _).obj G)
    where
  toFun := toRealInterleaving
  invFun := ofRealInterleaving
  left_inv i := by
    apply SheafInterleaving.ext
    · apply realSectionsFullyFaithful.map_injective
      change (realSections _).map (realSectionsFullyFaithful.preimage
        (((realSections _).map i.φ ≫ (shiftComparison R ε).hom.app G) ≫
          (shiftComparison R ε).inv.app G)) = _
      rw [Functor.FullyFaithful.map_preimage, Category.assoc, Iso.hom_inv_id_app]
      exact Category.comp_id _
    · apply realSectionsFullyFaithful.map_injective
      change (realSections _).map (realSectionsFullyFaithful.preimage
        (((realSections _).map i.ψ ≫ (shiftComparison R ε).hom.app F) ≫
          (shiftComparison R ε).inv.app F)) = _
      rw [Functor.FullyFaithful.map_preimage, Category.assoc, Iso.hom_inv_id_app]
      exact Category.comp_id _
  right_inv j := RealInterleaving.ext (map_preimage_comp_shiftComparison j.φ)
    (map_preimage_comp_shiftComparison j.ψ)

@[simp]
theorem equivRealInterleaving_apply_φ (i : SheafInterleaving ε F G) :
    (equivRealInterleaving i).φ = (realSections _).map i.φ ≫ (shiftComparison R ε).hom.app G :=
  rfl

@[simp]
theorem equivRealInterleaving_apply_ψ (i : SheafInterleaving ε F G) :
    (equivRealInterleaving i).ψ = (realSections _).map i.ψ ≫ (shiftComparison R ε).hom.app F :=
  rfl

/-- The first arrow of the inverse image, read through `Γ` and the comparison, is the first
module arrow. -/
theorem map_equivRealInterleaving_symm_φ
    (j : RealInterleaving ε ((realSections _).obj F) ((realSections _).obj G)) :
    (realSections _).map (equivRealInterleaving.symm j).φ ≫ (shiftComparison R ε).hom.app G =
      j.φ :=
  map_preimage_comp_shiftComparison j.φ

/-- The second arrow of the inverse image, read through `Γ` and the comparison, is the second
module arrow. -/
theorem map_equivRealInterleaving_symm_ψ
    (j : RealInterleaving ε ((realSections _).obj F) ((realSections _).obj G)) :
    (realSections _).map (equivRealInterleaving.symm j).ψ ≫ (shiftComparison R ε).hom.app F =
      j.ψ :=
  map_preimage_comp_shiftComparison j.ψ

/-- At `ε = 0`, sheaf witnesses are equivalent to actual isomorphisms of sheaves. -/
def zeroEquivIso : SheafInterleaving 0 F G ≃ (F ≅ G) :=
  equivRealInterleaving.trans
    (RealInterleaving.zeroEquivIso.trans realSectionsFullyFaithful.isoEquiv.symm)

/-- The isomorphism of a zero witness is its first arrow followed by the zero isomorphism. -/
theorem zeroEquivIso_apply_hom (i : SheafInterleaving 0 F G) :
    (zeroEquivIso i).hom = i.φ ≫ (sheafZeroIso _).hom.app G := by
  apply realSectionsFullyFaithful.map_injective
  change (realSections _).map (realSectionsFullyFaithful.preimage
    (((realSections _).map i.φ ≫ (shiftComparison R 0).hom.app G) ≫
      (RealShift.zeroIso ((realSections _).obj G)).hom)) = _
  rw [Functor.FullyFaithful.map_preimage, Functor.map_comp, shiftComparison_zeroIso,
    Category.assoc]

/-- The inverse of the isomorphism of a zero witness is its second arrow followed by the zero
isomorphism. -/
theorem zeroEquivIso_apply_inv (i : SheafInterleaving 0 F G) :
    (zeroEquivIso i).inv = i.ψ ≫ (sheafZeroIso _).hom.app F := by
  apply realSectionsFullyFaithful.map_injective
  change (realSections _).map (realSectionsFullyFaithful.preimage
    (((realSections _).map i.ψ ≫ (shiftComparison R 0).hom.app F) ≫
      (RealShift.zeroIso ((realSections _).obj F)).hom)) = _
  rw [Functor.FullyFaithful.map_preimage, Functor.map_comp, shiftComparison_zeroIso,
    Category.assoc]

end SheafInterleaving

/-- A sheaf witness exists exactly when a module witness exists for the principal sections. -/
theorem nonempty_sheafInterleaving_iff :
    Nonempty (SheafInterleaving ε F G) ↔
      Nonempty (RealInterleaving ε ((realSections _).obj F) ((realSections _).obj G)) :=
  SheafInterleaving.equivRealInterleaving.nonempty_congr

/-- For the sheaves attached to modules `M` and `N`, a sheaf witness exists exactly when a
module witness for `M` and `N` exists. -/
theorem nonempty_sheafInterleaving_upperSet_iff (M N : PModule.{u,0,0} R ℝ) :
    Nonempty (SheafInterleaving ε ((upperSetEquivalence ℝ (ModuleCat.{0} R)).functor.obj M)
        ((upperSetEquivalence ℝ (ModuleCat.{0} R)).functor.obj N)) ↔
      Nonempty (RealInterleaving ε M N) := by
  rw [nonempty_sheafInterleaving_iff]
  constructor
  · rintro ⟨i⟩
    exact ⟨i.congr ((upperSetEquivalence ℝ _).unitIso.app M).symm
      ((upperSetEquivalence ℝ _).unitIso.app N).symm⟩
  · rintro ⟨i⟩
    exact ⟨i.congr ((upperSetEquivalence ℝ _).unitIso.app M)
      ((upperSetEquivalence ℝ _).unitIso.app N)⟩

/-- The sheaf interleaving distance is the real interleaving distance of the principal
sections, since the two witness sets of radii agree. -/
theorem sheafInterleavingDistance_eq (F G : (upperSpace ℝ).Sheaf (ModuleCat.{0} R)) :
    sheafInterleavingDistance F G =
      realInterleavingDistance ((realSections _).obj F) ((realSections _).obj G) :=
  iInf_congr fun _ => iInf_congr_Prop nonempty_sheafInterleaving_iff fun _ => rfl

/-- On the sheaves attached to modules, the sheaf distance is the module distance. -/
theorem sheafInterleavingDistance_upperSet (M N : PModule.{u,0,0} R ℝ) :
    sheafInterleavingDistance ((upperSetEquivalence ℝ (ModuleCat.{0} R)).functor.obj M)
        ((upperSetEquivalence ℝ (ModuleCat.{0} R)).functor.obj N) =
      realInterleavingDistance M N :=
  iInf_congr fun _ => iInf_congr_Prop (nonempty_sheafInterleaving_upperSet_iff M N) fun _ => rfl

theorem sheafInterleavingDistance_self (F : (upperSpace ℝ).Sheaf (ModuleCat.{0} R)) :
    sheafInterleavingDistance F F = 0 := by
  rw [sheafInterleavingDistance_eq, realInterleavingDistance_self]

theorem sheafInterleavingDistance_comm (F G : (upperSpace ℝ).Sheaf (ModuleCat.{0} R)) :
    sheafInterleavingDistance F G = sheafInterleavingDistance G F := by
  rw [sheafInterleavingDistance_eq, sheafInterleavingDistance_eq, realInterleavingDistance_comm]

/-- The triangle inequality, transported from `realInterleavingDistance_triangle`. -/
theorem sheafInterleavingDistance_triangle (F G H : (upperSpace ℝ).Sheaf (ModuleCat.{0} R)) :
    sheafInterleavingDistance F H ≤
      sheafInterleavingDistance F G + sheafInterleavingDistance G H := by
  rw [sheafInterleavingDistance_eq, sheafInterleavingDistance_eq, sheafInterleavingDistance_eq]
  exact realInterleavingDistance_triangle _ _ _

end Witnesses

end

end TDA.Sheaf.AlexandrovTranslation
