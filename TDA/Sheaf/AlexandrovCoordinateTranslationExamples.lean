import TDA.Sheaf.AlexandrovCoordinateTranslation
import TDA.Sheaf.AlexandrovTranslation
import TDA.Persistence.CoordinateRealBridge

/-!
# Coordinate Alexandrov translations: fixtures

These fixtures consume `TDA.Sheaf.AlexandrovCoordinateTranslation` through actual Mathlib types.

* **`n = 0`.** `Fin 0 → ℝ` is a single point (`zeroDim_unique`), every translation is the identity
  map (`translate_eq_id_zero`), so every shift fixes every open and the shift is naturally the
  identity (`zeroDimShiftIso`). An `ε`-witness then yields an isomorphism
  (`isoOfSheafInterleaving`), so for sheaves of modules a witness exists at some (equivalently
  every) parameter exactly when the sheaves are isomorphic (`zeroDim_nonempty_iff`). The sheaf
  distance is `0` if and only if the sheaves are isomorphic and `∞` otherwise
  (`zeroDim_distance_eq_zero_iff`, `zeroDim_distance_eq_top_iff`,
  `zeroDim_distance_eq_zero_or_top`),
  and likewise for `coordinateInterleavingDistance` of modules on `Fin 0 → ℝ`
  (`zeroDim_coordinateDistance_eq_zero_iff`, `zeroDim_coordinateDistance_eq_top_iff`).
* **`n = 1`.** The order isomorphism `Fin 1 → ℝ ≃o ℝ` gives the homeomorphism `lineHomeomorph`
  of upper spaces; `linePushforward` pushes sheaves forward along it (`lineMap`), and carries
  the coordinate shift to the real shift (`linePushforward_sheafShift`). The witness map
  `lineWitness` pushes both arrows of a witness forward. The square with
  `CoordinateRealBridge.interleavingEquiv` commutes (`line_square`): reading `lineWitness i`
  through `equivRealInterleaving` and `interleavingEquiv` gives the coordinate witness
  `equivCoordinateInterleaving i`, transported along the section identification
  `lineSectionsIso` (restriction along `↑a = lineMap⁻¹ ↑(a 0)`). Hence `lineWitness` is a
  bijection (`lineWitness_bijective`, `lineEquiv`) and the sheaf distances agree
  (`line_sheafDistance_eq`; `line_distance_eq` for the sheaves attached to `fromReal M`,
  `fromReal N` and to `M`, `N`).
* **`n = 2`.** The upper set `mixedUpset s = {x | s < x₀ ∧ s ≤ x₁}`, strict in the first
  coordinate and closed in the second, pulls back under `translate ε` to `mixedUpset (s + ε)`,
  by the geometric preimage formula `coe_map_translate`. Holding the second coordinate fixed at a
  value `c` with `ε ≤ c`, the point `(t, c)` lies in the translate exactly when `ε < t`, so for
  `0 < ε ≤ c` the point `(ε, c)` lies in `mixedUpset 0` but not in its translate
  (`mixedUpset_status_change`): the shift changes status in the first coordinate alone.
-/

set_option autoImplicit false

universe u

namespace TDA.Sheaf.AlexandrovCoordinateTranslationExamples

open CategoryTheory Limits Opposite TopologicalSpace Topology TDA.Persistence
open TDA.Sheaf.Alexandrov TDA.Sheaf.AlexandrovCoordinateTranslation
open scoped NNReal ENNReal

noncomputable section

/-! ## The point: `n = 0` -/

section ZeroDim

/-- The coordinate space `Fin 0 → ℝ` is a single point. -/
theorem zeroDim_unique : Nonempty (Unique (upperSpace (Fin 0 → ℝ))) :=
  ⟨inferInstanceAs (Unique (Fin 0 → ℝ))⟩

/-- On the point every translation is the identity map. -/
theorem translate_eq_id_zero (ε : ℝ≥0) :
    translate (n := 0) ε = 𝟙 (upperSpace (Fin 0 → ℝ)) := by
  ext x
  exact Subsingleton.elim (α := Fin 0 → ℝ) _ _

/-- On the point every translation fixes every open. -/
theorem map_translate_eq_self (ε : ℝ≥0) (U : Opens (upperSpace (Fin 0 → ℝ))) :
    (Opens.map (translate ε)).obj U = U := by
  rw [translate_eq_id_zero]
  rfl

variable {C : Type u} [Category.{0} C]

/-- On the point the shifted sheaf has the same sections as the sheaf. -/
theorem sheafShift_zeroDim (ε : ℝ≥0) (F : (upperSpace (Fin 0 → ℝ)).Sheaf C)
    (U : Opens (upperSpace (Fin 0 → ℝ))) :
    ((sheafShift C ε).obj F).presheaf.obj (op U) = F.presheaf.obj (op U) := by
  rw [sheafShift_obj_presheaf_obj, map_translate_eq_self]

variable (C) in
/-- On the point the shift is naturally the identity: the inverse is the transition, and the
forward map is the restriction along `U ⊆ U + ε · 1 = U`. -/
def zeroDimShiftIso (ε : ℝ≥0) : sheafShift (n := 0) C ε ≅ 𝟭 _ where
  hom :=
    { app := fun F => ObjectProperty.homMk
        { app := fun U => F.presheaf.map (homOfLE (map_translate_eq_self ε U.unop).ge).op
          naturality := fun U V f => by
            change F.presheaf.map _ ≫ F.presheaf.map _ = F.presheaf.map _ ≫ F.presheaf.map _
            rw [← F.presheaf.map_comp, ← F.presheaf.map_comp]
            exact presheaf_map_eq _ _ _ }
      naturality := fun F G φ => by
        apply CategoryTheory.Sheaf.hom_ext
        ext U
        exact (φ.hom.naturality _).symm }
  inv := sheafTransition C ε
  hom_inv_id := by
    apply NatTrans.ext
    funext F
    apply CategoryTheory.Sheaf.hom_ext
    ext U
    exact (F.presheaf.map_comp _ _).symm.trans ((presheaf_map_eq _ _ _).trans (F.presheaf.map_id _))
  inv_hom_id := by
    apply NatTrans.ext
    funext F
    apply CategoryTheory.Sheaf.hom_ext
    ext U
    exact (F.presheaf.map_comp _ _).symm.trans ((presheaf_map_eq _ _ _).trans (F.presheaf.map_id _))

theorem zeroDimShiftIso_inv (ε : ℝ≥0) : (zeroDimShiftIso C ε).inv = sheafTransition C ε :=
  rfl

/-- Two forward identifications compose to the addition isomorphism followed by the forward
identification at the sum. -/
theorem zeroDimShiftIso_hom_comp (ε : ℝ≥0) (F : (upperSpace (Fin 0 → ℝ)).Sheaf C) :
    (zeroDimShiftIso C ε).hom.app ((sheafShift C ε).obj F) ≫ (zeroDimShiftIso C ε).hom.app F =
      (sheafCompIso C ε ε).hom.app F ≫ (zeroDimShiftIso C (ε + ε)).hom.app F := by
  apply CategoryTheory.Sheaf.hom_ext
  ext U
  exact (F.presheaf.map_comp _ _).symm.trans
    ((presheaf_map_eq _ _ _).trans (F.presheaf.map_comp _ _))

/-- One composite of a point witness, read through `zeroDimShiftIso`, is the identity. -/
private theorem comp_eq_id {ε : ℝ≥0} {F G : (upperSpace (Fin 0 → ℝ)).Sheaf C}
    (f : F ⟶ (sheafShift C ε).obj G) (g : G ⟶ (sheafShift C ε).obj F)
    (h : f ≫ (sheafShift C ε).map g ≫ (sheafCompIso C ε ε).hom.app F =
      (sheafTransition C (ε + ε)).app F) :
    (f ≫ (zeroDimShiftIso C ε).hom.app G) ≫ (g ≫ (zeroDimShiftIso C ε).hom.app F) = 𝟙 F := by
  have nat := (zeroDimShiftIso C ε).hom.naturality g
  simp only [Functor.id_map] at nat
  calc (f ≫ (zeroDimShiftIso C ε).hom.app G) ≫ (g ≫ (zeroDimShiftIso C ε).hom.app F)
      = f ≫ (sheafShift C ε).map g ≫ (zeroDimShiftIso C ε).hom.app ((sheafShift C ε).obj F) ≫
          (zeroDimShiftIso C ε).hom.app F := by
        rw [Category.assoc, ← Category.assoc _ g, ← nat, Category.assoc]
    _ = (f ≫ (sheafShift C ε).map g ≫ (sheafCompIso C ε ε).hom.app F) ≫
          (zeroDimShiftIso C (ε + ε)).hom.app F := by
        rw [zeroDimShiftIso_hom_comp]
        simp only [Category.assoc]
    _ = 𝟙 F := by
        rw [h, ← zeroDimShiftIso_inv, Iso.inv_hom_id_app]
        rfl

/-- On the point, an `ε`-witness yields an isomorphism: each arrow followed by the identification
`S ε ≅ 𝟭`. -/
def isoOfSheafInterleaving {ε : ℝ≥0} {F G : (upperSpace (Fin 0 → ℝ)).Sheaf C}
    (i : SheafInterleaving ε F G) : F ≅ G where
  hom := i.φ ≫ (zeroDimShiftIso C ε).hom.app G
  inv := i.ψ ≫ (zeroDimShiftIso C ε).hom.app F
  hom_inv_id := comp_eq_id i.φ i.ψ i.φ_ψ
  inv_hom_id := comp_eq_id i.ψ i.φ i.ψ_φ

variable {R : Type u} [Ring R]
variable {F G : (upperSpace (Fin 0 → ℝ)).Sheaf (ModuleCat.{0} R)}

/-- On the point, a sheaf `ε`-witness exists exactly when the sheaves are isomorphic, for every
`ε`. -/
theorem zeroDim_nonempty_iff (ε : ℝ≥0) :
    Nonempty (SheafInterleaving ε F G) ↔ Nonempty (F ≅ G) :=
  ⟨fun ⟨i⟩ => ⟨isoOfSheafInterleaving i⟩, fun ⟨e⟩ => nonempty_sheafInterleaving_iff.mpr
    ⟨(CoordinateInterleaving.ofIso ((coordinateSections _).mapIso e)).mono zero_le⟩⟩

/-- On the point, the sheaf distance is zero exactly when the sheaves are isomorphic. -/
theorem zeroDim_distance_eq_zero_iff : sheafInterleavingDistance F G = 0 ↔ Nonempty (F ≅ G) := by
  rw [sheafInterleavingDistance_eq, coordinateInterleavingDistance_eq_zero_iff]
  constructor
  · intro h
    exact (zeroDim_nonempty_iff 1).mp (nonempty_sheafInterleaving_iff.mpr (h 1 one_pos))
  · intro h ε _
    exact nonempty_sheafInterleaving_iff.mp ((zeroDim_nonempty_iff ε).mpr h)

/-- On the point, the sheaf distance is infinite exactly when the sheaves are not isomorphic. -/
theorem zeroDim_distance_eq_top_iff : sheafInterleavingDistance F G = ⊤ ↔ IsEmpty (F ≅ G) := by
  rw [sheafInterleavingDistance_eq, coordinateInterleavingDistance_eq_top_iff]
  simp only [← not_nonempty_iff, ← nonempty_sheafInterleaving_iff, zeroDim_nonempty_iff]
  exact ⟨fun h => h 0, fun h _ => h⟩

/-- On the point, the sheaf distance takes only the values `0` and `∞`. -/
theorem zeroDim_distance_eq_zero_or_top :
    sheafInterleavingDistance F G = 0 ∨ sheafInterleavingDistance F G = ⊤ := by
  rcases isEmpty_or_nonempty (F ≅ G) with h | h
  · exact Or.inr (zeroDim_distance_eq_top_iff.mpr h)
  · exact Or.inl (zeroDim_distance_eq_zero_iff.mpr h)

/-- On the point, the coordinate distance of modules is zero exactly when they are isomorphic. -/
theorem zeroDim_coordinateDistance_eq_zero_iff (M N : PModule.{u,0,0} R (Fin 0 → ℝ)) :
    coordinateInterleavingDistance M N = 0 ↔ Nonempty (M ≅ N) := by
  rw [← sheafInterleavingDistance_upperSet, zeroDim_distance_eq_zero_iff]
  exact (upperSetEquivalence (Fin 0 → ℝ) (ModuleCat.{0} R)).fullyFaithfulFunctor.isoEquiv
    |>.symm.nonempty_congr

/-- On the point, the coordinate distance of modules is infinite exactly when they are not
isomorphic. -/
theorem zeroDim_coordinateDistance_eq_top_iff (M N : PModule.{u,0,0} R (Fin 0 → ℝ)) :
    coordinateInterleavingDistance M N = ⊤ ↔ IsEmpty (M ≅ N) := by
  rw [← sheafInterleavingDistance_upperSet, zeroDim_distance_eq_top_iff]
  exact (upperSetEquivalence (Fin 0 → ℝ) (ModuleCat.{0} R)).fullyFaithfulFunctor.isoEquiv
    |>.symm.isEmpty_congr

end ZeroDim

/-! ## The line: `n = 1` -/

section Line

/-- The order isomorphism `Fin 1 → ℝ ≃o ℝ` (evaluation at the sole coordinate) as a
homeomorphism of upper Alexandrov spaces. -/
def lineHomeomorph : WithUpperSet (Fin 1 → ℝ) ≃ₜ WithUpperSet ℝ where
  toFun := WithUpperSet.map CoordinateRealBridge.evaluate
  invFun := WithUpperSet.map CoordinateRealBridge.diagonal
  left_inv x := congrArg WithUpperSet.toUpperSet
    (CoordinateRealBridge.diagonal_evaluate (WithUpperSet.ofUpperSet x))
  right_inv _ := rfl
  continuous_toFun := (WithUpperSet.map CoordinateRealBridge.evaluate).continuous
  continuous_invFun := (WithUpperSet.map CoordinateRealBridge.diagonal).continuous

/-- The homeomorphism `lineHomeomorph` as a morphism of `TopCat`. -/
def lineMap : upperSpace (Fin 1 → ℝ) ⟶ upperSpace ℝ :=
  TopCat.ofHom (WithUpperSet.map CoordinateRealBridge.evaluate)

/-- `lineMap` is the homeomorphism `lineHomeomorph`. -/
theorem lineMap_eq_lineHomeomorph (x : WithUpperSet (Fin 1 → ℝ)) : lineMap x = lineHomeomorph x :=
  rfl

theorem lineMap_apply (x : WithUpperSet (Fin 1 → ℝ)) :
    lineMap x = WithUpperSet.toUpperSet (WithUpperSet.ofUpperSet (α := Fin 1 → ℝ) x 0) :=
  rfl

/-- The principal open `↑a` of `Fin 1 → ℝ` is the preimage of the principal open `↑(a 0)`. -/
theorem principalOpen_eq_map_lineMap (a : Fin 1 → ℝ) :
    _root_.Alexandrov.principalOpen (X := upperSpace (Fin 1 → ℝ)) (WithUpperSet.toUpperSet a) =
      (Opens.map lineMap).obj (_root_.Alexandrov.principalOpen (X := upperSpace ℝ)
        (WithUpperSet.toUpperSet (a 0))) := by
  ext x
  change (∀ i, a i ≤ WithUpperSet.ofUpperSet (α := Fin 1 → ℝ) x i) ↔
    a 0 ≤ WithUpperSet.ofUpperSet (α := Fin 1 → ℝ) x 0
  refine ⟨fun h => h 0, fun h i => ?_⟩
  fin_cases i
  exact h

variable (C : Type u) [Category.{0} C]

/-- The identification of sheaves along `Fin 1 → ℝ ≃ ℝ`: pushforward along `lineMap`. -/
def linePushforward : (upperSpace (Fin 1 → ℝ)).Sheaf C ⥤ (upperSpace ℝ).Sheaf C :=
  TopCat.Sheaf.pushforward C lineMap

variable {C}

/-- Pushforward along `lineMap` carries the coordinate shift to the real shift: both send `U`
to the preimage of `U` under `x ↦ x 0 - ε`. -/
theorem linePushforward_sheafShift (ε : ℝ≥0) (G : (upperSpace (Fin 1 → ℝ)).Sheaf C) :
    (linePushforward C).obj ((sheafShift C ε).obj G) =
      (AlexandrovTranslation.sheafShift C ε).obj ((linePushforward C).obj G) :=
  rfl

/-- The witness map along `lineMap`: push both arrows of a witness on `Fin 1 → ℝ` forward,
using `linePushforward_sheafShift`. -/
def lineWitness {ε : ℝ≥0} {F G : (upperSpace (Fin 1 → ℝ)).Sheaf C}
    (i : SheafInterleaving ε F G) :
    AlexandrovTranslation.SheafInterleaving ε ((linePushforward C).obj F)
      ((linePushforward C).obj G) where
  φ := (linePushforward C).map i.φ
  ψ := (linePushforward C).map i.ψ
  φ_ψ := by
    apply CategoryTheory.Sheaf.hom_ext
    ext U
    exact congrArg (fun f => f.hom.app (op ((Opens.map lineMap).obj U.unop))) i.φ_ψ
  ψ_φ := by
    apply CategoryTheory.Sheaf.hom_ext
    ext U
    exact congrArg (fun f => f.hom.app (op ((Opens.map lineMap).obj U.unop))) i.ψ_φ

@[simp]
theorem lineWitness_φ_hom_app {ε : ℝ≥0} {F G : (upperSpace (Fin 1 → ℝ)).Sheaf C}
    (i : SheafInterleaving ε F G) (U : Opens (upperSpace ℝ)) :
    (lineWitness i).φ.hom.app (op U) = i.φ.hom.app (op ((Opens.map lineMap).obj U)) :=
  rfl

@[simp]
theorem lineWitness_ψ_hom_app {ε : ℝ≥0} {F G : (upperSpace (Fin 1 → ℝ)).Sheaf C}
    (i : SheafInterleaving ε F G) (U : Opens (upperSpace ℝ)) :
    (lineWitness i).ψ.hom.app (op U) = i.ψ.hom.app (op ((Opens.map lineMap).obj U)) :=
  rfl

variable {R : Type u} [Ring R] {ε : ℝ≥0}

/-- The principal sections of `F` on `Fin 1 → ℝ` are the one-coordinate reading of the real
principal sections of its pushforward: at `a`, the restriction along
`↑a = lineMap⁻¹ ↑(a 0)`. -/
def lineSectionsIso (F : (upperSpace (Fin 1 → ℝ)).Sheaf (ModuleCat.{0} R)) :
    (coordinateSections _).obj F ≅
      CoordinateRealBridge.fromReal
        ((AlexandrovTranslation.realSections _).obj ((linePushforward _).obj F)) :=
  NatIso.ofComponents (fun a => restrictIso F.presheaf (principalOpen_eq_map_lineMap a))
    (fun {_ _} _ => presheaf_map_comp_map_eq F.presheaf _ _ _ _)

/-- Moving a restriction of the source across an arrow into a pushforward presheaf: the arrow at
`A` followed by a restriction equals a restriction of the source, the arrow at `B` and two
restrictions of the target, whenever both sides start and end at the same opens. -/
private theorem comp_restrict {X : TopCat.{0}} {P G : (Opens X)ᵒᵖ ⥤ ModuleCat.{0} R}
    {t : X ⟶ X} (φ : P ⟶ (Opens.map t).op ⋙ G) {A B : (Opens X)ᵒᵖ}
    {W₁ W₂ : (Opens X)ᵒᵖ} (f : A ⟶ B) (g : (Opens.map t).op.obj A ⟶ W₂)
    (r₂ : (Opens.map t).op.obj B ⟶ W₁) (r₃ : W₁ ⟶ W₂) :
    φ.app A ≫ G.map g = (P.map f ≫ φ.app B ≫ G.map r₂) ≫ G.map r₃ := by
  simp only [Category.assoc]
  rw [← Category.assoc (P.map f), φ.naturality, Functor.comp_map, Category.assoc,
    ← G.map_comp, ← G.map_comp]
  exact congrArg (φ.app A ≫ ·) (presheaf_map_eq G _ _)

/-- The square of witness maps commutes: reading a witness on `Fin 1 → ℝ` through
`equivCoordinateInterleaving` and the section identification `lineSectionsIso` agrees with
pushing it to the line by `lineWitness`, reading it through `equivRealInterleaving` and then
through `CoordinateRealBridge.interleavingEquiv`. -/
theorem line_square {F G : (upperSpace (Fin 1 → ℝ)).Sheaf (ModuleCat.{0} R)}
    (i : SheafInterleaving ε F G) :
    CoordinateRealBridge.interleavingEquiv ε _ _
        (AlexandrovTranslation.SheafInterleaving.equivRealInterleaving (lineWitness i)) =
      (SheafInterleaving.equivCoordinateInterleaving i).congr (lineSectionsIso F)
        (lineSectionsIso G) := by
  apply CoordinateInterleaving.ext
  · apply NatTrans.ext
    funext a
    exact comp_restrict (t := translate ε) i.φ.hom
      (homOfLE (principalOpen_eq_map_lineMap a).le).op _ _ _
  · apply NatTrans.ext
    funext a
    exact comp_restrict (t := translate ε) i.ψ.hom
      (homOfLE (principalOpen_eq_map_lineMap a).le).op _ _ _

/-- `lineWitness` is a bijection, by the square `line_square` of equivalences. -/
theorem lineWitness_bijective {F G : (upperSpace (Fin 1 → ℝ)).Sheaf (ModuleCat.{0} R)} :
    Function.Bijective (lineWitness (ε := ε) (F := F) (G := G)) := by
  constructor
  · intro i j h
    have h' := congrArg (fun x => CoordinateRealBridge.interleavingEquiv ε _ _
      (AlexandrovTranslation.SheafInterleaving.equivRealInterleaving x)) h
    simp only [line_square] at h'
    have h'' := congrArg (fun k => CoordinateInterleaving.congr k (lineSectionsIso F).symm
      (lineSectionsIso G).symm) h'
    simp only [CoordinateInterleaving.congr_congr_symm] at h''
    exact SheafInterleaving.equivCoordinateInterleaving.injective h''
  · intro j
    refine ⟨SheafInterleaving.equivCoordinateInterleaving.symm
      ((CoordinateRealBridge.interleavingEquiv ε _ _
        (AlexandrovTranslation.SheafInterleaving.equivRealInterleaving j)).congr
          (lineSectionsIso F).symm (lineSectionsIso G).symm), ?_⟩
    apply (AlexandrovTranslation.SheafInterleaving.equivRealInterleaving.trans
      (CoordinateRealBridge.interleavingEquiv ε _ _)).injective
    change CoordinateRealBridge.interleavingEquiv ε _ _
        (AlexandrovTranslation.SheafInterleaving.equivRealInterleaving (lineWitness _)) =
      CoordinateRealBridge.interleavingEquiv ε _ _
        (AlexandrovTranslation.SheafInterleaving.equivRealInterleaving j)
    rw [line_square, Equiv.apply_symm_apply, CoordinateInterleaving.congr_symm_congr]

/-- Sheaf witnesses on `Fin 1 → ℝ` are equivalent to sheaf witnesses on the line for the
pushforwards, by `lineWitness`. -/
def lineEquiv (F G : (upperSpace (Fin 1 → ℝ)).Sheaf (ModuleCat.{0} R)) :
    SheafInterleaving ε F G ≃
      AlexandrovTranslation.SheafInterleaving ε ((linePushforward _).obj F)
        ((linePushforward _).obj G) :=
  Equiv.ofBijective lineWitness lineWitness_bijective

theorem lineEquiv_apply (F G : (upperSpace (Fin 1 → ℝ)).Sheaf (ModuleCat.{0} R))
    (i : SheafInterleaving ε F G) : lineEquiv F G i = lineWitness i :=
  rfl

/-- The sheaf distance on `Fin 1 → ℝ` is the line sheaf distance of the pushforwards. -/
theorem line_sheafDistance_eq (F G : (upperSpace (Fin 1 → ℝ)).Sheaf (ModuleCat.{0} R)) :
    sheafInterleavingDistance F G =
      AlexandrovTranslation.sheafInterleavingDistance ((linePushforward _).obj F)
        ((linePushforward _).obj G) :=
  iInf_congr fun _ => iInf_congr_Prop (lineEquiv F G).nonempty_congr fun _ => rfl

/-- The sheaf distance on `Fin 1 → ℝ` of the sheaves attached to `fromReal M` and `fromReal N`
is the sheaf distance on the upper Alexandrov line of the sheaves attached to `M` and `N`. -/
theorem line_distance_eq (M N : PModule.{u,0,0} R ℝ) :
    sheafInterleavingDistance
        ((upperSetEquivalence (Fin 1 → ℝ) (ModuleCat.{0} R)).functor.obj
          (CoordinateRealBridge.fromReal M))
        ((upperSetEquivalence (Fin 1 → ℝ) (ModuleCat.{0} R)).functor.obj
          (CoordinateRealBridge.fromReal N)) =
      AlexandrovTranslation.sheafInterleavingDistance
        ((upperSetEquivalence ℝ (ModuleCat.{0} R)).functor.obj M)
        ((upperSetEquivalence ℝ (ModuleCat.{0} R)).functor.obj N) := by
  rw [sheafInterleavingDistance_upperSet, AlexandrovTranslation.sheafInterleavingDistance_upperSet,
    CoordinateRealBridge.distance_eq]

end Line

/-! ## The plane: `n = 2` -/

section Plane

/-- The upper set `{x | s < x₀ ∧ s ≤ x₁}` of the plane, strict in the first coordinate and closed
in the second. -/
def mixedUpset (s : ℝ) : Opens (upperSpace (Fin 2 → ℝ)) :=
  ⟨{x | s < WithUpperSet.ofUpperSet (α := Fin 2 → ℝ) x 0 ∧
      s ≤ WithUpperSet.ofUpperSet (α := Fin 2 → ℝ) x 1},
    Topology.IsUpperSet.isOpen_iff_isUpperSet.mpr fun _ _ hab ha =>
      ⟨lt_of_lt_of_le ha.1 (WithUpperSet.ofUpperSet_le_iff.mpr hab 0),
        le_trans ha.2 (WithUpperSet.ofUpperSet_le_iff.mpr hab 1)⟩⟩

/-- The point `(t, c)` of the plane. -/
abbrev planePoint (t c : ℝ) : WithUpperSet (Fin 2 → ℝ) :=
  WithUpperSet.toUpperSet ![t, c]

theorem planePoint_mem_mixedUpset_iff (s t c : ℝ) :
    planePoint t c ∈ mixedUpset s ↔ s < t ∧ s ≤ c :=
  Iff.rfl

/-- `mixedUpset s` pulls back under `translate ε` to `mixedUpset (s + ε)`, by the geometric
preimage formula. -/
theorem map_translate_mixedUpset (ε : ℝ≥0) (s : ℝ) :
    (Opens.map (translate ε)).obj (mixedUpset s) = mixedUpset (s + ε) := by
  apply Opens.ext
  rw [coe_map_translate]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change s + (ε : ℝ) < WithUpperSet.ofUpperSet (α := Fin 2 → ℝ) y 0 + (ε : ℝ) ∧
      s + (ε : ℝ) ≤ WithUpperSet.ofUpperSet (α := Fin 2 → ℝ) y 1 + (ε : ℝ)
    exact ⟨add_lt_add_left hy.1 _, add_le_add_left hy.2 _⟩
  · intro hx
    refine ⟨translate ε x, ?_, ?_⟩
    · change s < WithUpperSet.ofUpperSet (α := Fin 2 → ℝ) x 0 - (ε : ℝ) ∧
        s ≤ WithUpperSet.ofUpperSet (α := Fin 2 → ℝ) x 1 - (ε : ℝ)
      exact ⟨lt_sub_iff_add_lt.mpr hx.1, le_sub_iff_add_le.mpr hx.2⟩
    · change WithUpperSet.toUpperSet (CoordinateShift.translation ε
        (downTranslation ε (WithUpperSet.ofUpperSet (α := Fin 2 → ℝ) x))) = x
      rw [translation_downTranslation]
      rfl

/-- With the second coordinate held at `c ≥ s + ε`, the point `(t, c)` lies in the translate of
`mixedUpset s` exactly when `s + ε < t`. -/
theorem planePoint_mem_map_translate_iff {ε : ℝ≥0} {s c : ℝ} (hc : s + ε ≤ c) (t : ℝ) :
    planePoint t c ∈ (Opens.map (translate ε)).obj (mixedUpset s) ↔ s + ε < t := by
  rw [map_translate_mixedUpset, planePoint_mem_mixedUpset_iff]
  exact ⟨And.left, fun h => ⟨h, hc⟩⟩

/-- For `0 < ε ≤ c`, the point `(ε, c)` lies in `mixedUpset 0` but not in its translate: with the
second coordinate held at the permitted value `c`, the shift changes status in the first
coordinate. -/
theorem mixedUpset_status_change {ε : ℝ≥0} (hε : 0 < ε) {c : ℝ} (hc : (ε : ℝ) ≤ c) :
    planePoint ε c ∈ mixedUpset 0 ∧
      planePoint ε c ∉ (Opens.map (translate ε)).obj (mixedUpset 0) := by
  have hc' : (0 : ℝ) + ε ≤ c := by rwa [zero_add]
  refine ⟨(planePoint_mem_mixedUpset_iff 0 ε c).mpr ⟨NNReal.coe_pos.mpr hε,
    ε.coe_nonneg.trans hc⟩, ?_⟩
  rw [planePoint_mem_map_translate_iff hc', zero_add]
  exact lt_irrefl _

variable {C : Type u} [Category.{0} C]

/-- Sections of the shifted sheaf over `mixedUpset s` are sections over `mixedUpset (s + ε)`. -/
theorem sheafShift_mixedUpset (ε : ℝ≥0) (F : (upperSpace (Fin 2 → ℝ)).Sheaf C) (s : ℝ) :
    ((sheafShift C ε).obj F).presheaf.obj (op (mixedUpset s)) =
      F.presheaf.obj (op (mixedUpset (s + ε))) := by
  rw [sheafShift_obj_presheaf_obj, map_translate_mixedUpset]

end Plane

/-! ## The zero witness of the identity -/

/-- The transitions of a sheaf form a zero witness whose isomorphism is the identity. -/
example {R : Type} [Ring R] {n : ℕ} (F : (upperSpace (Fin n → ℝ)).Sheaf (ModuleCat.{0} R)) :
    SheafInterleaving.zeroEquivIso (SheafInterleaving.refl 0 F) = Iso.refl F := by
  apply Iso.ext
  rw [SheafInterleaving.zeroEquivIso_apply_hom]
  exact sheafTransition_zero F

end

end TDA.Sheaf.AlexandrovCoordinateTranslationExamples
