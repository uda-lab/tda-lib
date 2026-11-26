import TDA.Sheaf.AlexandrovTranslation
import Mathlib.Topology.Order.LowerUpperTopology
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Sheaves.SheafCondition.PairwiseIntersections

/-!
# Real Alexandrov and upper ray sheaves at the distance level

`raySpace := TopCat.of (WithUpper ℝ)` is the real line with Mathlib's upper topology, whose
basic opens are the open rays `ray t = (t, ∞)` (`isBasis_ray`). Its open sets are exactly the
ordinary open upper sets of `ℝ` (`isOpen_ofUpper_preimage_iff`). The identity
`rayId : upperSpace ℝ ⟶ raySpace` from the upper Alexandrov line is continuous.

* `rayQ C : (ℝ ⥤ C) ⥤ raySpace.Sheaf C` is the Alexandrov sheaf `upperSetEquivalence ℝ C` of
  `TDA.Sheaf.Alexandrov`, pushed forward along `rayId`.
* `rayB C : raySpace.Sheaf C ⥤ (ℝ ⥤ C)` is `B(F)(t) = F((t, ∞))` with the restrictions of `F`.
* `rayProj M h : BQ(M)(t) ⟶ M(s)` for `t < s` is the limit projection of the Kan extension at
  `↑s ⊆ (t, ∞)`; `rayConeIsLimit` and `rayLimitIso` identify `BQ(M)(t)` with
  `lim_{s > t} M(s)` (`rayDiagram`), with projection equations `rayLimitIso_hom_π`,
  `rayProj_comp_map`, `map_rayProj`, `map_app_rayProj` and the extensionality `rayProj_ext`.
* `rayUnit C : 𝟭 ⟶ rayQ C ⋙ rayB C` is the unit `η`, the lift of the maps `M(t ≤ s)`
  (`rayUnit_app_app_rayProj`).
* `rayCounitIso C : rayB C ⋙ rayQ C ≅ 𝟭` is `QB ≅ 𝟭`: by the sheaf condition for the cover of an
  open `V` by the rays at its points, whose pairwise intersections are the rays at the larger
  point (`ray_inf`); the empty open has the empty cover (`iSup_ray`). Hence `rayB` is faithful.
* `rayShift C ε` is pushforward along `rayTranslate ε : x ↦ x - ε`, with `rayTransition` and
  `rayCompIso`; pushforward along `rayId` carries `sheafShift`, `sheafTransition` and
  `sheafCompIso` of `TDA.Sheaf.AlexandrovTranslation` to them at the same radius, and
  `rayShiftComparison R ε : rayShift ε ⋙ rayB ≅ rayB ⋙ RealShift.shift ε` carries them to
  `RealShift.transition` and `RealShift.compIso`.
* `RaySheafInterleaving` has the orientation of `RealInterleaving`;
  `RaySheafInterleaving.toRealInterleaving` (for `B`) and
  `RaySheafInterleaving.ofRealInterleaving` (for `Q`) transport witnesses at the same radius.
* For `ε > 0`, `unitInterleaving M hε` is an actual `ε`-interleaving of `M` and `BQ(M)`, so
  `realInterleavingDistance_rayB_rayQ`. Consequently `raySheafInterleavingDistance_rayQ` and
  `realInterleavingDistance_rayB` equate the extended distances of `M, N` and `Q M, Q N`, and of
  `F, G` and `B F, B G`.
* `isZero_rayQ_iff`: `Q M` is zero exactly when every map `M(s ≤ t)` with `s < t` is zero.

Distance zero does not give a zero-interleaving: `TDA.Sheaf.RaySheafExamples` exhibits a
singleton module with `Q M = 0` and `M ≠ 0`. The interleavings use `C = ModuleCat.{0} R`.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits Opposite TopologicalSpace Topology TopCat
open TDA.Persistence
open scoped NNReal ENNReal

namespace TDA.Sheaf.RaySheaf

open TDA.Sheaf.Alexandrov TDA.Sheaf.AlexandrovTranslation

noncomputable section

/-! ## The ray topology -/

/-- The real line with the ray topology: Mathlib's upper topology on `WithUpper ℝ`, generated
by the open rays `(t, ∞)`. -/
abbrev raySpace : TopCat.{0} :=
  TopCat.of (WithUpper ℝ)

/-- The open sets of the ray topology are exactly the ordinary open upper sets of `ℝ`. -/
theorem isOpen_ofUpper_preimage_iff (S : Set ℝ) :
    IsOpen (WithUpper.ofUpper ⁻¹' S : Set (WithUpper ℝ)) ↔ IsUpperSet S ∧ IsOpen S := by
  constructor
  · intro h
    exact ⟨fun _ _ hab ha => IsUpper.isUpperSet_of_isOpen h hab ha,
      h.preimage WithUpper.continuous_toUpper⟩
  · rintro ⟨hup, hS⟩
    rw [isOpen_iff_forall_mem_open]
    intro x hx
    obtain ⟨l, hl, hsub⟩ := exists_Ioc_subset_of_mem_nhds (a := WithUpper.ofUpper x)
      (hS.mem_nhds hx) ⟨_, sub_one_lt _⟩
    refine ⟨WithUpper.ofUpper ⁻¹' Set.Ioi l, fun y hy => ?_, ?_, hl⟩
    · exact hup (min_le_left (WithUpper.ofUpper y) (WithUpper.ofUpper x))
        (hsub ⟨lt_min hy hl, min_le_right _ _⟩)
    · rw [← Set.compl_Iic]
      exact isClosed_Iic.isOpen_compl

/-- An open of the ray space read on `ℝ` is an ordinary open upper set. -/
theorem isUpperSet_isOpen_toUpper_preimage (V : Opens raySpace) :
    IsUpperSet (WithUpper.toUpper ⁻¹' (V : Set (WithUpper ℝ))) ∧
      IsOpen (WithUpper.toUpper ⁻¹' (V : Set (WithUpper ℝ))) :=
  (isOpen_ofUpper_preimage_iff _).1 V.isOpen

/-- The open ray `(t, ∞)` of the ray space. -/
def ray (t : ℝ) : Opens raySpace :=
  ⟨WithUpper.ofUpper ⁻¹' Set.Ioi t,
    (isOpen_ofUpper_preimage_iff _).2 ⟨isUpperSet_Ioi t, isOpen_Ioi⟩⟩

@[simp]
theorem mem_ray (t : ℝ) (x : WithUpper ℝ) : x ∈ ray t ↔ t < WithUpper.ofUpper x :=
  Iff.rfl

/-- Rays are antitone in their left endpoint. -/
theorem ray_antitone {s t : ℝ} (h : s ≤ t) : ray t ≤ ray s :=
  fun _ hx => lt_of_le_of_lt h hx

/-- Two rays meet in the ray at the larger endpoint. -/
theorem ray_inf (s t : ℝ) : ray s ⊓ ray t = ray (max s t) := by
  ext x
  change s < WithUpper.ofUpper (α := ℝ) x ∧ t < WithUpper.ofUpper (α := ℝ) x ↔
    max s t < WithUpper.ofUpper (α := ℝ) x
  rw [max_lt_iff]

/-- The ray at a point of an open is contained in that open. -/
theorem ray_le {V : Opens raySpace} {p : ℝ} (hp : WithUpper.toUpper p ∈ V) : ray p ≤ V :=
  fun _ hx => (isUpperSet_isOpen_toUpper_preimage V).1 (le_of_lt hx) hp

/-- Each point of an open lies in the ray at some smaller point of that open. -/
theorem exists_ray_mem {V : Opens raySpace} {x : WithUpper ℝ} (hx : x ∈ V) :
    ∃ p : ℝ, WithUpper.toUpper p ∈ V ∧ x ∈ ray p := by
  obtain ⟨l, hl, hsub⟩ := exists_Ioc_subset_of_mem_nhds (a := WithUpper.ofUpper x)
    ((isUpperSet_isOpen_toUpper_preimage V).2.mem_nhds hx) ⟨_, sub_one_lt _⟩
  refine ⟨(l + WithUpper.ofUpper x) / 2,
    hsub (show (l + WithUpper.ofUpper x) / 2 ∈ Set.Ioc l (WithUpper.ofUpper x) from
      ⟨by linarith, by linarith⟩), ?_⟩
  change (l + WithUpper.ofUpper x) / 2 < WithUpper.ofUpper x
  linarith

/-- Every open is the union of the rays at its points; the empty open has the empty cover. -/
theorem iSup_ray (V : Opens raySpace) :
    ⨆ i : {p : ℝ // WithUpper.toUpper p ∈ V}, ray i.1 = V := by
  apply le_antisymm
  · exact iSup_le fun i => ray_le i.2
  · intro x hx
    obtain ⟨p, hp, hxp⟩ := exists_ray_mem hx
    exact Opens.mem_iSup.2 ⟨⟨p, hp⟩, hxp⟩

/-- The open rays form a basis of the ray topology. -/
theorem isBasis_ray : Opens.IsBasis (Set.range ray) := by
  rw [Opens.isBasis_iff_nbhd]
  intro V x hx
  obtain ⟨p, hp, hxp⟩ := exists_ray_mem hx
  exact ⟨ray p, ⟨p, rfl⟩, hxp, ray_le hp⟩

/-- The continuous identity from the upper Alexandrov line to the ray space. -/
def rayId : upperSpace ℝ ⟶ raySpace :=
  TopCat.ofHom ⟨fun x => WithUpper.toUpper (WithUpperSet.ofUpperSet x),
    Topology.IsUpperSet.monotone_to_upperTopology_continuous fun _ _ h => h⟩

theorem mem_map_rayId (V : Opens raySpace) (x : WithUpperSet ℝ) :
    x ∈ (Opens.map rayId).obj V ↔ WithUpper.toUpper (WithUpperSet.ofUpperSet x) ∈ V :=
  Iff.rfl

/-- For `t < s`, the principal open `↑s` lies in the preimage of the ray `(t, ∞)`. -/
theorem principalOpen_le_map_ray {t s : ℝ} (h : t < s) :
    _root_.Alexandrov.principalOpen (X := upperSpace ℝ) (WithUpperSet.toUpperSet s) ≤
      (Opens.map rayId).obj (ray t) :=
  (_root_.Alexandrov.principalOpen_le_iff _).2 h

/-! ## The functors `Q` and `B` -/

section Functors

variable (C : Type u) [Category.{0} C]

/-- The open rays as a functor `ℝ ⥤ (Opens raySpace)ᵒᵖ`: `t ↦ (t, ∞)`, and `s ≤ t` gives the
inclusion `(t, ∞) ⊆ (s, ∞)`. -/
def rayFunctor : ℝ ⥤ (Opens raySpace)ᵒᵖ where
  obj t := op (ray t)
  map f := (homOfLE (ray_antitone (leOfHom f))).op

/-- The functor `B`: `B(F)(t) = F((t, ∞))`, and for `s ≤ t` the map `B(F)(s) ⟶ B(F)(t)` is the
restriction along `(t, ∞) ⊆ (s, ∞)`. -/
def rayB : raySpace.Sheaf C ⥤ (ℝ ⥤ C) :=
  TopCat.Sheaf.forget C raySpace ⋙
    (Functor.whiskeringLeft ℝ (Opens raySpace)ᵒᵖ C).obj rayFunctor

variable {C}

@[simp]
theorem rayB_obj_obj (F : raySpace.Sheaf C) (t : ℝ) :
    ((rayB C).obj F).obj t = F.presheaf.obj (op (ray t)) :=
  rfl

@[simp]
theorem rayB_obj_map (F : raySpace.Sheaf C) {s t : ℝ} (f : s ⟶ t) :
    ((rayB C).obj F).map f = F.presheaf.map (homOfLE (ray_antitone (leOfHom f))).op :=
  rfl

@[simp]
theorem rayB_map_app {F G : raySpace.Sheaf C} (φ : F ⟶ G) (t : ℝ) :
    ((rayB C).map φ).app t = φ.hom.app (op (ray t)) :=
  rfl

variable (C) [HasLimits C]

/-- The functor `Q`: the Alexandrov sheaf `(upperSetEquivalence ℝ C).functor.obj M` of a
diagram `M`, pushed forward along the continuous identity `rayId` to the ray space. -/
def rayQ : (ℝ ⥤ C) ⥤ raySpace.Sheaf C :=
  (upperSetEquivalence ℝ C).functor ⋙ TopCat.Sheaf.pushforward C rayId

variable {C}

/-- `Q(M)(V)` is the Alexandrov sheaf of `M` on the preimage of `V`. -/
theorem rayQ_obj_presheaf_obj (M : ℝ ⥤ C) (V : Opens raySpace) :
    ((rayQ C).obj M).presheaf.obj (op V) =
      ((upperSetEquivalence ℝ C).functor.obj M).presheaf.obj (op ((Opens.map rayId).obj V)) :=
  rfl

/-- `Q` on a morphism is the component of the Alexandrov sheaf map on the preimage. -/
theorem rayQ_map_hom_app {M N : ℝ ⥤ C} (α : M ⟶ N) (V : Opens raySpace) :
    ((rayQ C).map α).hom.app (op V) =
      ((upperSetEquivalence ℝ C).functor.map α).hom.app (op ((Opens.map rayId).obj V)) :=
  rfl

/-- The diagram over the principal opens contained in the preimage of `V` whose limit is the
value of `Q(M)` on `V`. -/
private abbrev kanDiagram (M : ℝ ⥤ C) (V : Opens raySpace) :=
  StructuredArrow.proj (op ((Opens.map rayId).obj V))
      (_root_.Alexandrov.principals (upperSpace ℝ)) ⋙
    (WithUpperSet.toUpperSetOrderIso (α := ℝ)).symm.monotone.functor ⋙ M

/-- The index `↑s ⊆ (t, ∞)` of `kanDiagram`. -/
private abbrev kanIndex {t s : ℝ} (h : t < s) :
    StructuredArrow (op ((Opens.map rayId).obj (ray t)))
      (_root_.Alexandrov.principals (upperSpace ℝ)) :=
  StructuredArrow.mk (homOfLE (principalOpen_le_map_ray h)).op

/-- A principal open `↑p` contained in the preimage of an open `V` has `p ∈ V`. -/
private theorem mem_of_kanIndex {V : Opens raySpace}
    (j : StructuredArrow (op ((Opens.map rayId).obj V))
      (_root_.Alexandrov.principals (upperSpace ℝ))) :
    WithUpper.toUpper (WithUpperSet.ofUpperSet (α := ℝ) j.right) ∈ V :=
  (_root_.Alexandrov.principalOpen_le_iff (X := upperSpace ℝ) _).1 j.hom.unop.le

/-! ## Rays of `BQ(M)` as limits -/

/-- The projection `BQ(M)(t) ⟶ M(s)` for `t < s`: the limit projection of the Kan extension at
the principal open `↑s ⊆ (t, ∞)`. -/
def rayProj (M : ℝ ⥤ C) {t s : ℝ} (h : t < s) :
    ((rayB C).obj ((rayQ C).obj M)).obj t ⟶ M.obj s :=
  limit.π (kanDiagram M (ray t)) (kanIndex h)

/-- Projections are compatible with the maps of `M`. -/
@[reassoc]
theorem rayProj_comp_map (M : ℝ ⥤ C) {t s s' : ℝ} (h : t < s) (f : s ⟶ s') :
    rayProj M h ≫ M.map f = rayProj M (h.trans_le (leOfHom f)) :=
  limit.w (kanDiagram M (ray t)) (StructuredArrow.homMk (homOfLE (leOfHom f)) rfl :
    kanIndex h ⟶ kanIndex (h.trans_le (leOfHom f)))

/-- A restriction of `Q(M)` followed by a limit projection is the projection at the same
principal open. -/
private theorem kan_map_π (M : ℝ ⥤ C) {V W : Opens raySpace} (h : W ≤ V)
    (j : StructuredArrow (op ((Opens.map rayId).obj W))
      (_root_.Alexandrov.principals (upperSpace ℝ))) :
    ((rayQ C).obj M).presheaf.map (homOfLE h).op ≫ limit.π (kanDiagram M W) j =
      limit.π (kanDiagram M V)
        ((StructuredArrow.map ((Opens.map rayId).op.map (homOfLE h).op)).obj j) := by
  change ((_root_.Alexandrov.principals (upperSpace ℝ)).pointwiseRightKanExtension
      ((WithUpperSet.toUpperSetOrderIso (α := ℝ)).symm.monotone.functor ⋙ M)).map
        ((Opens.map rayId).op.map (homOfLE h).op) ≫ limit.π (kanDiagram M W) j = _
  erw [Functor.pointwiseRightKanExtension_map, limit.lift_π]
  rfl

/-- Projections are compatible with the maps of `BQ(M)`. -/
@[reassoc]
theorem map_rayProj (M : ℝ ⥤ C) {t t' s : ℝ} (f : t ⟶ t') (h : t' < s) :
    ((rayB C).obj ((rayQ C).obj M)).map f ≫ rayProj M h =
      rayProj M ((leOfHom f).trans_lt h) :=
  kan_map_π M (ray_antitone (leOfHom f)) (kanIndex h)

/-- Two maps into `BQ(M)(t)` agree when all their projections agree. -/
theorem rayProj_ext (M : ℝ ⥤ C) {t : ℝ} {X : C}
    {f g : X ⟶ ((rayB C).obj ((rayQ C).obj M)).obj t}
    (h : ∀ (s : ℝ) (hs : t < s), f ≫ rayProj M hs = g ≫ rayProj M hs) : f = g := by
  refine limit.hom_ext (F := kanDiagram M (ray t)) fun j => ?_
  obtain ⟨⟨⟨⟩⟩, p, j⟩ := j
  exact h (WithUpperSet.ofUpperSet (α := ℝ) p)
    ((_root_.Alexandrov.principalOpen_le_iff (X := upperSpace ℝ) _).1 j.unop.le)

/-- The projections commute with `Q` and `B` applied to a morphism. -/
@[reassoc]
theorem map_app_rayProj {M N : ℝ ⥤ C} (α : M ⟶ N) {t s : ℝ} (h : t < s) :
    ((rayB C).map ((rayQ C).map α)).app t ≫ rayProj N h = rayProj M h ≫ α.app s :=
  kanSheaf_map_hom_app_π (X := upperSpace ℝ) (C := C)
    (Functor.whiskerLeft (WithUpperSet.toUpperSetOrderIso (α := ℝ)).symm.monotone.functor α)
    (op ((Opens.map rayId).obj (ray t))) (kanIndex h)

/-- The diagram `s ↦ M(s)` on the open ray `(t, ∞)` of `ℝ`. -/
def rayDiagram (M : ℝ ⥤ C) (t : ℝ) : Set.Ioi t ⥤ C :=
  (show Monotone (Subtype.val : Set.Ioi t → ℝ) from fun _ _ h => h).functor ⋙ M

omit [HasLimits C] in
@[simp]
theorem rayDiagram_obj (M : ℝ ⥤ C) (t : ℝ) (s : Set.Ioi t) :
    (rayDiagram M t).obj s = M.obj s :=
  rfl

/-- The cone of projections from `BQ(M)(t)` over `s ↦ M(s)` on `(t, ∞)`. -/
@[simps]
def rayCone (M : ℝ ⥤ C) (t : ℝ) : Cone (rayDiagram M t) where
  pt := ((rayB C).obj ((rayQ C).obj M)).obj t
  π :=
    { app := fun s => rayProj M s.2
      naturality := fun s _ _ => (Category.id_comp _).trans (rayProj_comp_map M s.2 _).symm }

/-- `BQ(M)(t)` is the limit of `s ↦ M(s)` over `s > t`, with the projections `rayProj`. -/
def rayConeIsLimit (M : ℝ ⥤ C) (t : ℝ) : IsLimit (rayCone M t) where
  lift c := limit.lift (kanDiagram M (ray t))
    { pt := c.pt
      π :=
        { app := fun j => c.π.app ⟨WithUpperSet.ofUpperSet (α := ℝ) j.right, mem_of_kanIndex j⟩
          naturality := fun j j' g => (Category.id_comp _).trans
            (c.w (homOfLE (leOfHom g.right) :
              (⟨_, mem_of_kanIndex j⟩ : Set.Ioi t) ⟶ ⟨_, mem_of_kanIndex j'⟩)).symm } }
  fac c s := limit.lift_π _ (kanIndex s.2)
  uniq c m hm := rayProj_ext M fun s hs => by
    refine (hm ⟨s, hs⟩).trans ?_
    change _ = _ ≫ limit.π (kanDiagram M (ray t)) (kanIndex hs)
    rw [limit.lift_π]
    rfl

/-- The comparison `BQ(M)(t) ≅ lim_{s > t} M(s)`. -/
def rayLimitIso (M : ℝ ⥤ C) (t : ℝ) :
    ((rayB C).obj ((rayQ C).obj M)).obj t ≅ limit (rayDiagram M t) :=
  (rayConeIsLimit M t).conePointUniqueUpToIso (limit.isLimit _)

@[reassoc (attr := simp)]
theorem rayLimitIso_hom_π (M : ℝ ⥤ C) (t : ℝ) (s : Set.Ioi t) :
    (rayLimitIso M t).hom ≫ limit.π (rayDiagram M t) s = rayProj M s.2 :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ s

@[reassoc (attr := simp)]
theorem rayLimitIso_inv_rayProj (M : ℝ ⥤ C) (t : ℝ) (s : Set.Ioi t) :
    (rayLimitIso M t).inv ≫ rayProj M s.2 = limit.π (rayDiagram M t) s :=
  IsLimit.conePointUniqueUpToIso_inv_comp _ _ s

/-- A family of maps `X ⟶ M(s)` for `s > t`, compatible with the maps of `M`, lifts to
`X ⟶ BQ(M)(t)`. -/
def rayLift (M : ℝ ⥤ C) {t : ℝ} {X : C} (f : ∀ s : ℝ, t < s → (X ⟶ M.obj s))
    (hf : ∀ (s s' : ℝ) (hs : t < s) (h : s ≤ s'),
      f s hs ≫ M.map (homOfLE h) = f s' (hs.trans_le h)) :
    X ⟶ ((rayB C).obj ((rayQ C).obj M)).obj t :=
  (rayConeIsLimit M t).lift
    { pt := X
      π :=
        { app := fun s => f s.1 s.2
          naturality := fun s s' g =>
            (Category.id_comp _).trans (hf s.1 s'.1 s.2 (leOfHom g)).symm } }

@[reassoc (attr := simp)]
theorem rayLift_rayProj (M : ℝ ⥤ C) {t : ℝ} {X : C} (f : ∀ s : ℝ, t < s → (X ⟶ M.obj s))
    (hf : ∀ (s s' : ℝ) (hs : t < s) (h : s ≤ s'),
      f s hs ≫ M.map (homOfLE h) = f s' (hs.trans_le h)) {s : ℝ} (hs : t < s) :
    rayLift M f hf ≫ rayProj M hs = f s hs :=
  (rayConeIsLimit M t).fac _ ⟨s, hs⟩

/-! ## The unit -/

omit [HasLimits C] in
/-- The maps `M(t ≤ s)` for `s > t` are compatible with the maps of `M`. -/
private theorem unit_compat (M : ℝ ⥤ C) (t : ℝ) (s s' : ℝ) (hs : t < s) (h : s ≤ s') :
    M.map (homOfLE hs.le) ≫ M.map (homOfLE h) = M.map (homOfLE (hs.trans_le h).le) := by
  rw [← M.map_comp]
  rfl

variable (C)

/-- The unit `η : M ⟶ BQ(M)`: at `t`, the lift of the maps `M(t ≤ s)` for `s > t`. -/
def rayUnit : 𝟭 (ℝ ⥤ C) ⟶ rayQ C ⋙ rayB C where
  app M :=
    { app := fun t => rayLift M (fun _ hs => M.map (homOfLE hs.le)) (unit_compat M t)
      naturality := fun t t' f => rayProj_ext M fun _ hs => by
        simp only [Functor.id_obj, Functor.comp_obj, Category.assoc, rayLift_rayProj,
          map_rayProj, ← M.map_comp]
        rfl }
  naturality M N α := by
    ext t
    exact rayProj_ext N fun _ hs => by
      simp only [Functor.id_obj, Functor.comp_obj, Functor.id_map, NatTrans.comp_app,
        Functor.comp_map, Category.assoc, rayLift_rayProj, map_app_rayProj,
        rayLift_rayProj_assoc]
      exact (α.naturality _).symm

variable {C}

/-- The unit followed by a projection is the map of `M`. -/
@[reassoc (attr := simp)]
theorem rayUnit_app_app_rayProj (M : ℝ ⥤ C) {t s : ℝ} (h : t < s) :
    ((rayUnit C).app M).app t ≫ rayProj M h = M.map (homOfLE h.le) :=
  rayLift_rayProj M (fun _ hs => M.map (homOfLE hs.le)) (unit_compat M t) h

end Functors

/-! ## `QB ≅ 𝟭` by the ray cover -/

section Counit

variable {C : Type u} [Category.{0} C] [HasLimits C]

omit [HasLimits C] in


/-- The cone of restrictions `F(V) ⟶ F((p, ∞))` over the rays at the points `p` of `V`. -/
private def restrictionCone (F : raySpace.Sheaf C) (V : Opens raySpace) :
    Cone (kanDiagram ((rayB C).obj F) V) where
  pt := F.presheaf.obj (op V)
  π :=
    { app := fun j => F.presheaf.map (homOfLE (ray_le (mem_of_kanIndex j))).op
      naturality := fun _ _ _ =>
        (Category.id_comp _).trans (presheaf_map_comp_map F.presheaf _ _ _).symm }

/-- The index of the ray at a point `p` of `V`. -/
private abbrev pointIndex {V : Opens raySpace} (i : {p : ℝ // WithUpper.toUpper p ∈ V}) :
    StructuredArrow (op ((Opens.map rayId).obj V)) (_root_.Alexandrov.principals (upperSpace ℝ)) :=
  StructuredArrow.mk (homOfLE ((_root_.Alexandrov.principalOpen_le_iff (X := upperSpace ℝ)
    (x := WithUpperSet.toUpperSet i.1) _).2 i.2)).op

omit [HasLimits C] in
/-- On the intersection of two rays, the restrictions of a cone agree: both factor through the
ray at the larger endpoint. -/
private theorem cone_inf (F : raySpace.Sheaf C) {V : Opens raySpace}
    (s : Cone (kanDiagram ((rayB C).obj F) V)) (i j : {p : ℝ // WithUpper.toUpper p ∈ V}) :
    s.π.app (pointIndex i) ≫
        F.presheaf.map (homOfLE (inf_le_left : ray i.1 ⊓ ray j.1 ≤ ray i.1)).op =
      s.π.app (pointIndex j) ≫ F.presheaf.map (homOfLE inf_le_right).op := by
  have hk : WithUpper.toUpper (max i.1 j.1) ∈ V :=
    (isUpperSet_isOpen_toUpper_preimage V).1 (le_max_left i.1 j.1) i.2
  have hi := s.w (StructuredArrow.homMk (homOfLE (le_max_left i.1 j.1)) rfl :
    pointIndex i ⟶ pointIndex ⟨_, hk⟩)
  have hj := s.w (StructuredArrow.homMk (homOfLE (le_max_right i.1 j.1)) rfl :
    pointIndex j ⟶ pointIndex ⟨_, hk⟩)
  have hle : ray i.1 ⊓ ray j.1 ≤ ray (max i.1 j.1) := (ray_inf _ _).le
  have key : s.π.app (pointIndex i) ≫
        F.presheaf.map (homOfLE (ray_antitone (le_max_left i.1 j.1))).op =
      s.π.app (pointIndex j) ≫
        F.presheaf.map (homOfLE (ray_antitone (le_max_right i.1 j.1))).op :=
    hi.trans hj.symm
  refine (congrArg (s.π.app (pointIndex i) ≫ ·) (presheaf_map_comp_map F.presheaf
    (homOfLE (ray_antitone (le_max_left i.1 j.1))).op (homOfLE hle).op _).symm).trans ?_
  refine Eq.trans ?_ (congrArg (s.π.app (pointIndex j) ≫ ·) (presheaf_map_comp_map F.presheaf
    (homOfLE (ray_antitone (le_max_right i.1 j.1))).op (homOfLE hle).op _))
  refine (Category.assoc _ _ _).symm.trans (Eq.trans ?_ (Category.assoc _ _ _))
  exact congrArg (· ≫ F.presheaf.map (homOfLE hle).op) key

/-- The components of the cone over the pairwise intersections of the ray cover. -/
private def pairApp (F : raySpace.Sheaf C) {V : Opens raySpace}
    (s : Cone (kanDiagram ((rayB C).obj F) V)) :
    ∀ o : Pairwise {p : ℝ // WithUpper.toUpper p ∈ V},
      s.pt ⟶ F.presheaf.obj (op ((Pairwise.diagram fun i : {p : ℝ // WithUpper.toUpper p ∈ V} =>
        ray i.1).obj o))
  | .single i => s.π.app (pointIndex i)
  | .pair i _ => s.π.app (pointIndex i) ≫ F.presheaf.map (homOfLE inf_le_left).op

/-- A cone over the ray diagram of `V` gives a cone over the pairwise intersections of the ray
cover of `V`. -/
private def pairCone (F : raySpace.Sheaf C) {V : Opens raySpace}
    (s : Cone (kanDiagram ((rayB C).obj F) V)) :
    Cone ((Pairwise.diagram fun i : {p : ℝ // WithUpper.toUpper p ∈ V} => ray i.1).op ⋙
      F.presheaf) where
  pt := s.pt
  π :=
    { app := fun o => pairApp F s o.unop
      naturality := by
        rintro ⟨o⟩ ⟨o'⟩ ⟨f⟩
        refine (Category.id_comp _).trans ?_
        cases f with
        | id_single i =>
          change _ = _ ≫ F.presheaf.map (𝟙 _)
          rw [F.presheaf.map_id, Category.comp_id]
        | id_pair i j =>
          change _ = _ ≫ F.presheaf.map (𝟙 _)
          rw [F.presheaf.map_id, Category.comp_id]
        | left i j => rfl
        | right i j => exact cone_inf F s i j }

/-- The restrictions of a sheaf on the ray space to the rays at the points of `V` form a limit
cone: by the sheaf condition for the ray cover, whose pairwise intersections are rays. -/
private def restrictionConeIsLimit (F : raySpace.Sheaf C) (V : Opens raySpace) :
    IsLimit (restrictionCone F V) :=
  let P := (TopCat.Presheaf.IsSheaf.isSheafPairwiseIntersections (F := F.presheaf)
    (U := fun i : {p : ℝ // WithUpper.toUpper p ∈ V} => ray i.1) F.property).some
  { lift := fun s => P.lift (pairCone F s) ≫ F.presheaf.map (homOfLE (iSup_ray V).ge).op
    fac := fun s j => by
      obtain ⟨⟨⟨⟩⟩, p, hj⟩ := j
      have h := P.fac (pairCone F s)
        (op (Pairwise.single ⟨WithUpperSet.ofUpperSet (α := ℝ) p, mem_of_kanIndex ⟨_, p, hj⟩⟩))
      refine Eq.trans ?_ h
      refine (Category.assoc _ _ _).trans ?_
      exact congrArg (P.lift (pairCone F s) ≫ ·) (presheaf_map_comp_map F.presheaf _ _ _)
    uniq := fun s m hm => by
      have h1 : m ≫ F.presheaf.map (homOfLE (iSup_ray V).le).op = P.lift (pairCone F s) := by
        refine P.uniq (pairCone F s) _ fun o => ?_
        obtain ⟨o⟩ := o
        cases o with
        | single i =>
          refine Eq.trans ?_ (hm (pointIndex i))
          refine (Category.assoc _ _ _).trans ?_
          exact congrArg (m ≫ ·) (presheaf_map_comp_map F.presheaf _ _ _)
        | pair i j =>
          refine Eq.trans ?_
            (congrArg (· ≫ F.presheaf.map (homOfLE inf_le_left).op) (hm (pointIndex i)))
          refine (Category.assoc _ _ _).trans (Eq.trans ?_ (Category.assoc _ _ _).symm)
          exact congrArg (m ≫ ·) ((presheaf_map_comp_map F.presheaf _ _
            (homOfLE (inf_le_left.trans (ray_le i.2) : ray i.1 ⊓ ray j.1 ≤ V)).op).trans
              (presheaf_map_comp_map F.presheaf _ _ _).symm)
      refine Eq.trans ?_ (congrArg (· ≫ F.presheaf.map (homOfLE (iSup_ray V).ge).op) h1)
      refine Eq.trans ?_ (Category.assoc _ _ _).symm
      refine Eq.trans (Category.comp_id m).symm (congrArg (m ≫ ·) ?_)
      exact (F.presheaf.map_id _).symm.trans (presheaf_map_comp_map F.presheaf _ _ _).symm }

/-- The comparison `F(V) ⟶ Q(B F)(V)`: the lift of the restrictions to the rays in `V`. -/
private abbrev counitApp (F : raySpace.Sheaf C) (V : Opens raySpace) :
    F.presheaf.obj (op V) ⟶ ((rayQ C).obj ((rayB C).obj F)).presheaf.obj (op V) :=
  limit.lift (kanDiagram ((rayB C).obj F) V) (restrictionCone F V)

private theorem counitApp_π (F : raySpace.Sheaf C) (V : Opens raySpace)
    (j : StructuredArrow (op ((Opens.map rayId).obj V))
      (_root_.Alexandrov.principals (upperSpace ℝ))) :
    counitApp F V ≫ limit.π (kanDiagram ((rayB C).obj F) V) j =
      F.presheaf.map (homOfLE (ray_le (mem_of_kanIndex j))).op :=
  limit.lift_π _ _

/-- The comparison `F(V) ≅ Q(B F)(V)`, as a natural isomorphism of presheaves. -/
private def counitPresheafIso (F : raySpace.Sheaf C) :
    F.presheaf ≅ ((rayQ C).obj ((rayB C).obj F)).presheaf :=
  NatIso.ofComponents
    (fun V => (restrictionConeIsLimit F V.unop).conePointUniqueUpToIso (limit.isLimit _))
    (fun {V W} f => by
      obtain ⟨V⟩ := V
      obtain ⟨W⟩ := W
      obtain ⟨⟨⟨hf⟩⟩⟩ := f
      change F.presheaf.map (homOfLE hf).op ≫ counitApp F W =
        counitApp F V ≫ ((rayQ C).obj ((rayB C).obj F)).presheaf.map (homOfLE hf).op
      refine limit.hom_ext (F := kanDiagram ((rayB C).obj F) W) fun j => ?_
      refine (Category.assoc _ _ _).trans
        ((congrArg (F.presheaf.map (homOfLE hf).op ≫ ·) (counitApp_π F W j)).trans ?_)
      refine Eq.trans ?_ (Category.assoc _ _ _).symm
      refine Eq.trans ?_ (congrArg (counitApp F V ≫ ·) (kan_map_π _ hf j).symm)
      refine Eq.trans ?_ (counitApp_π F V
        ((StructuredArrow.map ((Opens.map rayId).op.map (homOfLE hf).op)).obj j)).symm
      exact presheaf_map_comp_map _ _ _ _)

variable (C)

/-- `QB ≅ 𝟭`: a sheaf `F` on the ray space is recovered from its values on rays. On an open `V`,
the inverse compares `F(V)` with the limit of `F((p, ∞))` over the points `p` of `V`, by
restriction; it is invertible by the sheaf condition for the ray cover of `V`. -/
def rayCounitIso : rayB C ⋙ rayQ C ≅ 𝟭 (raySpace.Sheaf C) :=
  (NatIso.ofComponents (fun F => ObjectProperty.isoMk _ (counitPresheafIso F))
    (fun {F G} φ => by
      apply CategoryTheory.Sheaf.hom_ext
      ext V
      obtain ⟨V⟩ := V
      change φ.hom.app (op V) ≫ counitApp G V =
        counitApp F V ≫ ((rayQ C).map ((rayB C).map φ)).hom.app (op V)
      refine limit.hom_ext (F := kanDiagram ((rayB C).obj G) V) fun j => ?_
      refine (Category.assoc _ _ _).trans
        ((congrArg (φ.hom.app (op V) ≫ ·) (counitApp_π G V j)).trans ?_)
      refine Eq.trans ?_ (Category.assoc _ _ _).symm
      refine Eq.trans ?_ (congrArg (counitApp F V ≫ ·) (kanSheaf_map_hom_app_π
        (X := upperSpace ℝ) (C := C)
        (Functor.whiskerLeft (WithUpperSet.toUpperSetOrderIso (α := ℝ)).symm.monotone.functor
          ((rayB C).map φ)) (op ((Opens.map rayId).obj V)) j).symm)
      refine Eq.trans ?_ (Category.assoc _ _ _)
      refine Eq.trans ?_ (congrArg (· ≫ _) (counitApp_π F V j).symm)
      exact (φ.hom.naturality _).symm)).symm

variable {C}

/-- On a ray, the inverse of the counit followed by a projection is the restriction of `F`. -/
@[reassoc (attr := simp)]
theorem rayCounitIso_inv_app_hom_app_rayProj (F : raySpace.Sheaf C) {t s : ℝ} (h : t < s) :
    ((rayCounitIso C).inv.app F).hom.app (op (ray t)) ≫ rayProj ((rayB C).obj F) h =
      F.presheaf.map (homOfLE (ray_antitone h.le)).op :=
  counitApp_π F (ray t) (kanIndex h)

/-- On a ray, the counit followed by a restriction of `F` is the projection. -/
@[reassoc (attr := simp)]
theorem rayCounitIso_hom_app_hom_app_map (F : raySpace.Sheaf C) {t s : ℝ} (h : t < s) :
    ((rayCounitIso C).hom.app F).hom.app (op (ray t)) ≫
        F.presheaf.map (homOfLE (ray_antitone h.le)).op =
      rayProj ((rayB C).obj F) h := by
  have h1 := congrArg (fun φ => φ.hom.app (op (ray t)) ≫ rayProj ((rayB C).obj F) h)
    ((rayCounitIso C).hom_inv_id_app F)
  refine Eq.trans ?_ (h1.trans (Category.id_comp _))
  refine (congrArg (_ ≫ ·) (rayCounitIso_inv_app_hom_app_rayProj F h).symm).trans ?_
  exact (Category.assoc _ _ _).symm

instance rayB_faithful : (rayB C).Faithful :=
  Functor.Faithful.of_comp_iso (rayCounitIso C)

end Counit

/-! ## Translations of the ray space -/

section Shift

/-- The continuous map `x ↦ x - ε` of the ray space. -/
def rayTranslate (ε : ℝ≥0) : raySpace ⟶ raySpace :=
  TopCat.ofHom ⟨fun x => WithUpper.toUpper (WithUpper.ofUpper x - (ε : ℝ)), by
    rw [IsUpper.continuous_iff_Iic]
    intro a
    have h : (fun x : WithUpper ℝ => WithUpper.toUpper (WithUpper.ofUpper x - (ε : ℝ))) ⁻¹'
        Set.Iic a = Set.Iic (WithUpper.toUpper (WithUpper.ofUpper a + (ε : ℝ))) := by
      ext x
      change WithUpper.ofUpper (α := ℝ) x - (ε : ℝ) ≤ WithUpper.ofUpper (α := ℝ) a ↔
        WithUpper.ofUpper (α := ℝ) x ≤ WithUpper.ofUpper (α := ℝ) a + (ε : ℝ)
      exact sub_le_iff_le_add
    rw [h]
    exact isClosed_Iic⟩

/-- The ray `(t, ∞)` pulls back to `(t + ε, ∞)` under `x ↦ x - ε`. -/
theorem map_rayTranslate_ray (ε : ℝ≥0) (t : ℝ) :
    (Opens.map (rayTranslate ε)).obj (ray t) = ray (t + ε) := by
  ext x
  change t < WithUpper.ofUpper (α := ℝ) x - (ε : ℝ) ↔ t + (ε : ℝ) < WithUpper.ofUpper (α := ℝ) x
  exact lt_sub_iff_add_lt

/-- The preimage of an open under `x ↦ x - ε` is contained in it. -/
theorem map_rayTranslate_le (ε : ℝ≥0) (V : Opens raySpace) :
    (Opens.map (rayTranslate ε)).obj V ≤ V := fun x hx =>
  (isUpperSet_isOpen_toUpper_preimage V).1
    (show WithUpper.ofUpper (α := ℝ) x - (ε : ℝ) ≤ WithUpper.ofUpper (α := ℝ) x from
      sub_le_self _ ε.coe_nonneg) hx

/-- Translating by `ε` and then by `δ` is translating by `ε + δ`. -/
theorem map_rayTranslate_comp (ε δ : ℝ≥0) (V : Opens raySpace) :
    (Opens.map (rayTranslate δ)).obj ((Opens.map (rayTranslate ε)).obj V) =
      (Opens.map (rayTranslate (ε + δ))).obj V := by
  ext x
  change WithUpper.toUpper (WithUpper.ofUpper (α := ℝ) x - (δ : ℝ) - (ε : ℝ)) ∈ V ↔
    WithUpper.toUpper (WithUpper.ofUpper (α := ℝ) x - ((ε + δ : ℝ≥0) : ℝ)) ∈ V
  rw [NNReal.coe_add, sub_sub, add_comm (δ : ℝ)]

/-- The identity to the ray space intertwines the translations of the two lines. -/
theorem translate_comp_rayId (ε : ℝ≥0) : translate ε ≫ rayId = rayId ≫ rayTranslate ε :=
  rfl

variable {C : Type u} [Category.{0} C]





/-- A composite of three restrictions is the restriction between the outer opens. -/
private theorem map_comp_map_comp (P : (Opens raySpace)ᵒᵖ ⥤ C) {U V W Z : (Opens raySpace)ᵒᵖ}
    (f : U ⟶ V) (g : V ⟶ W) (h : W ⟶ Z) (k : U ⟶ Z) :
    P.map f ≫ P.map g ≫ P.map h = P.map k :=
  (congrArg (P.map f ≫ ·) (presheaf_map_comp_map P g h (g ≫ h))).trans (presheaf_map_comp_map P _ _ _)



variable (C)

/-- The ray-sheaf shift: pushforward along `x ↦ x - ε`, so `(S ε F)(V) = F(V + ε)`. -/
def rayShift (ε : ℝ≥0) : raySpace.Sheaf C ⥤ raySpace.Sheaf C :=
  TopCat.Sheaf.pushforward C (rayTranslate ε)

/-- The transition `F ⟶ S ε F`: restriction along `V + ε ⊆ V`. -/
def rayTransition (ε : ℝ≥0) : 𝟭 (raySpace.Sheaf C) ⟶ rayShift C ε where
  app F := ObjectProperty.homMk
    { app := fun V => F.presheaf.map (homOfLE (map_rayTranslate_le ε V.unop)).op
      naturality := fun _ _ _ => by
        change F.presheaf.map _ ≫ F.presheaf.map _ = F.presheaf.map _ ≫ F.presheaf.map _
        exact presheaf_map_comp_map_eq _ _ _ _ _ }
  naturality _ _ φ := by
    apply CategoryTheory.Sheaf.hom_ext
    ext V
    exact (φ.hom.naturality _).symm

/-- The addition isomorphism `S δ ⋙ S ε ≅ S (ε + δ)`, by `(V + ε) + δ = V + (ε + δ)`. -/
def rayCompIso (ε δ : ℝ≥0) : rayShift C δ ⋙ rayShift C ε ≅ rayShift C (ε + δ) :=
  NatIso.ofComponents
    (fun F => ObjectProperty.isoMk _ (NatIso.ofComponents
      (fun V => TDA.Sheaf.restrictIso F.presheaf (map_rayTranslate_comp ε δ V.unop))
      (fun _ => by
        change F.presheaf.map _ ≫ F.presheaf.map _ = F.presheaf.map _ ≫ F.presheaf.map _
        exact presheaf_map_comp_map_eq _ _ _ _ _)))
    (fun φ => by
      apply CategoryTheory.Sheaf.hom_ext
      ext V
      exact (φ.hom.naturality _).symm)

variable {C}

@[simp]
theorem rayShift_obj_presheaf_obj (ε : ℝ≥0) (F : raySpace.Sheaf C) (V : Opens raySpace) :
    ((rayShift C ε).obj F).presheaf.obj (op V) =
      F.presheaf.obj (op ((Opens.map (rayTranslate ε)).obj V)) :=
  rfl

@[simp]
theorem rayShift_map_hom_app (ε : ℝ≥0) {F G : raySpace.Sheaf C} (φ : F ⟶ G)
    (V : Opens raySpace) :
    ((rayShift C ε).map φ).hom.app (op V) = φ.hom.app (op ((Opens.map (rayTranslate ε)).obj V)) :=
  rfl

@[simp]
theorem rayTransition_app_hom_app (ε : ℝ≥0) (F : raySpace.Sheaf C) (V : Opens raySpace) :
    ((rayTransition C ε).app F).hom.app (op V) =
      F.presheaf.map (homOfLE (map_rayTranslate_le ε V)).op :=
  rfl

@[simp]
theorem rayCompIso_hom_app_hom_app (ε δ : ℝ≥0) (F : raySpace.Sheaf C) (V : Opens raySpace) :
    ((rayCompIso C ε δ).hom.app F).hom.app (op V) =
      F.presheaf.map (homOfLE (map_rayTranslate_comp ε δ V).ge).op :=
  rfl

/-- Naturality of the addition isomorphism. -/
@[reassoc]
theorem rayCompIso_hom_naturality (ε δ : ℝ≥0) {F G : raySpace.Sheaf C} (φ : F ⟶ G) :
    (rayShift C ε).map ((rayShift C δ).map φ) ≫ (rayCompIso C ε δ).hom.app G =
      (rayCompIso C ε δ).hom.app F ≫ (rayShift C (ε + δ)).map φ :=
  (rayCompIso C ε δ).hom.naturality φ

/-- Naturality of the transition. -/
@[reassoc]
theorem rayTransition_naturality (ε : ℝ≥0) {F G : raySpace.Sheaf C} (φ : F ⟶ G) :
    φ ≫ (rayTransition C ε).app G = (rayTransition C ε).app F ≫ (rayShift C ε).map φ :=
  (rayTransition C ε).naturality φ

/-- Two transitions compose to the transition by the sum. -/
theorem rayTransition_add (ε δ : ℝ≥0) (F : raySpace.Sheaf C) :
    (rayTransition C ε).app F ≫ (rayShift C ε).map ((rayTransition C δ).app F) ≫
        (rayCompIso C ε δ).hom.app F =
      (rayTransition C (ε + δ)).app F := by
  apply CategoryTheory.Sheaf.hom_ext
  ext V
  exact map_comp_map_comp _ _ _ _ _

/-! ### Matching the translations of the upper Alexandrov line -/

/-- Pushing forward along `rayId` carries the Alexandrov shift to the ray-sheaf shift at the
same radius. -/
theorem pushforward_map_sheafShift_map (ε : ℝ≥0) {F G : (upperSpace ℝ).Sheaf C} (φ : F ⟶ G) :
    (TopCat.Sheaf.pushforward C rayId).map ((sheafShift C ε).map φ) =
      (rayShift C ε).map ((TopCat.Sheaf.pushforward C rayId).map φ) :=
  rfl

/-- Pushing forward along `rayId` carries the Alexandrov transition to the ray-sheaf
transition at the same radius. -/
theorem pushforward_map_sheafTransition (ε : ℝ≥0) (F : (upperSpace ℝ).Sheaf C) :
    (TopCat.Sheaf.pushforward C rayId).map ((sheafTransition C ε).app F) =
      (rayTransition C ε).app ((TopCat.Sheaf.pushforward C rayId).obj F) :=
  rfl

/-- Pushing forward along `rayId` carries the Alexandrov addition isomorphism to the
ray-sheaf one. -/
theorem pushforward_map_sheafCompIso (ε δ : ℝ≥0) (F : (upperSpace ℝ).Sheaf C) :
    (TopCat.Sheaf.pushforward C rayId).map ((sheafCompIso C ε δ).hom.app F) =
      (rayCompIso C ε δ).hom.app ((TopCat.Sheaf.pushforward C rayId).obj F) :=
  rfl

end Shift

/-! ## Ray-sheaf interleavings -/

section Interleaving

variable {C : Type u} [Category.{0} C]

/-- A ray-sheaf `ε`-interleaving, in the orientation of `RealInterleaving` and
`SheafInterleaving`. -/
structure RaySheafInterleaving (ε : ℝ≥0) (F G : raySpace.Sheaf C) where
  /-- The arrow from the first sheaf to the shifted second sheaf. -/
  φ : F ⟶ (rayShift C ε).obj G
  /-- The arrow from the second sheaf to the shifted first sheaf. -/
  ψ : G ⟶ (rayShift C ε).obj F
  /-- The first composite is the double-shift transition. -/
  φ_ψ : φ ≫ (rayShift C ε).map ψ ≫ (rayCompIso C ε ε).hom.app F =
    (rayTransition C (ε + ε)).app F
  /-- The second composite is the double-shift transition. -/
  ψ_φ : ψ ≫ (rayShift C ε).map φ ≫ (rayCompIso C ε ε).hom.app G =
    (rayTransition C (ε + ε)).app G

namespace RaySheafInterleaving

variable {ε : ℝ≥0} {F G : raySpace.Sheaf C}

/-- Two witnesses agree when their two arrows agree. -/
@[ext]
theorem ext {i j : RaySheafInterleaving ε F G} (hφ : i.φ = j.φ) (hψ : i.ψ = j.ψ) : i = j := by
  cases i; cases j; cases hφ; cases hψ; rfl

/-- Interchange the two arrows. -/
def symm (i : RaySheafInterleaving ε F G) : RaySheafInterleaving ε G F :=
  ⟨i.ψ, i.φ, i.ψ_φ, i.φ_ψ⟩

/-- A sheaf is interleaved with itself by its transitions. -/
def refl (ε : ℝ≥0) (F : raySpace.Sheaf C) : RaySheafInterleaving ε F F :=
  ⟨(rayTransition C ε).app F, (rayTransition C ε).app F, rayTransition_add ε ε F,
    rayTransition_add ε ε F⟩

/-- Transport a witness along isomorphisms of both sheaves. -/
def congr {F' G' : raySpace.Sheaf C} (i : RaySheafInterleaving ε F G) (e : F ≅ F')
    (d : G ≅ G') : RaySheafInterleaving ε F' G' := by
  have comp {A B A' B' : raySpace.Sheaf C}
      (f : A ⟶ (rayShift C ε).obj B) (g : B ⟶ (rayShift C ε).obj A)
      (h : f ≫ (rayShift C ε).map g ≫ (rayCompIso C ε ε).hom.app A =
        (rayTransition C (ε + ε)).app A)
      (a : A ≅ A') (b : B ≅ B') :
      (a.inv ≫ f ≫ (rayShift C ε).map b.hom) ≫
        (rayShift C ε).map (b.inv ≫ g ≫ (rayShift C ε).map a.hom) ≫
          (rayCompIso C ε ε).hom.app A' = (rayTransition C (ε + ε)).app A' := by
    simp only [Functor.map_comp, Category.assoc]
    rw [← Functor.map_comp_assoc, b.hom_inv_id, (rayShift C ε).map_id, Category.id_comp]
    rw [rayCompIso_hom_naturality]
    have hh := congrArg (fun m => a.inv ≫ m ≫ (rayShift C (ε + ε)).map a.hom) h
    simp only [Category.assoc] at hh
    rw [hh, ← rayTransition_naturality, Iso.inv_hom_id_assoc]
  exact ⟨e.inv ≫ i.φ ≫ (rayShift C ε).map d.hom,
    d.inv ≫ i.ψ ≫ (rayShift C ε).map e.hom,
    comp i.φ i.ψ i.φ_ψ e d, comp i.ψ i.φ i.ψ_φ d e⟩

end RaySheafInterleaving

/-- The extended-infimum interleaving distance of sheaves on the ray space. -/
def raySheafInterleavingDistance (F G : raySpace.Sheaf C) : ℝ≥0∞ :=
  ⨅ (ε : ℝ≥0) (_ : Nonempty (RaySheafInterleaving ε F G)), (ε : ℝ≥0∞)

/-- Isomorphisms preserve the ray-sheaf distance in both arguments. -/
theorem raySheafInterleavingDistance_congr {F G F' G' : raySpace.Sheaf C} (e : F ≅ F')
    (d : G ≅ G') : raySheafInterleavingDistance F G = raySheafInterleavingDistance F' G' :=
  le_antisymm (le_iInf₂ fun ε ⟨i⟩ => iInf₂_le ε ⟨i.congr e.symm d.symm⟩)
    (le_iInf₂ fun ε ⟨i⟩ => iInf₂_le ε ⟨i.congr e d⟩)

/-- A sheaf witness on the upper Alexandrov line, pushed forward along `rayId`, is a ray-sheaf
witness at the same radius. -/
def RaySheafInterleaving.ofSheafInterleaving {ε : ℝ≥0} {F G : (upperSpace ℝ).Sheaf C}
    (i : SheafInterleaving ε F G) :
    RaySheafInterleaving ε ((TopCat.Sheaf.pushforward C rayId).obj F)
      ((TopCat.Sheaf.pushforward C rayId).obj G) where
  φ := (TopCat.Sheaf.pushforward C rayId).map i.φ
  ψ := (TopCat.Sheaf.pushforward C rayId).map i.ψ
  φ_ψ := by
    have h := (TopCat.Sheaf.pushforward C rayId).congr_map i.φ_ψ
    rwa [Functor.map_comp, Functor.map_comp, pushforward_map_sheafShift_map,
      pushforward_map_sheafCompIso, pushforward_map_sheafTransition] at h
  ψ_φ := by
    have h := (TopCat.Sheaf.pushforward C rayId).congr_map i.ψ_φ
    rwa [Functor.map_comp, Functor.map_comp, pushforward_map_sheafShift_map,
      pushforward_map_sheafCompIso, pushforward_map_sheafTransition] at h

end Interleaving

/-! ## Comparison with the real shift -/

section Comparison

variable (R : Type u) [Ring R]

/-- The comparison `S ε ⋙ B ≅ B ⋙ RealShift.shift ε`: at `F` and `t`, the restriction along
the equality `(t, ∞) + ε = (t + ε, ∞)`. -/
def rayShiftComparison (ε : ℝ≥0) :
    rayShift (ModuleCat.{0} R) ε ⋙ rayB (ModuleCat.{0} R) ≅
      rayB (ModuleCat.{0} R) ⋙ RealShift.shift ε :=
  NatIso.ofComponents
    (fun F => NatIso.ofComponents
      (fun t => TDA.Sheaf.restrictIso F.presheaf (map_rayTranslate_ray ε t))
      (fun _ => by
        change F.presheaf.map _ ≫ F.presheaf.map _ = F.presheaf.map _ ≫ F.presheaf.map _
        exact presheaf_map_comp_map_eq _ _ _ _ _))
    (fun φ => by
      apply NatTrans.ext
      funext t
      exact (φ.hom.naturality _).symm)

variable {R}

@[simp]
theorem rayShiftComparison_hom_app_app (ε : ℝ≥0) (F : raySpace.Sheaf (ModuleCat.{0} R))
    (t : ℝ) :
    ((rayShiftComparison R ε).hom.app F).app t =
      F.presheaf.map (homOfLE (map_rayTranslate_ray ε t).ge).op :=
  rfl

/-- Naturality of the comparison in the sheaf. -/
@[reassoc]
theorem rayShiftComparison_hom_naturality (ε : ℝ≥0) {F G : raySpace.Sheaf (ModuleCat.{0} R)}
    (φ : F ⟶ G) :
    (rayB _).map ((rayShift _ ε).map φ) ≫ (rayShiftComparison R ε).hom.app G =
      (rayShiftComparison R ε).hom.app F ≫ (RealShift.shift ε).map ((rayB _).map φ) :=
  (rayShiftComparison R ε).hom.naturality φ

/-- The comparison carries the ray-sheaf transition to `RealShift.transition`. -/
@[reassoc]
theorem rayShiftComparison_transition (ε : ℝ≥0) (F : raySpace.Sheaf (ModuleCat.{0} R)) :
    (rayB _).map ((rayTransition _ ε).app F) ≫ (rayShiftComparison R ε).hom.app F =
      RealShift.transition ε ((rayB _).obj F) := by
  apply NatTrans.ext
  funext t
  exact presheaf_map_comp_map _ _ _ _

/-- The comparison carries the ray-sheaf addition isomorphism to `RealShift.compIso`. -/
@[reassoc]
theorem rayShiftComparison_compIso (ε δ : ℝ≥0) (F : raySpace.Sheaf (ModuleCat.{0} R)) :
    (rayB _).map ((rayCompIso _ ε δ).hom.app F) ≫ (rayShiftComparison R (ε + δ)).hom.app F =
      (rayShiftComparison R ε).hom.app ((rayShift _ δ).obj F) ≫
        (RealShift.shift ε).map ((rayShiftComparison R δ).hom.app F) ≫
          (RealShift.compIso ε δ ((rayB _).obj F)).hom := by
  apply NatTrans.ext
  funext t
  change F.presheaf.map _ ≫ F.presheaf.map _ =
    F.presheaf.map _ ≫ F.presheaf.map _ ≫ F.presheaf.map _
  exact presheaf_map_comp_map_eq_comp _ _ _ _ _ _

variable {ε : ℝ≥0}

/-- Under `B` and the comparison, the ray-sheaf double-shift composite becomes the module
one. -/
theorem rayB_map_doubleShift {F G : raySpace.Sheaf (ModuleCat.{0} R)}
    (f : F ⟶ (rayShift _ ε).obj G) (g : G ⟶ (rayShift _ ε).obj F) :
    (rayB _).map (f ≫ (rayShift _ ε).map g ≫ (rayCompIso _ ε ε).hom.app F) ≫
        (rayShiftComparison R (ε + ε)).hom.app F =
      ((rayB _).map f ≫ (rayShiftComparison R ε).hom.app G) ≫
        (RealShift.shift ε).map ((rayB _).map g ≫ (rayShiftComparison R ε).hom.app F) ≫
          (RealShift.compIso ε ε ((rayB _).obj F)).hom := by
  simp only [Functor.map_comp, Category.assoc]
  rw [rayShiftComparison_compIso, rayShiftComparison_hom_naturality_assoc]

/-- `B` is nonexpansive: a ray-sheaf witness gives a real witness of the values on rays, at the
same radius. -/
def RaySheafInterleaving.toRealInterleaving {F G : raySpace.Sheaf (ModuleCat.{0} R)}
    (i : RaySheafInterleaving ε F G) :
    RealInterleaving ε ((rayB _).obj F) ((rayB _).obj G) where
  φ := (rayB _).map i.φ ≫ (rayShiftComparison R ε).hom.app G
  ψ := (rayB _).map i.ψ ≫ (rayShiftComparison R ε).hom.app F
  φ_ψ := by
    rw [← rayB_map_doubleShift, i.φ_ψ, rayShiftComparison_transition]
  ψ_φ := by
    rw [← rayB_map_doubleShift, i.ψ_φ, rayShiftComparison_transition]

/-- `Q` is nonexpansive: a real witness of `M` and `N` gives a ray-sheaf witness of `Q M` and
`Q N` at the same radius, through `SheafInterleaving.equivRealInterleaving` and pushforward along
`rayId`. -/
def RaySheafInterleaving.ofRealInterleaving {M N : PModule.{u,0,0} R ℝ}
    (i : RealInterleaving ε M N) :
    RaySheafInterleaving ε ((rayQ _).obj M) ((rayQ _).obj N) :=
  RaySheafInterleaving.ofSheafInterleaving
    (SheafInterleaving.equivRealInterleaving.symm
      (i.congr ((upperSetEquivalence ℝ _).unitIso.app M)
        ((upperSetEquivalence ℝ _).unitIso.app N)))

end Comparison

/-! ## Positive-radius interleavings of `M` and `BQ(M)` -/

section UnitInterleaving

variable {R : Type u} [Ring R]

/-- For `ε > 0`, the reverse arrow `BQ(M) ⟶ S ε M`: at `t`, the projection to `M(t + ε)`. -/
def unitInterleavingψ (M : PModule.{u,0,0} R ℝ) {ε : ℝ≥0} (hε : 0 < ε) :
    (rayB _).obj ((rayQ _).obj M) ⟶ (RealShift.shift ε).obj M where
  app t := rayProj M (lt_add_of_pos_right t (NNReal.coe_pos.2 hε))
  naturality _ _ f := (map_rayProj M f _).trans (rayProj_comp_map M _ _).symm

@[simp]
theorem unitInterleavingψ_app (M : PModule.{u,0,0} R ℝ) {ε : ℝ≥0} (hε : 0 < ε) (t : ℝ) :
    (unitInterleavingψ M hε).app t = rayProj M (lt_add_of_pos_right t (NNReal.coe_pos.2 hε)) :=
  rfl

/-- For `ε > 0`, an actual `ε`-interleaving of `M` and `BQ(M)`: the forward arrow at `t` is
`M(t ≤ t + ε)` followed by the unit at `t + ε`, and the reverse arrow is the projection from
`BQ(M)(t)` to `M(t + ε)`. The first composite is checked on `M`, the second after projecting
at every `s > t + 2ε`. -/
def unitInterleaving (M : PModule.{u,0,0} R ℝ) {ε : ℝ≥0} (hε : 0 < ε) :
    RealInterleaving ε M ((rayB _).obj ((rayQ _).obj M)) :=
  RealInterleaving.ofApp
    (RealShift.transition ε M ≫ (RealShift.shift ε).map ((rayUnit _).app M))
    (unitInterleavingψ M hε)
    (fun t => by
      change M.map _ ≫ ((rayUnit _).app M).app (t + ε) ≫ rayProj M _ ≫ M.map _ = M.map _
      exact (congrArg (M.map _ ≫ ·) (rayUnit_app_app_rayProj_assoc M _ _)).trans
        ((congrArg (M.map _ ≫ ·) (M.map_comp _ _).symm).trans (M.map_comp _ _).symm))
    (fun t => rayProj_ext M fun s hs => by
      change (rayProj M _ ≫ M.map _ ≫ ((rayUnit _).app M).app (t + ε + ε) ≫
        ((rayB _).obj ((rayQ _).obj M)).map _) ≫ rayProj M hs =
          ((rayB _).obj ((rayQ _).obj M)).map _ ≫ rayProj M hs
      refine Eq.trans ?_ (map_rayProj M _ hs).symm
      refine (Category.assoc _ _ _).trans ?_
      refine (congrArg (rayProj M _ ≫ ·) ((Category.assoc _ _ _).trans
        (congrArg (M.map _ ≫ ·) ((Category.assoc _ _ _).trans
          (congrArg (((rayUnit _).app M).app (t + ε + ε) ≫ ·) (map_rayProj M _ hs)))))).trans ?_
      refine (congrArg (rayProj M _ ≫ ·) (congrArg (M.map _ ≫ ·)
        (rayUnit_app_app_rayProj M _))).trans ?_
      exact (rayProj_comp_map_assoc M _ _ _).trans (rayProj_comp_map M _ _))

@[simp]
theorem unitInterleaving_φ_app (M : PModule.{u,0,0} R ℝ) {ε : ℝ≥0} (hε : 0 < ε) (t : ℝ) :
    (unitInterleaving M hε).φ.app t =
      M.map (homOfLE (le_add_of_nonneg_right ε.coe_nonneg)) ≫
        ((rayUnit _).app M).app (t + ε) :=
  rfl

@[simp]
theorem unitInterleaving_ψ (M : PModule.{u,0,0} R ℝ) {ε : ℝ≥0} (hε : 0 < ε) :
    (unitInterleaving M hε).ψ = unitInterleavingψ M hε :=
  rfl

/-- `M` and `BQ(M)` are at real interleaving distance zero. -/
theorem realInterleavingDistance_rayB_rayQ (M : PModule.{u,0,0} R ℝ) :
    realInterleavingDistance M ((rayB _).obj ((rayQ _).obj M)) = 0 :=
  realInterleavingDistance_eq_zero_iff.2 fun _ hε => ⟨unitInterleaving M hε⟩

end UnitInterleaving

/-! ## Extended distances -/

section Distance

variable {R : Type u} [Ring R]

/-- `B` does not increase distances. -/
theorem realInterleavingDistance_rayB_le (F G : raySpace.Sheaf (ModuleCat.{0} R)) :
    realInterleavingDistance ((rayB _).obj F) ((rayB _).obj G) ≤
      raySheafInterleavingDistance F G :=
  le_iInf₂ fun _ ⟨i⟩ => i.toRealInterleaving.distance_le

/-- `Q` does not increase distances. -/
theorem raySheafInterleavingDistance_rayQ_le (M N : PModule.{u,0,0} R ℝ) :
    raySheafInterleavingDistance ((rayQ _).obj M) ((rayQ _).obj N) ≤
      realInterleavingDistance M N :=
  le_iInf₂ fun ε ⟨i⟩ => iInf₂_le ε ⟨RaySheafInterleaving.ofRealInterleaving i⟩

/-- `Q` preserves extended distances: the real distance of `M` and `N` equals the ray-sheaf
distance of `Q M` and `Q N`. The lower bound replaces `M` and `N` by `BQ(M)` and `BQ(N)` at
distance zero. -/
theorem raySheafInterleavingDistance_rayQ (M N : PModule.{u,0,0} R ℝ) :
    raySheafInterleavingDistance ((rayQ _).obj M) ((rayQ _).obj N) =
      realInterleavingDistance M N := by
  refine le_antisymm (raySheafInterleavingDistance_rayQ_le M N) ?_
  calc realInterleavingDistance M N
      ≤ realInterleavingDistance M ((rayB _).obj ((rayQ _).obj M)) +
          (realInterleavingDistance ((rayB _).obj ((rayQ _).obj M))
              ((rayB _).obj ((rayQ _).obj N)) +
            realInterleavingDistance ((rayB _).obj ((rayQ _).obj N)) N) :=
        (realInterleavingDistance_triangle _ _ _).trans
          (add_le_add le_rfl (realInterleavingDistance_triangle _ _ _))
    _ = realInterleavingDistance ((rayB _).obj ((rayQ _).obj M))
          ((rayB _).obj ((rayQ _).obj N)) := by
        rw [realInterleavingDistance_rayB_rayQ, realInterleavingDistance_comm _ N,
          realInterleavingDistance_rayB_rayQ, zero_add, add_zero]
    _ ≤ raySheafInterleavingDistance ((rayQ _).obj M) ((rayQ _).obj N) :=
        realInterleavingDistance_rayB_le _ _

/-- `B` preserves extended distances: the ray-sheaf distance of `F` and `G` equals the real
distance of `B F` and `B G`, by `QB ≅ 𝟭`. -/
theorem realInterleavingDistance_rayB (F G : raySpace.Sheaf (ModuleCat.{0} R)) :
    realInterleavingDistance ((rayB _).obj F) ((rayB _).obj G) =
      raySheafInterleavingDistance F G := by
  refine le_antisymm (realInterleavingDistance_rayB_le F G) ?_
  exact (raySheafInterleavingDistance_congr ((rayCounitIso _).app F)
    ((rayCounitIso _).app G)).symm.trans_le (raySheafInterleavingDistance_rayQ_le _ _)

end Distance

/-! ## The kernel of `Q` -/

section Kernel

variable {R : Type u} [Ring R]

/-- A sheaf of modules on the ray space is zero exactly when its values on rays are. -/
theorem isZero_iff_isZero_rayB (F : raySpace.Sheaf (ModuleCat.{0} R)) :
    IsZero F ↔ IsZero ((rayB _).obj F) := by
  -- Zero morphisms of the full subcategory of sheaves, used only inside this proof.
  let _ : HasZeroMorphisms (raySpace.Sheaf (ModuleCat.{0} R)) :=
    inferInstanceAs (HasZeroMorphisms
      (CategoryTheory.Sheaf (Opens.grothendieckTopology raySpace) (ModuleCat.{0} R)))
  have : (rayB (ModuleCat.{0} R)).PreservesZeroMorphisms := ⟨fun _ _ => rfl⟩
  refine ⟨fun h => (rayB _).map_isZero h, fun h => ?_⟩
  rw [IsZero.iff_id_eq_zero] at h ⊢
  apply (rayB _).map_injective
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_zero, h]

/-- `Q M` is zero exactly when every strict map `M(s < t)` is zero. -/
theorem isZero_rayQ_iff (M : PModule.{u,0,0} R ℝ) :
    IsZero ((rayQ _).obj M) ↔ ∀ s t : ℝ, ∀ h : s < t, M.map (homOfLE h.le) = 0 := by
  rw [isZero_iff_isZero_rayB]
  constructor
  · intro hz s t h
    rw [← rayUnit_app_app_rayProj M h, ((Functor.isZero_iff _).1 hz s).eq_zero_of_tgt
      (((rayUnit _).app M).app s), zero_comp]
  · intro h
    refine Functor.isZero _ fun t => (IsZero.iff_id_eq_zero _).2 ?_
    refine rayProj_ext M fun s hs => ?_
    have hr : t < (t + s) / 2 := by linarith
    have hrs : (t + s) / 2 < s := by linarith
    rw [Category.id_comp, zero_comp, ← rayProj_comp_map M hr (homOfLE hrs.le), h _ _ hrs,
      comp_zero]

end Kernel

end

end TDA.Sheaf.RaySheaf
