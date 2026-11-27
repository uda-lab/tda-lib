import TDA.Sheaf.Alexandrov
import TDA.Sheaf.PresheafRestriction
import Mathlib.Topology.Sheaves.Functors
import Mathlib.Topology.Sheaves.SheafCondition.PairwiseIntersections

/-!
# Sheaves on a basis of opens indexed by points

Let `P : Type v` be a join-semilattice, `X : TopCat.{v}`, and let `S : StrictBasis P X` consist of a
continuous map `S.ι : upperSpace P ⟶ X` from the upper Alexandrov space of `P` and opens
`S.U p` of `X`, with `t ≤ s` whenever `ι s ∈ U t` (`S.Strict t s`, read "`t` is strictly below
`s`"), such that `U` is antitone, `U p ≤ V` for every open `V ∋ ι p`, every point of an open `V`
lies in some `U p` with `ι p ∈ V` (`S.exists_mem`), `U s ⊓ U t ≤ U (s ⊔ t)`, and `Strict`
interpolates. The open rays of `TDA.Sheaf.RaySheaf` and the open orthants of
`TDA.Sheaf.OrthantSheaf` are instances.

* `S.isBasis_U`: the opens `U p` form a basis of `X`; `S.iSup_U V` covers an open `V` by the
  `U p` at its points, the empty open by the empty family.
* `S.Q C : (P ⥤ C) ⥤ X.Sheaf C` is the Alexandrov sheaf `upperSetEquivalence P C` of
  `TDA.Sheaf.Alexandrov`, pushed forward along `S.ι`; `S.B C : X.Sheaf C ⥤ (P ⥤ C)` is
  `B(F)(t) = F(U t)` with the restrictions of `F`.
* `S.proj M h : BQ(M)(t) ⟶ M(s)` for `h : S.Strict t s` is the limit projection of the Kan
  extension at `↑s ⊆ ι⁻¹(U t)`; `S.coneIsLimit` and `S.limitIso` identify `BQ(M)(t)` with the
  limit of `M` over `{s // S.Strict t s}` (`S.diagram`), with the projection equations
  `limitIso_hom_π`, `proj_comp_map`, `map_proj`, `map_app_proj`, the lift `S.lift` and the
  extensionality `proj_ext`.
* `S.unit C : 𝟭 ⟶ S.Q C ⋙ S.B C` is the lift of the maps `M(t ≤ s)` (`unit_app_app_proj`).
* `S.counitIso C : S.B C ⋙ S.Q C ≅ 𝟭` is `QB ≅ 𝟭`, by the sheaf condition for the cover of an
  open `V` by the `U p` at its points, whose pairwise intersections lie in `U (p ⊔ q)`
  (`counitIso_inv_app_hom_app_proj`, `counitIso_hom_app_hom_app_map`); hence `S.B C` is
  faithful.

The value category is `C : Type u` with `[Category.{v} C]`, and `[HasLimits C]` for `Q`; the ray
and orthant bases are the case `v = 0`.
-/

set_option autoImplicit false

universe u v

open CategoryTheory Limits Opposite TopologicalSpace Topology TopCat

namespace TDA.Sheaf

open TDA.Sheaf.Alexandrov

/-- A basis of opens `U p` of a space `X` indexed by the points of a join-semilattice `P`,
together with the continuous map `ι` from the upper Alexandrov space of `P`. The relation
`ι s ∈ U t` is the strict order `StrictBasis.Strict t s`. -/
structure StrictBasis (P : Type v) [SemilatticeSup P] (X : TopCat.{v}) where
  /-- The continuous map from the upper Alexandrov space of `P`. -/
  ι : upperSpace P ⟶ X
  /-- The basic open at a point of `P`. -/
  U : P → Opens X
  /-- The basic opens are antitone. -/
  antitone {s t : P} : s ≤ t → U t ≤ U s
  /-- A point strictly above `t` is above `t`. -/
  le_of_mem {t s : P} : ι (WithUpperSet.toUpperSet s) ∈ U t → t ≤ s
  /-- The basic open at a point of an open is contained in that open. -/
  U_le {V : Opens X} {p : P} : ι (WithUpperSet.toUpperSet p) ∈ V → U p ≤ V
  /-- Every point of an open lies in the basic open at some point of that open. -/
  exists_mem {V : Opens X} {x : X} : x ∈ V → ∃ p : P, ι (WithUpperSet.toUpperSet p) ∈ V ∧ x ∈ U p
  /-- Two basic opens meet inside the basic open at the join. -/
  inf_le (s t : P) : U s ⊓ U t ≤ U (s ⊔ t)
  /-- The strict order interpolates. -/
  interpolate {t s : P} : ι (WithUpperSet.toUpperSet s) ∈ U t →
    ∃ m : P, ι (WithUpperSet.toUpperSet m) ∈ U t ∧ ι (WithUpperSet.toUpperSet s) ∈ U m

namespace StrictBasis

noncomputable section

variable {P : Type v} [SemilatticeSup P] {X : TopCat.{v}} (S : StrictBasis P X)

/-! ## The strict order and the basis -/

/-- `t` is strictly below `s`: the point `s` lies in the basic open at `t`. -/
def Strict (t s : P) : Prop :=
  S.ι (WithUpperSet.toUpperSet s) ∈ S.U t

variable {S}

theorem le_of_strict {t s : P} (h : S.Strict t s) : t ≤ s :=
  S.le_of_mem h

/-- Points of an open of `X`, read on `P`, form an upper set. -/
theorem mem_of_le {V : Opens X} {p q : P} (hp : S.ι (WithUpperSet.toUpperSet p) ∈ V)
    (h : p ≤ q) : S.ι (WithUpperSet.toUpperSet q) ∈ V :=
  Topology.IsUpperSet.isOpen_iff_isUpperSet.1 ((Opens.map S.ι).obj V).isOpen
    (show WithUpperSet.toUpperSet p ≤ WithUpperSet.toUpperSet q from h) hp

theorem strict_of_strict_of_le {t s s' : P} (h : S.Strict t s) (h' : s ≤ s') :
    S.Strict t s' :=
  mem_of_le h h'

theorem strict_of_le_of_strict {t t' s : P} (h : t ≤ t') (h' : S.Strict t' s) :
    S.Strict t s :=
  S.antitone h h'

/-- The strict order interpolates. -/
theorem exists_strict_strict {t s : P} (h : S.Strict t s) :
    ∃ m : P, S.Strict t m ∧ S.Strict m s :=
  S.interpolate h

variable (S)

/-- Every open is the union of the basic opens at its points; the empty open has the empty
cover. -/
theorem iSup_U (V : Opens X) :
    ⨆ i : {p : P // S.ι (WithUpperSet.toUpperSet p) ∈ V}, S.U i.1 = V := by
  apply le_antisymm
  · exact iSup_le fun i => S.U_le i.2
  · intro x hx
    obtain ⟨p, hp, hxp⟩ := S.exists_mem hx
    exact Opens.mem_iSup.2 ⟨⟨p, hp⟩, hxp⟩

/-- The basic opens form a basis of `X`. -/
theorem isBasis_U : Opens.IsBasis (Set.range S.U) := by
  rw [Opens.isBasis_iff_nbhd]
  intro V x hx
  obtain ⟨p, hp, hxp⟩ := S.exists_mem hx
  exact ⟨S.U p, ⟨p, rfl⟩, hxp, S.U_le hp⟩

/-- For `t` strictly below `s`, the principal open `↑s` lies in the preimage of `U t`. -/
theorem principalOpen_le_map_U {t s : P} (h : S.Strict t s) :
    _root_.Alexandrov.principalOpen (X := upperSpace P) (WithUpperSet.toUpperSet s) ≤
      (Opens.map S.ι).obj (S.U t) :=
  (_root_.Alexandrov.principalOpen_le_iff _).2 h

/-! ## The functors `Q` and `B` -/

section Functors

variable (C : Type u) [Category.{v} C]

/-- The basic opens as a functor `P ⥤ (Opens X)ᵒᵖ`. -/
def basisFunctor : P ⥤ (Opens X)ᵒᵖ where
  obj t := op (S.U t)
  map f := (homOfLE (S.antitone (leOfHom f))).op

/-- The functor `B`: `B(F)(t) = F(U t)`, with the restrictions of `F`. -/
def B : X.Sheaf C ⥤ (P ⥤ C) :=
  TopCat.Sheaf.forget C X ⋙ (Functor.whiskeringLeft P (Opens X)ᵒᵖ C).obj S.basisFunctor

variable {C}

@[simp]
theorem B_obj_obj (F : X.Sheaf C) (t : P) :
    ((S.B C).obj F).obj t = F.presheaf.obj (op (S.U t)) :=
  rfl

@[simp]
theorem B_obj_map (F : X.Sheaf C) {s t : P} (f : s ⟶ t) :
    ((S.B C).obj F).map f = F.presheaf.map (homOfLE (S.antitone (leOfHom f))).op :=
  rfl

@[simp]
theorem B_map_app {F G : X.Sheaf C} (φ : F ⟶ G) (t : P) :
    ((S.B C).map φ).app t = φ.hom.app (op (S.U t)) :=
  rfl

variable (C) [HasLimits C]

/-- The functor `Q`: the Alexandrov sheaf of a diagram, pushed forward along `ι`. -/
def Q : (P ⥤ C) ⥤ X.Sheaf C :=
  (upperSetEquivalence P C).functor ⋙ TopCat.Sheaf.pushforward C S.ι

variable {C}

/-- `Q(M)(V)` is the Alexandrov sheaf of `M` on the preimage of `V`. -/
theorem Q_obj_presheaf_obj (M : P ⥤ C) (V : Opens X) :
    ((S.Q C).obj M).presheaf.obj (op V) =
      ((upperSetEquivalence P C).functor.obj M).presheaf.obj (op ((Opens.map S.ι).obj V)) :=
  rfl

/-- `Q` on a morphism is the component of the Alexandrov sheaf map on the preimage. -/
theorem Q_map_hom_app {M N : P ⥤ C} (α : M ⟶ N) (V : Opens X) :
    ((S.Q C).map α).hom.app (op V) =
      ((upperSetEquivalence P C).functor.map α).hom.app (op ((Opens.map S.ι).obj V)) :=
  rfl

/-- The diagram over the principal opens contained in the preimage of `V` whose limit is the
value of `Q(M)` on `V`. -/
private abbrev kanDiagram (M : P ⥤ C) (V : Opens X) :=
  StructuredArrow.proj (op ((Opens.map S.ι).obj V))
      (_root_.Alexandrov.principals (upperSpace P)) ⋙
    (WithUpperSet.toUpperSetOrderIso (α := P)).symm.monotone.functor ⋙ M

/-- The index `↑s ⊆ ι⁻¹(U t)` of `kanDiagram`. -/
private abbrev kanIndex {t s : P} (h : S.Strict t s) :
    StructuredArrow (op ((Opens.map S.ι).obj (S.U t)))
      (_root_.Alexandrov.principals (upperSpace P)) :=
  StructuredArrow.mk (homOfLE (S.principalOpen_le_map_U h)).op

/-- A principal open `↑p` contained in the preimage of an open `V` has `ι p ∈ V`. -/
private theorem mem_of_kanIndex {V : Opens X}
    (j : StructuredArrow (op ((Opens.map S.ι).obj V))
      (_root_.Alexandrov.principals (upperSpace P))) :
    S.ι (WithUpperSet.toUpperSet (WithUpperSet.ofUpperSet (α := P) j.right)) ∈ V :=
  (_root_.Alexandrov.principalOpen_le_iff (X := upperSpace P) _).1 j.hom.unop.le

/-! ## Values of `BQ(M)` as limits -/

/-- The projection `BQ(M)(t) ⟶ M(s)` for `t` strictly below `s`: the limit projection of the
Kan extension at the principal open `↑s ⊆ ι⁻¹(U t)`. -/
def proj (M : P ⥤ C) {t s : P} (h : S.Strict t s) :
    ((S.B C).obj ((S.Q C).obj M)).obj t ⟶ M.obj s :=
  limit.π (S.kanDiagram M (S.U t)) (S.kanIndex h)

/-- Projections are compatible with the maps of `M`. -/
@[reassoc]
theorem proj_comp_map (M : P ⥤ C) {t s s' : P} (h : S.Strict t s) (f : s ⟶ s') :
    S.proj M h ≫ M.map f = S.proj M (strict_of_strict_of_le h (leOfHom f)) :=
  limit.w (S.kanDiagram M (S.U t)) (StructuredArrow.homMk (homOfLE (leOfHom f)) rfl :
    S.kanIndex h ⟶ S.kanIndex (strict_of_strict_of_le h (leOfHom f)))

/-- A restriction of `Q(M)` followed by a limit projection is the projection at the same
principal open. -/
private theorem kan_map_π (M : P ⥤ C) {V W : Opens X} (h : W ≤ V)
    (j : StructuredArrow (op ((Opens.map S.ι).obj W))
      (_root_.Alexandrov.principals (upperSpace P))) :
    ((S.Q C).obj M).presheaf.map (homOfLE h).op ≫ limit.π (S.kanDiagram M W) j =
      limit.π (S.kanDiagram M V)
        ((StructuredArrow.map ((Opens.map S.ι).op.map (homOfLE h).op)).obj j) := by
  change ((_root_.Alexandrov.principals (upperSpace P)).pointwiseRightKanExtension
      ((WithUpperSet.toUpperSetOrderIso (α := P)).symm.monotone.functor ⋙ M)).map
        ((Opens.map S.ι).op.map (homOfLE h).op) ≫ limit.π (S.kanDiagram M W) j = _
  -- `erw`: the Kan-extension value is the limit over `kanDiagram` only up to unfolding.
  erw [Functor.pointwiseRightKanExtension_map, limit.lift_π]
  rfl

/-- Projections are compatible with the maps of `BQ(M)`. -/
@[reassoc]
theorem map_proj (M : P ⥤ C) {t t' s : P} (f : t ⟶ t') (h : S.Strict t' s) :
    ((S.B C).obj ((S.Q C).obj M)).map f ≫ S.proj M h =
      S.proj M (strict_of_le_of_strict (leOfHom f) h) :=
  S.kan_map_π M (S.antitone (leOfHom f)) (S.kanIndex h)

/-- Two maps into `BQ(M)(t)` agree when all their projections agree. -/
theorem proj_ext (M : P ⥤ C) {t : P} {Y : C}
    {f g : Y ⟶ ((S.B C).obj ((S.Q C).obj M)).obj t}
    (h : ∀ (s : P) (hs : S.Strict t s), f ≫ S.proj M hs = g ≫ S.proj M hs) : f = g := by
  refine limit.hom_ext (F := S.kanDiagram M (S.U t)) fun j => ?_
  obtain ⟨⟨⟨⟩⟩, p, j⟩ := j
  exact h (WithUpperSet.ofUpperSet (α := P) p)
    ((_root_.Alexandrov.principalOpen_le_iff (X := upperSpace P) _).1 j.unop.le)

/-- The projections commute with `Q` and `B` applied to a morphism. -/
@[reassoc]
theorem map_app_proj {M N : P ⥤ C} (α : M ⟶ N) {t s : P} (h : S.Strict t s) :
    ((S.B C).map ((S.Q C).map α)).app t ≫ S.proj N h = S.proj M h ≫ α.app s :=
  kanSheaf_map_hom_app_π (X := upperSpace P) (C := C)
    (Functor.whiskerLeft (WithUpperSet.toUpperSetOrderIso (α := P)).symm.monotone.functor α)
    (op ((Opens.map S.ι).obj (S.U t))) (S.kanIndex h)

/-- The diagram `s ↦ M(s)` on the points strictly above `t`. -/
def diagram (M : P ⥤ C) (t : P) : {s : P // S.Strict t s} ⥤ C :=
  (show Monotone (Subtype.val : {s : P // S.Strict t s} → P) from fun _ _ h => h).functor ⋙ M

omit [HasLimits C] in
@[simp]
theorem diagram_obj (M : P ⥤ C) (t : P) (s : {s : P // S.Strict t s}) :
    (S.diagram M t).obj s = M.obj s :=
  rfl

/-- The cone of projections from `BQ(M)(t)` over `s ↦ M(s)` on the points strictly above
`t`. -/
@[simps]
def cone (M : P ⥤ C) (t : P) : Cone (S.diagram M t) where
  pt := ((S.B C).obj ((S.Q C).obj M)).obj t
  π :=
    { app := fun s => S.proj M s.2
      naturality := fun s _ _ => (Category.id_comp _).trans (S.proj_comp_map M s.2 _).symm }

/-- `BQ(M)(t)` is the limit of `s ↦ M(s)` over the points strictly above `t`, with the
projections `proj`. -/
def coneIsLimit (M : P ⥤ C) (t : P) : IsLimit (S.cone M t) where
  lift c := limit.lift (S.kanDiagram M (S.U t))
    { pt := c.pt
      π :=
        { app := fun j => c.π.app ⟨WithUpperSet.ofUpperSet (α := P) j.right, S.mem_of_kanIndex j⟩
          naturality := fun j j' g => (Category.id_comp _).trans
            (c.w (homOfLE (leOfHom g.right) :
              (⟨_, S.mem_of_kanIndex j⟩ : {s : P // S.Strict t s}) ⟶
                ⟨_, S.mem_of_kanIndex j'⟩)).symm } }
  fac c s := limit.lift_π _ (S.kanIndex s.2)
  uniq c m hm := S.proj_ext M fun s hs => by
    refine (hm ⟨s, hs⟩).trans ?_
    change _ = _ ≫ limit.π (S.kanDiagram M (S.U t)) (S.kanIndex hs)
    rw [limit.lift_π]
    rfl

/-- The comparison of `BQ(M)(t)` with the limit of `M` over the points strictly above `t`. -/
def limitIso (M : P ⥤ C) (t : P) :
    ((S.B C).obj ((S.Q C).obj M)).obj t ≅ limit (S.diagram M t) :=
  (S.coneIsLimit M t).conePointUniqueUpToIso (limit.isLimit _)

@[reassoc (attr := simp)]
theorem limitIso_hom_π (M : P ⥤ C) (t : P) (s : {s : P // S.Strict t s}) :
    (S.limitIso M t).hom ≫ limit.π (S.diagram M t) s = S.proj M s.2 :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ s

@[reassoc (attr := simp)]
theorem limitIso_inv_proj (M : P ⥤ C) (t : P) (s : {s : P // S.Strict t s}) :
    (S.limitIso M t).inv ≫ S.proj M s.2 = limit.π (S.diagram M t) s :=
  IsLimit.conePointUniqueUpToIso_inv_comp _ _ s

/-- A family of maps `Y ⟶ M(s)` for `s` strictly above `t`, compatible with the maps of `M`,
lifts to `Y ⟶ BQ(M)(t)`. -/
def lift (M : P ⥤ C) {t : P} {Y : C} (f : ∀ s : P, S.Strict t s → (Y ⟶ M.obj s))
    (hf : ∀ (s s' : P) (hs : S.Strict t s) (h : s ≤ s'),
      f s hs ≫ M.map (homOfLE h) = f s' (strict_of_strict_of_le hs h)) :
    Y ⟶ ((S.B C).obj ((S.Q C).obj M)).obj t :=
  (S.coneIsLimit M t).lift
    { pt := Y
      π :=
        { app := fun s => f s.1 s.2
          naturality := fun s s' g =>
            (Category.id_comp _).trans (hf s.1 s'.1 s.2 (leOfHom g)).symm } }

@[reassoc (attr := simp)]
theorem lift_proj (M : P ⥤ C) {t : P} {Y : C} (f : ∀ s : P, S.Strict t s → (Y ⟶ M.obj s))
    (hf : ∀ (s s' : P) (hs : S.Strict t s) (h : s ≤ s'),
      f s hs ≫ M.map (homOfLE h) = f s' (strict_of_strict_of_le hs h)) {s : P}
    (hs : S.Strict t s) :
    S.lift M f hf ≫ S.proj M hs = f s hs :=
  (S.coneIsLimit M t).fac _ ⟨s, hs⟩

/-! ## The unit -/

omit [HasLimits C] in
/-- The maps `M(t ≤ s)` for `s` strictly above `t` are compatible with the maps of `M`. -/
private theorem unit_compat (M : P ⥤ C) (t : P) (s s' : P) (hs : S.Strict t s) (h : s ≤ s') :
    M.map (homOfLE (le_of_strict hs)) ≫ M.map (homOfLE h) =
      M.map (homOfLE (le_of_strict (strict_of_strict_of_le hs h))) := by
  rw [← M.map_comp]
  rfl

variable (C)

/-- The unit `η : M ⟶ BQ(M)`: at `t`, the lift of the maps `M(t ≤ s)` for `s` strictly above
`t`. -/
def unit : 𝟭 (P ⥤ C) ⟶ S.Q C ⋙ S.B C where
  app M :=
    { app := fun t => S.lift M (fun _ hs => M.map (homOfLE (le_of_strict hs))) (S.unit_compat M t)
      naturality := fun t t' f => S.proj_ext M fun _ hs => by
        simp only [Functor.id_obj, Functor.comp_obj, Category.assoc, lift_proj,
          map_proj, ← M.map_comp]
        rfl }
  naturality M N α := by
    ext t
    exact S.proj_ext N fun _ hs => by
      simp only [Functor.id_obj, Functor.comp_obj, Functor.id_map, NatTrans.comp_app,
        Functor.comp_map, Category.assoc, lift_proj, map_app_proj, lift_proj_assoc]
      exact (α.naturality _).symm

variable {C}

/-- The unit followed by a projection is the map of `M`. -/
@[reassoc (attr := simp)]
theorem unit_app_app_proj (M : P ⥤ C) {t s : P} (h : S.Strict t s) :
    ((S.unit C).app M).app t ≫ S.proj M h = M.map (homOfLE (le_of_strict h)) :=
  S.lift_proj M (fun _ hs => M.map (homOfLE (le_of_strict hs))) (S.unit_compat M t) h

end Functors

/-! ## `QB ≅ 𝟭` by the basic cover -/

section Counit

variable {C : Type u} [Category.{v} C] [HasLimits C]

/-- The cone of restrictions `F(V) ⟶ F(U p)` over the basic opens at the points `p` of `V`. -/
private def restrictionCone (F : X.Sheaf C) (V : Opens X) :
    Cone (S.kanDiagram ((S.B C).obj F) V) where
  pt := F.presheaf.obj (op V)
  π :=
    { app := fun j => F.presheaf.map (homOfLE (S.U_le (S.mem_of_kanIndex j))).op
      naturality := fun _ _ _ =>
        (Category.id_comp _).trans (presheaf_map_comp_map F.presheaf _ _ _).symm }

/-- The index of the basic open at a point `p` of `V`. -/
private abbrev pointIndex {V : Opens X} (i : {p : P // S.ι (WithUpperSet.toUpperSet p) ∈ V}) :
    StructuredArrow (op ((Opens.map S.ι).obj V)) (_root_.Alexandrov.principals (upperSpace P)) :=
  StructuredArrow.mk (homOfLE ((_root_.Alexandrov.principalOpen_le_iff (X := upperSpace P)
    (x := WithUpperSet.toUpperSet i.1) _).2 i.2)).op

omit [HasLimits C] in
/-- On the intersection of two basic opens, the restrictions of a cone agree: both factor
through the basic open at the join. -/
private theorem cone_inf (F : X.Sheaf C) {V : Opens X}
    (s : Cone (S.kanDiagram ((S.B C).obj F) V))
    (i j : {p : P // S.ι (WithUpperSet.toUpperSet p) ∈ V}) :
    s.π.app (S.pointIndex i) ≫
        F.presheaf.map (homOfLE (inf_le_left : S.U i.1 ⊓ S.U j.1 ≤ S.U i.1)).op =
      s.π.app (S.pointIndex j) ≫ F.presheaf.map (homOfLE inf_le_right).op := by
  have hk : S.ι (WithUpperSet.toUpperSet (α := P) (i.1 ⊔ j.1)) ∈ V := mem_of_le i.2 le_sup_left
  have hi := s.w (StructuredArrow.homMk (homOfLE (show WithUpperSet.toUpperSet i.1 ≤
      WithUpperSet.toUpperSet (α := P) (i.1 ⊔ j.1) from (le_sup_left : i.1 ≤ i.1 ⊔ j.1))) rfl :
    S.pointIndex i ⟶ S.pointIndex ⟨_, hk⟩)
  have hj := s.w (StructuredArrow.homMk (homOfLE (show WithUpperSet.toUpperSet j.1 ≤
      WithUpperSet.toUpperSet (α := P) (i.1 ⊔ j.1) from (le_sup_right : j.1 ≤ i.1 ⊔ j.1))) rfl :
    S.pointIndex j ⟶ S.pointIndex ⟨_, hk⟩)
  have hle : S.U i.1 ⊓ S.U j.1 ≤ S.U (i.1 ⊔ j.1) := S.inf_le _ _
  have key : s.π.app (S.pointIndex i) ≫
        F.presheaf.map (homOfLE (S.antitone (le_sup_left : i.1 ≤ i.1 ⊔ j.1))).op =
      s.π.app (S.pointIndex j) ≫
        F.presheaf.map (homOfLE (S.antitone (le_sup_right : j.1 ≤ i.1 ⊔ j.1))).op :=
    hi.trans hj.symm
  refine (congrArg (s.π.app (S.pointIndex i) ≫ ·) (presheaf_map_comp_map F.presheaf
    (homOfLE (S.antitone (le_sup_left : i.1 ≤ i.1 ⊔ j.1))).op (homOfLE hle).op _).symm).trans ?_
  refine Eq.trans ?_ (congrArg (s.π.app (S.pointIndex j) ≫ ·) (presheaf_map_comp_map F.presheaf
    (homOfLE (S.antitone (le_sup_right : j.1 ≤ i.1 ⊔ j.1))).op (homOfLE hle).op _))
  refine (Category.assoc _ _ _).symm.trans (Eq.trans ?_ (Category.assoc _ _ _))
  exact congrArg (· ≫ F.presheaf.map (homOfLE hle).op) key

/-- The components of the cone over the pairwise intersections of the basic cover. -/
private def pairApp (F : X.Sheaf C) {V : Opens X}
    (s : Cone (S.kanDiagram ((S.B C).obj F) V)) :
    ∀ o : Pairwise {p : P // S.ι (WithUpperSet.toUpperSet p) ∈ V},
      s.pt ⟶ F.presheaf.obj (op ((Pairwise.diagram
        fun i : {p : P // S.ι (WithUpperSet.toUpperSet p) ∈ V} => S.U i.1).obj o))
  | .single i => s.π.app (S.pointIndex i)
  | .pair i _ => s.π.app (S.pointIndex i) ≫ F.presheaf.map (homOfLE inf_le_left).op

/-- A cone over the basic diagram of `V` gives a cone over the pairwise intersections of the
basic cover of `V`. -/
private def pairCone (F : X.Sheaf C) {V : Opens X}
    (s : Cone (S.kanDiagram ((S.B C).obj F) V)) :
    Cone ((Pairwise.diagram fun i : {p : P // S.ι (WithUpperSet.toUpperSet p) ∈ V} =>
      S.U i.1).op ⋙ F.presheaf) where
  pt := s.pt
  π :=
    { app := fun o => S.pairApp F s o.unop
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
        | right i j => exact S.cone_inf F s i j }

/-- The restrictions of a sheaf on `X` to the basic opens at the points of `V` form a limit
cone: by the sheaf condition for the basic cover, whose pairwise intersections lie in basic
opens. -/
private def restrictionConeIsLimit (F : X.Sheaf C) (V : Opens X) :
    IsLimit (S.restrictionCone F V) :=
  let P' := (TopCat.Presheaf.IsSheaf.isSheafPairwiseIntersections (F := F.presheaf)
    (U := fun i : {p : P // S.ι (WithUpperSet.toUpperSet p) ∈ V} => S.U i.1) F.property).some
  { lift := fun s => P'.lift (S.pairCone F s) ≫ F.presheaf.map (homOfLE (S.iSup_U V).ge).op
    fac := fun s j => by
      obtain ⟨⟨⟨⟩⟩, p, hj⟩ := j
      have h := P'.fac (S.pairCone F s)
        (op (Pairwise.single ⟨WithUpperSet.ofUpperSet (α := P) p,
          S.mem_of_kanIndex ⟨_, p, hj⟩⟩))
      refine Eq.trans ?_ h
      refine (Category.assoc _ _ _).trans ?_
      exact congrArg (P'.lift (S.pairCone F s) ≫ ·) (presheaf_map_comp_map F.presheaf _ _ _)
    uniq := fun s m hm => by
      have h1 : m ≫ F.presheaf.map (homOfLE (S.iSup_U V).le).op = P'.lift (S.pairCone F s) := by
        refine P'.uniq (S.pairCone F s) _ fun o => ?_
        obtain ⟨o⟩ := o
        cases o with
        | single i =>
          refine Eq.trans ?_ (hm (S.pointIndex i))
          refine (Category.assoc _ _ _).trans ?_
          exact congrArg (m ≫ ·) (presheaf_map_comp_map F.presheaf _ _ _)
        | pair i j =>
          refine Eq.trans ?_
            (congrArg (· ≫ F.presheaf.map (homOfLE inf_le_left).op) (hm (S.pointIndex i)))
          refine (Category.assoc _ _ _).trans (Eq.trans ?_ (Category.assoc _ _ _).symm)
          exact congrArg (m ≫ ·) ((presheaf_map_comp_map F.presheaf _ _
            (homOfLE (inf_le_left.trans (S.U_le i.2) : S.U i.1 ⊓ S.U j.1 ≤ V)).op).trans
              (presheaf_map_comp_map F.presheaf _ _ _).symm)
      refine Eq.trans ?_ (congrArg (· ≫ F.presheaf.map (homOfLE (S.iSup_U V).ge).op) h1)
      refine Eq.trans ?_ (Category.assoc _ _ _).symm
      refine Eq.trans (Category.comp_id m).symm (congrArg (m ≫ ·) ?_)
      exact (F.presheaf.map_id _).symm.trans (presheaf_map_comp_map F.presheaf _ _ _).symm }

/-- The comparison `F(V) ⟶ Q(B F)(V)`: the lift of the restrictions to the basic opens in
`V`. -/
private abbrev counitApp (F : X.Sheaf C) (V : Opens X) :
    F.presheaf.obj (op V) ⟶ ((S.Q C).obj ((S.B C).obj F)).presheaf.obj (op V) :=
  limit.lift (S.kanDiagram ((S.B C).obj F) V) (S.restrictionCone F V)

private theorem counitApp_π (F : X.Sheaf C) (V : Opens X)
    (j : StructuredArrow (op ((Opens.map S.ι).obj V))
      (_root_.Alexandrov.principals (upperSpace P))) :
    S.counitApp F V ≫ limit.π (S.kanDiagram ((S.B C).obj F) V) j =
      F.presheaf.map (homOfLE (S.U_le (S.mem_of_kanIndex j))).op :=
  limit.lift_π _ _

/-- The comparison `F(V) ≅ Q(B F)(V)`, as a natural isomorphism of presheaves. -/
private def counitPresheafIso (F : X.Sheaf C) :
    F.presheaf ≅ ((S.Q C).obj ((S.B C).obj F)).presheaf :=
  NatIso.ofComponents
    (fun V => (S.restrictionConeIsLimit F V.unop).conePointUniqueUpToIso (limit.isLimit _))
    (fun {V W} f => by
      obtain ⟨V⟩ := V
      obtain ⟨W⟩ := W
      obtain ⟨⟨⟨hf⟩⟩⟩ := f
      change F.presheaf.map (homOfLE hf).op ≫ S.counitApp F W =
        S.counitApp F V ≫ ((S.Q C).obj ((S.B C).obj F)).presheaf.map (homOfLE hf).op
      refine limit.hom_ext (F := S.kanDiagram ((S.B C).obj F) W) fun j => ?_
      refine (Category.assoc _ _ _).trans
        ((congrArg (F.presheaf.map (homOfLE hf).op ≫ ·) (S.counitApp_π F W j)).trans ?_)
      refine Eq.trans ?_ (Category.assoc _ _ _).symm
      refine Eq.trans ?_ (congrArg (S.counitApp F V ≫ ·) (S.kan_map_π _ hf j).symm)
      refine Eq.trans ?_ (S.counitApp_π F V
        ((StructuredArrow.map ((Opens.map S.ι).op.map (homOfLE hf).op)).obj j)).symm
      exact presheaf_map_comp_map _ _ _ _)

variable (C)

/-- `QB ≅ 𝟭`: a sheaf `F` on `X` is recovered from its values on basic opens. On an open `V`,
the inverse compares `F(V)` with the limit of `F(U p)` over the points `p` of `V`, by
restriction; it is invertible by the sheaf condition for the basic cover of `V`. -/
def counitIso : S.B C ⋙ S.Q C ≅ 𝟭 (X.Sheaf C) :=
  (NatIso.ofComponents (fun F => ObjectProperty.isoMk _ (S.counitPresheafIso F))
    (fun {F G} φ => by
      apply CategoryTheory.Sheaf.hom_ext
      ext V
      obtain ⟨V⟩ := V
      change φ.hom.app (op V) ≫ S.counitApp G V =
        S.counitApp F V ≫ ((S.Q C).map ((S.B C).map φ)).hom.app (op V)
      refine limit.hom_ext (F := S.kanDiagram ((S.B C).obj G) V) fun j => ?_
      refine (Category.assoc _ _ _).trans
        ((congrArg (φ.hom.app (op V) ≫ ·) (S.counitApp_π G V j)).trans ?_)
      refine Eq.trans ?_ (Category.assoc _ _ _).symm
      refine Eq.trans ?_ (congrArg (S.counitApp F V ≫ ·) (kanSheaf_map_hom_app_π
        (X := upperSpace P) (C := C)
        (Functor.whiskerLeft (WithUpperSet.toUpperSetOrderIso (α := P)).symm.monotone.functor
          ((S.B C).map φ)) (op ((Opens.map S.ι).obj V)) j).symm)
      refine Eq.trans ?_ (Category.assoc _ _ _)
      refine Eq.trans ?_ (congrArg (· ≫ _) (S.counitApp_π F V j).symm)
      exact (φ.hom.naturality _).symm)).symm

variable {C}

/-- On a basic open, the inverse of the counit followed by a projection is the restriction of
`F`. -/
@[reassoc (attr := simp)]
theorem counitIso_inv_app_hom_app_proj (F : X.Sheaf C) {t s : P} (h : S.Strict t s) :
    ((S.counitIso C).inv.app F).hom.app (op (S.U t)) ≫ S.proj ((S.B C).obj F) h =
      F.presheaf.map (homOfLE (S.antitone (le_of_strict h))).op :=
  S.counitApp_π F (S.U t) (S.kanIndex h)

/-- On a basic open, the counit followed by a restriction of `F` is the projection. -/
@[reassoc (attr := simp)]
theorem counitIso_hom_app_hom_app_map (F : X.Sheaf C) {t s : P} (h : S.Strict t s) :
    ((S.counitIso C).hom.app F).hom.app (op (S.U t)) ≫
        F.presheaf.map (homOfLE (S.antitone (le_of_strict h))).op =
      S.proj ((S.B C).obj F) h := by
  have h1 := congrArg (fun φ => φ.hom.app (op (S.U t)) ≫ S.proj ((S.B C).obj F) h)
    ((S.counitIso C).hom_inv_id_app F)
  refine Eq.trans ?_ (h1.trans (Category.id_comp _))
  refine (congrArg (_ ≫ ·) (S.counitIso_inv_app_hom_app_proj F h).symm).trans ?_
  exact (Category.assoc _ _ _).symm

instance B_faithful : (S.B C).Faithful :=
  Functor.Faithful.of_comp_iso (S.counitIso C)

end Counit

end

end StrictBasis

end TDA.Sheaf
