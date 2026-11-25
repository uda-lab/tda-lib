import Mathlib.Topology.Sheaves.Alexandrov
import Mathlib.Topology.Sheaves.SheafCondition.Sites
import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise

/-!
# Persistence modules as sheaves on the upper Alexandrov topology

Let `X` be a preorder carrying its upper Alexandrov topology (`Topology.IsUpperSet X`: the open
sets are exactly the upper sets), and let `C` be a complete category. Write
`L := Alexandrov.principals X : X ⥤ (Opens X)ᵒᵖ` for the functor sending `p` to its principal
open `↑p = {y | p ≤ y}`; an inequality `p ≤ q` gives the inclusion `↑q ⊆ ↑p`.

* `principalSections X C : X.Sheaf C ⥤ (X ⥤ C)` (written `Γ`) is the forgetful functor to
  presheaves followed by precomposition with `L`: `Γ(F) p = F(↑p)`, and for `p ≤ q` the map
  `Γ(F)(p) ⟶ Γ(F)(q)` is the restriction of `F` along `↑q ⊆ ↑p`.
* `kanSheaf X C : (X ⥤ C) ⥤ X.Sheaf C` (written `A`) sends a covariant diagram `M` to the
  pointwise right Kan extension `L.pointwiseRightKanExtension M`, a sheaf by Mathlib's
  `Alexandrov.isSheaf_principalsKanExtension`; its value on an open `U` is the limit of `M`
  over the principal opens contained in `U`. On morphisms it is the lift
  `liftOfIsRightKanExtension` of the counit followed by the given transformation.
* `counitIso X C : kanSheaf X C ⋙ principalSections X C ≅ 𝟭 (X ⥤ C)` is the Kan-extension
  counit, i.e. the limit projection at the index `(p, 𝟙)`; it is invertible because `L` is
  fully faithful.
* `unitIso X C : 𝟭 (X.Sheaf C) ≅ principalSections X C ⋙ kanSheaf X C` compares the sections
  of a sheaf `F` over an arbitrary open `U` with the limit of its sections over the principal
  opens contained in `U`, by restriction. It is invertible for every actual sheaf `F`: the
  principal opens form a basis of the topology, and on a basic open the comparison is inverse
  to the counit.
* `equivalence X C : X.Sheaf C ≌ (X ⥤ C)` packages these with functor `Γ` and inverse `A`.

Consequently `restrictionConeIsLimit` shows that, for every sheaf `F` and open `U`, the
restrictions `F(U) ⟶ F(↑p)` for `↑p ⊆ U` form a limit cone, and `isPointwiseRightKanExtension`
states that `F` is the pointwise right Kan extension of `Γ F` along `L`.

For an unbundled preorder `P`, `upperSetEquivalence P C : (P ⥤ C) ≌ (upperSpace P).Sheaf C`
uses `upperSpace P := TopCat.of (Topology.WithUpperSet P)`, the type synonym carrying the upper
set topology, and the order isomorphism `Topology.WithUpperSet.toUpperSetOrderIso`. No topology
is installed on `P` itself. `upperSetSectionsIso` and `upperSetSectionsIso_hom_naturality`
identify the sections over `↑p` with `M p` and the restriction along `↑q ⊆ ↑p` with `M (p ≤ q)`.

The universe constraints are those of Mathlib's `Alexandrov.isSheaf_principalsKanExtension`:
`X : TopCat.{v}` and `C : Type u` with `[Category.{v} C] [HasLimits C]`. This is an
equivalence with sheaves on the upper Alexandrov space only; it says nothing about sheaves for
the ordinary topology of a Euclidean space.
-/

universe v u

open CategoryTheory Limits Functor Opposite TopologicalSpace TopCat

namespace TDA.Sheaf.Alexandrov

section Principals

variable (X : TopCat.{v}) [Preorder X] [Topology.IsUpperSet X]

/-- The principal opens `↑p = {y | p ≤ y}` form a basis of the upper Alexandrov topology. -/
theorem isBasis_principalOpen :
    Opens.IsBasis (Set.range (fun p : X => _root_.Alexandrov.principalOpen p)) := by
  rw [Opens.isBasis_iff_nbhd]
  intro U x hx
  exact ⟨_root_.Alexandrov.principalOpen x, ⟨x, rfl⟩,
    _root_.Alexandrov.self_mem_principalOpen x,
    (_root_.Alexandrov.principalOpen_le_iff U).2 hx⟩

/-- An inclusion of principal opens `↑q ⊆ ↑p` forces `p ≤ q`, since `q ∈ ↑q`. -/
theorem le_of_principalOpen_le {p q : X}
    (h : _root_.Alexandrov.principalOpen q ≤ _root_.Alexandrov.principalOpen p) : p ≤ q :=
  (_root_.Alexandrov.principalOpen_le_iff _).1 h

instance full_principals : (_root_.Alexandrov.principals X).Full where
  map_surjective {_ _} f := ⟨homOfLE (le_of_principalOpen_le X f.unop.le), rfl⟩

instance faithful_principals : (_root_.Alexandrov.principals X).Faithful where
  map_injective {_ _} _ _ _ := Subsingleton.elim _ _

end Principals

section Sections

variable (X : TopCat.{v}) [Preorder X] [Topology.IsUpperSet X]
variable (C : Type u) [Category.{v} C]

/-- The functor `Γ`: the sections of a sheaf over the principal opens,
`TopCat.Sheaf.forget C X ⋙ (whiskeringLeft _ _ C).obj (Alexandrov.principals X)`. -/
noncomputable def principalSections : X.Sheaf C ⥤ (X ⥤ C) :=
  TopCat.Sheaf.forget C X ⋙
    (Functor.whiskeringLeft X (Opens X)ᵒᵖ C).obj (_root_.Alexandrov.principals X)

variable {X C}

/-- `Γ(F)` is `F` precomposed with `Alexandrov.principals X`. -/
theorem principalSections_obj (F : X.Sheaf C) :
    (principalSections X C).obj F = _root_.Alexandrov.principals X ⋙ F.presheaf :=
  rfl

/-- `Γ(F)` at `p` is the sections of `F` over the principal open `↑p`. -/
@[simp]
theorem principalSections_obj_obj (F : X.Sheaf C) (p : X) :
    ((principalSections X C).obj F).obj p =
      F.presheaf.obj (op (_root_.Alexandrov.principalOpen p)) :=
  rfl

/-- For `f : p ⟶ q` (that is, `p ≤ q`), `Γ(F).map f` is the restriction of `F` along the
inclusion `↑q ⊆ ↑p`. -/
@[simp]
theorem principalSections_obj_map (F : X.Sheaf C) {p q : X} (f : p ⟶ q) :
    ((principalSections X C).obj F).map f =
      F.presheaf.map (homOfLE (_root_.Alexandrov.principalOpen_le f.le)).op :=
  rfl

/-- `Γ` on a morphism of sheaves is its component on each principal open. -/
@[simp]
theorem principalSections_map_app {F G : X.Sheaf C} (φ : F ⟶ G) (p : X) :
    ((principalSections X C).map φ).app p =
      φ.hom.app (op (_root_.Alexandrov.principalOpen p)) :=
  rfl

/-- The cone of restrictions `F(U) ⟶ F(↑p)` over the principal opens `↑p ⊆ U`, indexed by the
comma category of `L` under `U`. -/
@[simps]
def restrictionCone (F : X.Sheaf C) (U : Opens X) :
    Cone (StructuredArrow.proj (op U) (_root_.Alexandrov.principals X) ⋙
      _root_.Alexandrov.principals X ⋙ F.presheaf) where
  pt := F.presheaf.obj (op U)
  π :=
    { app := fun j => F.presheaf.map j.hom
      naturality := fun j j' g => by
        change 𝟙 _ ≫ F.presheaf.map j'.hom =
          F.presheaf.map j.hom ≫ F.presheaf.map ((_root_.Alexandrov.principals X).map g.right)
        rw [Category.id_comp, ← F.presheaf.map_comp, StructuredArrow.w g] }

end Sections

section Equivalence

variable (X : TopCat.{v}) [Preorder X] [Topology.IsUpperSet X]
variable (C : Type u) [Category.{v} C] [HasLimits C]

/-- The presheaf part of `A`: a covariant diagram `M : X ⥤ C` goes to its pointwise right Kan
extension along `Alexandrov.principals X`, and `α : M ⟶ N` to the Kan-extension lift
(`liftOfIsRightKanExtension`) of the counit of `M` followed by `α`. -/
@[simps]
noncomputable def kanPresheaf : (X ⥤ C) ⥤ ((Opens X)ᵒᵖ ⥤ C) where
  obj M := (_root_.Alexandrov.principals X).pointwiseRightKanExtension M
  map {M N} α :=
    ((_root_.Alexandrov.principals X).pointwiseRightKanExtension N).liftOfIsRightKanExtension
      ((_root_.Alexandrov.principals X).pointwiseRightKanExtensionCounit N) _
      ((_root_.Alexandrov.principals X).pointwiseRightKanExtensionCounit M ≫ α)
  map_id M :=
    hom_ext_of_isRightKanExtension _
      ((_root_.Alexandrov.principals X).pointwiseRightKanExtensionCounit M) _ _ (by simp)
  map_comp {M N K} α β :=
    hom_ext_of_isRightKanExtension _
      ((_root_.Alexandrov.principals X).pointwiseRightKanExtensionCounit K) _ _ (by
        ext p
        simp)

/-- The functor `A`: a covariant diagram `M : X ⥤ C` goes to the sheaf whose underlying presheaf
is the pointwise right Kan extension `(Alexandrov.principals X).pointwiseRightKanExtension M`,
a sheaf by `Alexandrov.isSheaf_principalsKanExtension`. -/
noncomputable def kanSheaf : (X ⥤ C) ⥤ X.Sheaf C :=
  ObjectProperty.lift _ (kanPresheaf X C)
    (fun M => _root_.Alexandrov.isSheaf_principalsKanExtension M)

variable {X C}

/-- The sheaf `A(M)` has underlying presheaf the pointwise right Kan extension of `M`. -/
@[simp]
theorem kanSheaf_obj_presheaf (M : X ⥤ C) :
    ((kanSheaf X C).obj M).presheaf =
      (_root_.Alexandrov.principals X).pointwiseRightKanExtension M :=
  rfl

/-- `A` on a morphism `α : M ⟶ N` is the Kan-extension lift of the counit of `M` followed by
`α`. -/
theorem kanSheaf_map_hom {M N : X ⥤ C} (α : M ⟶ N) :
    ((kanSheaf X C).map α).hom =
      ((_root_.Alexandrov.principals X).pointwiseRightKanExtension N).liftOfIsRightKanExtension
        ((_root_.Alexandrov.principals X).pointwiseRightKanExtensionCounit N) _
        ((_root_.Alexandrov.principals X).pointwiseRightKanExtensionCounit M ≫ α) :=
  rfl

/-- On sections over any open `U`, `A(α)` acts on the limit componentwise by `α`. -/
@[reassoc]
theorem kanSheaf_map_hom_app_π {M N : X ⥤ C} (α : M ⟶ N) (U : (Opens X)ᵒᵖ)
    (j : StructuredArrow U (_root_.Alexandrov.principals X)) :
    ((kanSheaf X C).map α).hom.app U ≫ limit.π (StructuredArrow.proj U _ ⋙ N) j =
      limit.π (StructuredArrow.proj U _ ⋙ M) j ≫ α.app j.right := by
  have key : ((_root_.Alexandrov.principals X).pointwiseRightKanExtension M).map j.hom ≫
      ((_root_.Alexandrov.principals X).pointwiseRightKanExtensionCounit M).app j.right =
        limit.π (StructuredArrow.proj U _ ⋙ M) j := by
    rw [pointwiseRightKanExtensionCounit_app]
    erw [pointwiseRightKanExtension_map, limit.lift_π]
    change limit.π _ ((StructuredArrow.map j.hom).obj (StructuredArrow.mk (𝟙 _))) = _
    congr 1
  rw [kanSheaf_map_hom, pointwiseRightKanExtension_lift_app]
  erw [limit.lift_π]
  exact (reassoc_of% key) (α.app j.right)

instance isIso_pointwiseRightKanExtensionCounit (M : X ⥤ C) :
    IsIso ((_root_.Alexandrov.principals X).pointwiseRightKanExtensionCounit M) :=
  ((_root_.Alexandrov.principals X).pointwiseRightKanExtensionIsPointwiseRightKanExtension
    M).isIso_hom

variable (X C)

/-- The counit `Γ(A M) ≅ M`, natural in `M`: at `p` it is the limit projection of
`A(M)(↑p)` at the index `(p, 𝟙)`. -/
noncomputable def counitIso : kanSheaf X C ⋙ principalSections X C ≅ 𝟭 (X ⥤ C) :=
  NatIso.ofComponents
    (fun M => (asIso ((_root_.Alexandrov.principals X).pointwiseRightKanExtensionCounit M) :
      _root_.Alexandrov.principals X ⋙
          (_root_.Alexandrov.principals X).pointwiseRightKanExtension M ≅ M))
    (fun {M N} α =>
      liftOfIsRightKanExtension_fac
        ((_root_.Alexandrov.principals X).pointwiseRightKanExtension N)
        ((_root_.Alexandrov.principals X).pointwiseRightKanExtensionCounit N)
        ((_root_.Alexandrov.principals X).pointwiseRightKanExtension M)
        ((_root_.Alexandrov.principals X).pointwiseRightKanExtensionCounit M ≫ α))

variable {X C}

/-- The counit at `M` and `p` is the projection of the limit `A(M)(↑p)` to its index `(p, 𝟙)`. -/
theorem counitIso_hom_app_app (M : X ⥤ C) (p : X) :
    ((counitIso X C).hom.app M).app p =
      limit.π (StructuredArrow.proj (op (_root_.Alexandrov.principalOpen p))
        (_root_.Alexandrov.principals X) ⋙ M) (StructuredArrow.mk (𝟙 _)) :=
  rfl

/-- Under the counit, the transition map `Γ(A M).map f` is the original `M.map f`. -/
@[reassoc]
theorem principalSections_kanSheaf_map_comp_counit (M : X ⥤ C) {p q : X} (f : p ⟶ q) :
    ((principalSections X C).obj ((kanSheaf X C).obj M)).map f ≫
        ((counitIso X C).hom.app M).app q =
      ((counitIso X C).hom.app M).app p ≫ M.map f :=
  ((counitIso X C).hom.app M).naturality f

/-- The transition map `Γ(A M).map f`, written through the counit isomorphisms. -/
theorem principalSections_kanSheaf_map (M : X ⥤ C) {p q : X} (f : p ⟶ q) :
    ((principalSections X C).obj ((kanSheaf X C).obj M)).map f =
      ((counitIso X C).hom.app M).app p ≫ M.map f ≫ ((counitIso X C).inv.app M).app q := by
  rw [← principalSections_kanSheaf_map_comp_counit_assoc, Iso.hom_inv_id_app_app]
  exact (Category.comp_id _).symm

/-- The counit is natural: `Γ(A α)` corresponds to `α`. -/
@[reassoc]
theorem principalSections_kanSheaf_map_app {M N : X ⥤ C} (α : M ⟶ N) (p : X) :
    ((principalSections X C).map ((kanSheaf X C).map α)).app p ≫
        ((counitIso X C).hom.app N).app p =
      ((counitIso X C).hom.app M).app p ≫ α.app p :=
  congr_app ((counitIso X C).hom.naturality α) p

/-- The comparison from a sheaf to the Kan extension of its principal sections, at the presheaf
level: the Kan-extension lift of the identity of `Γ F`. -/
noncomputable def unitPresheafHom (F : X.Sheaf C) :
    @Quiver.Hom ((Opens X)ᵒᵖ ⥤ C) _ F.presheaf
      ((_root_.Alexandrov.principals X).pointwiseRightKanExtension
        (_root_.Alexandrov.principals X ⋙ F.presheaf)) :=
  ((_root_.Alexandrov.principals X).pointwiseRightKanExtension
      (_root_.Alexandrov.principals X ⋙ F.presheaf)).liftOfIsRightKanExtension
    ((_root_.Alexandrov.principals X).pointwiseRightKanExtensionCounit _) F.presheaf
    (𝟙 (_root_.Alexandrov.principals X ⋙ F.presheaf))

/-- On an open `U`, the comparison is the lift of the restriction cone to the limit. -/
theorem unitPresheafHom_app (F : X.Sheaf C) (U : Opens X) :
    (unitPresheafHom F).app (op U) = limit.lift _ (restrictionCone F U) := by
  rw [unitPresheafHom, pointwiseRightKanExtension_lift_app]
  apply limit.hom_ext
  intro j
  rw [limit.lift_π]
  erw [limit.lift_π]
  rw [structuredArrowMapCone_π_app, restrictionCone_π_app, NatTrans.id_app]
  exact Category.comp_id _

@[reassoc (attr := simp)]
theorem unitPresheafHom_app_counit (F : X.Sheaf C) (p : X) :
    (unitPresheafHom F).app ((_root_.Alexandrov.principals X).obj p) ≫
        ((_root_.Alexandrov.principals X).pointwiseRightKanExtensionCounit
          (_root_.Alexandrov.principals X ⋙ F.presheaf)).app p = 𝟙 _ :=
  (liftOfIsRightKanExtension_fac_app _ _ _ _ p).trans (NatTrans.id_app _ _)

@[reassoc (attr := simp)]
theorem unitPresheafHom_fac (F : X.Sheaf C) :
    whiskerLeft (_root_.Alexandrov.principals X) (unitPresheafHom F) ≫
        (_root_.Alexandrov.principals X).pointwiseRightKanExtensionCounit
          (_root_.Alexandrov.principals X ⋙ F.presheaf) = 𝟙 _ :=
  liftOfIsRightKanExtension_fac _ _ _ _

instance isIso_unitPresheafHom_app_principals (F : X.Sheaf C) (p : X) :
    IsIso ((unitPresheafHom F).app ((_root_.Alexandrov.principals X).obj p)) := by
  have : IsIso ((unitPresheafHom F).app ((_root_.Alexandrov.principals X).obj p) ≫
      ((_root_.Alexandrov.principals X).pointwiseRightKanExtensionCounit
        (_root_.Alexandrov.principals X ⋙ F.presheaf)).app p) := by
    rw [unitPresheafHom_app_counit]
    infer_instance
  exact IsIso.of_isIso_comp_right _
    (((_root_.Alexandrov.principals X).pointwiseRightKanExtensionCounit
      (_root_.Alexandrov.principals X ⋙ F.presheaf)).app p)

theorem unitPresheafHom_naturality {F G : X.Sheaf C} (φ : F ⟶ G) :
    φ.hom ≫ unitPresheafHom G =
      unitPresheafHom F ≫
        ((_root_.Alexandrov.principals X).pointwiseRightKanExtension
          (_root_.Alexandrov.principals X ⋙ G.presheaf)).liftOfIsRightKanExtension
          ((_root_.Alexandrov.principals X).pointwiseRightKanExtensionCounit _) _
          ((_root_.Alexandrov.principals X).pointwiseRightKanExtensionCounit
            (_root_.Alexandrov.principals X ⋙ F.presheaf) ≫
            whiskerLeft (_root_.Alexandrov.principals X) φ.hom) := by
  apply hom_ext_of_isRightKanExtension _
    ((_root_.Alexandrov.principals X).pointwiseRightKanExtensionCounit
      (_root_.Alexandrov.principals X ⋙ G.presheaf))
  simp only [Functor.whiskerLeft_comp, Category.assoc, unitPresheafHom_fac,
    liftOfIsRightKanExtension_fac, unitPresheafHom_fac_assoc, Category.comp_id]

/-- The unit at a sheaf `F` as a morphism of sheaves `F ⟶ A(Γ F)`. -/
noncomputable def unitHom (F : X.Sheaf C) :
    F ⟶ (kanSheaf X C).obj ((principalSections X C).obj F) :=
  ObjectProperty.homMk (unitPresheafHom F)

instance isIso_unitHom (F : X.Sheaf C) : IsIso (unitHom F) :=
  TopCat.Sheaf.isIso_iff_isIso_basis (B := fun p : X => _root_.Alexandrov.principalOpen p)
    (isBasis_principalOpen X) (fun p =>
      inferInstanceAs (IsIso ((unitPresheafHom F).app ((_root_.Alexandrov.principals X).obj p))))

instance isIso_unitPresheafHom (F : X.Sheaf C) : IsIso (unitPresheafHom F) :=
  (Functor.map_isIso (TopCat.Sheaf.forget C X) (unitHom F) :)

variable (X C)

/-- The unit `F ≅ A(Γ F)`, natural in the sheaf `F`: on an open `U`, it compares the sections
over `U` with the limit of the sections over the principal opens contained in `U`, by
restriction. -/
noncomputable def unitIso : 𝟭 (X.Sheaf C) ≅ principalSections X C ⋙ kanSheaf X C :=
  NatIso.ofComponents
    (fun F => (asIso (unitHom F) : F ≅ (kanSheaf X C).obj ((principalSections X C).obj F)))
    (fun {_ _} φ => CategoryTheory.Sheaf.hom_ext (unitPresheafHom_naturality φ))

variable {X C}

/-- The unit at `F` on an open `U` is the lift of the restriction cone to the limit. -/
theorem unitIso_hom_app_hom_app (F : X.Sheaf C) (U : Opens X) :
    ((unitIso X C).hom.app F).hom.app (op U) = limit.lift _ (restrictionCone F U) :=
  unitPresheafHom_app F U

/-- Followed by the limit projection at `(p, ↑p ⊆ U)`, the unit is the restriction of `F` along
`↑p ⊆ U`. -/
@[reassoc]
theorem unitIso_hom_app_hom_app_π (F : X.Sheaf C) (U : Opens X)
    (j : StructuredArrow (op U) (_root_.Alexandrov.principals X)) :
    ((unitIso X C).hom.app F).hom.app (op U) ≫
        limit.π (StructuredArrow.proj (op U) (_root_.Alexandrov.principals X) ⋙
          _root_.Alexandrov.principals X ⋙ F.presheaf) j =
      F.presheaf.map j.hom :=
  (unitPresheafHom_app F U ▸ limit.lift_π (restrictionCone F U) j :)

/-- On a principal open `↑p`, the inverse unit is the limit projection at `(p, 𝟙)`. -/
theorem unitIso_inv_app_hom_app_principalOpen (F : X.Sheaf C) (p : X) :
    ((unitIso X C).inv.app F).hom.app (op (_root_.Alexandrov.principalOpen p)) =
      limit.π (StructuredArrow.proj (op (_root_.Alexandrov.principalOpen p))
        (_root_.Alexandrov.principals X) ⋙ _root_.Alexandrov.principals X ⋙ F.presheaf)
        (StructuredArrow.mk (𝟙 _)) := by
  have h : (unitPresheafHom F).app ((_root_.Alexandrov.principals X).obj p) ≫
      ((unitIso X C).inv.app F).hom.app (op (_root_.Alexandrov.principalOpen p)) = 𝟙 _ :=
    congr_arg (fun f => f.hom.app (op (_root_.Alexandrov.principalOpen p)))
      ((unitIso X C).hom_inv_id_app F)
  exact (IsIso.eq_inv_of_hom_inv_id h).trans
    (IsIso.inv_eq_of_hom_inv_id (unitPresheafHom_app_counit F p))

/-- The restrictions `F(U) ⟶ F(↑p)` for `↑p ⊆ U` form a limit cone, for every sheaf `F` on the
upper Alexandrov space and every open `U`. -/
noncomputable def restrictionConeIsLimit (F : X.Sheaf C) (U : Opens X) :
    IsLimit (restrictionCone F U) :=
  haveI : IsIso (limit.lift _ (restrictionCone F U)) := by
    have : IsIso ((unitPresheafHom F).app (op U)) := inferInstance
    rw [unitPresheafHom_app] at this
    exact this
  IsLimit.ofPointIso (limit.isLimit _) (i := this)

/-- Every sheaf `F` on the upper Alexandrov space is the pointwise right Kan extension of its
principal sections `Γ F` along `Alexandrov.principals X`, with identity counit. -/
noncomputable def isPointwiseRightKanExtension (F : X.Sheaf C) :
    (RightExtension.mk F.presheaf
      (𝟙 (_root_.Alexandrov.principals X ⋙ F.presheaf))).IsPointwiseRightKanExtension :=
  fun U => IsLimit.ofIsoLimit (restrictionConeIsLimit F U.unop)
    (Cone.ext (Iso.refl _) (fun j => by
      change F.presheaf.map j.hom = 𝟙 _ ≫ F.presheaf.map j.hom ≫ 𝟙 _
      rw [Category.id_comp, Category.comp_id]))

variable (X C)

/-- Sheaves of `C`-objects on the upper Alexandrov space of `X` are equivalent to covariant
diagrams `X ⥤ C`, with functor `Γ = principalSections X C` and inverse `A = kanSheaf X C`. -/
noncomputable def equivalence : X.Sheaf C ≌ (X ⥤ C) where
  functor := principalSections X C
  inverse := kanSheaf X C
  unitIso := unitIso X C
  counitIso := counitIso X C
  functor_unitIso_comp F := by
    ext p
    exact unitPresheafHom_app_counit F p

@[simp]
theorem equivalence_functor : (equivalence X C).functor = principalSections X C :=
  rfl

@[simp]
theorem equivalence_inverse : (equivalence X C).inverse = kanSheaf X C :=
  rfl

@[simp]
theorem equivalence_unitIso : (equivalence X C).unitIso = unitIso X C :=
  rfl

@[simp]
theorem equivalence_counitIso : (equivalence X C).counitIso = counitIso X C :=
  rfl

end Equivalence

section WithUpperSet

open Topology

variable (P : Type v) [Preorder P]

/-- The upper Alexandrov space of a preorder `P`: the type synonym `WithUpperSet P` with its
upper set topology, as an object of `TopCat`. No topology is placed on `P` itself. -/
abbrev upperSpace : TopCat.{v} :=
  TopCat.of (WithUpperSet P)

variable (C : Type u) [Category.{v} C] [HasLimits C]

/-- Covariant diagrams on an unbundled preorder `P` are equivalent to sheaves on its upper
Alexandrov space `WithUpperSet P`, transported along `WithUpperSet.toUpperSetOrderIso`. -/
noncomputable def upperSetEquivalence : (P ⥤ C) ≌ (upperSpace P).Sheaf C :=
  (WithUpperSet.toUpperSetOrderIso (α := P)).equivalence.congrLeft.trans
    (equivalence (upperSpace P) C).symm

variable {P C}

/-- The sheaf attached to `M : P ⥤ C` is `A` applied to `M` read on `WithUpperSet P`. -/
theorem upperSetEquivalence_functor_obj (M : P ⥤ C) :
    (upperSetEquivalence P C).functor.obj M =
      (kanSheaf (upperSpace P) C).obj
        ((WithUpperSet.toUpperSetOrderIso (α := P)).symm.monotone.functor ⋙ M) :=
  rfl

/-- The sections over the principal open of `toUpperSet p` of the sheaf attached to `M` are
`M p`. -/
noncomputable def upperSetSectionsIso (M : P ⥤ C) (p : P) :
    ((upperSetEquivalence P C).functor.obj M).presheaf.obj
        (op (_root_.Alexandrov.principalOpen (X := upperSpace P) (WithUpperSet.toUpperSet p))) ≅
      M.obj p :=
  ((counitIso (upperSpace P) C).app
    ((WithUpperSet.toUpperSetOrderIso (α := P)).symm.monotone.functor ⋙ M)).app
      (WithUpperSet.toUpperSet p)

/-- The restriction of the attached sheaf along `↑q ⊆ ↑p`, for `p ≤ q`, is `M.map` of
`p ≤ q` under the section isomorphisms. -/
@[reassoc]
theorem upperSetSectionsIso_hom_naturality (M : P ⥤ C) {p q : P} (h : p ≤ q) :
    ((upperSetEquivalence P C).functor.obj M).presheaf.map
        (homOfLE (_root_.Alexandrov.principalOpen_le (X := upperSpace P)
          (x := WithUpperSet.toUpperSet p) (y := WithUpperSet.toUpperSet q) h)).op ≫
        (upperSetSectionsIso M q).hom =
      (upperSetSectionsIso M p).hom ≫ M.map (homOfLE h) :=
  principalSections_kanSheaf_map_comp_counit
    ((WithUpperSet.toUpperSetOrderIso (α := P)).symm.monotone.functor ⋙ M)
    (X := upperSpace P) (homOfLE h)

/-- A morphism `α : M ⟶ N` of diagrams on `P` acts on the sections over `↑p` of the attached
sheaves as `α.app p`, under the section isomorphisms. -/
@[reassoc]
theorem upperSetEquivalence_map_app_sectionsIso {M N : P ⥤ C} (α : M ⟶ N) (p : P) :
    ((upperSetEquivalence P C).functor.map α).hom.app
        (op (_root_.Alexandrov.principalOpen (X := upperSpace P) (WithUpperSet.toUpperSet p))) ≫
        (upperSetSectionsIso N p).hom =
      (upperSetSectionsIso M p).hom ≫ α.app p :=
  principalSections_kanSheaf_map_app (X := upperSpace P) (C := C)
    (whiskerLeft (WithUpperSet.toUpperSetOrderIso (α := P)).symm.monotone.functor α)
    (WithUpperSet.toUpperSet p)

end WithUpperSet

end TDA.Sheaf.Alexandrov
