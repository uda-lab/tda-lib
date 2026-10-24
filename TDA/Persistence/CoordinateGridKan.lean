import TDA.Persistence.CoordinateGrid
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal

/-!
# Canonical fibers of finite-grid left Kan extensions

Where a real grade has lower grid points, their greatest point is terminal
in the Kan indexing category. The actual Kan unit followed by transition
from that point is therefore an isomorphism onto the extended fiber.
Where no lower point exists, the indexing category is empty and the fiber
is zero.
-/

set_option autoImplicit false

universe u w

namespace TDA.Persistence.CoordinateGrid

open CategoryTheory CategoryTheory.Limits
open scoped TDA.Persistence

variable {n : ℕ} (G : CoordinateGrid n)

private noncomputable abbrev floorArrow (a : Fin n → ℝ) (ha : G.HasLowerPoint a) :
    CostructuredArrow G.embedding.monotone.functor a :=
  CostructuredArrow.mk (Y := G.floor a ha) (homOfLE (G.floor_le a ha))

private noncomputable def floorArrowTerminal (a : Fin n → ℝ) (ha : G.HasLowerPoint a) :
    IsTerminal (floorArrow G a ha) :=
  IsTerminal.ofUniqueHom
    (fun t => CostructuredArrow.homMk
      (homOfLE (G.le_floor a ha (leOfHom t.hom))) (Subsingleton.elim _ _))
    (fun _ _ => CostructuredArrow.hom_ext _ _ (Subsingleton.elim _ _))

variable {R : Type u} [Ring R]

/-- The existing Mathlib left Kan functor along the grid inclusion. -/
noncomputable abbrev lan :
    PModule.{u,0,w} R G.Point ⥤ PModule.{u,0,w} R (Fin n → ℝ) :=
  G.embedding.monotone.functor.lan

variable (M : PModule.{u,0,w} R G.Point)

/-- Include the lower-point fiber using the actual Kan unit and real transition. -/
noncomputable def kanInclusion (a : Fin n → ℝ) (ha : G.HasLowerPoint a) :
    M.obj (G.floor a ha) ⟶ (G.lan.obj M).obj a :=
  (G.embedding.monotone.functor.leftKanExtensionUnit M).app (G.floor a ha) ≫
    structureMap (G.lan.obj M) (G.floor_le a ha)

private instance kanInclusion_isIso (a : Fin n → ℝ) (ha : G.HasLowerPoint a) :
    IsIso (G.kanInclusion M a ha) :=
  (Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit
    G.embedding.monotone.functor M a).isIso_ι_app_of_isTerminal
      (floorArrow G a ha) (floorArrowTerminal G a ha)

/-- The actual extended fiber is canonically the fiber at the greatest lower grid point. -/
noncomputable def appIso (a : Fin n → ℝ) (ha : G.HasLowerPoint a) :
    (G.lan.obj M).obj a ≅ M.obj (G.floor a ha) :=
  (asIso (G.kanInclusion M a ha)).symm

/-- The inverse fiber comparison is precisely Kan unit followed by transition. -/
theorem appIso_inv (a : Fin n → ℝ) (ha : G.HasLowerPoint a) :
    (G.appIso M a ha).inv =
      (G.embedding.monotone.functor.leftKanExtensionUnit M).app (G.floor a ha) ≫
        structureMap (G.lan.obj M) (G.floor_le a ha) := rfl

/-- The canonical inclusion followed by the fiber comparison is identity. -/
@[simp] theorem kanInclusion_appIso_hom (a : Fin n → ℝ) (ha : G.HasLowerPoint a) :
    G.kanInclusion M a ha ≫ (G.appIso M a ha).hom = 𝟙 _ := (G.appIso M a ha).inv_hom_id

/-- The fiber comparison followed by the canonical inclusion is identity. -/
@[simp] theorem appIso_hom_kanInclusion (a : Fin n → ℝ) (ha : G.HasLowerPoint a) :
    (G.appIso M a ha).hom ≫ G.kanInclusion M a ha = 𝟙 _ := (G.appIso M a ha).hom_inv_id

/-- With no lower grid point, the actual Kan fiber is zero. -/
theorem isZero_obj_of_not_hasLowerPoint (a : Fin n → ℝ) (ha : ¬ G.HasLowerPoint a) :
    IsZero ((G.lan.obj M).obj a) := by
  let : IsEmpty (CostructuredArrow G.embedding.monotone.functor a) :=
    ⟨fun t => ha ⟨t.left, leOfHom t.hom⟩⟩
  let E := Functor.LeftExtension.mk (G.lan.obj M)
    (G.embedding.monotone.functor.leftKanExtensionUnit M)
  have hc : IsColimit (E.coconeAt a) :=
    Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit G.embedding.monotone.functor M a
  have hi := isColimitEquivIsInitialOfIsEmpty (ModuleCat.{w} R) (E.coconeAt a) hc
  apply (IsZero.iff_id_eq_zero _).mpr
  exact hi.hom_ext _ _

/-- Every vector outside the region with lower grid points is zero. -/
theorem eq_zero_of_not_hasLowerPoint (a : Fin n → ℝ) (ha : ¬ G.HasLowerPoint a)
    (x : (G.lan.obj M).obj a) : x = 0 := by
  let := ModuleCat.subsingleton_of_isZero (G.isZero_obj_of_not_hasLowerPoint M a ha)
  exact Subsingleton.elim _ _

section Maps

variable {M} {N : PModule.{u,0,w} R G.Point}

/-- Canonical inclusions commute with the actual Lan map of a natural transformation. -/
theorem kanInclusion_naturality (θ : M ⟶ N) (a : Fin n → ℝ) (ha : G.HasLowerPoint a) :
    G.kanInclusion M a ha ≫ (G.lan.map θ).app a =
      θ.app (G.floor a ha) ≫ G.kanInclusion N a ha := by
  let p := G.floor a ha
  let uM : M.obj p ⟶ (G.lan.obj M).obj (G.embedding p) :=
    (G.embedding.monotone.functor.leftKanExtensionUnit M).app p
  let uN : N.obj p ⟶ (G.lan.obj N).obj (G.embedding p) :=
    (G.embedding.monotone.functor.leftKanExtensionUnit N).app p
  have hu := NatTrans.congr_app (G.embedding.monotone.functor.lanUnit.naturality θ) p
  change θ.app p ≫ uN = uM ≫ (G.lan.map θ).app (G.embedding p) at hu
  have hn := (G.lan.map θ).naturality (homOfLE (G.floor_le a ha))
  change structureMap (G.lan.obj M) (G.floor_le a ha) ≫ (G.lan.map θ).app a =
    (G.lan.map θ).app (G.embedding p) ≫ structureMap (G.lan.obj N) (G.floor_le a ha) at hn
  change (uM ≫ structureMap (G.lan.obj M) (G.floor_le a ha)) ≫ (G.lan.map θ).app a =
    θ.app p ≫ (uN ≫ structureMap (G.lan.obj N) (G.floor_le a ha))
  rw [Category.assoc, hn, ← Category.assoc, ← hu, Category.assoc]

/-- The canonical fiber comparisons are natural in the original grid module. -/
theorem appIso_naturality (θ : M ⟶ N) (a : Fin n → ℝ) (ha : G.HasLowerPoint a) :
    (G.lan.map θ).app a ≫ (G.appIso N a ha).hom =
      (G.appIso M a ha).hom ≫ θ.app (G.floor a ha) := by
  apply (cancel_epi (G.kanInclusion M a ha)).mp
  rw [← Category.assoc, G.kanInclusion_naturality, Category.assoc,
    G.kanInclusion_appIso_hom, Category.comp_id, ← Category.assoc,
    G.kanInclusion_appIso_hom, Category.id_comp]

/-- Transporting an actual Lan image reads the original grid-map image. -/
theorem appIso_map_apply (θ : M ⟶ N) (a : Fin n → ℝ) (ha : G.HasLowerPoint a)
    (x : (G.lan.obj M).obj a) :
    (G.appIso N a ha).hom.hom (((G.lan.map θ).app a).hom x) =
      (θ.app (G.floor a ha)).hom ((G.appIso M a ha).hom.hom x) :=
  congrArg (fun f => f.hom x) (G.appIso_naturality θ a ha)

end Maps

/-- Canonical inclusions commute with actual real-coordinate structure maps. -/
theorem kanInclusion_structureMap {a b : Fin n → ℝ} (hab : a ≤ b)
    (ha : G.HasLowerPoint a) (hb : G.HasLowerPoint b) :
    G.kanInclusion M a ha ≫ structureMap (G.lan.obj M) hab =
      structureMap M (G.floor_mono hab ha hb) ≫ G.kanInclusion M b hb := by
  let p := G.floor a ha
  let q := G.floor b hb
  let up : M.obj p ⟶ (G.lan.obj M).obj (G.embedding p) :=
    (G.embedding.monotone.functor.leftKanExtensionUnit M).app p
  let uq : M.obj q ⟶ (G.lan.obj M).obj (G.embedding q) :=
    (G.embedding.monotone.functor.leftKanExtensionUnit M).app q
  have hn := (G.embedding.monotone.functor.leftKanExtensionUnit M).naturality
    (homOfLE (G.floor_mono hab ha hb))
  change structureMap M (G.floor_mono hab ha hb) ≫ uq =
    up ≫ structureMap (G.lan.obj M) (G.embedding.monotone (G.floor_mono hab ha hb)) at hn
  change (up ≫ structureMap (G.lan.obj M) (G.floor_le a ha)) ≫ structureMap (G.lan.obj M) hab =
    structureMap M (G.floor_mono hab ha hb) ≫ (uq ≫ structureMap (G.lan.obj M) (G.floor_le b hb))
  rw [Category.assoc, structureMap_comp, ← Category.assoc, hn, Category.assoc, structureMap_comp]

/-- The actual real transition transports to the corresponding transition between floors. -/
theorem appIso_structureMap {a b : Fin n → ℝ} (hab : a ≤ b)
    (ha : G.HasLowerPoint a) (hb : G.HasLowerPoint b) :
    structureMap (G.lan.obj M) hab ≫ (G.appIso M b hb).hom =
      (G.appIso M a ha).hom ≫ structureMap M (G.floor_mono hab ha hb) := by
  apply (cancel_epi (G.kanInclusion M a ha)).mp
  rw [← Category.assoc, G.kanInclusion_structureMap, Category.assoc,
    G.kanInclusion_appIso_hom, Category.comp_id, ← Category.assoc,
    G.kanInclusion_appIso_hom, Category.id_comp]

/-- The fiber comparison reads each actual structure-map image as its floor image. -/
theorem appIso_structureMap_apply {a b : Fin n → ℝ} (hab : a ≤ b)
    (ha : G.HasLowerPoint a) (hb : G.HasLowerPoint b) (x : (G.lan.obj M).obj a) :
    (G.appIso M b hb).hom.hom (structureMapLinear (G.lan.obj M) hab x) =
      structureMapLinear M (G.floor_mono hab ha hb) ((G.appIso M a ha).hom.hom x) :=
  congrArg (fun f => f.hom x) (G.appIso_structureMap M hab ha hb)

end TDA.Persistence.CoordinateGrid
