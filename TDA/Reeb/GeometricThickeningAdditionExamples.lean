import TDA.Reeb.GeometricThickeningAddition
import TDA.Reeb.RGraphExamples
import TDA.Reeb.ConstructibleSpaceExamples
import TDA.Reeb.RGraphCosheafEquivalenceExamples

/-!
# Fixtures for the thickening addition map

Acceptance fixtures for `TDA.Reeb.GeometricThickeningAddition`, on the actual thickening, the
actual slice functors and the actual realizations of finite data:

* **One point.** No isomorphism `T_1 T_1 P ≅ T_(1+1) P` exists. The explicit pair
  `((*, 0), 0) ≠ ((*, 1), -1)` has one image under `μ_(1,1)`, and the boundary point `(*, 2)` is
  the image of `((*, 1), 1)`. Nevertheless `π₀` of `μ_(1,1)` at `ℝ` is bijective on the same
  object.
* **Boundary control.** On the point, `μ_(0,δ)` and `μ_(ε,0)` are injective, from the unit laws,
  so non-injectivity needs both parameters positive.
* **One edge.** On the realization of `singleEdge` over `0 < 1`, the thickened height of
  `((q, 1/4), 1/4)` with `q` at height `1/2` is `1` on both sides of `height_addMap`, and
  associativity at `ε = δ = γ = 1/4` gives band coordinate `3/4`.
* **Two merging edges.** On `parallelData`, the naturality squares of `addMap` and of
  `addNatTrans` for the edge swap send the point over edge `true` at height `1/2` to the point
  over edge `false`, which differs from it. The collapse onto the single edge is checked the same
  way; its target alone could not detect a wrong map.
* **Distinct classes.** On the two disjoint segments, `π₀` of `μ_(1,1)` at `ℝ` sends the classes
  over the labels `false` and `true` to classes separated by the component label.
-/

open Set Topology CategoryTheory
open scoped NNReal

namespace TDA.Reeb

noncomputable section

namespace Examples.GeometricThickeningAddition

open OpenInterval TDA.Reeb.GeometricThickening RGraph
open CylinderPresentation (ofFiniteData realizeHom height_ofStrip)
open TDA.Reeb.Examples.Cylinder (S01 half parallelData twoSegData twoSegLabel)
open TDA.Reeb.RGraph.Examples (singleEdge swap)
open TDA.Reeb.Examples.RGraphCosheafEquivalence (collapseParallel)

/-! ### One point -/

/-- The band point `1 ∈ [-1, 1]`, a boundary point. -/
def one₁ : Band 1 := ⟨((1 : ℝ≥0) : ℝ), right_mem_Icc.2 (neg_le_band 1)⟩

/-- The band point `-1 ∈ [-1, 1]`. -/
def negOne₁ : Band 1 := ⟨-((1 : ℝ≥0) : ℝ), left_mem_Icc.2 (neg_le_band 1)⟩

/-- The band point `0 ∈ [-1, 1]`. -/
def zero₁ : Band 1 := ⟨0, zero_mem_band 1⟩

/-- No height-preserving isomorphism `T_1 T_1 P ≅ T_(1+1) P` exists. -/
theorem point_not_iso :
    IsEmpty ((functor 1).obj ((functor 1).obj onePoint) ≅ (functor (1 + 1)).obj onePoint) :=
  not_iso_one_one

theorem point_not_isIso : ¬ IsIso ((addNatTrans 1 1).app onePoint) :=
  not_isIso_addNatTrans_app_one_one

/-- `((*, 0), 0)` and `((*, 1), -1)` are distinct. -/
theorem point_pair_ne :
    ((PUnit.unit, zero₁), zero₁) ≠
      (((PUnit.unit, one₁), negOne₁) : (PUnit.{1} × Band 1) × Band 1) :=
  fun h => by
    have h' := congrArg (fun z : (PUnit.{1} × Band 1) × Band 1 => (z.1.2 : ℝ)) h
    norm_num [zero₁, one₁] at h'

/-- ... and have the same image under `μ_(1,1)`. -/
theorem point_pair_addMap :
    addMap PUnit.{1} 1 1 ((PUnit.unit, zero₁), zero₁) =
      addMap PUnit.{1} 1 1 ((PUnit.unit, one₁), negOne₁) :=
  Prod.ext rfl (Subtype.ext (show (0 : ℝ) + 0 = ((1 : ℝ≥0) : ℝ) + -((1 : ℝ≥0) : ℝ) by ring))

theorem point_addMap_not_injective : ¬ Function.Injective (addMap PUnit.{1} 1 1) :=
  addMap_not_injective one_pos one_pos

theorem two_mem_band : (2 : ℝ) ∈ Band (1 + 1) := by
  rw [Band, NNReal.coe_add, NNReal.coe_one]
  norm_num

/-- The boundary point `(*, 2)` of `T_(1+1)` is the image of `((*, 1), 1)`. -/
theorem point_addMap_boundary :
    addMap PUnit.{1} 1 1 ((PUnit.unit, one₁), one₁) = (PUnit.unit, ⟨2, two_mem_band⟩) :=
  Prod.ext rfl (Subtype.ext (show ((1 : ℝ≥0) : ℝ) + ((1 : ℝ≥0) : ℝ) = 2 by norm_num))

theorem point_addMap_surjective_two :
    ∃ z, addMap PUnit.{1} 1 1 z = (PUnit.unit, ⟨2, two_mem_band⟩) :=
  addMap_surjective PUnit.{1} 1 1 _

/-- On the same object, `π₀` of `μ_(1,1)` at `ℝ` is bijective. -/
theorem point_map_addNatTrans_bijective_top :
    Function.Bijective ((intervalComponentsOver.map ((addNatTrans 1 1).app onePoint)).app ⊤) :=
  intervalComponentNatTrans_addMap_app_bijective (overBaseMap onePoint) 1 1 ⊤

/-! ### Boundary control: a zero parameter -/

/-- `μ_(0,δ)` is injective on the point, by the left unit law. -/
theorem point_addMap_zero_left_injective (δ : ℝ≥0) :
    Function.Injective (addMap PUnit.{1} 0 δ) := by
  have h : Function.Injective
      ((bandInclusion PUnit.{1} (zero_add δ).le).comp (addMap PUnit.{1} 0 δ)) := by
    rw [addMap_zero_left]
    exact (zeroHomeomorph _).injective
  exact fun a b hab => h (congrArg (bandInclusion PUnit.{1} (zero_add δ).le) hab)

/-- `μ_(ε,0)` is injective on the point, by the right unit law. -/
theorem point_addMap_zero_right_injective (ε : ℝ≥0) :
    Function.Injective (addMap PUnit.{1} ε 0) := by
  have h : Function.Injective
      ((bandInclusion PUnit.{1} (add_zero ε).le).comp (addMap PUnit.{1} ε 0)) := by
    rw [addMap_zero_right]
    intro a b hab
    rw [map_apply, map_apply, Prod.mk.injEq] at hab
    exact Prod.ext ((zeroHomeomorph _).injective hab.1) hab.2
  exact fun a b hab => h (congrArg (bandInclusion PUnit.{1} (add_zero ε).le) hab)

/-! ### One edge -/

/-- The parameter `1/4`. -/
def quarter : ℝ≥0 := ⟨1 / 4, by norm_num⟩

theorem coe_quarter : (quarter : ℝ) = 1 / 4 := rfl

/-- The band point `1/4 ∈ [-1/4, 1/4]`. -/
def quarterPt : Band quarter := ⟨(quarter : ℝ), right_mem_Icc.2 (neg_le_band quarter)⟩

/-- The band point `-1/4 ∈ [-1/4, 1/4]`. -/
def negQuarterPt : Band quarter := ⟨-(quarter : ℝ), left_mem_Icc.2 (neg_le_band quarter)⟩

/-- The realized single edge over `0 < 1` as an object of the slice. -/
abbrev edgeObj : Over (TopCat.of ℝ) := (realizationFunctor S01).obj singleEdge

/-- The point of the edge at height `1/2`. -/
def edgePt : edgeObj.left := (ofFiniteData singleEdge).ofStrip S01 0 ((), half)

/-- The thickened point `((q, 1/4), 1/4)`. -/
def edgeZ : (edgeObj.left × Band quarter) × Band quarter := ((edgePt, quarterPt), quarterPt)

/-- The addition map moves the band coordinate to `1/2`. -/
theorem edge_addMap :
    ((addMap edgeObj.left quarter quarter edgeZ).2 : ℝ) = 1 / 2 ∧
      (addMap edgeObj.left quarter quarter edgeZ).1 = edgePt :=
  ⟨show (quarter : ℝ) + quarter = 1 / 2 by rw [coe_quarter]; norm_num, rfl⟩

/-- Both sides of `height_addMap` are `1/2 + 1/4 + 1/4 = 1`. -/
theorem edge_height_addMap :
    height (overBaseMap edgeObj) (quarter + quarter) (addMap edgeObj.left quarter quarter edgeZ) =
        1 ∧
      height (height (overBaseMap edgeObj) quarter) quarter edgeZ = 1 := by
  have h : height (height (overBaseMap edgeObj) quarter) quarter edgeZ = 1 := by
    show (ofFiniteData singleEdge).height S01 edgePt + (quarter : ℝ) + quarter = 1
    rw [edgePt, height_ofStrip, coe_quarter]
    show (1 / 2 : ℝ) + 1 / 4 + 1 / 4 = 1
    norm_num
  exact ⟨(height_addMap _ _ _ _).trans h, h⟩

/-- Associativity at `(((q, 1/4), 1/4), 1/4)` with `ε = δ = γ = 1/4`: both composites agree, with
band coordinate `3/4`. -/
theorem edge_addMap_assoc :
    (bandInclusion edgeObj.left (add_assoc quarter quarter quarter).le).comp
        ((addMap edgeObj.left (quarter + quarter) quarter).comp
          (addMap (edgeObj.left × Band quarter) quarter quarter))
        (((edgePt, quarterPt), quarterPt), quarterPt) =
      (addMap edgeObj.left quarter (quarter + quarter)).comp
        (map (addMap edgeObj.left quarter quarter) quarter)
        (((edgePt, quarterPt), quarterPt), quarterPt) ∧
    (((addMap edgeObj.left quarter (quarter + quarter)).comp
        (map (addMap edgeObj.left quarter quarter) quarter)
        (((edgePt, quarterPt), quarterPt), quarterPt)).2 : ℝ) = 3 / 4 :=
  ⟨DFunLike.congr_fun (addMap_assoc quarter quarter quarter) _,
    show (quarter : ℝ) + quarter + quarter = 3 / 4 by rw [coe_quarter]; norm_num⟩

/-! ### Two merging edges -/

/-- Two parallel edges over `0 < 1` as an object of the slice. -/
abbrev parObj : Over (TopCat.of ℝ) := (realizationFunctor S01).obj parallelData

/-- The point over edge `b` at height `1/2`. -/
def parPt (b : Bool) : parObj.left := (ofFiniteData parallelData).ofStrip S01 0 (b, half)

/-- The thickened point `((q_b, 1/4), -1/4)`, at thickened height `1/2`. -/
def parZ (b : Bool) : (parObj.left × Band quarter) × Band quarter :=
  ((parPt b, quarterPt), negQuarterPt)

/-- The band coordinate of the image, `1/4 - 1/4`. -/
def parW : Band (quarter + quarter) := ⟨(quarterPt : ℝ) + negQuarterPt, add_mem_band _ _⟩

theorem height_parZ (b : Bool) :
    height (height (overBaseMap parObj) quarter) quarter (parZ b) = 1 / 2 := by
  show (ofFiniteData parallelData).height S01 (parPt b) + (quarter : ℝ) + -(quarter : ℝ) = 1 / 2
  rw [parPt, height_ofStrip]
  show (1 / 2 : ℝ) + quarter + -quarter = 1 / 2
  ring

/-- The points over the two edges differ. -/
theorem parPt_false_ne_true : parPt false ≠ parPt true := fun h =>
  Bool.false_ne_true (congrArg Prod.fst ((ofFiniteData parallelData).ofStrip_injective S01 0 h))

/-- The naturality square of `addMap` for the swap, from the general theorem. -/
theorem swap_addMap_natural :
    (map (realizeHom S01 swap) (quarter + quarter)).comp (addMap parObj.left quarter quarter) =
      (addMap parObj.left quarter quarter).comp (map (map (realizeHom S01 swap) quarter) quarter) :=
  addMap_natural _ _ _

/-- Both composites of the swap square send the point over edge `true` to the point over edge
`false`. -/
theorem swap_addMap_square_apply :
    (map (realizeHom S01 swap) (quarter + quarter)).comp (addMap parObj.left quarter quarter)
        (parZ true) = (parPt false, parW) ∧
      (addMap parObj.left quarter quarter).comp (map (map (realizeHom S01 swap) quarter) quarter)
        (parZ true) = (parPt false, parW) :=
  ⟨rfl, rfl⟩

/-- The image differs from the image under the identity, so the square detects the swap. -/
theorem swap_image_ne : ((parPt false, parW) : parObj.left × Band (quarter + quarter)) ≠
    addMap parObj.left quarter quarter (parZ true) := fun h =>
  parPt_false_ne_true (congrArg Prod.fst h)

/-- The slice naturality square of `addNatTrans` for the swap. -/
theorem swap_addNatTrans_square :
    (functor quarter ⋙ functor quarter).map ((realizationFunctor S01).map swap) ≫
        (addNatTrans quarter quarter).app parObj =
      (addNatTrans quarter quarter).app parObj ≫
        (functor (quarter + quarter)).map ((realizationFunctor S01).map swap) :=
  (addNatTrans quarter quarter).naturality _

/-- Both composites of the slice square send the point over edge `true` to the point over edge
`false`. -/
theorem swap_addNatTrans_square_apply :
    ((functor quarter ⋙ functor quarter).map ((realizationFunctor S01).map swap) ≫
        (addNatTrans quarter quarter).app parObj).left.hom (parZ true) = (parPt false, parW) ∧
      ((addNatTrans quarter quarter).app parObj ≫
        (functor (quarter + quarter)).map ((realizationFunctor S01).map swap)).left.hom
        (parZ true) = (parPt false, parW) :=
  ⟨rfl, rfl⟩

/-- The point of the single edge at height `1/2`, with the band coordinate of the image. -/
theorem collapse_addMap_square_apply :
    (map (realizeHom S01 collapseParallel) (quarter + quarter)).comp
        (addMap parObj.left quarter quarter) (parZ true) = (edgePt, parW) ∧
      (addMap edgeObj.left quarter quarter).comp
        (map (map (realizeHom S01 collapseParallel) quarter) quarter) (parZ true) =
        (edgePt, parW) :=
  ⟨rfl, rfl⟩

/-- The naturality square of `addMap` for the collapse, from the general theorem. -/
theorem collapse_addMap_natural :
    (map (realizeHom S01 collapseParallel) (quarter + quarter)).comp
        (addMap parObj.left quarter quarter) =
      (addMap edgeObj.left quarter quarter).comp
        (map (map (realizeHom S01 collapseParallel) quarter) quarter) :=
  addMap_natural _ _ _

/-- The slice naturality square of `addNatTrans` for the collapse. -/
theorem collapse_addNatTrans_square :
    (functor quarter ⋙ functor quarter).map ((realizationFunctor S01).map collapseParallel) ≫
        (addNatTrans quarter quarter).app edgeObj =
      (addNatTrans quarter quarter).app parObj ≫
        (functor (quarter + quarter)).map ((realizationFunctor S01).map collapseParallel) :=
  (addNatTrans quarter quarter).naturality _

theorem collapse_addNatTrans_square_apply :
    ((functor quarter ⋙ functor quarter).map ((realizationFunctor S01).map collapseParallel) ≫
        (addNatTrans quarter quarter).app edgeObj).left.hom (parZ true) = (edgePt, parW) ∧
      ((addNatTrans quarter quarter).app parObj ≫
        (functor (quarter + quarter)).map ((realizationFunctor S01).map collapseParallel)).left.hom
        (parZ true) = (edgePt, parW) :=
  ⟨rfl, rfl⟩

/-! ### Distinct classes: two disjoint segments -/

/-- The height of the two disjoint segments. -/
abbrev twoSegHeight : C((ofFiniteData twoSegData).Realization S01, ℝ) :=
  (ofFiniteData twoSegData).height S01

/-- The class of `((v_b, 0), 0)` over `ℝ`, for the vertex `v_b` at level `0` with label `b`. -/
def twoSegClass (b : Bool) :
    (intervalComponents (height (height twoSegHeight 1) 1)).obj ⊤ :=
  ZerothHomotopy.mk ⟨(((ofFiniteData twoSegData).ofVertex S01 0 b, zero₁), zero₁), Set.mem_univ _⟩

/-- The component label of `T_(1+1)` over `ℝ`: `twoSegLabel` of the first coordinate. -/
def twoSegTargetLabel : (intervalComponents (height twoSegHeight (1 + 1))).obj ⊤ → Bool :=
  ZerothHomotopy.lift (fun z => twoSegLabel z.1.1) fun _ _ p =>
    eq_of_joined_of_discrete ⟨p.map (twoSegLabel.continuous.comp
      (continuous_fst.comp continuous_subtype_val))⟩

theorem twoSegTargetLabel_addMap (b : Bool) :
    twoSegTargetLabel ((intervalComponentNatTrans (addMap _ 1 1)
      (height_addMap twoSegHeight 1 1)).app ⊤ (twoSegClass b)) = b :=
  rfl

/-- `π₀` of `μ_(1,1)` at `ℝ` sends the classes over the labels `false` and `true` to distinct
classes. -/
theorem twoSeg_addMap_distinct :
    (intervalComponentNatTrans (addMap _ 1 1) (height_addMap twoSegHeight 1 1)).app ⊤
        (twoSegClass false) ≠
      (intervalComponentNatTrans (addMap _ 1 1) (height_addMap twoSegHeight 1 1)).app ⊤
        (twoSegClass true) := fun h =>
  Bool.false_ne_true ((twoSegTargetLabel_addMap false).symm.trans
    ((congrArg twoSegTargetLabel h).trans (twoSegTargetLabel_addMap true)))

end Examples.GeometricThickeningAddition

end

end TDA.Reeb
