import TDA.Reeb.QuotientThickeningAbsorption
import TDA.Reeb.QuotientThickeningAdditionExamples
import TDA.Reeb.RGraphSmoothingExamples
import TDA.Reeb.RGraphCosheafEquivalenceExamples

/-!
# Fixtures for absorption and the geometric smoothing semigroup

Acceptance fixtures for `TDA.Reeb.QuotientThickeningAbsorption`, on the actual thickening, the
actual Reeb quotient and the actual realizations of finite data:

* **Negative control.** The Reeb projection of `T_(1/4)` of the single edge is not an
  isomorphism: two distinct points at height `1/2` are joined by a constant-height path. Absorption
  holds at this object nevertheless.
* **Graph-object control.** On the parallel edges the inverse of absorption is `ℛ T_(1/4)` of the
  inverse of `projNatIso`, computed through it and through the general inverse formula.
* **Boundary control.** `ℛ q_X = q_(ℛ X)`, and the left unit law on the point sends
  `[([(*, s)], 0)]` to `[(*, s)]`.
* **One edge.** At `ε = δ = 1/4` the semigroup sends `[([(q, 1/4)], 1/4)]` to `[(q, 1/2)]` and back,
  associativity gives band coordinate `3/4` on both sides, and the cosheaf square at `⊤` gives the
  class of `q` on both sides.
* **Two merging edges.** In `U_(1/4) U_(1/4)` the height-`1/2` fibre is a subsingleton and the
  classes over the two edges agree, while the height-`1/2` fibre of `U_(1/4)` is not a
  subsingleton; in `U_(1/8) U_(1/8)` the height-`1/2` fibre is not a subsingleton.
* **Naturality and packaging.** The edge-swap square of the semigroup, and the explicit
  isomorphism `U_1 U_1 P ≅ U_(1+1) P` on the point.
-/

open Set Topology CategoryTheory
open scoped NNReal

namespace TDA.Reeb

noncomputable section

namespace Examples.QuotientThickeningAbsorption

open OpenInterval TDA.Reeb.GeometricThickening RGraph
open CylinderPresentation (ofFiniteData height_ofStrip)
open TDA.Reeb.Examples.Cylinder (S01)
open TDA.Reeb.RGraph.Examples (singleEdge)
open TDA.Reeb.Examples.GeometricThickeningAddition (quarter coe_quarter quarterPt negQuarterPt
  edgeObj edgePt parObj parPt parZ parW height_parZ parPt_false_ne_true swap_image_ne)
open TDA.Reeb.Examples.QuotientThickeningAddition (halfPt zeroQ threeQuarterPt eighth
  par_eighth_fiber_not_subsingleton swap_geometricSmoothingAddIso_square_apply)
open TDA.Reeb.Examples.RGraphCosheafEquivalence (parallelGraph swapGraph singleGraph pointGraph)
open TDA.Reeb.Examples.RGraphSmoothing (parallel_smoothed_fiber_subsingleton
  parallel_quarter_fiber_not_subsingleton)

local notation "ℛ" => ReebQuotient.quotientFunctor ℝ

/-! ### Transport of fibres along isomorphisms -/

/-- An isomorphism of graph objects is injective and preserves height, so a subsingleton height
fibre of the target gives a subsingleton height fibre of the source. -/
theorem fiber_subsingleton_of_iso {B B' : RGraphCat} (e : B ≅ B') (t : ℝ)
    (h : Subsingleton (overBaseMap B'.obj ⁻¹' {t})) :
    Subsingleton (overBaseMap B.obj ⁻¹' {t}) := by
  constructor
  rintro ⟨x₁, h₁⟩ ⟨x₂, h₂⟩
  have hh : ∀ x, overBaseMap B'.obj (e.hom.hom.left.hom x) = overBaseMap B.obj x :=
    overBaseMap_comm e.hom.hom
  have hinv : ∀ x, e.inv.hom.left.hom (e.hom.hom.left.hom x) = x := fun x =>
    congrArg (fun φ => φ.hom.left.hom x) e.hom_inv_id
  have hx := congrArg Subtype.val
    (h.elim ⟨_, (hh x₁).trans (Set.mem_singleton_iff.1 h₁)⟩
      ⟨_, (hh x₂).trans (Set.mem_singleton_iff.1 h₂)⟩)
  exact Subtype.ext ((hinv x₁).symm.trans ((congrArg e.inv.hom.left.hom hx).trans (hinv x₂)))

/-! ### Negative control: the projection of `T_(1/4)` of the edge -/

/-- The regular height `1/4` of the gap `(0, 1)`. -/
def quarterStrip : (S01.K 0 : Set ℝ) := ⟨1 / 4, by
  show S01.value (Fin.castSucc 0) < 1 / 4 ∧ 1 / 4 < S01.value (Fin.succ 0)
  simp only [Fin.castSucc_zero, Fin.succ_zero_eq_one, Examples.Cylinder.S01_value_zero,
    Examples.Cylinder.S01_value_one]
  norm_num⟩

/-- The point of the edge at height `1/4`. -/
def edgeQuarterPt : edgeObj.left :=
  (ofFiniteData singleEdge).ofStrip S01 0 ((), quarterStrip)

/-- The strip height `1/2 - r/4 ∈ (0, 1)` for `r ∈ [0, 1]`. -/
def stripHeight (r : unitInterval) : (S01.K 0 : Set ℝ) := ⟨1 / 2 - (r : ℝ) / 4, by
  show S01.value (Fin.castSucc 0) < 1 / 2 - (r : ℝ) / 4 ∧
    1 / 2 - (r : ℝ) / 4 < S01.value (Fin.succ 0)
  simp only [Fin.castSucc_zero, Fin.succ_zero_eq_one, Examples.Cylinder.S01_value_zero,
    Examples.Cylinder.S01_value_one]
  constructor <;> linarith [r.2.1, r.2.2]⟩

/-- The band point `r/4 ∈ [-1/4, 1/4]` for `r ∈ [0, 1]`. -/
def bandQuarter (r : unitInterval) : Band quarter := ⟨(r : ℝ) / 4, by
  show -(quarter : ℝ) ≤ (r : ℝ) / 4 ∧ (r : ℝ) / 4 ≤ quarter
  rw [coe_quarter]
  constructor <;> linarith [r.2.1, r.2.2]⟩

/-- The constant-height path `r ↦ (q_(1/2 - r/4), r/4)` in `T_(1/4)` of the edge, from
`(q_(1/2), 0)` to `(q_(1/4), 1/4)`. -/
def edgeFiberPath : Path ((edgePt, zeroQ) : edgeObj.left × Band quarter)
    (edgeQuarterPt, quarterPt) where
  toFun r := ((ofFiniteData singleEdge).ofStrip S01 0 ((), stripHeight r),
    bandQuarter r)
  continuous_toFun := by
    have h₁ : Continuous fun r : unitInterval => (1 / 2 - (r : ℝ) / 4) := by fun_prop
    have h₂ : Continuous fun r : unitInterval => ((r : ℝ) / 4) := by fun_prop
    exact (((ofFiniteData singleEdge).continuous_ofStrip S01 0).comp
      (continuous_const.prodMk (h₁.subtype_mk _))).prodMk (h₂.subtype_mk _)
  source' := by
    refine Prod.ext (congrArg (fun v => (ofFiniteData singleEdge).ofStrip S01 0
      ((), v)) (Subtype.ext ?_)) (Subtype.ext ?_)
    · show (1 / 2 : ℝ) - ((0 : unitInterval) : ℝ) / 4 = 1 / 2
      simp
    · show ((0 : unitInterval) : ℝ) / 4 = 0
      simp
  target' := by
    refine Prod.ext (congrArg (fun v => (ofFiniteData singleEdge).ofStrip S01 0
      ((), v)) (Subtype.ext ?_)) (Subtype.ext ?_)
    · show (1 / 2 : ℝ) - ((1 : unitInterval) : ℝ) / 4 = 1 / 4
      norm_num
    · show ((1 : unitInterval) : ℝ) / 4 = quarter
      rw [coe_quarter]
      norm_num

/-- **The projection of `T_δ A` is not an isomorphism, and absorption holds there.** On the edge
with `δ = ε = 1/4`, the distinct points `(q_(1/2), 0)` and `(q_(1/4), 1/4)` of `T_(1/4) A` at height
`1/2` are joined by `edgeFiberPath`, so they have the same Reeb class, and a slice isomorphism is
injective. The absorption morphism `ℛ (T_(1/4) q_(T_(1/4) A))` is an isomorphism all the same. -/
theorem edge_projNatTrans_not_isIso :
    ¬ IsIso ((ReebQuotient.projNatTrans ℝ).app ((functor quarter).obj edgeObj)) ∧
      IsIso ((ℛ).map ((functor quarter).map
        ((ReebQuotient.projNatTrans ℝ).app ((functor quarter).obj edgeObj)))) := by
  refine ⟨fun hiso => ?_, isIso_quotientFunctor_map_functor_map_projNatTrans_app_thickening
    singleGraph quarter quarter⟩
  have hne : ((edgePt, zeroQ) : edgeObj.left × Band quarter) ≠ (edgeQuarterPt, quarterPt) :=
    fun h => by
      have h' := congrArg (fun z : edgeObj.left × Band quarter => (z.2 : ℝ)) h
      change (0 : ℝ) = quarter at h'
      rw [coe_quarter] at h'
      norm_num at h'
  have hmk : ReebQuotient.mk (height (overBaseMap edgeObj) quarter) (edgePt, zeroQ) =
      ReebQuotient.mk (height (overBaseMap edgeObj) quarter) (edgeQuarterPt, quarterPt) :=
    ReebQuotient.mk_eq_mk_of_path _ edgeFiberPath fun r => by
      show (1 / 2 - (r : ℝ) / 4) + (r : ℝ) / 4 = 1 / 2 + 0
      ring
  have hinv : ∀ z, (inv ((ReebQuotient.projNatTrans ℝ).app
      ((functor quarter).obj edgeObj))).left.hom
        (ReebQuotient.mk (height (overBaseMap edgeObj) quarter) z) = z := fun z =>
    congrArg (fun φ => φ.left.hom z)
      (IsIso.hom_inv_id ((ReebQuotient.projNatTrans ℝ).app ((functor quarter).obj edgeObj)))
  exact hne ((hinv _).symm.trans ((congrArg _ hmk).trans (hinv _)))

/-! ### Graph-object control -/

/-- **`ℛ A ≅ A` used explicitly.** On the parallel edges with `ε = 1/4`, the inverse of the
absorption morphism is `ℛ T_(1/4)` of the inverse of `projNatIso`, and it sends
`[([q_true], 1/4)]` to `[(q_true, 1/4)]`, computed through that description and through the general
inverse formula. -/
theorem par_absorption_inv :
    inv ((ℛ).map ((functor quarter).map
        ((ReebQuotient.projNatTrans ℝ).app parallelGraph.obj))) =
        (ℛ).map ((functor quarter).map (projNatIso.inv.app parallelGraph)) ∧
      ((ℛ).map ((functor quarter).map (projNatIso.inv.app parallelGraph))).left.hom
          (ReebQuotient.mk (height (overBaseMap ((ℛ).obj parObj)) quarter)
            (ReebQuotient.mk (overBaseMap parObj) (parPt true), quarterPt)) =
        ReebQuotient.mk (height (overBaseMap parObj) quarter) (parPt true, quarterPt) ∧
      (inv ((ℛ).map ((functor quarter).map
          ((ReebQuotient.projNatTrans ℝ).app parallelGraph.obj)))).left.hom
          (ReebQuotient.mk (height (overBaseMap ((ℛ).obj parObj)) quarter)
            (ReebQuotient.mk (overBaseMap parObj) (parPt true), quarterPt)) =
        ReebQuotient.mk (height (overBaseMap parObj) quarter) (parPt true, quarterPt) := by
  have hp : (projNatIso.inv.app parallelGraph).left.hom
      (ReebQuotient.mk (overBaseMap parObj) (parPt true)) = parPt true :=
    congrArg (fun φ => φ.left.hom (parPt true)) (projNatIso.hom_inv_id_app parallelGraph)
  have h₂ : ((ℛ).map ((functor quarter).map (projNatIso.inv.app parallelGraph))).left.hom
      (ReebQuotient.mk (height (overBaseMap ((ℛ).obj parObj)) quarter)
        (ReebQuotient.mk (overBaseMap parObj) (parPt true), quarterPt)) =
      ReebQuotient.mk (height (overBaseMap parObj) quarter) (parPt true, quarterPt) :=
    congrArg (fun x => ReebQuotient.mk (height (overBaseMap parObj) quarter) (x, quarterPt)) hp
  exact ⟨inv_quotientFunctor_map_functor_map_projNatTrans_app_of_isRGraph parallelGraph quarter,
    h₂, absorption_inv_mk (isConstructibleSpace_of_isRGraph parallelGraph.property) quarter
      (isRGraph_quotient_of_isConstructibleSpace
        (isConstructibleSpace_thickening parallelGraph.property quarter)) (parPt true) quarterPt⟩

/-! ### Boundary control: `ε = 0` -/

/-- `ℛ q_X = q_(ℛ X)` for every object of the real slice, in particular for every constructible
one: both send `[x]` to `[[x]]`. At `ε = 0` the absorption morphism is `ℛ (T_0 q_X)`, which
`zeroIso` identifies with `ℛ q_X`. -/
theorem quotientFunctor_map_projNatTrans_app (X : Over (TopCat.of ℝ)) :
    (ℛ).map ((ReebQuotient.projNatTrans ℝ).app X) =
      (ReebQuotient.projNatTrans ℝ).app ((ℛ).obj X) := by
  ext q
  induction q using ReebQuotient.ind with
  | h x => rfl

/-- **Left unit law at a representative.** On the point, `U_0 U_1 P ≅ U_(0+1) P ≅ U_1 P` sends
`[([(*, s)], 0)]` to `[(*, s)]`. -/
theorem point_compIso_zero_left_apply (x : pointGraph.obj.left) (s : Band 1) :
    ((geometricSmoothingCompIso 0 1 ≪≫ geometricSmoothingEqIso (zero_add 1)).hom.app
        pointGraph).hom.left.hom
        (ReebQuotient.mk (height (overBaseMap ((geometricSmoothing 1).obj pointGraph).obj) 0)
          (ReebQuotient.mk (height (overBaseMap pointGraph.obj) 1) (x, s),
            ⟨0, zero_mem_band 0⟩)) =
      ReebQuotient.mk (height (overBaseMap pointGraph.obj) 1) (x, s) := by
  rw [geometricSmoothingCompIso_zero_left]
  exact geometricSmoothingZeroIso_hom_app_hom_left_mk _ _ _

/-! ### One edge -/

/-- The class `[([(q, 1/4)], 1/4)]` in `U_(1/4) U_(1/4)` of the edge. -/
def edgeCls : ((geometricSmoothing quarter).obj ((geometricSmoothing quarter).obj
    singleGraph)).obj.left :=
  ReebQuotient.mk (height (overBaseMap ((geometricSmoothing quarter).obj singleGraph).obj) quarter)
    (ReebQuotient.mk (height (overBaseMap edgeObj) quarter) (edgePt, quarterPt), quarterPt)

/-- **The semigroup on the edge**: `[([(q, 1/4)], 1/4)] ↦ [(q, 1/2)]`, and the inverse returns
`[([(q, 1/4)], 1/4)]`, the clamp of `1/2` onto `[-1/4, 1/4]` being `1/4`. -/
theorem edge_compIso_apply :
    ((geometricSmoothingCompIso quarter quarter).hom.app singleGraph).hom.left.hom edgeCls =
        ReebQuotient.mk (height (overBaseMap edgeObj) (quarter + quarter)) (edgePt, halfPt) ∧
      ((geometricSmoothingCompIso quarter quarter).inv.app singleGraph).hom.left.hom
          (ReebQuotient.mk (height (overBaseMap edgeObj) (quarter + quarter)) (edgePt, halfPt)) =
        edgeCls := by
  refine ⟨(geometricSmoothingCompIso_hom_app_hom_left_mk quarter quarter singleGraph
    (edgePt, quarterPt) quarterPt).trans (congrArg (ReebQuotient.mk _) (Prod.ext rfl
      (Subtype.ext (show (quarter : ℝ) + quarter = 1 / 2 by rw [coe_quarter]; norm_num)))), ?_⟩
  have hc : (projIcc (-(quarter : ℝ)) quarter (neg_le_band quarter) (1 / 2) : ℝ) = 1 / 4 := by
    rw [coe_projIcc, coe_quarter, min_eq_left (by norm_num), max_eq_right (by norm_num)]
  have hσ : addSection edgeObj.left quarter quarter (edgePt, halfPt) =
      ((edgePt, quarterPt), quarterPt) := by
    refine Prod.ext (Prod.ext rfl (Subtype.ext ?_)) (Subtype.ext ?_)
    · show (projIcc (-(quarter : ℝ)) quarter (neg_le_band quarter) (1 / 2) : ℝ) = quarter
      rw [hc, coe_quarter]
    · show (1 / 2 : ℝ) - (projIcc (-(quarter : ℝ)) quarter (neg_le_band quarter) (1 / 2) : ℝ) =
        quarter
      rw [hc, coe_quarter]
      norm_num
  refine (geometricSmoothingCompIso_inv_app_hom_left_mk quarter quarter singleGraph
    (edgePt, halfPt)).trans ?_
  exact congrArg (fun w : (edgeObj.left × Band quarter) × Band quarter =>
    ReebQuotient.mk (height (overBaseMap ((geometricSmoothing quarter).obj singleGraph).obj)
      quarter) (ReebQuotient.mk (height (overBaseMap edgeObj) quarter) w.1, w.2)) hσ

/-- The class `[([([(q, 1/4)], 1/4)], 1/4)]` in `U_(1/4) U_(1/4) U_(1/4)` of the edge. -/
def edgeCls₃ : ((geometricSmoothing quarter).obj ((geometricSmoothing quarter).obj
    ((geometricSmoothing quarter).obj singleGraph))).obj.left :=
  ReebQuotient.mk (height (overBaseMap ((geometricSmoothing quarter).obj
    ((geometricSmoothing quarter).obj singleGraph)).obj) quarter) (edgeCls, quarterPt)

/-- **Associativity on the edge.** At `[([([(q, 1/4)], 1/4)], 1/4)]` both sides of
`geometricSmoothingCompIso_assoc` give `[(q, 3/4)]`. -/
theorem edge_compIso_assoc :
    ((Functor.isoWhiskerLeft (geometricSmoothing quarter)
          (geometricSmoothingCompIso quarter quarter) ≪≫
        geometricSmoothingCompIso (quarter + quarter) quarter ≪≫
          geometricSmoothingEqIso (add_assoc quarter quarter quarter)).hom.app
          singleGraph).hom.left.hom edgeCls₃ =
        ReebQuotient.mk (height (overBaseMap edgeObj) (quarter + (quarter + quarter)))
          (edgePt, threeQuarterPt) ∧
      ((Functor.isoWhiskerRight (geometricSmoothingCompIso quarter quarter)
          (geometricSmoothing quarter) ≪≫
          geometricSmoothingCompIso quarter (quarter + quarter)).hom.app
          singleGraph).hom.left.hom edgeCls₃ =
        ReebQuotient.mk (height (overBaseMap edgeObj) (quarter + (quarter + quarter)))
          (edgePt, threeQuarterPt) := by
  have e3 := geometricSmoothingCompIso_hom_app_hom_left_mk quarter quarter singleGraph
    (edgePt, quarterPt) quarterPt
  have e4 := geometricSmoothingCompIso_hom_app_hom_left_mk quarter (quarter + quarter) singleGraph
    (addMap edgeObj.left quarter quarter ((edgePt, quarterPt), quarterPt)) quarterPt
  have hR : ((Functor.isoWhiskerRight (geometricSmoothingCompIso quarter quarter)
      (geometricSmoothing quarter) ≪≫
        geometricSmoothingCompIso quarter (quarter + quarter)).hom.app
        singleGraph).hom.left.hom edgeCls₃ =
      ReebQuotient.mk (height (overBaseMap edgeObj) (quarter + (quarter + quarter)))
        (edgePt, threeQuarterPt) :=
    ((congrArg (fun w => ((geometricSmoothingCompIso quarter (quarter + quarter)).hom.app
      singleGraph).hom.left.hom (ReebQuotient.mk _ (w, quarterPt))) e3).trans e4).trans
      (congrArg (ReebQuotient.mk _) (Prod.ext rfl (Subtype.ext
        (show (quarter : ℝ) + quarter + quarter = 3 / 4 by rw [coe_quarter]; norm_num))))
  exact ⟨(congrArg (fun φ => (φ.hom.app singleGraph).hom.left.hom edgeCls₃)
    (geometricSmoothingCompIso_assoc quarter quarter quarter)).trans hR, hR⟩

/-- **The cosheaf square on the edge at `⊤`.** On the class of `[([(q, 1/4)], 1/4)]` both sides of
`cosheafFunctor_map_geometricSmoothingCompIso_hom_app` give the class of `q`. -/
theorem edge_cosheaf_square_top :
    ((cosheafFunctor.map ((geometricSmoothingCompIso quarter quarter).hom.app singleGraph)).hom ≫
        ((geometricSmoothingComparisonIso (quarter + quarter)).hom.app singleGraph).hom).app ⊤
        (ZerothHomotopy.mk ⟨edgeCls, Set.mem_univ _⟩) =
        ZerothHomotopy.mk (⟨edgePt, (by rw [thicken_top]; exact Set.mem_univ _)⟩ :
          {x : edgeObj.left // overBaseMap edgeObj x ∈ thicken (quarter + quarter) ⊤}) ∧
      (((geometricSmoothingComparisonIso quarter).hom.app
          ((geometricSmoothing quarter).obj singleGraph)).hom ≫
        (smoothing quarter).map ((geometricSmoothingComparisonIso quarter).hom.app
          singleGraph).hom ≫
          (smoothingCompIso quarter quarter).hom.app
            (intervalComponentsOver.obj singleGraph.obj)).app ⊤
        (ZerothHomotopy.mk ⟨edgeCls, Set.mem_univ _⟩) =
        ZerothHomotopy.mk (⟨edgePt, (by rw [thicken_top]; exact Set.mem_univ _)⟩ :
          {x : edgeObj.left // overBaseMap edgeObj x ∈ thicken (quarter + quarter) ⊤}) := by
  have r1 := geometricSmoothingComparisonIso_hom_app_hom_app_mk quarter
    ((geometricSmoothing quarter).obj singleGraph) ⊤
    ⟨(ReebQuotient.mk (height (overBaseMap edgeObj) quarter) (edgePt, quarterPt), quarterPt),
      Set.mem_univ _⟩
  have r2 := geometricSmoothingComparisonIso_hom_app_hom_app_mk quarter singleGraph
    (thicken quarter ⊤) ⟨(edgePt, quarterPt), (by rw [thicken_top]; exact Set.mem_univ _)⟩
  have hR : (((geometricSmoothingComparisonIso quarter).hom.app
          ((geometricSmoothing quarter).obj singleGraph)).hom ≫
        (smoothing quarter).map ((geometricSmoothingComparisonIso quarter).hom.app
          singleGraph).hom ≫
          (smoothingCompIso quarter quarter).hom.app
            (intervalComponentsOver.obj singleGraph.obj)).app ⊤
        (ZerothHomotopy.mk ⟨edgeCls, Set.mem_univ _⟩) =
        ZerothHomotopy.mk (⟨edgePt, (by rw [thicken_top]; exact Set.mem_univ _)⟩ :
          {x : edgeObj.left // overBaseMap edgeObj x ∈ thicken (quarter + quarter) ⊤}) :=
    (congrArg (fun w =>
      ((smoothingCompIso quarter quarter).hom.app (intervalComponentsOver.obj singleGraph.obj)).app
        ⊤ (((geometricSmoothingComparisonIso quarter).hom.app singleGraph).hom.app
          (thicken quarter ⊤) w)) r1).trans
      (congrArg (fun w =>
        ((smoothingCompIso quarter quarter).hom.app
          (intervalComponentsOver.obj singleGraph.obj)).app ⊤ w) r2)
  exact ⟨(ConcreteCategory.congr_hom (NatTrans.congr_app
    (cosheafFunctor_map_geometricSmoothingCompIso_hom_app quarter quarter singleGraph) ⊤)
    (ZerothHomotopy.mk ⟨edgeCls, Set.mem_univ _⟩)).trans hR, hR⟩

/-! ### Two merging edges -/

/-- The class `[([(q_b, 1/4)], -1/4)]` in `U_(1/4) U_(1/4)` of the parallel edges, at height
`1/2`. -/
def parCls (b : Bool) : ((geometricSmoothing quarter).obj ((geometricSmoothing quarter).obj
    parallelGraph)).obj.left :=
  ReebQuotient.mk (height (overBaseMap ((geometricSmoothing quarter).obj parallelGraph).obj)
    quarter) (ReebQuotient.mk (height (overBaseMap parObj) quarter) (parPt b, quarterPt),
      negQuarterPt)

theorem height_parCls (b : Bool) :
    overBaseMap ((geometricSmoothing quarter).obj ((geometricSmoothing quarter).obj
      parallelGraph)).obj (parCls b) = 1 / 2 :=
  height_parZ b

/-- **The loop dies at `1/4 + 1/4`.** The height-`1/2` fibre of `U_(1/4) U_(1/4)` of the parallel
edges is a subsingleton, transported from `U_(1/4 + 1/4)` through the height-preserving
`geometricSmoothingCompIso`. -/
theorem par_comp_fiber_subsingleton :
    Subsingleton (overBaseMap ((geometricSmoothing quarter).obj ((geometricSmoothing quarter).obj
      parallelGraph)).obj ⁻¹' {1 / 2}) := by
  have hε : 1 / 2 ≤ ((quarter + quarter : ℝ≥0) : ℝ) := by
    rw [NNReal.coe_add, coe_quarter]
    norm_num
  exact fiber_subsingleton_of_iso ((geometricSmoothingCompIso quarter quarter).app parallelGraph)
    _ (parallel_smoothed_fiber_subsingleton hε (1 / 2))

/-- **The second smoothing makes the identification.** In `U_(1/4) U_(1/4)` the classes over the
two edges at height `1/2` agree, although the edge points differ, while the height-`1/2` fibre of
the single smoothing `U_(1/4)` is not a subsingleton. -/
theorem par_comp_classes_eq :
    parPt false ≠ parPt true ∧ parCls false = parCls true ∧
      ¬ Subsingleton (overBaseMap ((geometricSmoothing Examples.ConstructibleSmoothing.quarter).obj
        parallelGraph).obj ⁻¹' {1 / 2}) :=
  ⟨parPt_false_ne_true, congrArg Subtype.val (par_comp_fiber_subsingleton.elim
    ⟨parCls false, height_parCls false⟩ ⟨parCls true, height_parCls true⟩),
    parallel_quarter_fiber_not_subsingleton⟩

/-- **The loop survives at `1/8 + 1/8`.** The height-`1/2` fibre of `U_(1/8) U_(1/8)` of the
parallel edges is not a subsingleton: by injectivity of absorption it would make the height-`1/2`
fibre of `ℛ T_(1/8) T_(1/8)` one, contradicting the merged `par_eighth_fiber_not_subsingleton`. -/
theorem par_eighth_comp_fiber_not_subsingleton :
    ¬ Subsingleton (overBaseMap ((geometricSmoothing eighth).obj ((geometricSmoothing eighth).obj
      parallelGraph)).obj ⁻¹' {1 / 2}) := fun h =>
  par_eighth_fiber_not_subsingleton (fiber_subsingleton_of_iso
    ((geometricSmoothingAbsorptionIso eighth eighth).app parallelGraph) _ h)

/-! ### Naturality on the edge swap -/

/-- **The swap square of the semigroup** at `[([(q_true, 1/4)], -1/4)]`: both composites give
`[(q_false, 1/4 - 1/4)]`, through the merged swap square of `geometricSmoothingAddIso`. The identity
image is the class of `μ (q_true, 1/4, -1/4)`, whose representative differs from
`(q_false, 1/4 - 1/4)`. (The classes themselves agree, the height-`1/2` fibre of `U_(1/4 + 1/4)`
being a subsingleton, so the square is detected on representatives.) -/
theorem swap_geometricSmoothingCompIso_square_apply :
    (((geometricSmoothing quarter ⋙ geometricSmoothing quarter).map swapGraph ≫
        (geometricSmoothingCompIso quarter quarter).hom.app parallelGraph).hom.left.hom
        (parCls true) =
        ReebQuotient.mk (height (overBaseMap parObj) (quarter + quarter)) (parPt false, parW)) ∧
      (((geometricSmoothingCompIso quarter quarter).hom.app parallelGraph ≫
        (geometricSmoothing (quarter + quarter)).map swapGraph).hom.left.hom (parCls true) =
        ReebQuotient.mk (height (overBaseMap parObj) (quarter + quarter)) (parPt false, parW)) ∧
      ((geometricSmoothingCompIso quarter quarter).hom.app parallelGraph).hom.left.hom
          (parCls true) =
        ReebQuotient.mk (height (overBaseMap parObj) (quarter + quarter))
          (addMap parObj.left quarter quarter (parZ true)) ∧
      ((parPt false, parW) : parObj.left × Band (quarter + quarter)) ≠
        addMap parObj.left quarter quarter (parZ true) := by
  have h₁ : ((geometricSmoothing quarter ⋙ geometricSmoothing quarter).map swapGraph ≫
      (geometricSmoothingCompIso quarter quarter).hom.app parallelGraph).hom.left.hom
        (parCls true) =
      ReebQuotient.mk (height (overBaseMap parObj) (quarter + quarter)) (parPt false, parW) :=
    (geometricSmoothingCompIso_hom_app_hom_left_mk quarter quarter parallelGraph
      (parPt false, quarterPt) negQuarterPt).trans swap_geometricSmoothingAddIso_square_apply.1
  exact ⟨h₁, (congrArg (fun φ => φ.hom.left.hom (parCls true))
    ((geometricSmoothingCompIso quarter quarter).hom.naturality swapGraph)).symm.trans h₁,
    geometricSmoothingCompIso_hom_app_hom_left_mk quarter quarter parallelGraph
      (parPt true, quarterPt) negQuarterPt, swap_image_ne⟩

/-! ### One point -/

/-- **The explicit isomorphism `U_1 U_1 P ≅ U_(1+1) P`** of the point in `RGraphCat`. Before the
Reeb quotient there is no slice isomorphism `T_1 T_1 P ≅ T_(1+1) P` (the merged
`GeometricThickening.not_iso_one_one`). -/
def pointCompIso :
    (geometricSmoothing 1).obj ((geometricSmoothing 1).obj pointGraph) ≅
      (geometricSmoothing (1 + 1)).obj pointGraph :=
  (geometricSmoothingCompIso 1 1).app pointGraph

end Examples.QuotientThickeningAbsorption

end

end TDA.Reeb
