import TDA.Reeb.ConstructibleHom
import TDA.Reeb.ConstructibleSpaceExamples
import TDA.Topology.QuotientProductExamples

/-!
# Presentation morphism fixtures

Fixtures for `TDA.Reeb.CylinderPresentation.Hom`, at the two levels `S01 = {0, 1}`.

* A collapse. Two disjoint segments map onto two parallel edges between single vertices,
  collapsing both vertex pieces (`collapse`). The realized map identifies the two vertex points at
  level `0` (`realize_collapse_glues`), so it is not injective, while it is injective on each
  regular fiber (`realize_collapse_strip`). It preserves height (`height_realize`).
* A non-Hausdorff presentation. `sierpSeg` has the Sierpiński space `Prop` as every piece and the
  identity as both endpoint maps; its realization is not Hausdorff (`not_t2Space_sierpSeg`).
  The discrete segments map into it (`twoSegToSierp`), it maps onto a single segment
  (`sierpToPoint`), and the realization of the composite is the composite of the realizations
  (`realize_twoSegToPoint`). Its thickened raw pieces still present `X × [-1, 1]` as a quotient
  (`isQuotientMap_rawBandMap_sierpSeg`).
* Empty pieces. The presentation with all pieces empty maps uniquely to every presentation
  (`fromEmpty`, `fromEmpty_unique`).
-/

open Set Topology
open scoped NNReal

namespace TDA.Reeb.Examples.CylinderHom

noncomputable section

open TDA.Reeb CylinderPresentation TDA.Reeb.Examples.Cylinder

/-! ### A collapse of finite data -/

/-- A single segment: one point at each level and one edge. -/
def pointSegData : FiniteReebData.{0} 1 :=
  ⟨fun _ => Unit, fun _ => Unit, fun _ => inferInstance, fun _ => inferInstance,
    fun _ _ => (), fun _ _ => ()⟩

/-- Collapse each vertex piece of two disjoint segments to a point, keeping both edges. -/
def collapseData : twoSegData.Hom parallelData where
  v _ _ := ()
  e _ y := y
  left_comm _ _ := rfl
  right_comm _ _ := rfl

/-- The collapse as a presentation morphism. -/
abbrev collapse : (ofFiniteData twoSegData).Hom (ofFiniteData parallelData) :=
  collapseData.toPresentationHom

/-- The two vertex points at level `0` are distinct before the collapse. -/
theorem twoSeg_ofVertex_ne :
    (ofFiniteData twoSegData).ofVertex S01 0 false ≠ (ofFiniteData twoSegData).ofVertex S01 0 true :=
  fun h => Bool.false_ne_true ((ofFiniteData twoSegData).ofVertex_injective S01 0 h)

/-- After the collapse they are identified. -/
theorem realize_collapse_glues :
    collapse.realize S01 ((ofFiniteData twoSegData).ofVertex S01 0 false) =
      collapse.realize S01 ((ofFiniteData twoSegData).ofVertex S01 0 true) := rfl

theorem realize_collapse_not_injective : ¬ Function.Injective (collapse.realize S01) :=
  fun h => twoSeg_ofVertex_ne (h realize_collapse_glues)

/-- Regular points of the two segments stay apart. -/
theorem realize_collapse_strip :
    collapse.realize S01 ((ofFiniteData twoSegData).ofStrip S01 0 (false, half)) ≠
      collapse.realize S01 ((ofFiniteData twoSegData).ofStrip S01 0 (true, half)) := by
  rw [Hom.realize_ofStrip, Hom.realize_ofStrip]
  exact fun h => Bool.false_ne_true (congrArg Prod.fst
    ((ofFiniteData parallelData).ofStrip_injective S01 0 h))

/-- The collapse agrees with the finite realization `realizeHom`. -/
example : collapse.realize S01 = realizeHom S01 collapseData :=
  realize_toPresentationHom S01 collapseData

/-! ### A non-Hausdorff presentation -/

/-- Every piece is the Sierpiński space `Prop`; both endpoint maps are the identity. -/
def sierpSeg : CylinderPresentation.{0} 1 where
  V _ := Prop
  E _ := Prop
  left _ := ContinuousMap.id _
  right _ := ContinuousMap.id _

/-- The realization of `sierpSeg` is not Hausdorff: it contains the vertex piece `Prop`. -/
theorem not_t2Space_sierpSeg : ¬ T2Space (sierpSeg.Realization S01) := fun _ =>
  TDA.Topology.Examples.not_t2Space_Prop (sierpSeg.isEmbedding_ofVertex S01 0).t2Space

/-- The thickened raw pieces of the non-Hausdorff presentation present its thickening. -/
theorem isQuotientMap_rawBandMap_sierpSeg :
    IsQuotientMap (Prod.map (sierpSeg.quotMk S01) id :
      sierpSeg.Raw S01 × GeometricThickening.Band 1 →
        sierpSeg.Realization S01 × GeometricThickening.Band 1) :=
  sierpSeg.isQuotientMap_rawBandMap S01 1

/-- The discrete segments map into `sierpSeg` by `b ↦ (b = true)`. -/
def twoSegToSierp : (ofFiniteData twoSegData).Hom sierpSeg where
  vertex i := ⟨fun b : (ofFiniteData twoSegData).V i => (b : Bool) = true,
    continuous_of_discreteTopology⟩
  edge e := ⟨fun b : (ofFiniteData twoSegData).E e => (b : Bool) = true,
    continuous_of_discreteTopology⟩
  left_comm _ _ := rfl
  right_comm _ _ := rfl

/-- `sierpSeg` maps onto a single segment. -/
def sierpToPoint : sierpSeg.Hom (ofFiniteData pointSegData) where
  vertex _ := ContinuousMap.const _ ()
  edge _ := ContinuousMap.const _ ()
  left_comm _ _ := rfl
  right_comm _ _ := rfl

/-- The realization of the composite through the non-Hausdorff presentation. -/
theorem realize_twoSegToPoint :
    (twoSegToSierp.comp sierpToPoint).realize S01 =
      (sierpToPoint.realize S01).comp (twoSegToSierp.realize S01) :=
  Hom.realize_comp S01 _ _

/-- The composite sends a regular point to the regular point of the single segment at the same
height. -/
theorem realize_twoSegToPoint_ofStrip (b : Bool) :
    (twoSegToSierp.comp sierpToPoint).realize S01 ((ofFiniteData twoSegData).ofStrip S01 0 (b, half)) =
      (ofFiniteData pointSegData).ofStrip S01 0 ((), half) := rfl

/-! ### Empty pieces -/

instance emptyData_isEmpty_E (n : ℕ) (e : Fin n) : IsEmpty ((ofFiniteData (emptyData n)).E e) :=
  inferInstanceAs (IsEmpty Empty)

/-- The presentation with all pieces empty maps to every presentation. -/
def fromEmpty {n : ℕ} (P : CylinderPresentation.{0} n) : (ofFiniteData (emptyData n)).Hom P where
  vertex _ := ⟨fun v => isEmptyElim v, continuous_of_discreteTopology⟩
  edge _ := ⟨fun y => isEmptyElim y, continuous_of_discreteTopology⟩
  left_comm _ y := isEmptyElim y
  right_comm _ y := isEmptyElim y

/-- That morphism is unique. -/
theorem fromEmpty_unique {n : ℕ} (P : CylinderPresentation.{0} n)
    (φ : (ofFiniteData (emptyData n)).Hom P) : φ = fromEmpty P :=
  Hom.ext (funext fun _ => ContinuousMap.ext fun v => isEmptyElim v)
    (funext fun _ => ContinuousMap.ext fun y => isEmptyElim y)

end

end TDA.Reeb.Examples.CylinderHom
