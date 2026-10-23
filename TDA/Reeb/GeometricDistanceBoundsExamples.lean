import TDA.Reeb.GeometricDistanceBounds
import TDA.Reeb.GeometricEnlargementExamples

/-!
# Fixtures for geometric distance bounds

This module records the acceptance fixtures for the geometric distance bounds: exact distances for
the edge and a point under smoothing, distances between singleton graphs, the edge–midpoint value,
the smoothed height range, the empty boundary, the component obstruction, and the two parallel-edge
non-sharpness controls.

* **G1–G2.** Exact self-smoothing distances for the edge and the midpoint graph.
* **G3–G4.** Distances between singleton graphs and the edge–midpoint distance.
* **G5–G6.** The half-smoothed range and the empty-versus-nonempty boundary.
* **G7–G8.** The component obstruction and the parallel-edge range control.
-/

open Set Topology CategoryTheory
open scoped NNReal ENNReal Pointwise

namespace TDA.Reeb

noncomputable section

namespace Examples.GeometricDistanceBounds

open OpenInterval CylinderPresentation FiniteReebData RGraph
open TDA.Reeb.Examples.Cylinder (S01 S01_value_zero S01_value_one height_zero)
open TDA.Reeb.Examples.ConstructibleCylinder (S0 D0)
open TDA.Reeb.RGraph.Examples (singleEdge)
open TDA.Reeb.Examples.ConstructibleRepresentation (pt0)
open TDA.Reeb.Examples.RGraphCosheafEquivalence
  (singleGraph parallelGraph twoPointGraph emptyGraph collapseGraph)
open TDA.Reeb.Examples.RGraphSmoothing
  (singletonGraph singleton_subsingleton singleton_smoothed_subsingleton
    fiber_subsingleton_of_cosheaf)
open TDA.Reeb.Examples.RGraphThickening (single halfNN coe_halfNN)
open TDA.Reeb.Examples.GeometricInterleaving
  (midGraph midPt edgeTop height_edgeTop height_single_mem edgeMidInterleaving
    coe_halfNN_ennreal includeGraph)

/-! ### Common singleton calculations -/

/-- Every point of `singletonGraph a` has height `a`. -/
theorem height_singleton (a : ℝ) (x : (singletonGraph a).obj.left) :
    overBaseMap (singletonGraph a).obj x = a := by
  exact height_zero (single a) (ofFiniteData pt0) x

private theorem heightRange_singleton (a : ℝ) :
    heightRange (singletonGraph a) = {a} := by
  unfold heightRange
  ext t
  constructor
  · rintro ⟨x, rfl⟩
    simpa only [Set.mem_singleton_iff] using height_singleton a x
  · intro ht
    have ht' : t = a := by simpa only [Set.mem_singleton_iff] using ht
    subst t
    exact ⟨(ofFiniteData pt0).ofVertex (single a) 0 (), height_singleton a _⟩

private def pointThick {a b : ℝ} {ε : ℝ≥0} (h : |a - b| ≤ ε) :
    (singletonGraph a).obj ⟶
      (GeometricThickening.functor ε).obj (singletonGraph b).obj := by
  have hband : a - b ∈ GeometricThickening.Band ε := abs_le.mp h
  refine Over.homMk (TopCat.ofHom
    ⟨fun _ => ((ofFiniteData pt0).ofVertex (single b) 0 (), ⟨a - b, hband⟩),
      continuous_const.prodMk continuous_const⟩) ?_
  ext x
  show overBaseMap (singletonGraph b).obj
      ((ofFiniteData pt0).ofVertex (single b) 0 ()) + (a - b) =
    overBaseMap (singletonGraph a).obj x
  have hb : overBaseMap (singletonGraph b).obj
      ((ofFiniteData pt0).ofVertex (single b) 0 ()) = b := by
    exact height_zero (single b) (ofFiniteData pt0) _
  rw [hb, height_singleton a x]
  ring

/-! ### G1 and G2: exact self-smoothing distances -/

/-- The single edge has geometric distance `1 / 2` from its half-smoothing. -/
theorem geometricInterleavingDistance_single_smoothing_half :
    geometricInterleavingDistance singleGraph
        ((geometricSmoothing halfNN).obj singleGraph) = 1 / 2 := by
  have : Nonempty singleGraph.obj.left := ⟨edgeTop⟩
  simpa only [coe_halfNN_ennreal] using
    (geometricInterleavingDistance_geometricSmoothing_self halfNN singleGraph)

/-- The point graph has geometric distance `ε` from its `ε`-smoothing, for every `ε`. -/
theorem geometricInterleavingDistance_mid_smoothing (ε : ℝ≥0) :
    geometricInterleavingDistance midGraph ((geometricSmoothing ε).obj midGraph) = ε := by
  have : Nonempty midGraph.obj.left := ⟨midPt⟩
  exact geometricInterleavingDistance_geometricSmoothing_self ε midGraph

/-! ### G3: singleton graphs -/

/-- The geometric `ε`-interleaving of the singleton graphs at heights `a` and `b`, for
`|a - b| ≤ ε`: each vertex goes to the point of the other smoothed singleton at the matching height. -/
def pointInterleaving {a b : ℝ} {ε : ℝ≥0} (h : |a - b| ≤ ε) :
    GeometricInterleaving ε (singletonGraph a) (singletonGraph b) := by
  have h' : |b - a| ≤ ε := by simpa [abs_sub_comm] using h
  refine
    { φ := ObjectProperty.homMk
        (pointThick (a := a) (b := b) h ≫
          (ReebQuotient.projNatTrans ℝ).app
            ((GeometricThickening.functor ε).obj (singletonGraph b).obj))
      ψ := ObjectProperty.homMk
        (pointThick (a := b) (b := a) h' ≫
          (ReebQuotient.projNatTrans ℝ).app
            ((GeometricThickening.functor ε).obj (singletonGraph a).obj))
      φ_ψ := hom_ext_of_fiber_subsingleton
        (fiber_subsingleton_of_cosheaf _
          (singleton_smoothed_subsingleton a (ε + ε)))
      ψ_φ := hom_ext_of_fiber_subsingleton
        (fiber_subsingleton_of_cosheaf _
          (singleton_smoothed_subsingleton b (ε + ε))) }

/-- The distance between singleton graphs at heights `a` and `b` is `|a - b|`. -/
theorem geometricInterleavingDistance_singleton {a b : ℝ} :
    geometricInterleavingDistance (singletonGraph a) (singletonGraph b) =
      ENNReal.ofReal |a - b| := by
  apply le_antisymm
  · apply geometricInterleavingDistance_le_iff.2
    intro ε hε
    have hε' : |a - b| < (ε : ℝ) :=
      (ENNReal.ofReal_lt_coe_iff (abs_nonneg _)).mp hε
    exact ⟨pointInterleaving (le_of_lt hε')⟩
  · have hdist := hausdorffEDist_heightRange_le_geometricInterleavingDistance
      (singletonGraph a) (singletonGraph b)
    have hleft : ENNReal.ofReal |a - b| ≤
        Metric.infEDist a (heightRange (singletonGraph b)) := by
      rw [heightRange_singleton, Metric.infEDist_singleton, edist_dist, Real.dist_eq]
    have hmem : a ∈ heightRange (singletonGraph a) := by
      rw [heightRange_singleton]
      exact Set.mem_singleton a
    exact hleft.trans ((Metric.infEDist_le_hausdorffEDist_of_mem hmem).trans hdist)

/-- The singleton graphs at heights `0` and `1` have distance `1`. -/
theorem geometricInterleavingDistance_singleton_zero_one :
    geometricInterleavingDistance (singletonGraph 0) (singletonGraph 1) = 1 := by
  rw [geometricInterleavingDistance_singleton]
  norm_num

/-! ### G4: the edge and its midpoint -/

/-- The single edge and its midpoint have geometric distance `1 / 2`; the lower bound is the
Hausdorff range obstruction at `edgeTop`, agreeing with `geometricInterleavingDistance_edge_mid`. -/
theorem geometricInterleavingDistance_single_mid :
    geometricInterleavingDistance singleGraph midGraph = 1 / 2 := by
  apply le_antisymm
  · rw [← coe_halfNN_ennreal]
    exact edgeMidInterleaving.geometricInterleavingDistance_le
  · have hdist := hausdorffEDist_heightRange_le_geometricInterleavingDistance
      singleGraph midGraph
    have htop : (1 : ℝ) ∈ heightRange singleGraph := ⟨edgeTop, height_edgeTop⟩
    have hleft : ENNReal.ofReal |(1 : ℝ) - 1 / 2| ≤
        Metric.infEDist (1 : ℝ) (heightRange midGraph) := by
      rw [heightRange_singleton, Metric.infEDist_singleton, edist_dist, Real.dist_eq]
    have hfull := hleft.trans ((Metric.infEDist_le_hausdorffEDist_of_mem htop).trans hdist)
    norm_num at hfull
    have hhalf : ENNReal.ofReal ((1 / 2 : ℝ)) = (1 / 2 : ℝ≥0∞) := by
      rw [ENNReal.ofReal_div_of_pos zero_lt_two, ENNReal.ofReal_one,
        ENNReal.ofReal_ofNat]
    rw [hhalf] at hfull
    exact hfull

/-! ### G5: the smoothed range -/

/-- The height range of the half-smoothed edge is contained in `Icc (-1 / 2) (3 / 2)`. -/
theorem heightRange_single_smoothing_half_subset :
    heightRange ((geometricSmoothing halfNN).obj singleGraph) ⊆ Icc (-1 / 2 : ℝ) (3 / 2) := by
  rw [heightRange_geometricSmoothing]
  rintro _ hz
  obtain ⟨x, hx, t, ht, rfl⟩ := Set.mem_add.1 hz
  obtain ⟨y, rfl⟩ := hx
  have hx' := height_single_mem y
  rw [coe_halfNN] at ht
  obtain ⟨ht1, ht2⟩ := ht
  obtain ⟨hx1, hx2⟩ := hx'
  constructor <;> linarith

/-- The lower endpoint `-1 / 2` belongs to the half-smoothed edge height range. -/
theorem neg_half_mem_heightRange_single_smoothing_half :
    (-1 / 2 : ℝ) ∈ heightRange ((geometricSmoothing halfNN).obj singleGraph) := by
  rw [heightRange_geometricSmoothing]
  refine Set.mem_add.2 ⟨0, ?_, -(1 / 2 : ℝ), ?_, by norm_num⟩
  · let x₀ : singleGraph.obj.left := (ofFiniteData singleEdge).ofVertex S01 0 ()
    refine ⟨x₀, ?_⟩
    change (ofFiniteData singleEdge).height S01
      ((ofFiniteData singleEdge).ofVertex S01 0 ()) = 0
    exact S01_value_zero
  · rw [coe_halfNN]
    norm_num

/-- The upper endpoint `3 / 2` belongs to the half-smoothed edge height range. -/
theorem three_halves_mem_heightRange_single_smoothing_half :
    (3 / 2 : ℝ) ∈ heightRange ((geometricSmoothing halfNN).obj singleGraph) := by
  rw [heightRange_geometricSmoothing]
  refine Set.mem_add.2 ⟨1, ⟨edgeTop, height_edgeTop⟩, (1 / 2 : ℝ), ?_, by norm_num⟩
  rw [coe_halfNN]
  norm_num

/-! ### G6: the empty boundary -/

/-- The empty graph and the midpoint have infinite geometric interleaving distance. -/
theorem geometricInterleavingDistance_empty_mid :
    geometricInterleavingDistance emptyGraph midGraph = ⊤ := by
  have : IsEmpty emptyGraph.obj.left :=
    TDA.Reeb.RGraph.Examples.emptyData_realization_isEmpty 0 S0
  have : Nonempty midGraph.obj.left := ⟨midPt⟩
  exact geometricInterleavingDistance_eq_top_of_isEmpty_of_nonempty
    (A := emptyGraph) (B := midGraph) inferInstance inferInstance

/-! ### G7: the component obstruction -/

/-- The two-point graph has height range `{0}`. -/
theorem heightRange_twoPoint : heightRange twoPointGraph = {0} := by
  unfold heightRange
  ext t
  constructor
  · rintro ⟨x, rfl⟩
    have hx : overBaseMap twoPointGraph.obj x = 0 :=
      height_zero S0 (ofFiniteData D0) x
    simpa only [Set.mem_singleton_iff] using hx
  · intro ht
    have ht' : t = 0 := by simpa only [Set.mem_singleton_iff] using ht
    subst t
    exact ⟨(ofFiniteData D0).ofVertex S0 0 (0 : Fin 2), height_zero S0 (ofFiniteData D0) _⟩

/-- The singleton graph at height `0` has height range `{0}`. -/
theorem heightRange_singleton_zero : heightRange (singletonGraph 0) = {0} :=
  heightRange_singleton 0

/-- The two-point graph and the singleton graph at `0` have infinite geometric distance, by the
component obstruction at `⊤`. -/
theorem geometricInterleavingDistance_twoPoint_singleton :
    geometricInterleavingDistance twoPointGraph (singletonGraph 0) = ⊤ := by
  have : Subsingleton (singletonGraph (0 : ℝ)).obj.left := singleton_subsingleton 0
  apply geometricInterleavingDistance_eq_top_of_isEmpty_equiv
  refine ⟨fun e => ?_⟩
  have hsub : Subsingleton ((cosheafFunctor.obj (singletonGraph 0)).obj.obj ⊤) := by
    change Subsingleton
      ((intervalComponents (overBaseMap (singletonGraph (0 : ℝ)).obj)).obj ⊤)
    exact ⟨fun c d => by
      induction c using ZerothHomotopy.rec with
      | mk x =>
        induction d using ZerothHomotopy.rec with
        | mk y =>
          exact congrArg ZerothHomotopy.mk (Subtype.ext (Subsingleton.elim _ _))⟩
  have htwo : Subsingleton ((cosheafFunctor.obj twoPointGraph).obj.obj ⊤) :=
    e.subsingleton_congr.mpr hsub
  have hcard_ne_zero : Nat.card ((cosheafFunctor.obj twoPointGraph).obj.obj ⊤) ≠ 0 := by
    rw [TDA.Reeb.Examples.RGraphCosheafEquivalence.twoPoint_card_top]
    norm_num
  have hnonempty : Nonempty ((cosheafFunctor.obj twoPointGraph).obj.obj ⊤) :=
    (Nat.card_ne_zero.mp hcard_ne_zero).1
  have hone : Nat.card ((cosheafFunctor.obj twoPointGraph).obj.obj ⊤) = 1 :=
    Nat.card_eq_one_iff_unique.mpr ⟨htwo, hnonempty⟩
  rw [TDA.Reeb.Examples.RGraphCosheafEquivalence.twoPoint_card_top] at hone
  norm_num at hone

/-! ### G8: parallel edges versus one edge -/

private theorem heightRange_subset_of_hom {A B : RGraphCat} (f : A ⟶ B) :
    heightRange A ⊆ heightRange B := by
  unfold heightRange
  rintro _ ⟨x, rfl⟩
  exact ⟨f.hom.left.hom x, overBaseMap_comm f.hom x⟩

/-- The parallel-edge and single-edge height ranges have Hausdorff edistance `0`. -/
theorem hausdorffEDist_heightRange_parallel_single :
    Metric.hausdorffEDist (heightRange parallelGraph) (heightRange singleGraph) = 0 := by
  have hr : heightRange parallelGraph = heightRange singleGraph := by
    apply Set.Subset.antisymm
    · exact heightRange_subset_of_hom collapseGraph
    · exact heightRange_subset_of_hom includeGraph
  rw [hr]
  exact Metric.hausdorffEDist_self

/-- There is no geometric `0`-interleaving between the parallel-edge and single-edge graphs. -/
theorem parallel_single_zero_isEmpty :
    IsEmpty (GeometricInterleaving 0 parallelGraph singleGraph) :=
  TDA.Reeb.Examples.GeometricInterleaving.parallelSingle_zero_isEmpty

/-- The geometric distance from the parallel-edge graph to the single edge is at most `1 / 4`. -/
theorem geometricInterleavingDistance_parallel_single_le :
    geometricInterleavingDistance parallelGraph singleGraph ≤ 1 / 4 :=
  TDA.Reeb.Examples.GeometricInterleaving.geometricInterleavingDistance_parallel_single_le

/-- The parallel-edge range bound is `0`, but it is not witnessed by a `0`-interleaving; the
existing geometric witness gives the upper bound `1 / 4`. -/
theorem parallel_single_range_bound_not_witnessed :
    IsEmpty (GeometricInterleaving 0 parallelGraph singleGraph) ∧
      geometricInterleavingDistance parallelGraph singleGraph ≤ 1 / 4 :=
  ⟨parallel_single_zero_isEmpty, geometricInterleavingDistance_parallel_single_le⟩

end Examples.GeometricDistanceBounds

end

end TDA.Reeb
