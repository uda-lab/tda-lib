import TDA.Reeb.GeometricEnlargement
import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Height-range and obstruction bounds for geometric interleavings

This module records the height-range and component obstructions for geometric interleavings of
graph objects, together with the exact distance from a graph object to its geometric smoothing.
These are library statements proved from the existing geometric interleaving API.  The
corresponding mathematical conventions are documented in
`docs/math/reeb-geometric-interleaving-equivalence.md`.
-/

open Set Topology CategoryTheory
open scoped NNReal ENNReal Pointwise

universe v

namespace TDA.Reeb

noncomputable section

namespace RGraph

open OpenInterval

/-! ### Height ranges -/

/-- The set of heights attained by a graph object. -/
def heightRange (A : RGraphCat) : Set ℝ := Set.range (overBaseMap A.obj)

/-- Every graph height range is contained in a bounded closed interval. -/
theorem heightRange_subset_Icc (A : RGraphCat) :
    ∃ a b : ℝ, heightRange A ⊆ Icc a b := by
  obtain ⟨m, T, D, ⟨e⟩⟩ := A.property
  refine ⟨T.value 0, T.value (Fin.last m), ?_⟩
  rintro _ ⟨x, rfl⟩
  rw [← overBaseMap_comm e.hom x]
  exact (CylinderPresentation.ofFiniteData D).height_mem_Icc T (e.hom.left.hom x)

/-- The height range of a graph object is bounded above. -/
theorem bddAbove_heightRange (A : RGraphCat) : BddAbove (heightRange A) := by
  obtain ⟨a, b, h⟩ := heightRange_subset_Icc A
  exact ⟨b, fun _ hx => (h hx).2⟩

/-- The height range of a graph object is bounded below. -/
theorem bddBelow_heightRange (A : RGraphCat) : BddBelow (heightRange A) := by
  obtain ⟨a, b, h⟩ := heightRange_subset_Icc A
  exact ⟨a, fun _ hx => (h hx).1⟩

/-- Isomorphic graph objects have equal height ranges. -/
theorem heightRange_eq_of_iso {A B : RGraphCat} (e : A ≅ B) :
    heightRange A = heightRange B := by
  ext t
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨e.hom.hom.left.hom x, overBaseMap_comm e.hom.hom x⟩
  · rintro ⟨x, rfl⟩
    exact ⟨e.inv.hom.left.hom x, overBaseMap_comm e.inv.hom x⟩

/-- The height range is nonempty exactly when the total space is nonempty. -/
theorem heightRange_nonempty_iff {A : RGraphCat} :
    (heightRange A).Nonempty ↔ Nonempty A.obj.left := by
  constructor
  · rintro ⟨_, ⟨x, rfl⟩⟩
    exact ⟨x⟩
  · rintro ⟨x⟩
    exact ⟨overBaseMap A.obj x, ⟨x, rfl⟩⟩

/-- Smoothing adds exactly the closed height band to the height range. -/
theorem heightRange_geometricSmoothing (ε : ℝ≥0) (A : RGraphCat) :
    heightRange ((geometricSmoothing ε).obj A) =
      heightRange A + Icc (-(ε : ℝ)) ε := by
  unfold heightRange
  rw [geometricSmoothing_obj_obj]
  ext q
  constructor
  · rintro ⟨q, rfl⟩
    obtain ⟨⟨x, t⟩, rfl⟩ := ReebQuotient.mk_surjective _ q
    show overBaseMap A.obj x + (t : ℝ) ∈ _
    exact Set.add_mem_add ⟨x, rfl⟩ t.2
  · intro hq
    obtain ⟨x, hx, t, ht, rfl⟩ := Set.mem_add.1 hq
    obtain ⟨x, rfl⟩ := hx
    refine ⟨ReebQuotient.mk _ (x, ⟨t, ht⟩), ?_⟩
    rfl

/-! ### Range obstruction -/

/-- A height-preserving map into a smoothing sends each source height within the smoothing band of
some height in the target range. -/
theorem exists_heightRange_near_of_hom {A B : RGraphCat} {ε : ℝ≥0}
    (φ : A ⟶ (geometricSmoothing ε).obj B) (x : A.obj.left) :
    ∃ y ∈ heightRange B, |overBaseMap A.obj x - y| ≤ ε := by
  have hx : overBaseMap A.obj x ∈ heightRange ((geometricSmoothing ε).obj B) :=
    ⟨φ.hom.left.hom x, overBaseMap_comm φ.hom x⟩
  rw [heightRange_geometricSmoothing] at hx
  obtain ⟨y, hy, t, ht, hyt⟩ := Set.mem_add.1 hx
  refine ⟨y, hy, ?_⟩
  rw [← hyt, add_sub_cancel_left]
  exact abs_le.2 ht

namespace GeometricInterleaving

variable {ε : ℝ≥0} {A B : RGraphCat}

/-- A geometric interleaving bounds the Hausdorff edistance of the two height ranges by its
parameter. -/
theorem hausdorffEDist_heightRange_le (i : GeometricInterleaving ε A B) :
    Metric.hausdorffEDist (heightRange A) (heightRange B) ≤ ε := by
  apply Metric.hausdorffEDist_le_of_mem_edist
  · intro z hz
    obtain ⟨x, rfl⟩ := hz
    obtain ⟨y, hy, hxy⟩ := exists_heightRange_near_of_hom i.φ x
    refine ⟨y, hy, ?_⟩
    simpa only [edist_dist, Real.dist_eq, ENNReal.ofReal_coe_nnreal] using
      ENNReal.ofReal_le_ofReal hxy
  · intro z hz
    obtain ⟨x, rfl⟩ := hz
    obtain ⟨y, hy, hxy⟩ := exists_heightRange_near_of_hom i.ψ x
    refine ⟨y, hy, ?_⟩
    simpa only [edist_dist, Real.dist_eq, ENNReal.ofReal_coe_nnreal] using
      ENNReal.ofReal_le_ofReal hxy

end GeometricInterleaving

/-- The Hausdorff edistance of height ranges is bounded by the geometric interleaving distance. -/
theorem hausdorffEDist_heightRange_le_geometricInterleavingDistance (A B : RGraphCat) :
    Metric.hausdorffEDist (heightRange A) (heightRange B) ≤
      geometricInterleavingDistance A B := by
  rw [le_geometricInterleavingDistance_iff]
  intro ε hε
  obtain ⟨i⟩ := hε
  exact i.hausdorffEDist_heightRange_le

/-- A graph with empty total space and a graph with nonempty total space have infinite geometric
interleaving distance. -/
theorem geometricInterleavingDistance_eq_top_of_isEmpty_of_nonempty
    {A B : RGraphCat} (hA : IsEmpty A.obj.left) (hB : Nonempty B.obj.left) :
    geometricInterleavingDistance A B = ⊤ := by
  have hRA : heightRange A = ∅ := by
    apply Set.not_nonempty_iff_eq_empty.mp
    intro h
    exact (not_nonempty_iff.mpr hA) (heightRange_nonempty_iff.mp h)
  have hRB : (heightRange B).Nonempty := heightRange_nonempty_iff.mpr hB
  have hzero : Metric.hausdorffEDist (heightRange A) (heightRange B) = ⊤ := by
    rw [hRA, Metric.hausdorffEDist_comm, Metric.hausdorffEDist_empty hRB]
  have hle := hausdorffEDist_heightRange_le_geometricInterleavingDistance A B
  rw [hzero] at hle
  exact top_unique hle

/-! ### Suprema of height ranges -/

/-- On the real line, the supremum difference of two nonempty bounded sets is bounded by their
Hausdorff edistance. -/
theorem ofReal_abs_sSup_sub_le_hausdorffEDist {s t : Set ℝ} (hs : s.Nonempty) (ht : t.Nonempty)
    (hs' : BddAbove s) (ht' : BddAbove t) :
    ENNReal.ofReal |sSup s - sSup t| ≤ Metric.hausdorffEDist s t := by
  have directional : ∀ (u v : Set ℝ), u.Nonempty → v.Nonempty → BddAbove u → BddAbove v →
      ENNReal.ofReal (sSup u - sSup v) ≤ Metric.hausdorffEDist u v := by
    intro u v hu hv hu' hv'
    refine ENNReal.le_of_forall_pos_le_add ?_
    intro δ hδ hH
    have hδ' : (0 : ℝ) < δ := by exact_mod_cast hδ
    obtain ⟨x, hx, hxs⟩ := exists_lt_of_lt_csSup hu (sub_lt_self _ hδ')
    have hpoint : ENNReal.ofReal (x - sSup v) ≤ Metric.infEDist x v := by
      apply (Metric.le_infEDist).2
      intro y hy
      rw [edist_dist, Real.dist_eq]
      exact ENNReal.ofReal_le_ofReal
        ((sub_le_sub_left (le_csSup hv' hy) x).trans (le_abs_self _))
    have hpoint' : ENNReal.ofReal (x - sSup v) ≤ Metric.hausdorffEDist u v :=
      hpoint.trans (Metric.infEDist_le_hausdorffEDist_of_mem hx)
    have hsup : sSup u - sSup v ≤ (x - sSup v) + (δ : ℝ) := by
      linarith
    calc
      ENNReal.ofReal (sSup u - sSup v) ≤
          ENNReal.ofReal ((x - sSup v) + (δ : ℝ)) :=
        ENNReal.ofReal_le_ofReal hsup
      _ ≤ ENNReal.ofReal (x - sSup v) + ENNReal.ofReal (δ : ℝ) :=
        ENNReal.ofReal_add_le
      _ ≤ Metric.hausdorffEDist u v + δ := by
        simpa only [ENNReal.ofReal_coe_nnreal, add_comm] using
          add_le_add_right hpoint' (δ : ℝ≥0∞)
  have hst := directional s t hs ht hs' ht'
  have hts := directional t s ht hs ht' hs'
  have hts' : ENNReal.ofReal (sSup t - sSup s) ≤ Metric.hausdorffEDist s t := by
    simpa only [Metric.hausdorffEDist_comm] using hts
  rcases le_total 0 (sSup s - sSup t) with h | h
  · simpa only [abs_of_nonneg h] using hst
  · simpa only [abs_of_nonpos h, neg_sub] using hts'

/-- On the real line, the infimum difference of two nonempty bounded sets is bounded by their
Hausdorff edistance. -/
theorem ofReal_abs_sInf_sub_le_hausdorffEDist {s t : Set ℝ} (hs : s.Nonempty) (ht : t.Nonempty)
    (hs' : BddBelow s) (ht' : BddBelow t) :
    ENNReal.ofReal |sInf s - sInf t| ≤ Metric.hausdorffEDist s t := by
  have h := ofReal_abs_sSup_sub_le_hausdorffEDist (s := -s) (t := -t) hs.neg ht.neg
    (bddAbove_neg.2 hs') (bddAbove_neg.2 ht')
  have hH : Metric.hausdorffEDist (-s) (-t) = Metric.hausdorffEDist s t := by
    rw [← Set.image_neg_eq_neg, ← Set.image_neg_eq_neg]
    exact Metric.hausdorffEDist_image
      (Isometry.of_dist_eq fun x y => by
        rw [Real.dist_eq, Real.dist_eq, neg_sub_neg, abs_sub_comm])
  have habs : |sInf s - sInf t| = |sSup (-s) - sSup (-t)| := by
    rw [Real.sInf_def, Real.sInf_def, ← abs_neg]
    congr 1
    ring
  rwa [habs, ← hH]

/-- The geometric interleaving distance from a graph object to its smoothing is exactly the
smoothing parameter. -/
theorem geometricInterleavingDistance_geometricSmoothing_self (ε : ℝ≥0) (A : RGraphCat)
    [Nonempty A.obj.left] :
    geometricInterleavingDistance A ((geometricSmoothing ε).obj A) = ε := by
  apply le_antisymm
  · exact geometricInterleavingDistance_geometricSmoothing_self_le ε A
  · have hs : (heightRange A).Nonempty := heightRange_nonempty_iff.mpr inferInstance
    have ht : (heightRange A + Icc (-(ε : ℝ)) ε).Nonempty :=
      hs.add (nonempty_Icc.mpr (GeometricThickening.neg_le_band ε))
    have hs' := bddAbove_heightRange A
    have ht' : BddAbove (heightRange A + Icc (-(ε : ℝ)) ε) :=
      hs'.add ⟨ε, fun _ hx => hx.2⟩
    have hsup : sSup (heightRange A + Icc (-(ε : ℝ)) ε) =
        sSup (heightRange A) + (ε : ℝ) := by
      rw [csSup_add hs hs' (nonempty_Icc.mpr (GeometricThickening.neg_le_band ε))
        ⟨ε, fun _ hx => hx.2⟩, csSup_Icc (GeometricThickening.neg_le_band ε)]
    have hbound := ofReal_abs_sSup_sub_le_hausdorffEDist hs ht hs' ht'
    rw [hsup] at hbound
    rw [abs_sub_comm, add_sub_cancel_left, abs_of_nonneg ε.coe_nonneg] at hbound
    have hd := hausdorffEDist_heightRange_le_geometricInterleavingDistance A
      ((geometricSmoothing ε).obj A)
    rw [heightRange_geometricSmoothing] at hd
    simpa only [ENNReal.ofReal_coe_nnreal] using
      hbound.trans hd

end RGraph

namespace Interleaving

open OpenInterval

variable {ε : ℝ≥0} {F G : OpenInterval ⥤ Type v}

/-- The equivalence between the top components of two interleaved Type-valued precosheaves. -/
def topEquiv (j : Interleaving ε F G) : F.obj ⊤ ≃ G.obj ⊤ where
  toFun x := G.map (homOfLE le_top) (j.φ.app ⊤ x)
  invFun y := F.map (homOfLE le_top) (j.ψ.app ⊤ y)
  left_inv := by
    intro x
    let g : thicken ε (⊤ : OpenInterval) ⟶ ⊤ := homOfLE le_top
    change F.map g (j.ψ.app ⊤ (G.map g (j.φ.app ⊤ x))) = x
    have hcomp :
        j.φ.app ⊤ ≫ G.map g ≫ j.ψ.app ⊤ ≫ F.map g = 𝟙 _ := by
      have htriangle :
          j.φ.app ⊤ ≫ G.map g ≫ j.ψ.app ⊤ =
            F.map (homOfLE ((le_thicken ε ⊤).trans
              (g.le.trans (le_thicken ε ⊤)))) :=
        j.φ_map_ψ g
      calc
        j.φ.app ⊤ ≫ G.map g ≫ j.ψ.app ⊤ ≫ F.map g =
            (j.φ.app ⊤ ≫ G.map g ≫ j.ψ.app ⊤) ≫ F.map g := by
          simp only [Category.assoc]
        _ = F.map (homOfLE ((le_thicken ε ⊤).trans
            (g.le.trans (le_thicken ε ⊤)))) ≫ F.map g := by
          exact congrArg (fun k => k ≫ F.map g) htriangle
        _ = F.map (homOfLE ((le_thicken ε ⊤).trans
            (g.le.trans (le_thicken ε ⊤))) ≫ g) := by
          exact (F.map_comp _ _).symm
        _ = F.map (𝟙 _) := map_eq_map_of_interval F _ _
        _ = 𝟙 _ := F.map_id _
    simpa only [types_comp_apply, types_id_apply] using congrArg (fun f => f x) hcomp
  right_inv := by
    intro y
    let g : thicken ε (⊤ : OpenInterval) ⟶ ⊤ := homOfLE le_top
    change G.map g (j.φ.app ⊤ (F.map g (j.ψ.app ⊤ y))) = y
    have hcomp :
        j.ψ.app ⊤ ≫ F.map g ≫ j.φ.app ⊤ ≫ G.map g = 𝟙 _ := by
      have htriangle :
          j.ψ.app ⊤ ≫ F.map g ≫ j.φ.app ⊤ =
            G.map (homOfLE ((le_thicken ε ⊤).trans
              (g.le.trans (le_thicken ε ⊤)))) :=
        j.ψ_map_φ g
      calc
        j.ψ.app ⊤ ≫ F.map g ≫ j.φ.app ⊤ ≫ G.map g =
            (j.ψ.app ⊤ ≫ F.map g ≫ j.φ.app ⊤) ≫ G.map g := by
          simp only [Category.assoc]
        _ = G.map (homOfLE ((le_thicken ε ⊤).trans
            (g.le.trans (le_thicken ε ⊤)))) ≫ G.map g := by
          exact congrArg (fun k => k ≫ G.map g) htriangle
        _ = G.map (homOfLE ((le_thicken ε ⊤).trans
            (g.le.trans (le_thicken ε ⊤))) ≫ g) := by
          exact (G.map_comp _ _).symm
        _ = G.map (𝟙 _) := map_eq_map_of_interval G _ _
        _ = 𝟙 _ := G.map_id _
    simpa only [types_comp_apply, types_id_apply] using congrArg (fun f => f y) hcomp

end Interleaving

namespace RGraph

namespace GeometricInterleaving

variable {ε : ℝ≥0} {A B : RGraphCat}

/-- The top-component equivalence induced by a geometric interleaving. -/
def componentsTopEquiv (i : GeometricInterleaving ε A B) :
    (cosheafFunctor.obj A).obj.obj ⊤ ≃ (cosheafFunctor.obj B).obj.obj ⊤ :=
  i.toCosheaf.topEquiv

end GeometricInterleaving

/-- If the top component types of two graph objects admit no bijection, there is no geometric
interleaving between them, so their geometric interleaving distance is infinite. -/
theorem geometricInterleavingDistance_eq_top_of_isEmpty_equiv {A B : RGraphCat}
    (h : IsEmpty ((cosheafFunctor.obj A).obj.obj ⊤ ≃ (cosheafFunctor.obj B).obj.obj ⊤)) :
    geometricInterleavingDistance A B = ⊤ := by
  rw [geometricInterleavingDistance_eq_top_iff]
  intro ε
  exact ⟨fun i => h.false i.componentsTopEquiv⟩

end RGraph

end

end TDA.Reeb
