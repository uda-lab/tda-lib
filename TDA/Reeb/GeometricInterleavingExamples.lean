import TDA.Reeb.GeometricInterleaving
import TDA.Reeb.QuotientThickeningAbsorptionExamples

/-!
# Fixtures for geometric interleavings of graph objects

Acceptance fixtures for `TDA.Reeb.GeometricInterleaving`, on graph objects:

* **Unit coherence on a representative.** On the single edge over `0 < 1` with `ε = δ = 1/4`,
  both unit coherence forms send the edge point at height `1/2` to its class at band coordinate
  `0` in `U_(1/4 + 1/4)`.
* **The edge against its midpoint: exact distance `1/2`.** The single edge spans heights `[0, 1]`,
  and the one-vertex graph `P` sits at height `1/2`. A geometric `1/2`-interleaving exists. Every
  point of `U_ε P` has height in `[1/2 - ε, 1/2 + ε]`, so for `ε < 1/2` the top vertex of the edge
  has nowhere to go and no `ε`-interleaving exists. Hence `d_geo = 1/2` in `ℝ≥0∞`, and the cosheaf
  interleaving distance is at most `1/2`.
* **Two merging edges against one edge at `1/4`.** The collapse and an edge inclusion, followed by
  the units, form a geometric `1/4`-interleaving, because `U_(1/4 + 1/4)` of both graphs has
  subsingleton height fibres. The same-shaped pair at `1/8` fails its first triangle: the two
  edge points stay apart in `U_(1/8 + 1/8) ≅ U_(1/4)`. This rules out only that specific pair; it
  does not show that no geometric `1/8`-interleaving exists.
* **Negative controls at `0`.** No `0`-interleaving between the parallel edges and the single
  edge, which are not isomorphic, and none between the edge and its midpoint.
* **Identity at `0` and distance `0` across presentations.** The unit `0`-interleaving of the
  parallel edges gives back the identity at an edge point, and the single edge over `0 < 1/2 < 1`
  and over `0 < 1` are at distance `0`.
* **Symmetry and transport on a witness.**
-/

open Set Topology CategoryTheory
open scoped NNReal ENNReal

namespace TDA.Reeb

noncomputable section

namespace Examples.GeometricInterleaving

open OpenInterval CylinderPresentation FiniteReebData RGraph
open TDA.Reeb.Examples.Cylinder (S01 S01_value_zero S01_value_one parallelData)
open TDA.Reeb.RGraph.Examples (singleEdge parallel_not_iso_single)
open TDA.Reeb.Examples.ConstructibleRepresentation (pt0)
open TDA.Reeb.Examples.RGraphCosheafEquivalence (parallelGraph singleGraph collapseGraph
  singleHalfGraph subdivisionIso)
open TDA.Reeb.Examples.RGraphSmoothing (singletonGraph singleton_smoothed_subsingleton
  fiber_subsingleton_of_cosheaf single_smoothed_fiber_subsingleton
  parallel_smoothed_fiber_subsingleton)
open TDA.Reeb.Examples.RGraphThickening (single halfNN coe_halfNN)
open TDA.Reeb.Examples.GeometricThickeningAddition (edgePt parPt)
open TDA.Reeb.Examples.QuotientThickeningAddition (eighth eighth_add_eighth)
open TDA.Reeb.Examples.QuotientThickeningAbsorption (par_quarter_classes_ne)
open TDA.Reeb.Examples.ConstructibleSmoothing (quarter coe_quarter)

/-! ### Unit coherence on a representative -/

/-- **Unit coherence at `(1/4, 1/4)`.** Both forms send the edge point `q` at height `1/2` to
`[(q, 0)]` in `U_(1/4 + 1/4)` of the single edge. -/
theorem unit_coherence_edgePt :
    ((geometricSmoothingUnit quarter).app singleGraph ≫
        (geometricSmoothingUnit quarter).app ((geometricSmoothing quarter).obj singleGraph) ≫
          (geometricSmoothingCompIso quarter quarter).hom.app singleGraph).hom.left.hom edgePt =
        ReebQuotient.mk _ (edgePt, ⟨0, GeometricThickening.zero_mem_band _⟩) ∧
      ((geometricSmoothingUnit quarter).app singleGraph ≫
        (geometricSmoothing quarter).map ((geometricSmoothingUnit quarter).app singleGraph) ≫
          (geometricSmoothingCompIso quarter quarter).hom.app singleGraph).hom.left.hom edgePt =
        ReebQuotient.mk _ (edgePt, ⟨0, GeometricThickening.zero_mem_band _⟩) :=
  ⟨congrArg (fun f => f.hom.left.hom edgePt)
      (geometricSmoothingUnit_comp_geometricSmoothingUnit quarter quarter singleGraph),
    congrArg (fun f => f.hom.left.hom edgePt)
      (geometricSmoothingUnit_comp_map_geometricSmoothingUnit quarter quarter singleGraph)⟩

/-! ### The edge against its midpoint -/

/-- The one-vertex graph at height `1/2`, the midpoint of the edge's height span. -/
abbrev midGraph : RGraphCat := singletonGraph (1 / 2)

/-- Its vertex. -/
def midPt : midGraph.obj.left := (ofFiniteData pt0).ofVertex (single (1 / 2)) 0 ()

/-- Every point of the one-vertex graph has height `1/2`. -/
theorem height_mid (x : midGraph.obj.left) : overBaseMap midGraph.obj x = 1 / 2 := by
  have h : (ofFiniteData pt0).height (single (1 / 2)) x ∈ Icc ((single (1 / 2)).value 0)
      ((single (1 / 2)).value (Fin.last 0)) := (ofFiniteData pt0).height_mem_Icc _ x
  exact le_antisymm h.2 h.1

/-- The single edge spans heights `[0, 1]`. -/
theorem height_single_mem (x : singleGraph.obj.left) :
    overBaseMap singleGraph.obj x ∈ Icc (0 : ℝ) 1 := by
  have h : (ofFiniteData singleEdge).height S01 x ∈ Icc (S01.value 0)
      (S01.value (Fin.last 1)) := (ofFiniteData singleEdge).height_mem_Icc _ x
  rw [S01_value_zero] at h
  exact ⟨h.1, h.2.trans_eq S01_value_one⟩

theorem height_edgePt : overBaseMap singleGraph.obj edgePt = 1 / 2 :=
  rfl

/-- The edge point at height `1/2` as a slice map out of the midpoint. -/
def midToEdge : midGraph ⟶ singleGraph :=
  ObjectProperty.homMk (Over.homMk (TopCat.ofHom (ContinuousMap.const _ edgePt)) (by
    ext x
    exact height_edgePt.trans (height_mid x).symm))

/-- The band point `f x - 1/2 ∈ [-1/2, 1/2]` for `x` on the edge. -/
def edgeOffset (x : singleGraph.obj.left) : GeometricThickening.Band halfNN :=
  ⟨overBaseMap singleGraph.obj x - 1 / 2, by
    have h := height_single_mem x
    show _ ∈ Icc (-(halfNN : ℝ)) (halfNN : ℝ)
    rw [coe_halfNN]
    exact ⟨by linarith [h.1], by linarith [h.2]⟩⟩

/-- The slice map `x ↦ (p, f x - 1/2)` from the edge into the thickening `T_(1/2) P`. -/
def edgeToMidThick : singleGraph.obj ⟶ (GeometricThickening.functor halfNN).obj midGraph.obj :=
  Over.homMk (TopCat.ofHom ⟨fun x => (midPt, edgeOffset x),
    continuous_const.prodMk (((overBaseMap singleGraph.obj).continuous.sub
      continuous_const).subtype_mk _)⟩) (by
    ext x
    show overBaseMap midGraph.obj midPt + (overBaseMap singleGraph.obj x - 1 / 2) = _
    rw [height_mid]
    exact add_sub_cancel _ _)

/-- **The geometric `1/2`-interleaving of the edge and its midpoint.**
`φ x = [(p, f x - 1/2)]` and `ψ p = [(q, 0)]` for the edge point `q` at height `1/2`. Both
triangles hold because their targets have subsingleton height fibres. -/
def edgeMidInterleaving : GeometricInterleaving halfNN singleGraph midGraph where
  φ := ObjectProperty.homMk (edgeToMidThick ≫
    (ReebQuotient.projNatTrans ℝ).app ((GeometricThickening.functor halfNN).obj midGraph.obj))
  ψ := midToEdge ≫ (geometricSmoothingUnit halfNN).app singleGraph
  φ_ψ := hom_ext_of_fiber_subsingleton (single_smoothed_fiber_subsingleton _)
  ψ_φ := hom_ext_of_fiber_subsingleton
    (fiber_subsingleton_of_cosheaf _ (singleton_smoothed_subsingleton (1 / 2) _))

/-- **Height bound.** Every point of `U_ε P` has height in `[1/2 - ε, 1/2 + ε]`. -/
theorem height_smoothed_mid_mem (ε : ℝ≥0) (q : ((geometricSmoothing ε).obj midGraph).obj.left) :
    overBaseMap ((geometricSmoothing ε).obj midGraph).obj q ∈
      Icc (1 / 2 - (ε : ℝ)) (1 / 2 + ε) := by
  obtain ⟨⟨x, t⟩, rfl⟩ := ReebQuotient.mk_surjective _ q
  show overBaseMap midGraph.obj x + (t : ℝ) ∈ _
  rw [height_mid]
  exact ⟨by linarith [t.2.1], by linarith [t.2.2]⟩

/-- The top vertex of the edge, at height `1`. -/
def edgeTop : singleGraph.obj.left := (ofFiniteData singleEdge).ofVertex S01 1 ()

theorem height_edgeTop : overBaseMap singleGraph.obj edgeTop = 1 :=
  S01_value_one

/-- **Threshold.** For `ε < 1/2` there is no geometric `ε`-interleaving of the edge and its
midpoint: `φ` would send the top vertex, at height `1`, to a point of height at most `1/2 + ε`. -/
theorem edgeMid_isEmpty {ε : ℝ≥0} (hε : (ε : ℝ) < 1 / 2) :
    IsEmpty (GeometricInterleaving ε singleGraph midGraph) := by
  refine ⟨fun i => ?_⟩
  have h := height_smoothed_mid_mem ε (i.φ.hom.left.hom edgeTop)
  rw [overBaseMap_comm i.φ.hom edgeTop, height_edgeTop] at h
  linarith [h.2]

theorem coe_halfNN_ennreal : ((halfNN : ℝ≥0) : ℝ≥0∞) = 1 / 2 := by
  rw [show halfNN = 1 / 2 from NNReal.eq (by rw [coe_halfNN]; norm_num),
    ENNReal.coe_div two_ne_zero, ENNReal.coe_one, ENNReal.coe_ofNat]

/-- **Exact distance.** `d_geo(edge, midpoint) = 1/2` in `ℝ≥0∞`: the witness at `1/2` and the
threshold below it. -/
theorem geometricInterleavingDistance_edge_mid :
    geometricInterleavingDistance singleGraph midGraph = 1 / 2 := by
  refine le_antisymm ?_ (le_geometricInterleavingDistance_iff.2 fun ε ⟨i⟩ => ?_)
  · rw [← coe_halfNN_ennreal]
    exact edgeMidInterleaving.geometricInterleavingDistance_le
  · rw [← coe_halfNN_ennreal, ENNReal.coe_le_coe, ← NNReal.coe_le_coe, coe_halfNN]
    by_contra h
    exact (edgeMid_isEmpty (not_le.1 h)).false i

/-- On the cosheaf side, the interleaving distance of the component precosheaves is `≤ 1/2`. -/
theorem interleavingDistance_edge_mid_le :
    interleavingDistance (cosheafFunctor.obj singleGraph).obj (cosheafFunctor.obj midGraph).obj ≤
      1 / 2 :=
  (interleavingDistance_cosheafFunctor_le_geometricInterleavingDistance _ _).trans_eq
    geometricInterleavingDistance_edge_mid

/-! ### Two merging edges against one edge -/

/-- Include the single edge as the edge `false` of the two parallel edges. -/
def includeEdge : singleEdge ⟶ parallelData :=
  (⟨fun _ => id, fun _ _ => false, fun _ _ => rfl, fun _ _ => rfl⟩ :
    FiniteReebData.Hom singleEdge parallelData)

/-- The inclusion as a graph morphism. -/
abbrev includeGraph : singleGraph ⟶ parallelGraph := (toRGraph S01).map includeEdge

theorem one_half_le_quarter_add_quarter : 1 / 2 ≤ ((quarter + quarter : ℝ≥0) : ℝ) := by
  rw [NNReal.coe_add, coe_quarter]
  norm_num

/-- **The geometric `1/4`-interleaving of the two parallel edges and the single edge**: the
collapse and the inclusion, followed by the units. -/
def parallelSingleInterleaving : GeometricInterleaving quarter parallelGraph singleGraph where
  φ := collapseGraph ≫ (geometricSmoothingUnit quarter).app singleGraph
  ψ := includeGraph ≫ (geometricSmoothingUnit quarter).app parallelGraph
  φ_ψ := hom_ext_of_fiber_subsingleton
    (parallel_smoothed_fiber_subsingleton one_half_le_quarter_add_quarter)
  ψ_φ := hom_ext_of_fiber_subsingleton (single_smoothed_fiber_subsingleton _)

theorem coe_quarter_ennreal : ((quarter : ℝ≥0) : ℝ≥0∞) = 1 / 4 := by
  rw [show quarter = 1 / 4 from NNReal.eq (by rw [coe_quarter]; norm_num),
    ENNReal.coe_div four_ne_zero, ENNReal.coe_one, ENNReal.coe_ofNat]

theorem geometricInterleavingDistance_parallel_single_le :
    geometricInterleavingDistance parallelGraph singleGraph ≤ 1 / 4 :=
  coe_quarter_ennreal ▸ parallelSingleInterleaving.geometricInterleavingDistance_le

theorem interleavingDistance_parallel_single_le :
    interleavingDistance (cosheafFunctor.obj parallelGraph).obj
        (cosheafFunctor.obj singleGraph).obj ≤ 1 / 4 :=
  (interleavingDistance_cosheafFunctor_le_geometricInterleavingDistance _ _).trans
    geometricInterleavingDistance_parallel_single_le

/-- **Boundary control at `1/8`.** The same-shaped pair at `1/8` fails its first triangle. At the
edge point over `true`, the shifted composite gives `[(q_false, 0 + 0)]` and the unit gives
`[(q_true, 0)]`; through `U_(1/8 + 1/8) ≅ U_(1/4)` these are distinct classes. This is an
inequality for this specific pair of maps only, not emptiness of all geometric
`1/8`-interleavings. -/
theorem parallelSingle_eighth_ne :
    (collapseGraph ≫ (geometricSmoothingUnit eighth).app singleGraph) ≫
        (geometricSmoothing eighth).map
          (includeGraph ≫ (geometricSmoothingUnit eighth).app parallelGraph) ≫
        (geometricSmoothingCompIso eighth eighth).hom.app parallelGraph ≠
      (geometricSmoothingUnit (eighth + eighth)).app parallelGraph := by
  intro h
  have h₁ := congrArg (fun f => ((geometricSmoothingEqIso eighth_add_eighth).hom.app
    parallelGraph).hom.left.hom (f.hom.left.hom (parPt true))) h
  have e := geometricSmoothingCompIso_hom_app_hom_left_mk eighth eighth parallelGraph
    (parPt false, ⟨0, GeometricThickening.zero_mem_band _⟩)
    ⟨0, GeometricThickening.zero_mem_band _⟩
  have h₂ := (congrArg (((geometricSmoothingEqIso eighth_add_eighth).hom.app
    parallelGraph).hom.left.hom) e).symm.trans h₁
  have h₃ : ReebQuotient.mk (GeometricThickening.height (overBaseMap parallelGraph.obj) quarter)
        (parPt false, ⟨0 + 0, by rw [add_zero]; exact GeometricThickening.zero_mem_band _⟩) =
      ReebQuotient.mk (GeometricThickening.height (overBaseMap parallelGraph.obj) quarter)
        (parPt true, ⟨0, GeometricThickening.zero_mem_band _⟩) := h₂
  have h₄ : ReebQuotient.mk (GeometricThickening.height (overBaseMap parallelGraph.obj) quarter)
        (parPt false, ⟨0, GeometricThickening.zero_mem_band _⟩) =
      ReebQuotient.mk (GeometricThickening.height (overBaseMap parallelGraph.obj) quarter)
        (parPt false, ⟨0 + 0, by rw [add_zero]; exact GeometricThickening.zero_mem_band _⟩) :=
    congrArg (ReebQuotient.mk _) (Prod.ext rfl (Subtype.ext (add_zero (0 : ℝ)).symm))
  exact par_quarter_classes_ne (h₄.trans h₃)

/-! ### Negative controls at `0` -/

/-- **No `0`-interleaving between non-isomorphic graph objects**: a `0`-interleaving would be an
isomorphism of the parallel edges with the single edge. -/
theorem parallelSingle_zero_isEmpty :
    IsEmpty (GeometricInterleaving 0 parallelGraph singleGraph) :=
  ⟨fun i => parallel_not_iso_single.false (IsRGraph.ι.mapIso i.toIso)⟩

/-- The `ε = 0` case of the threshold for the edge and its midpoint. -/
theorem edgeMid_zero_isEmpty : IsEmpty (GeometricInterleaving 0 singleGraph midGraph) :=
  edgeMid_isEmpty (by norm_num)

/-! ### Identity at `0` and distance `0` across presentations -/

/-- The unit `0`-interleaving of the parallel edges gives back the identity at an edge point. -/
theorem refl_zero_toIso_parPt :
    (GeometricInterleaving.refl 0 parallelGraph).toIso.hom.hom.left.hom (parPt true) =
      parPt true :=
  geometricSmoothingZeroIso_hom_app_hom_left_mk parallelGraph (parPt true) _

/-- The single edge over `0 < 1/2 < 1` and over `0 < 1` are at geometric distance `0`. -/
theorem geometricInterleavingDistance_singleHalf_single :
    geometricInterleavingDistance singleHalfGraph singleGraph = 0 :=
  geometricInterleavingDistance_eq_zero_of_iso subdivisionIso

/-! ### Symmetry and transport on a witness -/

theorem edgeMidInterleaving_symm_toCosheaf :
    edgeMidInterleaving.symm.toCosheaf = edgeMidInterleaving.toCosheaf.symm :=
  edgeMidInterleaving.toCosheaf_symm

theorem geometricInterleavingDistance_mid_edge :
    geometricInterleavingDistance midGraph singleGraph = 1 / 2 :=
  (geometricInterleavingDistance_comm _ _).trans geometricInterleavingDistance_edge_mid

end Examples.GeometricInterleaving

end

end TDA.Reeb
