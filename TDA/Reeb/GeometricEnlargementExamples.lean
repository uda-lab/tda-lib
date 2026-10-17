import TDA.Reeb.GeometricEnlargement
import TDA.Reeb.GeometricInterleavingEquivalenceExamples

/-!
# Fixtures for geometric enlargement and self-smoothing

Acceptance fixtures for `TDA.Reeb.GeometricEnlargement`, on the single edge, its midpoint, and the
parallel-edge loop. They record the enlargement laws, the collapse of the loop under strict
enlargement, monotonicity of witnesses, the self-smoothing bounds, and the associated threshold
controls.
-/

open Set Topology CategoryTheory
open scoped NNReal ENNReal

namespace TDA.Reeb

noncomputable section

namespace Examples.GeometricEnlargement

open RGraph
open TDA.Reeb.Examples.RGraphCosheafEquivalence (singleGraph parallelGraph)
open TDA.Reeb.Examples.RGraphSmoothing (parallel_quarter_fiber_not_subsingleton
  parallel_half_fiber_subsingleton)
open TDA.Reeb.Examples.RGraphThickening (halfNN coe_halfNN)
open TDA.Reeb.Examples.ConstructibleSmoothing (quarter coe_quarter)
open TDA.Reeb.Examples.GeometricInterleaving (midGraph edgeTop edgeMidInterleaving edgeMid_isEmpty
  parallelSingleInterleaving parallelSingle_zero_isEmpty coe_halfNN_ennreal
  geometricInterleavingDistance_edge_mid)
open TDA.Reeb.Examples.GeometricInterleavingEquivalence (parallelMidInterleaving)

/-- The quarter-band parameter is at most the half-band parameter. -/
theorem quarter_le_halfNN : quarter ≤ halfNN := by
  rw [← NNReal.coe_le_coe, coe_quarter, coe_halfNN]
  norm_num

/-- The quarter-band parameter is nonnegative. -/
theorem zero_le_quarter : (0 : ℝ≥0) ≤ quarter := zero_le

/-- Strict enlargement from `1/4` to `1/2` identifies the two points of the parallel-edge fibre over `1/2`.
This is the noninjectivity witness for the geometric enlargement on `parallelGraph`. -/
theorem enlargement_parallel_not_injective :
    ¬ Function.Injective ((geometricEnlargement quarter_le_halfNN).app parallelGraph).hom.left.hom := by
  intro hinj
  have : Nontrivial
      (overBaseMap ((geometricSmoothing quarter).obj parallelGraph).obj ⁻¹' {1 / 2}) :=
    not_subsingleton_iff_nontrivial.mp parallel_quarter_fiber_not_subsingleton
  obtain ⟨p, q, hpq⟩ := exists_pair_ne
    (overBaseMap ((geometricSmoothing quarter).obj parallelGraph).obj ⁻¹' {1 / 2})
  have hp' :
      overBaseMap ((geometricSmoothing halfNN).obj parallelGraph).obj
          (((geometricEnlargement quarter_le_halfNN).app parallelGraph).hom.left.hom p.1) =
        1 / 2 :=
    (overBaseMap_comm
      ((geometricEnlargement quarter_le_halfNN).app parallelGraph).hom p.1).trans p.2
  have hq' :
      overBaseMap ((geometricSmoothing halfNN).obj parallelGraph).obj
          (((geometricEnlargement quarter_le_halfNN).app parallelGraph).hom.left.hom q.1) =
        1 / 2 :=
    (overBaseMap_comm
      ((geometricEnlargement quarter_le_halfNN).app parallelGraph).hom q.1).trans q.2
  have hmap :
      ((geometricEnlargement quarter_le_halfNN).app parallelGraph).hom.left.hom p.1 =
        ((geometricEnlargement quarter_le_halfNN).app parallelGraph).hom.left.hom q.1 := by
    exact congrArg Subtype.val
      ((parallel_half_fiber_subsingleton (1 / 2)).elim
        (⟨_, hp'⟩ : overBaseMap ((geometricSmoothing halfNN).obj parallelGraph).obj ⁻¹' {1 / 2})
        (⟨_, hq'⟩ : overBaseMap ((geometricSmoothing halfNN).obj parallelGraph).obj ⁻¹' {1 / 2}))
  exact hpq (Subtype.ext (hinj hmap))

/-- The two-step enlargement `0 ≤ 1/4 ≤ 1/2` agrees with the direct enlargement on the loop. -/
theorem parallel_enlargement_comp :
    (geometricEnlargement zero_le_quarter).app parallelGraph ≫
        (geometricEnlargement quarter_le_halfNN).app parallelGraph =
      (geometricEnlargement (zero_le_quarter.trans quarter_le_halfNN)).app parallelGraph := by
  simpa only [NatTrans.comp_app] using congrArg (fun η => η.app parallelGraph)
    (geometricEnlargement_comp zero_le_quarter quarter_le_halfNN)

/-- The enlargement at the reflexive quarter inequality is the identity on the loop. -/
theorem quarter_enlargement_refl :
    geometricEnlargement (le_refl quarter) = 𝟙 (geometricSmoothing quarter) :=
  geometricEnlargement_refl quarter

/-- Enlargement sends the class of the top edge point at band coordinate `0` to the same point at
band coordinate `0` in the half-smoothing of the single edge. -/
theorem single_enlargement_edgeTop :
    ((geometricEnlargement quarter_le_halfNN).app singleGraph).hom.left.hom
        (ReebQuotient.mk (GeometricThickening.height (overBaseMap singleGraph.obj) quarter)
          (edgeTop, ⟨0, GeometricThickening.zero_mem_band quarter⟩)) =
      ReebQuotient.mk (GeometricThickening.height (overBaseMap singleGraph.obj) halfNN)
        (edgeTop, ⟨0, GeometricThickening.zero_mem_band halfNN⟩) := by
  simpa [GeometricThickening.bandInclusion] using
    (geometricEnlargement_app_hom_left_mk quarter_le_halfNN singleGraph edgeTop
      ⟨0, GeometricThickening.zero_mem_band quarter⟩)

/-- The single edge is at geometric distance at most `1/2` from its half-smoothing. -/
theorem geometricInterleavingDistance_single_smoothed_le :
    geometricInterleavingDistance singleGraph ((geometricSmoothing halfNN).obj singleGraph) ≤ 1 / 2 := by
  rw [← coe_halfNN_ennreal]
  exact geometricInterleavingDistance_geometricSmoothing_self_le halfNN singleGraph

/-- The first component of the self-smoothing witness for the single edge is the composite of its
two geometric units. -/
theorem single_selfSmoothing_φ :
    (GeometricInterleaving.selfSmoothing halfNN singleGraph).φ =
      (geometricSmoothingUnit halfNN).app singleGraph ≫
        (geometricSmoothingUnit halfNN).app ((geometricSmoothing halfNN).obj singleGraph) :=
  GeometricInterleaving.selfSmoothing_φ halfNN singleGraph

/-- The second component of the self-smoothing witness for the single edge is the identity. -/
theorem single_selfSmoothing_ψ :
    (GeometricInterleaving.selfSmoothing halfNN singleGraph).ψ = 𝟙 _ :=
  GeometricInterleaving.selfSmoothing_ψ halfNN singleGraph

/-- The point graph is at geometric distance at most `ε` from its `ε`-smoothing, for every `ε`. -/
theorem geometricInterleavingDistance_mid_smoothed_le (ε : ℝ≥0) :
    geometricInterleavingDistance midGraph ((geometricSmoothing ε).obj midGraph) ≤ ε :=
  geometricInterleavingDistance_geometricSmoothing_self_le ε midGraph

/-- Every graph object has zero distance from its zero-smoothing, using the zero smoothing
isomorphism. -/
theorem geometricInterleavingDistance_smoothed_zero (A : RGraphCat) :
    geometricInterleavingDistance A ((geometricSmoothing 0).obj A) = 0 :=
  geometricInterleavingDistance_eq_zero_of_iso (geometricSmoothingZeroIso.app A).symm

/-- The half-band parameter is at most one. -/
theorem halfNN_le_one : halfNN ≤ 1 := by
  rw [← NNReal.coe_le_coe, coe_halfNN]
  norm_num

/-- The first component of the monotone edge–midpoint witness is its original component followed
by geometric enlargement. -/
theorem edgeMid_mono_φ :
    (edgeMidInterleaving.mono halfNN_le_one).φ =
      edgeMidInterleaving.φ ≫ (geometricEnlargement halfNN_le_one).app midGraph :=
  GeometricInterleaving.mono_φ edgeMidInterleaving halfNN_le_one

/-- The edge–midpoint witness exists exactly at and above the height threshold `1/2`. -/
theorem edgeMid_nonempty_iff {ε : ℝ≥0} :
    Nonempty (GeometricInterleaving ε singleGraph midGraph) ↔ 1 / 2 ≤ (ε : ℝ) := by
  constructor
  · intro h
    by_contra hε
    exact h.elim (edgeMid_isEmpty (not_le.mp hε)).false
  · intro hε
    exact nonempty_mono (A := singleGraph) (B := midGraph)
      (by
        rw [← NNReal.coe_le_coe, coe_halfNN]
        exact hε)
      ⟨edgeMidInterleaving⟩

/-- Every parameter strictly above the edge–midpoint distance has a geometric witness. -/
theorem edgeMid_nonempty_of_lt {ε : ℝ≥0} (hε : (1 / 2 : ℝ≥0∞) < ε) :
    Nonempty (GeometricInterleaving ε singleGraph midGraph) := by
  apply nonempty_of_geometricInterleavingDistance_lt (A := singleGraph) (B := midGraph)
  rw [geometricInterleavingDistance_edge_mid]
  exact hε

/-- The edge–midpoint distance upper bound follows from the witnesses above every `1/2`, without
using the explicit `1/2` witness. -/
theorem geometricInterleavingDistance_edge_mid_le_of_witnesses :
    geometricInterleavingDistance singleGraph midGraph ≤ 1 / 2 := by
  apply geometricInterleavingDistance_le_iff.2
  intro ε hε
  exact edgeMid_nonempty_of_lt hε

/-- The second component of the composite parallel-edge–midpoint witness is the explicit composite
of `GeometricInterleaving.trans_ψ`. -/
theorem parallelMidInterleaving_ψ :
    parallelMidInterleaving.ψ =
      edgeMidInterleaving.ψ ≫ (geometricSmoothing halfNN).map parallelSingleInterleaving.ψ ≫
        (geometricSmoothingCompIso halfNN quarter).hom.app parallelGraph ≫
          (geometricSmoothingEqIso (add_comm halfNN quarter)).hom.app parallelGraph := by
  change (parallelSingleInterleaving.trans edgeMidInterleaving).ψ = _
  exact GeometricInterleaving.trans_ψ parallelSingleInterleaving edgeMidInterleaving

/-- A quarter witness between the parallel loop and the single edge does not reverse to a zero
witness. -/
theorem mono_not_reverse :
    Nonempty (GeometricInterleaving quarter parallelGraph singleGraph) ∧
      IsEmpty (GeometricInterleaving 0 parallelGraph singleGraph) :=
  ⟨⟨parallelSingleInterleaving⟩, parallelSingle_zero_isEmpty⟩

/-- The edge–midpoint monotonicity witness has no reverse witness at the quarter threshold. -/
theorem edgeMid_mono_not_reverse :
    Nonempty (GeometricInterleaving halfNN singleGraph midGraph) ∧
      IsEmpty (GeometricInterleaving quarter singleGraph midGraph) := by
  refine ⟨⟨edgeMidInterleaving⟩, edgeMid_isEmpty ?_⟩
  rw [coe_quarter]
  norm_num

/-- At the boundary, enlargement at the reflexive quarter inequality is the identity on the
parallel loop; the noninjectivity above therefore comes from strict parameter enlargement. -/
theorem parallel_enlargement_refl_app :
    (geometricEnlargement (le_refl quarter)).app parallelGraph =
      𝟙 ((geometricSmoothing quarter).obj parallelGraph) := by
  rw [geometricEnlargement_refl]
  rfl

end Examples.GeometricEnlargement

end

end TDA.Reeb
