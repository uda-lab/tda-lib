import TDA.Reeb.GeometricSmoothInterleaving
import TDA.Reeb.GeometricEnlargementExamples

/-!
# Fixtures for smoothing geometric interleavings

These fixtures record fibre thinness after repeated smoothing, computed components of smoothed
edge--midpoint and parallel--single witnesses, their coherence laws, and the resulting distance
bounds and threshold control.
-/

open Set Topology CategoryTheory
open scoped NNReal ENNReal

namespace TDA.Reeb

noncomputable section

namespace Examples.GeometricSmoothInterleaving

open OpenInterval RGraph
open TDA.Reeb.Examples.RGraphCosheafEquivalence (singleGraph parallelGraph collapseGraph)
open TDA.Reeb.Examples.RGraphSmoothing (singleton_smoothed_subsingleton
  fiber_subsingleton_of_cosheaf single_stretched_subsingleton)
open TDA.Reeb.Examples.RGraphThickening (halfNN coe_halfNN)
open TDA.Reeb.Examples.ConstructibleSmoothing (quarter coe_quarter)
open TDA.Reeb.Examples.GeometricInterleaving (midGraph midToEdge edgeMidInterleaving
  height_smoothed_mid_mem edgeTop height_edgeTop edgeMid_isEmpty coe_halfNN_ennreal includeGraph
  parallelSingleInterleaving coe_quarter_ennreal geometricInterleavingDistance_edge_mid)
open TDA.Reeb.Examples.GeometricEnlargement (halfNN_le_one)

/-- Every height fibre of a smoothing of a smoothed graph is subsingleton when all values of the
inner smoothed graph's component cosheaf are subsingleton. -/
theorem smoothed_smoothed_fiber_subsingleton (B : RGraphCat) (a b : ℝ≥0)
    (h : ∀ L, Subsingleton ((cosheafFunctor.obj ((geometricSmoothing b).obj B)).obj.obj L)) :
    ∀ t : ℝ, Subsingleton
      (overBaseMap ((geometricSmoothing a).obj ((geometricSmoothing b).obj B)).obj ⁻¹' {t}) := by
  intro t
  exact fiber_subsingleton_of_cosheaf _ (fun L =>
    (geometricSmoothingValueEquiv a _ L).subsingleton_congr.2 (h (thicken a L))) t

/-- The first component of the quarter-smoothed edge--midpoint witness is the smoothed original
component followed by geometric commutation. -/
theorem edgeMid_smooth_φ :
    (edgeMidInterleaving.smooth quarter).φ =
      (geometricSmoothing quarter).map edgeMidInterleaving.φ ≫
        (geometricSmoothingCommIso halfNN quarter).hom.app midGraph :=
  GeometricInterleaving.smooth_φ edgeMidInterleaving quarter

/-- The second component of the quarter-smoothed edge--midpoint witness is the smoothed midpoint
map followed by the half-band geometric unit. -/
theorem edgeMid_smooth_ψ :
    (edgeMidInterleaving.smooth quarter).ψ =
      (geometricSmoothing quarter).map midToEdge ≫
        (geometricSmoothingUnit halfNN).app ((geometricSmoothing quarter).obj singleGraph) := by
  apply hom_ext_of_fiber_subsingleton
  exact smoothed_smoothed_fiber_subsingleton singleGraph halfNN quarter
    (single_stretched_subsingleton quarter)

/-- The target of the first component of the quarter-smoothed edge--midpoint witness is thin. -/
theorem smoothed_mid_target_subsingleton :
    Subsingleton
      ((geometricSmoothing quarter).obj singleGraph ⟶
        (geometricSmoothing halfNN).obj ((geometricSmoothing quarter).obj midGraph)) := by
  exact ⟨fun f g => hom_ext_of_fiber_subsingleton
    (smoothed_smoothed_fiber_subsingleton midGraph halfNN quarter
      (singleton_smoothed_subsingleton (1 / 2) quarter))⟩

/-- The first component of the half-smoothed parallel--single witness is the smoothed collapse
followed by the quarter-band geometric unit. -/
theorem parallelSingle_smooth_φ :
    (parallelSingleInterleaving.smooth halfNN).φ =
      (geometricSmoothing halfNN).map collapseGraph ≫
        (geometricSmoothingUnit quarter).app ((geometricSmoothing halfNN).obj singleGraph) := by
  apply hom_ext_of_fiber_subsingleton
  exact smoothed_smoothed_fiber_subsingleton singleGraph quarter halfNN
    (single_stretched_subsingleton halfNN)

/-- Smoothing the edge--midpoint witness at zero recovers its original first component after the
zero isomorphisms. -/
theorem edgeMid_smooth_zero_φ :
    geometricSmoothingZeroIso.inv.app singleGraph ≫ (edgeMidInterleaving.smooth 0).φ ≫
        (geometricSmoothing halfNN).map (geometricSmoothingZeroIso.hom.app midGraph) =
      edgeMidInterleaving.φ :=
  GeometricInterleaving.smooth_zero_φ edgeMidInterleaving

/-- Smoothing the edge--midpoint witness twice at the quarter parameter agrees with smoothing it
at the sum, after the composition isomorphism. -/
theorem edgeMid_smooth_add_φ :
    (geometricSmoothingCompIso quarter quarter).inv.app singleGraph ≫
        ((edgeMidInterleaving.smooth quarter).smooth quarter).φ ≫
          (geometricSmoothing halfNN).map
            ((geometricSmoothingCompIso quarter quarter).hom.app midGraph) =
      (edgeMidInterleaving.smooth (quarter + quarter)).φ :=
  GeometricInterleaving.smooth_add_φ edgeMidInterleaving quarter quarter

/-- Smoothing commutes with enlarging the parameter of the edge--midpoint witness. -/
theorem edgeMid_smooth_mono :
    (edgeMidInterleaving.mono halfNN_le_one).smooth quarter =
      (edgeMidInterleaving.smooth quarter).mono halfNN_le_one :=
  GeometricInterleaving.smooth_mono edgeMidInterleaving halfNN_le_one quarter

/-- Below one half, there is no geometric interleaving at the unchanged parameter between the
quarter-smoothed edge and quarter-smoothed midpoint. -/
theorem smoothed_edgeMid_isEmpty (ε : ℝ≥0) (hε : (ε : ℝ) < 1 / 2) :
    IsEmpty
      (GeometricInterleaving ε ((geometricSmoothing quarter).obj singleGraph)
        ((geometricSmoothing quarter).obj midGraph)) := by
  refine ⟨fun i => ?_⟩
  have hupper : ∀ q : ((geometricSmoothing ε).obj
      ((geometricSmoothing quarter).obj midGraph)).obj.left,
      overBaseMap ((geometricSmoothing ε).obj
        ((geometricSmoothing quarter).obj midGraph)).obj q ≤ 3 / 4 + (ε : ℝ) := by
    intro q
    obtain ⟨⟨y, t⟩, rfl⟩ := ReebQuotient.mk_surjective _ q
    show overBaseMap ((geometricSmoothing quarter).obj midGraph).obj y + (t : ℝ) ≤
      3 / 4 + (ε : ℝ)
    have hy := height_smoothed_mid_mem quarter y
    rcases hy with ⟨hy₁, hy₂⟩
    norm_num [coe_quarter] at hy₂
    linarith [hy₂, t.2.2]
  let q : ((geometricSmoothing quarter).obj singleGraph).obj.left :=
    ReebQuotient.mk _
      (edgeTop, ⟨(quarter : ℝ), right_mem_Icc.2 (GeometricThickening.neg_le_band quarter)⟩)
  have h := hupper (i.φ.hom.left.hom q)
  rw [overBaseMap_comm i.φ.hom q] at h
  change overBaseMap singleGraph.obj edgeTop + (quarter : ℝ) ≤
      3 / 4 + (ε : ℝ) at h
  rw [height_edgeTop] at h
  norm_num [coe_quarter] at h
  linarith

/-- Smoothing the edge and midpoint by a quarter preserves their exact geometric distance of one
half. -/
theorem geometricInterleavingDistance_smoothed_edge_mid :
    geometricInterleavingDistance ((geometricSmoothing quarter).obj singleGraph)
        ((geometricSmoothing quarter).obj midGraph) = 1 / 2 := by
  refine le_antisymm ?_ (le_geometricInterleavingDistance_iff.2 fun ε ⟨i⟩ => ?_)
  · rw [← coe_halfNN_ennreal]
    exact edgeMidInterleaving.geometricInterleavingDistance_smooth_le quarter
  · rw [← coe_halfNN_ennreal, ENNReal.coe_le_coe, ← NNReal.coe_le_coe, coe_halfNN]
    by_contra h
    exact (smoothed_edgeMid_isEmpty ε (not_le.1 h)).false i

/-- The distance from the quarter-smoothed edge to the original midpoint is at most one half plus
one quarter. -/
theorem geometricInterleavingDistance_smoothed_single_mid_le :
    geometricInterleavingDistance ((geometricSmoothing quarter).obj singleGraph) midGraph ≤
      1 / 2 + 1 / 4 := by
  calc
    geometricInterleavingDistance ((geometricSmoothing quarter).obj singleGraph) midGraph ≤
        geometricInterleavingDistance singleGraph midGraph + (quarter : ℝ≥0∞) :=
      geometricInterleavingDistance_geometricSmoothing_left_le quarter singleGraph midGraph
    _ = 1 / 2 + 1 / 4 := by rw [geometricInterleavingDistance_edge_mid, coe_quarter_ennreal]

/-- The distance between the half-smoothed parallel and single graphs is at most one quarter. -/
theorem geometricInterleavingDistance_smoothed_parallel_single_le :
    geometricInterleavingDistance ((geometricSmoothing halfNN).obj parallelGraph)
        ((geometricSmoothing halfNN).obj singleGraph) ≤ 1 / 4 := by
  rw [← coe_quarter_ennreal]
  exact parallelSingleInterleaving.geometricInterleavingDistance_smooth_le halfNN

end Examples.GeometricSmoothInterleaving

end

end TDA.Reeb
