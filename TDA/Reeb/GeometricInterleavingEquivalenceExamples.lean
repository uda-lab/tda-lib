import TDA.Reeb.GeometricInterleavingEquivalence
import TDA.Reeb.GeometricInterleavingExamples

/-!
# Fixtures for the equivalence of geometric and cosheaf interleavings

Acceptance fixtures for `TDA.Reeb.GeometricInterleavingEquivalence`, on the graph objects of
`TDA.Reeb.GeometricInterleavingExamples`:

* **Round trip on a witness.** The geometric `1/2`-interleaving of the single edge and its
  midpoint is recovered from its precosheaf interleaving, and its first shifted map is recovered
  from the shifted-map bijection.
* **Exact cosheaf distance `1/2`.** The component precosheaves of the edge and its midpoint are at
  interleaving distance exactly `1/2`, and no precosheaf `ε`-interleaving of them exists for
  `ε < 1/2`. Likewise the component precosheaves of the two parallel edges and the single edge
  admit no `0`-interleaving.
* **Composite witness and the triangle instance.** The `1/4`-interleaving of the parallel edges
  with the single edge, composed with the `1/2`-interleaving of the edge with its midpoint, is a
  geometric `(1/4 + 1/2)`-interleaving; its cosheaf image and its first component are written out.
  The triangle inequality gives `d_geo(parallel, midpoint) ≤ 1/4 + 1/2`; no exact value is
  claimed.
* **Isomorphism invariance.** The subdivided edge is at distance `1/2` from the midpoint.
* **Zero-distance controls.** The subdivided edge and the edge have witnesses at every positive
  parameter; the edge and its midpoint do not.
-/

open Set Topology CategoryTheory
open scoped NNReal ENNReal

namespace TDA.Reeb

noncomputable section

namespace Examples.GeometricInterleavingEquivalence

open RGraph
open TDA.Reeb.Examples.RGraphCosheafEquivalence (parallelGraph singleGraph singleHalfGraph
  subdivisionIso)
open TDA.Reeb.Examples.RGraphThickening (halfNN)
open TDA.Reeb.Examples.ConstructibleSmoothing (quarter)
open TDA.Reeb.Examples.GeometricInterleaving (midGraph edgeMidInterleaving edgeMid_isEmpty
  geometricInterleavingDistance_edge_mid parallelSingleInterleaving
  geometricInterleavingDistance_parallel_single_le parallelSingle_zero_isEmpty
  geometricInterleavingDistance_singleHalf_single)

/-! ### Round trip on a witness -/

/-- The edge–midpoint witness is recovered from its precosheaf interleaving. -/
theorem cosheafEquiv_symm_edgeMid :
    (GeometricInterleaving.cosheafEquiv halfNN singleGraph midGraph).symm
        edgeMidInterleaving.toCosheaf = edgeMidInterleaving :=
  (GeometricInterleaving.cosheafEquiv halfNN singleGraph midGraph).symm_apply_apply _

/-- The first precosheaf map of the witness is the shifted map of its preimage. -/
theorem cosheafShiftMap_cosheafShiftEquiv_symm_edgeMid :
    cosheafShiftMap ((cosheafShiftEquiv halfNN singleGraph midGraph).symm
        edgeMidInterleaving.toCosheaf.φ) = edgeMidInterleaving.toCosheaf.φ :=
  cosheafShiftMap_cosheafShiftEquiv_symm _

/-! ### Exact cosheaf distance and the cosheaf-side threshold -/

/-- **Exact cosheaf distance.** The component precosheaves of the edge and its midpoint are at
interleaving distance `1/2`. -/
theorem interleavingDistance_edge_mid :
    interleavingDistance (cosheafFunctor.obj singleGraph).obj (cosheafFunctor.obj midGraph).obj =
      1 / 2 :=
  (geometricInterleavingDistance_eq_interleavingDistance _ _).symm.trans
    geometricInterleavingDistance_edge_mid

/-- **Cosheaf-side threshold.** For `ε < 1/2` the component precosheaves of the edge and its
midpoint admit no `ε`-interleaving. -/
theorem interleaving_edgeMid_isEmpty {ε : ℝ≥0} (hε : (ε : ℝ) < 1 / 2) :
    IsEmpty (Interleaving ε (cosheafFunctor.obj singleGraph).obj
      (cosheafFunctor.obj midGraph).obj) :=
  haveI := edgeMid_isEmpty hε
  (GeometricInterleaving.cosheafEquiv ε _ _).symm.isEmpty

/-- The component precosheaves of the two parallel edges and the single edge admit no
`0`-interleaving. -/
theorem interleaving_parallelSingle_zero_isEmpty :
    IsEmpty (Interleaving 0 (cosheafFunctor.obj parallelGraph).obj
      (cosheafFunctor.obj singleGraph).obj) :=
  haveI := parallelSingle_zero_isEmpty
  (GeometricInterleaving.cosheafEquiv 0 _ _).symm.isEmpty

/-! ### Composite witness and the triangle instance -/

/-- **Composite witness**: parallel edges ↔ edge at `1/4`, then edge ↔ midpoint at `1/2`. -/
def parallelMidInterleaving : GeometricInterleaving (quarter + halfNN) parallelGraph midGraph :=
  parallelSingleInterleaving.trans edgeMidInterleaving

theorem parallelMidInterleaving_toCosheaf :
    parallelMidInterleaving.toCosheaf =
      parallelSingleInterleaving.toCosheaf.trans edgeMidInterleaving.toCosheaf :=
  GeometricInterleaving.trans_toCosheaf _ _

theorem parallelMidInterleaving_φ :
    parallelMidInterleaving.φ =
      parallelSingleInterleaving.φ ≫ (geometricSmoothing quarter).map edgeMidInterleaving.φ ≫
        (geometricSmoothingCompIso quarter halfNN).hom.app midGraph :=
  GeometricInterleaving.trans_φ _ _

/-- **Triangle instance**: `d_geo(parallel, midpoint) ≤ 1/4 + 1/2`. -/
theorem geometricInterleavingDistance_parallel_mid_le :
    geometricInterleavingDistance parallelGraph midGraph ≤ 1 / 4 + 1 / 2 :=
  (geometricInterleavingDistance_triangle parallelGraph singleGraph midGraph).trans
    (add_le_add geometricInterleavingDistance_parallel_single_le
      geometricInterleavingDistance_edge_mid.le)

/-! ### Isomorphism invariance across presentations -/

/-- The single edge over `0 < 1/2 < 1` is at distance `1/2` from the midpoint. -/
theorem geometricInterleavingDistance_singleHalf_mid :
    geometricInterleavingDistance singleHalfGraph midGraph = 1 / 2 :=
  (geometricInterleavingDistance_congr_left subdivisionIso midGraph).trans
    geometricInterleavingDistance_edge_mid

/-! ### Zero-distance controls -/

/-- **Positive control**: the two presentations of the edge have geometric witnesses at every
positive parameter. -/
theorem singleHalf_single_nonempty :
    ∀ ε : ℝ≥0, 0 < ε → Nonempty (GeometricInterleaving ε singleHalfGraph singleGraph) :=
  geometricInterleavingDistance_eq_zero_iff.1 geometricInterleavingDistance_singleHalf_single

/-- **Negative control**: the edge and its midpoint do not have witnesses at every positive
parameter. -/
theorem not_edge_mid_nonempty :
    ¬ ∀ ε : ℝ≥0, 0 < ε → Nonempty (GeometricInterleaving ε singleGraph midGraph) := by
  intro h
  have h0 := geometricInterleavingDistance_eq_zero_iff.2 h
  rw [geometricInterleavingDistance_edge_mid] at h0
  simp at h0

end Examples.GeometricInterleavingEquivalence

end

end TDA.Reeb
