import TDA.Reeb.ConstructibleRepresentation
import TDA.Reeb.ConstructibleCylinderExamples

/-!
# Examples: constructible cosheaves from finite data

All cosheaves below are actual component cosheaves `D.toCosheaf S` of realized finite data, or
arbitrary constructible interval cosheaves.

* Pinch `DP` at the levels `S01 = {0, 1}`: two edges whose bottom ends both go to vertex `0`.
  The left incidence merges the two labelled edges and the right incidence separates them, with
  the edge label computed at the regular height `3/4`. The reconstruction preserves the named
  labels on both stars, which are the rays `J 0 = (-∞, 1)` and `J 1 = (0, ∞)`, and on the gap,
  and both natural-transformation inverse identities hold.
* Pinch reconstruction on intervals meeting both levels: on any interval containing a level, it
  sends the class of each realized vertex point to the class of the original vertex, and on any
  interval containing a regular height it does the same for strip points. These are stated on
  `⊤`, on `(-1, 2)`, on the ray `iio 2` and on the ray `ioi (-1)`. On `ℝ` the class of the merging
  vertex at level `0` coincides with the class of each vertex at level `1`, in the original and in
  the reconstructed cosheaf, so the two stars glue along the gap; the reconstruction sends the
  class coming from one star to the class coming from the other.
* Pinch boundary cases: on `(1/4, 3/4)`, a nonempty interval containing no level, the
  reconstruction is computed on strip classes. The empty interval and both exterior tails have
  empty values for both the reconstructed and the original cosheaf.
* The pinch at value universe `1`.
* Empty data: the zero cosheaf maps uniquely to every `Type`-valued constructible interval cosheaf
  at the same levels, and the vertex and edge sets of its extracted data are empty.
* `n = 0`: one vertex; the value on `ℝ` has one element, and the reconstruction is computed on
  `ℝ = J 0` through the inclusion `J 0 ≤ ⊤`.
* Parallel edges: the identity labelling lifts to the identity, and the swap labelling lifts to a
  different automorphism, so labelled uniqueness does not erase unlabelled automorphisms.
* Insertion of the level `1` into `S02 = {0, 2}`, giving `S012 = {0, 1, 2}`, for the same `F`
  constructible at `S02`: the new middle star is the old gap, both inserted incidences are
  bijective, and transported along that equality they are the covariant inclusions of the new
  gaps into the old gap. The two reconstructions compare through `F`.
-/

open Set CategoryTheory

universe u

namespace TDA.Reeb

noncomputable section

namespace Examples.ConstructibleRepresentation

open CylinderPresentation OpenInterval FiniteReebData CriticalValues
open TDA.Reeb.Examples.Cylinder TDA.Reeb.Examples.ConstructibleCylinder

/-! ### The pinch fixture `DP` at `S01 = {0, 1}` -/

/-- The pinch cosheaf: the actual component cosheaf of the pinch data `DP`. -/
abbrev FP : OpenInterval ⥤ Type := DP.toCosheaf S01

/-- The pinch cosheaf is the path-component cosheaf of the pinch height. -/
theorem FP_eq : FP = intervalComponents hP := rfl

/-- The pinch cosheaf is constructible at `S01`. -/
theorem FP_isConstructibleAt : S01.IsConstructibleAt FP := DP.toCosheaf_isConstructibleAt S01

/-- The pinch cosheaf is an interval cosheaf. -/
theorem FP_isIntervalCosheaf : IsIntervalCosheaf.{0} FP := DP.toCosheaf_isIntervalCosheaf S01

/-- Left incidence of the pinch labels: both edges go to vertex `0`. -/
theorem pinch_left_label (y : Fin 2) :
    FP.map (homOfLE (S01.K_le_J_castSucc 0)) (DP.edgeLabel S01 0 y) =
      DP.vertexLabel S01 0 (0 : Fin 2) :=
  DP.map_K_le_J_castSucc_edgeLabel S01 0 y

/-- Right incidence of the pinch labels: edge `y` goes to vertex `y`. -/
theorem pinch_right_label (y : Fin 2) :
    FP.map (homOfLE (S01.K_le_J_succ 0)) (DP.edgeLabel S01 0 y) = DP.vertexLabel S01 1 y :=
  DP.map_K_le_J_succ_edgeLabel S01 0 y

/-- The left incidence merges two distinct edge labels; the right one separates them. -/
theorem pinch_left_merges_right_separates :
    DP.edgeLabel S01 0 (0 : Fin 2) ≠ DP.edgeLabel S01 0 (1 : Fin 2) ∧
      FP.map (homOfLE (S01.K_le_J_castSucc 0)) (DP.edgeLabel S01 0 (0 : Fin 2)) =
        FP.map (homOfLE (S01.K_le_J_castSucc 0)) (DP.edgeLabel S01 0 (1 : Fin 2)) ∧
      FP.map (homOfLE (S01.K_le_J_succ 0)) (DP.edgeLabel S01 0 (0 : Fin 2)) ≠
        FP.map (homOfLE (S01.K_le_J_succ 0)) (DP.edgeLabel S01 0 (1 : Fin 2)) := by
  refine ⟨fun h => (by decide : (0 : Fin 2) ≠ 1) ((DP.edgeLabel S01 0).injective h),
    (pinch_left_label 0).trans (pinch_left_label 1).symm, fun h => ?_⟩
  rw [pinch_right_label, pinch_right_label] at h
  exact (by decide : (0 : Fin 2) ≠ 1) ((DP.vertexLabel S01 1).injective h)

/-- The edge label at the regular height `3/4` (away from both vertices), not the midpoint. -/
theorem pinch_edgeLabel_threeQuarters (y : Fin 2) :
    DP.edgeLabel S01 0 y =
      ZerothHomotopy.mk (⟨(ofFiniteData DP).ofStrip S01 0 (y, threeQuarters), threeQuarters.2⟩ :
        (ofFiniteData DP).heightPreimage S01 (S01.K 0)) :=
  DP.edgeLabel_apply S01 0 threeQuarters y

/-- The extracted pinch data. -/
abbrev DPx : FiniteReebData.{0} 1 := S01.extract FP FP_isConstructibleAt.finite

/-- The reconstruction of the pinch cosheaf from its extracted data. -/
abbrev pinchRecon : DPx.toCosheaf S01 ≅ FP :=
  realizeExtractIso FP_isConstructibleAt FP_isIntervalCosheaf

/-- Star computation on the ray `J 0 = (-∞, 1)`. -/
theorem pinch_recon_J0 (v : Fin 2) :
    pinchRecon.hom.app (S01.J 0) (DPx.vertexLabel S01 0 (DP.vertexLabel S01 0 v)) =
      DP.vertexLabel S01 0 v :=
  realizeExtractIso_hom_app_J _ _ 0 _

/-- Star computation on the ray `J 1 = (0, ∞)`. -/
theorem pinch_recon_J1 (v : Fin 2) :
    pinchRecon.hom.app (S01.J 1) (DPx.vertexLabel S01 1 (DP.vertexLabel S01 1 v)) =
      DP.vertexLabel S01 1 v :=
  realizeExtractIso_hom_app_J _ _ 1 _

/-- Gap computation: the named edge labels are preserved, not only the cardinality. -/
theorem pinch_recon_K (y : Fin 2) :
    pinchRecon.hom.app (S01.K 0) (DPx.edgeLabel S01 0 (DP.edgeLabel S01 0 y)) =
      DP.edgeLabel S01 0 y :=
  realizeExtractIso_hom_app_K _ _ 0 _

/-- The inverse of the pinch reconstruction on the gap is the edge label map. -/
theorem pinch_recon_inv_K (y : Fin 2) :
    pinchRecon.inv.app (S01.K 0) (DP.edgeLabel S01 0 y) =
      DPx.edgeLabel S01 0 (DP.edgeLabel S01 0 y) :=
  realizeExtractIso_inv_app_K _ _ 0 _

/-- In the reconstructed cosheaf the left incidence still merges the two labelled edges. -/
theorem pinch_reconstructed_left (y : Fin 2) :
    (DPx.toCosheaf S01).map (homOfLE (S01.K_le_J_castSucc 0))
        (DPx.edgeLabel S01 0 (DP.edgeLabel S01 0 y)) =
      DPx.vertexLabel S01 0 (DP.vertexLabel S01 0 (0 : Fin 2)) :=
  (DPx.map_K_le_J_castSucc_edgeLabel S01 0 _).trans
    (congrArg (DPx.vertexLabel S01 0) (pinch_left_label y))

/-- Both natural-transformation inverse identities of the pinch reconstruction. -/
theorem pinch_recon_inverse_identities :
    pinchRecon.hom ≫ pinchRecon.inv = 𝟙 _ ∧ pinchRecon.inv ≫ pinchRecon.hom = 𝟙 _ :=
  ⟨pinchRecon.hom_inv_id, pinchRecon.inv_hom_id⟩

/-- The regular height `1/2` lies in `(1/4, 3/4)`. -/
theorem half_mem_quarter : ((half : (S01.K 0 : Set ℝ)) : ℝ) ∈ ioo (1 / 4 : ℝ) (3 / 4) := by
  show (1 / 4 : ℝ) < 1 / 2 ∧ (1 / 2 : ℝ) < 3 / 4
  norm_num

/-- A nonempty interval with no level, `(1/4, 3/4)`: the reconstruction sends the strip point at
`1/2` over the label of edge `y` to the strip point of edge `y` at `1/2`. -/
theorem pinch_recon_regular (y : Fin 2) :
    pinchRecon.hom.app (ioo (1 / 4) (3 / 4))
        (ZerothHomotopy.mk (⟨(ofFiniteData DPx).ofStrip S01 0 (DP.edgeLabel S01 0 y, half),
          half_mem_quarter⟩ : (ofFiniteData DPx).heightPreimage S01 (ioo (1 / 4) (3 / 4)))) =
      ZerothHomotopy.mk (⟨(ofFiniteData DP).ofStrip S01 0 (y, half), half_mem_quarter⟩ :
        (ofFiniteData DP).heightPreimage S01 (ioo (1 / 4) (3 / 4))) := by
  apply pinch_regular_bijective.injective
  refine (map_realizeExtractIso_hom_app_strip FP_isConstructibleAt FP_isIntervalCosheaf
    quarter_le_K half half_mem_quarter (DP.edgeLabel S01 0 y)).trans ?_
  exact DP.edgeLabel_apply S01 0 half y

/-- The empty interval and both exterior tails have empty values, for the reconstructed and for
the original cosheaf. -/
theorem pinch_recon_empty_values :
    IsEmpty ((DPx.toCosheaf S01).obj ⊥) ∧ IsEmpty (FP.obj ⊥) ∧
      IsEmpty ((DPx.toCosheaf S01).obj S01.lowerTail) ∧ IsEmpty (FP.obj S01.lowerTail) ∧
      IsEmpty ((DPx.toCosheaf S01).obj S01.upperTail) ∧ IsEmpty (FP.obj S01.upperTail) :=
  ⟨(DPx.toCosheaf_isIntervalCosheaf S01 : IsIntervalCosheaf.{0} _).isEmpty_obj_bot,
    FP_isIntervalCosheaf.isEmpty_obj_bot,
    (DPx.toCosheaf_isConstructibleAt S01).isEmpty_lowerTail, FP_isConstructibleAt.isEmpty_lowerTail,
    (DPx.toCosheaf_isConstructibleAt S01).isEmpty_upperTail, FP_isConstructibleAt.isEmpty_upperTail⟩

/-! ### The pinch reconstruction on intervals meeting both levels

On these intervals the reconstruction is the glued extension, not a star or gap value. -/

/-- On any interval containing the level `a i`, the pinch reconstruction sends the class of the
realized vertex point labelled by `λV v` to the class of the vertex point `v` itself. -/
theorem pinch_recon_vertex {I : OpenInterval} (i : Fin 2) (hi : S01.value i ∈ I) (v : Fin 2) :
    pinchRecon.hom.app I
        (ZerothHomotopy.mk (⟨(ofFiniteData DPx).ofVertex S01 i (DP.vertexLabel S01 i v), hi⟩ :
          (ofFiniteData DPx).heightPreimage S01 I)) =
      ZerothHomotopy.mk (⟨(ofFiniteData DP).ofVertex S01 i v, hi⟩ :
        (ofFiniteData DP).heightPreimage S01 I) := by
  have hiA : S01.value i ∈ I ⊓ S01.J i := Set.mem_inter hi (S01.value_mem_J i)
  have hinj : Function.Injective (FP.map (homOfLE (inf_le_right : I ⊓ S01.J i ≤ S01.J i))) :=
    (FP_isConstructibleAt.bijective (inf_le_right : I ⊓ S01.J i ≤ S01.J i) ⟨_, hiA⟩ fun k =>
      ⟨fun h => Set.mem_of_mem_inter_right h,
        fun h => Set.mem_inter ((S01.value_mem_J_iff.1 h) ▸ hi) h⟩).1
  have hA : pinchRecon.hom.app (I ⊓ S01.J i)
      (ZerothHomotopy.mk (⟨(ofFiniteData DPx).ofVertex S01 i (DP.vertexLabel S01 i v), hiA⟩ :
        (ofFiniteData DPx).heightPreimage S01 (I ⊓ S01.J i))) =
      ZerothHomotopy.mk (⟨(ofFiniteData DP).ofVertex S01 i v, hiA⟩ :
        (ofFiniteData DP).heightPreimage S01 (I ⊓ S01.J i)) := by
    apply hinj
    exact (map_realizeExtractIso_hom_app_vertex FP_isConstructibleAt FP_isIntervalCosheaf
      inf_le_right hiA (DP.vertexLabel S01 i v)).trans (DP.vertexLabel_apply S01 i v)
  have key := NatTrans.naturality_apply pinchRecon.hom
    (homOfLE (inf_le_left : I ⊓ S01.J i ≤ I))
    (ZerothHomotopy.mk (⟨(ofFiniteData DPx).ofVertex S01 i (DP.vertexLabel S01 i v), hiA⟩ :
      (ofFiniteData DPx).heightPreimage S01 (I ⊓ S01.J i)))
  exact key.trans (congrArg (fun z => FP.map (homOfLE (inf_le_left : I ⊓ S01.J i ≤ I)) z) hA)

/-- On any interval containing the regular height `t`, the pinch reconstruction sends the class
of the realized strip point over `λE y` at `t` to the class of the strip point of edge `y` at
`t`. -/
theorem pinch_recon_strip {I : OpenInterval} (t : (S01.K 0 : Set ℝ)) (ht : (t : ℝ) ∈ I)
    (y : Fin 2) :
    pinchRecon.hom.app I
        (ZerothHomotopy.mk (⟨(ofFiniteData DPx).ofStrip S01 0 (DP.edgeLabel S01 0 y, t), ht⟩ :
          (ofFiniteData DPx).heightPreimage S01 I)) =
      ZerothHomotopy.mk (⟨(ofFiniteData DP).ofStrip S01 0 (y, t), ht⟩ :
        (ofFiniteData DP).heightPreimage S01 I) := by
  have htA : (t : ℝ) ∈ I ⊓ S01.K 0 := Set.mem_inter ht t.2
  have hinj : Function.Injective (FP.map (homOfLE (inf_le_right : I ⊓ S01.K 0 ≤ S01.K 0))) :=
    (FP_isConstructibleAt.bijective (inf_le_right : I ⊓ S01.K 0 ≤ S01.K 0) ⟨_, htA⟩ fun k =>
      iff_of_false (fun h => S01.value_notMem_K 0 k (Set.mem_of_mem_inter_right h))
        (S01.value_notMem_K 0 k)).1
  have hA : pinchRecon.hom.app (I ⊓ S01.K 0)
      (ZerothHomotopy.mk (⟨(ofFiniteData DPx).ofStrip S01 0 (DP.edgeLabel S01 0 y, t), htA⟩ :
        (ofFiniteData DPx).heightPreimage S01 (I ⊓ S01.K 0))) =
      ZerothHomotopy.mk (⟨(ofFiniteData DP).ofStrip S01 0 (y, t), htA⟩ :
        (ofFiniteData DP).heightPreimage S01 (I ⊓ S01.K 0)) := by
    apply hinj
    exact (map_realizeExtractIso_hom_app_strip FP_isConstructibleAt FP_isIntervalCosheaf
      inf_le_right t htA (DP.edgeLabel S01 0 y)).trans (DP.edgeLabel_apply S01 0 t y)
  have key := NatTrans.naturality_apply pinchRecon.hom
    (homOfLE (inf_le_left : I ⊓ S01.K 0 ≤ I))
    (ZerothHomotopy.mk (⟨(ofFiniteData DPx).ofStrip S01 0 (DP.edgeLabel S01 0 y, t), htA⟩ :
      (ofFiniteData DPx).heightPreimage S01 (I ⊓ S01.K 0)))
  exact key.trans (congrArg (fun z => FP.map (homOfLE (inf_le_left : I ⊓ S01.K 0 ≤ I)) z) hA)

/-- Both pinch levels lie in `[0, 1]`. -/
theorem S01_value_bounds (i : Fin 2) : 0 ≤ S01.value i ∧ S01.value i ≤ 1 := by
  show (0 : ℝ) ≤ ((i : ℕ) : ℝ) ∧ ((i : ℕ) : ℝ) ≤ 1
  exact ⟨Nat.cast_nonneg _, by exact_mod_cast Nat.lt_succ_iff.1 i.isLt⟩

/-- The pinch gap is `(0, 1)`. -/
theorem S01_mem_K0 {x : ℝ} (hx : x ∈ S01.K 0) : 0 < x ∧ x < 1 := by
  rw [S01.mem_K] at hx
  simpa only [Fin.castSucc_zero, Fin.succ_zero_eq_one, S01_value_zero, S01_value_one] using hx

/-- Both levels lie in `(-1, 2)`. -/
theorem S01_value_mem_ioo (i : Fin 2) : S01.value i ∈ ioo (-1) 2 := by
  rw [mem_ioo]
  constructor <;> linarith [S01_value_bounds i]

/-- Both levels lie in the ray `iio 2 = (-∞, 2)`. -/
theorem S01_value_mem_iio (i : Fin 2) : S01.value i ∈ iio 2 := by
  rw [mem_iio]
  linarith [S01_value_bounds i]

/-- Both levels lie in the ray `ioi (-1) = (-1, ∞)`. -/
theorem S01_value_mem_ioi (i : Fin 2) : S01.value i ∈ ioi (-1) := by
  rw [mem_ioi]
  linarith [S01_value_bounds i]

/-- The pinch gap lies in `(-1, 2)`. -/
theorem K0_le_ioo : S01.K 0 ≤ ioo (-1) 2 := fun x hx => by
  have h := S01_mem_K0 hx
  rw [mem_ioo]
  constructor <;> linarith [h.1, h.2]

/-- The pinch gap lies in the ray `iio 2`. -/
theorem K0_le_iio : S01.K 0 ≤ iio 2 := fun x hx => by
  have h := S01_mem_K0 hx
  rw [mem_iio]
  linarith [h.2]

/-- The pinch gap lies in the ray `ioi (-1)`. -/
theorem K0_le_ioi : S01.K 0 ≤ ioi (-1) := fun x hx => by
  have h := S01_mem_K0 hx
  rw [mem_ioi]
  linarith [h.1]

/-- The reconstruction on `ℝ` at the vertex points of both levels. -/
theorem pinch_recon_top_vertex (i v : Fin 2) :
    pinchRecon.hom.app ⊤
        (ZerothHomotopy.mk (⟨(ofFiniteData DPx).ofVertex S01 i (DP.vertexLabel S01 i v),
          trivial⟩ : (ofFiniteData DPx).heightPreimage S01 ⊤)) =
      ZerothHomotopy.mk (⟨(ofFiniteData DP).ofVertex S01 i v, trivial⟩ :
        (ofFiniteData DP).heightPreimage S01 ⊤) :=
  pinch_recon_vertex (I := ⊤) i trivial v

/-- The reconstruction on `ℝ` at the strip points of every regular height. -/
theorem pinch_recon_top_strip (t : (S01.K 0 : Set ℝ)) (y : Fin 2) :
    pinchRecon.hom.app ⊤
        (ZerothHomotopy.mk (⟨(ofFiniteData DPx).ofStrip S01 0 (DP.edgeLabel S01 0 y, t),
          trivial⟩ : (ofFiniteData DPx).heightPreimage S01 ⊤)) =
      ZerothHomotopy.mk (⟨(ofFiniteData DP).ofStrip S01 0 (y, t), trivial⟩ :
        (ofFiniteData DP).heightPreimage S01 ⊤) :=
  pinch_recon_strip (I := ⊤) t trivial y

/-- The reconstruction on the bounded interval `(-1, 2)`, which meets both levels, at the vertex
points of both levels. -/
theorem pinch_recon_ioo_vertex (i v : Fin 2) :
    pinchRecon.hom.app (ioo (-1) 2)
        (ZerothHomotopy.mk (⟨(ofFiniteData DPx).ofVertex S01 i (DP.vertexLabel S01 i v),
          S01_value_mem_ioo i⟩ : (ofFiniteData DPx).heightPreimage S01 (ioo (-1) 2))) =
      ZerothHomotopy.mk (⟨(ofFiniteData DP).ofVertex S01 i v, S01_value_mem_ioo i⟩ :
        (ofFiniteData DP).heightPreimage S01 (ioo (-1) 2)) :=
  pinch_recon_vertex i (S01_value_mem_ioo i) v

/-- The reconstruction on `(-1, 2)` at the strip points of every regular height. -/
theorem pinch_recon_ioo_strip (t : (S01.K 0 : Set ℝ)) (y : Fin 2) :
    pinchRecon.hom.app (ioo (-1) 2)
        (ZerothHomotopy.mk (⟨(ofFiniteData DPx).ofStrip S01 0 (DP.edgeLabel S01 0 y, t),
          K0_le_ioo t.2⟩ : (ofFiniteData DPx).heightPreimage S01 (ioo (-1) 2))) =
      ZerothHomotopy.mk (⟨(ofFiniteData DP).ofStrip S01 0 (y, t), K0_le_ioo t.2⟩ :
        (ofFiniteData DP).heightPreimage S01 (ioo (-1) 2)) :=
  pinch_recon_strip t (K0_le_ioo t.2) y

/-- The reconstruction on the ray `iio 2 = (-∞, 2)`, which meets both levels, at the vertex points
of both levels. -/
theorem pinch_recon_iio_vertex (i v : Fin 2) :
    pinchRecon.hom.app (iio 2)
        (ZerothHomotopy.mk (⟨(ofFiniteData DPx).ofVertex S01 i (DP.vertexLabel S01 i v),
          S01_value_mem_iio i⟩ : (ofFiniteData DPx).heightPreimage S01 (iio 2))) =
      ZerothHomotopy.mk (⟨(ofFiniteData DP).ofVertex S01 i v, S01_value_mem_iio i⟩ :
        (ofFiniteData DP).heightPreimage S01 (iio 2)) :=
  pinch_recon_vertex i (S01_value_mem_iio i) v

/-- The reconstruction on the ray `iio 2` at the strip points of every regular height. -/
theorem pinch_recon_iio_strip (t : (S01.K 0 : Set ℝ)) (y : Fin 2) :
    pinchRecon.hom.app (iio 2)
        (ZerothHomotopy.mk (⟨(ofFiniteData DPx).ofStrip S01 0 (DP.edgeLabel S01 0 y, t),
          K0_le_iio t.2⟩ : (ofFiniteData DPx).heightPreimage S01 (iio 2))) =
      ZerothHomotopy.mk (⟨(ofFiniteData DP).ofStrip S01 0 (y, t), K0_le_iio t.2⟩ :
        (ofFiniteData DP).heightPreimage S01 (iio 2)) :=
  pinch_recon_strip t (K0_le_iio t.2) y

/-- The reconstruction on the ray `ioi (-1) = (-1, ∞)`, which meets both levels, at the vertex
points of both levels. -/
theorem pinch_recon_ioi_vertex (i v : Fin 2) :
    pinchRecon.hom.app (ioi (-1))
        (ZerothHomotopy.mk (⟨(ofFiniteData DPx).ofVertex S01 i (DP.vertexLabel S01 i v),
          S01_value_mem_ioi i⟩ : (ofFiniteData DPx).heightPreimage S01 (ioi (-1)))) =
      ZerothHomotopy.mk (⟨(ofFiniteData DP).ofVertex S01 i v, S01_value_mem_ioi i⟩ :
        (ofFiniteData DP).heightPreimage S01 (ioi (-1))) :=
  pinch_recon_vertex i (S01_value_mem_ioi i) v

/-- The reconstruction on the ray `ioi (-1)` at the strip points of every regular height. -/
theorem pinch_recon_ioi_strip (t : (S01.K 0 : Set ℝ)) (y : Fin 2) :
    pinchRecon.hom.app (ioi (-1))
        (ZerothHomotopy.mk (⟨(ofFiniteData DPx).ofStrip S01 0 (DP.edgeLabel S01 0 y, t),
          K0_le_ioi t.2⟩ : (ofFiniteData DPx).heightPreimage S01 (ioi (-1)))) =
      ZerothHomotopy.mk (⟨(ofFiniteData DP).ofStrip S01 0 (y, t), K0_le_ioi t.2⟩ :
        (ofFiniteData DP).heightPreimage S01 (ioi (-1))) :=
  pinch_recon_strip t (K0_le_ioi t.2) y

/-- On `ℝ` the two stars glue along the gap: the class of the merging vertex `0` at level `0`
coincides with the class of each vertex `y` at level `1`. -/
theorem pinch_top_glue (y : Fin 2) :
    FP.map (homOfLE (le_top : S01.J 0 ≤ ⊤)) (DP.vertexLabel S01 0 (0 : Fin 2)) =
      FP.map (homOfLE (le_top : S01.J 1 ≤ ⊤)) (DP.vertexLabel S01 1 y) := by
  rw [← pinch_left_label y, ← pinch_right_label y, ← Functor.map_comp_apply,
    ← Functor.map_comp_apply]
  exact congrArg (fun f => FP.map f (DP.edgeLabel S01 0 y)) (Subsingleton.elim _ _)

/-- The same gluing in the reconstructed cosheaf: on `ℝ` the class of the label of vertex `0` at
level `0` coincides with the class of the label of each vertex `y` at level `1`. -/
theorem pinch_reconstructed_top_glue (y : Fin 2) :
    (DPx.toCosheaf S01).map (homOfLE (le_top : S01.J 0 ≤ ⊤))
        (DPx.vertexLabel S01 0 (DP.vertexLabel S01 0 (0 : Fin 2))) =
      (DPx.toCosheaf S01).map (homOfLE (le_top : S01.J 1 ≤ ⊤))
        (DPx.vertexLabel S01 1 (DP.vertexLabel S01 1 y)) := by
  rw [← pinch_reconstructed_left y]
  have hr : (DPx.toCosheaf S01).map (homOfLE (S01.K_le_J_succ 0))
      (DPx.edgeLabel S01 0 (DP.edgeLabel S01 0 y)) =
        DPx.vertexLabel S01 1 (DP.vertexLabel S01 1 y) :=
    (DPx.map_K_le_J_succ_edgeLabel S01 0 _).trans
      (congrArg (DPx.vertexLabel S01 1) (pinch_right_label y))
  rw [← hr, ← Functor.map_comp_apply, ← Functor.map_comp_apply]
  exact congrArg (fun f => (DPx.toCosheaf S01).map f (DPx.edgeLabel S01 0 (DP.edgeLabel S01 0 y)))
    (Subsingleton.elim _ _)

/-- The reconstruction on `ℝ` sends the class coming from the star `J 0` of the label of vertex
`0` to the class coming from the other star `J 1` of vertex `y`. -/
theorem pinch_recon_top_glue (y : Fin 2) :
    pinchRecon.hom.app ⊤ ((DPx.toCosheaf S01).map (homOfLE (le_top : S01.J 0 ≤ ⊤))
        (DPx.vertexLabel S01 0 (DP.vertexLabel S01 0 (0 : Fin 2)))) =
      FP.map (homOfLE (le_top : S01.J 1 ≤ ⊤)) (DP.vertexLabel S01 1 y) := by
  rw [NatTrans.naturality_apply, pinch_recon_J0]
  exact pinch_top_glue y

/-! ### An independent value universe -/

/-- The pinch data at value universe `1`. -/
def DPu : FiniteReebData.{1} 1 :=
  ⟨fun _ => ULift.{1} (Fin 2), fun _ => ULift.{1} (Fin 2), fun _ => inferInstance,
    fun _ => inferInstance, fun _ _ => ⟨0⟩, fun _ y => y⟩

/-- The pinch cosheaf at value universe `1`. -/
abbrev FPu : OpenInterval ⥤ Type 1 := DPu.toCosheaf S01

/-- The universe-`1` pinch cosheaf is constructible at `S01`. -/
theorem FPu_isConstructibleAt : S01.IsConstructibleAt FPu := DPu.toCosheaf_isConstructibleAt S01

/-- The universe-`1` pinch cosheaf is an interval cosheaf. -/
theorem FPu_isIntervalCosheaf : IsIntervalCosheaf.{0} FPu := DPu.toCosheaf_isIntervalCosheaf S01

/-- The reconstruction of the universe-`1` pinch cosheaf. -/
abbrev pinchReconU := realizeExtractIso FPu_isConstructibleAt FPu_isIntervalCosheaf

/-- Gap computation at value universe `1`. -/
theorem pinchU_recon_K (y : ULift.{1} (Fin 2)) :
    pinchReconU.hom.app (S01.K 0)
        ((S01.extract FPu FPu_isConstructibleAt.finite).edgeLabel S01 0 (DPu.edgeLabel S01 0 y)) =
      DPu.edgeLabel S01 0 y :=
  realizeExtractIso_hom_app_K _ _ 0 _

/-- Left incidence of the labels at value universe `1`. -/
theorem pinchU_left_label (y : ULift.{1} (Fin 2)) :
    FPu.map (homOfLE (S01.K_le_J_castSucc 0)) (DPu.edgeLabel S01 0 y) =
      DPu.vertexLabel S01 0 (⟨0⟩ : ULift.{1} (Fin 2)) :=
  DPu.map_K_le_J_castSucc_edgeLabel S01 0 y

/-! ### Empty data: the zero cosheaf -/

/-- The cosheaf of empty data has empty values on every interval. -/
theorem emptyData_toCosheaf_isEmpty (n : ℕ) (S : CriticalValues n) (I : OpenInterval) :
    IsEmpty (((emptyData n).toCosheaf S).obj I) :=
  ⟨fun c => by
    obtain ⟨x, -⟩ := ZerothHomotopy.mk_surjective c
    exact (emptyData_isEmpty n S).false x.1⟩

/-- The empty finite map into any extracted data. -/
def emptyHom {n : ℕ} (S : CriticalValues n) {G : OpenInterval ⥤ Type}
    (hG : S.IsConstructibleAt G) : (emptyData n).Hom (S.extract G hG.finite) :=
  ⟨fun _ x => Empty.elim x, fun _ x => Empty.elim x, fun _ x => Empty.elim x,
    fun _ x => Empty.elim x⟩

/-- The zero cosheaf maps uniquely to every `Type`-valued constructible interval cosheaf at the
same levels. -/
theorem emptyData_natTrans_unique {n : ℕ} (S : CriticalValues n) {G : OpenInterval ⥤ Type}
    (hG : S.IsConstructibleAt G) (hGc : IsIntervalCosheaf.{0} G)
    (α β : (emptyData n).toCosheaf S ⟶ G) : α = β :=
  ((emptyData n).existsUnique_natTrans_labelled hG hGc (emptyHom S hG)).unique
    ⟨fun _ x => Empty.elim x, fun _ x => Empty.elim x⟩
    ⟨fun _ x => Empty.elim x, fun _ x => Empty.elim x⟩

/-- Reconstruction of the zero cosheaf at `S01`; its extracted data are empty. -/
abbrev zeroRecon := realizeExtractIso ((emptyData 1).toCosheaf_isConstructibleAt S01)
  ((emptyData 1).toCosheaf_isIntervalCosheaf S01)

/-- The vertex sets of the extracted data of the zero cosheaf are empty. -/
theorem zero_extract_isEmpty (i : Fin 2) :
    IsEmpty ((S01.extract ((emptyData 1).toCosheaf S01)
      ((emptyData 1).toCosheaf_isConstructibleAt S01).finite).V i) :=
  emptyData_toCosheaf_isEmpty 1 S01 _

/-- The edge set of the extracted data of the zero cosheaf is empty. -/
theorem zero_extract_edge_isEmpty (e : Fin 1) :
    IsEmpty ((S01.extract ((emptyData 1).toCosheaf S01)
      ((emptyData 1).toCosheaf_isConstructibleAt S01).finite).E e) :=
  emptyData_toCosheaf_isEmpty 1 S01 _

/-! ### `n = 0`: a singleton vertex, value on `ℝ` -/

/-- One vertex at the single level, no edges. -/
def pt0 : FiniteReebData.{0} 0 :=
  ⟨fun _ => Unit, fun e => e.elim0, fun _ => inferInstance, fun e => e.elim0, fun e => e.elim0,
    fun e => e.elim0⟩

/-- The cosheaf of the singleton data. -/
abbrev F0 : OpenInterval ⥤ Type := pt0.toCosheaf S0

/-- The value of the singleton cosheaf on `ℝ` has one element. -/
theorem F0_card_top : Nat.card (F0.obj ⊤) = 1 := by
  rw [← S0.J_eq_top_of_zero, ← Nat.card_congr (pt0.vertexLabel S0 0)]
  show Nat.card Unit = 1
  exact Nat.card_unique

/-- The reconstruction of the singleton cosheaf. -/
abbrev pt0Recon := realizeExtractIso (pt0.toCosheaf_isConstructibleAt S0)
  (pt0.toCosheaf_isIntervalCosheaf S0)

/-- The reconstruction on `ℝ = J 0`, through the actual inclusion `J 0 ≤ ⊤`. -/
theorem pt0_recon_top (x : F0.obj (S0.J 0)) :
    pt0Recon.hom.app ⊤
        (((S0.extract F0 (pt0.toCosheaf_isConstructibleAt S0).finite).toCosheaf S0).map
          (homOfLE le_top)
          ((S0.extract F0 (pt0.toCosheaf_isConstructibleAt S0).finite).vertexLabel S0 0 x)) =
      F0.map (homOfLE le_top) x := by
  rw [NatTrans.naturality_apply, realizeExtractIso_hom_app_J]

/-! ### Parallel edges and relabelling: labelled uniqueness versus automorphisms -/

/-- Exchange of the two parallel edges of `parallelData` (vertices fixed). -/
def swapPar : parallelData.Hom parallelData where
  v _ := id
  e _ := not
  left_comm _ _ := rfl
  right_comm _ _ := rfl

/-- The cosheaf of the parallel-edge data. -/
abbrev Cpar : OpenInterval ⥤ Type := parallelData.toCosheaf S01

/-- The parallel-edge cosheaf is constructible at `S01`. -/
theorem Cpar_isConstructibleAt : S01.IsConstructibleAt Cpar :=
  parallelData.toCosheaf_isConstructibleAt S01

/-- The parallel-edge cosheaf is an interval cosheaf. -/
theorem Cpar_isIntervalCosheaf : IsIntervalCosheaf.{0} Cpar :=
  parallelData.toCosheaf_isIntervalCosheaf S01

/-- The identity labelling lifts to the identity. -/
theorem par_lift_toExtractHom :
    parallelData.toCosheafLift Cpar_isConstructibleAt Cpar_isIntervalCosheaf
      (parallelData.toExtractHom S01) = 𝟙 Cpar :=
  (parallelData.toCosheafLift_unique _ _ _ (𝟙 _) (fun _ _ => rfl) (fun _ _ => rfl)).symm

/-- The swap labelling lifts to an isomorphism. -/
theorem par_swap_isIso :
    IsIso (parallelData.toCosheafLift Cpar_isConstructibleAt Cpar_isIntervalCosheaf
      (swapPar.comp (parallelData.toExtractHom S01))) :=
  parallelData.isIso_toCosheafLift _ _ _
    (fun i => (parallelData.vertexLabel S01 i).bijective.comp Function.bijective_id)
    (fun e => (parallelData.edgeLabel S01 e).bijective.comp Bool.involutive_not.bijective)

/-- The swap labelling gives a different automorphism, unique for its own labels: labelled
uniqueness does not erase unlabelled automorphisms. -/
theorem par_swap_ne_id :
    parallelData.toCosheafLift Cpar_isConstructibleAt Cpar_isIntervalCosheaf
      (swapPar.comp (parallelData.toExtractHom S01)) ≠ 𝟙 Cpar := by
  intro h
  have h1 := parallelData.toCosheafLift_app_K Cpar_isConstructibleAt Cpar_isIntervalCosheaf
    (swapPar.comp (parallelData.toExtractHom S01)) 0 (false : Bool)
  rw [h] at h1
  have h2 : parallelData.edgeLabel S01 0 (false : Bool) = parallelData.edgeLabel S01 0 true := h1
  exact Bool.false_ne_true ((parallelData.edgeLabel S01 0).injective h2)

/-! ### Insertion of a critical level: `S02 = {0, 2}` refined by `S012 = {0, 1, 2}` -/

/-- Levels `0 < 2`. -/
def S02 : CriticalValues 1 where
  value i := 2 * ((i : ℕ) : ℝ)
  strictMono a b h := by
    have : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := Nat.cast_lt.2 h
    linarith

/-- The levels of `S02` are among those of `S012`. -/
theorem S02_refines : Set.range S02.value ⊆ Set.range S012.value := by
  rintro _ ⟨i, rfl⟩
  refine ⟨⟨2 * (i : ℕ), by have := i.isLt; omega⟩, ?_⟩
  show (((2 * (i : ℕ) : ℕ)) : ℝ) = 2 * ((i : ℕ) : ℝ)
  push_cast
  ring

/-- The middle star of `S012` is the old gap of `S02`. -/
theorem insertion_middle_star : S012.J 1 = S02.K 0 := by
  ext x
  rw [bounded_J1_mem_iff, S02.mem_K]
  simp [S02]

/-- No level of `S02` lies in the middle star of `S012`. -/
theorem S02_value_notMem_J1 (i : Fin 2) : S02.value i ∉ S012.J 1 := by
  rw [bounded_J1_mem_iff]
  fin_cases i <;> norm_num [S02]

/-- For any `F` constructible at `S02`, the inserted right incidence `K 0 ≤ J 1` of the extracted
`S012`-data is bijective (constructibility at `S02`; no level of `S02` lies in `J 1`). -/
theorem insertion_right_bijective {F : OpenInterval ⥤ Type u} (hF : S02.IsConstructibleAt F) :
    Function.Bijective ((S012.extract F hF.finite).right 0) :=
  hF.bijective (S012.K_le_J_succ 0) (S012.K_nonempty 0) fun i =>
    iff_of_false (fun h => S02_value_notMem_J1 i (S012.K_le_J_succ 0 h)) (S02_value_notMem_J1 i)

/-- The inserted left incidence `K 1 ≤ J 1` is bijective. -/
theorem insertion_left_bijective {F : OpenInterval ⥤ Type u} (hF : S02.IsConstructibleAt F) :
    Function.Bijective ((S012.extract F hF.finite).left 1) :=
  hF.bijective (S012.K_le_J_castSucc 1) (S012.K_nonempty 1) fun i =>
    iff_of_false (fun h => S02_value_notMem_J1 i (S012.K_le_J_castSucc 1 h))
      (S02_value_notMem_J1 i)

/-- The first new gap `(0, 1)` of `S012` lies in the old gap `(0, 2)` of `S02`. -/
theorem insertion_K0_le_oldGap : S012.K 0 ≤ S02.K 0 :=
  (S012.K_le_J_succ 0).trans insertion_middle_star.le

/-- The second new gap `(1, 2)` of `S012` lies in the old gap `(0, 2)` of `S02`. -/
theorem insertion_K1_le_oldGap : S012.K 1 ≤ S02.K 0 :=
  (S012.K_le_J_castSucc 1).trans insertion_middle_star.le

/-- The inserted right incidence, transported along `S012.J 1 = S02.K 0`, is the covariant
inclusion of the first new gap into the old gap: `τ ∘ right₀ = c₀`. -/
theorem insertion_right_transport {F : OpenInterval ⥤ Type u} (hF : S02.IsConstructibleAt F)
    (x : F.obj (S012.K 0)) :
    F.map (eqToHom insertion_middle_star)
        ((S012.extract F (hF.of_refines S02_refines).finite).right 0 x) =
      F.map (homOfLE insertion_K0_le_oldGap) x := by
  show F.map (eqToHom insertion_middle_star) (F.map (homOfLE (S012.K_le_J_succ 0)) x) = _
  rw [← Functor.map_comp_apply]
  exact congrArg (fun f => F.map f x) (Subsingleton.elim _ _)

/-- The inserted left incidence, transported along `S012.J 1 = S02.K 0`, is the covariant
inclusion of the second new gap into the old gap: `τ ∘ left₁ = c₁`. -/
theorem insertion_left_transport {F : OpenInterval ⥤ Type u} (hF : S02.IsConstructibleAt F)
    (x : F.obj (S012.K 1)) :
    F.map (eqToHom insertion_middle_star)
        ((S012.extract F (hF.of_refines S02_refines).finite).left 1 x) =
      F.map (homOfLE insertion_K1_le_oldGap) x := by
  show F.map (eqToHom insertion_middle_star) (F.map (homOfLE (S012.K_le_J_castSucc 1)) x) = _
  rw [← Functor.map_comp_apply]
  exact congrArg (fun f => F.map f x) (Subsingleton.elim _ _)

/-- The two reconstructions of the same `F`, compared through `F`: `ε_S` followed by `ε_T⁻¹`. -/
def insertionComparison {F : OpenInterval ⥤ Type u} (hF : S02.IsConstructibleAt F)
    (hFc : IsIntervalCosheaf.{0} F) :
    (S02.extract F hF.finite).toCosheaf S02 ≅
      (S012.extract F (hF.of_refines S02_refines).finite).toCosheaf S012 :=
  realizeExtractIso hF hFc ≪≫ (realizeExtractIso (hF.of_refines S02_refines) hFc).symm

/-- The comparison followed by the `S012`-reconstruction is the `S02`-reconstruction. -/
theorem insertionComparison_hom_comp {F : OpenInterval ⥤ Type u} (hF : S02.IsConstructibleAt F)
    (hFc : IsIntervalCosheaf.{0} F) :
    (insertionComparison hF hFc).hom ≫ (realizeExtractIso (hF.of_refines S02_refines) hFc).hom =
      (realizeExtractIso hF hFc).hom := by
  simp [insertionComparison]

/-- The pinch realized at `S02` instantiates the insertion fixture. -/
theorem insertion_pinch :
    Function.Bijective ((S012.extract (DP.toCosheaf S02)
        (DP.toCosheaf_isConstructibleAt S02).finite).right 0) ∧
      Function.Bijective ((S012.extract (DP.toCosheaf S02)
        (DP.toCosheaf_isConstructibleAt S02).finite).left 1) :=
  ⟨insertion_right_bijective (DP.toCosheaf_isConstructibleAt S02),
    insertion_left_bijective (DP.toCosheaf_isConstructibleAt S02)⟩

end Examples.ConstructibleRepresentation

end

end TDA.Reeb
