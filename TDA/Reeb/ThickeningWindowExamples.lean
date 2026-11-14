import TDA.Reeb.ThickeningWindow
import TDA.Reeb.ConstructibleHomExamples

/-!
# Fixtures for windows and transfers

Acceptance fixtures for `TDA.Reeb.ThickeningWindow`, at the two levels `S01 = {0, 1}`.

* **A collapsing transfer.** For the single segment `seg` at `ε = 1/4`, the window at `0` contains
  the two distinct edge points at parameters `0` and `1/4` (`ξ0_ne_ξ1`). The transfer to `-1/4`, a
  slab end of the shifted levels where the edge slice is the point `{0}`, identifies them
  (`transfer_collapse`), so it is not injective (`transfer_not_injective`).
* **`ε = 0`.** The transfers between the heights `1/2` and `1/4` form a homeomorphism of windows
  (`zeroHomeomorph`) with no positivity hypothesis; it sends the edge point at `1/2` to the edge
  point at `1/4` (`windowToSpace_zeroHomeomorph`).
* **A non-Hausdorff piece.** For the presentation `sierpSeg` with every piece the Sierpiński space
  `Prop`, the window at `0` is compact and locally path-connected (`compactSpace_sierpWindow`,
  `locallyPathConnectedSpace_sierpWindow`) but not Hausdorff (`not_t2Space_sierpWindow`): the vertex
  piece embeds (`isEmbedding_sierpIncl`). The transfer between two heights of an open slab is still a
  homeomorphism (`sierpHomeomorph`).
* **Empty pieces.** A window far from the levels is empty (`isEmpty_window_far`), and so is every
  window of the presentation with empty pieces (`isEmpty_window_emptyData`).
-/

open Set Topology
open scoped NNReal

namespace TDA.Reeb.Examples.ThickeningWindow

noncomputable section

open TDA.Reeb CylinderPresentation Thickening TDA.Reeb.Examples.Cylinder
  TDA.Reeb.Examples.CylinderHom
open TDA.Reeb.RGraph (TransferOK)

/-- A single segment: one point at each level and one edge. -/
def seg : CylinderPresentation.{0} 1 where
  V _ := Unit
  E _ := Unit
  left _ := ContinuousMap.const _ ()
  right _ := ContinuousMap.const _ ()

/-- The half-width `1/4`. -/
def quarterNN : ℝ≥0 := ⟨1 / 4, by norm_num⟩

@[simp] theorem coe_quarterNN : (quarterNN : ℝ) = 1 / 4 := rfl

theorem S01_value_castSucc_zero : S01.value (Fin.castSucc 0) = 0 := by simp

theorem S01_value_succ_zero : S01.value (Fin.succ 0) = 1 := by simp

/-! ### A collapsing transfer -/

/-- The transfer hypotheses from `0` to the slab end `-1/4` at `ε = 1/4`. -/
theorem transferOK_collapse : TransferOK S01 quarterNN 0 (-1 / 4) where
  ne_sub i := by fin_cases i <;> norm_num [S01]
  ne_add i := by fin_cases i <;> norm_num [S01]
  lo_le i := by fin_cases i <;> norm_num [S01]
  le_hi i := by fin_cases i <;> norm_num [S01]

/-- The edge point at parameter `0`, glued to the vertex at level `0`. -/
def ξ0 : seg.Window S01 quarterNN 0 :=
  seg.windowMk S01 quarterNN 0 (.inr ⟨0, (), ⟨0, by
    simp only [slice, mem_Icc, max_le_iff, le_min_iff, coe_quarterNN, S01_value_castSucc_zero,
      S01_value_succ_zero]
    norm_num⟩⟩)

/-- The edge point at parameter `1/4`. -/
def ξ1 : seg.Window S01 quarterNN 0 :=
  seg.windowMk S01 quarterNN 0 (.inr ⟨0, (), ⟨1 / 4, by
    simp only [slice, mem_Icc, max_le_iff, le_min_iff, coe_quarterNN, S01_value_castSucc_zero,
      S01_value_succ_zero]
    norm_num⟩⟩)

/-- The two edge points of the window are distinct: they have different heights. -/
theorem ξ0_ne_ξ1 : ξ0 ≠ ξ1 := fun h => by
  have := congrArg (fun ξ => seg.height S01 (seg.windowToSpace S01 quarterNN 0 ξ)) h
  change (0 : ℝ) = 1 / 4 at this
  norm_num at this

/-- At the slab end `-1/4` the edge slice is a point, so the transfer identifies the two points. -/
theorem transfer_collapse :
    seg.transfer S01 quarterNN transferOK_collapse ξ0 =
      seg.transfer S01 quarterNN transferOK_collapse ξ1 := by
  have hu : max (S01.value (Fin.castSucc 0)) ((-1 / 4 : ℝ) - quarterNN) =
      min (S01.value (Fin.succ 0)) ((-1 / 4 : ℝ) + quarterNN) := by
    rw [S01_value_castSucc_zero, S01_value_succ_zero, coe_quarterNN]
    norm_num
  refine congrArg (seg.windowMk S01 quarterNN (-1 / 4))
    (congrArg Sum.inr (Sigma.ext rfl (heq_of_eq (Prod.ext rfl (Subtype.ext ?_)))))
  exact (RGraph.fragAff_collapse hu _ _).trans (RGraph.fragAff_collapse hu _ _).symm

/-- **A non-injective transfer.** -/
theorem transfer_not_injective :
    ¬ Function.Injective (seg.transfer S01 quarterNN transferOK_collapse) :=
  fun hi => ξ0_ne_ξ1 (hi transfer_collapse)

/-! ### `ε = 0` -/

theorem transferOK_zero : TransferOK S01 0 (1 / 2) (1 / 4) where
  ne_sub i := by fin_cases i <;> norm_num [S01]
  ne_add i := by fin_cases i <;> norm_num [S01]
  lo_le i := by fin_cases i <;> norm_num [S01]
  le_hi i := by fin_cases i <;> norm_num [S01]

theorem transferOK_zero' : TransferOK S01 0 (1 / 4) (1 / 2) where
  ne_sub i := by fin_cases i <;> norm_num [S01]
  ne_add i := by fin_cases i <;> norm_num [S01]
  lo_le i := by fin_cases i <;> norm_num [S01]
  le_hi i := by fin_cases i <;> norm_num [S01]

/-- At `ε = 0` the transfers between `1/2` and `1/4` are mutually inverse homeomorphisms. -/
def zeroHomeomorph : seg.Window S01 0 (1 / 2) ≃ₜ seg.Window S01 0 (1 / 4) :=
  seg.transferHomeomorph S01 0 transferOK_zero transferOK_zero'

/-- At `ε = 0` the edge point at height `1/2` goes to the edge point at height `1/4`. -/
theorem windowToSpace_zeroHomeomorph
    (σ : slice (S01.value (Fin.castSucc 0)) (S01.value (Fin.succ 0)) 0 (1 / 2)) :
    seg.windowToSpace S01 0 (1 / 4) (zeroHomeomorph (seg.windowMk S01 0 (1 / 2) (.inr ⟨0, (), σ⟩))) =
      seg.ofCylinder S01 0 ((), ⟨1 / 4, by
        show (1 / 4 : ℝ) ∈ Icc (S01.value (Fin.castSucc 0)) (S01.value (Fin.succ 0))
        rw [S01_value_castSucc_zero, S01_value_succ_zero]
        norm_num⟩) := by
  refine (seg.windowToSpace_transfer_inr S01 0 transferOK_zero 0 (() : seg.E 0) σ).trans ?_
  have hu : max (S01.value (Fin.castSucc 0)) ((1 / 4 : ℝ) - ((0 : ℝ≥0) : ℝ)) =
      min (S01.value (Fin.succ 0)) ((1 / 4 : ℝ) + ((0 : ℝ≥0) : ℝ)) := by
    rw [S01_value_castSucc_zero, S01_value_succ_zero, NNReal.coe_zero]
    norm_num
  refine congrArg (fun t => seg.ofCylinder S01 0 ((), t)) (Subtype.ext ?_)
  refine (RGraph.fragAff_collapse hu _ _).trans ?_
  show max (S01.value (Fin.castSucc 0)) ((1 / 4 : ℝ) - ((0 : ℝ≥0) : ℝ)) = 1 / 4
  rw [S01_value_castSucc_zero, NNReal.coe_zero]
  norm_num

/-! ### A non-Hausdorff piece -/

instance instCompactSpaceSierpV (i : Fin 2) : CompactSpace (sierpSeg.V i) :=
  inferInstanceAs (CompactSpace Prop)

instance instCompactSpaceSierpE (e : Fin 1) : CompactSpace (sierpSeg.E e) :=
  inferInstanceAs (CompactSpace Prop)

instance instLocallyPathConnectedSpaceSierpV (i : Fin 2) :
    LocallyPathConnectedSpace (sierpSeg.V i) :=
  inferInstanceAs (LocallyPathConnectedSpace Prop)

instance instLocallyPathConnectedSpaceSierpE (e : Fin 1) :
    LocallyPathConnectedSpace (sierpSeg.E e) :=
  inferInstanceAs (LocallyPathConnectedSpace Prop)

/-- The window of the Sierpiński presentation at `0` is compact. -/
theorem compactSpace_sierpWindow : CompactSpace (sierpSeg.Window S01 quarterNN 0) := inferInstance

/-- The window of the Sierpiński presentation at `0` is locally path-connected. -/
theorem locallyPathConnectedSpace_sierpWindow :
    LocallyPathConnectedSpace (sierpSeg.Window S01 quarterNN 0) := inferInstance

/-- The projection of the Sierpiński presentation onto its piece `Prop`. -/
def sierpProj : C(sierpSeg.Realization S01, Prop) :=
  lift
    { vertex := fun _ => ContinuousMap.id _
      cylinder := fun _ => ContinuousMap.fst
      segBot_eq := fun _ _ => rfl
      segTop_eq := fun _ _ => rfl }

/-- The vertex piece at level `0` in the window at `0`. -/
def sierpIncl : C(Prop, sierpSeg.Window S01 quarterNN 0) where
  toFun v := sierpSeg.windowMk S01 quarterNN 0 (.inl ⟨0, v, ⟨0, by
    simp only [slice, mem_Icc, max_le_iff, le_min_iff, coe_quarterNN, S01_value_zero]
    norm_num⟩⟩)
  continuous_toFun := (sierpSeg.continuous_windowMk S01 quarterNN 0).comp
    (continuous_inl.comp (continuous_sigmaMk.comp (continuous_id.prodMk continuous_const)))

/-- The vertex piece embeds in the window. -/
theorem isEmbedding_sierpIncl : IsEmbedding sierpIncl :=
  Function.LeftInverse.isEmbedding (f := fun ξ => sierpProj (sierpSeg.windowToSpace S01 quarterNN 0 ξ))
    (fun _ => rfl) (sierpProj.continuous.comp (sierpSeg.windowToSpace S01 quarterNN 0).continuous)
    sierpIncl.continuous

/-- **Not Hausdorff.** The window of the Sierpiński presentation contains `Prop`. -/
theorem not_t2Space_sierpWindow : ¬ T2Space (sierpSeg.Window S01 quarterNN 0) := fun _ =>
  TDA.Topology.Examples.not_t2Space_Prop isEmbedding_sierpIncl.t2Space

theorem transferOK_sierp : TransferOK S01 quarterNN (1 / 2) (3 / 8) where
  ne_sub i := by fin_cases i <;> norm_num [S01]
  ne_add i := by fin_cases i <;> norm_num [S01]
  lo_le i := by fin_cases i <;> norm_num [S01]
  le_hi i := by fin_cases i <;> norm_num [S01]

theorem transferOK_sierp' : TransferOK S01 quarterNN (3 / 8) (1 / 2) where
  ne_sub i := by fin_cases i <;> norm_num [S01]
  ne_add i := by fin_cases i <;> norm_num [S01]
  lo_le i := by fin_cases i <;> norm_num [S01]
  le_hi i := by fin_cases i <;> norm_num [S01]

/-- Within the open slab `(1/4, 3/4)` the transfer of non-Hausdorff windows is a homeomorphism. -/
def sierpHomeomorph : sierpSeg.Window S01 quarterNN (1 / 2) ≃ₜ sierpSeg.Window S01 quarterNN (3 / 8) :=
  sierpSeg.transferHomeomorph S01 quarterNN transferOK_sierp transferOK_sierp'

/-! ### Empty pieces -/

private theorem S01_value_le_one (i : Fin 2) : S01.value i ≤ 1 := by
  simp only [S01]
  exact_mod_cast Nat.le_of_lt_succ i.2

/-- The window of the segment at height `5` is empty: every slice is. -/
theorem isEmpty_window_far : IsEmpty (seg.Window S01 quarterNN 5) :=
  ⟨fun ξ => by
    obtain ⟨r, -⟩ := seg.windowMk_surjective S01 quarterNN 5 ξ
    rcases r with ⟨i, _, σ⟩ | ⟨e, _, σ⟩
    · have h := (mem_Icc_of_mem_slice σ.2).2
      have := S01_value_le_one i
      rw [coe_quarterNN] at h
      linarith
    · have h := (mem_Icc_of_mem_slice σ.2).2
      have := S01_value_le_one e.succ
      rw [coe_quarterNN] at h
      linarith⟩

/-- Every window of the presentation with empty pieces is empty. -/
theorem isEmpty_window_emptyData (ε : ℝ≥0) (c : ℝ) :
    IsEmpty ((ofFiniteData (emptyData 1)).Window S01 ε c) :=
  inferInstance

end

end TDA.Reeb.Examples.ThickeningWindow
