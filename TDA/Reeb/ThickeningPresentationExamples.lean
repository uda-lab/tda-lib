import TDA.Reeb.ThickeningPresentation
import TDA.Reeb.ThickeningWindowExamples
import TDA.Reeb.ThickeningSliceExamples

/-!
# Fixtures for the thickening presentation

Acceptance fixtures for `TDA.Reeb.ThickeningPresentation`; in each the homeomorphism
`thickHomeomorph` is applied.

* **No edges.** For one point at one level (`n = 0`), the inverse homeomorphism sends `(x, t)` to a
  point of height `t` (`height_ptThick_symm`).
* **Empty pieces.** For the presentation with all pieces empty, the thickening presentation and
  its realization are empty (`isEmpty_emptyThick_realization`). On a grid with the extra level `5`
  far from the segment, the vertex piece at `5` is empty (`isEmpty_farThick_V`), and the
  homeomorphism still holds (`farThickHomeomorph`).
* **Duplicate shifted values.** For the segment over `pair 0 1` at `ε = 1/2`, the shifted values
  `0 + ε = 1 - ε` merge (`shiftedCount_P01`), and the bottom vertex at band coordinate `1/2` comes
  from the merged level `1/2` (`height_dupThick_symm`).
* **`ε = 0`.** On the grid `S01` itself, every cylinder point of `P_0` at height `u` goes to the
  point of parameter `u` of the segment (`fst_zeroThickHomeomorph_ofCylinder`).
* **A non-Hausdorff input.** For the Sierpiński presentation `sierpSeg`, the pieces of `P_ε` are
  compact and locally path-connected, the realization of `P_ε` is not Hausdorff
  (`not_t2Space_sierpThick`), and the homeomorphism holds (`sierpThickHomeomorph`).
-/

open Set Topology
open scoped NNReal

namespace TDA.Reeb.Examples.ThickeningPresentation

noncomputable section

open TDA.Reeb CylinderPresentation Thickening TDA.Reeb.Examples.Cylinder
  TDA.Reeb.Examples.CylinderHom TDA.Reeb.Examples.ThickeningWindow
  TDA.Reeb.Examples.ThickeningSlice

/-! ### No edges -/

/-- One level `0`. -/
def L0 : CriticalValues 0 where
  value _ := 0
  strictMono a b h :=
    absurd h (by rw [Fin.fin_one_eq_zero a, Fin.fin_one_eq_zero b]; exact lt_irrefl _)

/-- One point at one level, no edges. -/
def pt : CylinderPresentation.{0} 0 where
  V _ := Unit
  E e := e.elim0
  topV _ := inferInstance
  topE e := e.elim0
  left e := e.elim0
  right e := e.elim0

/-- **No edges.** The homeomorphism for one point at one level. -/
def ptThickHomeomorph (ε : ℝ≥0) :
    (pt.shiftedThick L0 ε).Realization (L0.shifted ε) ≃ₜ
      pt.Realization L0 × GeometricThickening.Band ε :=
  pt.shiftedThickHomeomorph L0 ε

/-- **No edges.** The inverse sends the point at band coordinate `t` to height `t`. -/
theorem height_ptThick_symm (ε : ℝ≥0) (t : GeometricThickening.Band ε) :
    (pt.shiftedThick L0 ε).height (L0.shifted ε)
      ((ptThickHomeomorph ε).symm (pt.ofVertex L0 0 (), t)) = t := by
  rw [show ptThickHomeomorph ε =
      pt.thickHomeomorph L0 ε _ (L0.containsShifted_shifted ε) from rfl,
    height_thickHomeomorph_symm,
    GeometricThickening.height_apply]
  show (0 : ℝ) + t = t
  ring

/-! ### Empty pieces -/

instance instIsEmptyEmptyDataV (i : Fin 2) : IsEmpty ((ofFiniteData (emptyData 1)).V i) :=
  inferInstanceAs (IsEmpty Empty)

/-- The pieces of the thickening presentation of the empty presentation are empty. -/
theorem isEmpty_emptyThick_V (ε : ℝ≥0) (j : Fin (S01.shiftedCount ε + 1)) :
    IsEmpty (((ofFiniteData (emptyData 1)).shiftedThick S01 ε).V j) :=
  inferInstanceAs (IsEmpty ((ofFiniteData (emptyData 1)).Window S01 ε _))

/-- **Empty input.** The realization of the thickening presentation of the empty presentation is
empty, through the homeomorphism. -/
theorem isEmpty_emptyThick_realization (ε : ℝ≥0) :
    IsEmpty (((ofFiniteData (emptyData 1)).shiftedThick S01 ε).Realization (S01.shifted ε)) := by
  have : IsEmpty ((ofFiniteData (emptyData 1)).Realization S01) := ⟨fun q => by
    obtain ⟨r, -⟩ := (ofFiniteData (emptyData 1)).quotMk_surjective S01 q
    rcases r with ⟨_, v⟩ | ⟨_, y, _⟩
    exacts [isEmptyElim v, isEmptyElim y]⟩
  exact ((ofFiniteData (emptyData 1)).shiftedThickHomeomorph S01 ε).toEquiv.isEmpty

/-- A grid listing the shifted levels of `S01` at `ε = 1/4`, with the extra level `5`. -/
def G5 : CriticalValues 4 where
  value := ![-1 / 4, 1 / 4, 3 / 4, 5 / 4, 5]
  strictMono := Fin.strictMono_iff_lt_succ.2 fun i => by
    fin_cases i <;> norm_num [Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four]

theorem containsShifted_G5 : S01.ContainsShifted quarterNN G5 := fun i => by
  fin_cases i
  · exact ⟨⟨0, by norm_num [G5, S01]⟩, ⟨1, by norm_num [G5, S01]⟩⟩
  · exact ⟨⟨2, by norm_num [G5, S01, Matrix.cons_val_two]⟩,
      ⟨3, by norm_num [G5, S01, Matrix.cons_val_three]⟩⟩

/-- **Extra level.** The vertex piece at the level `5`, far from the segment, is empty. -/
theorem isEmpty_farThick_V : IsEmpty ((seg.thick S01 quarterNN G5 containsShifted_G5).V 4) := by
  have h : G5.value 4 = 5 := by norm_num [G5, Matrix.cons_val_four]
  show IsEmpty (seg.Window S01 quarterNN (G5.value 4))
  rw [h]
  exact isEmpty_window_far

/-- **Extra level.** The homeomorphism on a grid with an extra level. -/
def farThickHomeomorph :
    (seg.thick S01 quarterNN G5 containsShifted_G5).Realization G5 ≃ₜ
      seg.Realization S01 × GeometricThickening.Band quarterNN :=
  seg.thickHomeomorph S01 quarterNN G5 containsShifted_G5

/-! ### Duplicate shifted values -/

/-- **Duplicate shifted values.** The homeomorphism for the segment over `pair 0 1` at `ε = 1/2`,
where the shifted values `0 + ε` and `1 - ε` coincide. -/
def dupThickHomeomorph :
    (seg.shiftedThick P01 halfNN).Realization (P01.shifted halfNN) ≃ₜ
      seg.Realization P01 × GeometricThickening.Band halfNN :=
  seg.shiftedThickHomeomorph P01 halfNN

/-- **Duplicate shifted values.** The shifts `0 + ε` and `1 - ε` coincide, so the shifted grid has
two slabs rather than three, and the bottom vertex at band coordinate `1/2` comes from height
`1/2`, the merged level of the shifted grid. -/
theorem height_dupThick_symm :
    P01.shiftedCount halfNN = 2 ∧
      (seg.shiftedThick P01 halfNN).height (P01.shifted halfNN)
        (dupThickHomeomorph.symm (seg.ofVertex P01 0 (), ⟨1 / 2, by norm_num⟩)) = 1 / 2 ∧
      (1 / 2 : ℝ) ∈ Set.range (P01.shifted halfNN).value := by
  refine ⟨shiftedCount_P01, ?_, by rw [range_shifted_P01]; simp⟩
  rw [show dupThickHomeomorph =
      seg.thickHomeomorph P01 halfNN _ (P01.containsShifted_shifted halfNN) from rfl,
    height_thickHomeomorph_symm, GeometricThickening.height_apply]
  show (0 : ℝ) + 1 / 2 = 1 / 2
  ring

/-! ### `ε = 0` -/

theorem containsShifted_zero : S01.ContainsShifted 0 S01 := fun i =>
  ⟨⟨i, by simp⟩, ⟨i, by simp⟩⟩

/-- **`ε = 0`.** The homeomorphism on the grid `S01`. -/
def zeroThickHomeomorph :
    (seg.thick S01 0 S01 containsShifted_zero).Realization S01 ≃ₜ
      seg.Realization S01 × GeometricThickening.Band 0 :=
  seg.thickHomeomorph S01 0 S01 containsShifted_zero

/-- **`ε = 0`.** A cylinder point of `P_0` at height `u` goes to the point of parameter `u`. -/
theorem fst_zeroThickHomeomorph_ofCylinder
    (σ : slice (S01.value (Fin.castSucc 0)) (S01.value (Fin.succ 0)) 0 (S01.mid 0))
    (u : Seg S01 0) :
    (zeroThickHomeomorph ((seg.thick S01 0 S01 containsShifted_zero).ofCylinder S01 0
        (seg.windowMk S01 0 _ (.inr ⟨0, (), σ⟩), u))).1 = seg.ofCylinder S01 0 ((), u) := by
  refine (seg.windowToSpace_transfer_inr S01 0 _ 0 () σ).trans ?_
  refine congrArg (fun s => seg.ofCylinder S01 0 ((), s)) (Subtype.ext ?_)
  have hu := u.2
  have h0 : max (S01.value (Fin.castSucc 0)) ((u : ℝ) - ((0 : ℝ≥0) : ℝ)) =
      min (S01.value (Fin.succ 0)) ((u : ℝ) + ((0 : ℝ≥0) : ℝ)) := by
    rw [NNReal.coe_zero, sub_zero, add_zero, max_eq_right hu.1, min_eq_right hu.2]
  show RGraph.fragAff (S01.value (Fin.castSucc 0)) (S01.value (Fin.succ 0)) ((0 : ℝ≥0) : ℝ)
    (S01.mid 0) u σ = u
  rw [RGraph.fragAff_collapse h0, NNReal.coe_zero, sub_zero, max_eq_right hu.1]

/-! ### A non-Hausdorff input -/

/-- The pieces of the thickening presentation of the Sierpiński presentation are compact. -/
theorem compactSpace_sierpThick_V (j : Fin (S01.shiftedCount quarterNN + 1)) :
    CompactSpace ((sierpSeg.shiftedThick S01 quarterNN).V j) := inferInstance

/-- The pieces of the thickening presentation of the Sierpiński presentation are locally
path-connected. -/
theorem locallyPathConnectedSpace_sierpThick_E (k : Fin (S01.shiftedCount quarterNN)) :
    LocallyPathConnectedSpace ((sierpSeg.shiftedThick S01 quarterNN).E k) := inferInstance

/-- **A non-Hausdorff input.** The homeomorphism for the Sierpiński presentation. -/
def sierpThickHomeomorph :
    (sierpSeg.shiftedThick S01 quarterNN).Realization (S01.shifted quarterNN) ≃ₜ
      sierpSeg.Realization S01 × GeometricThickening.Band quarterNN :=
  sierpSeg.shiftedThickHomeomorph S01 quarterNN

/-- **Not Hausdorff.** The realization of the thickening presentation of the Sierpiński
presentation is not Hausdorff: through the homeomorphism it contains the realization of
`sierpSeg`. -/
theorem not_t2Space_sierpThick :
    ¬ T2Space ((sierpSeg.shiftedThick S01 quarterNN).Realization (S01.shifted quarterNN)) :=
  fun _ =>
    haveI : T2Space (sierpSeg.Realization S01 × GeometricThickening.Band quarterNN) :=
      sierpThickHomeomorph.symm.isEmbedding.t2Space
    not_t2Space_sierpSeg
      (isEmbedding_prodMkLeft
        (⟨0, GeometricThickening.zero_mem_band _⟩ : GeometricThickening.Band quarterNN)).t2Space

end

end TDA.Reeb.Examples.ThickeningPresentation
