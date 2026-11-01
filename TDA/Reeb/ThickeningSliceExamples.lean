import TDA.Reeb.ThickeningSlice

/-!
# Fixtures for scalar slices and polygons

Acceptance fixtures for `TDA.Reeb.ThickeningSlice`:

* **`ε = 0`.** Every slice is the point `{u}` for `u ∈ [a, d]` and empty otherwise; the transfer to a
  height `u ∈ [a, d]` is the constant `u`; the parallelogram is the diagonal over `[a, d]`.
* **A vertex strip (`a = d`).** The slice of `[1, 1]` at `ε = 1/2` is `{1}` at height `5/4` and
  empty at height `2`; every transfer of a vertex strip fixes `a`; the parallelogram of `[a, a]` is
  `{a} × [a - ε, a + ε]`.
* **Coincident events.** For `[0, 1]` at `ε = 1/2`, the events `1 - ε = 0 + ε` coincide, so the
  shifted witness of `pair 0 1` has the three levels `-1/2`, `1/2`, `3/2` and two slabs. The slice
  at the coincident level is the whole segment, and the polygons and level slices cover the
  parallelogram.
* **A corner-only slab.** On the grid `-3/2 < -1/2 < 1/2 < 3/2`, which lists the events of
  `[0, 1]` at `ε = 1/2`, the first slab `[-3/2, -1/2]` meets `[a - ε, d + ε] = [-1/2, 3/2]` only in its
  corner. Its polygon and its midpoint slice are empty, and the corner fibre `{(0, -1/2)}` is the
  level slice at `-1/2`; the corner also lies in the next polygon, as its collapsing end.
-/

open Set
open scoped NNReal

namespace TDA.Reeb

noncomputable section

namespace Examples.ThickeningSlice

open CylinderPresentation Thickening CriticalValues
open RGraph (fragAff)

/-! ### `ε = 0` -/

/-- At `ε = 0` the slice at a height of the segment is that height. -/
theorem slice_zero_eq_singleton {a d u : ℝ} (hu : u ∈ Icc a d) : slice a d 0 u = {u} := by
  rw [slice_zero, max_eq_right hu.1, min_eq_right hu.2, Icc_self]

/-- At `ε = 0` the slice at a height outside the segment is empty. -/
theorem slice_zero_eq_empty {a d u : ℝ} (hu : u ∉ Icc a d) : slice a d 0 u = ∅ := by
  rw [slice_zero]
  exact Icc_eq_empty fun h => hu ⟨le_max_left _ _ |>.trans (h.trans (min_le_right _ _)),
    (le_max_right _ _).trans (h.trans (min_le_left _ _))⟩

/-- At `ε = 0` the transfer to a height `u` of the segment is the constant `u`. -/
theorem fragAff_zero {a d u : ℝ} (hu : u ∈ Icc a d) (c s : ℝ) :
    fragAff a d (0 : ℝ≥0) c u s = u := by
  have h := RGraph.fragAff_collapse (a := a) (d := d) (ε := ((0 : ℝ≥0) : ℝ)) (u := u)
    (by simp [max_eq_right hu.1, min_eq_right hu.2]) c s
  simpa [max_eq_right hu.1] using h

/-- At `ε = 0` the parallelogram is the diagonal over the segment. -/
theorem parallelogram_zero (a d : ℝ) :
    parallelogram a d 0 = {p | p.1 = p.2 ∧ p.2 ∈ Icc a d} := by
  ext ⟨s, u⟩
  simp only [parallelogram, slice_zero, mem_ofPred_eq, mem_Icc, max_le_iff, le_min_iff]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    exact ⟨le_antisymm h4 h2, by linarith, by linarith⟩
  · rintro ⟨rfl, h1, h2⟩
    exact ⟨⟨h1, le_rfl⟩, h2, le_rfl⟩

/-! ### A vertex strip -/

/-- The half-width `1/2`. -/
def halfNN : ℝ≥0 := ⟨1 / 2, by norm_num⟩

@[simp] theorem coe_halfNN : (halfNN : ℝ) = 1 / 2 := rfl

/-- The slice of the vertex strip `[1, 1]` at height `5/4` is `{1}`. -/
theorem slice_strip : slice 1 1 halfNN (5 / 4) = {1} :=
  slice_self_eq (by norm_num)

/-- The slice of the vertex strip `[1, 1]` at height `2` is empty. -/
theorem slice_strip_far : slice 1 1 halfNN 2 = ∅ :=
  slice_self_eq_empty (by norm_num)

/-- Every transfer of a vertex strip fixes the vertex. -/
theorem fragAff_strip {a c u s : ℝ} {ε : ℝ≥0} (h : SliceTransfer a a ε c u)
    (hs : s ∈ slice a a ε c) : fragAff a a ε c u s = a :=
  h.fragAff_eq_left hs (le_antisymm ((slice_subset_Icc a a ε c hs).2)
    (slice_subset_Icc a a ε c hs).1)

/-- The parallelogram of the vertex strip `[a, a]` is `{a} × [a - ε, a + ε]`. -/
theorem parallelogram_self (a : ℝ) (ε : ℝ≥0) :
    parallelogram a a ε = {a} ×ˢ Icc (a - ε) (a + ε) := by
  ext ⟨s, u⟩
  simp only [parallelogram, mem_ofPred_eq, mem_prod, mem_singleton_iff, mem_Icc, max_le_iff,
    le_min_iff]
  constructor
  · rintro ⟨⟨h1, h3⟩, h2, h4⟩
    obtain rfl := le_antisymm h2 h1
    exact ⟨rfl, by linarith, by linarith⟩
  · rintro ⟨rfl, h1, h2⟩
    exact ⟨⟨le_rfl, by linarith⟩, le_rfl, by linarith⟩

/-! ### Coincident events -/

/-- The events `1 - ε` and `0 + ε` of `[0, 1]` coincide at `ε = 1/2`. -/
theorem coincident_events : (1 : ℝ) - halfNN = 0 + halfNN := by norm_num

/-- The single segment `[0, 1]`. -/
abbrev P01 : CriticalValues 1 := pair 0 1 one_pos

/-- The four events `{-1/2, 1/2} ∪ {1/2, 3/2}` merge to three levels. -/
theorem range_shifted_P01 :
    Set.range (P01.shifted halfNN).value = {-1 / 2, 1 / 2, 3 / 2} := by
  rw [range_shifted_pair]
  ext x
  simp only [mem_insert_iff, mem_singleton_iff, coe_halfNN]
  constructor
  · rintro (h | h | h | h) <;> rw [h] <;> norm_num
  · rintro (h | h | h) <;> rw [h] <;> norm_num

/-- The shifted witness of `pair 0 1` at `ε = 1/2` has two slabs, not three. -/
theorem shiftedCount_P01 : P01.shiftedCount halfNN = 2 := by
  have h : P01.shiftedSet halfNN = {-1 / 2, 1 / 2, 3 / 2} := by
    rw [← Finset.coe_inj, ← range_shifted, range_shifted_P01]
    simp
  unfold shiftedCount
  rw [h, Finset.card_insert_of_notMem (by norm_num), Finset.card_insert_of_notMem (by norm_num),
    Finset.card_singleton]

/-- The slice at the coincident level `1/2` is the whole segment. -/
theorem slice_coincident : slice 0 1 halfNN (1 / 2) = Icc 0 1 := by
  simp only [slice, coe_halfNN]
  norm_num

/-- The slab polygons and the level slices cover the parallelogram of `[0, 1]` at `ε = 1/2`. -/
theorem cover_coincident :
    (⋃ k, polygon 0 1 halfNN (P01.shifted halfNN) k) ∪
        ⋃ j, levelSet 0 1 halfNN (P01.shifted halfNN) j =
      parallelogram 0 1 halfNN :=
  iUnion_polygon_union_levelSet (pair_hasEvents one_pos halfNN)

/-! ### A corner-only slab -/

/-- The grid `-3/2 < -1/2 < 1/2 < 3/2`. -/
def G4 : CriticalValues 3 where
  value i := ((i : ℕ) : ℝ) - 3 / 2
  strictMono _ _ h := sub_lt_sub_right (Nat.cast_lt.2 h) _

@[simp] theorem G4_value_zero : G4.value 0 = -3 / 2 := by norm_num [G4]
@[simp] theorem G4_value_one : G4.value 1 = -1 / 2 := by norm_num [G4]
@[simp] theorem G4_value_two : G4.value 2 = 1 / 2 := by norm_num [G4]
@[simp] theorem G4_value_three : G4.value 3 = 3 / 2 := by norm_num [G4]

/-- The grid lists the events `-1/2`, `1/2`, `3/2` of `[0, 1]` at `ε = 1/2`. -/
theorem hasEvents_G4 : G4.HasEvents 0 1 halfNN :=
  ⟨⟨1, by norm_num⟩, ⟨2, by norm_num⟩, ⟨2, by norm_num⟩, ⟨3, by norm_num⟩⟩

theorem seg_G4_zero : Seg G4 0 = Icc (-3 / 2) (-1 / 2) := by
  simp [Seg, Fin.castSucc_zero, Fin.succ_zero_eq_one]

theorem seg_G4_one : Seg G4 1 = Icc (-1 / 2) (1 / 2) := by
  simp only [Seg]
  rw [show (1 : Fin 3).castSucc = 1 from rfl, show (1 : Fin 3).succ = 2 from rfl, G4_value_one,
    G4_value_two]

/-- The first slab meets `[a - ε, d + ε]` in its corner only. -/
theorem seg_G4_zero_inter : Seg G4 0 ∩ Icc (0 - halfNN) (1 + halfNN) = {-1 / 2} := by
  rw [seg_G4_zero, coe_halfNN, Icc_inter_Icc]
  norm_num

/-- **Corner-only slab.** Its polygon is empty. -/
theorem polygon_G4_zero : polygon 0 1 halfNN G4 0 = ∅ := by
  refine eq_empty_of_forall_notMem fun p hp => ?_
  have h := hp.2.2 (show (-3 / 2 : ℝ) ∈ Seg G4 0 by rw [seg_G4_zero]; norm_num)
  rw [coe_halfNN] at h
  norm_num at h

/-- **Corner-only slab.** Its midpoint slice is empty. -/
theorem slice_mid_G4_zero : slice 0 1 halfNN (G4.mid 0) = ∅ := by
  have hm : G4.mid 0 = -1 := by
    simp only [CriticalValues.mid, Fin.castSucc_zero, Fin.succ_zero_eq_one, G4_value_zero,
      G4_value_one]
    norm_num
  rw [hm]
  exact Icc_eq_empty (by norm_num)

/-- **Corner-only slab.** The corner fibre is the level slice at `-1/2`. -/
theorem levelSet_G4_one : levelSet 0 1 halfNN G4 1 = {((0 : ℝ), (-1 / 2 : ℝ))} := by
  ext ⟨s, u⟩
  simp only [levelSet, mem_ofPred_eq, mem_singleton_iff, Prod.mk.injEq, G4_value_one]
  constructor
  · rintro ⟨hs, rfl⟩
    rw [mem_Icc, coe_halfNN] at hs
    norm_num at hs
    exact ⟨le_antisymm hs.2 hs.1, rfl⟩
  · rintro ⟨rfl, rfl⟩
    refine ⟨?_, rfl⟩
    rw [mem_Icc, coe_halfNN]
    norm_num

/-- The corner also lies in the polygon of the next slab, at its collapsing lower end. -/
theorem corner_mem_polygon_G4_one : ((0 : ℝ), (-1 / 2 : ℝ)) ∈ polygon 0 1 halfNN G4 1 := by
  refine ⟨?_, ?_, ?_⟩
  · show (0 : ℝ) ∈ Icc _ _
    rw [mem_Icc, coe_halfNN]
    norm_num
  · rw [seg_G4_one]
    norm_num
  · rw [seg_G4_one, coe_halfNN]
    exact Icc_subset_Icc (by norm_num) (by norm_num)

end Examples.ThickeningSlice

end

end TDA.Reeb
