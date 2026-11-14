import TDA.Reeb.RGraphThickening
import TDA.Topology.QuotientProduct

/-!
# Scalar slices and polygons of a thickened segment

The scalar part of the thickening of a cylinder `E × [a, d]` (de Silva–Munch–Patel, *Categorified
Reeb Graphs*, proof of Theorem 4.27), for `a ≤ d` and `ε ≥ 0`, with no hypothesis on `E`. Under
`(s, t) ↦ (s, u = s + t)` the thickening `[a, d] × [-ε, ε]` of the segment, with height `s + t`,
becomes the parallelogram `{(s, u) | s ∈ [a, d], |s - u| ≤ ε}` with height `u`.

## Slices

`slice a d ε u = [max a (u - ε), min d (u + ε)]` is DMP's slice `J(u)` of the segment at height
`u`, with ends `sliceLo a ε u` and `sliceHi d ε u`. It may be empty or a point. It is nonempty
exactly for `u ∈ [a - ε, d + ε]` (`slice_nonempty_iff`). When `a` lies in the slice it is the
lower end, and when `d` lies in it, it is the upper end (`sliceLo_eq_left`, `sliceHi_eq_right`).
For the degenerate segment `[a, a]` of a vertex strip, the slice is `{a}` or empty
(`slice_self_eq`, `slice_self_eq_empty`). At `ε = 0` it is `[max a u, min d u]` (`slice_zero`).
Slices are compact, and locally path-connected (`locallyPathConnectedSpace_slice`, used as a
local instance).

## Transfer between slices

`SliceTransfer a d ε c u` records that `c` avoids the four events `a ± ε`, `d ± ε` and that the
two branches of each slice end persist from `c` to `u`. It is the restriction of
`RGraph.TransferOK` to one segment (`TransferOK.sliceTransfer_edge`,
`TransferOK.sliceTransfer_vertex`). Under it the affine fragment map `RGraph.fragAff` sends the
slice at `c` into the slice at `u` (`SliceTransfer.fragAff_mem`) and fixes the segment ends
(`SliceTransfer.fragAff_eq_left`, `SliceTransfer.fragAff_eq_right`), so the normalized slice ends
`0` and `1` are preserved; this is the boundary compatibility of the thickening. With transfer
hypotheses in both directions, both slices are nondegenerate or both are degenerate
(`SliceTransfer.lt_iff`), and the two transfers are mutually inverse on the slice
(`SliceTransfer.fragAff_fragAff`, `SliceTransfer.fragAff_injOn`). These statements need neither
`ε > 0` nor `a < d`: for a point slice the denominator of `fragAff` is `0`, Lean's division
returns `0`, and `fragAff` is the constant lower end.

## Grids

`G.HasEvents a d ε` says that the levels of a grid `G` include the four events, and
`S.ContainsShifted ε G` that they include every shifted level `S.value i ± ε`, as those of the
shifted witness `S.shifted ε` do (`containsShifted_shifted`). Such a grid lists the events of every
segment and every vertex strip of `S` (`ContainsShifted.hasEvents_edge`,
`ContainsShifted.hasEvents_vertex`). From a height in an open slab to any height of the closed slab,
the transfer hypotheses hold (`ContainsShifted.transferOK_of_mem`,
`HasEvents.sliceTransfer_of_mem`). `G.mid k` is the midpoint of slab `k`; on the shifted witness it
is the graph-case `RGraph.mid` (`RGraph.mid_eq_shifted_mid`). A closed slab lies inside
`[a - ε, d + ε]` as soon as its midpoint does (`HasEvents.seg_subset_of_mid_mem`), exactly when the
midpoint slice is nonempty (`HasEvents.slice_mid_nonempty_iff`), and every height of
`[a - ε, d + ε]` is a level or lies in such a slab (`HasEvents.eq_value_or_mem_K`). For a single
segment `a < d`, the shifted witness of the two-level grid `pair a d had` has as levels exactly the
distinct values among `a ± ε`, `d ± ε` (`range_shifted_pair`, `pair_hasEvents`).

## Polygons

The parallelogram is covered by the closed slab polygons `polygon a d ε G k`, present only when the
closed slab lies inside `[a - ε, d + ε]`, and the closed level slices `levelSet a d ε G j`
(`iUnion_polygon_union_levelSet`). A slab that meets `[a - ε, d + ε]` in a corner only has an empty
polygon; its corner fibre lies in a level slice. The scalar polygon map
`polygonMap : J(mid k) × [b k, b (k+1)] → polygon k`, `(σ, u) ↦ (fragAff (mid k) u σ, u)`, is a
continuous surjection (`polygonMap_surjective`) from a compact space to a Hausdorff space, hence
proper (`isProperMap_polygonMap`), and stays a quotient map after product with an arbitrary
space (`isQuotientMap_prodMap_polygonMap`). Two parameters have the same image exactly when they
have the same height and the same transferred parameter (`polygonMap_eq_iff`). At a slab end with
a point slice the map collapses the whole reference slice.

See `docs/math/reeb-thickening-constructible.md`.
-/

open Set Topology
open scoped NNReal

namespace TDA.Reeb

noncomputable section

open CylinderPresentation
open RGraph (fragAff)

namespace Thickening

/-! ### Slices -/

section Slice

variable (a d : ℝ) (ε : ℝ≥0)

/-- DMP's slice `J(u) = [max a (u - ε), min d (u + ε)]` of the segment `[a, d]` at height `u`;
possibly empty or a point. -/
abbrev slice (u : ℝ) : Set ℝ := Icc (max a (u - ε)) (min d (u + ε))

/-- The lower end `max a (u - ε)` of the slice at `u`. -/
abbrev sliceLo (u : ℝ) : ℝ := max a (u - ε)

/-- The upper end `min d (u + ε)` of the slice at `u`. -/
abbrev sliceHi (u : ℝ) : ℝ := min d (u + ε)

theorem slice_subset_Icc (u : ℝ) : slice a d ε u ⊆ Icc a d :=
  Icc_subset_Icc (le_max_left _ _) (min_le_left _ _)

theorem slice_subset_window (u : ℝ) : slice a d ε u ⊆ Icc (u - ε) (u + ε) :=
  Icc_subset_Icc (le_max_right _ _) (min_le_right _ _)

variable {a d ε}

theorem mem_slice_iff {s u : ℝ} : s ∈ slice a d ε u ↔ s ∈ Icc a d ∧ u - ε ≤ s ∧ s ≤ u + ε := by
  simp only [slice, mem_Icc, max_le_iff, le_min_iff]
  tauto

/-- A height with a nonempty slice lies in `[a - ε, d + ε]`. -/
theorem mem_Icc_of_mem_slice {s u : ℝ} (hs : s ∈ slice a d ε u) : u ∈ Icc (a - ε) (d + ε) := by
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := mem_slice_iff.1 hs
  exact ⟨by linarith, by linarith⟩

theorem slice_nonempty_iff (had : a ≤ d) {u : ℝ} :
    (slice a d ε u).Nonempty ↔ u ∈ Icc (a - ε) (d + ε) := by
  have hε := ε.coe_nonneg
  simp only [slice, nonempty_Icc, max_le_iff, le_min_iff, mem_Icc]
  constructor
  · rintro ⟨⟨-, h2⟩, h3, -⟩
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨had, by linarith⟩, by linarith, by linarith⟩

/-- **Boundary compatibility.** When `a` lies in the slice, it is the lower end. -/
theorem sliceLo_eq_left {u : ℝ} (h : a ∈ slice a d ε u) : sliceLo a ε u = a :=
  max_eq_left ((le_max_right _ _).trans h.1)

/-- **Boundary compatibility.** When `d` lies in the slice, it is the upper end. -/
theorem sliceHi_eq_right {u : ℝ} (h : d ∈ slice a d ε u) : sliceHi d ε u = d :=
  min_eq_left (h.2.trans (min_le_right _ _))

/-- **Vertex strips.** The slice of the degenerate segment `[a, a]` within `ε` of `a` is `{a}`. -/
theorem slice_self_eq {u : ℝ} (h : a ∈ Icc (u - ε) (u + ε)) : slice a a ε u = {a} := by
  rw [slice, max_eq_left h.1, min_eq_left h.2, Icc_self]

/-- **Vertex strips.** The slice of the degenerate segment `[a, a]` farther than `ε` from `a` is
empty. -/
theorem slice_self_eq_empty {u : ℝ} (h : a ∉ Icc (u - ε) (u + ε)) : slice a a ε u = ∅ :=
  Icc_eq_empty fun hle => h ⟨(le_max_right _ _).trans (hle.trans (min_le_left _ _)),
    (le_max_left _ _).trans (hle.trans (min_le_right _ _))⟩

variable (a d) in
/-- At `ε = 0` the slice is `[max a u, min d u]`: the point `u` when `u ∈ [a, d]`, else empty. -/
theorem slice_zero (u : ℝ) : slice a d 0 u = Icc (max a u) (min d u) := by
  simp only [slice, NNReal.coe_zero, sub_zero, add_zero]

variable (a d ε) in
/-- Slices are locally path-connected (convex subsets of `ℝ`). Activated as a local instance where
needed, as `RGraph.locallyPathConnectedSpace_Icc` is. -/
theorem locallyPathConnectedSpace_slice (u : ℝ) : LocallyPathConnectedSpace (slice a d ε u) :=
  RGraph.locallyPathConnectedSpace_Icc _ _

end Slice

/-! ### Transfer between slices -/

/-- **Slice transfer hypotheses** for the segment `[a, d]` from height `c` to height `u`: `c` avoids
the four events `a ± ε`, `d ± ε`, and the branches of both slice ends persist from `c` to `u`. -/
structure SliceTransfer (a d : ℝ) (ε : ℝ≥0) (c u : ℝ) : Prop where
  ne_lo_sub : c ≠ a - ε
  ne_lo_add : c ≠ a + ε
  ne_hi_sub : c ≠ d - ε
  ne_hi_add : c ≠ d + ε
  lo_le_left : c - ε ≤ a → u - ε ≤ a
  lo_le_right : c - ε ≤ d → u - ε ≤ d
  le_hi_left : a ≤ c + ε → a ≤ u + ε
  le_hi_right : d ≤ c + ε → d ≤ u + ε

end Thickening

open Thickening

/-- The transfer hypotheses of a critical list restrict to the segment of each edge. -/
theorem RGraph.TransferOK.sliceTransfer_edge {n : ℕ} {S : CriticalValues n} {ε : ℝ≥0} {c u : ℝ}
    (h : RGraph.TransferOK S ε c u) (e : Fin n) :
    SliceTransfer (S.value e.castSucc) (S.value e.succ) ε c u :=
  ⟨h.ne_sub _, h.ne_add _, h.ne_sub _, h.ne_add _, h.lo_le _, h.lo_le _, h.le_hi _, h.le_hi _⟩

/-- The transfer hypotheses of a critical list restrict to the degenerate segment of each level. -/
theorem RGraph.TransferOK.sliceTransfer_vertex {n : ℕ} {S : CriticalValues n} {ε : ℝ≥0}
    {c u : ℝ} (h : RGraph.TransferOK S ε c u) (i : Fin (n + 1)) :
    SliceTransfer (S.value i) (S.value i) ε c u :=
  ⟨h.ne_sub _, h.ne_add _, h.ne_sub _, h.ne_add _, h.lo_le _, h.lo_le _, h.le_hi _, h.le_hi _⟩

namespace Thickening

namespace SliceTransfer

variable {a d : ℝ} {ε : ℝ≥0} {c u : ℝ} (h : SliceTransfer a d ε c u)
include h

/-- The target slice is nonempty when the source slice is. -/
theorem sliceLo_le_sliceHi {s : ℝ} (hs : s ∈ slice a d ε c) : sliceLo a ε u ≤ sliceHi d ε u := by
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := mem_slice_iff.1 hs
  have hε := ε.coe_nonneg
  exact max_le (le_min (by linarith) (h.le_hi_left (by linarith)))
    (le_min (h.lo_le_right (by linarith)) (by linarith))

/-- Slice to slice. -/
theorem fragAff_mem {s : ℝ} (hs : s ∈ slice a d ε c) : fragAff a d ε c u s ∈ slice a d ε u :=
  RGraph.fragAff_mem (h.sliceLo_le_sliceHi hs) hs

/-- **Boundary compatibility.** A slice end at the lower segment end `a` stays there. -/
theorem fragAff_eq_left {s : ℝ} (hs : s ∈ slice a d ε c) (hsa : s = a) :
    fragAff a d ε c u s = a := by
  rw [hsa] at hs ⊢
  have hca : c - ε ≤ a := (le_max_right _ _).trans hs.1
  calc fragAff a d ε c u a = fragAff a d ε c u (max a (c - ε)) := by rw [max_eq_left hca]
    _ = max a (u - ε) := RGraph.fragAff_left _ _ _ _ _
    _ = a := max_eq_left (h.lo_le_left hca)

/-- **Boundary compatibility.** A slice end at the upper segment end `d` stays there. For a point
source slice this uses `a = d`, forced by event avoidance. -/
theorem fragAff_eq_right {s : ℝ} (hs : s ∈ slice a d ε c) (hsd : s = d) :
    fragAff a d ε c u s = d := by
  rw [hsd] at hs ⊢
  have hdc : d ≤ c + ε := hs.2.trans (min_le_right _ _)
  have hcd : c - ε ≤ d := (le_max_right _ _).trans hs.1
  have hR : min d (c + ε) = d := min_eq_left hdc
  rcases lt_or_ge (max a (c - ε)) (min d (c + ε)) with hlt | hge
  · calc fragAff a d ε c u d = fragAff a d ε c u (min d (c + ε)) := by rw [hR]
      _ = min d (u + ε) := RGraph.fragAff_right hlt
      _ = d := min_eq_left (h.le_hi_right hdc)
  · have hL : max a (c - ε) = d := le_antisymm hs.1 (hR.symm.le.trans hge)
    have had : a = d := by
      rcases max_choice a (c - ε) with hm | hm <;> rw [hm] at hL
      · exact hL
      · exact absurd (by linarith : c = d + ε) h.ne_hi_add
    calc fragAff a d ε c u d = fragAff a d ε c u (max a (c - ε)) := by rw [hL]
      _ = max a (u - ε) := RGraph.fragAff_left _ _ _ _ _
      _ = d := by rw [had]; exact max_eq_left (h.lo_le_right hcd)

omit h in
private theorem lt_of_lt (h : SliceTransfer a d ε c u) (h' : SliceTransfer a d ε u c)
    (hc : sliceLo a ε c < sliceHi d ε c) : sliceLo a ε u < sliceHi d ε u := by
  simp only [sliceLo, sliceHi, max_lt_iff, lt_min_iff] at hc ⊢
  obtain ⟨⟨h1, h3⟩, h2, h4⟩ := hc
  refine ⟨⟨h1, lt_of_le_of_ne (h.lo_le_right h3.le) fun he => h'.ne_hi_add (by linarith)⟩,
    lt_of_le_of_ne (h.le_hi_left h2.le) fun he => h'.ne_lo_sub (by linarith), by linarith⟩

/-- **Degenerate-uniform width.** With transfer hypotheses in both directions, the slices at `c`
and `u` are both nondegenerate or both degenerate. -/
theorem lt_iff (h' : SliceTransfer a d ε u c) :
    sliceLo a ε c < sliceHi d ε c ↔ sliceLo a ε u < sliceHi d ε u :=
  ⟨lt_of_lt h h', lt_of_lt h' h⟩

/-- **Degenerate-uniform interior inverse.** With transfer hypotheses in both directions, the
transfers `c → u` and `u → c` are mutually inverse on the slice at `c`. Unlike
`RGraph.fragAff_fragAff`, no slice is assumed nondegenerate. -/
theorem fragAff_fragAff (h' : SliceTransfer a d ε u c) {s : ℝ} (hs : s ∈ slice a d ε c) :
    fragAff a d ε u c (fragAff a d ε c u s) = s := by
  rcases lt_or_ge (sliceLo a ε c) (sliceHi d ε c) with hlt | hge
  · exact RGraph.fragAff_fragAff hlt (lt_of_lt h h' hlt) s
  · have hsL : s = max a (c - ε) := le_antisymm (hs.2.trans hge) hs.1
    rw [hsL, RGraph.fragAff_left, RGraph.fragAff_left]

/-- With transfer hypotheses in both directions, the transfer is injective on the slice. -/
theorem fragAff_injOn (h' : SliceTransfer a d ε u c) :
    Set.InjOn (fragAff a d ε c u) (slice a d ε c) := fun _ hs _ hs' he =>
  (h.fragAff_fragAff h' hs).symm.trans ((congrArg _ he).trans (h.fragAff_fragAff h' hs'))

end SliceTransfer

end Thickening

/-! ### Grids -/

namespace CriticalValues

variable {m : ℕ} (G : CriticalValues m)

/-- The levels of the grid `G` include the four events `a ± ε`, `d ± ε` of the segment `[a, d]`. -/
def HasEvents (a d : ℝ) (ε : ℝ≥0) : Prop :=
  a - ε ∈ Set.range G.value ∧ a + ε ∈ Set.range G.value ∧
    d - ε ∈ Set.range G.value ∧ d + ε ∈ Set.range G.value

/-- The levels of the grid `G` include every shifted level `S.value i ± ε` of `S` (and possibly
more). -/
def ContainsShifted {n : ℕ} (S : CriticalValues n) (ε : ℝ≥0) (G : CriticalValues m) : Prop :=
  ∀ i, S.value i - ε ∈ Set.range G.value ∧ S.value i + ε ∈ Set.range G.value

/-- The shifted witness lists every shifted level. -/
theorem containsShifted_shifted {n : ℕ} (S : CriticalValues n) (ε : ℝ≥0) :
    S.ContainsShifted ε (S.shifted ε) := fun i =>
  ⟨S.exists_shifted_value_eq_sub ε i, S.exists_shifted_value_eq_add ε i⟩

variable {G}

/-- A grid listing the shifted levels lists the events of the segment of each edge. -/
theorem ContainsShifted.hasEvents_edge {n : ℕ} {S : CriticalValues n} {ε : ℝ≥0}
    (hG : S.ContainsShifted ε G) (e : Fin n) :
    G.HasEvents (S.value e.castSucc) (S.value e.succ) ε :=
  ⟨(hG _).1, (hG _).2, (hG _).1, (hG _).2⟩

/-- A grid listing the shifted levels lists the events of the degenerate segment of each level. -/
theorem ContainsShifted.hasEvents_vertex {n : ℕ} {S : CriticalValues n} {ε : ℝ≥0}
    (hG : S.ContainsShifted ε G) (i : Fin (n + 1)) : G.HasEvents (S.value i) (S.value i) ε :=
  ⟨(hG i).1, (hG i).2, (hG i).1, (hG i).2⟩

private theorem ne_of_mem_K_of_mem_range {k : Fin m} {c x : ℝ} (hx : x ∈ Set.range G.value)
    (hc : c ∈ (G.K k : Set ℝ)) : c ≠ x := by
  rintro rfl
  obtain ⟨j, hj⟩ := hx
  exact G.value_notMem_K k j (by rw [hj]; exact hc)

private theorem le_of_mem_K_of_le {k : Fin m} {c u x : ℝ} (hx : x ∈ Set.range G.value)
    (hc : c ∈ (G.K k : Set ℝ)) (hu : u ∈ Seg G k) (hcx : c ≤ x) : u ≤ x := by
  obtain ⟨j, rfl⟩ := hx
  rcases RGraph.value_le_or_le G j k with h | h
  · exact absurd (hcx.trans h) (not_le.2 hc.1)
  · exact hu.2.trans h

private theorem le_of_mem_K_of_ge {k : Fin m} {c u x : ℝ} (hx : x ∈ Set.range G.value)
    (hc : c ∈ (G.K k : Set ℝ)) (hu : u ∈ Seg G k) (hxc : x ≤ c) : x ≤ u := by
  obtain ⟨j, rfl⟩ := hx
  rcases RGraph.value_le_or_le G j k with h | h
  · exact h.trans hu.1
  · exact absurd (h.trans hxc) (not_le.2 hc.2)

private theorem seg_subset_Icc_of_mem_K {k : Fin m} {c x y : ℝ} (hx : x ∈ Set.range G.value)
    (hy : y ∈ Set.range G.value) (hc : c ∈ (G.K k : Set ℝ)) (hcxy : c ∈ Icc x y) :
    Seg G k ⊆ Icc x y := fun _ hu =>
  ⟨le_of_mem_K_of_ge hx hc hu hcxy.1, le_of_mem_K_of_le hy hc hu hcxy.2⟩

/-- **Slab facts.** On a grid listing the shifted levels, the transfer hypotheses hold from a height
of an open slab to any height of the closed slab. Generalizes `RGraph.transferOK_of_mem` from the
shifted witness to any such grid. -/
theorem ContainsShifted.transferOK_of_mem {n : ℕ} {S : CriticalValues n} {ε : ℝ≥0}
    (hG : S.ContainsShifted ε G) {k : Fin m} {c u : ℝ} (hc : c ∈ (G.K k : Set ℝ))
    (hu : u ∈ Seg G k) : RGraph.TransferOK S ε c u where
  ne_sub i := ne_of_mem_K_of_mem_range (hG i).1 hc
  ne_add i := ne_of_mem_K_of_mem_range (hG i).2 hc
  lo_le i hi := by
    have := le_of_mem_K_of_le (hG i).2 hc hu (by linarith)
    linarith
  le_hi i hi := by
    have := le_of_mem_K_of_ge (hG i).1 hc hu (by linarith)
    linarith

/-- **Slab facts.** On a grid listing the events, the slice transfer hypotheses hold from a height
of an open slab to any height of the closed slab. -/
theorem HasEvents.sliceTransfer_of_mem {a d : ℝ} {ε : ℝ≥0} (hG : G.HasEvents a d ε) {k : Fin m}
    {c u : ℝ} (hc : c ∈ (G.K k : Set ℝ)) (hu : u ∈ Seg G k) : SliceTransfer a d ε c u where
  ne_lo_sub := ne_of_mem_K_of_mem_range hG.1 hc
  ne_lo_add := ne_of_mem_K_of_mem_range hG.2.1 hc
  ne_hi_sub := ne_of_mem_K_of_mem_range hG.2.2.1 hc
  ne_hi_add := ne_of_mem_K_of_mem_range hG.2.2.2 hc
  lo_le_left hi := by
    have := le_of_mem_K_of_le hG.2.1 hc hu (by linarith)
    linarith
  lo_le_right hi := by
    have := le_of_mem_K_of_le hG.2.2.2 hc hu (by linarith)
    linarith
  le_hi_left hi := by
    have := le_of_mem_K_of_ge hG.1 hc hu (by linarith)
    linarith
  le_hi_right hi := by
    have := le_of_mem_K_of_ge hG.2.2.1 hc hu (by linarith)
    linarith

variable (G)

/-- The midpoint of slab `k` of a grid. For the shifted witness it is `RGraph.mid`. -/
def mid (k : Fin m) : ℝ := (G.value k.castSucc + G.value k.succ) / 2

theorem mid_mem_K (k : Fin m) : G.mid k ∈ (G.K k : Set ℝ) := by
  have := G.strictMono (Fin.castSucc_lt_succ (i := k))
  exact ⟨by unfold mid; linarith, by unfold mid; linarith⟩

/-- On the shifted witness, the grid midpoint is the midpoint `RGraph.mid` of the graph case. -/
theorem _root_.TDA.Reeb.RGraph.mid_eq_shifted_mid {n : ℕ} (S : CriticalValues n) (ε : ℝ≥0)
    (k : Fin (S.shiftedCount ε)) : RGraph.mid S ε k = (S.shifted ε).mid k :=
  rfl

variable {G}

/-- **Slab facts.** If the midpoint of a slab lies in `[a - ε, d + ε]`, so does the closed slab. -/
theorem HasEvents.seg_subset_of_mid_mem {a d : ℝ} {ε : ℝ≥0} (hG : G.HasEvents a d ε) {k : Fin m}
    (hmid : G.mid k ∈ Icc (a - ε) (d + ε)) : Seg G k ⊆ Icc (a - ε) (d + ε) :=
  seg_subset_Icc_of_mem_K hG.1 hG.2.2.2 (G.mid_mem_K k) hmid

/-- The midpoint slice of a slab is nonempty exactly when the closed slab lies in
`[a - ε, d + ε]`. -/
theorem HasEvents.slice_mid_nonempty_iff {a d : ℝ} {ε : ℝ≥0} (hG : G.HasEvents a d ε) (had : a ≤ d)
    {k : Fin m} : (slice a d ε (G.mid k)).Nonempty ↔ Seg G k ⊆ Icc (a - ε) (d + ε) := by
  rw [slice_nonempty_iff had]
  exact ⟨hG.seg_subset_of_mid_mem, fun h => h ⟨(G.mid_mem_K k).1.le, (G.mid_mem_K k).2.le⟩⟩

/-- Every height of `[a - ε, d + ε]` is a level of the grid or lies in an open slab whose closure is
inside `[a - ε, d + ε]`. -/
theorem HasEvents.eq_value_or_mem_K {a d : ℝ} {ε : ℝ≥0} (hG : G.HasEvents a d ε) {u : ℝ}
    (hu : u ∈ Icc (a - ε) (d + ε)) :
    (∃ j, G.value j = u) ∨ ∃ k, u ∈ (G.K k : Set ℝ) ∧ Seg G k ⊆ Icc (a - ε) (d + ε) := by
  by_cases hv : ∃ j, G.value j = u
  · exact .inl hv
  obtain ⟨j0, hj0⟩ := hG.1
  obtain ⟨j1, hj1⟩ := hG.2.2.2
  have h0 : G.value 0 ≤ u :=
    (G.strictMono.monotone (Fin.zero_le j0)).trans (by rw [hj0]; exact hu.1)
  have h1 : u ≤ G.value (Fin.last m) :=
    (by rw [hj1]; exact hu.2 : u ≤ G.value j1).trans (G.strictMono.monotone (Fin.le_last j1))
  obtain ⟨k, hk⟩ := CriticalValues.exists_mem_K_of_mem_Icc ⟨h0, h1⟩ (not_exists.1 hv)
  exact .inr ⟨k, hk, seg_subset_Icc_of_mem_K hG.1 hG.2.2.2 hk hu⟩

/-- The two-level grid `a < d` of a single segment. -/
def pair (a d : ℝ) (had : a < d) : CriticalValues 1 where
  value := ![a, d]
  strictMono := Fin.strictMono_iff_lt_succ.2 fun i => by fin_cases i; simpa using had

@[simp] theorem pair_value_zero {a d : ℝ} (had : a < d) : (pair a d had).value 0 = a := rfl

@[simp] theorem pair_value_one {a d : ℝ} (had : a < d) : (pair a d had).value 1 = d := rfl

/-- The levels of the shifted witness of `pair a d had` are the distinct values among
`a ± ε`, `d ± ε`. -/
theorem range_shifted_pair {a d : ℝ} (had : a < d) (ε : ℝ≥0) :
    Set.range ((pair a d had).shifted ε).value = {a - ε, a + ε, d - ε, d + ε} := by
  ext x
  rw [mem_range_shifted_iff]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, h | h⟩ <;> fin_cases i
    exacts [.inl h, .inr (.inr (.inl h)), .inr (.inl h), .inr (.inr (.inr h))]
  · rintro (h | h | h | h)
    exacts [⟨0, .inl h⟩, ⟨0, .inr h⟩, ⟨1, .inl h⟩, ⟨1, .inr h⟩]

/-- The shifted witness of `pair a d had` lists the four events of `[a, d]`. -/
theorem pair_hasEvents {a d : ℝ} (had : a < d) (ε : ℝ≥0) :
    ((pair a d had).shifted ε).HasEvents a d ε :=
  ((pair a d had).containsShifted_shifted ε).hasEvents_edge 0

end CriticalValues

/-! ### Polygons -/

namespace Thickening

section Polygon

variable (a d : ℝ) (ε : ℝ≥0) {m : ℕ} (G : CriticalValues m)

/-- The parallelogram `{(s, u) | s ∈ [a, d], |s - u| ≤ ε} = {(s, u) | s ∈ J(u)}`, the thickened
segment in the coordinates `(s, u = s + t)`. -/
def parallelogram : Set (ℝ × ℝ) := {p | p.1 ∈ slice a d ε p.2}

/-- The slab polygon over the closed slab `k`, present only when the closed slab lies inside
`[a - ε, d + ε]`. A slab meeting `[a - ε, d + ε]` in a corner only has an empty polygon; its corner
fibre lies in a level slice. -/
def polygon (k : Fin m) : Set (ℝ × ℝ) :=
  {p | p.1 ∈ slice a d ε p.2 ∧ p.2 ∈ Seg G k ∧ Seg G k ⊆ Icc (a - ε) (d + ε)}

/-- The slice at level `j`, as a subset of the parallelogram. -/
def levelSet (j : Fin (m + 1)) : Set (ℝ × ℝ) := {p | p.1 ∈ slice a d ε p.2 ∧ p.2 = G.value j}

theorem isClosed_parallelogram : IsClosed (parallelogram a d ε) :=
  (isClosed_le (by fun_prop) continuous_fst).inter (isClosed_le continuous_fst (by fun_prop))

theorem isClosed_polygon (k : Fin m) : IsClosed (polygon a d ε G k) :=
  (isClosed_parallelogram a d ε).inter
    ((isClosed_Icc.preimage continuous_snd).inter isClosed_const)

theorem isClosed_levelSet (j : Fin (m + 1)) : IsClosed (levelSet a d ε G j) :=
  (isClosed_parallelogram a d ε).inter (isClosed_eq continuous_snd continuous_const)

theorem polygon_subset (k : Fin m) : polygon a d ε G k ⊆ parallelogram a d ε := fun _ hp => hp.1

theorem levelSet_subset (j : Fin (m + 1)) : levelSet a d ε G j ⊆ parallelogram a d ε :=
  fun _ hp => hp.1

variable {a d ε G}

/-- The slab polygons and the level slices cover the parallelogram. -/
theorem iUnion_polygon_union_levelSet (hG : G.HasEvents a d ε) :
    (⋃ k, polygon a d ε G k) ∪ ⋃ j, levelSet a d ε G j = parallelogram a d ε := by
  refine Subset.antisymm (union_subset (iUnion_subset fun k => polygon_subset a d ε G k)
    (iUnion_subset fun j => levelSet_subset a d ε G j)) fun p hp => ?_
  rcases hG.eq_value_or_mem_K (mem_Icc_of_mem_slice hp) with ⟨j, hj⟩ | ⟨k, hk, hseg⟩
  · exact mem_union_right _ (mem_iUnion.2 ⟨j, hp, hj.symm⟩)
  · exact mem_union_left _ (mem_iUnion.2 ⟨k, hp, ⟨hk.1.le, hk.2.le⟩, hseg⟩)

variable (a d ε G)

/-- The scalar polygon map `(σ, u) ↦ (fragAff a d ε (mid k) u σ, u)` from the reference slice at
the slab midpoint times the closed slab onto the slab polygon. -/
def polygonMap (hG : G.HasEvents a d ε) (k : Fin m) :
    C(slice a d ε (G.mid k) × Seg G k, polygon a d ε G k) where
  toFun p := ⟨(fragAff a d ε (G.mid k) p.2 p.1, p.2),
    (hG.sliceTransfer_of_mem (G.mid_mem_K k) p.2.2).fragAff_mem p.1.2, p.2.2,
    hG.seg_subset_of_mid_mem (mem_Icc_of_mem_slice p.1.2)⟩
  continuous_toFun :=
    (((RGraph.continuous_fragAff a d ε (G.mid k)).comp
      (continuous_subtype_val.prodMap continuous_subtype_val)).prodMk
        (continuous_subtype_val.comp continuous_snd)).subtype_mk _

@[simp] theorem coe_polygonMap (hG : G.HasEvents a d ε) (k : Fin m)
    (p : slice a d ε (G.mid k) × Seg G k) :
    ((polygonMap a d ε G hG k p : polygon a d ε G k) : ℝ × ℝ) =
      (fragAff a d ε (G.mid k) p.2 p.1, (p.2 : ℝ)) :=
  rfl

variable {a d ε G}

/-- The scalar polygon map is onto. At a slab end with a point slice, the lower end of the
reference slice is a preimage; elsewhere the inverse transfer is. -/
theorem polygonMap_surjective (hG : G.HasEvents a d ε) (k : Fin m) :
    Function.Surjective (polygonMap a d ε G hG k) := by
  rintro ⟨⟨s, u⟩, hs, hu, hseg⟩
  have hK := G.mid_mem_K k
  have hmid : G.mid k ∈ Icc (a - ε) (d + ε) := hseg ⟨hK.1.le, hK.2.le⟩
  have had : a ≤ d := (mem_slice_iff.1 hs).1.1.trans (mem_slice_iff.1 hs).1.2
  have hne : (slice a d ε (G.mid k)).Nonempty := (slice_nonempty_iff had).2 hmid
  rcases lt_or_ge (sliceLo a ε u) (sliceHi d ε u) with hlt | hge
  · have hmlt : sliceLo a ε (G.mid k) < sliceHi d ε (G.mid k) := by
      have hne1 := CriticalValues.ne_of_mem_K_of_mem_range hG.1 hK
      have hne4 := CriticalValues.ne_of_mem_K_of_mem_range hG.2.2.2 hK
      simp only [sliceLo, sliceHi, max_lt_iff, lt_min_iff] at hlt ⊢
      have h1 := hmid.1
      have h2 := hmid.2
      refine ⟨⟨hlt.1.1, lt_of_le_of_ne (by linarith) fun he => hne4 (by linarith)⟩,
        lt_of_le_of_ne (by linarith) fun he => hne1 (by linarith), by linarith [hlt.2.2]⟩
    refine ⟨(⟨fragAff a d ε u (G.mid k) s, RGraph.fragAff_mem hmlt.le hs⟩, ⟨u, hu⟩), ?_⟩
    exact Subtype.ext (Prod.ext (RGraph.fragAff_fragAff hlt hmlt s) rfl)
  · have hsL : s = sliceLo a ε u := le_antisymm (hs.2.trans hge) hs.1
    refine ⟨(⟨sliceLo a ε (G.mid k), left_mem_Icc.2 (nonempty_Icc.1 hne)⟩, ⟨u, hu⟩), ?_⟩
    exact Subtype.ext (Prod.ext ((RGraph.fragAff_left _ _ _ _ _).trans hsL.symm) rfl)

/-- The scalar polygon map is proper: a continuous map from a compact space to a Hausdorff
subspace of `ℝ × ℝ`. -/
theorem isProperMap_polygonMap (hG : G.HasEvents a d ε) (k : Fin m) :
    IsProperMap (polygonMap a d ε G hG k) :=
  (polygonMap a d ε G hG k).continuous.isProperMap

/-- The fibres of the scalar polygon map: same height and same transferred parameter. -/
theorem polygonMap_eq_iff (hG : G.HasEvents a d ε) (k : Fin m)
    {p p' : slice a d ε (G.mid k) × Seg G k} :
    polygonMap a d ε G hG k p = polygonMap a d ε G hG k p' ↔
      (p.2 : ℝ) = p'.2 ∧
        fragAff a d ε (G.mid k) p.2 p.1 = fragAff a d ε (G.mid k) p'.2 p'.1 := by
  rw [← Subtype.coe_inj, coe_polygonMap, coe_polygonMap, Prod.mk.injEq, and_comm]

/-- Issue #706 (2) applied to the scalar polygon map: after product with an arbitrary space `E`,
with no separation hypothesis on `E`, it is still a quotient map. -/
theorem isQuotientMap_prodMap_polygonMap (hG : G.HasEvents a d ε) (k : Fin m) (E : Type*)
    [TopologicalSpace E] :
    Topology.IsQuotientMap (Prod.map (id : E → E) (polygonMap a d ε G hG k)) :=
  TDA.Topology.isQuotientMap_prodMap_id_of_compactSpace (polygonMap a d ε G hG k).continuous
    (polygonMap_surjective hG k)

end Polygon

end Thickening

end

end TDA.Reeb
