import TDA.Reeb.ConstructibleSpace
import Mathlib.Topology.Algebra.Module.LocallyConvex

/-!
# Closed height windows of finite ℝ-graphs

For finite data `D` over a list of levels `S`, the closed window
`window S D lo hi = {x | lo ≤ height x ≤ hi}` of the realization, with its exact topology,
and the affine fragment map that moves fragments of a segment between windows.

## The affine fragment map

For a segment `[a, d]`, a half-width `ε` and heights `c`, `u`, write `L(u) = max a (u - ε)` and
`R(u) = min d (u + ε)`. The map

```
fragAff a d ε c u s = L(u) + (s - L(c)) * ((R(u) - L(u)) / (R(c) - L(c)))
```

sends the fragment `[L(c), R(c)]` to `[L(u), R(u)]` whenever the target is nonempty
(`fragAff_mem`). Its denominator depends on `c` only, so it is jointly continuous in the parameter
and the height (`continuous_fragAff`). It preserves the lower end (`fragAff_left`), and the upper
end for a nondegenerate source (`fragAff_right`); it is constant when the target is a point
(`fragAff_collapse`); the maps `c → u` and `u → c` are mutually inverse when both fragments are
nondegenerate (`fragAff_fragAff`). A nonempty fragment at a height `c` that avoids the four events
`a ± ε`, `d ± ε` is nondegenerate when `ε > 0` (`fragLo_lt_fragHi`).

## The window and its raw cover

The raw window `WindowRaw S D lo hi` is the finite sum of the window vertices (`WindowV`, the
vertices whose level lies in `[lo, hi]`, discrete) and one closed fragment
`frag S e lo hi = [max a lo, min d hi]` per labelled edge with segment `[a, d]` (`WindowE`), which
may be empty or a point. `windowCover` is the merged `quotMk` on these raw points, so two raw
points are identified exactly when their merged normal forms agree (`windowCover_eq_iff`): a
fragment end is glued to its original vertex precisely when it equals that vertex's level, and
nothing else is glued. Every window point is a vertex at a level in the window or an edge point
whose height lies in the window (`windowCover_surjective`).

The raw window is compact and the window is Hausdorff, as a subspace of the realization of finite
data, so `windowCover` is a quotient map (`isQuotientMap_windowCover`). This is the exact topology
of the window. Every closed real interval is locally path-connected
(`locallyPathConnectedSpace_Icc`, used here as a local instance), so the window is compact,
Hausdorff and locally path-connected (`instCompactSpaceWindow`,
`instLocallyPathConnectedSpaceWindow`, `window_t2Space`).

See `docs/math/reeb-rgraph-thickening.md`.
-/

open Set Topology

universe u

namespace TDA.Reeb

noncomputable section

namespace RGraph

open CylinderPresentation

/-! ### The affine fragment map -/

section Fragment

variable {a d ε c u s : ℝ}

/-- The affine fragment map from `[max a (c - ε), min d (c + ε)]` to
`[max a (u - ε), min d (u + ε)]`. The denominator depends on `c` only. -/
def fragAff (a d ε c u s : ℝ) : ℝ :=
  max a (u - ε) + (s - max a (c - ε)) *
    ((min d (u + ε) - max a (u - ε)) / (min d (c + ε) - max a (c - ε)))

/-- Joint continuity in the parameter `s` and the height `u`. -/
theorem continuous_fragAff (a d ε c : ℝ) : Continuous fun p : ℝ × ℝ => fragAff a d ε c p.2 p.1 := by
  unfold fragAff
  fun_prop

/-- The lower fragment end goes to the lower fragment end. -/
theorem fragAff_left (a d ε c u : ℝ) : fragAff a d ε c u (max a (c - ε)) = max a (u - ε) := by
  simp [fragAff]

/-- The upper fragment end goes to the upper fragment end, for a nondegenerate source fragment. -/
theorem fragAff_right (h : max a (c - ε) < min d (c + ε)) :
    fragAff a d ε c u (min d (c + ε)) = min d (u + ε) := by
  have h' : min d (c + ε) - max a (c - ε) ≠ 0 := (sub_pos.2 h).ne'
  have hm : (min d (c + ε) - max a (c - ε)) *
      ((min d (u + ε) - max a (u - ε)) / (min d (c + ε) - max a (c - ε))) =
        min d (u + ε) - max a (u - ε) := by
    rw [mul_div_assoc', mul_div_cancel_left₀ _ h']
  unfold fragAff
  rw [hm]
  ring

/-- Fragment to fragment, whenever the target fragment is nonempty. -/
theorem fragAff_mem (hu : max a (u - ε) ≤ min d (u + ε))
    (hs : s ∈ Icc (max a (c - ε)) (min d (c + ε))) :
    fragAff a d ε c u s ∈ Icc (max a (u - ε)) (min d (u + ε)) := by
  have hw : 0 ≤ min d (c + ε) - max a (c - ε) := sub_nonneg.2 (hs.1.trans hs.2)
  have hW : 0 ≤ min d (u + ε) - max a (u - ε) := sub_nonneg.2 hu
  have h1 : 0 ≤ s - max a (c - ε) := sub_nonneg.2 hs.1
  have h2 : s - max a (c - ε) ≤ min d (c + ε) - max a (c - ε) := sub_le_sub_right hs.2 _
  have hq : 0 ≤ (min d (u + ε) - max a (u - ε)) / (min d (c + ε) - max a (c - ε)) :=
    div_nonneg hW hw
  have h3 : (s - max a (c - ε)) *
      ((min d (u + ε) - max a (u - ε)) / (min d (c + ε) - max a (c - ε))) ≤
        min d (u + ε) - max a (u - ε) := by
    rcases hw.eq_or_lt with h0 | h0
    · rw [← h0, div_zero, mul_zero]
      exact hW
    · calc _ ≤ (min d (c + ε) - max a (c - ε)) *
            ((min d (u + ε) - max a (u - ε)) / (min d (c + ε) - max a (c - ε))) :=
            mul_le_mul_of_nonneg_right h2 hq
        _ = _ := by rw [mul_div_assoc', mul_div_cancel_left₀ _ h0.ne']
  have h4 := mul_nonneg h1 hq
  unfold fragAff
  exact ⟨by linarith, by linarith⟩

/-- **Endpoint collapse.** When the target fragment is a point, the map is constant. -/
theorem fragAff_collapse (hu : max a (u - ε) = min d (u + ε)) (c s : ℝ) :
    fragAff a d ε c u s = max a (u - ε) := by
  simp [fragAff, hu]

/-- **Interior inverse.** For two nondegenerate fragments the maps `c → u` and `u → c` are
mutually inverse. -/
theorem fragAff_fragAff (hc : max a (c - ε) < min d (c + ε))
    (hu : max a (u - ε) < min d (u + ε)) (s : ℝ) :
    fragAff a d ε u c (fragAff a d ε c u s) = s := by
  have h1 := (sub_pos.2 hc).ne'
  have h2 := (sub_pos.2 hu).ne'
  have hAB : (min d (u + ε) - max a (u - ε)) / (min d (c + ε) - max a (c - ε)) *
      ((min d (c + ε) - max a (c - ε)) / (min d (u + ε) - max a (u - ε))) = 1 := by
    rw [div_mul_div_comm, mul_comm (min d (u + ε) - max a (u - ε)),
      div_self (mul_ne_zero h1 h2)]
  unfold fragAff
  linear_combination (s - max a (c - ε)) * hAB

/-- **Fixed positive denominator.** A nonempty fragment of `[a, d]` at a height `c` that avoids
the four events `a ± ε`, `d ± ε` is nondegenerate when `ε > 0`. -/
theorem fragLo_lt_fragHi (had : a < d) (hε : 0 < ε) (h1 : a ≤ c + ε) (h1' : c ≠ a - ε)
    (h2 : c - ε ≤ d) (h2' : c ≠ d + ε) : max a (c - ε) < min d (c + ε) := by
  refine max_lt (lt_min had (lt_of_le_of_ne h1 ?_)) (lt_min (lt_of_le_of_ne h2 ?_) (by linarith))
  · intro h
    exact h1' (by linarith)
  · intro h
    exact h2' (by linarith)

end Fragment

/-! ### The closed window and its raw cover -/

/-- Closed real intervals are locally path-connected (convex subsets of `ℝ`). The pinned mathlib
has no such instance; this theorem is activated as a local instance where fragments need it, not
as a global instance on every real interval. -/
theorem locallyPathConnectedSpace_Icc (a b : ℝ) : LocallyPathConnectedSpace (Icc a b) :=
  (convex_Icc a b).locallyPathConnectedSpace

attribute [local instance] locallyPathConnectedSpace_Icc

section Window

variable {n : ℕ} (S : CriticalValues n) (D : FiniteReebData.{u} n)

/-- The closed window `{x | lo ≤ height x ≤ hi}` of the realization of finite data. -/
def window (lo hi : ℝ) : Set ((ofFiniteData D).Realization S) :=
  (ofFiniteData D).height S ⁻¹' Icc lo hi

theorem mem_window {lo hi : ℝ} {x : (ofFiniteData D).Realization S} :
    x ∈ window S D lo hi ↔ (ofFiniteData D).height S x ∈ Icc lo hi :=
  Iff.rfl

/-- The closed fragment `[max a lo, min d hi]` of the segment `[a, d]` of edge `e`; possibly empty
or a point. -/
abbrev frag (e : Fin n) (lo hi : ℝ) : Set ℝ :=
  Icc (max (S.value e.castSucc) lo) (min (S.value e.succ) hi)

variable {S} in
theorem frag_subset_seg {e : Fin n} {lo hi : ℝ} : frag S e lo hi ⊆ Seg S e :=
  Icc_subset_Icc (le_max_left _ _) (min_le_left _ _)

variable {S} in
theorem frag_subset_Icc {e : Fin n} {lo hi : ℝ} : frag S e lo hi ⊆ Icc lo hi :=
  Icc_subset_Icc (le_max_right _ _) (min_le_right _ _)

/-- Window vertices: vertices whose level lies in the window (finite, discrete). -/
abbrev WindowV (lo hi : ℝ) := {p : (ofFiniteData D).VertexPiece // S.value p.1 ∈ Icc lo hi}

/-- Window edge fragments: one closed fragment per labelled edge. -/
abbrev WindowE (lo hi : ℝ) := Σ c : (Σ e, D.E e), frag S c.1 lo hi

/-- The raw window: a finite sum of points and closed real intervals. -/
abbrev WindowRaw (lo hi : ℝ) := WindowV S D lo hi ⊕ WindowE S D lo hi

/-- Raw window points as raw points of the presentation. -/
def windowIncl (lo hi : ℝ) : WindowRaw S D lo hi → (ofFiniteData D).Raw S :=
  Sum.map Subtype.val fun c => ⟨c.1.1, c.1.2, ⟨c.2.1, frag_subset_seg c.2.2⟩⟩

theorem continuous_windowIncl (lo hi : ℝ) : Continuous (windowIncl S D lo hi) :=
  continuous_subtype_val.sumMap (continuous_sigma fun c => by
    dsimp only
    exact continuous_sigmaMk.comp (continuous_const.prodMk (continuous_subtype_val.subtype_mk _)))

theorem windowIncl_mem {lo hi : ℝ} (r : WindowRaw S D lo hi) :
    (ofFiniteData D).quotMk S (windowIncl S D lo hi r) ∈ window S D lo hi := by
  rcases r with p | c
  · exact p.2
  · exact frag_subset_Icc c.2.2

/-- The raw cover of the window: the quotient map on raw window points. -/
def windowCover (lo hi : ℝ) : C(WindowRaw S D lo hi, window S D lo hi) where
  toFun r := ⟨(ofFiniteData D).quotMk S (windowIncl S D lo hi r), windowIncl_mem S D r⟩
  continuous_toFun :=
    (((ofFiniteData D).continuous_quotMk S).comp (continuous_windowIncl S D lo hi)).subtype_mk _

theorem coe_windowCover {lo hi : ℝ} (r : WindowRaw S D lo hi) :
    (windowCover S D lo hi r : (ofFiniteData D).Realization S) =
      (ofFiniteData D).quotMk S (windowIncl S D lo hi r) :=
  rfl

/-- **Exact gluing.** Two raw window points are identified exactly when their merged normal forms
agree: a fragment end is glued to its original vertex precisely when it is that vertex's level,
and nothing else is glued. -/
theorem windowCover_eq_iff {lo hi : ℝ} {r r' : WindowRaw S D lo hi} :
    windowCover S D lo hi r = windowCover S D lo hi r' ↔
      (ofFiniteData D).nf S (windowIncl S D lo hi r) =
        (ofFiniteData D).nf S (windowIncl S D lo hi r') :=
  Subtype.ext_iff.trans ((ofFiniteData D).quotMk_eq_iff S)

theorem windowCover_surjective (lo hi : ℝ) : Function.Surjective (windowCover S D lo hi) := by
  rintro ⟨x, hx⟩
  rcases (ofFiniteData D).exists_rep S x with ⟨i, v, rfl⟩ | ⟨e, ⟨y, t⟩, rfl⟩
  · exact ⟨.inl ⟨⟨i, v⟩, hx⟩, rfl⟩
  · have ht : (t : ℝ) ∈ Icc lo hi := hx
    exact ⟨.inr ⟨⟨e, y⟩, ⟨t, max_le t.2.1.le ht.1, le_min t.2.2.le ht.2⟩⟩, rfl⟩

/-- **The topology bridge.** The raw cover is a quotient map: a continuous surjection from a
compact space onto a Hausdorff subspace of the graph realization. -/
theorem isQuotientMap_windowCover (lo hi : ℝ) : IsQuotientMap (windowCover S D lo hi) :=
  IsQuotientMap.of_surjective_continuous (windowCover_surjective S D lo hi)
    (windowCover S D lo hi).continuous

instance instCompactSpaceWindow (lo hi : ℝ) : CompactSpace (window S D lo hi) :=
  Function.Surjective.compactSpace (windowCover S D lo hi).continuous
    (windowCover_surjective S D lo hi)

instance instLocallyPathConnectedSpaceWindow (lo hi : ℝ) :
    LocallyPathConnectedSpace (window S D lo hi) :=
  (isQuotientMap_windowCover S D lo hi).locallyPathConnectedSpace

theorem window_t2Space (lo hi : ℝ) : T2Space (window S D lo hi) := inferInstance

theorem window_compactSpace (lo hi : ℝ) : CompactSpace (window S D lo hi) := inferInstance

theorem window_locallyPathConnectedSpace (lo hi : ℝ) :
    LocallyPathConnectedSpace (window S D lo hi) := inferInstance

end Window

end RGraph

end

end TDA.Reeb
