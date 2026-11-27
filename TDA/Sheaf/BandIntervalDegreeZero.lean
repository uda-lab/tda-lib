import TDA.Sheaf.BandThickening
import TDA.Sheaf.RealIntervalRecognition
import TDA.Sheaf.RealConstructibleRefinement
import Mathlib.Analysis.Convex.Topology
import Mathlib.Topology.Algebra.Group.Pointwise

/-!
# Degree-zero convolution of real interval sheaves

The output set consists of the centres whose closed band window meets the input interval
in a nonempty closed set. Thickening a convex open meets the input in a nonempty relatively
closed set exactly when the open meets this output in the same way.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite TDA.Persistence
open scoped Pointwise

namespace TDA.Sheaf.BandConvolution

open RealStratification RealConstructible AlternatingDiagram

/-- The centres whose closed radius-`ε` window meets `I` in a nonempty closed set. -/
def outSet0 (ε : ℝ) (I : Set ℝ) : Set ℝ :=
  {y | (I ∩ Set.Icc (y - ε) (y + ε)).Nonempty ∧ IsClosed (I ∩ Set.Icc (y - ε) (y + ε))}

private def windowHits (ε : ℝ) (I : Set ℝ) : Set ℝ :=
  {y | ∃ x ∈ I, x ∈ Set.Icc (y - ε) (y + ε)}

private theorem windowHits_eq_add (ε : ℝ) (I : Set ℝ) :
    windowHits ε I = I + Set.Icc (-ε) ε := by
  ext y
  change (∃ x ∈ I, x ∈ Set.Icc (y - ε) (y + ε)) ↔ y ∈ I + Set.Icc (-ε) ε
  rw [Set.mem_add]
  constructor
  · rintro ⟨x, hx, hl, hu⟩
    exact ⟨x, hx, y - x, ⟨by linarith, by linarith⟩, by ring⟩
  · rintro ⟨x, hx, z, ⟨hl, hu⟩, rfl⟩
    exact ⟨x, hx, ⟨by linarith, by linarith⟩⟩

private theorem isClosed_windowHits {ε : ℝ} {I : Set ℝ} (h : IsClosed I) :
    IsClosed (windowHits ε I) := by
  rw [windowHits_eq_add]
  exact h.add_right_of_isCompact isCompact_Icc

private theorem closure_inter_window {I : Set ℝ} (hI : Convex ℝ I) {l u : ℝ}
    (hne : (I ∩ Set.Icc l u).Nonempty) :
    closure (I ∩ Set.Icc l u) = closure I ∩ Set.Icc l u := by
  refine Set.Subset.antisymm (closure_minimal
    (Set.inter_subset_inter_left _ subset_closure) (isClosed_closure.inter isClosed_Icc)) ?_
  rintro x ⟨hx, hxK⟩
  by_cases hxI : x ∈ I
  · exact subset_closure ⟨hxI, hxK⟩
  obtain ⟨z, hzI, hzK⟩ := hne
  rcases lt_or_gt_of_ne (show x ≠ z from fun h => hxI (h ▸ hzI)) with h | h
  · have hsub : Set.Ioo x z ⊆ I ∩ Set.Icc l u := fun w hw =>
      ⟨hI.Ioo_subset_of_mem_closure hx (subset_closure hzI) hw,
        ⟨hxK.1.trans hw.1.le, hw.2.le.trans hzK.2⟩⟩
    exact closure_mono hsub (by rw [closure_Ioo h.ne]; exact ⟨le_rfl, h.le⟩)
  · have hsub : Set.Ioo z x ⊆ I ∩ Set.Icc l u := fun w hw =>
      ⟨hI.Ioo_subset_of_mem_closure (subset_closure hzI) hx hw,
        ⟨hzK.1.trans hw.1.le, hw.2.le.trans hxK.2⟩⟩
    exact closure_mono hsub (by rw [closure_Ioo h.ne]; exact ⟨h.le, le_rfl⟩)

private theorem outSet0_eq_sdiff {I : Set ℝ} (hI : I.OrdConnected) (ε : ℝ) :
    outSet0 ε I = windowHits ε (closure I) \ windowHits ε (closure I \ I) := by
  ext y
  constructor
  · rintro ⟨hne, hcl⟩
    have hc := closure_inter_window (convex_iff_ordConnected.2 hI) hne
    obtain ⟨x, hx, hxy⟩ := hne
    refine ⟨⟨x, subset_closure hx, hxy⟩, ?_⟩
    rintro ⟨z, ⟨hz, hzI⟩, hzK⟩
    have hz' : z ∈ closure (I ∩ Set.Icc (y - ε) (y + ε)) := hc.symm ▸ ⟨hz, hzK⟩
    exact hzI (hcl.closure_eq ▸ hz' : z ∈ I ∩ Set.Icc (y - ε) (y + ε)).1
  · rintro ⟨⟨x, hx, hxy⟩, hbad⟩
    have hsub : closure I ∩ Set.Icc (y - ε) (y + ε) ⊆ I := fun z hz =>
      not_not.mp fun hn => hbad ⟨z, ⟨hz.1, hn⟩, hz.2⟩
    refine ⟨⟨x, hsub ⟨hx, hxy⟩, hxy⟩, ?_⟩
    have he : I ∩ Set.Icc (y - ε) (y + ε) = closure I ∩ Set.Icc (y - ε) (y + ε) :=
      Set.Subset.antisymm (Set.inter_subset_inter_left _ subset_closure)
        (fun z hz => ⟨hsub hz, hz.2⟩)
    rw [he]
    exact isClosed_closure.inter isClosed_Icc

private theorem mem_bandOpen_window {ε : ℝ} {U : Opens realLine} {x : ℝ} :
    x ∈ bandOpen ε U ↔ ∃ y ∈ U, x ∈ Set.Icc (y - ε) (y + ε) := by
  change (∃ y ∈ U, dist x y ≤ ε) ↔ _
  refine exists_congr fun y => and_congr_right fun _ => ?_
  rw [Real.dist_eq, abs_le, Set.mem_Icc]
  constructor <;> rintro ⟨hl, hu⟩ <;> constructor <;> linarith

/-- Sections on an order-connected open are governed by the same nonempty relative closedness
test for the output set as sections on the thickened open are for the input interval. -/
theorem meetsClosed_outSet0_iff {ε : ℝ} (_hε : 0 ≤ ε) {I : Set ℝ}
    (hI : I.OrdConnected) (hclosed : IsLocallyClosed I)
    {U : Opens realLine} (hU : (U : Set ℝ).OrdConnected) :
    MeetsClosed (outSet0 ε I) U ↔ MeetsClosed I (bandOpen ε U) := by
  let H := windowHits ε (closure I)
  let B := windowHits ε (closure I \ I)
  have hH : IsClosed H := isClosed_windowHits isClosed_closure
  have hB : IsClosed B :=
    isClosed_windowHits (isOpen_compl_iff.mp hclosed.isOpen_coborder)
  have hout : outSet0 ε I = H \ B := outSet0_eq_sdiff hI ε
  have hs : (outSet0 ε I) ⊆ H := hout ▸ Set.sdiff_subset
  constructor
  · rintro ⟨hcl, y, hyU, hy⟩
    have hc : IsPreconnected (H ∩ (U : Set ℝ)) := by
      apply Convex.isPreconnected
      refine Convex.inter ?_ (convex_iff_ordConnected.2 hU)
      dsimp [H]
      rw [windowHits_eq_add]
      exact (convex_iff_ordConnected.2 hI).closure.add (convex_Icc _ _)
    have hsub : H ∩ (U : Set ℝ) ⊆ outSet0 ε I := by
      intro z hz
      by_contra hn
      have hcover : H ∩ (U : Set ℝ) ⊆ Bᶜ ∪ (closure (outSet0 ε I))ᶜ := by
        intro w hw
        by_cases h : w ∈ closure (outSet0 ε I)
        · exact Or.inl (show w ∈ H \ B from hout ▸ hcl ⟨h, hw.2⟩).2
        · exact Or.inr h
      obtain ⟨w, hw, hwB, hwCl⟩ := hc _ _ hB.isOpen_compl isClosed_closure.isOpen_compl hcover
        ⟨y, ⟨hs hy, hyU⟩, (show y ∈ H \ B from hout ▸ hy).2⟩
        ⟨z, hz, fun h => hn (hcl ⟨h, hz.2⟩)⟩
      exact hwCl (subset_closure (show w ∈ outSet0 ε I from hout.symm ▸ ⟨hw.1, hwB⟩))
    refine ⟨?_, ?_⟩
    · rintro x ⟨hx, hxU⟩
      by_contra hn
      obtain ⟨z, hz, hxK⟩ := mem_bandOpen_window.mp hxU
      exact (show z ∈ H \ B from hout ▸ hsub ⟨⟨x, hx, hxK⟩, hz⟩).2
        ⟨x, ⟨hx, hn⟩, hxK⟩
    · obtain ⟨x, hx, hxK⟩ := hy.1
      exact ⟨x, mem_bandOpen_window.mpr ⟨y, hyU, hxK⟩, hx⟩
  · rintro ⟨hcl, x, hxU, hxI⟩
    have hsub : H ∩ (U : Set ℝ) ⊆ outSet0 ε I := by
      rintro y ⟨hy, hyU⟩
      rw [hout]
      refine ⟨hy, fun ⟨z, ⟨hz, hn⟩, hzK⟩ => ?_⟩
      exact hn (hcl ⟨hz, mem_bandOpen_window.mpr ⟨y, hyU, hzK⟩⟩)
    obtain ⟨y, hy, hxK⟩ := mem_bandOpen_window.mp hxU
    exact ⟨fun z hz => hsub ⟨closure_minimal hs hH hz.1, hz.2⟩,
      ⟨y, hy, hsub ⟨⟨x, subset_closure hxI, hxK⟩, hy⟩⟩⟩

private theorem ordConnected_outSet0 {I : Set ℝ} (hI : I.OrdConnected) (ε : ℝ) :
    (outSet0 ε I).OrdConnected := by
  rw [outSet0_eq_sdiff hI]
  have hH : (windowHits ε (closure I)).OrdConnected := by
    rw [windowHits_eq_add, ← convex_iff_ordConnected]
    exact (convex_iff_ordConnected.2 hI).closure.add (convex_Icc _ _)
  refine ⟨fun ⦃a⦄ ha ⦃b⦄ hb y hy => ⟨hH.out ha.1 hb.1 hy, ?_⟩⟩
  rintro ⟨c, ⟨hc, hcI⟩, hcK⟩
  have hside : (∀ x ∈ closure I, c ≤ x) ∨ (∀ x ∈ closure I, x ≤ c) := by
    by_contra! hn
    obtain ⟨⟨l, hl, hlc⟩, r, hr, hcr⟩ := hn
    exact hcI ((convex_iff_ordConnected.2 hI).Ioo_subset_of_mem_closure hl hr ⟨hlc, hcr⟩)
  rcases hside with hlo | hhi
  · obtain ⟨z, hz, hzK⟩ := ha.1
    exact ha.2 ⟨c, ⟨hc, hcI⟩, ⟨by linarith [hy.1, hcK.1], (hlo z hz).trans hzK.2⟩⟩
  · obtain ⟨z, hz, hzK⟩ := hb.1
    exact hb.2 ⟨c, ⟨hc, hcI⟩, ⟨hzK.1.trans (hhi z hz), by linarith [hy.2, hcK.2]⟩⟩

/-- The union of the input breakpoints shifted by `−ε` and `+ε`. -/
noncomputable def bandBreakpoints {m : ℕ} (p : Fin m → ℝ) (ε : ℝ) : Finset ℝ :=
  (breakpoints p).image (· - ε) ∪ (breakpoints p).image (· + ε)

private theorem stratum_translate {m n : ℕ} {p : Fin m → ℝ} {q : Fin n → ℝ} {d : ℝ}
    (hsub : ∀ i, p i - d ∈ breakpoints q) {v w} {x y : ℝ}
    (hx : x ∈ stratum q v) (hy : y ∈ stratum q v) (hw : x + d ∈ stratum p w) :
    y + d ∈ stratum p w := by
  have hc (i : Fin m) :
      (p i < x + d ↔ p i < y + d) ∧ (x + d < p i ↔ y + d < p i) ∧
        (x + d = p i ↔ y + d = p i) := by
    obtain ⟨j, hj⟩ := mem_breakpoints.mp (hsub i)
    rcases lt_trichotomy (2 * j.val + 1) v.val with h | h | h
    · have hx' := (hx.1 j).1 h
      have hy' := (hy.1 j).1 h
      rw [hj] at hx' hy'
      refine ⟨?_, ?_, ?_⟩ <;> constructor <;> intro <;> linarith
    · have hx' := hx.2 j h.symm
      have hy' := hy.2 j h.symm
      rw [hj] at hx' hy'
      rw [show x = y by linarith]
      simp
    · have hx' := (hx.1 j).2 h
      have hy' := (hy.1 j).2 h
      rw [hj] at hx' hy'
      refine ⟨?_, ?_, ?_⟩ <;> constructor <;> intro <;> linarith
  exact ⟨fun i => ⟨fun h => (hc i).1.mp ((hw.1 i).1 h),
    fun h => (hc i).2.1.mp ((hw.1 i).2 h)⟩, fun i h => (hc i).2.2.mp (hw.2 i h)⟩

private theorem mem_windowHits_congr {m : ℕ} {p : Fin m → ℝ}
    (hp : StrictMono p) {S : Set ℝ}
    (hs : ∀ ⦃v x y⦄, x ∈ stratum p v → y ∈ stratum p v → x ∈ S → y ∈ S)
    {ε x y : ℝ} (hε : 0 ≤ ε) {v w}
    (hl : x - ε ∈ stratum p v) (hl' : y - ε ∈ stratum p v)
    (hu : x + ε ∈ stratum p w) (hu' : y + ε ∈ stratum p w) :
    x ∈ windowHits ε S ↔ y ∈ windowHits ε S := by
  have transfer {a b : ℝ} (hal : a - ε ∈ stratum p v) (hbl : b - ε ∈ stratum p v)
      (hau : a + ε ∈ stratum p w) (hbu : b + ε ∈ stratum p w)
      (ha : a ∈ windowHits ε S) : b ∈ windowHits ε S := by
    obtain ⟨z, hz, hza⟩ := ha
    obtain ⟨t, hzt⟩ := exists_mem_stratum hp z
    rcases lt_trichotomy t v with h | rfl | h
    · exact (not_lt_of_ge hza.1 (lt_of_mem_stratum hzt hal h)).elim
    · exact ⟨b - ε, hs hzt hbl hz, ⟨le_rfl, by linarith⟩⟩
    rcases lt_trichotomy t w with h' | rfl | h'
    · exact ⟨z, hz, ⟨(lt_of_mem_stratum hbl hzt h).le, (lt_of_mem_stratum hzt hbu h').le⟩⟩
    · exact ⟨b + ε, hs hzt hbu hz, ⟨by linarith, le_rfl⟩⟩
    · exact (not_lt_of_ge hza.2 (lt_of_mem_stratum hau hzt h')).elim
  exact ⟨transfer hl hl' hu hu', transfer hl' hl hu' hu⟩

private theorem closure_intervalSet_stratum {m : ℕ} {p : Fin m → ℝ}
    (J : FiniteInterval (2 * m + 1)) {v x y}
    (hx : x ∈ stratum p v) (hy : y ∈ stratum p v)
    (hc : x ∈ closure (intervalSet p J)) : y ∈ closure (intervalSet p J) := by
  rcases Nat.even_or_odd' v.val with ⟨j, hj | hj⟩
  · have ho : IsOpen (stratum p v) := by
      rw [stratum_of_even (show v.val % 2 = 0 by omega)]
      exact (star p v).isOpen
    obtain ⟨z, hz, hzI⟩ := mem_closure_iff.1 hc _ ho hx
    exact subset_closure ((mem_intervalSet_iff_alive hy).2 ((mem_intervalSet_iff_alive hz).1 hzI))
  · let i : Fin m := ⟨j, by have := v.isLt; omega⟩
    exact (hx.2 i hj).trans (hy.2 i hj).symm ▸ hc

private theorem outSet0_stratum {m : ℕ} {p : Fin m → ℝ} (hp : StrictMono p)
    (J : FiniteInterval (2 * m + 1)) {ε : ℝ} (hε : 0 ≤ ε)
    {v x y} (hx : x ∈ stratum (sortedBreakpoints (bandBreakpoints p ε)) v)
    (hy : y ∈ stratum (sortedBreakpoints (bandBreakpoints p ε)) v)
    (hout : x ∈ outSet0 ε (intervalSet p J)) :
    y ∈ outSet0 ε (intervalSet p J) := by
  have hminus (i : Fin m) : p i - (-ε) ∈
      breakpoints (sortedBreakpoints (bandBreakpoints p ε)) := by
    rw [breakpoints_sortedBreakpoints, sub_neg_eq_add]
    exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ (apply_mem_breakpoints p i))
  have hplus (i : Fin m) : p i - ε ∈
      breakpoints (sortedBreakpoints (bandBreakpoints p ε)) := by
    rw [breakpoints_sortedBreakpoints]
    exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ (apply_mem_breakpoints p i))
  obtain ⟨l, hl⟩ := exists_mem_stratum hp (x - ε)
  obtain ⟨u, hu⟩ := exists_mem_stratum hp (x + ε)
  have hl' : y - ε ∈ stratum p l := by
    simpa only [sub_eq_add_neg] using
      stratum_translate hminus hx hy (show x + (-ε) ∈ stratum p l from hl)
  have hu' := stratum_translate hplus hx hy hu
  rw [outSet0_eq_sdiff (ordConnected_intervalSet hp J)] at hout ⊢
  refine ⟨(mem_windowHits_congr hp (fun ⦃_ _ _⦄ => closure_intervalSet_stratum J)
    hε hl hl' hu hu').1 hout.1, ?_⟩
  refine mt (mem_windowHits_congr hp ?_ hε hl hl' hu hu').2 hout.2
  intro w a b ha hb hab
  exact ⟨closure_intervalSet_stratum J ha hb hab.1,
    fun h => hab.2 ((mem_intervalSet_iff_alive ha).2 ((mem_intervalSet_iff_alive hb).1 h))⟩

/-- A nonempty degree-zero output is an interval on the shifted breakpoint stratification. -/
theorem exists_intervalSet_outSet0 {m : ℕ} {p : Fin m → ℝ} (hp : StrictMono p)
    (J : FiniteInterval (2 * m + 1)) {ε : ℝ} (hε : 0 ≤ ε)
    (hne : (outSet0 ε (intervalSet p J)).Nonempty) :
    ∃ K : FiniteInterval (2 * (bandBreakpoints p ε).card + 1),
      intervalSet (sortedBreakpoints (bandBreakpoints p ε)) K = outSet0 ε (intervalSet p J) :=
  exists_intervalSet_of_strata (strictMono_sortedBreakpoints _)
    (ordConnected_outSet0 (ordConnected_intervalSet hp J) ε) hne
    (fun ⦃_ _ _⦄ hx hy hout => outSet0_stratum hp J hε hx hy hout)

private theorem windowHits_Icc {ε a b : ℝ} (hε : 0 ≤ ε) (hab : a ≤ b) :
    windowHits ε (Set.Icc a b) = Set.Icc (a - ε) (b + ε) := by
  ext y
  change (∃ x, (a ≤ x ∧ x ≤ b) ∧ (y - ε ≤ x ∧ x ≤ y + ε)) ↔
    a - ε ≤ y ∧ y ≤ b + ε
  constructor
  · rintro ⟨x, ⟨ha, hb⟩, hl, hu⟩
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨hl, hu⟩
    exact ⟨max a (y - ε), ⟨le_max_left .., max_le hab (by linarith)⟩,
      ⟨le_max_right .., max_le (by linarith) (by linarith)⟩⟩

private theorem windowHits_Ici {ε a : ℝ} (hε : 0 ≤ ε) :
    windowHits ε (Set.Ici a) = Set.Ici (a - ε) := by
  ext y
  change (∃ x, a ≤ x ∧ (y - ε ≤ x ∧ x ≤ y + ε)) ↔ a - ε ≤ y
  constructor
  · rintro ⟨x, hx, hl, hu⟩
    linarith
  · intro hy
    exact ⟨y + ε, by linarith, by linarith, le_rfl⟩

private theorem windowHits_Iic {ε b : ℝ} (hε : 0 ≤ ε) :
    windowHits ε (Set.Iic b) = Set.Iic (b + ε) := by
  ext y
  change (∃ x, x ≤ b ∧ (y - ε ≤ x ∧ x ≤ y + ε)) ↔ y ≤ b + ε
  constructor
  · rintro ⟨x, hx, hl, hu⟩
    linarith
  · intro hy
    exact ⟨y - ε, by linarith, le_rfl, by linarith⟩

private theorem windowHits_singleton (ε a : ℝ) :
    windowHits ε {a} = Set.Icc (a - ε) (a + ε) := by
  ext y
  change (∃ x, x = a ∧ (y - ε ≤ x ∧ x ≤ y + ε)) ↔ a - ε ≤ y ∧ y ≤ a + ε
  simp only [exists_eq_left]
  constructor <;> rintro ⟨hl, hu⟩ <;> exact ⟨by linarith, by linarith⟩

private theorem outSet0_closed {I : Set ℝ} (hI : I.OrdConnected) (h : IsClosed I) (ε : ℝ) :
    outSet0 ε I = windowHits ε I := by
  have he : windowHits ε ∅ = ∅ := by ext; simp [windowHits]
  rw [outSet0_eq_sdiff hI, h.closure_eq, Set.sdiff_self, he, Set.sdiff_empty]

/-- A closed bounded interval expands at both ends. -/
theorem outSet0_Icc {ε a b : ℝ} (hε : 0 ≤ ε) (hab : a ≤ b) :
    outSet0 ε (Set.Icc a b) = Set.Icc (a - ε) (b + ε) := by
  rw [outSet0_closed Set.ordConnected_Icc isClosed_Icc, windowHits_Icc hε hab]

/-- A singleton expands to the closed window about that point. -/
theorem outSet0_singleton {ε : ℝ} (hε : 0 ≤ ε) (a : ℝ) :
    outSet0 ε {a} = Set.Icc (a - ε) (a + ε) := by
  rw [← Set.Icc_self, outSet0_Icc hε le_rfl]

/-- A half-open interval closed on the left translates to the left. -/
theorem outSet0_Ico {ε a b : ℝ} (hε : 0 ≤ ε) (hab : a < b) :
    outSet0 ε (Set.Ico a b) = Set.Ico (a - ε) (b - ε) := by
  have hb : Set.Icc a b \ Set.Ico a b = {b} := by
    ext x
    simp only [Set.mem_sdiff, Set.mem_Icc, Set.mem_Ico, Set.mem_singleton_iff]
    grind
  rw [outSet0_eq_sdiff Set.ordConnected_Ico, closure_Ico hab.ne, hb,
    windowHits_Icc hε hab.le, windowHits_singleton]
  ext x
  simp only [Set.mem_sdiff, Set.mem_Icc, Set.mem_Ico]
  grind

/-- A half-open interval closed on the right translates to the right. -/
theorem outSet0_Ioc {ε a b : ℝ} (hε : 0 ≤ ε) (hab : a < b) :
    outSet0 ε (Set.Ioc a b) = Set.Ioc (a + ε) (b + ε) := by
  have ha : Set.Icc a b \ Set.Ioc a b = {a} := by
    ext x
    simp only [Set.mem_sdiff, Set.mem_Icc, Set.mem_Ioc, Set.mem_singleton_iff]
    grind
  rw [outSet0_eq_sdiff Set.ordConnected_Ioc, closure_Ioc hab.ne, ha,
    windowHits_Icc hε hab.le, windowHits_singleton]
  ext x
  simp only [Set.mem_sdiff, Set.mem_Icc, Set.mem_Ioc]
  grind

/-- An open bounded interval shrinks at both ends, and is empty at or beyond the threshold. -/
theorem outSet0_Ioo {ε a b : ℝ} (hε : 0 ≤ ε) (hab : a < b) :
    outSet0 ε (Set.Ioo a b) = Set.Ioo (a + ε) (b - ε) := by
  have hends : Set.Icc a b \ Set.Ioo a b = {a} ∪ {b} := by
    ext x
    simp only [Set.mem_sdiff, Set.mem_Icc, Set.mem_Ioo, Set.mem_union, Set.mem_singleton_iff]
    grind
  have hunion : windowHits ε ({a} ∪ {b}) = windowHits ε {a} ∪ windowHits ε {b} := by
    ext x
    simp only [windowHits, Set.mem_ofPred_eq, Set.mem_union, or_and_right, exists_or]
  rw [outSet0_eq_sdiff Set.ordConnected_Ioo, closure_Ioo hab.ne, hends, hunion,
    windowHits_Icc hε hab.le, windowHits_singleton, windowHits_singleton]
  ext x
  simp only [Set.mem_sdiff, Set.mem_union, Set.mem_Icc, Set.mem_Ioo]
  grind

/-- A closed right ray expands to the left. -/
theorem outSet0_Ici {ε : ℝ} (hε : 0 ≤ ε) (a : ℝ) :
    outSet0 ε (Set.Ici a) = Set.Ici (a - ε) := by
  rw [outSet0_closed Set.ordConnected_Ici isClosed_Ici, windowHits_Ici hε]

/-- A closed left ray expands to the right. -/
theorem outSet0_Iic {ε : ℝ} (hε : 0 ≤ ε) (b : ℝ) :
    outSet0 ε (Set.Iic b) = Set.Iic (b + ε) := by
  rw [outSet0_closed Set.ordConnected_Iic isClosed_Iic, windowHits_Iic hε]

/-- An open right ray shrinks from the left. -/
theorem outSet0_Ioi {ε : ℝ} (hε : 0 ≤ ε) (a : ℝ) :
    outSet0 ε (Set.Ioi a) = Set.Ioi (a + ε) := by
  rw [outSet0_eq_sdiff Set.ordConnected_Ioi, closure_Ioi, Set.Ici_sdiff_Ioi_same,
    windowHits_Ici hε, windowHits_singleton]
  ext x
  simp only [Set.mem_sdiff, Set.mem_Icc, Set.mem_Ici, Set.mem_Ioi]
  grind

/-- An open left ray shrinks from the right. -/
theorem outSet0_Iio {ε : ℝ} (hε : 0 ≤ ε) (b : ℝ) :
    outSet0 ε (Set.Iio b) = Set.Iio (b - ε) := by
  rw [outSet0_eq_sdiff Set.ordConnected_Iio, closure_Iio, Set.Iic_sdiff_Iio_same,
    windowHits_Iic hε, windowHits_singleton]
  ext x
  simp only [Set.mem_sdiff, Set.mem_Icc, Set.mem_Iic, Set.mem_Iio]
  grind

/-- The whole line is invariant under the degree-zero calculation. -/
theorem outSet0_univ {ε : ℝ} (hε : 0 ≤ ε) :
    outSet0 ε Set.univ = Set.univ := by
  rw [outSet0_closed Set.ordConnected_univ isClosed_univ]
  exact Set.eq_univ_of_forall fun y => ⟨y, Set.mem_univ _, ⟨by linarith, by linarith⟩⟩


section Sheaf

open DerivedCategory ZeroObject

variable {k : Type} [Field k] [HasDerivedCategory (realLine.Sheaf (ModuleCat k))]
  [∀ a : ℝ, HasDerivedCategory ((D a).Sheaf (ModuleCat k))]

local notation "H₀[" k "," ε "]" =>
  (Plus.singleFunctor _ 0 ⋙ T k ε ⋙ Plus.homologyFunctor _ 0)

/-- The degree-zero section isomorphisms commute with restriction of order-connected opens. -/
@[reassoc]
theorem H0TSectionsIso_hom_map {ε : ℝ} (_hε : 0 ≤ ε) (F : realLine.Sheaf (ModuleCat k))
    {V U : Opens realLine} (h : V ≤ U) (hV : (V : Set ℝ).OrdConnected)
    (hU : (U : Set ℝ).OrdConnected) :
    ((H₀[k, ε]).obj F).presheaf.map (homOfLE h).op ≫ (H0TSectionsIso k ε F V hV).hom =
      (H0TSectionsIso k ε F U hU).hom ≫
        F.presheaf.map (homOfLE (bandOpen_mono_right ε h)).op := by
  let e := ((H0TIso k ε).app F).hom.hom
  change _ ≫ e.app (op V) ≫ _ = (e.app (op U) ≫ _) ≫ _
  calc
    _ = e.app (op U) ≫ ((thickening k ε).obj F).presheaf.map (homOfLE h).op ≫
        (thickeningSectionsIso k ε F V hV).hom := by
      simpa only [Category.assoc] using congrArg
        (fun f => f ≫ (thickeningSectionsIso k ε F V hV).hom) (e.naturality (homOfLE h).op)
    _ = _ := by rw [thickeningSectionsIso_hom_map, Category.assoc]

variable {m : ℕ} {p : Fin m → ℝ} (hp : StrictMono p) (J : FiniteInterval (2 * m + 1))
  {ε : ℝ} (hε : 0 ≤ ε)

local notation "ISh[" k "," hp "," J "]" => Functor.obj (extension k hp) (interval _ J)

include hε

/-- If the output set is an interval set for a given stratification, degree-zero convolution
is isomorphic to the interval sheaf of that interval. -/
theorem nonempty_iso_H0T_interval {n : ℕ} {q : Fin n → ℝ} (hq : StrictMono q)
    (K : FiniteInterval (2 * n + 1)) (hK : intervalSet q K = outSet0 ε (intervalSet p J)) :
    Nonempty ((H₀[k, ε]).obj (ISh[k, hp, J]) ≅
      (extension k hq).obj (interval (orient n) K)) := by
  have good {U : Opens realLine} (hU : (U : Set ℝ).OrdConnected) :
      MeetsClosed (intervalSet q K) U ↔ MeetsClosed (intervalSet p J) (bandOpen ε U) :=
    hK.symm ▸ meetsClosed_outSet0_iff hε (ordConnected_intervalSet hp J)
      (isLocallyClosed_intervalSet hp J) hU
  refine nonempty_iso_extension_interval_of_sections hq _ K ?_ ?_ ?_
  · intro U hU h
    obtain ⟨x, hx, hxI⟩ := ((good hU.2.1).1 h).2
    have hg := isIso_germ_extension_interval k hp J (ordConnected_bandOpen ε hU.2.1)
      ((good hU.2.1).1 h).1 hx hxI
    exact ⟨H0TSectionsIso k ε (ISh[k, hp, J]) U hU.2.1 ≪≫
      asIso ((ISh[k, hp, J]).presheaf.germ (bandOpen ε U) x hx) ≪≫
      (nonempty_stalk_extension_interval_iso k hp hxI).some⟩
  · intro U hU h
    exact (isZero_sections_extension_interval k hp J (ordConnected_bandOpen ε hU.2.1)
      (mt (good hU.2.1).2 h)).of_iso (H0TSectionsIso k ε (ISh[k, hp, J]) U hU.2.1)
  · intro V U h hV hU hv hu
    have hv' := (good hV.2.1).1 hv
    have hu' := (good hU.2.1).1 hu
    obtain ⟨x, hx, hxI⟩ := hv'.2
    have := isIso_map_extension_interval k hp J (bandOpen_mono_right ε h)
      (ordConnected_bandOpen ε hV.2.1) (ordConnected_bandOpen ε hU.2.1) hv'.1 hu'.1 hx hxI
    have hcomp : IsIso (((H₀[k, ε]).obj (ISh[k, hp, J])).presheaf.map (homOfLE h).op ≫
        (H0TSectionsIso k ε (ISh[k, hp, J]) V hV.2.1).hom) := by
      rw [H0TSectionsIso_hom_map hε (ISh[k, hp, J]) h hV.2.1 hU.2.1]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (H0TSectionsIso k ε (ISh[k, hp, J]) V hV.2.1).hom

/-- A nonempty degree-zero output yields an interval sheaf on the shifted stratification. -/
theorem exists_intervalSheaf_H0T (hne : (outSet0 ε (intervalSet p J)).Nonempty) :
    ∃ K : FiniteInterval (2 * (bandBreakpoints p ε).card + 1),
      intervalSet (sortedBreakpoints (bandBreakpoints p ε)) K = outSet0 ε (intervalSet p J) ∧
        Nonempty (((H₀[k, ε]).obj (ISh[k, hp, J])) ≅
          (extension k (strictMono_sortedBreakpoints _)).obj
            (interval (orient (bandBreakpoints p ε).card) K)) := by
  obtain ⟨K, hK⟩ := exists_intervalSet_outSet0 hp J hε hne
  exact ⟨K, hK, nonempty_iso_H0T_interval hp J hε (strictMono_sortedBreakpoints _) K hK⟩

/-- An empty degree-zero output gives the zero sheaf. -/
theorem isZero_H0T_interval (he : outSet0 ε (intervalSet p J) = ∅) :
    IsZero ((H₀[k, ε]).obj (ISh[k, hp, J])) := by
  let G := (H₀[k, ε]).obj (ISh[k, hp, J])
  have hi : IsIso (0 : G ⟶ 0) :=
    TopCat.Sheaf.isIso_iff_isIso_basis (isBasis_range_basicOpen (breakpoints p)) (fun U => by
      have hn : ¬ MeetsClosed (outSet0 ε (intervalSet p J)) U.1 := by simp [he, MeetsClosed]
      have hz := isZero_sections_extension_interval k hp J (ordConnected_bandOpen ε U.2.2.1)
        (mt (meetsClosed_outSet0_iff hε (ordConnected_intervalSet hp J)
          (isLocallyClosed_intervalSet hp J) U.2.2.1).2 hn)
      exact (hz.of_iso (H0TSectionsIso k ε (ISh[k, hp, J]) U.1 U.2.2.1)).isIso
        ((sheafToPresheaf _ _ ⋙ (evaluation _ _).obj (op U.1)).map_isZero (isZero_zero _)) _)
  exact (isZero_zero _).of_iso (asIso (0 : G ⟶ 0))

/-- Degree-zero convolution of an interval sheaf is constructible for the shifted breakpoints. -/
theorem isConstructible_H0T_interval :
    IsConstructible (bandBreakpoints p ε) ((H₀[k, ε]).obj (ISh[k, hp, J])) := by
  rcases (outSet0 ε (intervalSet p J)).eq_empty_or_nonempty with he | hn
  · rw [← breakpoints_sortedBreakpoints (bandBreakpoints p ε)]
    exact isConstructible_of_isZero k (strictMono_sortedBreakpoints _)
      (isZero_H0T_interval hp J hε he)
  · obtain ⟨K, _, ⟨e⟩⟩ := exists_intervalSheaf_H0T (k := k) hp J hε hn
    rw [← breakpoints_sortedBreakpoints (bandBreakpoints p ε)]
    exact isConstructible_of_iso e.symm
      (isConstructible_extension k (strictMono_sortedBreakpoints _) fun _ => inferInstance)

end Sheaf

end TDA.Sheaf.BandConvolution
