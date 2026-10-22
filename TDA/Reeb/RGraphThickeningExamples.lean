import TDA.Reeb.RGraphThickening
import TDA.Reeb.ConstructibleSpaceExamples
import TDA.Reeb.RGraphExamples
import TDA.Reeb.ConstructibleRepresentationExamples

/-!
# Fixtures for constructible graph thickenings

Acceptance fixtures for `TDA.Reeb.RGraphWindow` and `TDA.Reeb.RGraphThickening`, on realizations, windows, thickening presentations and slice thickenings:

* **Window gluing on the parallel-edge loop.** In the window `[-1/2, 1/2]` both parallel fragments
  are glued to the common lower vertex, and their interior points at parameter `1/4` stay
  distinct. In the window `[-1/2, 3/2]`, which contains both common endpoints, both whole edges are
  glued to the lower and to the upper vertex. The windows are compact, Hausdorff and locally
  path-connected.
* **Endpoint collapse.** At `ε = 1`, the left attaching map of the first gap of the thickened loop
  sends two distinct interior points of the two parallel edges to the common vertex, so it is not
  injective. This is a two-incident-edge attachment.
* **A window touching a vertex.** The window `[1, 3/2]` meets each edge in the point fragment `{1}`,
  which is glued to the upper vertex, so the window is a single point.
* **A window containing no old level.** The window `[1/4, 3/4]` has no window vertex; the edge
  label descends along the window quotient, so the window is not preconnected.
* **The empty graph.** Its thickening and the realization of its thickening presentation are empty,
  for every `ε`, and the thickening is constructible.
* **A singleton at an arbitrary height `a`.** The thickening is the closed segment `[-ε, ε]` with
  height `a + t`; for `ε > 0`, every strip point of its thickening presentation at height `t` has
  band coordinate `t - a`.
* **`ε = 0`.** The lift at `ε = 0`, followed by the inclusion of constructible spaces, is
  isomorphic to the inclusion of graph objects, by the merged zero isomorphism.
* **A single edge.** At `ε = 1`, on the first gap, a strip point at height `t` over an edge point
  of parameter `s` lies over the edge point of height `s (t + 1) / (mid + 1)`, a linear stretch of
  an edge that crosses one window end.
* **Disjoint edges.** For two disjoint segments, the left attaching map of the same gap keeps the
  two segments' points apart, and the thickening is not preconnected for every `ε`.
* **A shifted-level collision.** For `0 < 1` at `ε = 1/2`, the shifts `0 + ε = 1 - ε` merge, so the
  witness has three levels `-1/2`, `1/2`, `3/2`. The vertex piece at the collision level is the
  whole single edge, and the right attaching map of the first gap sends the upper end `c + ε` of
  the edge fragment at the midpoint `c = 0` to the upper vertex.
* **The bundled lift** on the parallel-edge loop has underlying object the thickening.
-/

open Set Topology CategoryTheory
open scoped NNReal

namespace TDA.Reeb

noncomputable section

namespace Examples.RGraphThickening

open RGraph CylinderPresentation
open TDA.Reeb.Examples.Cylinder (S01 S01_value_zero S01_value_one parallelData emptyData
  emptyData_isEmpty twoSegData twoSegLabel)
open TDA.Reeb.RGraph.Examples (singleEdge)
open TDA.Reeb.Examples.ConstructibleRepresentation (pt0)

/-! ### The window bridge on the parallel-edge loop -/

/-- The window `[-1/2, 1/2]` of the two-parallel-edge loop over `0 < 1`. -/
abbrev pw := window S01 parallelData (-1 / 2) (1 / 2)

theorem pw_compactSpace : CompactSpace pw := inferInstance
theorem pw_t2Space : T2Space pw := inferInstance
theorem pw_locallyPathConnectedSpace : LocallyPathConnectedSpace pw := inferInstance

theorem zero_mem_frag : (0 : ℝ) ∈ frag S01 0 (-1 / 2) (1 / 2) := by
  norm_num [frag]

theorem quarter_mem_frag : (1 / 4 : ℝ) ∈ frag S01 0 (-1 / 2) (1 / 2) := by
  norm_num [frag]

/-- The fragment of edge `b` at parameter `s`. -/
def pwEdge (b : Bool) (s : frag S01 0 (-1 / 2) (1 / 2)) :
    WindowRaw S01 parallelData (-1 / 2) (1 / 2) :=
  .inr ⟨⟨0, b⟩, s⟩

/-- The common lower vertex as a raw window vertex. -/
def pwVertex : WindowRaw S01 parallelData (-1 / 2) (1 / 2) :=
  .inl ⟨⟨0, ()⟩, by norm_num⟩

/-- **Genuine gluing.** Both parallel fragments are glued to the common vertex at their lower
ends. -/
theorem pw_glued (b : Bool) :
    windowCover S01 parallelData _ _ (pwEdge b ⟨0, zero_mem_frag⟩) =
      windowCover S01 parallelData _ _ pwVertex := by
  refine Subtype.ext ?_
  have hs : (⟨0, frag_subset_seg zero_mem_frag⟩ : Seg S01 0) = segBot S01 0 :=
    Subtype.ext (by simp [segBot])
  change (ofFiniteData parallelData).ofCylinder S01 0 (b, ⟨0, frag_subset_seg zero_mem_frag⟩) =
    (ofFiniteData parallelData).ofVertex S01 0 ()
  rw [hs]
  exact (ofFiniteData parallelData).ofCylinder_segBot S01 0 b

/-- The interior points at parameter `1/4` of the two parallel fragments stay distinct. -/
theorem pw_separate :
    windowCover S01 parallelData _ _ (pwEdge false ⟨1 / 4, quarter_mem_frag⟩) ≠
      windowCover S01 parallelData _ _ (pwEdge true ⟨1 / 4, quarter_mem_frag⟩) := by
  intro h
  have ht : (1 / 4 : ℝ) ∈ (S01.K 0 : Set ℝ) :=
    ⟨by rw [Fin.castSucc_zero, S01_value_zero]; norm_num,
      by rw [Fin.succ_zero_eq_one, S01_value_one]; norm_num⟩
  have h' : (ofFiniteData parallelData).ofStrip S01 0 (false, ⟨_, ht⟩) =
      (ofFiniteData parallelData).ofStrip S01 0 (true, ⟨_, ht⟩) :=
    congrArg Subtype.val h
  exact Bool.false_ne_true
    (congrArg Prod.fst ((ofFiniteData parallelData).ofStrip_injective S01 0 h'))

/-! ### Endpoint collapse in the thickening presentation -/

theorem S01_shifted_zero : (S01.shifted 1).value 0 = -1 := by
  rw [S01.shifted_value_zero, S01_value_zero, NNReal.coe_one]
  norm_num

theorem S01_shiftedCount_pos : 0 < S01.shiftedCount 1 := by
  have h1 : (-1 : ℝ) ∈ S01.shiftedSet 1 := by
    have := S01.sub_mem_shiftedSet 1 0
    rwa [S01_value_zero, NNReal.coe_one, zero_sub] at this
  have h2 : (2 : ℝ) ∈ S01.shiftedSet 1 := by
    have := S01.add_mem_shiftedSet 1 1
    rw [S01_value_one, NNReal.coe_one] at this
    norm_num at this
    exact this
  have hc : 1 < (S01.shiftedSet 1).card := Finset.one_lt_card.2 ⟨_, h1, _, h2, by norm_num⟩
  have := S01.card_shiftedSet 1
  omega

/-- The first gap `[b 0, b 1] = [-1, b 1]` of the shifted witness of `S01` at `ε = 1`. -/
def k0 : Fin (S01.shiftedCount 1) := ⟨0, S01_shiftedCount_pos⟩

theorem k0_castSucc : (k0.castSucc : Fin (S01.shiftedCount 1 + 1)) = 0 :=
  Fin.ext (by simp [k0])

theorem coe_segBot_k0 : ((segBot (S01.shifted 1) k0 : Seg (S01.shifted 1) k0) : ℝ) = -1 := by
  rw [show ((segBot (S01.shifted 1) k0 : Seg (S01.shifted 1) k0) : ℝ) =
    (S01.shifted 1).value k0.castSucc from rfl, k0_castSucc, S01_shifted_zero]

/-- The second shifted level is at most `0`, the shifted level `1 - 1`. -/
theorem S01_shifted_one_le : (S01.shifted 1).value k0.succ ≤ 0 := by
  obtain ⟨j, hj⟩ := S01.exists_shifted_value_eq_sub 1 1
  rw [S01_value_one, NNReal.coe_one, sub_self] at hj
  have hj0 : j ≠ 0 := by
    rintro rfl
    rw [S01_shifted_zero] at hj
    norm_num at hj
  have hjv : j.val ≠ 0 := fun h => hj0 (Fin.ext (by simpa using h))
  have hle : k0.succ ≤ j := by
    rw [Fin.le_def, Fin.val_succ]
    show 0 + 1 ≤ j.val
    omega
  exact ((S01.shifted 1).strictMono.monotone hle).trans_eq hj

theorem mid_k0_bounds : -1 < mid S01 1 k0 ∧ mid S01 1 k0 < 0 := by
  have h := mid_mem_K S01 1 k0
  have h1 : (S01.shifted 1).value k0.castSucc < mid S01 1 k0 := h.1
  have h2 : mid S01 1 k0 < (S01.shifted 1).value k0.succ := h.2
  rw [k0_castSucc, S01_shifted_zero] at h1
  exact ⟨h1, h2.trans_le S01_shifted_one_le⟩

theorem s0_mem : (mid S01 1 k0 + 1) / 2 ∈
    frag S01 0 (mid S01 1 k0 - ((1 : ℝ≥0) : ℝ)) (mid S01 1 k0 + ((1 : ℝ≥0) : ℝ)) := by
  have hb := mid_k0_bounds
  rw [NNReal.coe_one]
  simp only [frag, Fin.castSucc_zero, Fin.succ_zero_eq_one, S01_value_zero, S01_value_one]
  exact ⟨max_le (by linarith [hb.1]) (by linarith [hb.2]),
    le_min (by linarith [hb.2]) (by linarith [hb.1])⟩

/-- The interior point of parameter `(mid + 1) / 2` on parallel edge `b`, a point of the edge
piece of gap `k0`. -/
def collapsePt (b : Bool) : win S01 parallelData 1 (mid S01 1 k0) :=
  ⟨(ofFiniteData parallelData).ofCylinder S01 0 (b, ⟨_, frag_subset_seg s0_mem⟩),
    frag_subset_Icc s0_mem⟩

theorem collapsePt_ne : collapsePt false ≠ collapsePt true := by
  intro h
  have hb := mid_k0_bounds
  have ht : (mid S01 1 k0 + 1) / 2 ∈ (S01.K 0 : Set ℝ) :=
    ⟨by rw [Fin.castSucc_zero, S01_value_zero]; linarith [hb.1],
      by rw [Fin.succ_zero_eq_one, S01_value_one]; linarith [hb.2]⟩
  have h' : (ofFiniteData parallelData).ofStrip S01 0 (false, ⟨_, ht⟩) =
      (ofFiniteData parallelData).ofStrip S01 0 (true, ⟨_, ht⟩) :=
    congrArg Subtype.val h
  exact Bool.false_ne_true
    (congrArg Prod.fst ((ofFiniteData parallelData).ofStrip_injective S01 0 h'))

/-- The left attaching map of gap `k0` sends both interior points to the common vertex:
the window at `b 0 = -1` meets each edge only at that vertex, so both fragments collapse onto
it. -/
theorem left_collapse_apply (b : Bool) :
    ((thickPresentation S01 parallelData 1).left k0 (collapsePt b)).1 =
      (ofFiniteData parallelData).ofVertex S01 0 () := by
  have hok := transferOK_of_mem S01 1 (mid_mem_K S01 1 k0) (segBot (S01.shifted 1) k0).2
  change (windowTransfer S01 parallelData 1 hok (collapsePt b) :
    (ofFiniteData parallelData).Realization S01) = _
  rw [coe_windowTransfer_ofCylinder S01 parallelData 1 hok s0_mem (collapsePt b) (y := b) rfl]
  have hz : fragAff (S01.value (Fin.castSucc 0)) (S01.value (Fin.succ 0)) ((1 : ℝ≥0) : ℝ)
      (mid S01 1 k0) ((segBot (S01.shifted 1) k0 : Seg (S01.shifted 1) k0) : ℝ)
      ((mid S01 1 k0 + 1) / 2) = S01.value (Fin.castSucc 0) := by
    rw [fragAff_collapse]
    · rw [coe_segBot_k0, Fin.castSucc_zero, S01_value_zero, NNReal.coe_one]
      norm_num
    · rw [coe_segBot_k0, Fin.castSucc_zero, Fin.succ_zero_eq_one, S01_value_zero, S01_value_one,
        NNReal.coe_one]
      norm_num
  have hseg : (⟨_, frag_subset_seg (hok.fragAff_mem s0_mem)⟩ : Seg S01 0) = segBot S01 0 :=
    Subtype.ext hz
  rw [hseg]
  exact (ofFiniteData parallelData).ofCylinder_segBot S01 0 b

/-- **Nontrivial endpoint collapse.** Two distinct interior points of the parallel edges have the
same image under the left attaching map. -/
theorem left_collapse :
    (thickPresentation S01 parallelData 1).left k0 (collapsePt false) =
      (thickPresentation S01 parallelData 1).left k0 (collapsePt true) :=
  Subtype.ext ((left_collapse_apply false).trans (left_collapse_apply true).symm)

/-- The left attaching map of the presentation is not injective. -/
theorem left_not_injective :
    ¬ Function.Injective ((thickPresentation S01 parallelData 1).left k0) :=
  fun h => collapsePt_ne (h left_collapse)

/-- The thickened parallel-edge loop as an object of constructible ℝ-spaces, at `ε = 1`. -/
abbrev parallelThick : ConstructibleSpaceCat :=
  (thickeningToConstructible 1).obj ((toRGraph S01).obj parallelData)

theorem parallelThick_obj :
    parallelThick.obj = (GeometricThickening.functor 1).obj (toOver S01 parallelData) :=
  rfl

/-! ### Gluing at both common endpoints -/

/-- The window `[-1/2, 3/2]` of the two-parallel-edge loop, which contains both common
endpoints. -/
abbrev pwFull := window S01 parallelData (-1 / 2) (3 / 2)

theorem zero_mem_fragFull : (0 : ℝ) ∈ frag S01 0 (-1 / 2) (3 / 2) := by
  norm_num [frag]

theorem one_mem_fragFull : (1 : ℝ) ∈ frag S01 0 (-1 / 2) (3 / 2) := by
  norm_num [frag]

/-- The fragment of edge `b` of the window `[-1/2, 3/2]` at parameter `s`. -/
def pwFullEdge (b : Bool) (s : frag S01 0 (-1 / 2) (3 / 2)) :
    WindowRaw S01 parallelData (-1 / 2) (3 / 2) :=
  .inr ⟨⟨0, b⟩, s⟩

/-- The common lower vertex as a raw point of the window `[-1/2, 3/2]`. -/
def pwFullBot : WindowRaw S01 parallelData (-1 / 2) (3 / 2) :=
  .inl ⟨⟨0, ()⟩, by norm_num⟩

/-- The common upper vertex as a raw point of the window `[-1/2, 3/2]`. -/
def pwFullTop : WindowRaw S01 parallelData (-1 / 2) (3 / 2) :=
  .inl ⟨⟨1, ()⟩, by norm_num⟩

/-- **Gluing at the lower common endpoint.** Both parallel edges are glued to the lower vertex. -/
theorem pwFull_glued_bot (b : Bool) :
    windowCover S01 parallelData _ _ (pwFullEdge b ⟨0, zero_mem_fragFull⟩) =
      windowCover S01 parallelData _ _ pwFullBot := by
  refine Subtype.ext ?_
  have hs : (⟨0, frag_subset_seg zero_mem_fragFull⟩ : Seg S01 0) = segBot S01 0 :=
    Subtype.ext (by simp [segBot])
  change (ofFiniteData parallelData).ofCylinder S01 0
      (b, ⟨0, frag_subset_seg zero_mem_fragFull⟩) = (ofFiniteData parallelData).ofVertex S01 0 ()
  rw [hs]
  exact (ofFiniteData parallelData).ofCylinder_segBot S01 0 b

/-- **Gluing at the upper common endpoint.** Both parallel edges are glued to the upper vertex. -/
theorem pwFull_glued_top (b : Bool) :
    windowCover S01 parallelData _ _ (pwFullEdge b ⟨1, one_mem_fragFull⟩) =
      windowCover S01 parallelData _ _ pwFullTop := by
  refine Subtype.ext ?_
  have hs : (⟨1, frag_subset_seg one_mem_fragFull⟩ : Seg S01 0) = segTop S01 0 :=
    Subtype.ext (by simp [segTop])
  change (ofFiniteData parallelData).ofCylinder S01 0
      (b, ⟨1, frag_subset_seg one_mem_fragFull⟩) = (ofFiniteData parallelData).ofVertex S01 1 ()
  rw [hs]
  exact (ofFiniteData parallelData).ofCylinder_segTop S01 0 b

/-! ### A window touching a vertex -/

/-- The window `[1, 3/2]` of the parallel-edge loop, which touches the upper vertex at its lower
end. -/
abbrev pwTouch := window S01 parallelData 1 (3 / 2)

theorem one_mem_fragTouch : (1 : ℝ) ∈ frag S01 0 1 (3 / 2) := by
  norm_num [frag]

/-- The upper vertex as a raw point of the window `[1, 3/2]`. -/
def touchVertex : WindowRaw S01 parallelData 1 (3 / 2) :=
  .inl ⟨⟨1, ()⟩, by norm_num⟩

/-- **A point fragment at a vertex.** The fragment `{1}` of each parallel edge is glued to the
upper vertex. -/
theorem touch_glued (b : Bool) :
    windowCover S01 parallelData 1 (3 / 2) (.inr ⟨⟨0, b⟩, ⟨1, one_mem_fragTouch⟩⟩) =
      windowCover S01 parallelData 1 (3 / 2) touchVertex := by
  refine Subtype.ext ?_
  have hs : (⟨1, frag_subset_seg one_mem_fragTouch⟩ : Seg S01 0) = segTop S01 0 :=
    Subtype.ext (by simp [segTop])
  change (ofFiniteData parallelData).ofCylinder S01 0
      (b, ⟨1, frag_subset_seg one_mem_fragTouch⟩) = (ofFiniteData parallelData).ofVertex S01 1 ()
  rw [hs]
  exact (ofFiniteData parallelData).ofCylinder_segTop S01 0 b

/-- Every raw point of the window `[1, 3/2]` is glued to the upper vertex. -/
theorem touch_eq_vertex (r : WindowRaw S01 parallelData 1 (3 / 2)) :
    windowCover S01 parallelData 1 (3 / 2) r =
      windowCover S01 parallelData 1 (3 / 2) touchVertex := by
  rcases r with ⟨⟨i, v⟩, hi⟩ | ⟨⟨e, b⟩, s, hs⟩
  · obtain rfl : i = 1 := by
      have h1 : (1 : ℝ) ≤ ((i : ℕ) : ℝ) := hi.1
      have h2 := i.isLt
      have h3 := Nat.one_le_cast.1 h1
      exact Fin.ext (by simp only [Fin.val_one]; omega)
    rfl
  · obtain rfl : e = 0 := Fin.fin_one_eq_zero e
    have hs1 : s = 1 := le_antisymm
      (hs.2.trans ((min_le_left _ _).trans_eq (by simp)))
      ((le_max_right _ _).trans hs.1)
    subst hs1
    exact touch_glued b

/-- The window `[1, 3/2]` is the single upper vertex. -/
theorem pwTouch_subsingleton : Subsingleton pwTouch :=
  ⟨fun x y => by
    obtain ⟨r, rfl⟩ := windowCover_surjective S01 parallelData 1 (3 / 2) x
    obtain ⟨r', rfl⟩ := windowCover_surjective S01 parallelData 1 (3 / 2) y
    rw [touch_eq_vertex r, touch_eq_vertex r']⟩

/-! ### A window containing no old level -/

/-- The window `[1/4, 3/4]` of the parallel-edge loop, which contains no old level. -/
abbrev pwMid := window S01 parallelData (1 / 4) (3 / 4)

/-- The window `[1/4, 3/4]` has no window vertex. -/
theorem pwMid_isEmpty_V : IsEmpty (WindowV S01 parallelData (1 / 4) (3 / 4)) :=
  ⟨fun ⟨⟨i, _⟩, hi⟩ => by
    have h1 : (1 / 4 : ℝ) ≤ ((i : ℕ) : ℝ) := hi.1
    have h2 : ((i : ℕ) : ℝ) ≤ 3 / 4 := hi.2
    have hi2 := i.isLt
    have h : (i : ℕ) = 0 ∨ (i : ℕ) = 1 := by omega
    rcases h with h | h
    · rw [h] at h1
      norm_num at h1
    · rw [h] at h2
      norm_num at h2⟩

/-- The edge label on the raw points of the window `[1/4, 3/4]`. -/
def pwMidRawLabel : C(WindowRaw S01 parallelData (1 / 4) (3 / 4), Bool) where
  toFun := Sum.elim (fun v => (pwMid_isEmpty_V.false v).elim) fun q => q.1.2
  continuous_toFun := by
    refine Continuous.sumElim continuous_of_discreteTopology (continuous_sigma fun c => ?_)
    show Continuous fun _ => @id Bool c.2
    exact continuous_const

theorem pwMidRawLabel_factors :
    Function.FactorsThrough pwMidRawLabel (windowCover S01 parallelData (1 / 4) (3 / 4)) := by
  rintro (v | ⟨⟨e, b⟩, s, hs⟩) (v' | ⟨⟨e', b'⟩, s', hs'⟩) h
  · exact (pwMid_isEmpty_V.false v).elim
  · exact (pwMid_isEmpty_V.false v).elim
  · exact (pwMid_isEmpty_V.false v').elim
  · obtain rfl : e = 0 := Fin.fin_one_eq_zero e
    obtain rfl : e' = 0 := Fin.fin_one_eq_zero e'
    have hK : ∀ {r : ℝ}, r ∈ frag S01 0 (1 / 4) (3 / 4) → r ∈ (S01.K 0 : Set ℝ) := fun hr =>
      ⟨by rw [Fin.castSucc_zero, S01_value_zero]; linarith [(le_max_right _ _).trans hr.1],
        by rw [Fin.succ_zero_eq_one, S01_value_one]; linarith [hr.2.trans (min_le_right _ _)]⟩
    have h' : (ofFiniteData parallelData).ofStrip S01 0 (b, ⟨s, hK hs⟩) =
        (ofFiniteData parallelData).ofStrip S01 0 (b', ⟨s', hK hs'⟩) :=
      congrArg Subtype.val h
    have hb := congrArg Prod.fst ((ofFiniteData parallelData).ofStrip_injective S01 0 h')
    exact hb

/-- The edge label of the window `[1/4, 3/4]`, descended along the window quotient. -/
def pwMidLabel : C(pwMid, Bool) :=
  (isQuotientMap_windowCover S01 parallelData (1 / 4) (3 / 4)).lift pwMidRawLabel
    pwMidRawLabel_factors

theorem pwMidLabel_windowCover (r : WindowRaw S01 parallelData (1 / 4) (3 / 4)) :
    pwMidLabel (windowCover S01 parallelData _ _ r) = pwMidRawLabel r := by
  have := DFunLike.congr_fun (IsQuotientMap.lift_comp
    (isQuotientMap_windowCover S01 parallelData (1 / 4) (3 / 4)) pwMidRawLabel
    pwMidRawLabel_factors) r
  rw [ContinuousMap.comp_apply] at this
  exact this

theorem half_mem_fragMid : (1 / 2 : ℝ) ∈ frag S01 0 (1 / 4) (3 / 4) := by
  norm_num [frag]

/-- **A window without old levels.** The window `[1/4, 3/4]` is not preconnected: its edge label
is continuous and takes both values. -/
theorem pwMid_not_preconnected : ¬ PreconnectedSpace pwMid := fun h => by
  have := PreconnectedSpace.constant h pwMidLabel.continuous
    (x := windowCover S01 parallelData _ _ (.inr ⟨⟨0, false⟩, ⟨1 / 2, half_mem_fragMid⟩⟩))
    (y := windowCover S01 parallelData _ _ (.inr ⟨⟨0, true⟩, ⟨1 / 2, half_mem_fragMid⟩⟩))
  rw [pwMidLabel_windowCover, pwMidLabel_windowCover] at this
  exact Bool.false_ne_true this

/-! ### The empty graph -/

/-- **The empty graph.** Its thickening is empty, for every `ε`. -/
theorem emptyThick_isEmpty (n : ℕ) (S : CriticalValues n) (ε : ℝ≥0) :
    IsEmpty ((GeometricThickening.functor ε).obj (toOver S (emptyData n))).left :=
  haveI := emptyData_isEmpty n S
  inferInstanceAs
    (IsEmpty ((ofFiniteData (emptyData n)).Realization S × GeometricThickening.Band ε))

/-- The realization of the thickening presentation of the empty graph is empty, for every `ε`:
every window is empty. -/
theorem emptyPresentation_isEmpty (n : ℕ) (S : CriticalValues n) (ε : ℝ≥0) :
    IsEmpty ((thickPresentation S (emptyData n) ε).Realization (S.shifted ε)) :=
  haveI := emptyData_isEmpty n S
  haveI : ∀ j, IsEmpty ((thickPresentation S (emptyData n) ε).V j) := fun _ =>
    ⟨fun x => isEmptyElim (Subtype.val x : (ofFiniteData (emptyData n)).Realization S)⟩
  (thickPresentation S (emptyData n) ε).isEmpty_realization (S.shifted ε)

/-- The thickening of the empty graph is constructible. -/
theorem emptyThick_isConstructibleSpace (n : ℕ) (S : CriticalValues n) (ε : ℝ≥0) :
    IsConstructibleSpace ((GeometricThickening.functor ε).obj (toOver S (emptyData n))) :=
  isConstructibleSpace_thickening_toOver S (emptyData n) ε

/-! ### A singleton at an arbitrary height -/

/-- The single level `a`. -/
def single (a : ℝ) : CriticalValues 0 where
  value _ := a
  strictMono i j h :=
    absurd h (by rw [Fin.fin_one_eq_zero i, Fin.fin_one_eq_zero j]; exact lt_irrefl _)

/-- **A singleton at height `a`.** The thickening of a single vertex at height `a` is the
closed segment `Band ε = [-ε, ε]`. -/
def singletonHomeomorph (a : ℝ) (ε : ℝ≥0) :
    ((GeometricThickening.functor ε).obj (toOver (single a) pt0)).left ≃ₜ
      GeometricThickening.Band ε where
  toFun z := z.2
  invFun t := ((ofFiniteData pt0).ofVertex (single a) 0 (), t)
  left_inv z := by
    obtain ⟨v, hv⟩ := Examples.Cylinder.ofVertex_surjective_zero (single a) (ofFiniteData pt0) z.1
    exact Prod.ext hv rfl
  right_inv _ := rfl
  continuous_toFun := continuous_snd
  continuous_invFun := continuous_const.prodMk continuous_id

/-- The thickened height of the singleton at the point `t` of the segment is `a + t`. -/
theorem height_singletonHomeomorph_symm (a : ℝ) (ε : ℝ≥0) (t : GeometricThickening.Band ε) :
    GeometricThickening.height ((ofFiniteData pt0).height (single a)) ε
      ((singletonHomeomorph a ε).symm t) = a + t :=
  rfl

/-- In the thickening presentation of the singleton, for `ε > 0`, a strip point at height `t` has
band coordinate `t - a`. -/
theorem singleton_snd_ofStrip (a : ℝ) {ε : ℝ≥0} (hε : 0 < ε)
    (k : Fin ((single a).shiftedCount ε)) (x : (thickPresentation (single a) pt0 ε).E k)
    (t : (((single a).shifted ε).K k : Set ℝ)) :
    ((thickProdHomeomorph (single a) pt0 ε hε
      ((thickPresentation (single a) pt0 ε).ofStrip _ k (x, t))).2 : ℝ) = t - a := by
  rw [snd_thickProdHomeomorph_ofStrip]
  have h := (ofFiniteData pt0).height_mem_Icc (single a)
    (windowTransfer (single a) pt0 ε
      (transferOK_of_mem (single a) ε (mid_mem_K (single a) ε k) (Ioo_subset_Icc_self t.2)) x :
        (ofFiniteData pt0).Realization (single a))
  rw [le_antisymm h.2 h.1]
  rfl

/-! ### `ε = 0` -/

/-- **`ε = 0`.** The lift at `ε = 0`, followed by the inclusion of constructible spaces, is
isomorphic to the inclusion of graph objects, by the merged zero isomorphism. -/
def thickeningZeroIso : thickeningToConstructible 0 ⋙ IsConstructibleSpace.ι ≅ IsRGraph.ι :=
  NatIso.ofComponents (fun A => GeometricThickening.zeroIso.app A.obj)
    fun φ => GeometricThickening.zeroIso.hom.naturality φ.hom

theorem thickeningZeroIso_hom_app (A : RGraphCat) :
    thickeningZeroIso.hom.app A = GeometricThickening.zeroIso.hom.app A.obj :=
  rfl

/-! ### A single edge -/

/-- **A single edge.** On gap `k0` of the thickened single edge at `ε = 1`, a strip point at height
`t` over the edge point of parameter `s` lies over the edge point of height
`s (t + 1) / (mid + 1)`: a linear stretch of an edge that crosses one window end. -/
theorem singleEdge_strip_height {s : ℝ}
    (hs : s ∈ frag S01 0 (mid S01 1 k0 - ((1 : ℝ≥0) : ℝ)) (mid S01 1 k0 + ((1 : ℝ≥0) : ℝ)))
    (x : (thickPresentation S01 singleEdge 1).E k0) {y : singleEdge.E 0}
    (hx : x.1 = (ofFiniteData singleEdge).ofCylinder S01 0 (y, ⟨s, frag_subset_seg hs⟩))
    (t : ((S01.shifted 1).K k0 : Set ℝ)) :
    (ofFiniteData singleEdge).height S01 (thickProdHomeomorph S01 singleEdge 1 one_pos
      ((thickPresentation S01 singleEdge 1).ofStrip _ k0 (x, t))).1 =
        s * ((t + 1) / (mid S01 1 k0 + 1)) := by
  rw [fst_thickProdHomeomorph_ofStrip, coe_windowTransfer_ofCylinder S01 singleEdge 1 _ hs x hx]
  have hb := mid_k0_bounds
  have ht1 : -1 < (t : ℝ) := by
    have := t.2.1
    rwa [k0_castSucc, S01_shifted_zero] at this
  have ht2 : (t : ℝ) ≤ 0 := t.2.2.le.trans S01_shifted_one_le
  show fragAff (S01.value (Fin.castSucc 0)) (S01.value (Fin.succ 0)) ((1 : ℝ≥0) : ℝ)
    (mid S01 1 k0) t s = _
  have e1 : max (0 : ℝ) ((t : ℝ) - 1) = 0 := max_eq_left (by linarith)
  have e2 : max (0 : ℝ) (mid S01 1 k0 - 1) = 0 := max_eq_left (by linarith [hb.2])
  have e3 : min (1 : ℝ) ((t : ℝ) + 1) = t + 1 := min_eq_right (by linarith)
  have e4 : min (1 : ℝ) (mid S01 1 k0 + 1) = mid S01 1 k0 + 1 := min_eq_right (by linarith [hb.2])
  simp only [fragAff, Fin.castSucc_zero, Fin.succ_zero_eq_one, S01_value_zero, S01_value_one,
    NNReal.coe_one]
  rw [e1, e2, e3, e4]
  ring

/-! ### Disjoint edges remain distinct -/

/-- At the lower end `-1` of gap `k0`, every parameter of the edge `[0, 1]` goes to `0`. -/
theorem fragAff_segBot_k0 (s : ℝ) :
    fragAff (S01.value (Fin.castSucc 0)) (S01.value (Fin.succ 0)) ((1 : ℝ≥0) : ℝ)
      (mid S01 1 k0) ((segBot (S01.shifted 1) k0 : Seg (S01.shifted 1) k0) : ℝ) s =
        S01.value (Fin.castSucc 0) := by
  rw [fragAff_collapse]
  · rw [coe_segBot_k0, Fin.castSucc_zero, S01_value_zero, NNReal.coe_one]
    norm_num
  · rw [coe_segBot_k0, Fin.castSucc_zero, Fin.succ_zero_eq_one, S01_value_zero, S01_value_one,
      NNReal.coe_one]
    norm_num

/-- The interior point of parameter `(mid + 1) / 2` on segment `b` of the two disjoint segments, a
point of the edge piece of gap `k0`. -/
def twoSegPt (b : Bool) : win S01 twoSegData 1 (mid S01 1 k0) :=
  ⟨(ofFiniteData twoSegData).ofCylinder S01 0 (b, ⟨_, frag_subset_seg s0_mem⟩),
    frag_subset_Icc s0_mem⟩

/-- The left attaching map of gap `k0` sends the point of each segment to that segment's
own lower vertex. -/
theorem twoSeg_left_apply (b : Bool) :
    ((thickPresentation S01 twoSegData 1).left k0 (twoSegPt b)).1 =
      (ofFiniteData twoSegData).ofVertex S01 0 b := by
  have hok := transferOK_of_mem S01 1 (mid_mem_K S01 1 k0) (segBot (S01.shifted 1) k0).2
  change (windowTransfer S01 twoSegData 1 hok (twoSegPt b) :
    (ofFiniteData twoSegData).Realization S01) = _
  rw [coe_windowTransfer_ofCylinder S01 twoSegData 1 hok s0_mem (twoSegPt b) (y := b) rfl]
  have hseg : (⟨_, frag_subset_seg (hok.fragAff_mem s0_mem)⟩ : Seg S01 0) = segBot S01 0 :=
    Subtype.ext (fragAff_segBot_k0 _)
  rw [hseg]
  exact (ofFiniteData twoSegData).ofCylinder_segBot S01 0 b

/-- **Disjoint edges remain distinct.** Unlike the parallel edges (`left_collapse`), the left
attaching map of gap `k0` keeps the points of the two disjoint segments apart. -/
theorem twoSeg_left_ne :
    (thickPresentation S01 twoSegData 1).left k0 (twoSegPt false) ≠
      (thickPresentation S01 twoSegData 1).left k0 (twoSegPt true) := fun h =>
  Bool.false_ne_true ((ofFiniteData twoSegData).ofVertex_injective S01 0
    ((twoSeg_left_apply false).symm.trans ((congrArg Subtype.val h).trans
      (twoSeg_left_apply true))))

/-- The thickening of the two disjoint segments is not preconnected, for every `ε`: the
component label of the segments factors through the first coordinate. -/
theorem twoSegThick_not_preconnected (ε : ℝ≥0) :
    ¬ PreconnectedSpace ((GeometricThickening.functor ε).obj (toOver S01 twoSegData)).left :=
  fun h => Bool.false_ne_true (PreconnectedSpace.constant h
    (twoSegLabel.continuous.comp continuous_fst)
    (x := ((ofFiniteData twoSegData).ofVertex S01 0 false,
      ⟨0, GeometricThickening.zero_mem_band ε⟩))
    (y := ((ofFiniteData twoSegData).ofVertex S01 0 true,
      ⟨0, GeometricThickening.zero_mem_band ε⟩)))

/-! ### A shifted-level collision -/

/-- `ε = 1/2`, where the shifts `0 + ε` and `1 - ε` of the levels `0 < 1` coincide. -/
def halfNN : ℝ≥0 := ⟨1 / 2, by norm_num⟩

@[simp] theorem coe_halfNN : (halfNN : ℝ) = 1 / 2 := rfl

/-- The shifts `{-1/2, 1/2} ∪ {1/2, 3/2}` merge to `{-1/2, 1/2, 3/2}`. -/
theorem S01_shiftedSet_half : S01.shiftedSet halfNN = {-1 / 2, 1 / 2, 3 / 2} := by
  ext x
  rw [CriticalValues.mem_shiftedSet]
  constructor
  · rintro ⟨i, h | h⟩ <;> fin_cases i <;> norm_num [S01] at h <;> rw [h] <;> norm_num
  · intro h
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with rfl | rfl | rfl
    · exact ⟨0, Or.inl (by norm_num [S01])⟩
    · exact ⟨0, Or.inr (by norm_num [S01])⟩
    · exact ⟨1, Or.inr (by norm_num [S01])⟩

/-- The collision witness has three levels, not four. -/
theorem S01_shiftedCount_half : S01.shiftedCount halfNN = 2 := by
  unfold CriticalValues.shiftedCount
  rw [S01_shiftedSet_half, Finset.card_insert_of_notMem (by norm_num),
    Finset.card_insert_of_notMem (by norm_num), Finset.card_singleton]

theorem S01_shifted_half_first : (S01.shifted halfNN).value 0 = -1 / 2 := by
  rw [CriticalValues.shifted_value_zero, S01_value_zero, coe_halfNN]
  norm_num

theorem S01_shifted_half_last : (S01.shifted halfNN).value (Fin.last _) = 3 / 2 := by
  rw [CriticalValues.shifted_value_last, show Fin.last 1 = 1 from rfl, S01_value_one, coe_halfNN]
  norm_num

/-- The middle index of the collision witness. -/
def kc : Fin (S01.shiftedCount halfNN + 1) := ⟨1, by rw [S01_shiftedCount_half]; omega⟩

/-- **Shifted-level collision.** The middle level is `1/2 = 0 + ε = 1 - ε`. -/
theorem S01_shifted_half_middle : (S01.shifted halfNN).value kc = 1 / 2 := by
  have hmem : (S01.shifted halfNN).value kc ∈ Set.range (S01.shifted halfNN).value := ⟨_, rfl⟩
  rw [CriticalValues.range_shifted, S01_shiftedSet_half] at hmem
  have h0 : (S01.shifted halfNN).value 0 < (S01.shifted halfNN).value kc :=
    (S01.shifted halfNN).strictMono (by simp [Fin.lt_def, kc])
  have h2 : (S01.shifted halfNN).value kc < (S01.shifted halfNN).value (Fin.last _) :=
    (S01.shifted halfNN).strictMono (by simp [Fin.lt_def, kc, S01_shiftedCount_half])
  rw [S01_shifted_half_first] at h0
  rw [S01_shifted_half_last] at h2
  simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
    Set.mem_singleton_iff] at hmem
  rcases hmem with h | h | h
  · linarith
  · exact h
  · linarith

/-- The first gap `[-1/2, 1/2]` of the collision witness. -/
def kh : Fin (S01.shiftedCount halfNN) := ⟨0, by rw [S01_shiftedCount_half]; omega⟩

theorem kh_castSucc : (kh.castSucc : Fin (S01.shiftedCount halfNN + 1)) = 0 :=
  Fin.ext (by simp [kh])

theorem kh_succ : kh.succ = kc :=
  Fin.ext (by simp [kh, kc])

theorem mid_kh : mid S01 halfNN kh = 0 := by
  unfold mid
  rw [kh_castSucc, kh_succ, S01_shifted_half_first, S01_shifted_half_middle]
  norm_num

/-- The vertex piece at the collision level is the whole single edge: the window `[0, 1]` contains
both original vertices. -/
theorem collision_window_eq_univ :
    win S01 singleEdge halfNN ((S01.shifted halfNN).value kc) = univ := by
  rw [S01_shifted_half_middle]
  refine eq_univ_of_forall fun x => ?_
  have h := (ofFiniteData singleEdge).height_mem_Icc S01 x
  rw [S01_value_zero, show Fin.last 1 = 1 from rfl, S01_value_one] at h
  show (ofFiniteData singleEdge).height S01 x ∈ Icc (1 / 2 - (halfNN : ℝ)) (1 / 2 + (halfNN : ℝ))
  rw [coe_halfNN]
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

theorem half_mem_fragCollision :
    (1 / 2 : ℝ) ∈
      frag S01 0 (mid S01 halfNN kh - (halfNN : ℝ)) (mid S01 halfNN kh + (halfNN : ℝ)) := by
  rw [mid_kh, coe_halfNN]
  norm_num [frag]

/-- The upper end, at parameter `1/2`, of the edge fragment of the window at the midpoint `0` of the
first gap; an interior point of the original edge. -/
def collisionTop : win S01 singleEdge halfNN (mid S01 halfNN kh) :=
  ⟨(ofFiniteData singleEdge).ofCylinder S01 0 ((), ⟨_, frag_subset_seg half_mem_fragCollision⟩),
    frag_subset_Icc half_mem_fragCollision⟩

/-- **The edge reaches the upper vertex at the collision level.** The right attaching map of the
first gap sends the upper fragment end `c + ε = 1/2` to the original upper vertex `1`, which lies in
the vertex piece of the collision level `1/2`. -/
theorem collision_right_apply :
    ((thickPresentation S01 singleEdge halfNN).right kh collisionTop).1 =
      (ofFiniteData singleEdge).ofVertex S01 1 () := by
  have hok := transferOK_of_mem S01 halfNN (mid_mem_K S01 halfNN kh)
    (segTop (S01.shifted halfNN) kh).2
  change (windowTransfer S01 singleEdge halfNN hok collisionTop :
    (ofFiniteData singleEdge).Realization S01) = _
  rw [coe_windowTransfer_ofCylinder S01 singleEdge halfNN hok half_mem_fragCollision collisionTop
    (y := ()) rfl]
  have htop : ((segTop (S01.shifted halfNN) kh : Seg (S01.shifted halfNN) kh) : ℝ) = 1 / 2 := by
    show (S01.shifted halfNN).value kh.succ = 1 / 2
    rw [kh_succ, S01_shifted_half_middle]
  have hz : fragAff (S01.value (Fin.castSucc 0)) (S01.value (Fin.succ 0)) (halfNN : ℝ)
      (mid S01 halfNN kh) ((segTop (S01.shifted halfNN) kh : Seg (S01.shifted halfNN) kh) : ℝ)
      (1 / 2) = S01.value (Fin.succ 0) := by
    rw [htop, mid_kh, coe_halfNN]
    simp only [fragAff, Fin.castSucc_zero, Fin.succ_zero_eq_one, S01_value_zero, S01_value_one]
    norm_num
  have hseg : (⟨_, frag_subset_seg (hok.fragAff_mem half_mem_fragCollision)⟩ : Seg S01 0) =
      segTop S01 0 :=
    Subtype.ext hz
  rw [hseg]
  exact (ofFiniteData singleEdge).ofCylinder_segTop S01 0 ()

end Examples.RGraphThickening

end

end TDA.Reeb
