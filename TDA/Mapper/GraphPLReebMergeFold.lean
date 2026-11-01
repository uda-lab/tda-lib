import TDA.Mapper.GraphPLReebMapPair
import TDA.Mapper.GraphPLReebScaling
import TDA.Mapper.UniformCover
import TDA.Reeb.GraphRealization
import TDA.Reeb.GraphPLHeight

/-!
# Height-preserving folds for merge-height trees

For `0 < c ≤ M`, `mergeSection c M` selects the point of the path `0 — 2 — 3` at each
height in `[0, M]` and clamps other inputs to that interval. Every point of the merge-tree
realization has a path to the selected point at its height, with height deviation at most `c`.
These folds give the exact graph-PL Reeb distance
`ENNReal.ofReal (min (b - a) (b / 2))` for `0 < a < b ≤ M`. The result is specific to this
three-edge merge tree. It gives no formula for other trees, more than two leaves, unequal leaf
heights, or a branch height below a leaf, and gives no converse to the height-map-pair bound.
-/

open Set
open TDA.Reeb
open TDA.Reeb.GraphPL
open TDA.Reeb.RGraph
open TDA.Reeb.GraphRealization
open TDA.Mapper.GraphPL
open scoped NNReal ENNReal

namespace TDA.Mapper.GraphPL

noncomputable section

private def mergeSectionPoint (c M : ℝ) (h0c : 0 < c) (hcM : c ≤ M) (y : ℝ) :
    Realization mergeY := by
  let clamp := Set.projIcc 0 M (le_trans h0c.le hcM) y
  let topDen := if c = M then 1 else M - c
  exact if (clamp : ℝ) ≤ c then
      edgePoint mergeY mergeFoldD02
        (Set.projIcc 0 1 zero_le_one ((clamp : ℝ) / c))
    else
      edgePoint mergeY mergeFoldD23
        (Set.projIcc 0 1 zero_le_one (((clamp : ℝ) - c) / topDen))

private theorem continuous_mergeSectionPoint (c M : ℝ) (h0c : 0 < c) (hcM : c ≤ M) :
    Continuous (mergeSectionPoint c M h0c hcM) := by
  classical
  let z : ℝ → ℝ := fun y => (Set.projIcc 0 M (le_trans h0c.le hcM) y : ℝ)
  let topDen : ℝ := if c = M then 1 else M - c
  let lower : ℝ → Realization mergeY := fun y =>
    edgePoint mergeY mergeFoldD02 (Set.projIcc 0 1 zero_le_one (z y / c))
  let upper : ℝ → Realization mergeY := fun y =>
    edgePoint mergeY mergeFoldD23
      (Set.projIcc 0 1 zero_le_one ((z y - c) / topDen))
  have hz : Continuous z := by
    exact continuous_subtype_val.comp continuous_projIcc
  have hden : topDen ≠ 0 := by
    dsimp [topDen]
    split_ifs with h
    · norm_num
    · have hlt : c < M := by
        rcases lt_or_eq_of_le hcM with hlt | heq
        · exact hlt
        · exact (h heq).elim
      exact sub_ne_zero.mpr (by linarith)
  have hlower : Continuous lower := by
    dsimp [lower]
    exact (continuous_edgePoint mergeY mergeFoldD02).comp
      (continuous_projIcc.comp (hz.div_const c))
  have hupper : Continuous upper := by
    dsimp [upper]
    exact (continuous_edgePoint mergeY mergeFoldD23).comp
      (continuous_projIcc.comp ((hz.sub continuous_const).div_const topDen))
  have hzg : Continuous fun _ : ℝ => c := continuous_const
  change Continuous fun y => if z y ≤ c then lower y else upper y
  exact hlower.if_le hupper hz hzg fun y hy => by
    have hzero : z y - c = 0 := sub_eq_zero.mpr hy
    have hratio₁ : z y / c = 1 := by rw [hy]; exact div_self h0c.ne'
    have hratio₂ : (z y - c) / topDen = 0 := by rw [hzero, zero_div]
    have h₁ : Set.projIcc 0 1 zero_le_one (z y / c) = (1 : unitInterval) := by
      rw [hratio₁]
      exact Set.projIcc_of_mem zero_le_one (by norm_num)
    have h₂ : Set.projIcc 0 1 zero_le_one ((z y - c) / topDen) = (0 : unitInterval) := by
      rw [hratio₂]
      exact Set.projIcc_of_mem zero_le_one (by norm_num)
    change edgePoint mergeY mergeFoldD02 _ = edgePoint mergeY mergeFoldD23 _
    rw [h₁, h₂, edgePoint_one, edgePoint_zero]
    rfl

/-- The selected point on `0 — 2 — 3` at each height, with inputs clamped to `[0, M]`. -/
def mergeSection (c M : ℝ) (h0c : 0 < c) (hcM : c ≤ M) :
    C(ℝ, Realization mergeY) :=
  ⟨mergeSectionPoint c M h0c hcM, continuous_mergeSectionPoint c M h0c hcM⟩

@[simp] theorem mergeSection_apply (c M : ℝ) (h0c : 0 < c) (hcM : c ≤ M) (y : ℝ) :
    mergeSection c M h0c hcM y = mergeSectionPoint c M h0c hcM y := rfl

/-- On the lower edge, the section selects the point at the given height. -/
theorem mergeSection_lower (c M : ℝ) (h0c : 0 < c) (hcM : c ≤ M) (t : unitInterval) :
    mergeSection c M h0c hcM (c * (t : ℝ)) = edgePoint mergeY mergeFoldD02 t := by
  have ht0 : 0 ≤ (t : ℝ) := t.2.1
  have ht1 : (t : ℝ) ≤ 1 := t.2.2
  have hy0 : 0 ≤ c * (t : ℝ) := mul_nonneg h0c.le ht0
  have hyM : c * (t : ℝ) ≤ M := by
    calc
      c * (t : ℝ) ≤ c := by nlinarith [mul_le_mul_of_nonneg_left ht1 h0c.le]
      _ ≤ M := hcM
  have hclamp : (Set.projIcc 0 M (le_trans h0c.le hcM) (c * (t : ℝ)) : ℝ) = c * (t : ℝ) := by
    rw [Set.projIcc_of_mem (le_trans h0c.le hcM) ⟨hy0, hyM⟩]
  have hratio : c * (t : ℝ) / c = (t : ℝ) := by
    field_simp [h0c.ne']
  have hproj : Set.projIcc 0 1 zero_le_one (c * (t : ℝ) / c) = t := by
    rw [hratio]
    exact Set.projIcc_of_mem zero_le_one t.2
  have hbranch : c * (t : ℝ) ≤ c := by
    nlinarith [mul_le_mul_of_nonneg_left ht1 h0c.le]
  simp only [mergeSection_apply, mergeSectionPoint, hclamp, if_pos hbranch, hproj]

/-- Below the top vertex, the section selects the point at the given height on `2 — 3`. -/
theorem mergeSection_upper (c M : ℝ) (h0c : 0 < c) (hcM : c ≤ M) (hcM' : c < M)
    (t : unitInterval) :
    mergeSection c M h0c hcM (c + (M - c) * (t : ℝ)) = edgePoint mergeY mergeFoldD23 t := by
  have hMc : 0 < M - c := sub_pos.mpr hcM'
  have ht0 : 0 ≤ (t : ℝ) := t.2.1
  have ht1 : (t : ℝ) ≤ 1 := t.2.2
  have hy0 : 0 ≤ c + (M - c) * (t : ℝ) := by positivity
  have hyM : c + (M - c) * (t : ℝ) ≤ M := by nlinarith [mul_le_mul_of_nonneg_left ht1 hMc.le]
  have hclamp :
      (Set.projIcc 0 M (le_trans h0c.le hcM) (c + (M - c) * (t : ℝ)) : ℝ) =
        c + (M - c) * (t : ℝ) := by
    rw [Set.projIcc_of_mem (le_trans h0c.le hcM) ⟨hy0, hyM⟩]
  by_cases htzero : (t : ℝ) = 0
  · have hden : (if c = M then (1 : ℝ) else M - c) = M - c := by
      simp [ne_of_lt hcM']
    have htzero' : t = 0 := Subtype.ext htzero
    subst t
    have hratio : c / c = 1 := div_self h0c.ne'
    have hproj : Set.projIcc 0 1 zero_le_one (c / c) = (1 : unitInterval) := by
      rw [hratio]
      exact Set.projIcc_of_mem zero_le_one (by norm_num)
    have hclamp0 : (Set.projIcc 0 M (le_trans h0c.le hcM) c : ℝ) = c := by
      exact congrArg Subtype.val
        (Set.projIcc_of_mem (le_trans h0c.le hcM) ⟨h0c.le, hcM⟩)
    simp [mergeSection, mergeSectionPoint, hclamp0, hratio,
      edgePoint_one, edgePoint_zero]
  have htpos : 0 < (t : ℝ) := by
    rcases lt_or_eq_of_le t.2.1 with h | h
    · exact h
    · exact (htzero h.symm).elim
  have hgt : c < c + (M - c) * (t : ℝ) := by
    nlinarith [mul_pos (sub_pos.mpr hcM') htpos]
  have hratio :
      (c + (M - c) * (t : ℝ) - c) / (M - c) = (t : ℝ) := by
    rw [show c + (M - c) * (t : ℝ) - c = (M - c) * (t : ℝ) by ring,
      mul_div_cancel_left₀ _ hMc.ne']
  have hproj :
      Set.projIcc 0 1 zero_le_one
          ((c + (M - c) * (t : ℝ) - c) / (M - c)) = t := by
    rw [hratio]
    exact Set.projIcc_of_mem zero_le_one t.2
  have hden : (if c = M then (1 : ℝ) else M - c) = M - c := by
    simp [ne_of_lt hcM']
  rw [mergeSection_apply]
  unfold mergeSectionPoint
  simp only [hclamp]
  rw [if_neg (not_le.mpr hgt), hden, hproj]

/-- When the branch height is the top height, the section stays on `0 — 2` for every input. -/
theorem mergeSection_at_top_apex (M : ℝ) (hM : 0 < M) (y : ℝ) :
    mergeSection M M hM le_rfl y = edgePoint mergeY mergeFoldD02
      (Set.projIcc 0 1 zero_le_one
        (((Set.projIcc 0 M hM.le y : ℝ) : ℝ) / M)) := by
  rw [mergeSection_apply]
  unfold mergeSectionPoint
  have hclamp_le : (Set.projIcc 0 M hM.le y : ℝ) ≤ M :=
    (Set.projIcc 0 M hM.le y).2.2
  simp only [if_pos hclamp_le]

/-- The section preserves every height in its unclamped interval. -/
theorem plHeight_mergeSection (c M : ℝ) (h0c : 0 < c) (hcM : c ≤ M) {y : ℝ}
    (hy : y ∈ Icc 0 M) :
    plHeight mergeY (mergeHeights c M) (mergeSection c M h0c hcM y) = y := by
  by_cases hyc : y ≤ c
  · have ht : (y / c : ℝ) ∈ Icc 0 1 := by
      constructor
      · exact div_nonneg hy.1 h0c.le
      · exact (div_le_one h0c).2 hyc
    have hclamp : (Set.projIcc 0 M (le_trans h0c.le hcM) y : ℝ) = y := by
      exact congrArg Subtype.val (Set.projIcc_of_mem (le_trans h0c.le hcM) hy)
    have hparam : Set.projIcc 0 1 zero_le_one (y / c) = ⟨y / c, ht⟩ :=
      Set.projIcc_of_mem zero_le_one ht
    rw [mergeSection_apply]
    unfold mergeSectionPoint
    simp only [hclamp]
    rw [if_pos hyc, hparam]
    simp [GraphPL.plHeight_edgePoint, GraphPL.dartHeight, mergeHeights, mergeFoldD02]
    field_simp [h0c.ne']
  · have hcy : c < y := lt_of_not_ge hyc
    have hcM' : c < M := by linarith [hcy, hy.2]
    have hden : (if c = M then (1 : ℝ) else M - c) = M - c := by
      simp [ne_of_lt hcM']
    have ht : ((y - c) / (M - c) : ℝ) ∈ Icc 0 1 := by
      constructor
      · exact div_nonneg (sub_nonneg.mpr hcy.le) (sub_nonneg.mpr hcM)
      · exact (div_le_one (sub_pos.mpr hcM')).2 (by linarith [hy.2])
    have hclamp : (Set.projIcc 0 M (le_trans h0c.le hcM) y : ℝ) = y := by
      exact congrArg Subtype.val (Set.projIcc_of_mem (le_trans h0c.le hcM) hy)
    have hparam : Set.projIcc 0 1 zero_le_one ((y - c) / (M - c)) =
        ⟨(y - c) / (M - c), ht⟩ := Set.projIcc_of_mem zero_le_one ht
    have hden0 : M - c ≠ 0 := ne_of_gt (sub_pos.mpr hcM')
    have hden1 : -c + M ≠ 0 := by linarith
    rw [mergeSection_apply]
    unfold mergeSectionPoint
    simp only [hclamp]
    rw [if_neg (not_le.mpr hcy), hden, hparam]
    simp [GraphPL.plHeight_edgePoint, GraphPL.dartHeight, mergeHeights, mergeFoldD23]
    change (1 - ((y - c) / (M - c))) * c + ((y - c) / (M - c)) * M = y
    field_simp [hden0]; ring_nf

private theorem castPath_apply {x y x' y' : Realization mergeY}
    (γ : Path x y) (hx : x' = x) (hy : y' = y) (t : unitInterval) :
    γ.cast hx hy t = γ t := by
  exact congrFun (Path.cast_coe γ hx hy) t

private theorem mergeFoldHeight_d02 (c M : ℝ) (t : unitInterval) :
    plHeight mergeY (mergeHeights c M) (edgePoint mergeY mergeFoldD02 t) = c * (t : ℝ) := by
  simp [GraphPL.plHeight_edgePoint, GraphPL.dartHeight, mergeHeights, mergeFoldD02]; ring

private theorem mergeFoldHeight_d12 (c M : ℝ) (t : unitInterval) :
    plHeight mergeY (mergeHeights c M) (edgePoint mergeY mergeFoldD12 t) = c * (t : ℝ) := by
  simp [GraphPL.plHeight_edgePoint, GraphPL.dartHeight, mergeHeights, mergeFoldD12]; ring

private theorem mergeFoldHeight_d23 (c M : ℝ) (t : unitInterval) :
    plHeight mergeY (mergeHeights c M) (edgePoint mergeY mergeFoldD23 t) =
      c + (M - c) * (t : ℝ) := by
  simp [GraphPL.plHeight_edgePoint, GraphPL.dartHeight, mergeHeights, mergeFoldD23]
  ring

private abbrev mergeFoldHeight (c M : ℝ) : C(Realization mergeY, ℝ) :=
  plHeight mergeY (mergeHeights c M)

private theorem mergeSection_top_eq_d23zero (c M : ℝ) (h0c : 0 < c) (hcM : c ≤ M)
    (hcm : c = M) :
    mergeSection c M h0c hcM M = edgePoint mergeY mergeFoldD23 0 := by
  subst M
  calc
    mergeSection c c h0c le_rfl c = mergeSection c c h0c le_rfl (c * (1 : ℝ)) := by rw [mul_one]
    _ = edgePoint mergeY mergeFoldD02 1 := mergeSection_lower c c h0c le_rfl 1
    _ = edgePoint mergeY mergeFoldD23 0 := by
      rw [edgePoint_one, edgePoint_zero]
      simp [mergeFoldD02, mergeFoldD23]

private theorem mergeFoldD12TurnSource :
    vertex mergeY mergeFoldD12.snd = edgePoint mergeY mergeFoldD02 1 := by
  rw [edgePoint_one]
  simp [mergeFoldD02, mergeFoldD12]

private def mergeFoldD12Route (t : unitInterval) :
    Path (edgePoint mergeY mergeFoldD12 t) (edgePoint mergeY mergeFoldD02 t) :=
  ((edgeSegment mergeY mergeFoldD12 t 1).cast rfl
    (edgePoint_one mergeY mergeFoldD12).symm).trans
    ((edgeSegment mergeY mergeFoldD02 1 t).cast mergeFoldD12TurnSource rfl)

private theorem mergeFoldPathD02_target (c M : ℝ) (h0c : 0 < c) (hcM : c ≤ M)
    (t : unitInterval) :
    mergeSection c M h0c hcM
        (plHeight mergeY (mergeHeights c M) (edgePoint mergeY mergeFoldD02 t)) =
      edgePoint mergeY mergeFoldD02 t := by
  rw [mergeFoldHeight_d02, mergeSection_lower]

private def mergeFoldPathD02 (c M : ℝ) (h0c : 0 < c) (hcM : c ≤ M)
    (t : unitInterval) :
    Path (edgePoint mergeY mergeFoldD02 t)
      (mergeSection c M h0c hcM
        (plHeight mergeY (mergeHeights c M) (edgePoint mergeY mergeFoldD02 t))) :=
  (Path.refl (edgePoint mergeY mergeFoldD02 t)).cast rfl
    (mergeFoldPathD02_target c M h0c hcM t)

private theorem mergeFoldPathD12_target (c M : ℝ) (h0c : 0 < c) (hcM : c ≤ M)
    (t : unitInterval) :
    mergeSection c M h0c hcM
        (plHeight mergeY (mergeHeights c M) (edgePoint mergeY mergeFoldD12 t)) =
      edgePoint mergeY mergeFoldD02 t := by
  rw [mergeFoldHeight_d12, mergeSection_lower]

private def mergeFoldPathD12 (c M : ℝ) (h0c : 0 < c) (hcM : c ≤ M)
    (t : unitInterval) :
    Path (edgePoint mergeY mergeFoldD12 t)
      (mergeSection c M h0c hcM
        (plHeight mergeY (mergeHeights c M) (edgePoint mergeY mergeFoldD12 t))) :=
  (mergeFoldD12Route t).cast rfl (mergeFoldPathD12_target c M h0c hcM t)

private theorem mergeFoldPathD23_target_top (c M : ℝ) (h0c : 0 < c) (hcM : c ≤ M)
    (t : unitInterval) (hcm : c = M) :
    mergeSection c M h0c hcM
        (plHeight mergeY (mergeHeights c M) (edgePoint mergeY mergeFoldD23 t)) =
      edgePoint mergeY mergeFoldD23 0 := by
  have hheight :
      plHeight mergeY (mergeHeights c M) (edgePoint mergeY mergeFoldD23 t) = M := by
    rw [mergeFoldHeight_d23, hcm]
    ring
  calc
    _ = mergeSection c M h0c hcM M := congrArg (mergeSection c M h0c hcM) hheight
    _ = edgePoint mergeY mergeFoldD23 0 := mergeSection_top_eq_d23zero c M h0c hcM hcm

private theorem mergeFoldPathD23_target_self (c M : ℝ) (h0c : 0 < c) (hcM : c ≤ M)
    (t : unitInterval) (hcM' : c < M) :
    mergeSection c M h0c hcM
        (plHeight mergeY (mergeHeights c M) (edgePoint mergeY mergeFoldD23 t)) =
      edgePoint mergeY mergeFoldD23 t := by
  rw [mergeFoldHeight_d23, mergeSection_upper c M h0c hcM hcM']

private def mergeFoldPathD23 (c M : ℝ) (h0c : 0 < c) (hcM : c ≤ M)
    (t : unitInterval) :
    Path (edgePoint mergeY mergeFoldD23 t)
      (mergeSection c M h0c hcM
        (plHeight mergeY (mergeHeights c M) (edgePoint mergeY mergeFoldD23 t))) := by
  by_cases hcm : c = M
  · exact (edgeSegment mergeY mergeFoldD23 t 0).cast rfl
      (mergeFoldPathD23_target_top c M h0c hcM t hcm)
  · have hcM' : c < M := by
      rcases lt_or_eq_of_le hcM with h | heq
      · exact h
      · exact (hcm heq).elim
    exact (Path.refl (edgePoint mergeY mergeFoldD23 t)).cast rfl
      (mergeFoldPathD23_target_self c M h0c hcM t hcM')

private theorem mergeFoldDart_cases (d : mergeY.Dart) :
    d = mergeFoldD02 ∨ d = mergeFoldD02.symm ∨
      d = mergeFoldD12 ∨ d = mergeFoldD12.symm ∨
      d = mergeFoldD23 ∨ d = mergeFoldD23.symm := by
  rcases d with ⟨⟨u, v⟩, huv⟩
  rcases (mergeY_adj u v).1 huv with h | h | h | h | h | h
  · rcases h with ⟨rfl, rfl⟩
    left
    apply SimpleGraph.Dart.ext
    rfl
  · rcases h with ⟨rfl, rfl⟩
    right
    left
    apply SimpleGraph.Dart.ext
    rfl
  · rcases h with ⟨rfl, rfl⟩
    right
    right
    left
    apply SimpleGraph.Dart.ext
    rfl
  · rcases h with ⟨rfl, rfl⟩
    right
    right
    right
    left
    apply SimpleGraph.Dart.ext
    rfl
  · rcases h with ⟨rfl, rfl⟩
    right
    right
    right
    right
    left
    apply SimpleGraph.Dart.ext
    rfl
  · rcases h with ⟨rfl, rfl⟩
    right
    right
    right
    right
    right
    apply SimpleGraph.Dart.ext
    rfl

private theorem edgePoint_reverse (d : mergeY.Dart) (t : unitInterval) :
    edgePoint mergeY d.symm t = edgePoint mergeY d (unitInterval.symm t) := by
  calc
    edgePoint mergeY d.symm t = edgePoint mergeY d.symm (unitInterval.symm (unitInterval.symm t)) := by simp
    _ = edgePoint mergeY d (unitInterval.symm t) := edgePoint_symm mergeY d _

private theorem mergeFoldD12Route_height (c M : ℝ) (hc : 0 ≤ c) (t r : unitInterval) :
    c * (t : ℝ) ≤
        plHeight mergeY (mergeHeights c M) (mergeFoldD12Route t r) ∧
      plHeight mergeY (mergeHeights c M) (mergeFoldD12Route t r) ≤ c := by
  have hct : c * (t : ℝ) ≤ c := by
    calc
      c * (t : ℝ) ≤ c * 1 := mul_le_mul_of_nonneg_left t.2.2 hc
      _ = c := by ring
  have hD12 (u : unitInterval) :
      c * (t : ℝ) ≤ mergeFoldHeight c M (edgeSegment mergeY mergeFoldD12 t 1 u) ∧
        mergeFoldHeight c M (edgeSegment mergeY mergeFoldD12 t 1 u) ≤ c := by
    have h := GraphPL.plHeight_edgeSegment_bounds mergeY (mergeHeights c M)
      mergeFoldD12 t 1 u
    change min (mergeFoldHeight c M (edgePoint mergeY mergeFoldD12 t))
        (mergeFoldHeight c M (edgePoint mergeY mergeFoldD12 1)) ≤ _ ∧
      _ ≤ max (mergeFoldHeight c M (edgePoint mergeY mergeFoldD12 t))
        (mergeFoldHeight c M (edgePoint mergeY mergeFoldD12 1)) at h
    have hone : ((1 : unitInterval) : ℝ) = 1 := rfl
    rw [mergeFoldHeight_d12 c M t, mergeFoldHeight_d12 c M 1, hone, mul_one,
      min_eq_left hct, max_eq_right hct] at h
    exact h
  have hD02 (u : unitInterval) :
      c * (t : ℝ) ≤ mergeFoldHeight c M (edgeSegment mergeY mergeFoldD02 1 t u) ∧
        mergeFoldHeight c M (edgeSegment mergeY mergeFoldD02 1 t u) ≤ c := by
    have h := GraphPL.plHeight_edgeSegment_bounds mergeY (mergeHeights c M)
      mergeFoldD02 1 t u
    change min (mergeFoldHeight c M (edgePoint mergeY mergeFoldD02 1))
        (mergeFoldHeight c M (edgePoint mergeY mergeFoldD02 t)) ≤ _ ∧
      _ ≤ max (mergeFoldHeight c M (edgePoint mergeY mergeFoldD02 1))
        (mergeFoldHeight c M (edgePoint mergeY mergeFoldD02 t)) at h
    have hone : ((1 : unitInterval) : ℝ) = 1 := rfl
    rw [mergeFoldHeight_d02 c M 1, mergeFoldHeight_d02 c M t, hone, mul_one,
      min_eq_right hct, max_eq_left hct] at h
    exact h
  unfold mergeFoldD12Route
  rw [Path.trans_apply]
  split_ifs with h
  · let u : unitInterval := ⟨2 * (r : ℝ),
      (unitInterval.mul_pos_mem_iff (by norm_num)).2 ⟨r.2.1, h⟩⟩
    simpa only [castPath_apply, mergeFoldHeight] using hD12 u
  · have hr0 : (0 : ℝ) ≤ r := r.2.1
    have hr1 : (r : ℝ) ≤ 1 := r.2.2
    have hq0 : (0 : ℝ) ≤ 2 * (r : ℝ) - 1 := by linarith
    have hq1 : 2 * (r : ℝ) - 1 ≤ 1 := by linarith
    let u : unitInterval := ⟨2 * (r : ℝ) - 1, ⟨hq0, hq1⟩⟩
    simpa only [castPath_apply, mergeFoldHeight] using hD02 u

private def mergeFoldPathProperty (c M : ℝ) (h0c : 0 < c) (hcM : c ≤ M)
    (x : Realization mergeY) : Prop :=
  ∃ γ : Path x (mergeSection c M h0c hcM (mergeFoldHeight c M x)),
    ∀ t, (mergeFoldHeight c M x ≤ c →
        mergeFoldHeight c M x ≤ mergeFoldHeight c M (γ t) ∧
          mergeFoldHeight c M (γ t) ≤ c) ∧
      (c < mergeFoldHeight c M x → mergeFoldHeight c M (γ t) = mergeFoldHeight c M x)

private theorem mergeFoldPath_d02_good (c M : ℝ) (h0c : 0 < c) (hcM : c ≤ M)
    (t : unitInterval) :
    mergeFoldPathProperty c M h0c hcM (edgePoint mergeY mergeFoldD02 t) := by
  refine ⟨mergeFoldPathD02 c M h0c hcM t, fun s => ?_⟩
  have hpath : mergeFoldPathD02 c M h0c hcM t s = edgePoint mergeY mergeFoldD02 t := by
    exact (castPath_apply _ _ _ _).trans (Path.refl_apply _ _)
  have hpathHeight := congrArg (mergeFoldHeight c M) hpath
  constructor
  · intro hs
    exact ⟨hpathHeight.symm.le, hpathHeight.le.trans hs⟩
  · intro _
    exact hpathHeight

private theorem mergeFoldPath_d12_good (c M : ℝ) (h0c : 0 < c) (hcM : c ≤ M)
    (t : unitInterval) :
    mergeFoldPathProperty c M h0c hcM (edgePoint mergeY mergeFoldD12 t) := by
  refine ⟨mergeFoldPathD12 c M h0c hcM t, fun s => ?_⟩
  have hpath : mergeFoldPathD12 c M h0c hcM t s = mergeFoldD12Route t s := by
    exact castPath_apply _ _ _ _
  have hroute := mergeFoldD12Route_height c M h0c.le t s
  have hroute' :
      mergeFoldHeight c M (edgePoint mergeY mergeFoldD12 t) ≤
          mergeFoldHeight c M (mergeFoldD12Route t s) ∧
        mergeFoldHeight c M (mergeFoldD12Route t s) ≤ c := by
    rw [mergeFoldHeight_d12]
    exact hroute
  have hpathHeight := congrArg (mergeFoldHeight c M) hpath
  constructor
  · intro _
    exact ⟨hroute'.1.trans hpathHeight.symm.le, hpathHeight.le.trans hroute'.2⟩
  · intro hgt
    have hstart : c * (t : ℝ) ≤ c := by
      nlinarith [mul_le_mul_of_nonneg_left t.2.2 h0c.le]
    have hgt' : c < c * (t : ℝ) := by
      simpa [GraphPL.dartHeight, mergeHeights, mergeFoldD12, mul_comm] using hgt
    exact (not_lt_of_ge hstart hgt').elim

private theorem mergeFoldPath_d23_top_height (c M : ℝ) (hcm : c = M)
    (t s : unitInterval) :
    mergeFoldHeight c M (edgeSegment mergeY mergeFoldD23 t 0 s) = c := by
  have hbounds := GraphPL.plHeight_edgeSegment_bounds mergeY (mergeHeights c M)
    mergeFoldD23 t 0 s
  change min (mergeFoldHeight c M (edgePoint mergeY mergeFoldD23 t))
      (mergeFoldHeight c M (edgePoint mergeY mergeFoldD23 0)) ≤ _ ∧
    _ ≤ max (mergeFoldHeight c M (edgePoint mergeY mergeFoldD23 t))
      (mergeFoldHeight c M (edgePoint mergeY mergeFoldD23 0)) at hbounds
  rw [mergeFoldHeight_d23 c M t, mergeFoldHeight_d23 c M 0, hcm] at hbounds
  simp only [sub_self, zero_mul, add_zero, min_self, max_self] at hbounds
  change M ≤ mergeFoldHeight M M (edgeSegment mergeY mergeFoldD23 t 0 s) ∧
    mergeFoldHeight M M (edgeSegment mergeY mergeFoldD23 t 0 s) ≤ M at hbounds
  have hEq : mergeFoldHeight M M (edgeSegment mergeY mergeFoldD23 t 0 s) = M :=
    le_antisymm hbounds.2 hbounds.1
  simpa [hcm] using hEq

private theorem mergeFoldPath_d23_good (c M : ℝ) (h0c : 0 < c) (hcM : c ≤ M)
    (t : unitInterval) :
    mergeFoldPathProperty c M h0c hcM (edgePoint mergeY mergeFoldD23 t) := by
  by_cases hcm : c = M
  · refine ⟨mergeFoldPathD23 c M h0c hcM t, fun s => ?_⟩
    have hstart : mergeFoldHeight c M (edgePoint mergeY mergeFoldD23 t) = c := by
      rw [mergeFoldHeight_d23, hcm]
      ring
    have hpath :
        mergeFoldHeight c M (mergeFoldPathD23 c M h0c hcM t s) = c := by
      have hpath' :
          mergeFoldPathD23 c M h0c hcM t s = edgeSegment mergeY mergeFoldD23 t 0 s := by
        simp only [mergeFoldPathD23, hcm]
        exact castPath_apply (edgeSegment mergeY mergeFoldD23 t 0) rfl
          (mergeFoldPathD23_target_top c M h0c hcM t hcm) s
      calc
        mergeFoldHeight c M (mergeFoldPathD23 c M h0c hcM t s) =
            mergeFoldHeight c M (edgeSegment mergeY mergeFoldD23 t 0 s) :=
          congrArg (mergeFoldHeight c M) hpath'
        _ = c := mergeFoldPath_d23_top_height c M hcm t s
    constructor
    · intro _
      exact ⟨hstart.le.trans hpath.symm.le, hpath.le⟩
    · intro _
      exact hpath.trans hstart.symm
  · have hcM' : c < M := by
      rcases lt_or_eq_of_le hcM with h | heq
      · exact h
      · exact (hcm heq).elim
    refine ⟨mergeFoldPathD23 c M h0c hcM t, fun s => ?_⟩
    have hpath :
        mergeFoldPathD23 c M h0c hcM t s = edgePoint mergeY mergeFoldD23 t := by
      simp only [mergeFoldPathD23, hcm]
      exact castPath_apply (Path.refl (edgePoint mergeY mergeFoldD23 t)) rfl
        (mergeFoldPathD23_target_self c M h0c hcM t hcM') s
    have hpathHeight :
        mergeFoldHeight c M (mergeFoldPathD23 c M h0c hcM t s) =
          mergeFoldHeight c M (edgePoint mergeY mergeFoldD23 t) :=
      congrArg (mergeFoldHeight c M) hpath
    have hstart_le : c ≤ mergeFoldHeight c M (edgePoint mergeY mergeFoldD23 t) := by
      rw [mergeFoldHeight_d23]
      have ht0 : 0 ≤ (t : ℝ) := t.2.1
      have hMc : 0 ≤ M - c := by linarith
      nlinarith [mul_nonneg hMc ht0]
    constructor
    · intro hle
      have heq : mergeFoldHeight c M (edgePoint mergeY mergeFoldD23 t) = c := le_antisymm hle hstart_le
      exact ⟨hpathHeight.symm.le, hpathHeight.le.trans heq.le⟩
    · intro _
      exact hpathHeight.trans rfl

/-- Every point of the merge tree is joined to the section at its height. Along this path, a point
at height at most `c` moves only through heights between its starting height and `c`; a point
above `c` keeps its height. When `c = M`, the path from the horizontal edge `2 — 3` to vertex 2
runs along that edge at constant height. -/
theorem exists_mergeSection_path (c M : ℝ) (h0c : 0 < c) (hcM : c ≤ M)
    (x : Realization mergeY) :
    ∃ γ : Path x (mergeSection c M h0c hcM (plHeight mergeY (mergeHeights c M) x)),
      ∀ t,
        (plHeight mergeY (mergeHeights c M) x ≤ c →
          plHeight mergeY (mergeHeights c M) x ≤ plHeight mergeY (mergeHeights c M) (γ t) ∧
            plHeight mergeY (mergeHeights c M) (γ t) ≤ c) ∧
        (c < plHeight mergeY (mergeHeights c M) x →
          plHeight mergeY (mergeHeights c M) (γ t) =
            plHeight mergeY (mergeHeights c M) x) := by
  apply ind mergeY (p := mergeFoldPathProperty c M h0c hcM)
  · intro v
    fin_cases v
    · simpa [mergeFoldD02, edgePoint_zero] using mergeFoldPath_d02_good c M h0c hcM 0
    · simpa [mergeFoldD12, edgePoint_zero] using mergeFoldPath_d12_good c M h0c hcM 0
    · simpa [mergeFoldD02, edgePoint_one] using mergeFoldPath_d02_good c M h0c hcM 1
    · simpa [mergeFoldD23, edgePoint_one] using mergeFoldPath_d23_good c M h0c hcM 1
  · intro d t
    rcases mergeFoldDart_cases d with h | h | h | h | h | h
    · rw [h]
      exact mergeFoldPath_d02_good c M h0c hcM t
    · rw [h, edgePoint_reverse]
      exact mergeFoldPath_d02_good c M h0c hcM (unitInterval.symm t)
    · rw [h]
      exact mergeFoldPath_d12_good c M h0c hcM t
    · rw [h, edgePoint_reverse]
      exact mergeFoldPath_d12_good c M h0c hcM (unitInterval.symm t)
    · rw [h]
      exact mergeFoldPath_d23_good c M h0c hcM t
    · rw [h, edgePoint_reverse]
      exact mergeFoldPath_d23_good c M h0c hcM (unitInterval.symm t)

private theorem mergeFoldHeight_mem_Icc (c M : ℝ) (hc0 : 0 ≤ c) (hcM : c ≤ M)
    (x : Realization mergeY) :
    plHeight mergeY (mergeHeights c M) x ∈ Icc 0 M := by
  have hM0 : 0 ≤ M := hc0.trans hcM
  apply plHeight_mem_Icc_of_forall
  intro v
  fin_cases v <;> simp [mergeHeights, hc0, hcM, hM0]

private theorem mergeFoldPath_deviation_le (c B M : ℝ) (h0c : 0 < c) (hcM : c ≤ M)
    (hcb : c ≤ B) (x : Realization mergeY) (γ : Path x
      (mergeSection c M h0c hcM (plHeight mergeY (mergeHeights c M) x)))
    (hγ : ∀ t,
      (plHeight mergeY (mergeHeights c M) x ≤ c →
        plHeight mergeY (mergeHeights c M) x ≤ plHeight mergeY (mergeHeights c M) (γ t) ∧
          plHeight mergeY (mergeHeights c M) (γ t) ≤ c) ∧
      (c < plHeight mergeY (mergeHeights c M) x →
        plHeight mergeY (mergeHeights c M) (γ t) =
          plHeight mergeY (mergeHeights c M) x)) :
    ∀ t, |plHeight mergeY (mergeHeights c M) (γ t) -
      plHeight mergeY (mergeHeights c M) x| ≤ B := by
  have hx0 : 0 ≤ plHeight mergeY (mergeHeights c M) x :=
    (mergeFoldHeight_mem_Icc c M h0c.le hcM x).1
  have hB0 : 0 ≤ B := h0c.le.trans hcb
  intro t
  by_cases hle : plHeight mergeY (mergeHeights c M) x ≤ c
  · obtain ⟨hlo, hhi⟩ := (hγ t).1 hle
    rw [abs_of_nonneg (sub_nonneg.mpr hlo)]
    have hdiff := sub_le_sub_right hhi (plHeight mergeY (mergeHeights c M) x)
    linarith
  · have hgt : c < plHeight mergeY (mergeHeights c M) x := lt_of_not_ge hle
    rw [(hγ t).2 hgt, sub_self, abs_zero]
    exact hB0

/-- The two height sections form a height-preserving map pair with parameter `b / 2`. -/
def mergeFoldHeightMapPair {a b M : ℝ} (ha : 0 < a) (hab : a < b) (hbM : b ≤ M) :
    TDA.Reeb.HeightMapPair (plHeight mergeY (mergeHeights a M))
      (plHeight mergeY (mergeHeights b M)) (⟨b / 2, by linarith [ha, hab]⟩ : ℝ≥0) := by
  let hb : 0 < b := ha.trans hab
  let haM : a ≤ M := hab.le.trans hbM
  let ε : ℝ≥0 := ⟨b / 2, by linarith⟩
  have hsum : ((ε + ε : ℝ≥0) : ℝ) = b := by
    rw [NNReal.coe_add]
    change b / 2 + b / 2 = b
    ring
  refine {
    φ := (mergeSection b M hb hbM).comp (plHeight mergeY (mergeHeights a M))
    ψ := (mergeSection a M ha haM).comp (plHeight mergeY (mergeHeights b M))
    hφ := ?_
    hψ := ?_
    hψφ := ?_
    hφψ := ?_ }
  · intro x
    change |plHeight mergeY (mergeHeights b M)
        (mergeSection b M hb hbM (plHeight mergeY (mergeHeights a M) x)) -
      plHeight mergeY (mergeHeights a M) x| ≤ (ε : ℝ)
    rw [plHeight_mergeSection b M hb hbM
      (mergeFoldHeight_mem_Icc a M ha.le haM x)]
    simp
  · intro y
    change |plHeight mergeY (mergeHeights a M)
        (mergeSection a M ha haM (plHeight mergeY (mergeHeights b M) y)) -
      plHeight mergeY (mergeHeights b M) y| ≤ (ε : ℝ)
    rw [plHeight_mergeSection a M ha haM
      (mergeFoldHeight_mem_Icc b M hb.le hbM y)]
    simp
  · intro x
    obtain ⟨γ, hγ⟩ := exists_mergeSection_path a M ha haM x
    have htarget :
        (mergeSection a M ha haM).comp (plHeight mergeY (mergeHeights b M))
            ((mergeSection b M hb hbM).comp (plHeight mergeY (mergeHeights a M)) x) =
          mergeSection a M ha haM (plHeight mergeY (mergeHeights a M) x) := by
      change mergeSection a M ha haM
          (plHeight mergeY (mergeHeights b M)
            (mergeSection b M hb hbM (plHeight mergeY (mergeHeights a M) x))) = _
      rw [plHeight_mergeSection b M hb hbM
        (mergeFoldHeight_mem_Icc a M ha.le haM x)]
    refine ⟨γ.cast rfl htarget, ?_⟩
    intro t
    have hbound := mergeFoldPath_deviation_le a b M ha haM hab.le x γ hγ t
    have hcast := castPath_apply γ rfl htarget t
    change |plHeight mergeY (mergeHeights a M) (γ.cast rfl htarget t) -
      plHeight mergeY (mergeHeights a M) x| ≤
        ((ε + ε : ℝ≥0) : ℝ)
    rw [hcast, hsum]
    exact hbound
  · intro y
    obtain ⟨γ, hγ⟩ := exists_mergeSection_path b M hb hbM y
    have htarget :
        (mergeSection b M hb hbM).comp (plHeight mergeY (mergeHeights a M))
            ((mergeSection a M ha haM).comp (plHeight mergeY (mergeHeights b M)) y) =
          mergeSection b M hb hbM (plHeight mergeY (mergeHeights b M) y) := by
      change mergeSection b M hb hbM
          (plHeight mergeY (mergeHeights a M)
            (mergeSection a M ha haM (plHeight mergeY (mergeHeights b M) y))) = _
      rw [plHeight_mergeSection a M ha haM
        (mergeFoldHeight_mem_Icc b M hb.le hbM y)]
    refine ⟨γ.cast rfl htarget, ?_⟩
    intro t
    have hbound := mergeFoldPath_deviation_le b b M hb hbM le_rfl y γ hγ t
    have hcast := castPath_apply γ rfl htarget t
    change |plHeight mergeY (mergeHeights b M) (γ.cast rfl htarget t) -
      plHeight mergeY (mergeHeights b M) y| ≤
        ((ε + ε : ℝ≥0) : ℝ)
    rw [hcast, hsum]
    exact hbound

/-- The geometric Reeb distance of the merge-height trees is the smaller of the apex shift and
half the higher apex. -/
theorem geometricInterleavingDistance_mergeY_eq_min {a b M : ℝ}
    (ha : 0 < a) (hab : a < b) (hbM : b ≤ M) :
    geometricInterleavingDistance (graphPLReebGraph mergeY (mergeHeights a M))
      (graphPLReebGraph mergeY (mergeHeights b M)) =
        ENNReal.ofReal (min (b - a) (b / 2)) := by
  have hbudget :
      geometricInterleavingDistance (graphPLReebGraph mergeY (mergeHeights a M))
        (graphPLReebGraph mergeY (mergeHeights b M)) ≤ ENNReal.ofReal (b - a) := by
    rw [← edist_mergeHeights hab.le]
    exact geometricInterleavingDistance_graphPLReebGraph_le_edist mergeY _ _
  have hfold := geometricInterleavingDistance_graphPLReebGraph_le_of_heightMapPair
    (mergeFoldHeightMapPair ha hab hbM)
  have hfold' :
      geometricInterleavingDistance (graphPLReebGraph mergeY (mergeHeights a M))
        (graphPLReebGraph mergeY (mergeHeights b M)) ≤ ENNReal.ofReal (b / 2) := by
    have hconvert : ENNReal.ofReal (b / 2) =
        ENNReal.ofNNReal (⟨b / 2, by linarith [ha, hab]⟩ : ℝ≥0) := by
      rw [ENNReal.ofReal_eq_coe_nnreal (by linarith [ha, hab])]
      rfl
    rw [hconvert]
    exact hfold
  have hupper :
      geometricInterleavingDistance (graphPLReebGraph mergeY (mergeHeights a M))
        (graphPLReebGraph mergeY (mergeHeights b M)) ≤
          ENNReal.ofReal (min (b - a) (b / 2)) := by
    rw [ENNReal.ofReal_min]
    exact le_min hbudget hfold'
  exact le_antisymm hupper
    (ofReal_min_le_geometricInterleavingDistance_mergeY ha hab hbM)

/-- For `0 < a` and `2a ≤ b ≤ M` (so `a < b`), the merge-height distance is `b / 2`. -/
theorem geometricInterleavingDistance_mergeY_eq_half {a b M : ℝ}
    (ha : 0 < a) (h2a : 2 * a ≤ b) (hbM : b ≤ M) :
    geometricInterleavingDistance (graphPLReebGraph mergeY (mergeHeights a M))
      (graphPLReebGraph mergeY (mergeHeights b M)) = ENNReal.ofReal (b / 2) := by
  have hab : a < b := by linarith
  rw [geometricInterleavingDistance_mergeY_eq_min ha hab hbM,
    min_eq_right (by linarith : b / 2 ≤ b - a)]

/-- For `2a < b`, the fold gives a strictly smaller value than the vertex-height budget. -/
theorem geometricInterleavingDistance_mergeY_lt_vertex_budget {a b M : ℝ}
    (ha : 0 < a) (h2a : 2 * a < b) (hbM : b ≤ M) :
    geometricInterleavingDistance (graphPLReebGraph mergeY (mergeHeights a M))
      (graphPLReebGraph mergeY (mergeHeights b M)) < ENNReal.ofReal (b - a) := by
  have hab : a < b := by linarith
  rw [geometricInterleavingDistance_mergeY_eq_min ha hab hbM,
    ENNReal.ofReal_min]
  rw [min_eq_right ((ENNReal.ofReal_le_ofReal_iff (by linarith : 0 ≤ b - a)).2
    (by linarith : b / 2 ≤ b - a))]
  exact ENNReal.ofReal_lt_ofReal_iff (by linarith : 0 < b - a) |>.2 (by linarith)

/-- Reflection gives the exact formula for the split-height tree. -/
theorem geometricInterleavingDistance_splitY_eq_min {a b M : ℝ}
    (ha : 0 < a) (hab : a < b) (hbM : b ≤ M) :
    geometricInterleavingDistance (graphPLReebGraph mergeY (splitHeights a M))
      (graphPLReebGraph mergeY (splitHeights b M)) =
        ENNReal.ofReal (min (b - a) (b / 2)) := by
  unfold splitHeights
  rw [geometricInterleavingDistance_graphPLReebGraph_neg]
  exact geometricInterleavingDistance_mergeY_eq_min ha hab hbM

end

end TDA.Mapper.GraphPL
