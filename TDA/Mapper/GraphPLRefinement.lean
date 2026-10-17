import TDA.Mapper.UniformMapperReebData
import TDA.Reeb.RGraphRefinement

/-!
# Refinement geometry for graph-PL finite Reeb data

This module records the level and edge geometry used to compare graph-PL finite Reeb data
over a critical list with the data obtained from a refinement of that list.  The graph-side
equivalences in this first section are elementary consequences of a covering list: a level in
an open gap has no level vertices, and crossing or spanning conditions agree on the underlying
graph edge.
-/

namespace TDA.Mapper.GraphPL

open Set SimpleGraph CategoryTheory
open TDA.Reeb TDA.Reeb.OpenInterval TDA.Reeb.GraphPL TDA.Reeb.GraphRealization

noncomputable section

universe u

variable {V : Type u} (G : SimpleGraph V) (h : V → ℝ)
  {n m l : ℕ} {S : CriticalValues n} {T : CriticalValues m} {U : CriticalValues l}

/-! ## Level geometry -/

/-- A point in the closed span of the extreme levels, which is not a level, lies in a gap. -/
theorem exists_mem_K_of_mem_Icc {x : ℝ}
    (hx : x ∈ Icc (S.value 0) (S.value (Fin.last n)))
    (hne : ∀ i, S.value i ≠ x) : ∃ e : Fin n, x ∈ (S.K e : Set ℝ) := by
  obtain ⟨p, hxp, hp⟩ := S.exists_piece x
  cases p with
  | star i => exact (hne i (hp i (S.value_mem_J i))).elim
  | gap e => exact ⟨e, hxp⟩
  | lowerTail => exact (not_lt_of_ge hx.1 (S.mem_lowerTail.1 hxp)).elim
  | upperTail => exact (not_lt_of_ge hx.2 (S.mem_upperTail.1 hxp)).elim

/-- A refined gap whose base point is exterior to the old extreme segment is exterior on one side. -/
theorem exterior_segment (hST : Set.range S.value ⊆ Set.range T.value) (k : Fin m)
    (hk : (RGraph.basePt T k : ℝ) ∉ Icc (S.value 0) (S.value (Fin.last n))) :
    T.value k.succ ≤ S.value 0 ∨ S.value (Fin.last n) ≤ T.value k.castSucc := by
  obtain ⟨i₀, hi₀⟩ := hST ⟨0, rfl⟩
  obtain ⟨iₙ, hiₙ⟩ := hST ⟨Fin.last n, rfl⟩
  have hleft : T.value k.castSucc < (RGraph.basePt T k : ℝ) := (RGraph.basePt T k).2.1
  have hright : (RGraph.basePt T k : ℝ) < T.value k.succ := (RGraph.basePt T k).2.2
  by_cases hbelow : (RGraph.basePt T k : ℝ) < S.value 0
  · left
    apply le_of_not_gt
    intro hlt
    apply T.value_notMem_K k i₀
    refine ⟨?_, ?_⟩
    · exact hleft.trans (hbelow.trans_eq hi₀.symm)
    · exact hi₀.trans_lt hlt
  · right
    have habove : S.value (Fin.last n) < (RGraph.basePt T k : ℝ) := by
      apply lt_of_not_ge
      intro hle
      exact hk ⟨le_of_not_gt hbelow, hle⟩
    apply le_of_not_gt
    intro hlt
    apply T.value_notMem_K k iₙ
    refine ⟨?_, ?_⟩
    · exact hlt.trans_eq hiₙ.symm
    · exact hiₙ.trans_lt (habove.trans hright)

/-! ## Covering and graph-side equivalences -/

/-- A list refining a covering list also covers all vertex heights. -/
theorem CoversVertexHeights.mono {h : V → ℝ} (hS : CoversVertexHeights S h)
    (hST : Set.range S.value ⊆ Set.range T.value) : CoversVertexHeights T h := by
  intro v
  obtain ⟨i, hi⟩ := hS v
  obtain ⟨j, hj⟩ := hST ⟨i, hi⟩
  exact ⟨j, hj⟩

/-- Transport a graph-PL level vertex across an equality of its real level. -/
def levelVertexEquivOfEq {c c' : ℝ} (hc : c = c') :
    LevelVertex G h c ≃ LevelVertex G h c' :=
  Equiv.cast (congrArg (LevelVertex G h) hc)

/-- The level transport equivalence is the identity when its equality is reflexive. -/
@[simp]
theorem levelVertexEquivOfEq_rfl (r : ℝ) :
    levelVertexEquivOfEq G h (c := r) (c' := r) rfl = Equiv.refl _ := rfl

@[simp]
private theorem levelVertexEquivOfEq_inl {c c' : ℝ} (hc : c = c') (v : V)
    (hv : h v = c) :
    levelVertexEquivOfEq G h hc
        (Sum.inl ((G.induce {v | h v = c}).connectedComponentMk ⟨v, hv⟩)) =
      Sum.inl ((G.induce {v | h v = c'}).connectedComponentMk ⟨v, hv.trans hc⟩) := by
  subst c'
  rfl

@[simp]
private theorem levelVertexEquivOfEq_inr {c c' : ℝ} (hc : c = c')
    (y : {e : G.edgeSet // EdgeCrosses G h c e}) :
    levelVertexEquivOfEq G h hc (Sum.inr y) =
      Sum.inr ⟨y.1, hc ▸ y.2⟩ := by
  subst c'
  rfl

private theorem basePt_mem_Icc (k : Fin m) :
    (RGraph.basePt T k : ℝ) ∈ Icc (T.value k.castSucc) (T.value k.succ) :=
  Ioo_subset_Icc_self (RGraph.basePt T k).2

private theorem mem_hull_of_covers (hS : CoversVertexHeights S h) (v : V) :
    h v ∈ Icc (S.value 0) (S.value (Fin.last n)) := by
  obtain ⟨i, hi⟩ := hS v
  rw [← hi]
  exact ⟨S.strictMono.monotone (Fin.zero_le i),
    S.strictMono.monotone (Fin.le_last i)⟩

private theorem edgeCrosses_iff_span_of_mem_K (hS : CoversVertexHeights S h) (e : Fin n)
    {c : ℝ} (hc : c ∈ (S.K e : Set ℝ)) (x : G.edgeSet) :
    EdgeCrosses G h c x ↔
      EdgeSpans G h (S.value e.castSucc) (S.value e.succ) x := by
  obtain ⟨d, rfl⟩ := exists_dartEdge_eq x
  rw [edgeCrosses_dartEdge_iff, edgeSpans_dartEdge_iff]
  have hK := S.mem_K.1 hc
  constructor
  · intro hcross
    have hmin : min (h d.fst) (h d.snd) ≤ S.value e.castSucc := by
      by_contra ha
      have ha' : S.value e.castSucc < min (h d.fst) (h d.snd) := lt_of_not_ge ha
      rcases min_choice (h d.fst) (h d.snd) with hm | hm
      · exact hS.notMem_K e d.fst
          ⟨ha'.trans_eq hm, hm.symm.trans_lt (hcross.1.trans hK.2)⟩
      · exact hS.notMem_K e d.snd
          ⟨ha'.trans_eq hm, hm.symm.trans_lt (hcross.1.trans hK.2)⟩
    have hmax : S.value e.succ ≤ max (h d.fst) (h d.snd) := by
      by_contra hb
      have hb' : max (h d.fst) (h d.snd) < S.value e.succ := lt_of_not_ge hb
      rcases max_choice (h d.fst) (h d.snd) with hm | hm
      · exact hS.notMem_K e d.fst
          ⟨hK.1.trans (hcross.2.trans_eq hm), hm.symm.trans_lt hb'⟩
      · exact hS.notMem_K e d.snd
          ⟨hK.1.trans (hcross.2.trans_eq hm), hm.symm.trans_lt hb'⟩
    exact ⟨hmin, hmax⟩
  · rintro ⟨hmin, hmax⟩
    exact ⟨hmin.trans_lt hK.1, hK.2.trans_le hmax⟩

/-- A graph-PL level in an old open gap is equivalent to the spanning-edge type of that gap. -/
def levelVertexEquivSpanOfMemK (hS : CoversVertexHeights S h) (e : Fin n) {c : ℝ}
    (hc : c ∈ (S.K e : Set ℝ)) :
    LevelVertex G h c ≃ SpanEdge G h (S.value e.castSucc) (S.value e.succ) := by
  haveI : IsEmpty (G.induce {v | h v = c}).ConnectedComponent :=
    ⟨fun z => by
      induction z using ConnectedComponent.ind with
      | h v => exact hS.notMem_K e v.1 (by rw [v.2]; exact hc)⟩
  exact (Equiv.emptySum _ _).trans
    (Equiv.subtypeEquivRight (edgeCrosses_iff_span_of_mem_K G h hS e hc))

/-- The graph-side gap equivalence fixes the underlying edge of a crossing vertex. -/
@[simp]
theorem levelVertexEquivSpanOfMemK_inr (hS : CoversVertexHeights S h) (e : Fin n)
    {c : ℝ} (hc : c ∈ (S.K e : Set ℝ))
    (y : {e : G.edgeSet // EdgeCrosses G h c e}) :
    levelVertexEquivSpanOfMemK G h hS e hc (Sum.inr y) =
      ⟨y.1, (edgeCrosses_iff_span_of_mem_K G h hS e hc y.1).mp y.2⟩ := rfl

/-- A spanning edge over a subsegment of an old gap is equivalent to the old spanning-edge type. -/
def spanEdgeEquivOfSubset (hS : CoversVertexHeights S h) (e : Fin n) {p q : ℝ}
    (hpq : p < q)
    (hsub : Icc p q ⊆ Icc (S.value e.castSucc) (S.value e.succ)) :
    SpanEdge G h p q ≃ SpanEdge G h (S.value e.castSucc) (S.value e.succ) := by
  apply Equiv.subtypeEquivRight
  intro x
  obtain ⟨d, rfl⟩ := exists_dartEdge_eq x
  rw [edgeSpans_dartEdge_iff, edgeSpans_dartEdge_iff]
  have hpa : S.value e.castSucc ≤ p := (hsub ⟨le_rfl, hpq.le⟩).1
  have hqb : q ≤ S.value e.succ := (hsub ⟨hpq.le, le_rfl⟩).2
  constructor
  · rintro ⟨hmin, hmax⟩
    have hmin' : min (h d.fst) (h d.snd) ≤ S.value e.castSucc := by
      by_contra ha
      have ha' : S.value e.castSucc < min (h d.fst) (h d.snd) := lt_of_not_ge ha
      have hlt : min (h d.fst) (h d.snd) < S.value e.succ :=
        hmin.trans_lt (hpq.trans_le hqb)
      rcases min_choice (h d.fst) (h d.snd) with hm | hm
      · exact hS.notMem_K e d.fst
          ⟨ha'.trans_eq hm, hm.symm.trans_lt hlt⟩
      · exact hS.notMem_K e d.snd
          ⟨ha'.trans_eq hm, hm.symm.trans_lt hlt⟩
    have hmax' : S.value e.succ ≤ max (h d.fst) (h d.snd) := by
      by_contra hb
      have hb' : max (h d.fst) (h d.snd) < S.value e.succ := lt_of_not_ge hb
      have hlt : S.value e.castSucc < max (h d.fst) (h d.snd) :=
        hpa.trans_lt (hpq.trans_le hmax)
      rcases max_choice (h d.fst) (h d.snd) with hm | hm
      · exact hS.notMem_K e d.fst
          ⟨hlt.trans_eq hm, hm.symm.trans_lt hb'⟩
      · exact hS.notMem_K e d.snd
          ⟨hlt.trans_eq hm, hm.symm.trans_lt hb'⟩
    exact ⟨hmin', hmax'⟩
  · rintro ⟨hmin, hmax⟩
    exact ⟨hmin.trans hpa, hqb.trans hmax⟩

/-- The subsegment equivalence fixes the underlying graph edge. -/
@[simp]
theorem spanEdgeEquivOfSubset_apply_coe (hS : CoversVertexHeights S h) (e : Fin n)
    {p q : ℝ} (hpq : p < q)
    (hsub : Icc p q ⊆ Icc (S.value e.castSucc) (S.value e.succ))
    (y : SpanEdge G h p q) :
    ((spanEdgeEquivOfSubset G h hS e hpq hsub y :
      SpanEdge G h (S.value e.castSucc) (S.value e.succ)) : G.edgeSet) = y.1 := rfl

/-- A covered graph-PL level outside the old extreme segment has no level vertices. -/
theorem isEmpty_levelVertex_of_notMem_Icc (hS : CoversVertexHeights S h) {c : ℝ}
    (hc : c ∉ Icc (S.value 0) (S.value (Fin.last n))) :
    IsEmpty (LevelVertex G h c) := by
  have hcomp : IsEmpty (G.induce {v | h v = c}).ConnectedComponent :=
    ⟨fun z => by
      induction z using ConnectedComponent.ind with
      | h v =>
        have hvc : h v.1 = c := v.2
        have hv := mem_hull_of_covers (S := S) (h := h) hS v.1
        rw [hvc] at hv
        exact hc hv⟩
  have hcross : IsEmpty {e : G.edgeSet // EdgeCrosses G h c e} :=
    ⟨fun z => by
      rcases z.2 with ⟨d, _, hmin, hmax⟩
      have hfst := mem_hull_of_covers (S := S) (h := h) hS d.fst
      have hsnd := mem_hull_of_covers (S := S) (h := h) hS d.snd
      apply hc
      exact ⟨((le_min hfst.1 hsnd.1).trans_lt hmin).le,
        (hmax.trans_le (max_le hfst.2 hsnd.2)).le⟩⟩
  exact ⟨fun z => by
    cases z with
    | inl z => exact hcomp.false z
    | inr z => exact hcross.false z⟩

/-- A covered graph-PL spanning-edge type is empty when its whole interval is exterior. -/
theorem isEmpty_spanEdge_of_exterior (hS : CoversVertexHeights S h) {p q : ℝ} (hpq : p < q)
    (hout : q ≤ S.value 0 ∨ S.value (Fin.last n) ≤ p) :
    IsEmpty (SpanEdge G h p q) := by
  exact ⟨fun z => by
    rcases z.2 with ⟨d, _, hmin, hmax⟩
    have hfst := mem_hull_of_covers (S := S) (h := h) hS d.fst
    have hsnd := mem_hull_of_covers (S := S) (h := h) hS d.snd
    have hlow : S.value 0 ≤ min (h d.fst) (h d.snd) := le_min hfst.1 hsnd.1
    have hupp : max (h d.fst) (h d.snd) ≤ S.value (Fin.last n) :=
      max_le hfst.2 hsnd.2
    rcases hout with hout | hout
    · exact (not_lt_of_ge (hlow.trans hmin)) (hpq.trans_le hout)
    · exact (not_lt_of_ge hout) (hpq.trans_le (hmax.trans hupp))⟩

/-! ## Refinement homomorphism -/

private theorem value_exterior_of_not_old_not_gap
    (j : Fin (m + 1))
    (hi : ¬ ∃ i, T.value j = S.value i)
    (he : ¬ ∃ e, T.value j ∈ (S.K e : Set ℝ)) :
    T.value j ∉ Icc (S.value 0) (S.value (Fin.last n)) := by
  intro hx
  obtain ⟨e, he'⟩ := exists_mem_K_of_mem_Icc hx (fun i h => hi ⟨i, h.symm⟩)
  exact he ⟨e, he'⟩

private theorem basePt_exterior_of_not_gap
    (hST : Set.range S.value ⊆ Set.range T.value) (k : Fin m)
    (he : ¬ ∃ e, (RGraph.basePt T k : ℝ) ∈ (S.K e : Set ℝ)) :
    (RGraph.basePt T k : ℝ) ∉ Icc (S.value 0) (S.value (Fin.last n)) := by
  intro hx
  obtain ⟨e, he'⟩ := exists_mem_K_of_mem_Icc hx
    (fun i h => RGraph.value_ne hST (RGraph.basePt T k).2 i h)
  exact he ⟨e, he'⟩

private theorem endpoint_mem_K_left
    (hST : Set.range S.value ⊆ Set.range T.value) (k : Fin m) (e : Fin n)
    (he : (RGraph.basePt T k : ℝ) ∈ (S.K e : Set ℝ))
    (hold : ¬ ∃ i, T.value k.castSucc = S.value i) :
    T.value k.castSucc ∈ (S.K e : Set ℝ) := by
  apply RGraph.mem_K_of_ne
    (RGraph.Icc_subset_of_mem hST (basePt_mem_Icc (T := T) k) he
      (left_mem_Icc.2 (T.value_castSucc_lt_succ k).le))
  intro i hi
  exact hold ⟨i, hi.symm⟩

private theorem endpoint_mem_K_right
    (hST : Set.range S.value ⊆ Set.range T.value) (k : Fin m) (e : Fin n)
    (he : (RGraph.basePt T k : ℝ) ∈ (S.K e : Set ℝ))
    (hold : ¬ ∃ i, T.value k.succ = S.value i) :
    T.value k.succ ∈ (S.K e : Set ℝ) := by
  apply RGraph.mem_K_of_ne
    (RGraph.Icc_subset_of_mem hST (basePt_mem_Icc (T := T) k) he
      (right_mem_Icc.2 (T.value_castSucc_lt_succ k).le))
  intro i hi
  exact hold ⟨i, hi.symm⟩

private noncomputable def graphPLRefineV [Finite V]
    (hS : CoversVertexHeights S h)
    (hST : Set.range S.value ⊆ Set.range T.value) (j : Fin (m + 1)) :
    LevelVertex G h (T.value j) →
      (RGraph.refineData hST (graphPLReebData G h S)).V j := fun x => by
  classical
  by_cases hi : ∃ i, T.value j = S.value i
  · exact (RGraph.refineVEquivOld hST (graphPLReebData G h S) j hi.choose
      hi.choose_spec).symm (levelVertexEquivOfEq G h hi.choose_spec x)
  · by_cases he : ∃ e, T.value j ∈ (S.K e : Set ℝ)
    · exact (RGraph.refineVEquiv hST (graphPLReebData G h S) j he.choose
        he.choose_spec).symm
        (levelVertexEquivSpanOfMemK G h hS he.choose he.choose_spec x)
    · have hout := value_exterior_of_not_old_not_gap (S := S) (T := T) j hi he
      letI := isEmpty_levelVertex_of_notMem_Icc G h hS hout
      exact isEmptyElim x

private noncomputable def graphPLRefineE [Finite V]
    (hS : CoversVertexHeights S h)
    (hST : Set.range S.value ⊆ Set.range T.value) (k : Fin m) :
    SpanEdge G h (T.value k.castSucc) (T.value k.succ) →
      (RGraph.refineData hST (graphPLReebData G h S)).E k := fun y => by
  classical
  by_cases he : ∃ e, (RGraph.basePt T k : ℝ) ∈ (S.K e : Set ℝ)
  · exact (RGraph.refineEEquiv hST (graphPLReebData G h S) k he.choose
      he.choose_spec).symm
      (spanEdgeEquivOfSubset G h hS he.choose (T.value_castSucc_lt_succ k)
        (RGraph.Icc_subset_of_mem hST (basePt_mem_Icc (T := T) k)
          he.choose_spec) y)
  · have hout := basePt_exterior_of_not_gap (S := S) (T := T) hST k he
    letI := isEmpty_spanEdge_of_exterior G h hS (T.value_castSucc_lt_succ k)
      (exterior_segment hST k hout)
    exact isEmptyElim y

private theorem graphPLRefineV_old [Finite V]
    (hS : CoversVertexHeights S h)
    (hST : Set.range S.value ⊆ Set.range T.value) (j : Fin (m + 1)) (i : Fin (n + 1))
    (hi : T.value j = S.value i) (x : LevelVertex G h (T.value j)) :
    graphPLRefineV G h hS hST j x =
      (RGraph.refineVEquivOld hST (graphPLReebData G h S) j i hi).symm
        (levelVertexEquivOfEq G h hi x) := by
  classical
  unfold graphPLRefineV
  rw [dif_pos ⟨i, hi⟩]
  have hchoose : Classical.choose (⟨i, hi⟩ : ∃ i, T.value j = S.value i) = i := by
    apply S.strictMono.injective
    calc
      S.value (Classical.choose (⟨i, hi⟩ : ∃ i, T.value j = S.value i)) = T.value j :=
        (Classical.choose_spec (⟨i, hi⟩ : ∃ i, T.value j = S.value i)).symm
      _ = S.value i := hi
  have key : ∀ (i' : Fin (n + 1)) (hi' : T.value j = S.value i'), i' = i →
      (RGraph.refineVEquivOld hST (graphPLReebData G h S) j i' hi').symm
          (levelVertexEquivOfEq G h hi' x) =
        (RGraph.refineVEquivOld hST (graphPLReebData G h S) j i hi).symm
          (levelVertexEquivOfEq G h hi x) := by
    rintro _ _ rfl
    rfl
  exact key _ _ hchoose

private theorem graphPLRefineV_inserted [Finite V]
    (hS : CoversVertexHeights S h)
    (hST : Set.range S.value ⊆ Set.range T.value) (j : Fin (m + 1)) (e : Fin n)
    (he : T.value j ∈ (S.K e : Set ℝ)) (x : LevelVertex G h (T.value j)) :
    graphPLRefineV G h hS hST j x =
      (RGraph.refineVEquiv hST (graphPLReebData G h S) j e he).symm
        (levelVertexEquivSpanOfMemK G h hS e he x) := by
  classical
  have hnot : ¬ ∃ i, T.value j = S.value i := by
    rintro ⟨i, hi⟩
    exact S.value_notMem_K e i (hi ▸ he)
  unfold graphPLRefineV
  rw [dif_neg hnot, dif_pos ⟨e, he⟩]
  have hchoose : Classical.choose (⟨e, he⟩ : ∃ e, T.value j ∈ (S.K e : Set ℝ)) = e := by
    exact S.eq_of_mem_K_of_mem_Icc
      (Classical.choose_spec (⟨e, he⟩ : ∃ e, T.value j ∈ (S.K e : Set ℝ)))
      (Ioo_subset_Icc_self he)
  have key : ∀ (e' : Fin n) (he' : T.value j ∈ (S.K e' : Set ℝ)), e' = e →
      (RGraph.refineVEquiv hST (graphPLReebData G h S) j e' he').symm
          (levelVertexEquivSpanOfMemK G h hS e' he' x) =
        (RGraph.refineVEquiv hST (graphPLReebData G h S) j e he).symm
          (levelVertexEquivSpanOfMemK G h hS e he x) := by
    rintro _ _ rfl
    rfl
  exact key _ _ hchoose

private theorem graphPLRefineE_mem [Finite V]
    (hS : CoversVertexHeights S h)
    (hST : Set.range S.value ⊆ Set.range T.value) (k : Fin m) (e : Fin n)
    (he : (RGraph.basePt T k : ℝ) ∈ (S.K e : Set ℝ))
    (y : SpanEdge G h (T.value k.castSucc) (T.value k.succ)) :
    graphPLRefineE G h hS hST k y =
      (RGraph.refineEEquiv hST (graphPLReebData G h S) k e he).symm
        (spanEdgeEquivOfSubset G h hS e (T.value_castSucc_lt_succ k)
          (RGraph.Icc_subset_of_mem hST (basePt_mem_Icc (T := T) k) he) y) := by
  classical
  unfold graphPLRefineE
  rw [dif_pos ⟨e, he⟩]
  have hchoose : Classical.choose
      (⟨e, he⟩ : ∃ e, (RGraph.basePt T k : ℝ) ∈ (S.K e : Set ℝ)) = e := by
    exact S.eq_of_mem_K_of_mem_Icc
      (Classical.choose_spec
        (⟨e, he⟩ : ∃ e, (RGraph.basePt T k : ℝ) ∈ (S.K e : Set ℝ)))
      (Ioo_subset_Icc_self he)
  have key : ∀ (e' : Fin n) (he' : (RGraph.basePt T k : ℝ) ∈ (S.K e' : Set ℝ)), e' = e →
      (RGraph.refineEEquiv hST (graphPLReebData G h S) k e' he').symm
          (spanEdgeEquivOfSubset G h hS e' (T.value_castSucc_lt_succ k)
            (RGraph.Icc_subset_of_mem hST (basePt_mem_Icc (T := T) k) he') y) =
        (RGraph.refineEEquiv hST (graphPLReebData G h S) k e he).symm
          (spanEdgeEquivOfSubset G h hS e (T.value_castSucc_lt_succ k)
            (RGraph.Icc_subset_of_mem hST (basePt_mem_Icc (T := T) k) he) y) := by
    rintro _ _ rfl
    rfl
  exact key _ _ hchoose

private theorem graphPL_left_old [Finite V]
    (hS : CoversVertexHeights S h)
    (hST : Set.range S.value ⊆ Set.range T.value) (k : Fin m) (e : Fin n)
    (he : (RGraph.basePt T k : ℝ) ∈ (S.K e : Set ℝ))
    (hi : T.value k.castSucc = S.value e.castSucc)
    (y : SpanEdge G h (T.value k.castSucc) (T.value k.succ)) :
    (graphPLReebData G h S).left e
        (spanEdgeEquivOfSubset G h hS e (T.value_castSucc_lt_succ k)
          (RGraph.Icc_subset_of_mem hST (basePt_mem_Icc (T := T) k) he) y) =
      levelVertexEquivOfEq G h hi ((graphPLReebData G h T).left k y) := by
  let z := spanEdgeEquivOfSubset G h hS e (T.value_castSucc_lt_succ k)
    (RGraph.Icc_subset_of_mem hST (basePt_mem_Icc (T := T) k) he) y
  have hzcoe : (z.1 : G.edgeSet) = y.1 := by
    exact spanEdgeEquivOfSubset_apply_coe G h hS e (T.value_castSucc_lt_succ k)
      (RGraph.Icc_subset_of_mem hST (basePt_mem_Icc (T := T) k) he) y
  by_cases hv : ∃ v ∈ (y.1 : Sym2 V), h v = T.value k.castSucc
  · obtain ⟨v, hvy, hv⟩ := hv
    have hvz : v ∈ (z.1 : Sym2 V) := by rw [hzcoe]; exact hvy
    have hv' : h v = S.value e.castSucc := hv.trans hi
    rw [graphPLReebData_left_of_mem G h T k y hvy hv,
      graphPLReebData_left_of_mem G h S e z hvz hv']
    rw [levelVertexEquivOfEq_inl]
  · have hvz : ∀ v ∈ (z.1 : Sym2 V), h v ≠ S.value e.castSucc := by
      intro v hvz hv'
      apply hv
      refine ⟨v, ?_, hv'.trans hi.symm⟩
      rw [← hzcoe]
      exact hvz
    rw [graphPLReebData_left_of_forall_ne G h T k y
        (fun v hvy hv' => hv ⟨v, hvy, hv'⟩),
      graphPLReebData_left_of_forall_ne G h S e z hvz]
    rw [levelVertexEquivOfEq_inr]
    rfl

private theorem graphPL_right_old [Finite V]
    (hS : CoversVertexHeights S h)
    (hST : Set.range S.value ⊆ Set.range T.value) (k : Fin m) (e : Fin n)
    (he : (RGraph.basePt T k : ℝ) ∈ (S.K e : Set ℝ))
    (hi : T.value k.succ = S.value e.succ)
    (y : SpanEdge G h (T.value k.castSucc) (T.value k.succ)) :
    (graphPLReebData G h S).right e
        (spanEdgeEquivOfSubset G h hS e (T.value_castSucc_lt_succ k)
          (RGraph.Icc_subset_of_mem hST (basePt_mem_Icc (T := T) k) he) y) =
      levelVertexEquivOfEq G h hi ((graphPLReebData G h T).right k y) := by
  let z := spanEdgeEquivOfSubset G h hS e (T.value_castSucc_lt_succ k)
    (RGraph.Icc_subset_of_mem hST (basePt_mem_Icc (T := T) k) he) y
  have hzcoe : (z.1 : G.edgeSet) = y.1 := by
    exact spanEdgeEquivOfSubset_apply_coe G h hS e (T.value_castSucc_lt_succ k)
      (RGraph.Icc_subset_of_mem hST (basePt_mem_Icc (T := T) k) he) y
  by_cases hv : ∃ v ∈ (y.1 : Sym2 V), h v = T.value k.succ
  · obtain ⟨v, hvy, hv⟩ := hv
    have hvz : v ∈ (z.1 : Sym2 V) := by rw [hzcoe]; exact hvy
    have hv' : h v = S.value e.succ := hv.trans hi
    rw [graphPLReebData_right_of_mem G h T k y hvy hv,
      graphPLReebData_right_of_mem G h S e z hvz hv']
    rw [levelVertexEquivOfEq_inl]
  · have hvz : ∀ v ∈ (z.1 : Sym2 V), h v ≠ S.value e.succ := by
      intro v hvz hv'
      apply hv
      refine ⟨v, ?_, hv'.trans hi.symm⟩
      rw [← hzcoe]
      exact hvz
    rw [graphPLReebData_right_of_forall_ne G h T k y
        (fun v hvy hv' => hv ⟨v, hvy, hv'⟩),
      graphPLReebData_right_of_forall_ne G h S e z hvz]
    rw [levelVertexEquivOfEq_inr]
    rfl

private theorem refineEEquiv_graphPLRefineE [Finite V]
    (hS : CoversVertexHeights S h)
    (hST : Set.range S.value ⊆ Set.range T.value) (k : Fin m) (e : Fin n)
    (he : (RGraph.basePt T k : ℝ) ∈ (S.K e : Set ℝ))
    (y : SpanEdge G h (T.value k.castSucc) (T.value k.succ)) :
    RGraph.refineEEquiv hST (graphPLReebData G h S) k e he
        (graphPLRefineE G h hS hST k y) =
      (spanEdgeEquivOfSubset G h hS e (T.value_castSucc_lt_succ k)
        (RGraph.Icc_subset_of_mem hST (basePt_mem_Icc (T := T) k) he) y :
        (graphPLReebData G h S).E e) := by
  exact
    (congrArg (RGraph.refineEEquiv hST (graphPLReebData G h S) k e he)
      (graphPLRefineE_mem G h hS hST k e he y)).trans
      (Equiv.apply_symm_apply _ _)

private theorem graphPLRefine_left_comm [Finite V]
    (hS : CoversVertexHeights S h)
    (hST : Set.range S.value ⊆ Set.range T.value) (k : Fin m)
    (y : SpanEdge G h (T.value k.castSucc) (T.value k.succ)) :
    (RGraph.refineData hST (graphPLReebData G h S)).left k
        (graphPLRefineE G h hS hST k y) =
      graphPLRefineV G h hS hST k.castSucc ((graphPLReebData G h T).left k y) := by
  classical
  by_cases hbase : ∃ e, (RGraph.basePt T k : ℝ) ∈ (S.K e : Set ℝ)
  · obtain ⟨e, he⟩ := hbase
    by_cases hold : ∃ i, T.value k.castSucc = S.value i
    · obtain ⟨i, hi⟩ := hold
      have hindex := RGraph.old_level_castSucc hST k e he i hi
      subst i
      apply (RGraph.refineVEquivOld hST (graphPLReebData G h S) k.castSucc e.castSucc hi).injective
      refine (RGraph.refine_left_old hST (graphPLReebData G h S) k e he hi _).trans ?_
      refine (congrArg ((graphPLReebData G h S).left e)
        (refineEEquiv_graphPLRefineE G h hS hST k e he y)).trans ?_
      refine (graphPL_left_old G h hS hST k e he hi y).trans ?_
      exact ((congrArg
          (RGraph.refineVEquivOld hST (graphPLReebData G h S) k.castSucc e.castSucc hi)
          (graphPLRefineV_old G h hS hST k.castSucc e.castSucc hi
            ((graphPLReebData G h T).left k y))).trans (Equiv.apply_symm_apply _ _)).symm
    · have he' := endpoint_mem_K_left hST k e he hold
      apply (RGraph.refineVEquiv hST (graphPLReebData G h S) k.castSucc e he').injective
      have hne : ∀ v ∈ (y.1 : Sym2 V), h v ≠ T.value k.castSucc := by
        intro v hv hv'
        exact hS.notMem_K e v (by rw [hv']; exact he')
      refine (RGraph.refine_left_eq hST (graphPLReebData G h S) k e he' _).trans ?_
      refine (refineEEquiv_graphPLRefineE G h hS hST k e he y).trans ?_
      refine Eq.trans ?_ ((congrArg
          (RGraph.refineVEquiv hST (graphPLReebData G h S) k.castSucc e he')
          (graphPLRefineV_inserted G h hS hST k.castSucc e he'
            ((graphPLReebData G h T).left k y))).trans (Equiv.apply_symm_apply _ _)).symm
      refine Eq.trans ?_ (congrArg (levelVertexEquivSpanOfMemK G h hS e he')
        (graphPLReebData_left_of_forall_ne G h T k y hne)).symm
      refine Eq.trans ?_ (levelVertexEquivSpanOfMemK_inr G h hS e he'
        ⟨y.1, y.2.crosses_left (T.value_castSucc_lt_succ k) hne⟩).symm
      exact Subtype.ext (spanEdgeEquivOfSubset_apply_coe G h hS e
        (T.value_castSucc_lt_succ k)
        (RGraph.Icc_subset_of_mem hST (basePt_mem_Icc (T := T) k) he) y)
  · have hout := basePt_exterior_of_not_gap hST k hbase
    exact ((isEmpty_spanEdge_of_exterior G h hS (T.value_castSucc_lt_succ k)
      (exterior_segment hST k hout)).false y).elim

private theorem graphPLRefine_right_comm [Finite V]
    (hS : CoversVertexHeights S h)
    (hST : Set.range S.value ⊆ Set.range T.value) (k : Fin m)
    (y : SpanEdge G h (T.value k.castSucc) (T.value k.succ)) :
    (RGraph.refineData hST (graphPLReebData G h S)).right k
        (graphPLRefineE G h hS hST k y) =
      graphPLRefineV G h hS hST k.succ ((graphPLReebData G h T).right k y) := by
  classical
  by_cases hbase : ∃ e, (RGraph.basePt T k : ℝ) ∈ (S.K e : Set ℝ)
  · obtain ⟨e, he⟩ := hbase
    by_cases hold : ∃ i, T.value k.succ = S.value i
    · obtain ⟨i, hi⟩ := hold
      have hindex := RGraph.old_level_succ hST k e he i hi
      subst i
      apply (RGraph.refineVEquivOld hST (graphPLReebData G h S) k.succ e.succ hi).injective
      refine (RGraph.refine_right_old hST (graphPLReebData G h S) k e he hi _).trans ?_
      refine (congrArg ((graphPLReebData G h S).right e)
        (refineEEquiv_graphPLRefineE G h hS hST k e he y)).trans ?_
      refine (graphPL_right_old G h hS hST k e he hi y).trans ?_
      exact ((congrArg
          (RGraph.refineVEquivOld hST (graphPLReebData G h S) k.succ e.succ hi)
          (graphPLRefineV_old G h hS hST k.succ e.succ hi
            ((graphPLReebData G h T).right k y))).trans (Equiv.apply_symm_apply _ _)).symm
    · have he' := endpoint_mem_K_right hST k e he hold
      apply (RGraph.refineVEquiv hST (graphPLReebData G h S) k.succ e he').injective
      have hne : ∀ v ∈ (y.1 : Sym2 V), h v ≠ T.value k.succ := by
        intro v hv hv'
        exact hS.notMem_K e v (by rw [hv']; exact he')
      refine (RGraph.refine_right_eq hST (graphPLReebData G h S) k e he' _).trans ?_
      refine (refineEEquiv_graphPLRefineE G h hS hST k e he y).trans ?_
      refine Eq.trans ?_ ((congrArg
          (RGraph.refineVEquiv hST (graphPLReebData G h S) k.succ e he')
          (graphPLRefineV_inserted G h hS hST k.succ e he'
            ((graphPLReebData G h T).right k y))).trans (Equiv.apply_symm_apply _ _)).symm
      refine Eq.trans ?_ (congrArg (levelVertexEquivSpanOfMemK G h hS e he')
        (graphPLReebData_right_of_forall_ne G h T k y hne)).symm
      refine Eq.trans ?_ (levelVertexEquivSpanOfMemK_inr G h hS e he'
        ⟨y.1, y.2.crosses_right (T.value_castSucc_lt_succ k) hne⟩).symm
      exact Subtype.ext (spanEdgeEquivOfSubset_apply_coe G h hS e
        (T.value_castSucc_lt_succ k)
        (RGraph.Icc_subset_of_mem hST (basePt_mem_Icc (T := T) k) he) y)
  · have hout := basePt_exterior_of_not_gap hST k hbase
    exact ((isEmpty_spanEdge_of_exterior G h hS (T.value_castSucc_lt_succ k)
      (exterior_segment hST k hout)).false y).elim

/-- The finite-data homomorphism from graph-PL data over `T` to its `S`-refinement. -/
def graphPLRefineHom [Finite V]
    (hS : CoversVertexHeights S h)
    (hST : Set.range S.value ⊆ Set.range T.value) :
    graphPLReebData G h T ⟶ RGraph.refineData hST (graphPLReebData G h S) where
  v := graphPLRefineV G h hS hST
  e := graphPLRefineE G h hS hST
  left_comm k y := graphPLRefine_left_comm G h hS hST k y
  right_comm k y := graphPLRefine_right_comm G h hS hST k y

/-- The vertex component at an old level is the old-fiber equivalence followed by level transport. -/
theorem graphPLRefineHom_v_old [Finite V]
    (hS : CoversVertexHeights S h)
    (hST : Set.range S.value ⊆ Set.range T.value) (j : Fin (m + 1)) (i : Fin (n + 1))
    (hi : T.value j = S.value i) (x : LevelVertex G h (T.value j)) :
    (graphPLRefineHom G h hS hST).v j x =
      (RGraph.refineVEquivOld hST (graphPLReebData G h S) j i hi).symm
        (levelVertexEquivOfEq G h hi x) := by
  change graphPLRefineV G h hS hST j x = _
  exact graphPLRefineV_old G h hS hST j i hi x

/-- The vertex component at an inserted level is the gap-fiber equivalence on crossing edges. -/
theorem graphPLRefineHom_v_inserted [Finite V]
    (hS : CoversVertexHeights S h)
    (hST : Set.range S.value ⊆ Set.range T.value) (j : Fin (m + 1)) (e : Fin n)
    (he : T.value j ∈ (S.K e : Set ℝ)) (x : LevelVertex G h (T.value j)) :
    (graphPLRefineHom G h hS hST).v j x =
      (RGraph.refineVEquiv hST (graphPLReebData G h S) j e he).symm
        (levelVertexEquivSpanOfMemK G h hS e he x) := by
  change graphPLRefineV G h hS hST j x = _
  exact graphPLRefineV_inserted G h hS hST j e he x

/-- The edge component is the gap-fiber equivalence followed by the underlying-edge equivalence. -/
theorem graphPLRefineHom_e [Finite V]
    (hS : CoversVertexHeights S h)
    (hST : Set.range S.value ⊆ Set.range T.value) (k : Fin m) (e : Fin n)
    (he : (RGraph.basePt T k : ℝ) ∈ (S.K e : Set ℝ))
    (y : SpanEdge G h (T.value k.castSucc) (T.value k.succ)) :
    (graphPLRefineHom G h hS hST).e k y =
      (RGraph.refineEEquiv hST (graphPLReebData G h S) k e he).symm
        (spanEdgeEquivOfSubset G h hS e (T.value_castSucc_lt_succ k)
          (RGraph.Icc_subset_of_mem hST (basePt_mem_Icc (T := T) k) he) y) := by
  change graphPLRefineE G h hS hST k y = _
  exact graphPLRefineE_mem G h hS hST k e he y

/-- The vertex component of `graphPLRefineHom` is bijective at every `T`-level. -/
theorem graphPLRefineHom_bijective_v [Finite V]
    (hS : CoversVertexHeights S h)
    (hST : Set.range S.value ⊆ Set.range T.value) (j : Fin (m + 1)) :
    Function.Bijective ((graphPLRefineHom G h hS hST).v j) := by
  classical
  by_cases hi : ∃ i, T.value j = S.value i
  · obtain ⟨i, hi⟩ := hi
    have hgap : ¬ ∃ e, T.value j ∈ (S.K e : Set ℝ) := by
      rintro ⟨e, he⟩
      exact S.value_notMem_K e i (hi ▸ he)
    have hfun : (graphPLRefineHom G h hS hST).v j =
        (RGraph.refineVEquivOld hST (graphPLReebData G h S) j i hi).symm ∘
          levelVertexEquivOfEq G h hi := by
      funext x
      exact graphPLRefineHom_v_old G h hS hST j i hi x
    rw [hfun]
    exact (RGraph.refineVEquivOld hST (graphPLReebData G h S) j i hi).symm.bijective.comp
      (levelVertexEquivOfEq G h hi).bijective
  · by_cases he : ∃ e, T.value j ∈ (S.K e : Set ℝ)
    · obtain ⟨e, he⟩ := he
      have hfun : (graphPLRefineHom G h hS hST).v j =
          (RGraph.refineVEquiv hST (graphPLReebData G h S) j e he).symm ∘
            levelVertexEquivSpanOfMemK G h hS e he := by
        funext x
        exact graphPLRefineHom_v_inserted G h hS hST j e he x
      rw [hfun]
      exact (RGraph.refineVEquiv hST (graphPLReebData G h S) j e he).symm.bijective.comp
        (levelVertexEquivSpanOfMemK G h hS e he).bijective
    · have hout := value_exterior_of_not_old_not_gap (S := S) (T := T) j hi he
      have hEmpty1 : IsEmpty ((graphPLReebData G h T).V j) := by
        change IsEmpty (LevelVertex G h (T.value j))
        exact isEmpty_levelVertex_of_notMem_Icc G h hS hout
      have hEmpty2 :
          IsEmpty ((RGraph.refineData hST (graphPLReebData G h S)).V j) :=
        RGraph.isEmpty_refine_V hST (graphPLReebData G h S) j hout
      exact ⟨fun x => (hEmpty1.false x).elim, fun y => (hEmpty2.false y).elim⟩

/-- The edge component of `graphPLRefineHom` is bijective at every `T`-gap. -/
theorem graphPLRefineHom_bijective_e [Finite V]
    (hS : CoversVertexHeights S h)
    (hST : Set.range S.value ⊆ Set.range T.value) (k : Fin m) :
    Function.Bijective ((graphPLRefineHom G h hS hST).e k) := by
  classical
  by_cases he : ∃ e, (RGraph.basePt T k : ℝ) ∈ (S.K e : Set ℝ)
  · obtain ⟨e, he⟩ := he
    have hfun : (graphPLRefineHom G h hS hST).e k =
        (RGraph.refineEEquiv hST (graphPLReebData G h S) k e he).symm ∘
          spanEdgeEquivOfSubset G h hS e (T.value_castSucc_lt_succ k)
            (RGraph.Icc_subset_of_mem hST (basePt_mem_Icc (T := T) k) he) := by
      funext y
      exact graphPLRefineHom_e G h hS hST k e he y
    rw [hfun]
    exact (RGraph.refineEEquiv hST (graphPLReebData G h S) k e he).symm.bijective.comp
      (spanEdgeEquivOfSubset G h hS e (T.value_castSucc_lt_succ k)
        (RGraph.Icc_subset_of_mem hST (basePt_mem_Icc (T := T) k) he)).bijective
  · have hout := basePt_exterior_of_not_gap hST k he
    have hEmpty1 : IsEmpty ((graphPLReebData G h T).E k) := by
      change IsEmpty (SpanEdge G h (T.value k.castSucc) (T.value k.succ))
      exact isEmpty_spanEdge_of_exterior G h hS (T.value_castSucc_lt_succ k)
        (exterior_segment hST k hout)
    have hEmpty2 :
        IsEmpty ((RGraph.refineData hST (graphPLReebData G h S)).E k) :=
      RGraph.isEmpty_refine_E hST (graphPLReebData G h S) k hout
    exact ⟨fun x => (hEmpty1.false x).elim, fun y => (hEmpty2.false y).elim⟩

/-- The graph-PL finite Reeb data over `T` are isomorphic to the merged `S`-refinement. -/
def graphPLRefineIso [Finite V]
    (hS : CoversVertexHeights S h)
    (hST : Set.range S.value ⊆ Set.range T.value) :
    graphPLReebData G h T ≅ RGraph.refineData hST (graphPLReebData G h S) where
  hom := graphPLRefineHom G h hS hST
  inv := (graphPLRefineHom G h hS hST).inv
    (graphPLRefineHom_bijective_v G h hS hST)
    (graphPLRefineHom_bijective_e G h hS hST)
  hom_inv_id := (graphPLRefineHom G h hS hST).comp_inv _ _
  inv_hom_id := (graphPLRefineHom G h hS hST).inv_comp _ _

/-- The homomorphism underlying `graphPLRefineIso` is `graphPLRefineHom`. -/
@[simp]
theorem graphPLRefineIso_hom [Finite V]
    (hS : CoversVertexHeights S h)
    (hST : Set.range S.value ⊆ Set.range T.value) :
    (graphPLRefineIso G h hS hST).hom = graphPLRefineHom G h hS hST := rfl

end
end TDA.Mapper.GraphPL
