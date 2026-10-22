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
  obtain ⟨e, he'⟩ := CriticalValues.exists_mem_K_of_mem_Icc hx (fun i h => hi ⟨i, h.symm⟩)
  exact he ⟨e, he'⟩

private theorem basePt_exterior_of_not_gap
    (hST : Set.range S.value ⊆ Set.range T.value) (k : Fin m)
    (he : ¬ ∃ e, (RGraph.basePt T k : ℝ) ∈ (S.K e : Set ℝ)) :
    (RGraph.basePt T k : ℝ) ∉ Icc (S.value 0) (S.value (Fin.last n)) := by
  intro hx
  obtain ⟨e, he'⟩ := CriticalValues.exists_mem_K_of_mem_Icc hx
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

/-! ## Pointwise transitivity -/

private theorem graphPLRefineHom_v_val_old [Finite V]
    (hS : CoversVertexHeights S h)
    (hST : Set.range S.value ⊆ Set.range T.value) (j : Fin (m + 1)) (i : Fin (n + 1))
    (hi : T.value j = S.value i) (x : LevelVertex G h (T.value j)) :
    ((graphPLRefineHom G h hS hST).v j x).1 =
      (TDA.Reeb.CylinderPresentation.ofFiniteData (graphPLReebData G h S)).ofVertex S i
        (levelVertexEquivOfEq G h hi x) := by
  exact
    (congrArg Subtype.val (graphPLRefineHom_v_old G h hS hST j i hi x)).trans
      (TDA.Reeb.CylinderPresentation.criticalFiberHomeomorph_apply S
        (TDA.Reeb.CylinderPresentation.ofFiniteData (graphPLReebData G h S)) i
        (levelVertexEquivOfEq G h hi x))

private theorem graphPLRefineHom_v_val_inserted [Finite V]
    (hS : CoversVertexHeights S h)
    (hST : Set.range S.value ⊆ Set.range T.value) (j : Fin (m + 1)) (e : Fin n)
    (he : T.value j ∈ (S.K e : Set ℝ)) (x : LevelVertex G h (T.value j)) :
    ((graphPLRefineHom G h hS hST).v j x).1 =
      (TDA.Reeb.CylinderPresentation.ofFiniteData (graphPLReebData G h S)).ofStrip S e
        (levelVertexEquivSpanOfMemK G h hS e he x, ⟨_, he⟩) := by
  exact
    (congrArg Subtype.val (graphPLRefineHom_v_inserted G h hS hST j e he x)).trans
      (TDA.Reeb.CylinderPresentation.regularFiberHomeomorph_apply S
        (TDA.Reeb.CylinderPresentation.ofFiniteData (graphPLReebData G h S)) e ⟨_, he⟩
        (levelVertexEquivSpanOfMemK G h hS e he x))

private theorem graphPLRefineHom_e_val [Finite V]
    (hS : CoversVertexHeights S h)
    (hST : Set.range S.value ⊆ Set.range T.value) (k : Fin m) (e : Fin n)
    (he : (RGraph.basePt T k : ℝ) ∈ (S.K e : Set ℝ))
    (y : SpanEdge G h (T.value k.castSucc) (T.value k.succ)) :
    ((graphPLRefineHom G h hS hST).e k y).1 =
      (TDA.Reeb.CylinderPresentation.ofFiniteData (graphPLReebData G h S)).ofStrip S e
        (spanEdgeEquivOfSubset G h hS e (T.value_castSucc_lt_succ k)
          (RGraph.Icc_subset_of_mem hST (basePt_mem_Icc (T := T) k) he) y,
          ⟨_, he⟩) := by
  exact
    (congrArg Subtype.val (graphPLRefineHom_e G h hS hST k e he y)).trans
      (TDA.Reeb.CylinderPresentation.regularFiberHomeomorph_apply S
        (TDA.Reeb.CylinderPresentation.ofFiniteData (graphPLReebData G h S)) e ⟨_, he⟩
        (spanEdgeEquivOfSubset G h hS e (T.value_castSucc_lt_succ k)
          (RGraph.Icc_subset_of_mem hST (basePt_mem_Icc (T := T) k) he) y))

private theorem levelVertexEquivOfEq_trans {c c' c'' : ℝ}
    (h₁ : c = c') (h₂ : c' = c'') (h₃ : c = c'') (x : LevelVertex G h c) :
    levelVertexEquivOfEq G h h₃ x =
      levelVertexEquivOfEq G h h₂ (levelVertexEquivOfEq G h h₁ x) := by
  subst c'
  subst c''
  rfl

private theorem levelVertexEquivSpan_transport (hS : CoversVertexHeights S h) (e : Fin n)
    {c c' : ℝ} (hcc : c = c') (hc : c ∈ (S.K e : Set ℝ))
    (hc' : c' ∈ (S.K e : Set ℝ)) (x : LevelVertex G h c) :
    levelVertexEquivSpanOfMemK G h hS e hc'
        (levelVertexEquivOfEq G h hcc x) =
      levelVertexEquivSpanOfMemK G h hS e hc x := by
  subst c'
  apply Subtype.ext
  cases x with
  | inl z =>
      induction z using SimpleGraph.ConnectedComponent.ind with
      | h v => exact (hS.notMem_K e v.1 (by rw [v.2]; exact hc)).elim
  | inr y => simp

private theorem refineMap_realizeHom_ofVertex [Finite V] {D : FiniteReebData.{u} n}
    {S : CriticalValues n} {T : CriticalValues m}
    (hST : Set.range S.value ⊆ Set.range T.value)
    (φ : graphPLReebData G h T ⟶ RGraph.refineData hST D)
    (i : Fin (m + 1)) (z : (graphPLReebData G h T).V i) :
    RGraph.refineMap hST D
        (TDA.Reeb.CylinderPresentation.realizeHom T φ
          ((TDA.Reeb.CylinderPresentation.ofFiniteData (graphPLReebData G h T)).ofVertex T i z)) =
      ((φ.v i z).1) := rfl

private theorem refineMap_realizeHom_ofStrip [Finite V] {D : FiniteReebData.{u} n}
    {S : CriticalValues n} {T : CriticalValues m}
    (hST : Set.range S.value ⊆ Set.range T.value)
    (φ : graphPLReebData G h T ⟶ RGraph.refineData hST D)
    (k : Fin m) (z : (graphPLReebData G h T).E k) (t : (T.K k : Set ℝ)) :
    RGraph.refineMap hST D
        (TDA.Reeb.CylinderPresentation.realizeHom T φ
          ((TDA.Reeb.CylinderPresentation.ofFiniteData (graphPLReebData G h T)).ofStrip T k
            (z, t))) =
      RGraph.edgePoint hST D k (φ.e k z) (TDA.Reeb.CylinderPresentation.gapIncl T k t) := rfl

section transitivity

variable [Finite V]

/-- The vertex component of graph-PL refinement is pointwise transitive. -/
theorem graphPLRefineHom_trans_v
    (hS : CoversVertexHeights S h)
    (hST : Set.range S.value ⊆ Set.range T.value)
    (hTU : Set.range T.value ⊆ Set.range U.value)
    (hSU : Set.range S.value ⊆ Set.range U.value)
    (j : Fin (l + 1)) (x : LevelVertex G h (U.value j)) :
    ((graphPLRefineHom G h hS hSU).v j x).1 =
      RGraph.refineMap hST (graphPLReebData G h S)
        (TDA.Reeb.CylinderPresentation.realizeHom T
          (graphPLRefineHom G h hS hST)
          ((graphPLRefineHom G h (hS.mono hST) hTU).v j x).1) := by
  classical
  by_cases hUT : ∃ i, U.value j = T.value i
  · obtain ⟨iT, hiT⟩ := hUT
    by_cases hUS : ∃ i, U.value j = S.value i
    · obtain ⟨iS, hiS⟩ := hUS
      have hiST : T.value iT = S.value iS := hiT.symm.trans hiS
      refine (graphPLRefineHom_v_val_old G h hS hSU j iS hiS x).trans ?_
      refine (congrArg
        ((TDA.Reeb.CylinderPresentation.ofFiniteData (graphPLReebData G h S)).ofVertex S iS)
        (levelVertexEquivOfEq_trans G h hiT hiST hiS x)).trans ?_
      refine (graphPLRefineHom_v_val_old G h hS hST iT iS hiST
        (levelVertexEquivOfEq G h hiT x)).symm.trans ?_
      refine (refineMap_realizeHom_ofVertex G h hST (graphPLRefineHom G h hS hST) iT
        (levelVertexEquivOfEq G h hiT x)).symm.trans ?_
      exact congrArg
        (fun q : (TDA.Reeb.CylinderPresentation.ofFiniteData
            (graphPLReebData G h T)).Realization T =>
          RGraph.refineMap hST (graphPLReebData G h S)
            (TDA.Reeb.CylinderPresentation.realizeHom T
              (graphPLRefineHom G h hS hST) q))
        (graphPLRefineHom_v_val_old G h (hS.mono hST) hTU j iT hiT x).symm
    · by_cases hUSgap : ∃ e, U.value j ∈ (S.K e : Set ℝ)
      · obtain ⟨e, he⟩ := hUSgap
        have heT : T.value iT ∈ (S.K e : Set ℝ) := hiT ▸ he
        have hstrip :
            (TDA.Reeb.CylinderPresentation.ofFiniteData (graphPLReebData G h S)).ofStrip S e
                (levelVertexEquivSpanOfMemK G h hS e he x, ⟨_, he⟩) =
              (TDA.Reeb.CylinderPresentation.ofFiniteData (graphPLReebData G h S)).ofStrip S e
                (levelVertexEquivSpanOfMemK G h hS e heT
                    (levelVertexEquivOfEq G h hiT x), ⟨_, heT⟩) := by
          congr 1
          exact Prod.ext (levelVertexEquivSpan_transport G h hS e hiT he heT x).symm
            (Subtype.ext hiT)
        refine (graphPLRefineHom_v_val_inserted G h hS hSU j e he x).trans ?_
        refine hstrip.trans ?_
        refine (graphPLRefineHom_v_val_inserted G h hS hST iT e heT
          (levelVertexEquivOfEq G h hiT x)).symm.trans ?_
        refine (refineMap_realizeHom_ofVertex G h hST (graphPLRefineHom G h hS hST) iT
          (levelVertexEquivOfEq G h hiT x)).symm.trans ?_
        exact congrArg
          (fun q : (TDA.Reeb.CylinderPresentation.ofFiniteData
              (graphPLReebData G h T)).Realization T =>
            RGraph.refineMap hST (graphPLReebData G h S)
              (TDA.Reeb.CylinderPresentation.realizeHom T
                (graphPLRefineHom G h hS hST) q))
          (graphPLRefineHom_v_val_old G h (hS.mono hST) hTU j iT hiT x).symm
      · have hout := value_exterior_of_not_old_not_gap (S := S) (T := U) j
          hUS hUSgap
        exact ((isEmpty_levelVertex_of_notMem_Icc G h hS hout).false x).elim
  · obtain ⟨kT, hkT⟩ : ∃ k, U.value j ∈ (T.K k : Set ℝ) := by
      obtain ⟨p, hp, hpne⟩ := T.exists_piece (U.value j)
      cases p with
      | star i => exact (hUT ⟨i, (hpne i (T.value_mem_J i)).symm⟩).elim
      | gap k => exact ⟨k, hp⟩
      | lowerTail =>
          have houtT : U.value j ∉ Icc (T.value 0) (T.value (Fin.last m)) := by
            intro hx
            exact (not_lt_of_ge hx.1) (T.mem_lowerTail.1 hp)
          exact ((isEmpty_levelVertex_of_notMem_Icc G h (hS.mono hST) houtT).false x).elim
      | upperTail =>
          have houtT : U.value j ∉ Icc (T.value 0) (T.value (Fin.last m)) := by
            intro hx
            exact (not_le_of_gt (T.mem_upperTail.1 hp)) hx.2
          exact ((isEmpty_levelVertex_of_notMem_Icc G h (hS.mono hST) houtT).false x).elim
    by_cases hUS : ∃ i, U.value j = S.value i
    · obtain ⟨iS, hiS⟩ := hUS
      obtain ⟨iT, hiT⟩ := hST ⟨iS, rfl⟩
      exact (T.value_notMem_K kT iT (by rw [hiT, ← hiS]; exact hkT)).elim
    · by_cases hUSgap : ∃ e, U.value j ∈ (S.K e : Set ℝ)
      · obtain ⟨e, he⟩ := hUSgap
        have hsub : Icc (T.value kT.castSucc) (T.value kT.succ) ⊆
            Icc (S.value e.castSucc) (S.value e.succ) :=
          RGraph.Icc_subset_of_mem hST (Ioo_subset_Icc_self hkT) he
        have hebase : (RGraph.basePt T kT : ℝ) ∈ (S.K e : Set ℝ) :=
          RGraph.mem_K_of_ne (hsub (basePt_mem_Icc (T := T) kT))
            (RGraph.value_ne hST (RGraph.basePt T kT).2)
        let zT := levelVertexEquivSpanOfMemK G h (hS.mono hST) kT hkT x
        have hz : levelVertexEquivSpanOfMemK G h hS e he x =
            spanEdgeEquivOfSubset G h hS e (T.value_castSucc_lt_succ kT)
              hsub zT := by
          apply Subtype.ext
          cases x with
          | inl w =>
              induction w using SimpleGraph.ConnectedComponent.ind with
              | h v => exact (hS.notMem_K e v.1 (by rw [v.2]; exact he)).elim
          | inr w => rfl
        refine (graphPLRefineHom_v_val_inserted G h hS hSU j e he x).trans ?_
        refine Eq.trans ?_
          (congrArg
            (fun q : (TDA.Reeb.CylinderPresentation.ofFiniteData
                (graphPLReebData G h T)).Realization T =>
              RGraph.refineMap hST (graphPLReebData G h S)
                (TDA.Reeb.CylinderPresentation.realizeHom T
                  (graphPLRefineHom G h hS hST) q))
            (graphPLRefineHom_v_val_inserted G h (hS.mono hST) hTU j kT hkT x).symm)
        refine Eq.trans ?_
          (refineMap_realizeHom_ofStrip G h hST (graphPLRefineHom G h hS hST) kT zT
            (⟨_, hkT⟩ : (T.K kT : Set ℝ))).symm
        have hy := graphPLRefineHom_e_val G h hS hST kT e hebase zT
        refine Eq.trans ?_
          (RGraph.edgePoint_eq hST (graphPLReebData G h S) kT
            ((graphPLRefineHom G h hS hST).e kT zT)
            (spanEdgeEquivOfSubset G h hS e (T.value_castSucc_lt_succ kT) hsub zT)
            hebase hy
            (TDA.Reeb.CylinderPresentation.gapIncl T kT (⟨_, hkT⟩ : (T.K kT : Set ℝ)))).symm
        refine (congrArg
          (fun z : (graphPLReebData G h S).E e =>
            (TDA.Reeb.CylinderPresentation.ofFiniteData (graphPLReebData G h S)).ofStrip S e
              (z, ⟨_, he⟩)) hz).trans ?_
        rfl
      · have hout := value_exterior_of_not_old_not_gap (S := S) (T := U) j hUS hUSgap
        exact ((isEmpty_levelVertex_of_notMem_Icc G h hS hout).false x).elim

/-- The edge component of graph-PL refinement is pointwise transitive. -/
theorem graphPLRefineHom_trans_e
    (hS : CoversVertexHeights S h)
    (hST : Set.range S.value ⊆ Set.range T.value)
    (hTU : Set.range T.value ⊆ Set.range U.value)
    (hSU : Set.range S.value ⊆ Set.range U.value)
    (k : Fin l) (y : SpanEdge G h (U.value k.castSucc) (U.value k.succ)) :
    ((graphPLRefineHom G h hS hSU).e k y).1 =
      RGraph.refineMap hST (graphPLReebData G h S)
        (TDA.Reeb.CylinderPresentation.realizeHom T
          (graphPLRefineHom G h hS hST)
          ((graphPLRefineHom G h (hS.mono hST) hTU).e k y).1) := by
  classical
  by_cases hUT : ∃ k', (RGraph.basePt U k : ℝ) ∈ (T.K k' : Set ℝ)
  · obtain ⟨kT, hkT⟩ := hUT
    by_cases hUS : ∃ e, (RGraph.basePt U k : ℝ) ∈ (S.K e : Set ℝ)
    · obtain ⟨e, he⟩ := hUS
      have hsub : Icc (T.value kT.castSucc) (T.value kT.succ) ⊆
          Icc (S.value e.castSucc) (S.value e.succ) :=
        RGraph.Icc_subset_of_mem hST (Ioo_subset_Icc_self hkT) he
      have hebase : (RGraph.basePt T kT : ℝ) ∈ (S.K e : Set ℝ) :=
        RGraph.mem_K_of_ne (hsub (basePt_mem_Icc (T := T) kT))
          (RGraph.value_ne hST (RGraph.basePt T kT).2)
      let zT := spanEdgeEquivOfSubset G h (hS.mono hST) kT
        (U.value_castSucc_lt_succ k)
        (RGraph.Icc_subset_of_mem hTU (basePt_mem_Icc (T := U) k) hkT) y
      let zS := spanEdgeEquivOfSubset G h hS e (U.value_castSucc_lt_succ k)
        (RGraph.Icc_subset_of_mem hSU (basePt_mem_Icc (T := U) k) he) y
      have hzcoe : (zT : G.edgeSet) = (y : G.edgeSet) := by
        exact spanEdgeEquivOfSubset_apply_coe G h (hS.mono hST) kT
          (U.value_castSucc_lt_succ k)
          (RGraph.Icc_subset_of_mem hTU (basePt_mem_Icc (T := U) k) hkT) y
      have hz : zS = spanEdgeEquivOfSubset G h hS e (T.value_castSucc_lt_succ kT) hsub zT := by
        apply Subtype.ext
        exact (spanEdgeEquivOfSubset_apply_coe G h hS e (U.value_castSucc_lt_succ k)
          (RGraph.Icc_subset_of_mem hSU (basePt_mem_Icc (T := U) k) he) y).trans
          ((spanEdgeEquivOfSubset_apply_coe G h hS e (T.value_castSucc_lt_succ kT)
            hsub zT).symm.trans hzcoe)
      refine (graphPLRefineHom_e_val G h hS hSU k e he y).trans ?_
      refine Eq.trans ?_
        (congrArg
          (fun q : (TDA.Reeb.CylinderPresentation.ofFiniteData
              (graphPLReebData G h T)).Realization T =>
            RGraph.refineMap hST (graphPLReebData G h S)
              (TDA.Reeb.CylinderPresentation.realizeHom T
                (graphPLRefineHom G h hS hST) q))
          (graphPLRefineHom_e_val G h (hS.mono hST) hTU k kT hkT y).symm)
      refine Eq.trans ?_
        (refineMap_realizeHom_ofStrip G h hST (graphPLRefineHom G h hS hST) kT zT
          (⟨_, hkT⟩ : (T.K kT : Set ℝ))).symm
      have hy := graphPLRefineHom_e_val G h hS hST kT e hebase zT
      refine Eq.trans ?_
        (RGraph.edgePoint_eq hST (graphPLReebData G h S) kT
          ((graphPLRefineHom G h hS hST).e kT zT)
          (spanEdgeEquivOfSubset G h hS e (T.value_castSucc_lt_succ kT) hsub zT)
          hebase hy
          (TDA.Reeb.CylinderPresentation.gapIncl T kT (⟨_, hkT⟩ : (T.K kT : Set ℝ)))).symm
      refine (congrArg
        (fun z : (graphPLReebData G h S).E e =>
          (TDA.Reeb.CylinderPresentation.ofFiniteData (graphPLReebData G h S)).ofStrip S e
            (z, ⟨_, he⟩)) hz).trans ?_
      rfl
    · have hout := basePt_exterior_of_not_gap hSU k hUS
      exact ((isEmpty_spanEdge_of_exterior G h hS (U.value_castSucc_lt_succ k)
        (exterior_segment hSU k hout)).false y).elim
  · have hout := basePt_exterior_of_not_gap hTU k hUT
    exact ((isEmpty_spanEdge_of_exterior G h (hS.mono hST) (U.value_castSucc_lt_succ k)
      (exterior_segment hTU k hout)).false y).elim

end transitivity

/-! ## Mapper and realization corollaries -/

/-- The adapted Mapper finite data are isomorphic to the refinement of graph-PL data over `S`. -/
def uniformMapperRefineIso [Finite V] {a r g : ℝ} (T : CriticalValues m)
    (hT : LevelsAdapted T a r g) (hcov : CoversVertexHeights T h)
    (hS : CoversVertexHeights S h) (hST : Set.range S.value ⊆ Set.range T.value)
    (hg : 0 < g) (hgr : g ≤ r) :
    uniformMapperData G h a r g m ≅ RGraph.refineData hST (graphPLReebData G h S) :=
  uniformMapperIso G h T hT hcov hg hgr ≪≫ graphPLRefineIso G h hS hST

/-- The canonical vertex-height list is refined by every covering critical list. -/
theorem range_vertexHeightLevels_subset [Fintype V] [Nonempty V]
    (hcov : CoversVertexHeights T h) :
    Set.range (vertexHeightLevels h).value ⊆ Set.range T.value := by
  rw [range_vertexHeightLevels h]
  intro x hx
  obtain ⟨v, rfl⟩ := hx
  exact hcov v

/-- The adapted Mapper finite data refine to graph-PL data over the canonical list. -/
def uniformMapperCanonicalIso [Fintype V] [Nonempty V] {a r g : ℝ} (T : CriticalValues m)
    (hT : LevelsAdapted T a r g) (hcov : CoversVertexHeights T h)
    (hg : 0 < g) (hgr : g ≤ r) :
    uniformMapperData G h a r g m ≅
      RGraph.refineData (range_vertexHeightLevels_subset h hcov)
        (graphPLReebData G h (vertexHeightLevels h)) :=
  uniformMapperRefineIso G h T hT hcov (coversVertexHeights_vertexHeightLevels h)
    (range_vertexHeightLevels_subset h hcov) hg hgr

/-- Every bounded finite graph-PL height has a canonical-list Mapper/refinement isomorphism. -/
theorem exists_uniformMapperCanonicalIso [Fintype V] [Nonempty V] {m₀ M ρ : ℝ}
    (hh : ∀ v, h v ∈ Set.Icc m₀ M) (hρ : 0 < ρ) :
    ∃ (a r g : ℝ) (n : ℕ) (T : CriticalValues n)
      (hST : Set.range (vertexHeightLevels h).value ⊆ Set.range T.value),
      0 < g ∧ 2 * g ≤ r ∧ r < ρ ∧ LevelsAdapted T a r g ∧
        Nonempty (uniformMapperData G h a r g n ≅
          RGraph.refineData hST (graphPLReebData G h (vertexHeightLevels h))) := by
  obtain ⟨a, r, g, n, T, hg, hgr, hrρ, hT, hcov, _hiso⟩ :=
    exists_uniformMapperIso G h hh hρ
  refine ⟨a, r, g, n, T, range_vertexHeightLevels_subset h hcov,
    hg, hgr, hrρ, hT, ?_⟩
  have hgr' : g ≤ r := by linarith
  exact ⟨uniformMapperCanonicalIso G h T hT hcov hg hgr'⟩

section realization

variable {V : Type} (G : SimpleGraph V) (h : V → ℝ)
  {n m : ℕ} {S : CriticalValues n} {T : CriticalValues m}

/-- The graph-PL realization isomorphism induced by a refinement of critical values. -/
def graphPLRefineToOverIso [Finite V]
    (hS : CoversVertexHeights S h)
    (hST : Set.range S.value ⊆ Set.range T.value) :
    RGraph.toOver T (graphPLReebData G h T) ≅
      RGraph.toOver S (graphPLReebData G h S) :=
  (RGraph.realizationFunctor T).mapIso (graphPLRefineIso G h hS hST) ≪≫
    RGraph.refineIso hST _

/-- The adapted Mapper realization is isomorphic to the canonical graph-PL realization. -/
def uniformMapperCanonicalToOverIso [Fintype V] [Nonempty V] {a r g : ℝ}
    (T : CriticalValues m) (hT : LevelsAdapted T a r g)
    (hcov : CoversVertexHeights T h) (hg : 0 < g) (hgr : g ≤ r) :
    RGraph.toOver T (uniformMapperData G h a r g m) ≅
      RGraph.toOver (vertexHeightLevels h)
        (graphPLReebData G h (vertexHeightLevels h)) :=
  (RGraph.realizationFunctor T).mapIso (uniformMapperIso G h T hT hcov hg hgr) ≪≫
    graphPLRefineToOverIso G h (coversVertexHeights_vertexHeightLevels h)
      (range_vertexHeightLevels_subset h hcov)

end realization

end
end TDA.Mapper.GraphPL
