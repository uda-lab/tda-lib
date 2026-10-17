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

/-! Further graph-PL refinement declarations are added in later blocks. -/

end
end TDA.Mapper.GraphPL
