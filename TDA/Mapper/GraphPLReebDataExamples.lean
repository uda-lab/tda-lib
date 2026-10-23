import TDA.Mapper.GraphPLReebData
import TDA.Mapper.UniformCoverCellsExamples
import TDA.Reeb.RGraphExamples
import TDA.Reeb.ConstructibleRepresentationExamples
import TDA.Reeb.ConstructibleCylinderExamples
import TDA.Reeb.ConstructibleSpaceExamples

/-!
# Finite Reeb data of graph-PL input: fixtures

Acceptance fixtures for `TDA.Mapper.GraphPLReebData`, on the merged graph-PL objects and critical
lists. Every count is a `Nat.card` equality derived through `graphPLReebData`, `LevelVertex`,
`SpanEdge`, or transported through `graphPLStarEquiv`.

* **F1. 4-cycle at `0 < 1 < 2`.** Vertex counts `1, 2, 1`, edge counts `2, 2`; the left endpoint
  map of the lower gap is constant, its right endpoint map injective. A map of finite data from the
  merged `cycleData` with bijective components identifies the two, so the realization is not the
  path's. Through the star bijection, the preimage of `(0, 2)` has two path components.
* **F2. Single edge.** At `0 < 2` both endpoints are level components. At `0 < 1 < 2` the level
  `1` carries no vertex and the edge crosses it: one Reeb vertex in the crossing branch, shared by
  the two incident gaps.
* **F3. Subdivided Y-tree at `0 < 1 < 2 < 3`.** Vertex counts `1, 2, 1, 1`, edge counts `1, 2, 1`,
  with the crossing edge `0 — 2` as a degree-two Reeb vertex at level `1`; the counts agree with
  the merged MultiNerve Mapper cell counts.
* **F4. One vertex**, **F5. horizontal edges**, **F6. two isolated vertices** of equal height and
  **F8. the empty graph** at the single level `0`.
* **F7. Negative control.** For two isolated vertices of heights `0` and `2` and the single level
  `0`, the covering hypothesis fails, the star `ℝ` has two path components and the level has one
  Reeb vertex: the star comparison does not hold without covering.
-/

namespace TDA.Mapper.GraphPLReebDataExamples

open Set SimpleGraph CategoryTheory
open TDA.Reeb TDA.Reeb.GraphPL TDA.Reeb.GraphRealization TDA.Reeb.OpenInterval TDA.Reeb.RGraph
open TDA.Reeb.Examples.GraphPL
open TDA.Reeb.Examples.GraphRealization (edgeGraph d₀ edgeGraph_dart pointGraph path3)
open TDA.Mapper.GraphPL
open TDA.Mapper.UniformCoverExamples (d12 d03 c4_edge_cases)
open TDA.Mapper.UniformCoverCellsExamples (Y hY y02 y12 y23 Y_edge_cases Y_vertexCells_one
  Y_vertexCells_other Y_edgeCells)
open TDA.Reeb.Examples.Cylinder (S01 S01_value_zero S01_value_one)
open TDA.Reeb.Examples.ConstructibleCylinder (S0 S012)
open TDA.Reeb.Examples.ConstructibleRepresentation (S02)
open TDA.Reeb.RGraph.Examples (cycleData pathData cycle_not_iso_path)

noncomputable section

/-! ## Counting helpers -/

section helpers

variable {α : Type*}

private theorem card_zero_of {P : α → Prop} (hP : ∀ x, ¬ P x) : Nat.card {x // P x} = 0 := by
  have : IsEmpty {x // P x} := ⟨fun x => hP x.1 x.2⟩
  exact Nat.card_of_isEmpty

private theorem card_one_of {P : α → Prop} {a : α} (ha : P a) (hP : ∀ x, P x → x = a) :
    Nat.card {x // P x} = 1 :=
  Nat.card_eq_one_iff_unique.2
    ⟨⟨fun x y => Subtype.ext ((hP x.1 x.2).trans (hP y.1 y.2).symm)⟩, ⟨⟨a, ha⟩⟩⟩

private theorem card_two_of {P : α → Prop} {a b : α} (hab : a ≠ b) (ha : P a) (hb : P b)
    (hP : ∀ x, P x → x = a ∨ x = b) : Nat.card {x // P x} = 2 := by
  rw [Nat.card_eq_two_iff]
  refine ⟨⟨a, ha⟩, ⟨b, hb⟩, fun h => hab (congrArg Subtype.val h), ?_⟩
  ext x
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
  rcases hP x.1 x.2 with h | h
  · exact .inl (Subtype.ext h)
  · exact .inr (Subtype.ext h)

variable {V : Type*} {G : SimpleGraph V}

/-- Without adjacency inside `S`, the induced class map is injective. -/
private theorem induce_mk_injective_of_not_adj {S : Set V}
    (hS : ∀ x ∈ S, ∀ y ∈ S, ¬ G.Adj x y) :
    Function.Injective (G.induce S).connectedComponentMk := fun x y hxy => by
  obtain ⟨p⟩ := ConnectedComponent.exact hxy
  cases p with
  | nil => rfl
  | cons hadj _ => exact (hS _ (Subtype.prop _) _ (Subtype.prop _) hadj).elim

/-- Without adjacency between the vertices of `S`, the components of the induced graph are the
vertices of `S`. -/
private theorem card_induce_of_not_adj {S : Set V} (hS : ∀ x ∈ S, ∀ y ∈ S, ¬ G.Adj x y) :
    Nat.card (G.induce S).ConnectedComponent = Nat.card S := by
  refine (Nat.card_congr (Equiv.ofBijective (G.induce S).connectedComponentMk
    ⟨induce_mk_injective_of_not_adj hS, fun c => ?_⟩)).symm
  induction c using ConnectedComponent.ind with
  | h v => exact ⟨v, rfl⟩

/-- A single-vertex set induces one component. -/
private theorem card_induce_singleton {S : Set V} {v₀ : V} (hv₀ : v₀ ∈ S)
    (hS : ∀ v ∈ S, v = v₀) : Nat.card (G.induce S).ConnectedComponent = 1 := by
  rw [card_induce_of_not_adj fun x hx y hy hxy => G.loopless.irrefl x
    (by rw [hS x hx, ← hS y hy] at hxy ⊢; exact hxy)]
  exact card_one_of (P := (· ∈ S)) hv₀ hS

/-- A nonempty set whose distinct vertices are adjacent induces one component. -/
private theorem card_induce_complete {S : Set V} {v₀ : V} (hv₀ : v₀ ∈ S)
    (hS : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → G.Adj x y) :
    Nat.card (G.induce S).ConnectedComponent = 1 := by
  refine Nat.card_eq_one_iff_unique.2 ⟨⟨ConnectedComponent.ind₂ fun x y => ?_⟩,
    ⟨(G.induce S).connectedComponentMk ⟨v₀, hv₀⟩⟩⟩
  by_cases hxy : (x : V) = y
  · rw [Subtype.ext hxy]
  · exact ConnectedComponent.connectedComponentMk_eq_of_adj (hS x x.2 y y.2 hxy)

/-- An empty set induces no component. -/
private theorem card_induce_empty {S : Set V} (hS : ∀ v, v ∉ S) :
    Nat.card (G.induce S).ConnectedComponent = 0 := by
  have : IsEmpty (G.induce S).ConnectedComponent :=
    ⟨fun c => by
      induction c using ConnectedComponent.ind with
      | h v => exact hS v.1 v.2⟩
  exact Nat.card_of_isEmpty

/-- The empty graph has no edge. -/
private theorem bot_edge_false (e : (⊥ : SimpleGraph V).edgeSet) : False := by
  obtain ⟨d, -⟩ := exists_dartEdge_eq e
  exact d.adj

variable {h : V → ℝ}

/-- No edge crosses a height at most every vertex height. -/
private theorem not_edgeCrosses_of_le {c : ℝ} (hc : ∀ v, c ≤ h v) (e : G.edgeSet) :
    ¬ EdgeCrosses G h c e := fun ⟨d, _, hmin, _⟩ => by
  rcases min_choice (h d.fst) (h d.snd) with hm | hm <;> rw [hm] at hmin <;>
    linarith [hc d.fst, hc d.snd]

/-- No edge crosses a height at least every vertex height. -/
private theorem not_edgeCrosses_of_ge {c : ℝ} (hc : ∀ v, h v ≤ c) (e : G.edgeSet) :
    ¬ EdgeCrosses G h c e := fun ⟨d, _, _, hmax⟩ => by
  rcases max_choice (h d.fst) (h d.snd) with hm | hm <;> rw [hm] at hmax <;>
    linarith [hc d.fst, hc d.snd]

/-- No edge with an endpoint at height `c` crosses `c`. -/
private theorem not_edgeCrosses_dartEdge_of_eq {c : ℝ} {d : G.Dart}
    (hd : h d.fst = c ∨ h d.snd = c) : ¬ EdgeCrosses G h c (dartEdge d) := fun hcr => by
  obtain ⟨hmin, hmax⟩ := (edgeCrosses_dartEdge_iff d).1 hcr
  rcases hd with hd | hd <;> rw [hd] at hmin hmax
  · rcases min_lt_iff.1 hmin with h' | h'
    · exact lt_irrefl _ h'
    · rcases lt_max_iff.1 hmax with h'' | h''
      · exact lt_irrefl _ h''
      · linarith
  · rcases min_lt_iff.1 hmin with h' | h'
    · rcases lt_max_iff.1 hmax with h'' | h''
      · linarith
      · exact lt_irrefl _ h''
    · exact lt_irrefl _ h'

/-- Distinct darts that are not opposite have distinct edges. -/
private theorem dartEdge_ne {d d' : G.Dart} (h₁ : d.toProd ≠ d'.toProd)
    (h₂ : d.toProd ≠ d'.toProd.swap) : dartEdge d ≠ dartEdge d' := fun hdd => by
  rcases dartEdge_eq_iff.1 hdd with h | h
  · exact h₁ (congrArg Dart.toProd h)
  · exact h₂ (congrArg Dart.toProd h)

/-- The Reeb vertices at a level are the level components plus the crossing edges. -/
private theorem card_levelVertex [Finite V] (G : SimpleGraph V) (h : V → ℝ) (c : ℝ) {m k : ℕ}
    (hm : Nat.card (G.induce {v | h v = c}).ConnectedComponent = m)
    (hk : Nat.card {e : G.edgeSet // EdgeCrosses G h c e} = k) :
    Nat.card (LevelVertex G h c) = m + k := by
  classical
  have := Fintype.ofFinite V
  rw [Nat.card_sum, hm, hk]

end helpers

/-! ## F1. The 4-cycle at `0 < 1 < 2` -/

section Cycle

@[simp] private theorem S012_zero : S012.value 0 = 0 := by
  show ((0 : ℕ) : ℝ) = 0
  norm_num

@[simp] private theorem S012_one : S012.value 1 = 1 := by
  show ((1 : ℕ) : ℝ) = 1
  norm_num

@[simp] private theorem S012_two : S012.value 2 = 2 := by
  show ((2 : ℕ) : ℝ) = 2
  norm_num

/-- The levels `0, 1, 2` cover the heights of the 4-cycle. -/
theorem c4_covers : CoversVertexHeights S012 h4 := fun v => by
  fin_cases v
  · exact ⟨0, by simp⟩
  · exact ⟨1, by simp⟩
  · exact ⟨2, by simp⟩
  · exact ⟨1, by simp⟩

/-- No two vertices of equal height are adjacent in the 4-cycle. -/
private theorem c4_level_not_adj (c : ℝ) :
    ∀ x ∈ {v | h4 v = c}, ∀ y ∈ {v | h4 v = c}, ¬ C4.Adj x y := by
  intro x hx y hy hadj
  have hxy : h4 x = h4 y := hx.trans hy.symm
  fin_cases x <;> fin_cases y <;> first | exact absurd hadj (by decide) | norm_num [h4] at hxy

private theorem c4_card_V0 : Nat.card ((graphPLReebData C4 h4 S012).V 0) = 1 :=
  card_levelVertex C4 h4 _
    (card_induce_singleton (v₀ := 0) (by simp) fun v hv => by
      fin_cases v <;> simp_all [h4])
    (card_zero_of (not_edgeCrosses_of_le fun v => by
      rw [S012_zero]; fin_cases v <;> norm_num [h4]))

private theorem c4_level_one_card : Nat.card ↥{v | h4 v = S012.value 1} = 2 :=
  card_two_of (P := fun v => v ∈ {v | h4 v = S012.value 1}) (a := 1) (b := 3) (by decide)
    (by simp) (by simp) fun v hv => by fin_cases v <;> simp_all [h4]

/-- Every edge of the 4-cycle has an endpoint at height `1`, so none crosses `1`. -/
private theorem c4_not_crosses_one (e : C4.edgeSet) : ¬ EdgeCrosses C4 h4 (S012.value 1) e := by
  rcases c4_edge_cases e with rfl | rfl | rfl | rfl
  · exact not_edgeCrosses_dartEdge_of_eq (.inr (by simp [d01]))
  · exact not_edgeCrosses_dartEdge_of_eq (.inl (by simp [d12]))
  · exact not_edgeCrosses_dartEdge_of_eq (.inr (by simp [d23]))
  · exact not_edgeCrosses_dartEdge_of_eq (.inr (by simp [d03]))

/-- **F1 at level `1`.** The level graph on `{1, 3}` has two components, and no edge crosses `1`. -/
theorem c4_level_one :
    Nat.card (C4.induce {v | h4 v = S012.value 1}).ConnectedComponent = 2 ∧
      ∀ e : C4.edgeSet, ¬ EdgeCrosses C4 h4 (S012.value 1) e :=
  ⟨(card_induce_of_not_adj (c4_level_not_adj _)).trans c4_level_one_card, c4_not_crosses_one⟩

private theorem c4_card_V1 : Nat.card ((graphPLReebData C4 h4 S012).V 1) = 2 :=
  card_levelVertex C4 h4 _ c4_level_one.1 (card_zero_of c4_level_one.2)

private theorem c4_card_V2 : Nat.card ((graphPLReebData C4 h4 S012).V 2) = 1 :=
  card_levelVertex C4 h4 _
    (card_induce_singleton (v₀ := 2) (by simp) fun v hv => by
      fin_cases v <;> simp_all [h4])
    (card_zero_of (not_edgeCrosses_of_ge fun v => by
      rw [S012_two]; fin_cases v <;> norm_num [h4]))

/-- **F1 vertex counts** `1, 2, 1`. -/
theorem c4_vertexCounts :
    Nat.card ((graphPLReebData C4 h4 S012).V 0) = 1 ∧
      Nat.card ((graphPLReebData C4 h4 S012).V 1) = 2 ∧
      Nat.card ((graphPLReebData C4 h4 S012).V 2) = 1 :=
  ⟨c4_card_V0, c4_card_V1, c4_card_V2⟩

/-- The spanning edges of the lower gap are `0 — 1` and `0 — 3`. -/
private theorem c4_spans_zero_cases (e : C4.edgeSet)
    (he : EdgeSpans C4 h4 (S012.value (Fin.castSucc 0)) (S012.value (Fin.succ 0)) e) :
    e = dartEdge d01 ∨ e = dartEdge d03 := by
  rcases c4_edge_cases e with rfl | rfl | rfl | rfl
  · exact .inl rfl
  · rw [edgeSpans_dartEdge_iff] at he
    norm_num [d12] at he
  · rw [edgeSpans_dartEdge_iff] at he
    norm_num [d23] at he
  · exact .inr rfl

/-- The spanning edges of the upper gap are `1 — 2` and `2 — 3`. -/
private theorem c4_spans_one_cases (e : C4.edgeSet)
    (he : EdgeSpans C4 h4 (S012.value (Fin.castSucc 1)) (S012.value (Fin.succ 1)) e) :
    e = dartEdge d12 ∨ e = dartEdge d23 := by
  rcases c4_edge_cases e with rfl | rfl | rfl | rfl
  · rw [edgeSpans_dartEdge_iff] at he
    norm_num [d01] at he
  · exact .inl rfl
  · exact .inr rfl
  · rw [edgeSpans_dartEdge_iff] at he
    norm_num [d03] at he

private theorem c4_spans_d01 :
    EdgeSpans C4 h4 (S012.value (Fin.castSucc 0)) (S012.value (Fin.succ 0)) (dartEdge d01) := by
  rw [edgeSpans_dartEdge_iff]
  norm_num [d01]

private theorem c4_spans_d03 :
    EdgeSpans C4 h4 (S012.value (Fin.castSucc 0)) (S012.value (Fin.succ 0)) (dartEdge d03) := by
  rw [edgeSpans_dartEdge_iff]
  norm_num [d03]

private theorem c4_spans_d12 :
    EdgeSpans C4 h4 (S012.value (Fin.castSucc 1)) (S012.value (Fin.succ 1)) (dartEdge d12) := by
  rw [edgeSpans_dartEdge_iff]
  norm_num [d12]

private theorem c4_spans_d23 :
    EdgeSpans C4 h4 (S012.value (Fin.castSucc 1)) (S012.value (Fin.succ 1)) (dartEdge d23) := by
  rw [edgeSpans_dartEdge_iff]
  norm_num [d23]

/-- **F1 edge counts** `2, 2`: `0 — 1, 0 — 3` span `[0, 1]` and `1 — 2, 2 — 3` span `[1, 2]`. -/
theorem c4_edgeCounts :
    Nat.card ((graphPLReebData C4 h4 S012).E 0) = 2 ∧
      Nat.card ((graphPLReebData C4 h4 S012).E 1) = 2 :=
  ⟨card_two_of (dartEdge_ne (by decide) (by decide)) c4_spans_d01 c4_spans_d03
      c4_spans_zero_cases,
    card_two_of (dartEdge_ne (by decide) (by decide)) c4_spans_d12 c4_spans_d23
      c4_spans_one_cases⟩

/-- The edge `0 — 1` over the lower gap. -/
def c4e01 : (graphPLReebData C4 h4 S012).E 0 := ⟨dartEdge d01, c4_spans_d01⟩

/-- The edge `0 — 3` over the lower gap. -/
def c4e03 : (graphPLReebData C4 h4 S012).E 0 := ⟨dartEdge d03, c4_spans_d03⟩

/-- The edge `1 — 2` over the upper gap. -/
def c4e12 : (graphPLReebData C4 h4 S012).E 1 := ⟨dartEdge d12, c4_spans_d12⟩

/-- The edge `2 — 3` over the upper gap. -/
def c4e23 : (graphPLReebData C4 h4 S012).E 1 := ⟨dartEdge d23, c4_spans_d23⟩

private theorem c4e01_ne_c4e03 : c4e01 ≠ c4e03 := fun h =>
  dartEdge_ne (d := d01) (d' := d03) (by decide) (by decide) (congrArg Subtype.val h)

/-- **F1 left endpoints of the lower gap**: both edges go to the component of `0`. -/
theorem c4_left_zero (y : (graphPLReebData C4 h4 S012).E 0) :
    ((graphPLReebData C4 h4 S012).left 0 y : LevelVertex C4 h4 (S012.value (Fin.castSucc 0))) =
      Sum.inl ((C4.induce {v | h4 v = S012.value (Fin.castSucc 0)}).connectedComponentMk
        ⟨0, by simp⟩) := by
  have hv : (0 : Fin 4) ∈ (y.1 : Sym2 (Fin 4)) := by
    rcases c4_spans_zero_cases y.1 y.2 with h | h <;> rw [h]
    · exact fst_mem_dartEdge d01
    · exact fst_mem_dartEdge d03
  exact graphPLReebData_left_of_mem C4 h4 S012 0 y hv (by simp)

/-- **F1 right endpoints of the lower gap**: `0 — 1` goes to the component of `1`. -/
theorem c4_right_zero_01 :
    ((graphPLReebData C4 h4 S012).right 0 c4e01 : LevelVertex C4 h4 (S012.value (Fin.succ 0))) =
      Sum.inl ((C4.induce {v | h4 v = S012.value (Fin.succ 0)}).connectedComponentMk
        ⟨1, by simp⟩) :=
  graphPLReebData_right_of_mem C4 h4 S012 0 c4e01 (snd_mem_dartEdge d01) (by simp [d01])

/-- **F1 right endpoints of the lower gap**: `0 — 3` goes to the component of `3`. -/
theorem c4_right_zero_03 :
    ((graphPLReebData C4 h4 S012).right 0 c4e03 : LevelVertex C4 h4 (S012.value (Fin.succ 0))) =
      Sum.inl ((C4.induce {v | h4 v = S012.value (Fin.succ 0)}).connectedComponentMk
        ⟨3, by simp⟩) :=
  graphPLReebData_right_of_mem C4 h4 S012 0 c4e03 (snd_mem_dartEdge d03) (by simp [d03])

/-- **F1 left endpoints of the upper gap**: `1 — 2` goes to the component of `1`. -/
theorem c4_left_one_12 :
    ((graphPLReebData C4 h4 S012).left 1 c4e12 :
        LevelVertex C4 h4 (S012.value (Fin.castSucc 1))) =
      Sum.inl ((C4.induce {v | h4 v = S012.value (Fin.castSucc 1)}).connectedComponentMk
        ⟨1, by simp⟩) :=
  graphPLReebData_left_of_mem C4 h4 S012 1 c4e12 (fst_mem_dartEdge d12) (by simp [d12])

/-- **F1 left endpoints of the upper gap**: `2 — 3` goes to the component of `3`. -/
theorem c4_left_one_23 :
    ((graphPLReebData C4 h4 S012).left 1 c4e23 :
        LevelVertex C4 h4 (S012.value (Fin.castSucc 1))) =
      Sum.inl ((C4.induce {v | h4 v = S012.value (Fin.castSucc 1)}).connectedComponentMk
        ⟨3, by simp⟩) :=
  graphPLReebData_left_of_mem C4 h4 S012 1 c4e23 (snd_mem_dartEdge d23) (by simp [d23])

/-- **F1 right endpoints of the upper gap**: both edges go to the component of `2`. -/
theorem c4_right_one (y : (graphPLReebData C4 h4 S012).E 1) :
    ((graphPLReebData C4 h4 S012).right 1 y : LevelVertex C4 h4 (S012.value (Fin.succ 1))) =
      Sum.inl ((C4.induce {v | h4 v = S012.value (Fin.succ 1)}).connectedComponentMk
        ⟨2, by simp⟩) := by
  have hv : (2 : Fin 4) ∈ (y.1 : Sym2 (Fin 4)) := by
    rcases c4_spans_one_cases y.1 y.2 with h | h <;> rw [h]
    · exact snd_mem_dartEdge d12
    · exact fst_mem_dartEdge d23
  exact graphPLReebData_right_of_mem C4 h4 S012 1 y hv (by simp)

/-- **F1.** The left endpoint map of the lower gap is not injective. -/
theorem c4_left_zero_not_injective :
    ¬ Function.Injective ((graphPLReebData C4 h4 S012).left 0) := fun hinj =>
  c4e01_ne_c4e03 (hinj ((c4_left_zero c4e01).trans (c4_left_zero c4e03).symm))

/-- **F1.** The right endpoint map of the lower gap is injective: the components of `1` and `3`
at level `1` are distinct. -/
theorem c4_right_zero_injective : Function.Injective ((graphPLReebData C4 h4 S012).right 0) := by
  have hne : ((C4.induce {v | h4 v = S012.value (Fin.succ 0)}).connectedComponentMk
      ⟨1, by simp⟩) ≠ (C4.induce {v | h4 v = S012.value (Fin.succ 0)}).connectedComponentMk
      ⟨3, by simp⟩ := fun h => by
    have := congrArg Subtype.val (induce_mk_injective_of_not_adj (c4_level_not_adj _) h)
    exact absurd this (by decide)
  have hcases : ∀ y : (graphPLReebData C4 h4 S012).E 0, y = c4e01 ∨ y = c4e03 := fun y => by
    rcases c4_spans_zero_cases y.1 y.2 with h | h
    · exact .inl (Subtype.ext h)
    · exact .inr (Subtype.ext h)
  intro y y' hyy
  rcases hcases y with rfl | rfl <;> rcases hcases y' with rfl | rfl
  · rfl
  · exact (hne (c4_right_zero_01.symm.trans (hyy.trans c4_right_zero_03) |> Sum.inl_injective)).elim
  · exact (hne (c4_right_zero_01.symm.trans (hyy.symm.trans c4_right_zero_03)
      |> Sum.inl_injective)).elim
  · rfl

/-! ### Identification with the merged cycle data -/

/-- The vertex of the 4-cycle representing vertex `m` of the cycle data at level `i`. -/
private def cycVert (i : Fin 3) (m : ℕ) : Fin 4 :=
  if i = 0 then 0 else if i = 1 then (if m = 0 then 1 else 3) else 2

private theorem h4_cycVert (i : Fin 3) (m : ℕ) : h4 (cycVert i m) = S012.value i := by
  fin_cases i
  · simp [cycVert]
  · by_cases hm : m = 0 <;> simp [cycVert, hm]
  · simp [cycVert]

/-- Lower endpoint of the dart representing edge `m` of the cycle data over gap `i`. -/
private def cycA (i : Fin 2) (m : ℕ) : Fin 4 := if i = 0 then 0 else if m = 0 then 1 else 3

/-- Upper endpoint of the dart representing edge `m` of the cycle data over gap `i`. -/
private def cycB (i : Fin 2) (m : ℕ) : Fin 4 := if i = 0 then (if m = 0 then 1 else 3) else 2

/-- The dart representing edge `y` of the cycle data over gap `i`. -/
private def cycDart (i y : Fin 2) : C4.Dart :=
  ⟨(cycA i y.val, cycB i y.val), by fin_cases i <;> fin_cases y <;> decide⟩

private theorem h4_cycA (i : Fin 2) (m : ℕ) : h4 (cycA i m) = S012.value i.castSucc := by
  fin_cases i
  · simp [cycA]
  · by_cases hm : m = 0 <;> simp [cycA, hm]

private theorem h4_cycB (i : Fin 2) (m : ℕ) : h4 (cycB i m) = S012.value i.succ := by
  fin_cases i
  · by_cases hm : m = 0 <;> simp [cycB, hm]
  · simp [cycB]

private theorem cyc_spans (i y : Fin 2) :
    EdgeSpans C4 h4 (S012.value i.castSucc) (S012.value i.succ) (dartEdge (cycDart i y)) := by
  rw [edgeSpans_dartEdge_iff]
  exact ⟨(min_le_left _ _).trans_eq (h4_cycA i y.val),
    (h4_cycB i y.val).symm.trans_le (le_max_right _ _)⟩

private theorem cycA_eq (i y : Fin 2) :
    cycA i y.val = cycVert i.castSucc (cycleData.left i y).val := by
  fin_cases i <;> fin_cases y <;> decide

private theorem cycB_eq (i y : Fin 2) :
    cycB i y.val = cycVert i.succ (cycleData.right i y).val := by
  fin_cases i <;> fin_cases y <;> decide

/-- The map of finite data from the merged cycle data to the graph-PL data of the 4-cycle. -/
def cycleToGraphPL : FiniteReebData.Hom cycleData (graphPLReebData C4 h4 S012) where
  v i k := Sum.inl ((C4.induce {v | h4 v = S012.value i}).connectedComponentMk
    ⟨cycVert i k.val, h4_cycVert i k.val⟩)
  e i y := ⟨dartEdge (cycDart i y), cyc_spans i y⟩
  left_comm i y := (graphPLReebData_left_of_mem C4 h4 S012 i ⟨dartEdge (cycDart i y), cyc_spans i y⟩
      (fst_mem_dartEdge (cycDart i y)) (h4_cycA i y.val)).trans
    (congrArg Sum.inl (congrArg _ (Subtype.ext (cycA_eq i y))))
  right_comm i y := (graphPLReebData_right_of_mem C4 h4 S012 i
      ⟨dartEdge (cycDart i y), cyc_spans i y⟩
      (snd_mem_dartEdge (cycDart i y)) (h4_cycB i y.val)).trans
    (congrArg Sum.inl (congrArg _ (Subtype.ext (cycB_eq i y))))

private theorem cycVert_injective (i : Fin 3) (a b : cycleData.V i)
    (hab : cycVert i a.val = cycVert i b.val) : a = b := by
  obtain ⟨a, ha⟩ := a
  obtain ⟨b, hb⟩ := b
  apply Fin.ext
  fin_cases i
  · simp at ha hb
    simp only
    omega
  · simp at ha hb
    simp only
    by_cases ha0 : a = 0 <;> by_cases hb0 : b = 0 <;>
      simp [cycVert, ha0, hb0] at hab <;> omega
  · simp at ha hb
    simp only
    omega

private theorem cycleToGraphPL_v_injective (i : Fin 3) :
    Function.Injective (cycleToGraphPL.v i) := fun a b hab =>
  cycVert_injective i a b (congrArg Subtype.val
    (induce_mk_injective_of_not_adj (c4_level_not_adj _) (Sum.inl_injective hab)))

private theorem cycDart_edge_injective (i a b : Fin 2)
    (h : dartEdge (cycDart i a) = dartEdge (cycDart i b)) : a = b := by
  fin_cases i <;> fin_cases a <;> fin_cases b <;> first
    | rfl
    | exact absurd h (dartEdge_ne (by decide) (by decide))

private theorem cycleToGraphPL_e_injective (i : Fin 2) :
    Function.Injective (cycleToGraphPL.e i) := fun a b hab =>
  cycDart_edge_injective i a b (congrArg Subtype.val hab)

private theorem card_cycleData_V (i : Fin 3) : Nat.card (cycleData.V i) = ![1, 2, 1] i := by
  show Nat.card (Fin _) = _
  exact Nat.card_eq_fintype_card.trans (Fintype.card_fin _)

private theorem cycleToGraphPL_v_bijective (i : Fin 3) :
    Function.Bijective (cycleToGraphPL.v i) := by
  refine (cycleToGraphPL_v_injective i).bijective_of_nat_card_le ?_
  rw [card_cycleData_V]
  fin_cases i
  · exact c4_card_V0.le
  · exact c4_card_V1.le
  · exact c4_card_V2.le

private theorem cycleToGraphPL_e_bijective (i : Fin 2) :
    Function.Bijective (cycleToGraphPL.e i) := by
  refine (cycleToGraphPL_e_injective i).bijective_of_nat_card_le ?_
  rw [show Nat.card (cycleData.E i) = 2 from by show Nat.card (Fin 2) = 2; simp]
  fin_cases i
  · exact c4_edgeCounts.1.le
  · exact c4_edgeCounts.2.le

/-- The cycle data and the graph-PL data of the 4-cycle are isomorphic. -/
def cycleIso : cycleData ≅ graphPLReebData C4 h4 S012 where
  hom := cycleToGraphPL
  inv := cycleToGraphPL.inv cycleToGraphPL_v_bijective cycleToGraphPL_e_bijective
  hom_inv_id := cycleToGraphPL.comp_inv _ _
  inv_hom_id := cycleToGraphPL.inv_comp _ _

/-- **F1 identification.** The graph-PL data of the 4-cycle are the merged cycle data. -/
theorem c4_iso_cycleData : Nonempty (graphPLReebData C4 h4 S012 ≅ cycleData) :=
  ⟨cycleIso.symm⟩

/-- **F1 consequence.** The realization of the graph-PL data of the 4-cycle is not the path. -/
theorem c4_not_iso_path :
    IsEmpty (toOver S012 (graphPLReebData C4 h4 S012) ≅ toOver S012 pathData) :=
  ⟨fun i => cycle_not_iso_path.false (((realizationFunctor S012).mapIso cycleIso).trans i)⟩

/-- **F1 through (i).** The preimage of the star `(0, 2)` of level `1` has two path components. -/
theorem c4_star_one_card :
    Nat.card ((intervalComponents (plHeight C4 h4)).obj (S012.J 1)) = 2 :=
  (Nat.card_congr (graphPLStarEquiv C4 h4 S012 c4_covers 1)).trans c4_card_V1

end Cycle

/-! ## F2. The single edge -/

section SingleEdge

@[simp] private theorem h02_false' : h02 false = 0 := rfl

@[simp] private theorem h02_true' : h02 true = 2 := rfl

@[simp] private theorem S02_zero : S02.value 0 = 0 := by
  show 2 * ((0 : ℕ) : ℝ) = 0
  norm_num

@[simp] private theorem S02_one : S02.value 1 = 2 := by
  show 2 * ((1 : ℕ) : ℝ) = 2
  norm_num

private theorem edge_cases (e : edgeGraph.edgeSet) : e = dartEdge d₀ := by
  obtain ⟨d, rfl⟩ := exists_dartEdge_eq e
  rcases edgeGraph_dart d with rfl | rfl
  · rfl
  · exact dartEdge_symm d₀

private theorem edge_mem (y : edgeGraph.edgeSet) (b : Bool) : b ∈ (y : Sym2 Bool) := by
  rw [edge_cases y]
  cases b
  · exact fst_mem_dartEdge d₀
  · exact snd_mem_dartEdge d₀

private theorem h02_nonneg' (v : Bool) : 0 ≤ h02 v := by cases v <;> norm_num

private theorem h02_le_two' (v : Bool) : h02 v ≤ 2 := by cases v <;> norm_num

/-- The levels `0, 2` cover the heights of the single edge. -/
theorem edge_covers_S02 : CoversVertexHeights S02 h02 := fun v => by
  cases v
  · exact ⟨0, by simp⟩
  · exact ⟨1, by simp⟩

private theorem edge_spans_S02 :
    EdgeSpans edgeGraph h02 (S02.value (Fin.castSucc 0)) (S02.value (Fin.succ 0)) (dartEdge d₀) := by
  rw [edgeSpans_dartEdge_iff]
  norm_num [d₀]

/-- **F2 at `0 < 2`.** One Reeb vertex per level and one Reeb edge. -/
theorem edge_S02_counts :
    Nat.card ((graphPLReebData edgeGraph h02 S02).V 0) = 1 ∧
      Nat.card ((graphPLReebData edgeGraph h02 S02).V 1) = 1 ∧
      Nat.card ((graphPLReebData edgeGraph h02 S02).E 0) = 1 :=
  ⟨card_levelVertex edgeGraph h02 _
      (card_induce_singleton (v₀ := false) (by simp) fun v hv => by cases v <;> simp_all)
      (card_zero_of (not_edgeCrosses_of_le fun v => by rw [S02_zero]; exact h02_nonneg' v)),
    card_levelVertex edgeGraph h02 _
      (card_induce_singleton (v₀ := true) (by simp) fun v hv => by cases v <;> simp_all)
      (card_zero_of (not_edgeCrosses_of_ge fun v => by rw [S02_one]; exact h02_le_two' v)),
    card_one_of edge_spans_S02 fun e _ => edge_cases e⟩

/-- **F2 at `0 < 2`.** Both endpoint maps land in the level-component branch. -/
theorem edge_S02_endpoints (y : (graphPLReebData edgeGraph h02 S02).E 0) :
    ((graphPLReebData edgeGraph h02 S02).left 0 y :
        LevelVertex edgeGraph h02 (S02.value (Fin.castSucc 0))) =
      Sum.inl ((edgeGraph.induce {v | h02 v = S02.value (Fin.castSucc 0)}).connectedComponentMk
        ⟨false, by simp⟩) ∧
    ((graphPLReebData edgeGraph h02 S02).right 0 y :
        LevelVertex edgeGraph h02 (S02.value (Fin.succ 0))) =
      Sum.inl ((edgeGraph.induce {v | h02 v = S02.value (Fin.succ 0)}).connectedComponentMk
        ⟨true, by simp⟩) :=
  ⟨graphPLReebData_left_of_mem edgeGraph h02 S02 0 y (edge_mem y.1 false) (by simp),
    graphPLReebData_right_of_mem edgeGraph h02 S02 0 y (edge_mem y.1 true) (by simp)⟩

/-- The levels `0, 1, 2` cover the heights of the single edge; the level `1` carries no vertex. -/
theorem edge_covers_S012 : CoversVertexHeights S012 h02 := fun v => by
  cases v
  · exact ⟨0, by simp⟩
  · exact ⟨2, by simp⟩

/-- The single edge crosses the level `1`. -/
theorem edge_crosses_one : EdgeCrosses edgeGraph h02 (S012.value 1) (dartEdge d₀) := by
  rw [edgeCrosses_dartEdge_iff]
  norm_num [d₀]

/-- **F2 at `0 < 1 < 2`.** The level `1` has an empty level graph and one crossing edge. -/
theorem edge_S012_V1 :
    Nat.card (edgeGraph.induce {v | h02 v = S012.value 1}).ConnectedComponent = 0 ∧
      Nat.card ((graphPLReebData edgeGraph h02 S012).V 1) = 1 := by
  have h0 : Nat.card (edgeGraph.induce {v | h02 v = S012.value 1}).ConnectedComponent = 0 :=
    card_induce_empty fun v hv => by cases v <;> norm_num at hv
  exact ⟨h0, card_levelVertex edgeGraph h02 _ h0
    (card_one_of edge_crosses_one fun e _ => edge_cases e)⟩

/-- **F2 at `0 < 1 < 2`.** The two incident gaps send the edge to one crossing vertex. -/
theorem edge_S012_crossing
    (y : (graphPLReebData edgeGraph h02 S012).E 0) (y' : (graphPLReebData edgeGraph h02 S012).E 1) :
    ((graphPLReebData edgeGraph h02 S012).right 0 y : LevelVertex edgeGraph h02 (S012.value 1)) =
        Sum.inr ⟨dartEdge d₀, edge_crosses_one⟩ ∧
      ((graphPLReebData edgeGraph h02 S012).left 1 y' :
        LevelVertex edgeGraph h02 (S012.value 1)) = Sum.inr ⟨dartEdge d₀, edge_crosses_one⟩ := by
  have hne : ∀ v : Bool, h02 v ≠ S012.value 1 := fun v => by cases v <;> norm_num
  refine ⟨(graphPLReebData_right_of_forall_ne edgeGraph h02 S012 0 y fun v _ => hne v).trans ?_,
    (graphPLReebData_left_of_forall_ne edgeGraph h02 S012 1 y' fun v _ => hne v).trans ?_⟩
  · exact congrArg Sum.inr (Subtype.ext (edge_cases y.1))
  · exact congrArg Sum.inr (Subtype.ext (edge_cases y'.1))

/-- **F2 through (i).** The preimage of `(0, 2)` is one open arc without a vertex. -/
theorem edge_star_one_card :
    Nat.card ((intervalComponents (plHeight edgeGraph h02)).obj (S012.J 1)) = 1 :=
  (Nat.card_congr (graphPLStarEquiv edgeGraph h02 S012 edge_covers_S012 1)).trans edge_S012_V1.2

end SingleEdge

/-! ## F3. The subdivided Y-tree at `0 < 1 < 2 < 3` -/

section YTree

/-- Levels `0 < 1 < 2 < 3`. -/
def S0123 : CriticalValues 3 where
  value i := ((i : ℕ) : ℝ)
  strictMono _ _ h := Nat.cast_lt.2 h

@[simp] private theorem S0123_zero : S0123.value 0 = 0 := by
  show ((0 : ℕ) : ℝ) = 0
  norm_num

@[simp] private theorem S0123_one : S0123.value 1 = 1 := by
  show ((1 : ℕ) : ℝ) = 1
  norm_num

@[simp] private theorem S0123_two : S0123.value 2 = 2 := by
  show ((2 : ℕ) : ℝ) = 2
  norm_num

@[simp] private theorem S0123_three : S0123.value 3 = 3 := by
  show ((3 : ℕ) : ℝ) = 3
  norm_num

@[simp] private theorem S0123_castSucc_two : S0123.value (Fin.castSucc 2) = 2 := by
  show ((2 : ℕ) : ℝ) = 2
  norm_num

@[simp] private theorem S0123_succ_two : S0123.value (Fin.succ 2) = 3 := by
  show ((3 : ℕ) : ℝ) = 3
  norm_num

@[simp] private theorem hY_zero' : hY 0 = 0 := rfl

@[simp] private theorem hY_one' : hY 1 = 1 := rfl

@[simp] private theorem hY_two' : hY 2 = 2 := rfl

@[simp] private theorem hY_three' : hY 3 = 3 := rfl

/-- The levels `0, 1, 2, 3` cover the heights of the tree. -/
theorem Y_covers : CoversVertexHeights S0123 hY := fun v => ⟨v, by fin_cases v <;> simp [hY, S0123]⟩

/-- Every level set of the tree is a single vertex. -/
private theorem Y_level_card (k : Fin 4) :
    Nat.card (Y.induce {v | hY v = S0123.value k}).ConnectedComponent = 1 :=
  card_induce_singleton (v₀ := k) (by fin_cases k <;> simp [hY, S0123]) fun v hv => by
    fin_cases v <;> fin_cases k <;> first | rfl | simp_all [hY, S0123]

private theorem Y_nonneg (v : Fin 4) : 0 ≤ hY v := by fin_cases v <;> norm_num [hY]

private theorem Y_le_three (v : Fin 4) : hY v ≤ 3 := by fin_cases v <;> norm_num [hY]

/-- The edge `0 — 2` crosses the level `1`. -/
theorem Y_crosses_one : EdgeCrosses Y hY (S0123.value 1) (dartEdge y02) := by
  rw [edgeCrosses_dartEdge_iff]
  norm_num [y02]

private theorem Y_card_V1 : Nat.card ((graphPLReebData Y hY S0123).V 1) = 2 :=
  card_levelVertex Y hY _ (Y_level_card 1)
    (card_one_of Y_crosses_one fun e he => by
      rcases Y_edge_cases e with rfl | rfl | rfl
      · rfl
      · exact absurd he (not_edgeCrosses_dartEdge_of_eq (.inl (by show hY 1 = _; simp)))
      · rw [edgeCrosses_dartEdge_iff] at he
        norm_num [y23] at he)

/-- **F3 vertex counts** `1, 2, 1, 1`. -/
theorem Y_vertexCounts :
    Nat.card ((graphPLReebData Y hY S0123).V 0) = 1 ∧
      Nat.card ((graphPLReebData Y hY S0123).V 1) = 2 ∧
      Nat.card ((graphPLReebData Y hY S0123).V 2) = 1 ∧
      Nat.card ((graphPLReebData Y hY S0123).V 3) = 1 := by
  refine ⟨card_levelVertex Y hY _ (Y_level_card 0)
      (card_zero_of (not_edgeCrosses_of_le fun v => by rw [S0123_zero]; exact Y_nonneg v)),
    Y_card_V1,
    card_levelVertex Y hY _ (Y_level_card 2) (card_zero_of fun e => ?_),
    card_levelVertex Y hY _ (Y_level_card 3)
      (card_zero_of (not_edgeCrosses_of_ge fun v => by rw [S0123_three]; exact Y_le_three v))⟩
  rcases Y_edge_cases e with rfl | rfl | rfl
  · exact not_edgeCrosses_dartEdge_of_eq (.inr (by show hY 2 = _; simp))
  · exact not_edgeCrosses_dartEdge_of_eq (.inr (by show hY 2 = _; simp))
  · exact not_edgeCrosses_dartEdge_of_eq (.inl (by show hY 2 = _; simp))

private theorem Y_spans_02_zero :
    EdgeSpans Y hY (S0123.value (Fin.castSucc 0)) (S0123.value (Fin.succ 0)) (dartEdge y02) := by
  rw [edgeSpans_dartEdge_iff]
  norm_num [y02]

private theorem Y_spans_02_one :
    EdgeSpans Y hY (S0123.value (Fin.castSucc 1)) (S0123.value (Fin.succ 1)) (dartEdge y02) := by
  rw [edgeSpans_dartEdge_iff]
  norm_num [y02]

private theorem Y_spans_12_one :
    EdgeSpans Y hY (S0123.value (Fin.castSucc 1)) (S0123.value (Fin.succ 1)) (dartEdge y12) := by
  rw [edgeSpans_dartEdge_iff]
  norm_num [y12]

private theorem Y_spans_23_two :
    EdgeSpans Y hY (S0123.value (Fin.castSucc 2)) (S0123.value (Fin.succ 2)) (dartEdge y23) := by
  rw [edgeSpans_dartEdge_iff]
  norm_num [y23]

private theorem Y_spans_one_cases (e : Y.edgeSet)
    (he : EdgeSpans Y hY (S0123.value (Fin.castSucc 1)) (S0123.value (Fin.succ 1)) e) :
    e = dartEdge y02 ∨ e = dartEdge y12 := by
  rcases Y_edge_cases e with rfl | rfl | rfl
  · exact .inl rfl
  · exact .inr rfl
  · rw [edgeSpans_dartEdge_iff] at he
    norm_num [y23] at he

/-- **F3 edge counts** `1, 2, 1`: `0 — 2`, then `0 — 2, 1 — 2`, then `2 — 3`. -/
theorem Y_edgeCounts :
    Nat.card ((graphPLReebData Y hY S0123).E 0) = 1 ∧
      Nat.card ((graphPLReebData Y hY S0123).E 1) = 2 ∧
      Nat.card ((graphPLReebData Y hY S0123).E 2) = 1 := by
  refine ⟨card_one_of Y_spans_02_zero fun e he => ?_,
    card_two_of (dartEdge_ne (by decide) (by decide)) Y_spans_02_one Y_spans_12_one
      Y_spans_one_cases,
    card_one_of Y_spans_23_two fun e he => ?_⟩
  · rcases Y_edge_cases e with rfl | rfl | rfl
    · rfl
    · rw [edgeSpans_dartEdge_iff] at he
      norm_num [y12] at he
    · rw [edgeSpans_dartEdge_iff] at he
      norm_num [y23] at he
  · rcases Y_edge_cases e with rfl | rfl | rfl
    · rw [edgeSpans_dartEdge_iff] at he
      norm_num [y02] at he
    · rw [edgeSpans_dartEdge_iff] at he
      norm_num [y12] at he
    · rfl

/-- **F3 endpoints at the crossing.** `0 — 2` meets the level `1` in a degree-two Reeb vertex: the
right endpoint over the lower gap and the left endpoint over the middle gap are the crossing
vertex. -/
theorem Y_crossing_endpoints :
    ((graphPLReebData Y hY S0123).right 0 ⟨dartEdge y02, Y_spans_02_zero⟩ :
        LevelVertex Y hY (S0123.value 1)) = Sum.inr ⟨dartEdge y02, Y_crosses_one⟩ ∧
      ((graphPLReebData Y hY S0123).left 1 ⟨dartEdge y02, Y_spans_02_one⟩ :
        LevelVertex Y hY (S0123.value 1)) = Sum.inr ⟨dartEdge y02, Y_crosses_one⟩ := by
  have hne : ∀ v ∈ (dartEdge y02 : Sym2 (Fin 4)), hY v ≠ S0123.value 1 := by
    intro v hv
    rcases mem_dartEdge.1 hv with rfl | rfl <;> norm_num [y02]
  exact ⟨graphPLReebData_right_of_forall_ne Y hY S0123 0 _ hne,
    graphPLReebData_left_of_forall_ne Y hY S0123 1 _ hne⟩

/-- **F3 endpoints over the middle gap.** `1 — 2` starts at the level component of `1`, and both
edges end at the level component of `2`. -/
theorem Y_middle_endpoints :
    ((graphPLReebData Y hY S0123).left 1 ⟨dartEdge y12, Y_spans_12_one⟩ :
        LevelVertex Y hY (S0123.value (Fin.castSucc 1))) =
      Sum.inl ((Y.induce {v | hY v = S0123.value (Fin.castSucc 1)}).connectedComponentMk
        ⟨1, by simp⟩) ∧
    ∀ y : (graphPLReebData Y hY S0123).E 1,
      ((graphPLReebData Y hY S0123).right 1 y : LevelVertex Y hY (S0123.value (Fin.succ 1))) =
        Sum.inl ((Y.induce {v | hY v = S0123.value (Fin.succ 1)}).connectedComponentMk
          ⟨2, by simp⟩) := by
  refine ⟨graphPLReebData_left_of_mem Y hY S0123 1 _ (fst_mem_dartEdge y12) (by simp),
    fun y => ?_⟩
  have hv : (2 : Fin 4) ∈ (y.1 : Sym2 (Fin 4)) := by
    rcases Y_spans_one_cases y.1 y.2 with h | h <;> rw [h]
    · exact snd_mem_dartEdge y02
    · exact snd_mem_dartEdge y12
  exact graphPLReebData_right_of_mem Y hY S0123 1 y hv (by simp)

/-- **F3 agreement with the MultiNerve Mapper cells.** The counts agree with the merged vertex and
edge cell counts of the height-separating cover `uniformCover (-1/2) (5/4) (1/4) 4`. -/
theorem Y_counts_eq_cells :
    Nat.card ((graphPLReebData Y hY S0123).V 1) =
        Nat.card {c : multiNerveMapper (plHeight Y hY)
          (fun k : Fin 4 => ((uniformCover (-1 / 2 : ℝ) (5 / 4) (1 / 4) 4 k : OpenInterval) :
            Set ℝ)) // c.support.image Sigma.fst = {1}} ∧
      Nat.card ((graphPLReebData Y hY S0123).V 0) =
        Nat.card {c : multiNerveMapper (plHeight Y hY)
          (fun k : Fin 4 => ((uniformCover (-1 / 2 : ℝ) (5 / 4) (1 / 4) 4 k : OpenInterval) :
            Set ℝ)) // c.support.image Sigma.fst = {0}} ∧
      Nat.card ((graphPLReebData Y hY S0123).V 2) =
        Nat.card {c : multiNerveMapper (plHeight Y hY)
          (fun k : Fin 4 => ((uniformCover (-1 / 2 : ℝ) (5 / 4) (1 / 4) 4 k : OpenInterval) :
            Set ℝ)) // c.support.image Sigma.fst = {2}} ∧
      Nat.card ((graphPLReebData Y hY S0123).V 3) =
        Nat.card {c : multiNerveMapper (plHeight Y hY)
          (fun k : Fin 4 => ((uniformCover (-1 / 2 : ℝ) (5 / 4) (1 / 4) 4 k : OpenInterval) :
            Set ℝ)) // c.support.image Sigma.fst = {3}} ∧
      Nat.card ((graphPLReebData Y hY S0123).E 0) =
        Nat.card {c : multiNerveMapper (plHeight Y hY)
          (fun k : Fin 4 => ((uniformCover (-1 / 2 : ℝ) (5 / 4) (1 / 4) 4 k : OpenInterval) :
            Set ℝ)) // c.support.image Sigma.fst = {0, 1}} ∧
      Nat.card ((graphPLReebData Y hY S0123).E 1) =
        Nat.card {c : multiNerveMapper (plHeight Y hY)
          (fun k : Fin 4 => ((uniformCover (-1 / 2 : ℝ) (5 / 4) (1 / 4) 4 k : OpenInterval) :
            Set ℝ)) // c.support.image Sigma.fst = {1, 2}} ∧
      Nat.card ((graphPLReebData Y hY S0123).E 2) =
        Nat.card {c : multiNerveMapper (plHeight Y hY)
          (fun k : Fin 4 => ((uniformCover (-1 / 2 : ℝ) (5 / 4) (1 / 4) 4 k : OpenInterval) :
            Set ℝ)) // c.support.image Sigma.fst = {2, 3}} :=
  ⟨Y_vertexCounts.2.1.trans Y_vertexCells_one.symm,
    Y_vertexCounts.1.trans Y_vertexCells_other.1.symm,
    Y_vertexCounts.2.2.1.trans Y_vertexCells_other.2.1.symm,
    Y_vertexCounts.2.2.2.trans Y_vertexCells_other.2.2.symm,
    Y_edgeCounts.1.trans Y_edgeCells.1.symm,
    Y_edgeCounts.2.1.trans Y_edgeCells.2.1.symm,
    Y_edgeCounts.2.2.trans Y_edgeCells.2.2.symm⟩

end YTree

/-! ## F4. One vertex -/

section Point

/-- **F4.** One isolated vertex of height `0` at the single level `0`: one Reeb vertex, and no
gap carries an edge type. -/
theorem point_counts :
    Nat.card ((graphPLReebData pointGraph (fun _ => (0 : ℝ)) S0).V 0) = 1 ∧
      ∀ e : Fin 0, IsEmpty ((graphPLReebData pointGraph (fun _ => (0 : ℝ)) S0).E e) :=
  ⟨card_levelVertex pointGraph _ _
      (card_induce_singleton (v₀ := ()) rfl fun _ _ => rfl)
      (card_zero_of fun e _ => bot_edge_false e),
    fun e => e.elim0⟩

/-- **F4.** The canonical list of a single height has no gap. -/
theorem point_vertexGapCount : vertexGapCount (fun _ : Unit => (0 : ℝ)) = 0 := by
  simp [vertexGapCount, vertexHeightSet]

/-- **F4.** The canonical list covers the single height. -/
theorem point_covers :
    CoversVertexHeights (vertexHeightLevels (fun _ : Unit => (0 : ℝ))) fun _ : Unit => (0 : ℝ) :=
  coversVertexHeights_vertexHeightLevels _

end Point

/-! ## F5. Horizontal edges -/

section Horizontal

/-- Heights `0, 1, 1` on the path `0 — 1 — 2`. -/
def h011 : Fin 3 → ℝ := ![0, 1, 1]

@[simp] private theorem h011_zero : h011 0 = 0 := rfl

@[simp] private theorem h011_one : h011 1 = 1 := rfl

@[simp] private theorem h011_two : h011 2 = 1 := rfl

/-- The dart `0 → 1` of the path. -/
def p01 : path3.Dart := ⟨(0, 1), pathGraph_adj.2 (.inl (by decide))⟩

/-- The horizontal dart `1 → 2` of the path. -/
def p12 : path3.Dart := ⟨(1, 2), pathGraph_adj.2 (.inl (by decide))⟩

private theorem path3_edge_cases (e : path3.edgeSet) : e = dartEdge p01 ∨ e = dartEdge p12 := by
  obtain ⟨⟨⟨a, b⟩, hab⟩, rfl⟩ := exists_dartEdge_eq e
  have hab' := pathGraph_adj.1 hab
  fin_cases a <;> fin_cases b <;> first
    | exact absurd hab' (by decide)
    | exact Or.inl rfl
    | exact Or.inl (Subtype.ext Sym2.eq_swap)
    | exact Or.inr rfl
    | exact Or.inr (Subtype.ext Sym2.eq_swap)

/-- The levels `0, 1` cover the heights `0, 1, 1`. -/
theorem path_covers : CoversVertexHeights S01 h011 := fun v => by
  fin_cases v
  · exact ⟨0, by simp⟩
  · exact ⟨1, by simp⟩
  · exact ⟨1, by simp⟩

private theorem path_spans_p01 :
    EdgeSpans path3 h011 (S01.value (Fin.castSucc 0)) (S01.value (Fin.succ 0)) (dartEdge p01) := by
  rw [edgeSpans_dartEdge_iff]
  norm_num [p01]

/-- **F5.** The horizontal edge `1 — 2` spans no gap. -/
theorem path_not_spans_p12 :
    ¬ EdgeSpans path3 h011 (S01.value (Fin.castSucc 0)) (S01.value (Fin.succ 0)) (dartEdge p12) := by
  rw [edgeSpans_dartEdge_iff]
  norm_num [p12]

/-- **F5 counts.** One Reeb vertex per level: the level graph at `1` is the edge `1 — 2`. One Reeb
edge, `0 — 1`. -/
theorem path_counts :
    Nat.card ((graphPLReebData path3 h011 S01).V 0) = 1 ∧
      Nat.card ((graphPLReebData path3 h011 S01).V 1) = 1 ∧
      Nat.card ((graphPLReebData path3 h011 S01).E 0) = 1 := by
  refine ⟨card_levelVertex path3 h011 _
      (card_induce_singleton (v₀ := 0) (by simp) fun v hv => by fin_cases v <;> simp_all [h011])
      (card_zero_of (not_edgeCrosses_of_le fun v => by
        rw [S01_value_zero]; fin_cases v <;> norm_num [h011])),
    card_levelVertex path3 h011 _
      (card_induce_complete (v₀ := 1) (by simp) fun x hx y hy hxy => ?_)
      (card_zero_of (not_edgeCrosses_of_ge fun v => by
        rw [S01_value_one]; fin_cases v <;> norm_num [h011])),
    card_one_of path_spans_p01 fun e he => ?_⟩
  · fin_cases x <;> fin_cases y <;> first
      | exact absurd rfl hxy
      | exact pathGraph_adj.2 (by decide)
      | simp_all [h011]
  · rcases path3_edge_cases e with rfl | rfl
    · rfl
    · exact absurd he path_not_spans_p12

/-- **F5 endpoint.** The horizontal edge merges `1` and `2`: the edge `0 — 1` ends at the level
component of `2`. -/
theorem path_right_zero :
    ((graphPLReebData path3 h011 S01).right 0 ⟨dartEdge p01, path_spans_p01⟩ :
        LevelVertex path3 h011 (S01.value (Fin.succ 0))) =
      Sum.inl ((path3.induce {v | h011 v = S01.value (Fin.succ 0)}).connectedComponentMk
        ⟨2, by simp⟩) :=
  (graphPLReebData_right_of_mem path3 h011 S01 0 _ (snd_mem_dartEdge p01) (by simp)).trans
    (congrArg Sum.inl (ConnectedComponent.connectedComponentMk_eq_of_adj
      (show path3.Adj 1 2 from pathGraph_adj.2 (.inl (by decide)))))

/-- **F5.** The single edge of constant height `0` at the level `0`: one Reeb vertex. -/
theorem flatEdge_count : Nat.card ((graphPLReebData edgeGraph (fun _ => (0 : ℝ)) S0).V 0) = 1 :=
  card_levelVertex edgeGraph _ _
    (card_induce_complete (v₀ := false) rfl fun _ _ _ _ hxy => hxy)
    (card_zero_of (not_edgeCrosses_of_le fun _ => le_rfl))

end Horizontal

/-! ## F6. Equal heights without connection -/

section Isolated

/-- The levels `{0}` cover a constant height `0`. -/
theorem const_covers {V : Type*} : CoversVertexHeights S0 fun _ : V => (0 : ℝ) :=
  fun _ => ⟨0, rfl⟩

/-- **F6.** Two isolated vertices of height `0`: two Reeb vertices, against one for the edge. -/
theorem isolated_count :
    Nat.card ((graphPLReebData (⊥ : SimpleGraph Bool) (fun _ => (0 : ℝ)) S0).V 0) = 2 :=
  card_levelVertex (⊥ : SimpleGraph Bool) _ _
    ((card_induce_of_not_adj fun _ _ _ _ h => h).trans
      (card_two_of (P := fun v => v ∈ {v : Bool | (0 : ℝ) = S0.value 0}) Bool.false_ne_true rfl
        rfl fun v _ => by cases v <;> simp))
    (card_zero_of fun e _ => bot_edge_false e)

/-- **F6 through (i).** The realization of two isolated vertices has two path components. -/
theorem isolated_components :
    Nat.card ((intervalComponents (plHeight (⊥ : SimpleGraph Bool) fun _ => (0 : ℝ))).obj ⊤) =
      2 := by
  rw [← S0.J_eq_top_of_zero]
  exact (Nat.card_congr (graphPLStarEquiv (⊥ : SimpleGraph Bool) _ S0 const_covers 0)).trans
    isolated_count

end Isolated

/-! ## F7. A list missing a vertex height -/

section Missing

/-- **F7.** The single level `0` misses the height `2`. -/
theorem missing_not_covers : ¬ CoversVertexHeights S0 h02 := fun hS => by
  obtain ⟨i, hi⟩ := hS true
  have : (0 : ℝ) = 2 := hi
  norm_num at this

/-- **F7.** Over the star `ℝ` the two isolated vertices give two path components, through the
incidence comparison and the splitting with no uncovered edge. -/
theorem missing_star_card :
    Nat.card ((intervalComponents (plHeight (⊥ : SimpleGraph Bool) h02)).obj (S0.J 0)) = 2 := by
  rw [S0.J_eq_top_of_zero]
  have := isEmpty_uncoveredEdge_of_coverage (⊥ : SimpleGraph Bool) h02 ⊤
    (endpointCoverage_top _ _)
  refine (Nat.card_congr ((preimageComponentsEquiv (⊥ : SimpleGraph Bool) h02 ⊤).trans
    (cellComponentsEquivSum (⊥ : SimpleGraph Bool) h02 ⊤))).trans ?_
  rw [Nat.card_sum,
    card_induce_of_not_adj fun _ _ _ _ h => h, Nat.card_of_isEmpty (α := UncoveredEdge _ _ _)]
  exact card_two_of (P := fun v => v ∈ h02 ⁻¹' ((⊤ : OpenInterval) : Set ℝ)) Bool.false_ne_true
    trivial trivial fun v _ => by cases v <;> simp

/-- **F7.** The data at the single level `0` have one Reeb vertex, the vertex of height `0`. -/
theorem missing_count : Nat.card ((graphPLReebData (⊥ : SimpleGraph Bool) h02 S0).V 0) = 1 :=
  card_levelVertex (⊥ : SimpleGraph Bool) h02 _
    (card_induce_singleton (v₀ := false) rfl fun v hv => by
      cases v
      · rfl
      · have : (2 : ℝ) = 0 := hv
        norm_num at this)
    (card_zero_of fun e _ => bot_edge_false e)

/-- **F7.** Without covering, the star comparison fails: no bijection exists. -/
theorem missing_no_equiv :
    IsEmpty ((intervalComponents (plHeight (⊥ : SimpleGraph Bool) h02)).obj (S0.J 0) ≃
      (graphPLReebData (⊥ : SimpleGraph Bool) h02 S0).V 0) :=
  ⟨fun e => by
    have := Nat.card_congr e
    rw [missing_star_card, missing_count] at this
    norm_num at this⟩

end Missing

/-! ## F8. The empty graph -/

section Empty

/-- **F8.** The empty graph at the single level `0`: no Reeb vertex, and the star comparison holds
with both sides empty. No nonemptiness is needed for the construction. -/
theorem empty_data :
    IsEmpty ((graphPLReebData (⊥ : SimpleGraph Empty) Empty.elim S0).V 0) ∧
      IsEmpty ((intervalComponents (plHeight (⊥ : SimpleGraph Empty) Empty.elim)).obj (S0.J 0)) ∧
      Nonempty ((intervalComponents (plHeight (⊥ : SimpleGraph Empty) Empty.elim)).obj (S0.J 0) ≃
        (graphPLReebData (⊥ : SimpleGraph Empty) Empty.elim S0).V 0) := by
  have hV : IsEmpty ((graphPLReebData (⊥ : SimpleGraph Empty) Empty.elim S0).V 0) :=
    ⟨fun x => by
      rcases x with c | e
      · induction c using ConnectedComponent.ind with
        | h v => exact v.1.elim
      · exact bot_edge_false e.1⟩
  have e := graphPLStarEquiv (⊥ : SimpleGraph Empty) Empty.elim S0 (fun v => v.elim) 0
  exact ⟨hV, e.isEmpty, ⟨e⟩⟩

end Empty

end

end TDA.Mapper.GraphPLReebDataExamples
