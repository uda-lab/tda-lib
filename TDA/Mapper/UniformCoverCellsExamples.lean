import TDA.Mapper.UniformCoverCells
import TDA.Mapper.UniformCoverExamples

/-!
# Height-separating uniform-cover fixtures

Acceptance fixtures for `TDA.Mapper.UniformCoverCells`, on the merged graph-PL objects. Every count
is a `Nat.card` equality derived through the new equivalences.

* **4-cycle, three members.** For `C4` with heights `0, 1, 2, 1` the attained range is `[0, 2]` and
  `uniformCover (-1/8) 1 (3/8) 3` is height-separating. The vertex cells over `{0}`, `{1}`, `{2}`
  number `1, 2, 1` through the level branch, in agreement with the merged preimage counts; over
  `{1}` the vertices `1` and `3` are not adjacent and no edge crosses height `1`. The edge cells
  over `{0, 1}` and `{1, 2}` number `2` each, spanned by `0 — 1, 0 — 3` and by `1 — 2, 2 — 3`. Read
  informally, there is one cell at height `0`, two at height `1` and one at height `2`, the shape
  of a cycle, matching the Reeb graph of the 4-cycle because the level set at `1` has two
  components. No incidence, multigraph or Reeb graph is stated here.
* **Single edge, same cover.** Member `1 = (1/2, 3/2)` contains no vertex height; its one vertex
  cell comes from the spanning edge. Members `0` and `2` give one cell each through the level
  branch.
* **Subdivided Y-tree.** On `Fin 4` with edges `0 — 2`, `1 — 2`, `2 — 3` and heights `0, 1, 2, 3`,
  the cover `uniformCover (-1/2) (5/4) (1/4) 4` is height-separating and the attained range is
  `[0, 3]`. The vertex cells over `{1}` number `2`: one level component and the crossing edge
  `0 — 2`. The other members carry one vertex cell each, and the consecutive pairs carry `1, 2, 1`
  edge cells.
* **One member.** The single member `(-1/2, 5/2)` contains both heights of the single edge, so the
  family is not height-separating; the splitting still gives one vertex cell.
* **Vertex height in an overlap.** For `uniformCover (-1/4) (3/2) (1/2) 3` on the 4-cycle the
  overlap `(3/4, 5/4)` contains the height `1`. There are two edge cells over `{0, 1}` but no edge
  spans `[3/4, 5/4]`: the spanning classification fails without its hypothesis.
* **Disconnected graph.** For two isolated vertices of heights `0` and `2` the height `1` is not
  attained: connectedness cannot be dropped from `range_plHeight_eq_Icc`.
* **Boundary of the strict and non-strict predicates.** For the single edge of heights `0` and `2`,
  the edge spans `[0, 2]` and is the one active edge over `(0, 2)`, while it crosses neither
  endpoint height `0` nor `2`.
* **Far labels.** `uniformCover (-1/4) (3/2) 1 3` is height-separating for the single edge, but
  with `2g > r` its labels `0` and `2` meet and carry an edge cell.
* **Existence.** `heightSeparating_covers_range` gives a height-separating cover of the attained
  range of the 4-cycle with `r < 1/2`; no counts are stated.
-/

namespace TDA.Mapper.UniformCoverCellsExamples

open Finset Set SimpleGraph
open TDA.Topology TDA.Topology.MultiNerveCell
open TDA.Reeb TDA.Reeb.GraphPL TDA.Reeb.GraphRealization TDA.Reeb.OpenInterval
open TDA.Reeb.Examples.GraphPL
open TDA.Reeb.Examples.GraphRealization (edgeGraph d₀ edgeGraph_dart)
open TDA.Mapper.GraphPL
open TDA.Mapper.UniformCoverExamples (d12 d03 c4_edge_cases h4_mem_Icc oneMember_eq_J4)

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

/-- A sum of two finite types with computed cardinalities. -/
private theorem card_eq_add_of_equiv {β γ : Type*} [Finite β] [Finite γ] (e : α ≃ β ⊕ γ)
    {m k : ℕ} (hm : Nat.card β = m) (hk : Nat.card γ = k) : Nat.card α = m + k := by
  rw [Nat.card_congr e, Nat.card_sum, hm, hk]

variable {V : Type*} {G : SimpleGraph V}

/-- Without adjacency between the vertices of `S`, the components of the induced graph are the
vertices of `S`. -/
private theorem card_induce_of_not_adj {S : Set V} (hS : ∀ x ∈ S, ∀ y ∈ S, ¬ G.Adj x y) :
    Nat.card (G.induce S).ConnectedComponent = Nat.card S := by
  refine (Nat.card_congr (Equiv.ofBijective (G.induce S).connectedComponentMk
    ⟨fun x y hxy => ?_, fun c => ?_⟩)).symm
  · obtain ⟨p⟩ := ConnectedComponent.exact hxy
    cases p with
    | nil => rfl
    | cons hadj _ => exact (hS _ (Subtype.prop _) _ (Subtype.prop _) hadj).elim
  · induction c using ConnectedComponent.ind with
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

/-- The first clause of height separation from a level function on the uniform members. -/
private theorem sep₁_of {a r g : ℝ} {n : ℕ} (c : ℕ → ℝ)
    (hc : ∀ k : ℕ, k < n → ∀ v, h v ∈ uniformInterval a r g k → h v = c k) :
    ∀ k v w, h v ∈ uniformCover a r g n k → h w ∈ uniformCover a r g n k → h v = h w :=
  fun k v w hv hw => (hc k k.2 v hv).trans (hc k k.2 w hw).symm

/-- The second clause of height separation from vertex-free overlaps. -/
private theorem sep₂_of {a r g : ℝ} {n : ℕ} (hgr : g ≤ r)
    (hl : ∀ l : ℕ, 1 ≤ l → l < n → ∀ v,
      h v ∉ ioo (a + (l : ℝ) * (r - g)) (a + (l : ℝ) * (r - g) + g)) :
    ∀ k l : Fin n, (k : ℕ) + 1 = l → ∀ v, h v ∉ uniformCover a r g n k ⊓ uniformCover a r g n l :=
  fun k l hkl v hv => hl l (by omega) l.2 v (by rwa [uniformCover_inf_of_succ hgr hkl] at hv)

end helpers

/-- The three-member uniform family `(-1/8, 7/8)`, `(1/2, 3/2)`, `(9/8, 17/8)`. -/
local notation "U₃" => uniformCover (-1 / 8 : ℝ) 1 (3 / 8) 3

/-- The three-member family as real sets. -/
local notation "F₃" => fun k : Fin 3 => ((U₃ k : OpenInterval) : Set ℝ)

/-! ## F1. The 4-cycle with three members -/

section Cycle

private theorem h4_cases (v : Fin 4) : h4 v = 0 ∨ h4 v = 1 ∨ h4 v = 2 := by
  fin_cases v <;> norm_num [h4]

private theorem h4_nonneg (v : Fin 4) : 0 ≤ h4 v := by
  rcases h4_cases v with h | h | h <;> rw [h] <;> norm_num

private theorem h4_le_two (v : Fin 4) : h4 v ≤ 2 := by
  rcases h4_cases v with h | h | h <;> rw [h] <;> norm_num

/-- **Attained range** of the 4-cycle height, through `range_plHeight_eq_Icc`. -/
theorem c4_range : Set.range (plHeight C4 h4) = Set.Icc 0 2 := by
  have := range_plHeight_eq_Icc (G := C4) (h := h4) cycleGraph_connected (lo := 0) (hi := 2)
    h4_nonneg h4_le_two
  rwa [h4_zero, h4_two] at this

/-- The three-member family is height-separating for the 4-cycle. -/
theorem c4_heightSeparating : HeightSeparating h4 U₃ := by
  refine ⟨sep₁_of (fun k => k) fun k hk v hv => ?_, sep₂_of (by norm_num) fun l h1 h2 v hv => ?_⟩
  · rw [mem_uniformInterval] at hv
    obtain rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    all_goals rcases h4_cases v with h | h | h <;> rw [h] at hv ⊢ <;>
      first | (norm_num at hv; done) | norm_num
  · rw [mem_ioo] at hv
    obtain rfl | rfl : l = 1 ∨ l = 2 := by omega
    all_goals rcases h4_cases v with h | h | h <;> rw [h] at hv <;> norm_num at hv

private theorem h4_mem_U₃_zero : h4 0 ∈ U₃ 0 := by
  norm_num [uniformCover_apply, mem_uniformInterval]

private theorem h4_mem_U₃_one : h4 1 ∈ U₃ 1 := by
  norm_num [uniformCover_apply, mem_uniformInterval]

private theorem h4_mem_U₃_two : h4 2 ∈ U₃ 2 := by
  norm_num [uniformCover_apply, mem_uniformInterval]

/-- The level of height `1` consists of the non-adjacent vertices `1` and `3`. -/
private theorem c4_level_one_card :
    Nat.card (C4.induce {v | h4 v = h4 1}).ConnectedComponent = 2 := by
  have hlev : ∀ v : Fin 4, h4 v = h4 1 ↔ v = 1 ∨ v = 3 := by
    intro v
    fin_cases v <;> norm_num [h4] <;> decide
  rw [card_induce_of_not_adj fun x hx y hy hxy => ?_]
  · exact card_two_of (P := fun v => h4 v = h4 1) (a := 1) (b := 3) (by decide) rfl
      (h4_three.trans h4_one.symm) fun x hx => (hlev x).1 hx
  · rcases (hlev x).1 hx with rfl | rfl <;> rcases (hlev y).1 hy with rfl | rfl <;>
      revert hxy <;> decide

/-- **Vertex cells over `{0}`**, through the level branch: one level component, no crossing edge. -/
theorem c4_vertexCells_zero :
    Nat.card {c : multiNerveMapper (plHeight C4 h4) F₃ // c.support.image Sigma.fst = {0}} = 1 :=
  card_eq_add_of_equiv
    (uniformVertexCellsEquivLevel C4 h4 c4_heightSeparating 0 0 h4_mem_U₃_zero)
    (card_induce_singleton (v₀ := 0) rfl fun v hv => by
      have hv' : h4 v = 0 := hv
      fin_cases v <;> first | rfl | (norm_num [h4] at hv'))
    (card_zero_of (not_edgeCrosses_of_le h4_nonneg))

/-- **Vertex cells over `{1}`**, through the level branch: the vertices `1` and `3` are not
adjacent, and no edge crosses height `1`. -/
theorem c4_vertexCells_one :
    Nat.card {c : multiNerveMapper (plHeight C4 h4) F₃ // c.support.image Sigma.fst = {1}} = 2 :=
  card_eq_add_of_equiv
    (uniformVertexCellsEquivLevel C4 h4 c4_heightSeparating 1 1 h4_mem_U₃_one)
    c4_level_one_card
    (card_zero_of fun e => by
      obtain ⟨d, rfl⟩ := exists_dartEdge_eq e
      obtain ⟨w, hw, hw13⟩ := C4_edge_endpoint d
      refine not_edgeCrosses_dartEdge_of_eq ?_
      rcases mem_dartEdge.1 hw with rfl | rfl
      · exact .inl (by rcases hw13 with h | h <;> simp [h])
      · exact .inr (by rcases hw13 with h | h <;> simp [h]))

/-- **Vertex cells over `{2}`**, through the level branch. -/
theorem c4_vertexCells_two :
    Nat.card {c : multiNerveMapper (plHeight C4 h4) F₃ // c.support.image Sigma.fst = {2}} = 1 :=
  card_eq_add_of_equiv
    (uniformVertexCellsEquivLevel C4 h4 c4_heightSeparating 2 2 h4_mem_U₃_two)
    (card_induce_singleton (v₀ := 2) rfl fun v hv => by
      have hv' : h4 v = 2 := hv
      fin_cases v <;> first | rfl | (norm_num [h4] at hv'))
    (card_zero_of (not_edgeCrosses_of_ge h4_le_two))

/-- The vertex-cell counts agree with the merged preimage counts `threeMember_card_*`. -/
theorem c4_vertexCells_eq_preimage :
    Nat.card {c : multiNerveMapper (plHeight C4 h4) F₃ // c.support.image Sigma.fst = {0}} =
        Nat.card (ZerothHomotopy {x : Realization C4 // plHeight C4 h4 x ∈ U₃ 0}) ∧
      Nat.card {c : multiNerveMapper (plHeight C4 h4) F₃ // c.support.image Sigma.fst = {1}} =
        Nat.card (ZerothHomotopy {x : Realization C4 // plHeight C4 h4 x ∈ U₃ 1}) ∧
      Nat.card {c : multiNerveMapper (plHeight C4 h4) F₃ // c.support.image Sigma.fst = {2}} =
        Nat.card (ZerothHomotopy {x : Realization C4 // plHeight C4 h4 x ∈ U₃ 2}) := by
  rw [c4_vertexCells_zero, c4_vertexCells_one, c4_vertexCells_two,
    UniformCoverExamples.threeMember_card_zero, UniformCoverExamples.threeMember_card_one,
    UniformCoverExamples.threeMember_card_two]
  exact ⟨rfl, rfl, rfl⟩

private theorem c4_edges_ne_low : dartEdge d01 ≠ dartEdge d03 :=
  dartEdge_ne (by decide) (by decide)

private theorem c4_edges_ne_high : dartEdge d12 ≠ dartEdge d23 :=
  dartEdge_ne (by decide) (by decide)

/-- **Edge cells over `{0, 1}`**, through the spanning branch: the overlap `(1/2, 7/8)` is spanned
by `0 — 1` and `0 — 3`. -/
theorem c4_edgeCells01 :
    Nat.card {c : multiNerveMapper (plHeight C4 h4) F₃ // c.support.image Sigma.fst = {0, 1}} =
      2 := by
  rw [Nat.card_congr (uniformEdgeCellsEquivSpans C4 h4 c4_heightSeparating (by norm_num)
    (by norm_num) (k := 0) (l := 1) rfl)]
  refine card_two_of c4_edges_ne_low ?_ ?_ fun e he => ?_
  · rw [edgeSpans_dartEdge_iff]
    norm_num [d01]
  · rw [edgeSpans_dartEdge_iff]
    norm_num [d03]
  · rcases c4_edge_cases e with rfl | rfl | rfl | rfl
    · exact .inl rfl
    · rw [edgeSpans_dartEdge_iff] at he
      norm_num [d12] at he
    · rw [edgeSpans_dartEdge_iff] at he
      norm_num [d23] at he
    · exact .inr rfl

/-- **Edge cells over `{1, 2}`**, through the spanning branch: the overlap `(9/8, 3/2)` is spanned
by `1 — 2` and `2 — 3`. -/
theorem c4_edgeCells12 :
    Nat.card {c : multiNerveMapper (plHeight C4 h4) F₃ // c.support.image Sigma.fst = {1, 2}} =
      2 := by
  rw [Nat.card_congr (uniformEdgeCellsEquivSpans C4 h4 c4_heightSeparating (by norm_num)
    (by norm_num) (k := 1) (l := 2) rfl)]
  refine card_two_of c4_edges_ne_high ?_ ?_ fun e he => ?_
  · rw [edgeSpans_dartEdge_iff]
    norm_num [d12]
  · rw [edgeSpans_dartEdge_iff]
    norm_num [d23]
  · rcases c4_edge_cases e with rfl | rfl | rfl | rfl
    · rw [edgeSpans_dartEdge_iff] at he
      norm_num [d01] at he
    · exact .inl rfl
    · exact .inr rfl
    · rw [edgeSpans_dartEdge_iff] at he
      norm_num [d03] at he

/-- **F1.** The 4-cycle under the three-member family: attained range `[0, 2]`, height separation,
vertex cells `1, 2, 1` over the labels and two edge cells over each consecutive pair. -/
theorem c4_threeMember :
    Set.range (plHeight C4 h4) = Set.Icc 0 2 ∧ HeightSeparating h4 U₃ ∧
      Nat.card {c : multiNerveMapper (plHeight C4 h4) F₃ // c.support.image Sigma.fst = {0}} = 1 ∧
      Nat.card {c : multiNerveMapper (plHeight C4 h4) F₃ // c.support.image Sigma.fst = {1}} = 2 ∧
      Nat.card {c : multiNerveMapper (plHeight C4 h4) F₃ // c.support.image Sigma.fst = {2}} = 1 ∧
      Nat.card {c : multiNerveMapper (plHeight C4 h4) F₃ //
        c.support.image Sigma.fst = {0, 1}} = 2 ∧
      Nat.card {c : multiNerveMapper (plHeight C4 h4) F₃ //
        c.support.image Sigma.fst = {1, 2}} = 2 :=
  ⟨c4_range, c4_heightSeparating, c4_vertexCells_zero, c4_vertexCells_one, c4_vertexCells_two,
    c4_edgeCells01, c4_edgeCells12⟩

end Cycle

/-! ## F2. The single edge under the same cover -/

section SingleEdge

private theorem edgeGraph_edge (e : edgeGraph.edgeSet) : e = dartEdge d₀ := by
  obtain ⟨d, rfl⟩ := exists_dartEdge_eq e
  rcases edgeGraph_dart d with rfl | rfl
  · rfl
  · exact dartEdge_symm d₀

private theorem h02_cases (v : Bool) : h02 v = 0 ∨ h02 v = 2 := by
  cases v
  · exact .inl rfl
  · exact .inr rfl

private theorem h02_nonneg (v : Bool) : 0 ≤ h02 v := by
  rcases h02_cases v with h | h <;> norm_num [h]

private theorem h02_le_two (v : Bool) : h02 v ≤ 2 := by
  rcases h02_cases v with h | h <;> norm_num [h]

/-- The three-member family is height-separating for the single edge. -/
theorem edge_heightSeparating : HeightSeparating h02 U₃ := by
  refine ⟨sep₁_of (fun k => k) fun k hk v hv => ?_, sep₂_of (by norm_num) fun l h1 h2 v hv => ?_⟩
  · rw [mem_uniformInterval] at hv
    obtain rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    all_goals rcases h02_cases v with h | h <;> rw [h] at hv ⊢ <;>
      first | (norm_num at hv; done) | norm_num
  · rw [mem_ioo] at hv
    obtain rfl | rfl : l = 1 ∨ l = 2 := by omega
    all_goals rcases h02_cases v with h | h <;> rw [h] at hv <;> norm_num at hv

/-- The middle member `(1/2, 3/2)` contains no vertex height. -/
theorem edge_not_mem_one (v : Bool) : h02 v ∉ U₃ 1 := fun hv => by
  rw [uniformCover_apply, mem_uniformInterval] at hv
  rcases h02_cases v with h | h <;> rw [h] at hv <;> norm_num at hv

/-- **Vertex cells over `{1}`**, through the without-a-level branch: the edge spans `[1/2, 3/2]`. -/
theorem edge_vertexCells_one :
    Nat.card {c : multiNerveMapper (plHeight edgeGraph h02) F₃ //
      c.support.image Sigma.fst = {1}} = 1 := by
  rw [Nat.card_congr (uniformVertexCellsEquivSpans edgeGraph h02 1 edge_not_mem_one
    (by norm_num))]
  refine card_one_of (a := dartEdge d₀) ?_ fun e _ => edgeGraph_edge e
  rw [edgeSpans_dartEdge_iff]
  norm_num [d₀, h02]

/-- **Vertex cells over `{0}`**, through the level branch. -/
theorem edge_vertexCells_zero :
    Nat.card {c : multiNerveMapper (plHeight edgeGraph h02) F₃ //
      c.support.image Sigma.fst = {0}} = 1 :=
  card_eq_add_of_equiv
    (uniformVertexCellsEquivLevel edgeGraph h02 edge_heightSeparating 0 false
      (by norm_num [h02, uniformCover_apply, mem_uniformInterval]))
    (card_induce_singleton (v₀ := false) rfl fun v hv => by
      cases v
      · rfl
      · norm_num [h02] at hv)
    (card_zero_of (not_edgeCrosses_of_le h02_nonneg))

/-- **Vertex cells over `{2}`**, through the level branch. -/
theorem edge_vertexCells_two :
    Nat.card {c : multiNerveMapper (plHeight edgeGraph h02) F₃ //
      c.support.image Sigma.fst = {2}} = 1 :=
  card_eq_add_of_equiv
    (uniformVertexCellsEquivLevel edgeGraph h02 edge_heightSeparating 2 true
      (by norm_num [h02, uniformCover_apply, mem_uniformInterval]))
    (card_induce_singleton (v₀ := true) rfl fun v hv => by
      cases v
      · norm_num [h02] at hv
      · rfl)
    (card_zero_of (not_edgeCrosses_of_ge h02_le_two))

/-- **F2.** The single edge under the three-member family: height separation and one vertex cell
over each label, the middle one through the spanning edge. -/
theorem edge_threeMember :
    HeightSeparating h02 U₃ ∧
      Nat.card {c : multiNerveMapper (plHeight edgeGraph h02) F₃ //
        c.support.image Sigma.fst = {0}} = 1 ∧
      Nat.card {c : multiNerveMapper (plHeight edgeGraph h02) F₃ //
        c.support.image Sigma.fst = {1}} = 1 ∧
      Nat.card {c : multiNerveMapper (plHeight edgeGraph h02) F₃ //
        c.support.image Sigma.fst = {2}} = 1 :=
  ⟨edge_heightSeparating, edge_vertexCells_zero, edge_vertexCells_one, edge_vertexCells_two⟩

end SingleEdge

/-! ## F3. A subdivided Y-tree -/

section YTree

/-- The tree with edges `0 — 2`, `1 — 2` and `2 — 3`. -/
def Y : SimpleGraph (Fin 4) := SimpleGraph.fromEdgeSet {s(0, 2), s(1, 2), s(2, 3)}

/-- Heights `0, 1, 2, 3`. -/
def hY : Fin 4 → ℝ := ![0, 1, 2, 3]

/-- The cover `uniformCover (-1/2) (5/4) (1/4) 4`, with members `(k - 1/2, k + 3/4)`. -/
local notation "U₄" => uniformCover (-1 / 2 : ℝ) (5 / 4) (1 / 4) 4

/-- The four-member family as real sets. -/
local notation "F₄" => fun k : Fin 4 => ((U₄ k : OpenInterval) : Set ℝ)

theorem Y_adj (a b : Fin 4) :
    Y.Adj a b ↔ (a = 0 ∧ b = 2) ∨ (a = 2 ∧ b = 0) ∨ (a = 1 ∧ b = 2) ∨ (a = 2 ∧ b = 1) ∨
      (a = 2 ∧ b = 3) ∨ (a = 3 ∧ b = 2) := by
  fin_cases a <;> fin_cases b <;> simp [Y, fromEdgeSet_adj]

/-- The dart `0 → 2`. -/
def y02 : Y.Dart := ⟨(0, 2), (Y_adj 0 2).2 (by decide)⟩

/-- The dart `1 → 2`. -/
def y12 : Y.Dart := ⟨(1, 2), (Y_adj 1 2).2 (by decide)⟩

/-- The dart `2 → 3`. -/
def y23 : Y.Dart := ⟨(2, 3), (Y_adj 2 3).2 (by decide)⟩

/-- The three edges of the tree. -/
theorem Y_edge_cases (e : Y.edgeSet) : e = dartEdge y02 ∨ e = dartEdge y12 ∨ e = dartEdge y23 := by
  obtain ⟨⟨⟨a, b⟩, hab⟩, rfl⟩ := exists_dartEdge_eq e
  rcases (Y_adj a b).1 hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩
  · exact .inl rfl
  · exact .inl (Subtype.ext Sym2.eq_swap)
  · exact .inr (.inl rfl)
  · exact .inr (.inl (Subtype.ext Sym2.eq_swap))
  · exact .inr (.inr rfl)
  · exact .inr (.inr (Subtype.ext Sym2.eq_swap))

theorem Y_connected : Y.Connected := by
  have hr : ∀ u : Fin 4, Y.Reachable u 2 := by
    intro u
    fin_cases u
    · exact ((Y_adj 0 2).2 (by decide)).reachable
    · exact ((Y_adj 1 2).2 (by decide)).reachable
    · exact Reachable.refl _
    · exact ((Y_adj 3 2).2 (by decide)).reachable
  exact ⟨fun u v => (hr u).trans (hr v).symm⟩

@[simp] private theorem hY_zero : hY 0 = 0 := rfl

@[simp] private theorem hY_one : hY 1 = 1 := rfl

@[simp] private theorem hY_two : hY 2 = 2 := rfl

@[simp] private theorem hY_three : hY 3 = 3 := rfl

private theorem hY_cases (v : Fin 4) : hY v = 0 ∨ hY v = 1 ∨ hY v = 2 ∨ hY v = 3 := by
  fin_cases v <;> norm_num [hY]

private theorem hY_nonneg (v : Fin 4) : 0 ≤ hY v := by
  rcases hY_cases v with h | h | h | h <;> rw [h] <;> norm_num

private theorem hY_le_three (v : Fin 4) : hY v ≤ 3 := by
  rcases hY_cases v with h | h | h | h <;> rw [h] <;> norm_num

private theorem hY_injective {v w : Fin 4} (h : hY v = hY w) : v = w := by
  fin_cases v <;> fin_cases w <;> first | rfl | (norm_num [hY] at h)

/-- **Attained range** of the tree height. -/
theorem Y_range : Set.range (plHeight Y hY) = Set.Icc 0 3 := by
  have := range_plHeight_eq_Icc (G := Y) (h := hY) Y_connected (lo := 0) (hi := 3)
    hY_nonneg hY_le_three
  rwa [hY_zero, hY_three] at this

/-- The four-member family is height-separating for the tree. -/
theorem Y_heightSeparating : HeightSeparating hY U₄ := by
  refine ⟨sep₁_of (fun k => k) fun k hk v hv => ?_, sep₂_of (by norm_num) fun l h1 h2 v hv => ?_⟩
  · rw [mem_uniformInterval] at hv
    obtain rfl | rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
    all_goals rcases hY_cases v with h | h | h | h <;> rw [h] at hv ⊢ <;>
      first | (norm_num at hv; done) | norm_num
  · rw [mem_ioo] at hv
    obtain rfl | rfl | rfl : l = 1 ∨ l = 2 ∨ l = 3 := by omega
    all_goals rcases hY_cases v with h | h | h | h <;> rw [h] at hv <;> norm_num at hv

/-- The level sets of the tree are single vertices. -/
private theorem Y_level_card (k : Fin 4) :
    Nat.card (Y.induce {v | hY v = hY k}).ConnectedComponent = 1 :=
  card_induce_singleton (v₀ := k) rfl fun _ hv => hY_injective hv

private theorem Y_mem (k : Fin 4) : hY k ∈ U₄ k := by
  rw [uniformCover_apply, mem_uniformInterval]
  fin_cases k <;> norm_num [hY]

/-- **Vertex cells over `{1}`**: the level component `{1}` and the crossing edge `0 — 2`. -/
theorem Y_vertexCells_one :
    Nat.card {c : multiNerveMapper (plHeight Y hY) F₄ // c.support.image Sigma.fst = {1}} = 2 :=
  card_eq_add_of_equiv (uniformVertexCellsEquivLevel Y hY Y_heightSeparating 1 1 (Y_mem 1))
    (Y_level_card 1)
    (card_one_of (a := dartEdge y02)
      (by rw [edgeCrosses_dartEdge_iff]; norm_num [y02])
      fun e he => by
        rcases Y_edge_cases e with rfl | rfl | rfl
        · rfl
        · exact absurd he (not_edgeCrosses_dartEdge_of_eq (.inl rfl))
        · rw [edgeCrosses_dartEdge_iff] at he
          norm_num [y23] at he)

/-- The only crossing edge of the tree is `0 — 2`, at height `1`. -/
theorem Y_edgeCrosses_one : EdgeCrosses Y hY 1 (dartEdge y02) := by
  rw [edgeCrosses_dartEdge_iff]
  norm_num [y02]

/-- **Vertex cells over `{0}`, `{2}` and `{3}`**: one level component each, no crossing edge. -/
theorem Y_vertexCells_other :
    Nat.card {c : multiNerveMapper (plHeight Y hY) F₄ // c.support.image Sigma.fst = {0}} = 1 ∧
      Nat.card {c : multiNerveMapper (plHeight Y hY) F₄ // c.support.image Sigma.fst = {2}} = 1 ∧
      Nat.card {c : multiNerveMapper (plHeight Y hY) F₄ //
        c.support.image Sigma.fst = {3}} = 1 := by
  refine ⟨card_eq_add_of_equiv (uniformVertexCellsEquivLevel Y hY Y_heightSeparating 0 0 (Y_mem 0))
      (Y_level_card 0) (card_zero_of (not_edgeCrosses_of_le hY_nonneg)),
    card_eq_add_of_equiv (uniformVertexCellsEquivLevel Y hY Y_heightSeparating 2 2 (Y_mem 2))
      (Y_level_card 2) (card_zero_of fun e => ?_),
    card_eq_add_of_equiv (uniformVertexCellsEquivLevel Y hY Y_heightSeparating 3 3 (Y_mem 3))
      (Y_level_card 3) (card_zero_of (not_edgeCrosses_of_ge fun v => by
        rw [hY_three]; exact hY_le_three v))⟩
  rcases Y_edge_cases e with rfl | rfl | rfl
  · exact not_edgeCrosses_dartEdge_of_eq (.inr rfl)
  · exact not_edgeCrosses_dartEdge_of_eq (.inr rfl)
  · exact not_edgeCrosses_dartEdge_of_eq (.inl rfl)

private theorem Y_edges_ne : dartEdge y02 ≠ dartEdge y12 :=
  dartEdge_ne (by decide) (by decide)

/-- **Edge cells over the consecutive pairs** number `1, 2, 1`, spanned by `0 — 2`, by
`0 — 2, 1 — 2` and by `2 — 3`. -/
theorem Y_edgeCells :
    Nat.card {c : multiNerveMapper (plHeight Y hY) F₄ //
        c.support.image Sigma.fst = {0, 1}} = 1 ∧
      Nat.card {c : multiNerveMapper (plHeight Y hY) F₄ //
        c.support.image Sigma.fst = {1, 2}} = 2 ∧
      Nat.card {c : multiNerveMapper (plHeight Y hY) F₄ //
        c.support.image Sigma.fst = {2, 3}} = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Nat.card_congr (uniformEdgeCellsEquivSpans Y hY Y_heightSeparating (by norm_num)
      (by norm_num) (k := 0) (l := 1) rfl)]
    refine card_one_of (a := dartEdge y02) ?_ fun e he => ?_
    · rw [edgeSpans_dartEdge_iff]
      norm_num [y02]
    · rcases Y_edge_cases e with rfl | rfl | rfl
      · rfl
      · rw [edgeSpans_dartEdge_iff] at he
        norm_num [y12] at he
      · rw [edgeSpans_dartEdge_iff] at he
        norm_num [y23] at he
  · rw [Nat.card_congr (uniformEdgeCellsEquivSpans Y hY Y_heightSeparating (by norm_num)
      (by norm_num) (k := 1) (l := 2) rfl)]
    refine card_two_of Y_edges_ne ?_ ?_ fun e he => ?_
    · rw [edgeSpans_dartEdge_iff]
      norm_num [y02]
    · rw [edgeSpans_dartEdge_iff]
      norm_num [y12]
    · rcases Y_edge_cases e with rfl | rfl | rfl
      · exact .inl rfl
      · exact .inr rfl
      · rw [edgeSpans_dartEdge_iff] at he
        norm_num [y23] at he
  · rw [Nat.card_congr (uniformEdgeCellsEquivSpans Y hY Y_heightSeparating (by norm_num)
      (by norm_num) (k := 2) (l := 3) rfl)]
    refine card_one_of (a := dartEdge y23) ?_ fun e he => ?_
    · rw [edgeSpans_dartEdge_iff]
      norm_num [y23]
    · rcases Y_edge_cases e with rfl | rfl | rfl
      · rw [edgeSpans_dartEdge_iff] at he
        norm_num [y02] at he
      · rw [edgeSpans_dartEdge_iff] at he
        norm_num [y12] at he
      · rfl

/-- **F3.** The subdivided Y-tree: attained range `[0, 3]`, height separation, vertex cells
`1, 2, 1, 1` with the crossing edge over `{1}`, and edge cells `1, 2, 1`. -/
theorem Y_fourMember :
    Set.range (plHeight Y hY) = Set.Icc 0 3 ∧ HeightSeparating hY U₄ ∧
      Nat.card {c : multiNerveMapper (plHeight Y hY) F₄ // c.support.image Sigma.fst = {1}} = 2 ∧
      Nat.card {c : multiNerveMapper (plHeight Y hY) F₄ // c.support.image Sigma.fst = {0}} = 1 ∧
      Nat.card {c : multiNerveMapper (plHeight Y hY) F₄ // c.support.image Sigma.fst = {2}} = 1 ∧
      Nat.card {c : multiNerveMapper (plHeight Y hY) F₄ // c.support.image Sigma.fst = {3}} = 1 ∧
      Nat.card {c : multiNerveMapper (plHeight Y hY) F₄ //
        c.support.image Sigma.fst = {0, 1}} = 1 ∧
      Nat.card {c : multiNerveMapper (plHeight Y hY) F₄ //
        c.support.image Sigma.fst = {1, 2}} = 2 ∧
      Nat.card {c : multiNerveMapper (plHeight Y hY) F₄ //
        c.support.image Sigma.fst = {2, 3}} = 1 :=
  ⟨Y_range, Y_heightSeparating, Y_vertexCells_one, Y_vertexCells_other.1, Y_vertexCells_other.2.1,
    Y_vertexCells_other.2.2, Y_edgeCells.1, Y_edgeCells.2.1, Y_edgeCells.2.2⟩

end YTree

/-! ## F4. One member -/

section OneMember

private theorem edge_mem_J4 (v : Bool) : h02 v ∈ J4 := by
  cases v <;> norm_num [h02, mem_ioo]

/-- **F4.** The single member `(-1/2, 5/2)` contains both heights `0` and `2` of the single edge, so
the family is not height-separating; the splitting still gives one vertex cell: one induced
component and no uncovered edge. -/
theorem oneMember_edge (g : ℝ) :
    ¬ HeightSeparating h02 (uniformCover (-1 / 2) 3 g 1) ∧
      Nat.card {c : multiNerveMapper (plHeight edgeGraph h02)
          (fun k => (uniformCover (-1 / 2) 3 g 1 k : Set ℝ)) //
        c.support.image Sigma.fst = {0}} = 1 := by
  have hmem : ∀ v, h02 v ∈ uniformCover (-1 / 2) 3 g 1 0 := fun v => by
    rw [oneMember_eq_J4]
    exact edge_mem_J4 v
  refine ⟨fun hs => ?_, ?_⟩
  · have := hs.1 0 false true (hmem false) (hmem true)
    norm_num [h02] at this
  · have hunc : IsEmpty (UncoveredEdge edgeGraph h02 (uniformCover (-1 / 2) 3 g 1 0)) :=
      ⟨fun e => by
        have he := edgeGraph_edge e.1
        exact e.2.2 false (he ▸ fst_mem_dartEdge d₀) (hmem false)⟩
    exact card_eq_add_of_equiv
      ((vertexCellsCellGraphEquiv edgeGraph h02 (uniformCover (-1 / 2) 3 g 1) 0).trans
        (cellComponentsEquivSum edgeGraph h02 _))
      (card_induce_complete (v₀ := false) (hmem false) fun x _ y _ hxy => hxy)
      Nat.card_of_isEmpty

end OneMember

/-! ## F5. A vertex height in an overlap -/

section Overlap

/-- The cover `uniformCover (-1/4) (3/2) (1/2) 3`, with members `(-1/4, 5/4)`, `(3/4, 9/4)` and
`(7/4, 13/4)`. -/
local notation "W₃" => uniformCover (-1 / 4 : ℝ) (3 / 2) (1 / 2) 3

/-- The overlap of the first two members is `(3/4, 5/4)`. -/
theorem overlap_inf : W₃ 0 ⊓ W₃ 1 = ioo (3 / 4) (5 / 4) := by
  rw [uniformCover_inf_of_succ (by norm_num) (k := 0) (l := 1) rfl]
  congr 1 <;> norm_num

/-- **F5.** The overlap `(3/4, 5/4)` contains the vertex height `1`, so the second clause of
`HeightSeparating` fails. There are two edge cells over `{0, 1}`, through `edgeCellsCellGraphEquiv`
and `cellComponentsEquivSum`: two induced components `{1}`, `{3}` and no uncovered edge. No edge
spans `[3/4, 5/4]`, so the spanning classification fails without its hypothesis. -/
theorem overlap_control :
    h4 1 ∈ W₃ 0 ⊓ W₃ 1 ∧
      ¬ (∀ k l : Fin 3, (k : ℕ) + 1 = l → ∀ v, h4 v ∉ W₃ k ⊓ W₃ l) ∧
      ¬ HeightSeparating h4 W₃ ∧
      Nat.card {c : multiNerveMapper (plHeight C4 h4) (fun k => (W₃ k : Set ℝ)) //
        c.support.image Sigma.fst = {0, 1}} = 2 ∧
      Nat.card {e // EdgeSpans C4 h4 (3 / 4) (5 / 4) e} = 0 ∧
      Nat.card {c : multiNerveMapper (plHeight C4 h4) (fun k => (W₃ k : Set ℝ)) //
        c.support.image Sigma.fst = {0, 1}} ≠
        Nat.card {e // EdgeSpans C4 h4 (3 / 4) (5 / 4) e} := by
  have hmem : h4 1 ∈ W₃ 0 ⊓ W₃ 1 := by
    rw [overlap_inf, mem_ioo]
    norm_num
  have hclause : ¬ (∀ k l : Fin 3, (k : ℕ) + 1 = l → ∀ v, h4 v ∉ W₃ k ⊓ W₃ l) :=
    fun h => h 0 1 rfl 1 hmem
  -- The vertices with height in the overlap are `1` and `3`.
  have hlev : ∀ v : Fin 4, h4 v ∈ ioo (3 / 4) (5 / 4) ↔ v = 1 ∨ v = 3 := by
    intro v
    rw [mem_ioo]
    fin_cases v <;> norm_num [h4] <;> decide
  have hcells : Nat.card {c : multiNerveMapper (plHeight C4 h4) (fun k => (W₃ k : Set ℝ)) //
      c.support.image Sigma.fst = {0, 1}} = 2 := by
    rw [Nat.card_congr ((edgeCellsCellGraphEquiv C4 h4 W₃ 0 1).trans
      (cellComponentsEquivSum C4 h4 _)), overlap_inf]
    have hunc : IsEmpty (UncoveredEdge C4 h4 (ioo (3 / 4) (5 / 4))) :=
      ⟨fun e => by
        obtain ⟨d, hd⟩ := exists_dartEdge_eq e.1
        obtain ⟨w, hw, hw13⟩ := C4_edge_endpoint d
        exact e.2.2 w (hd ▸ hw) ((hlev w).2 hw13)⟩
    rw [Nat.card_sum, Nat.card_of_isEmpty (α := UncoveredEdge C4 h4 _), add_zero,
      card_induce_of_not_adj fun x hx y hy hxy => ?_]
    · exact card_two_of (P := fun v => h4 v ∈ ioo (3 / 4) (5 / 4)) (by decide)
        ((hlev 1).2 (.inl rfl)) ((hlev 3).2 (.inr rfl)) fun x hx => (hlev x).1 hx
    · rcases (hlev x).1 hx with rfl | rfl <;> rcases (hlev y).1 hy with rfl | rfl <;>
        revert hxy <;> decide
  have hspans : Nat.card {e // EdgeSpans C4 h4 (3 / 4) (5 / 4) e} = 0 :=
    card_zero_of fun e he => by
      rcases c4_edge_cases e with rfl | rfl | rfl | rfl <;> rw [edgeSpans_dartEdge_iff] at he
      · norm_num [d01] at he
      · norm_num [d12] at he
      · norm_num [d23] at he
      · norm_num [d03] at he
  exact ⟨hmem, hclause, fun hs => hclause hs.2, hcells, hspans, by rw [hcells, hspans]; decide⟩

end Overlap

/-! ## F6. A disconnected graph -/

section Disconnected

/-- Heights `0` and `2` on two isolated vertices. -/
def hb : Fin 2 → ℝ := ![0, 2]

/-- **F6.** On two isolated vertices of heights `0` and `2` the height `1` is not attained, so the
attained range is not `[0, 2]` although `0` and `2` are the extreme heights: connectedness cannot be
dropped from `range_plHeight_eq_Icc`. Every point is a vertex, since `⊥` has no darts. -/
theorem disconnected_range :
    (∀ v, hb 0 ≤ hb v) ∧ (∀ v, hb v ≤ hb 1) ∧
      (1 : ℝ) ∉ Set.range (plHeight (⊥ : SimpleGraph (Fin 2)) hb) ∧
      Set.range (plHeight (⊥ : SimpleGraph (Fin 2)) hb) ≠ Set.Icc (hb 0) (hb 1) ∧
      ¬ (⊥ : SimpleGraph (Fin 2)).Connected := by
  have hlo : ∀ v, hb 0 ≤ hb v := fun v => by fin_cases v <;> norm_num [hb]
  have hhi : ∀ v, hb v ≤ hb 1 := fun v => by fin_cases v <;> norm_num [hb]
  have hnot : (1 : ℝ) ∉ Set.range (plHeight (⊥ : SimpleGraph (Fin 2)) hb) := by
    rintro ⟨p, hp⟩
    induction p using ind (⊥ : SimpleGraph (Fin 2)) with
    | vertex v =>
      rw [plHeight_vertex] at hp
      fin_cases v <;> norm_num [hb] at hp
    | edgePoint d t => exact d.adj.elim
  have hne : Set.range (plHeight (⊥ : SimpleGraph (Fin 2)) hb) ≠ Set.Icc (hb 0) (hb 1) :=
    fun heq => hnot (heq ▸ ⟨by norm_num [hb], by norm_num [hb]⟩)
  exact ⟨hlo, hhi, hnot, hne, fun hc => hne (range_plHeight_eq_Icc hc hlo hhi)⟩

end Disconnected

/-! ## Boundary cases of crossing and spanning -/

/-- **Boundary.** An edge whose endpoint heights are exactly `p = 0` and `q = 2` spans `[0, 2]` and
is the one active edge over `(0, 2)`, through `activeEdgeEquivSpans`, while crossing is strict: the
edge crosses neither `0` nor `2`, and it crosses `1`. -/
theorem edge_boundary :
    EdgeSpans edgeGraph h02 0 2 (dartEdge d₀) ∧
      Nat.card {e // EdgeActive edgeGraph h02 (ioo 0 2) e} = 1 ∧
      ¬ EdgeCrosses edgeGraph h02 0 (dartEdge d₀) ∧ ¬ EdgeCrosses edgeGraph h02 2 (dartEdge d₀) ∧
      EdgeCrosses edgeGraph h02 1 (dartEdge d₀) := by
  have hspans : EdgeSpans edgeGraph h02 0 2 (dartEdge d₀) := by
    rw [edgeSpans_dartEdge_iff]
    norm_num [d₀, h02]
  refine ⟨hspans, ?_, not_edgeCrosses_dartEdge_of_eq (.inl rfl),
    not_edgeCrosses_dartEdge_of_eq (.inr rfl), ?_⟩
  · rw [Nat.card_congr (activeEdgeEquivSpans (G := edgeGraph) (h := h02) (by norm_num)
      fun v hv => by rw [mem_ioo] at hv; rcases h02_cases v with h | h <;> rw [h] at hv <;>
        norm_num at hv)]
    exact card_one_of hspans fun e _ => edgeGraph_edge e
  · rw [edgeCrosses_dartEdge_iff]
    norm_num [d₀, h02]

/-! ## Far labels need `2g ≤ r` -/

/-- **Far labels.** For the single edge, `uniformCover (-1/4) (3/2) 1 3` with members `(-1/4, 5/4)`,
`(1/4, 7/4)`, `(3/4, 9/4)` is height-separating, but `2g > r` and the labels `0` and `2` meet in
`(3/4, 5/4)`, which carries one edge cell: height separation alone does not give the emptiness of
far edge cells. -/
theorem edge_farLabels :
    HeightSeparating h02 (uniformCover (-1 / 4) (3 / 2) 1 3) ∧
      uniformCover (-1 / 4 : ℝ) (3 / 2) 1 3 0 ⊓ uniformCover (-1 / 4) (3 / 2) 1 3 2 =
        ioo (3 / 4) (5 / 4) ∧
      Nat.card {c : multiNerveMapper (plHeight edgeGraph h02)
          (fun k => (uniformCover (-1 / 4) (3 / 2) 1 3 k : Set ℝ)) //
        c.support.image Sigma.fst = {0, 2}} = 1 := by
  have hsep : HeightSeparating h02 (uniformCover (-1 / 4) (3 / 2) 1 3) := by
    refine ⟨sep₁_of (fun k => k) fun k hk v hv => ?_,
      sep₂_of (by norm_num) fun l h1 h2 v hv => ?_⟩
    · rw [mem_uniformInterval] at hv
      obtain rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 := by omega
      all_goals rcases h02_cases v with h | h <;> rw [h] at hv ⊢ <;>
        first | (norm_num at hv; done) | norm_num
    · rw [mem_ioo] at hv
      obtain rfl | rfl : l = 1 ∨ l = 2 := by omega
      all_goals rcases h02_cases v with h | h <;> rw [h] at hv <;> norm_num at hv
  have hK : uniformCover (-1 / 4 : ℝ) (3 / 2) 1 3 0 ⊓ uniformCover (-1 / 4) (3 / 2) 1 3 2 =
      ioo (3 / 4) (5 / 4) := by
    apply SetLike.coe_injective
    ext y
    simp only [coe_inf, uniformCover_apply, coe_uniformInterval, coe_ioo, Set.mem_inter_iff,
      Set.mem_Ioo]
    constructor
    · rintro ⟨⟨h₁, h₂⟩, h₃, h₄⟩
      norm_num at h₁ h₂ h₃ h₄
      exact ⟨by linarith, by linarith⟩
    · rintro ⟨h₁, h₂⟩
      norm_num
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith
  have hnot : ∀ v, h02 v ∉ ioo (3 / 4) (5 / 4) := fun v hv => by
    rw [mem_ioo] at hv
    rcases h02_cases v with h | h <;> rw [h] at hv <;> norm_num at hv
  refine ⟨hsep, hK, ?_⟩
  rw [Nat.card_congr
      (edgeCellsCellGraphEquiv edgeGraph h02 (uniformCover (-1 / 4) (3 / 2) 1 3) 0 2),
    hK, Nat.card_congr ((cellGraphComponentsEquivActiveEdges hnot).trans
      (activeEdgeEquivSpans (by norm_num) hnot))]
  refine card_one_of (a := dartEdge d₀) ?_ fun e _ => edgeGraph_edge e
  rw [edgeSpans_dartEdge_iff]
  norm_num [d₀, h02]

/-! ## F7. Existence -/

/-- **F7.** The existence theorem yields a height-separating uniform cover of the attained range of
the 4-cycle with `r < 1/2`. No counts are stated. -/
theorem c4_exists_heightSeparating :
    ∃ (a r g : ℝ) (n : ℕ), 0 < g ∧ 2 * g ≤ r ∧ r < 1 / 2 ∧ 0 < n ∧
      HeightSeparating h4 (uniformCover a r g n) ∧
      Covers (fun k => (uniformCover a r g n k : Set ℝ)) (Set.range (plHeight C4 h4)) := by
  obtain ⟨a, r, g, n, hg, hgr, hrρ, hn, -, -, -, hsep, hcov⟩ :=
    heightSeparating_covers_range h4 (m := 0) (M := 2) (ρ := 1 / 2) h4_mem_Icc (by norm_num)
  exact ⟨a, r, g, n, hg, hgr, hrρ, hn, hsep, hcov C4⟩

end

end TDA.Mapper.UniformCoverCellsExamples
