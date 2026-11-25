import TDA.Mapper.GraphPLReebData
import Mathlib.Data.List.Sort
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.List.FinRange
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Executable incidence extraction for graph-PL input

A `HeightGraph N` is a Boolean adjacency function on `Fin N` with rational vertex heights. This
module computes, without quotient representatives and without real-number comparison, the lists
from which the finite Reeb data of the graph-PL height are built:

* `levels`: the sorted distinct heights, and the single dummy level `0` when `N = 0`;
* `label`: the least vertex index in the component of a vertex in the graph induced on the
  vertices of its height, by `N` rounds of minimum-label propagation along horizontal edges;
* `cellList c`: the label fixed points of height `c`, one for each component of the level graph,
  and one cell for each edge crossing `c`, written as the ordered pair (lower endpoint, upper
  endpoint);
* `edgeList p q`: the edges whose height interval contains `[p, q]`, as ordered pairs, each with
  its two endpoint cells. An endpoint cell is the label of the endpoint when the endpoint lies on
  the level, and the edge itself as a crossing cell otherwise. Distinct edges are distinct
  entries, also when their endpoint cells coincide.

`incidence` collects the lists over all levels and gaps, and `incidence?` returns them for valid
input only: adjacency must be symmetric with an empty diagonal, and nothing is repaired.

## Semantic statements

For valid input, `graph` is the simple graph and `realHeight` the real-valued height.
`label_eq_label_iff_reachable` states that two vertices of height `c` have the same label exactly
when they are joined in the graph induced on `{v | realHeight v = c}`, the vertex set of
`LevelVertex` in `TDA.Mapper.GraphPLReebData`, and `componentEquiv` is the resulting bijection
between label fixed points and connected components. `criticalValues` is the list of levels as
a `CriticalValues`, and it covers the vertex heights (`coversVertexHeights`). The membership
statements `mem_cellList_inl`, `mem_cellList_inr` and `mem_edgeList` describe the lists, which
have no repetition (`nodup_cellList`, `nodup_edgeList`). Which vertex represents a component is a
property of this implementation; consumers should use the reachability statement.

The identification of these lists with `graphPLReebData` and with the Reeb quotient is in
`TDA.Mapper.GraphPLIncidenceReebData`.

## Cost

For `incidence` and `incidence?`, count one evaluation of `adj` or `height`, one rational
comparison and one index comparison as a unit. The label propagation makes `N` rounds, each
scanning `N` candidates for each of `N` vertices: `O(N³)` units. The levels take `O(N²)`. Each
level scans `N` vertices and `N²` ordered pairs, and each gap scans `N²` ordered pairs:
`O(L N²)` for `L` levels. The total is `O(N³)` units; the bit cost of rational comparison is
separate. `incidence` computes the label vector once. The forms `label`, `cellList`, `edgeList`,
`leftEnd` and `rightEnd` are for statements: each call recomputes the label vector. These counts
are not theorems. The executable definitions use lists, `Vector`, `Fin` and rational comparison;
the bound proofs of vector indexing are the only reason `#print axioms` lists `Classical.choice`
for them.

These are elementary library results, not attributed to a source. See `docs/math/mapper.md`.
-/

set_option autoImplicit false

namespace TDA.Mapper.GraphPL

open SimpleGraph TDA.Reeb

/-- Finite graph-PL input: Boolean adjacency on `Fin N` and rational vertex heights. -/
structure HeightGraph (N : ℕ) where
  /-- The adjacency function. -/
  adj : Fin N → Fin N → Bool
  /-- The vertex heights. -/
  height : Fin N → ℚ

namespace HeightGraph

/-- A cell over a level: a component representative, or a crossing edge as the ordered pair
(lower endpoint, upper endpoint). -/
abbrev Cell (N : ℕ) : Type := Fin N ⊕ Fin N × Fin N

/-- Executed incidence lists: the levels, the cells at each level, and over each gap between
consecutive levels the spanning edges with their left and right endpoint cells. -/
structure Incidence (N : ℕ) where
  /-- The levels, increasing. -/
  levels : List ℚ
  /-- The cells at each level. -/
  cells : List (List (Cell N))
  /-- The spanning edges over each gap, each with its left and right endpoint cells. -/
  edges : List (List ((Fin N × Fin N) × Cell N × Cell N))
  deriving DecidableEq, Repr

variable {N : ℕ} (X : HeightGraph N)

/-! ## Validation and semantic adapters -/

/-- The adjacency function is symmetric and has an empty diagonal. -/
def Valid : Prop := (∀ u w, X.adj u w = X.adj w u) ∧ ∀ u, X.adj u u = false

instance instDecidableValid : Decidable X.Valid := by unfold Valid; infer_instance

/-- The simple graph of a valid input. -/
def graph (hX : X.Valid) : SimpleGraph (Fin N) where
  Adj u w := X.adj u w = true
  symm := ⟨fun u w h => by rw [← hX.1 u w]; exact h⟩
  loopless := ⟨fun u h => by simp [hX.2 u] at h⟩

instance instDecidableRelGraphAdj (hX : X.Valid) : DecidableRel (X.graph hX).Adj := fun u w =>
  inferInstanceAs (Decidable (X.adj u w = true))

theorem graph_adj (hX : X.Valid) {u w : Fin N} : (X.graph hX).Adj u w ↔ X.adj u w = true :=
  Iff.rfl

/-- The vertex heights as real numbers. -/
noncomputable def realHeight : Fin N → ℝ := fun v => (X.height v : ℝ)

theorem realHeight_eq_iff {v : Fin N} {c : ℚ} : X.realHeight v = (c : ℝ) ↔ X.height v = c :=
  Rat.cast_inj

/-! ## Levels -/

/-- The sorted distinct heights; the dummy level `0` when there is no vertex. -/
def levels : List ℚ :=
  if N = 0 then [0] else ((List.ofFn X.height).dedup).insertionSort (· ≤ ·)

theorem levels_pairwise : X.levels.Pairwise (· < ·) := by
  unfold levels
  split
  · simp
  · have hs := List.pairwise_insertionSort (· ≤ ·) ((List.ofFn X.height).dedup)
    have hn : (((List.ofFn X.height).dedup).insertionSort (· ≤ ·)).Nodup :=
      (List.perm_insertionSort _ _).nodup_iff.2 (List.nodup_dedup _)
    exact (hs.and hn).imp fun h => lt_of_le_of_ne h.1 h.2

theorem mem_levels (hN : 0 < N) {c : ℚ} : c ∈ X.levels ↔ ∃ v, X.height v = c := by
  unfold levels
  simp only [hN.ne', ↓reduceIte, List.mem_insertionSort, List.mem_dedup, List.mem_ofFn]

theorem levels_ne_nil : X.levels ≠ [] := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · unfold levels
    simp only [hN, ↓reduceIte]
    exact List.cons_ne_nil _ _
  · exact List.ne_nil_of_mem ((X.mem_levels hN).2 ⟨⟨0, hN⟩, rfl⟩)

theorem levels_of_eq_zero (X : HeightGraph 0) : X.levels = [0] := rfl

/-- The number of gaps between consecutive levels. -/
def gapCount : ℕ := X.levels.length - 1

theorem length_levels : X.levels.length = X.gapCount + 1 :=
  (Nat.sub_add_cancel (List.length_pos_iff.2 X.levels_ne_nil)).symm

/-- The levels, indexed. -/
def level (i : Fin (X.gapCount + 1)) : ℚ := X.levels.get (i.cast X.length_levels.symm)

theorem level_strictMono : StrictMono X.level := fun _ _ hij =>
  List.pairwise_iff_get.1 X.levels_pairwise _ _ hij

theorem level_mem_levels (i : Fin (X.gapCount + 1)) : X.level i ∈ X.levels :=
  List.get_mem _ _

theorem exists_level_eq {c : ℚ} (hc : c ∈ X.levels) : ∃ i, X.level i = c := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.1 hc
  exact ⟨j.cast X.length_levels, hj⟩

theorem range_level (hN : 0 < N) : Set.range X.level = Set.range X.height := by
  ext c
  constructor
  · rintro ⟨i, rfl⟩
    exact (X.mem_levels hN).1 (X.level_mem_levels i)
  · rintro ⟨v, rfl⟩
    exact X.exists_level_eq ((X.mem_levels hN).2 ⟨v, rfl⟩)

/-- The computed covering list: the levels as real numbers. -/
noncomputable def criticalValues : CriticalValues X.gapCount where
  value i := (X.level i : ℝ)
  strictMono := fun _ _ hij => Rat.cast_lt.2 (X.level_strictMono hij)

@[simp] theorem criticalValues_value (i : Fin (X.gapCount + 1)) :
    X.criticalValues.value i = (X.level i : ℝ) := rfl

theorem coversVertexHeights : CoversVertexHeights X.criticalValues X.realHeight := fun v => by
  obtain ⟨i, hi⟩ := X.exists_level_eq ((X.mem_levels v.pos).2 ⟨v, rfl⟩)
  exact ⟨i, by rw [criticalValues_value, hi]; rfl⟩

/-! ## Component labels -/

/-- Adjacent vertices of equal height. -/
def horizontal (u w : Fin N) : Bool := X.adj u w && decide (X.height u = X.height w)

/-- One round of label propagation: every vertex takes the least label among its own and
those of its horizontal neighbours. -/
def relax (L : Vector (Fin N) N) : Vector (Fin N) N :=
  Vector.ofFn fun v =>
    ((List.finRange N).filter fun w => X.horizontal v w).foldr (fun w m => min L[w] m) L[v]

/-- The component labels: `N` rounds of propagation from the identity labelling. -/
def labels : Vector (Fin N) N := X.relax^[N] (Vector.ofFn id)

/-- The label of a vertex. For valid input it is the least index in its level component
(`label_eq_label_iff_reachable`, `label_le`). Total; meaningful only under `X.Valid`; use
`incidence?`. On an asymmetric adjacency it is the least vertex reachable by a directed walk
along horizontal edges. -/
def label (v : Fin N) : Fin N := X.labels[v]

section fold

variable {α β : Type*} [LinearOrder β]

private theorem foldr_min_le_init (f : α → β) (b : β) (l : List α) :
    l.foldr (fun w m => min (f w) m) b ≤ b := by
  induction l with
  | nil => exact le_rfl
  | cons a l ih => exact (min_le_right _ _).trans ih

private theorem foldr_min_le_of_mem (f : α → β) (b : β) {l : List α} {w : α} (hw : w ∈ l) :
    l.foldr (fun w m => min (f w) m) b ≤ f w := by
  induction l with
  | nil => simp at hw
  | cons a l ih =>
    rcases List.mem_cons.1 hw with rfl | h
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (ih h)

private theorem foldr_min_eq (f : α → β) (b : β) (l : List α) :
    l.foldr (fun w m => min (f w) m) b = b ∨
      ∃ w ∈ l, l.foldr (fun w m => min (f w) m) b = f w := by
  induction l with
  | nil => exact .inl rfl
  | cons a l ih =>
    rw [List.foldr_cons]
    rcases min_choice (f a) (l.foldr (fun w m => min (f w) m) b) with h | h
    · exact .inr ⟨a, List.mem_cons_self, h⟩
    · rw [h]
      rcases ih with h' | ⟨w, hw, h'⟩
      · exact .inl h'
      · exact .inr ⟨w, List.mem_cons_of_mem _ hw, h'⟩

end fold

private theorem relax_getElem (L : Vector (Fin N) N) (v : Fin N) :
    (X.relax L)[v] =
      ((List.finRange N).filter fun w => X.horizontal v w).foldr (fun w m => min L[w] m) L[v] := by
  simp [relax]

/-- A chain of at most `k` horizontal steps. -/
private inductive Within : ℕ → Fin N → Fin N → Prop
  | refl (k : ℕ) (v : Fin N) : Within k v v
  | step {k : ℕ} {u x w : Fin N} : X.horizontal u x = true → Within k x w → Within (k + 1) u w

private theorem Within.succ {k : ℕ} {u w : Fin N} (h : Within X k u w) :
    Within X (k + 1) u w := by
  induction h with
  | refl k v => exact .refl _ _
  | step hux _ ih => exact .step hux ih

private theorem Within.height_eq {k : ℕ} {u w : Fin N} (h : Within X k u w) :
    X.height w = X.height u := by
  induction h with
  | refl k v => rfl
  | step hux _ ih =>
    rw [ih]
    simp only [horizontal, Bool.and_eq_true, decide_eq_true_eq] at hux
    exact hux.2.symm

/-- After `k` rounds the label of `v` is the least vertex within `k` horizontal steps. -/
private theorem iterate_relax (k : ℕ) (v : Fin N) :
    Within X k v (X.relax^[k] (Vector.ofFn id))[v] ∧
      ∀ w, Within X k v w → (X.relax^[k] (Vector.ofFn id))[v] ≤ w := by
  induction k generalizing v with
  | zero =>
    have h0 : (X.relax^[0] (Vector.ofFn id))[v] = v := by simp
    rw [h0]
    refine ⟨.refl _ _, fun w hw => ?_⟩
    cases hw
    exact le_rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', relax_getElem]
    set L := X.relax^[k] (Vector.ofFn id) with hL
    constructor
    · rcases foldr_min_eq (fun w => L[w]) L[v]
        ((List.finRange N).filter fun w => X.horizontal v w) with h | ⟨w, hw, h⟩
      · rw [h]
        exact (ih v).1.succ
      · rw [h]
        exact .step (List.mem_filter.1 hw).2 (ih w).1
    · intro w hw
      cases hw with
      | refl =>
        exact (foldr_min_le_init _ _ _).trans ((ih v).2 v (.refl _ _))
      | step hux hxw =>
        exact (foldr_min_le_of_mem (fun w => L[w]) L[v]
          (List.mem_filter.2 ⟨List.mem_finRange _, hux⟩)).trans ((ih _).2 w hxw)

theorem label_le (v : Fin N) : X.label v ≤ v :=
  (X.iterate_relax N v).2 v (.refl _ _)

theorem height_label (v : Fin N) : X.height (X.label v) = X.height v :=
  (X.iterate_relax N v).1.height_eq

/-- The graph of horizontal edges of a valid input. -/
private def horizontalGraph (hX : X.Valid) : SimpleGraph (Fin N) where
  Adj u w := X.horizontal u w = true
  symm := ⟨fun u w h => by
    simp only [horizontal, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
    exact ⟨by rw [← hX.1 u w]; exact h.1, h.2.symm⟩⟩
  loopless := ⟨fun u h => by simp [horizontal, hX.2 u] at h⟩

private theorem within_of_walk (hX : X.Valid) {u w : Fin N}
    (p : (X.horizontalGraph hX).Walk u w) : Within X p.length u w := by
  induction p with
  | nil => exact .refl _ _
  | cons h _ ih => exact .step h ih

private theorem Within.mono {k m : ℕ} {u w : Fin N} (h : Within X k u w) (hkm : k ≤ m) :
    Within X m u w := by
  induction hkm with
  | refl => exact h
  | step _ ih => exact ih.succ

private theorem Within.reachable (hX : X.Valid) {k : ℕ} {u w : Fin N} (h : Within X k u w) :
    (X.horizontalGraph hX).Reachable u w := by
  induction h with
  | refl k v => exact .refl _
  | step hux _ ih => exact (Adj.reachable (G := X.horizontalGraph hX) hux).trans ih

private theorem within_of_reachable (hX : X.Valid) {u w : Fin N}
    (h : (X.horizontalGraph hX).Reachable u w) : Within X N u w := by
  obtain ⟨p, hp⟩ := h.exists_isPath
  have hlen : p.length < N := by simpa using hp.length_lt
  exact (X.within_of_walk hX p).mono X hlen.le

private theorem label_eq_label_iff (hX : X.Valid) {u w : Fin N} :
    X.label u = X.label w ↔ (X.horizontalGraph hX).Reachable u w := by
  have hreach : ∀ v, (X.horizontalGraph hX).Reachable v (X.label v) := fun v =>
    (X.iterate_relax N v).1.reachable X hX
  have hle : ∀ {a b}, (X.horizontalGraph hX).Reachable a b → X.label a ≤ b := fun {a b} h =>
    (X.iterate_relax N a).2 b (X.within_of_reachable hX h)
  constructor
  · intro h
    exact (hreach u).trans (h ▸ (hreach w).symm)
  · intro h
    exact le_antisymm (hle (h.trans (hreach w))) (hle (h.symm.trans (hreach u)))

theorem label_label (hX : X.Valid) (v : Fin N) : X.label (X.label v) = X.label v :=
  (X.label_eq_label_iff hX).2 ((X.iterate_relax N v).1.reachable X hX).symm

/-- Reachability in the induced level graph is horizontal reachability. -/
private theorem reachable_induce_iff (hX : X.Valid) {c : ℚ} {u w : Fin N}
    (hu : X.height u = c) (hw : X.height w = c) :
    ((X.graph hX).induce {v | X.realHeight v = (c : ℝ)}).Reachable
        ⟨u, X.realHeight_eq_iff.2 hu⟩ ⟨w, X.realHeight_eq_iff.2 hw⟩ ↔
      (X.horizontalGraph hX).Reachable u w := by
  constructor
  · intro h
    let f : (X.graph hX).induce {v | X.realHeight v = (c : ℝ)} →g X.horizontalGraph hX :=
      { toFun := fun v => v.1
        map_rel' := fun {a b} hab => by
          show X.horizontal a.1 b.1 = true
          simp only [horizontal, Bool.and_eq_true, decide_eq_true_eq]
          exact ⟨hab, (X.realHeight_eq_iff.1 a.2).trans (X.realHeight_eq_iff.1 b.2).symm⟩ }
    exact h.map f
  · rintro ⟨p⟩
    induction p with
    | nil => exact .refl _
    | @cons a b d hab _ ih =>
      have hab' : X.adj a b = true ∧ X.height a = X.height b := by
        have := hab
        simp only [horizontalGraph, horizontal, Bool.and_eq_true, decide_eq_true_eq] at this
        exact this
      have hb : X.height b = c := hab'.2.symm.trans hu
      have hadj : ((X.graph hX).induce {v | X.realHeight v = (c : ℝ)}).Adj
          ⟨a, X.realHeight_eq_iff.2 hu⟩ ⟨b, X.realHeight_eq_iff.2 hb⟩ := hab'.1
      exact hadj.reachable.trans (ih hb hw)

/-- Label equality is reachability in the actual induced level graph. -/
theorem label_eq_label_iff_reachable (hX : X.Valid) {c : ℚ} {u w : Fin N}
    (hu : X.height u = c) (hw : X.height w = c) :
    X.label u = X.label w ↔
      ((X.graph hX).induce {v | X.realHeight v = (c : ℝ)}).Reachable
        ⟨u, X.realHeight_eq_iff.2 hu⟩ ⟨w, X.realHeight_eq_iff.2 hw⟩ :=
  (X.label_eq_label_iff hX).trans (X.reachable_induce_iff hX hu hw).symm

/-- The label fixed points of height `c` are the connected components of the level graph. -/
noncomputable def componentEquiv (hX : X.Valid) (c : ℚ) :
    {r : Fin N // X.label r = r ∧ X.height r = c} ≃
      ((X.graph hX).induce {v | X.realHeight v = (c : ℝ)}).ConnectedComponent where
  toFun r := ((X.graph hX).induce {v | X.realHeight v = (c : ℝ)}).connectedComponentMk
    ⟨r.1, X.realHeight_eq_iff.2 r.2.2⟩
  invFun := ConnectedComponent.lift
    (fun v => ⟨X.label v.1, X.label_label hX v.1,
      (X.height_label v.1).trans (X.realHeight_eq_iff.1 v.2)⟩)
    (fun v w p _ => Subtype.ext
      ((X.label_eq_label_iff_reachable hX (X.realHeight_eq_iff.1 v.2)
        (X.realHeight_eq_iff.1 w.2)).2 ⟨p⟩))
  left_inv r := Subtype.ext r.2.1
  right_inv := by
    refine ConnectedComponent.ind fun v => ?_
    refine ConnectedComponent.sound ?_
    exact ((X.label_eq_label_iff_reachable hX
      ((X.height_label v.1).trans (X.realHeight_eq_iff.1 v.2))
      (X.realHeight_eq_iff.1 v.2)).1 (X.label_label hX v.1))

theorem componentEquiv_apply (hX : X.Valid) (c : ℚ)
    (r : {r : Fin N // X.label r = r ∧ X.height r = c}) :
    X.componentEquiv hX c r =
      ((X.graph hX).induce {v | X.realHeight v = (c : ℝ)}).connectedComponentMk
        ⟨r.1, X.realHeight_eq_iff.2 r.2.2⟩ := rfl

theorem componentEquiv_symm_mk (hX : X.Valid) (c : ℚ) (v : Fin N) (hv : X.height v = c) :
    ((X.componentEquiv hX c).symm
      (((X.graph hX).induce {v | X.realHeight v = (c : ℝ)}).connectedComponentMk
        ⟨v, X.realHeight_eq_iff.2 hv⟩) : Fin N) = X.label v := rfl

/-! ## Cells and edges -/

/-- All ordered pairs of vertices. -/
def vertexPairs (N : ℕ) : List (Fin N × Fin N) := List.finRange N ×ˢ List.finRange N

/-- The cells at level `c` for a labelling `ℓ`: the label fixed points of height `c`, then the
edges crossing `c`. -/
def cellsWith (ℓ : Fin N → Fin N) (c : ℚ) : List (Cell N) :=
  ((List.finRange N).filter fun r => ℓ r = r ∧ X.height r = c).map Sum.inl ++
    ((vertexPairs N).filter fun y =>
      X.adj y.1 y.2 = true ∧ X.height y.1 < c ∧ c < X.height y.2).map Sum.inr

/-- The cell at level `p` of the lower end of an edge. -/
def leftEndWith (ℓ : Fin N → Fin N) (p : ℚ) (y : Fin N × Fin N) : Cell N :=
  if X.height y.1 = p then .inl (ℓ y.1) else .inr y

/-- The cell at level `q` of the upper end of an edge. -/
def rightEndWith (ℓ : Fin N → Fin N) (q : ℚ) (y : Fin N × Fin N) : Cell N :=
  if X.height y.2 = q then .inl (ℓ y.2) else .inr y

/-- The edges spanning `[p, q]` for a labelling `ℓ`, with their endpoint cells. -/
def edgesWith (ℓ : Fin N → Fin N) (p q : ℚ) : List ((Fin N × Fin N) × Cell N × Cell N) :=
  ((vertexPairs N).filter fun y =>
      X.adj y.1 y.2 = true ∧ X.height y.1 ≤ p ∧ q ≤ X.height y.2).map
    fun y => (y, X.leftEndWith ℓ p y, X.rightEndWith ℓ q y)

/-- The cells at level `c`. -/
def cellList (c : ℚ) : List (Cell N) := X.cellsWith X.label c

/-- The left endpoint cell of an edge over a gap with lower level `p`. -/
def leftEnd (p : ℚ) (y : Fin N × Fin N) : Cell N := X.leftEndWith X.label p y

/-- The right endpoint cell of an edge over a gap with upper level `q`. -/
def rightEnd (q : ℚ) (y : Fin N × Fin N) : Cell N := X.rightEndWith X.label q y

/-- The edges spanning `[p, q]`, with their endpoint cells. -/
def edgeList (p q : ℚ) : List ((Fin N × Fin N) × Cell N × Cell N) := X.edgesWith X.label p q

/-- The executed incidence lists; the label vector is computed once. -/
def incidence : Incidence N :=
  let L := X.labels
  let ℓ : Fin N → Fin N := fun v => L[v]
  let lv := X.levels
  { levels := lv
    cells := lv.map (X.cellsWith ℓ)
    edges := (lv.zip lv.tail).map fun pq => X.edgesWith ℓ pq.1 pq.2 }

/-- The executed incidence lists of a valid input; `none` for invalid input. -/
def incidence? : Option (Incidence N) := if X.Valid then some X.incidence else none

private theorem mem_vertexPairs (y : Fin N × Fin N) : y ∈ vertexPairs N := by
  obtain ⟨a, b⟩ := y
  simp [vertexPairs]

theorem incidence_levels : X.incidence.levels = X.levels := rfl

theorem incidence_cells : X.incidence.cells = X.levels.map X.cellList := rfl

theorem incidence_edges :
    X.incidence.edges = (X.levels.zip X.levels.tail).map fun pq => X.edgeList pq.1 pq.2 := rfl

theorem incidence?_eq_some_iff {P : Incidence N} :
    X.incidence? = some P ↔ X.Valid ∧ X.incidence = P := by
  unfold incidence?
  split <;> simp [*]

theorem incidence?_eq_none_iff : X.incidence? = none ↔ ¬ X.Valid := by
  unfold incidence?
  split <;> simp [*]

theorem levels_getElem? (i : Fin (X.gapCount + 1)) : X.levels[i.1]? = some (X.level i) :=
  List.getElem?_eq_getElem _

theorem incidence_cells_getElem? (i : Fin (X.gapCount + 1)) :
    X.incidence.cells[i.1]? = some (X.cellList (X.level i)) := by
  rw [incidence_cells, List.getElem?_map, levels_getElem?]
  rfl

theorem incidence_edges_getElem? (e : Fin X.gapCount) :
    X.incidence.edges[e.1]? = some (X.edgeList (X.level e.castSucc) (X.level e.succ)) := by
  have h₁ : X.levels[e.1]? = some (X.level e.castSucc) := X.levels_getElem? e.castSucc
  have h₂ : X.levels.tail[e.1]? = some (X.level e.succ) := by
    rw [List.getElem?_tail]
    exact X.levels_getElem? e.succ
  rw [incidence_edges, List.getElem?_map,
    List.getElem?_zip_eq_some (z := (X.level e.castSucc, X.level e.succ)) |>.2 ⟨h₁, h₂⟩]
  rfl

theorem mem_cellList_inl {c : ℚ} {r : Fin N} :
    Sum.inl r ∈ X.cellList c ↔ X.label r = r ∧ X.height r = c := by
  simp [cellList, cellsWith]

theorem mem_cellList_inr {c : ℚ} {y : Fin N × Fin N} :
    Sum.inr y ∈ X.cellList c ↔
      X.adj y.1 y.2 = true ∧ X.height y.1 < c ∧ c < X.height y.2 := by
  simp [cellList, cellsWith, mem_vertexPairs]

private theorem nodup_vertexPairs : (vertexPairs N).Nodup :=
  (List.nodup_finRange N).product (List.nodup_finRange N)

theorem nodup_cellList (c : ℚ) : (X.cellList c).Nodup := by
  unfold cellList cellsWith
  refine List.Nodup.append ?_ ?_ ?_
  · exact ((List.nodup_finRange N).filter _).map Sum.inl_injective
  · exact (nodup_vertexPairs.filter _).map Sum.inr_injective
  · intro x hx hx'
    obtain ⟨r, -, rfl⟩ := List.mem_map.1 hx
    obtain ⟨y, -, hy⟩ := List.mem_map.1 hx'
    exact Sum.inr_ne_inl hy

theorem mem_edgeList {p q : ℚ} {z : (Fin N × Fin N) × Cell N × Cell N} :
    z ∈ X.edgeList p q ↔
      (X.adj z.1.1 z.1.2 = true ∧ X.height z.1.1 ≤ p ∧ q ≤ X.height z.1.2) ∧
        z.2.1 = X.leftEnd p z.1 ∧ z.2.2 = X.rightEnd q z.1 := by
  obtain ⟨y, a, b⟩ := z
  simp only [edgeList, edgesWith, leftEnd, rightEnd, List.mem_map, List.mem_filter,
    mem_vertexPairs, true_and, decide_eq_true_eq, Prod.mk.injEq]
  constructor
  · rintro ⟨y', hy', rfl, rfl, rfl⟩
    exact ⟨hy', rfl, rfl⟩
  · rintro ⟨hy, rfl, rfl⟩
    exact ⟨y, hy, rfl, rfl, rfl⟩

/-- One entry per spanning edge. -/
theorem nodup_edgeList (p q : ℚ) : ((X.edgeList p q).map Prod.fst).Nodup := by
  unfold edgeList edgesWith
  rw [List.map_map]
  exact (nodup_vertexPairs.filter _).map fun _ _ h => h

/-- The left endpoint cell of a listed edge is a listed cell of the lower level. -/
theorem leftEnd_mem_cellList (hX : X.Valid) {p q : ℚ} (hpq : p < q)
    {z : (Fin N × Fin N) × Cell N × Cell N} (hz : z ∈ X.edgeList p q) :
    z.2.1 ∈ X.cellList p := by
  obtain ⟨⟨hadj, hlo, hhi⟩, hl, -⟩ := X.mem_edgeList.1 hz
  rw [hl]
  unfold leftEnd leftEndWith
  split_ifs with h
  · exact X.mem_cellList_inl.2 ⟨X.label_label hX _, (X.height_label _).trans h⟩
  · exact X.mem_cellList_inr.2 ⟨hadj, lt_of_le_of_ne hlo h, hpq.trans_le hhi⟩

/-- The right endpoint cell of a listed edge is a listed cell of the upper level. -/
theorem rightEnd_mem_cellList (hX : X.Valid) {p q : ℚ} (hpq : p < q)
    {z : (Fin N × Fin N) × Cell N × Cell N} (hz : z ∈ X.edgeList p q) :
    z.2.2 ∈ X.cellList q := by
  obtain ⟨⟨hadj, hlo, hhi⟩, -, hr⟩ := X.mem_edgeList.1 hz
  rw [hr]
  unfold rightEnd rightEndWith
  split_ifs with h
  · exact X.mem_cellList_inl.2 ⟨X.label_label hX _, (X.height_label _).trans h⟩
  · exact X.mem_cellList_inr.2 ⟨hadj, hlo.trans_lt hpq, lt_of_le_of_ne hhi (Ne.symm h)⟩

end HeightGraph

end TDA.Mapper.GraphPL
