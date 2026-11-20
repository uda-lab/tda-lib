import TDA.Persistence.Reduction.FiniteInput
import TDA.Filtration.Rips
import Mathlib.Data.List.Sublists
import Mathlib.Data.List.Sort
import Mathlib.Data.List.FinRange
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Powerset

/-!
# Rips simplex input from an integer distance table

A `DistanceTable N` is a function `Fin N → Fin N → ℤ`. This module validates it as a metric and
computes from it the complete Rips simplex list in the format of
`TDA.Persistence.Reduction.FiniteInput`:

* `Valid`: nonnegative entries, symmetry, zero diagonal, positive distance between distinct
  labels and every triangle inequality; a decidable proposition. Nothing is repaired.
* `diameter s`: the integer diameter of a set of labels, the maximum entry over its ordered pairs
  and `0` for the empty set.
* `faceLists N`: the nonempty strictly increasing label lists, by length and then
  lexicographically, each once.
* `ripsInput`: one entry `(s.map Fin.valEmbedding, diameter s)` for each nonempty set `s` of
  labels, by grade, then by cardinality, then lexicographically in the increasing label lists.
  The labels `0, …, N - 1` are transported into the ambient vertex type `ℕ` of `FiniteInput`;
  no metric on `ℕ` is introduced.
* `ripsInput?` and `ripsRun`: the list, and the occurrence records of the existing reduction on
  it, for valid tables only; `none` for an invalid table.

## Statements

`mem_ripsInput` characterizes the entries, `ripsInput_pairwise` the order and
`length_ripsInput` the number `2 ^ N - 1` of entries. `ripsInput_valid` proves the five
conditions of `FiniteInput.Valid`; it holds for every table, because the maximum over pairs is
monotone in the set, so `ripsRun` does not validate the list again
(`ripsRun_eq_bind_run`). For a valid table, `metric` is the metric on `Fin N` with the table
entries as distances and `cast_diameter` identifies `diameter` with `Rips.diameter`. The
represented complex is the image of `Rips.fullComplex (Fin N)` (`mem_complex_ripsInput`,
`complex_ripsInput`), `ripsFace` is the bijection of faces, and `gradeFilter_ripsFace`
identifies the listed grade of a face with the value of `Rips.filter` at the corresponding
face. The comparison of the resulting diagrams is not in this module.

## Cost

Write `F = 2 ^ N - 1` for the number of faces and `G` for the number of distinct grades; every
grade is `0` or a table entry, so `G ≤ N (N - 1) / 2 + 1` for a valid table. Validation makes
`O(N³)` integer comparisons and additions. The enumeration builds `F` lists of total length
`N 2 ^ (N - 1)`. Each face of `k` labels costs `O(k²)` label comparisons to form its set of
labels and `k²` table lookups and integer maxima for its diameter: `O(N² F)` in total. The
distinct grades cost `O(F G)` integer comparisons to collect and `O(G²)` to sort by insertion,
and the grouping by grade scans the `F` entries once for each grade: `O(F G)`. Together the list
costs `O(N² F)` operations on labels and integers, which is exponential in `N`; an integer
operation costs time proportional to the bit length of the entries. `ripsRun` adds the cost of
the existing `FiniteInput.occurrences` on `F` faces, which this module does not bound; it is at
least quadratic in `F` (the dense `F × F` boundary matrix) and dominates already for small
tables. These counts are documented and are not theorems.

The executable definitions use lists, finite sets given by lists, and integer comparison: no
decision by `Classical` and no real-number comparison. This is shown by evaluation: the proofs
carried by `Finset` are the only reason `#print axioms` lists `Classical.choice` for them.
`metric`, `cast_diameter` and the statements about `Rips` are semantic adapters.

These are elementary library results, not attributed to a source. See
`docs/math/finite-ph-computation.md`.
-/

set_option autoImplicit false

namespace TDA.Persistence.Reduction

open TDA.Simplicial TDA.Filtration

/-- A finite table of integer distances on the labels `Fin N`. -/
structure DistanceTable (N : ℕ) where
  /-- The distance between two labels. -/
  dist : Fin N → Fin N → ℤ

namespace DistanceTable

variable {N : ℕ} (D : DistanceTable N)

/-! ## Validation and the metric -/

/-- The table is a metric: nonnegative entries, symmetry, zero diagonal, positive distance
between distinct labels, and the triangle inequality. -/
def Valid : Prop :=
  (∀ i j, 0 ≤ D.dist i j) ∧ (∀ i j, D.dist i j = D.dist j i) ∧ (∀ i, D.dist i i = 0) ∧
    (∀ i j, i ≠ j → 0 < D.dist i j) ∧ ∀ i j k, D.dist i k ≤ D.dist i j + D.dist j k

instance instDecidableValid : Decidable D.Valid := by unfold Valid; infer_instance

/-- The metric on the labels of a valid table, with the table entries as distances. -/
@[instance_reducible]
noncomputable def metric (hD : D.Valid) : MetricSpace (Fin N) where
  dist i j := (D.dist i j : ℝ)
  dist_self i := by simp [hD.2.2.1 i]
  dist_comm i j := by rw [hD.2.1 i j]
  dist_triangle i j k := by exact_mod_cast hD.2.2.2.2 i j k
  eq_of_dist_eq_zero := by
    intro i j h
    by_contra hij
    have hpos := hD.2.2.2.1 i j hij
    have h0 : D.dist i j = 0 := by exact_mod_cast h
    omega

theorem metric_dist (hD : D.Valid) (i j : Fin N) :
    (D.metric hD).dist i j = (D.dist i j : ℝ) := rfl

/-! ## Integer diameter -/

/-- The integer diameter of a set of labels: the maximum entry over its ordered pairs, and `0`
for the empty set. -/
def diameter (s : Finset (Fin N)) : ℤ := (s ×ˢ s).fold max 0 fun p => D.dist p.1 p.2

theorem diameter_le_iff (s : Finset (Fin N)) (r : ℤ) :
    D.diameter s ≤ r ↔ 0 ≤ r ∧ ∀ v ∈ s, ∀ w ∈ s, D.dist v w ≤ r := by
  unfold diameter
  rw [Finset.fold_max_le]
  constructor
  · rintro ⟨hr, h⟩
    exact ⟨hr, fun v hv w hw => h (v, w) (Finset.mem_product.mpr ⟨hv, hw⟩)⟩
  · rintro ⟨hr, h⟩
    exact ⟨hr, fun p hp => h p.1 (Finset.mem_product.mp hp).1 p.2 (Finset.mem_product.mp hp).2⟩

theorem diameter_nonneg (s : Finset (Fin N)) : 0 ≤ D.diameter s :=
  ((D.diameter_le_iff s _).1 le_rfl).1

theorem dist_le_diameter {s : Finset (Fin N)} {v w : Fin N} (hv : v ∈ s) (hw : w ∈ s) :
    D.dist v w ≤ D.diameter s :=
  ((D.diameter_le_iff s _).1 le_rfl).2 v hv w hw

theorem diameter_mono {s t : Finset (Fin N)} (hst : s ⊆ t) : D.diameter s ≤ D.diameter t :=
  (D.diameter_le_iff s _).2
    ⟨D.diameter_nonneg t, fun _ hv _ hw => D.dist_le_diameter (hst hv) (hst hw)⟩

/-- A single label has diameter `0` when the diagonal entry is `0`. -/
theorem diameter_singleton (hD : D.Valid) (v : Fin N) : D.diameter {v} = 0 := by
  apply le_antisymm _ (D.diameter_nonneg _)
  refine (D.diameter_le_iff _ _).2 ⟨le_rfl, fun a ha b hb => ?_⟩
  rw [Finset.mem_singleton.1 ha, Finset.mem_singleton.1 hb, hD.2.2.1 v]

/-- The integer diameter is the diameter of the existing Rips filtration for `metric`. -/
theorem cast_diameter (hD : D.Valid) (s : Finset (Fin N)) :
    ((D.diameter s : ℤ) : ℝ) = Rips.diameter (D.metric hD) s := by
  unfold diameter Rips.diameter
  rw [← Finset.fold_hom (op := max) (op' := max) (m := ((↑) : ℤ → ℝ))
    fun _ _ => Int.cast_max]
  simp only [Int.cast_zero, metric_dist]

/-! ## Enumeration of the faces -/

/-- The nonempty strictly increasing label lists: by length, then lexicographically. -/
def faceLists (N : ℕ) : List (List (Fin N)) :=
  (List.range N).flatMap fun k => (List.sublistsLen (k + 1) (List.finRange N)).reverse

private theorem mem_faceLists_iff {l : List (Fin N)} :
    l ∈ faceLists N ↔ ∃ k < N, l.Sublist (List.finRange N) ∧ l.length = k + 1 := by
  simp only [faceLists, List.mem_flatMap, List.mem_range, List.mem_reverse,
    List.mem_sublistsLen]

theorem mem_faceLists {l : List (Fin N)} :
    l ∈ faceLists N ↔ l ≠ [] ∧ l.Pairwise (· < ·) := by
  rw [mem_faceLists_iff]
  constructor
  · rintro ⟨k, -, hl, hk⟩
    exact ⟨fun h => by simp [h] at hk, (List.pairwise_lt_finRange N).sublist hl⟩
  · rintro ⟨hne, hp⟩
    have hnd : l.Nodup := hp.imp ne_of_lt
    have hsub : l.Sublist (List.finRange N) :=
      List.sublist_of_subperm_of_pairwise
        (List.subperm_of_subset hnd fun x _ => List.mem_finRange x) hp
        (List.pairwise_lt_finRange N)
    have hpos : 0 < l.length := List.length_pos_iff.2 hne
    have hle : l.length ≤ N := by simpa using hsub.length_le
    exact ⟨l.length - 1, by omega, hsub, by omega⟩

private theorem pairwise_sublistsLen {α : Type*} [LinearOrder α] :
    ∀ (k : ℕ) (l : List α), l.Pairwise (· < ·) →
      (List.sublistsLen k l).Pairwise fun x y => y < x
  | 0, l, _ => by simp
  | k + 1, [], _ => by simp
  | k + 1, a :: l, h => by
    rw [List.sublistsLen_succ_cons, List.pairwise_append]
    have hl := (List.pairwise_cons.1 h).2
    refine ⟨pairwise_sublistsLen (k + 1) l hl, ?_, ?_⟩
    · rw [List.pairwise_map]
      exact (pairwise_sublistsLen k l hl).imp fun hxy =>
        List.cons_lt_cons_iff.2 (.inr ⟨rfl, hxy⟩)
    · intro x hx y hy
      obtain ⟨y', -, rfl⟩ := List.mem_map.1 hy
      obtain ⟨hxl, hlen⟩ := List.mem_sublistsLen.1 hx
      match x, hlen with
      | b :: x', _ =>
        exact List.cons_lt_cons_iff.2
          (.inl ((List.pairwise_cons.1 h).1 b (hxl.subset List.mem_cons_self)))

/-- The order of the enumeration: by length, then lexicographically. -/
private def ListLT (x y : List (Fin N)) : Prop :=
  x.length < y.length ∨ x.length = y.length ∧ x < y

private theorem pairwise_faceLists : (faceLists N).Pairwise ListLT := by
  unfold faceLists
  rw [List.pairwise_flatMap]
  constructor
  · intro k _
    rw [List.pairwise_reverse]
    refine (pairwise_sublistsLen (k + 1) _ (List.pairwise_lt_finRange N)).imp_of_mem ?_
    intro x y hx hy hxy
    exact .inr ⟨(List.mem_sublistsLen.1 hy).2.trans (List.mem_sublistsLen.1 hx).2.symm, hxy⟩
  · refine (List.pairwise_lt_range (n := N)).imp ?_
    intro k₁ k₂ hk x hx y hy
    rw [List.mem_reverse, List.mem_sublistsLen] at hx hy
    exact .inl (by omega)

theorem nodup_faceLists : (faceLists N).Nodup :=
  (pairwise_faceLists (N := N)).imp fun {x y} h hxy => by
    subst hxy
    rcases h with h | ⟨-, h⟩
    · exact lt_irrefl _ h
    · exact List.lt_irrefl _ h

/-! ## The simplex list -/

/-- The entry of a label list: its set of labels in `ℕ` and its integer diameter. -/
def entry (l : List (Fin N)) : FiniteInput.Entry :=
  let s := l.toFinset
  (s.map Fin.valEmbedding, D.diameter s)

/-- The entries of all faces in the order of `faceLists`. -/
def entries : List FiniteInput.Entry := (faceLists N).map D.entry

/-- The Rips simplex list of the table: the entries grouped by grade in increasing order, each
group in the order of `faceLists`. -/
def ripsInput : FiniteInput.Input :=
  let es := D.entries
  (((es.map Prod.snd).dedup).insertionSort (· ≤ ·)).flatMap fun g => es.filter fun e => e.2 = g

/-- The Rips simplex list of a valid table; `none` for an invalid table. -/
def ripsInput? : Option FiniteInput.Input := if D.Valid then some D.ripsInput else none

/-- The occurrence records of the existing reduction on the Rips simplex list of a valid
table; `none` for an invalid table. -/
def ripsRun : Option (List FiniteInput.Occurrence) :=
  if D.Valid then some (FiniteInput.occurrences D.ripsInput) else none

theorem ripsInput?_eq_some_iff {xs : FiniteInput.Input} :
    D.ripsInput? = some xs ↔ D.Valid ∧ xs = D.ripsInput := by
  unfold ripsInput?
  by_cases h : D.Valid <;> simp [h, eq_comm]

theorem ripsInput?_eq_none_iff : D.ripsInput? = none ↔ ¬ D.Valid := by
  unfold ripsInput?
  by_cases h : D.Valid <;> simp [h]

theorem ripsRun_eq_some_iff {out : List FiniteInput.Occurrence} :
    D.ripsRun = some out ↔ D.Valid ∧ out = FiniteInput.occurrences D.ripsInput := by
  unfold ripsRun
  by_cases h : D.Valid <;> simp [h, eq_comm]

theorem ripsRun_eq_none_iff : D.ripsRun = none ↔ ¬ D.Valid := by
  unfold ripsRun
  by_cases h : D.Valid <;> simp [h]

/-! ## Entries -/

private theorem mem_entries {e : FiniteInput.Entry} :
    e ∈ D.entries ↔
      ∃ s : Finset (Fin N), s.Nonempty ∧ e = (s.map Fin.valEmbedding, D.diameter s) := by
  simp only [entries, List.mem_map, mem_faceLists, entry]
  constructor
  · rintro ⟨l, ⟨hne, -⟩, rfl⟩
    exact ⟨l.toFinset, (List.toFinset_nonempty_iff l).2 hne, rfl⟩
  · rintro ⟨s, hs, rfl⟩
    have hlt : (s.sort (· ≤ ·)).Pairwise (· < ·) :=
      ((Finset.pairwise_sort s (· ≤ ·)).and (Finset.sort_nodup s (· ≤ ·))).imp
        fun h => lt_of_le_of_ne h.1 h.2
    refine ⟨s.sort (· ≤ ·), ⟨?_, hlt⟩, by rw [Finset.sort_toFinset]⟩
    intro h
    have hlen := Finset.length_sort (s := s) (· ≤ ·)
    rw [h] at hlen
    exact hs.ne_empty (Finset.card_eq_zero.1 hlen.symm)

private theorem ripsInput_eq :
    D.ripsInput = (((D.entries.map Prod.snd).dedup).insertionSort (· ≤ ·)).flatMap
      fun g => D.entries.filter fun e => e.2 = g := rfl

private theorem mem_ripsInput_iff_mem_entries {e : FiniteInput.Entry} :
    e ∈ D.ripsInput ↔ e ∈ D.entries := by
  simp only [ripsInput_eq, List.mem_flatMap, List.mem_insertionSort, List.mem_dedup,
    List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨g, -, he, -⟩
    exact he
  · intro he
    exact ⟨e.2, ⟨e, he, rfl⟩, he, rfl⟩

/-- The entries: one for each nonempty set of labels, with its integer diameter. -/
theorem mem_ripsInput {e : FiniteInput.Entry} :
    e ∈ D.ripsInput ↔
      ∃ s : Finset (Fin N), s.Nonempty ∧ e = (s.map Fin.valEmbedding, D.diameter s) :=
  D.mem_ripsInput_iff_mem_entries.trans D.mem_entries

theorem mem_faces_ripsInput {t : Finset ℕ} :
    t ∈ FiniteInput.faces D.ripsInput ↔
      ∃ s : Finset (Fin N), s.Nonempty ∧ t = s.map Fin.valEmbedding := by
  simp only [FiniteInput.faces, List.mem_map, mem_ripsInput]
  constructor
  · rintro ⟨e, ⟨s, hs, rfl⟩, rfl⟩
    exact ⟨s, hs, rfl⟩
  · rintro ⟨s, hs, rfl⟩
    exact ⟨_, ⟨s, hs, rfl⟩, rfl⟩

private theorem snd_eq_diameter {e : FiniteInput.Entry} (he : e ∈ D.ripsInput)
    {s : Finset (Fin N)} (hs : e.1 = s.map Fin.valEmbedding) : e.2 = D.diameter s := by
  obtain ⟨s', -, rfl⟩ := D.mem_ripsInput.1 he
  rw [Finset.map_injective _ hs]

/-- The grade listed with the face of a set of labels is its integer diameter. -/
theorem mk_mem_ripsInput {s : Finset (Fin N)} {g : ℤ} :
    (s.map Fin.valEmbedding, g) ∈ D.ripsInput ↔ s.Nonempty ∧ g = D.diameter s := by
  constructor
  · intro h
    obtain ⟨s', hs', he⟩ := D.mem_ripsInput.1 h
    have hs : s = s' := Finset.map_injective _ (congrArg Prod.fst he)
    exact ⟨hs ▸ hs', D.snd_eq_diameter h rfl⟩
  · rintro ⟨hs, rfl⟩
    exact D.mem_ripsInput.2 ⟨s, hs, rfl⟩

/-! ## Order -/

/-- The order of the entries of one grade: by cardinality, then lexicographically in the
increasing label lists. -/
private def FaceLT (a b : FiniteInput.Entry) : Prop :=
  a.1.card < b.1.card ∨ a.1.card = b.1.card ∧ a.1.sort (· ≤ ·) < b.1.sort (· ≤ ·)

private theorem map_val_lt_map_val :
    ∀ {x y : List (Fin N)}, x < y → x.map Fin.val < y.map Fin.val
  | [], [], h => absurd h (List.lt_irrefl _)
  | [], b :: y, _ => by simp
  | a :: x, [], h => by simp at h
  | a :: x, b :: y, h => by
    rw [List.map_cons, List.map_cons, List.cons_lt_cons_iff]
    rcases List.cons_lt_cons_iff.1 h with hab | ⟨hab, hxy⟩
    · exact .inl hab
    · exact .inr ⟨congrArg Fin.val hab, map_val_lt_map_val hxy⟩

private theorem entry_fst_card {l : List (Fin N)} (hl : l ∈ faceLists N) :
    (D.entry l).1.card = l.length := by
  have hnd : l.Nodup := (mem_faceLists.1 hl).2.imp ne_of_lt
  simp only [entry, Finset.card_map, List.toFinset_card_of_nodup hnd]

private theorem entry_fst_sort {l : List (Fin N)} (hl : l ∈ faceLists N) :
    (D.entry l).1.sort (· ≤ ·) = l.map Fin.val := by
  have hp : (l.map Fin.val).Pairwise (· < ·) :=
    List.pairwise_map.2 ((mem_faceLists.1 hl).2.imp fun h => h)
  have hnd : (l.map Fin.val).Nodup := hp.imp ne_of_lt
  have hfin : (D.entry l).1 = (l.map Fin.val).toFinset := by
    ext x
    simp [entry]
  rw [hfin]
  exact (List.toFinset_sort (· ≤ ·) hnd).2 (hp.imp le_of_lt)

private theorem pairwise_entries : D.entries.Pairwise FaceLT := by
  unfold entries
  rw [List.pairwise_map]
  refine (pairwise_faceLists (N := N)).imp_of_mem ?_
  intro x y hx hy h
  unfold FaceLT
  rw [D.entry_fst_card hx, D.entry_fst_card hy, D.entry_fst_sort hx, D.entry_fst_sort hy]
  rcases h with h | ⟨h₁, h₂⟩
  · exact .inl h
  · exact .inr ⟨h₁, map_val_lt_map_val h₂⟩

/-- The order of the list: by grade, then by cardinality, then lexicographically in the
increasing label lists. -/
theorem ripsInput_pairwise :
    D.ripsInput.Pairwise fun a b =>
      a.2 < b.2 ∨ a.2 = b.2 ∧
        (a.1.card < b.1.card ∨
          a.1.card = b.1.card ∧ a.1.sort (· ≤ ·) < b.1.sort (· ≤ ·)) := by
  rw [ripsInput_eq, List.pairwise_flatMap]
  constructor
  · intro g _
    refine (D.pairwise_entries.filter _).imp_of_mem ?_
    intro a b ha hb h
    have ha' : a.2 = g := by simpa using (List.mem_filter.1 ha).2
    have hb' : b.2 = g := by simpa using (List.mem_filter.1 hb).2
    exact .inr ⟨ha'.trans hb'.symm, h⟩
  · have hs := List.pairwise_insertionSort (· ≤ ·) ((D.entries.map Prod.snd).dedup)
    have hn : (((D.entries.map Prod.snd).dedup).insertionSort (· ≤ ·)).Nodup :=
      (List.perm_insertionSort _ _).nodup_iff.2 (List.nodup_dedup _)
    refine (hs.and hn).imp ?_
    intro g₁ g₂ h a ha b hb
    have ha' : a.2 = g₁ := by simpa using (List.mem_filter.1 ha).2
    have hb' : b.2 = g₂ := by simpa using (List.mem_filter.1 hb).2
    exact .inl (by rw [ha', hb']; exact lt_of_le_of_ne h.1 h.2)

/-- Each nonempty set of labels is listed once. -/
theorem nodup_faces_ripsInput : (FiniteInput.faces D.ripsInput).Nodup := by
  unfold FiniteInput.faces
  rw [List.Nodup, List.pairwise_map]
  refine D.ripsInput_pairwise.imp_of_mem ?_
  intro a b ha hb h hab
  obtain ⟨s, -, rfl⟩ := D.mem_ripsInput.1 ha
  have hb2 := D.snd_eq_diameter hb hab.symm
  rcases h with h | ⟨-, h | ⟨-, h⟩⟩
  · exact absurd h (by rw [hb2]; exact lt_irrefl _)
  · exact absurd h (by rw [hab]; exact lt_irrefl _)
  · exact absurd h (by rw [hab]; exact List.lt_irrefl _)

theorem length_ripsInput : D.ripsInput.length = 2 ^ N - 1 := by
  have hlen : D.ripsInput.length = (FiniteInput.faces D.ripsInput).toFinset.card := by
    rw [List.toFinset_card_of_nodup D.nodup_faces_ripsInput, FiniteInput.faces,
      List.length_map]
  have hset : (FiniteInput.faces D.ripsInput).toFinset =
      ((Finset.univ : Finset (Fin N)).powerset.erase ∅).map
        ⟨Finset.map Fin.valEmbedding, Finset.map_injective _⟩ := by
    ext t
    simp only [List.mem_toFinset, mem_faces_ripsInput, Finset.mem_map, Finset.mem_erase,
      Finset.mem_powerset, Finset.subset_univ, and_true, Function.Embedding.coeFn_mk,
      Finset.nonempty_iff_ne_empty]
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨s, hs, rfl⟩
    · rintro ⟨s, hs, rfl⟩
      exact ⟨s, hs, rfl⟩
  rw [hlen, hset, Finset.card_map, Finset.card_erase_of_mem (by simp), Finset.card_powerset,
    Finset.card_univ, Fintype.card_fin]

/-! ## Validity of the list -/

/-- The list satisfies the five conditions of `FiniteInput.Valid`, for every table. -/
theorem ripsInput_valid : FiniteInput.Valid D.ripsInput := by
  have hget : ∀ i : Fin D.ripsInput.length, ∃ s : Finset (Fin N), s.Nonempty ∧
      D.ripsInput.get i = (s.map Fin.valEmbedding, D.diameter s) := fun i =>
    D.mem_ripsInput.1 (List.get_mem _ i)
  have hpw := List.pairwise_iff_get.1 D.ripsInput_pairwise
  refine ⟨?_, D.nodup_faces_ripsInput, ?_, ?_, ?_⟩
  · intro i
    obtain ⟨s, hs, h⟩ := hget i
    rw [h]
    exact hs.map
  · intro i t ht hne
    obtain ⟨s, -, h⟩ := hget i
    rw [h, Finset.mem_powerset] at ht
    obtain ⟨u, -, rfl⟩ := Finset.subset_map_iff.1 ht
    exact D.mem_faces_ripsInput.2 ⟨u, Finset.map_nonempty.1 hne, rfl⟩
  · intro i j hij
    by_contra hnot
    rcases lt_or_eq_of_le (not_lt.1 hnot) with hlt | heq
    · obtain ⟨s, -, hi⟩ := hget i
      obtain ⟨t, -, hj⟩ := hget j
      rw [hi, hj] at hij
      have hmono := D.diameter_mono (Finset.map_subset_map.1 hij.subset)
      have hcard : s.card < t.card := by simpa using Finset.card_lt_card hij
      have h := hpw j i hlt
      rw [hi, hj] at h
      simp only [Finset.card_map] at h
      omega
    · rw [heq] at hij
      exact ssubset_irrefl _ hij
  · intro i j hij
    rcases lt_or_eq_of_le hij with hlt | heq
    · rcases hpw i j hlt with h | ⟨h, -⟩
      · exact h.le
      · exact h.le
    · rw [heq]

/-- `ripsRun` is the existing `FiniteInput.run` on the validated list; the list itself is not
validated again. -/
theorem ripsRun_eq_bind_run : D.ripsRun = D.ripsInput?.bind FiniteInput.run := by
  unfold ripsRun ripsInput?
  by_cases h : D.Valid
  · simp only [h, ↓reduceIte, Option.bind_some]
    exact ((FiniteInput.run_eq_some_iff _ _).2 ⟨D.ripsInput_valid, rfl⟩).symm
  · simp only [h, ↓reduceIte, Option.bind_none]

/-! ## Comparison with the Rips filtration -/

/-- The listed faces are the images of the faces of the full complex on the labels. -/
theorem mem_complex_ripsInput {t : Finset ℕ} :
    t ∈ FiniteInput.complex D.ripsInput D.ripsInput_valid ↔
      ∃ s ∈ Rips.fullComplex (Fin N), t = s.map Fin.valEmbedding := by
  rw [FiniteInput.mem_complex, mem_faces_ripsInput]
  simp only [Rips.mem_fullComplex_iff]

/-- The represented complex is the image of the full complex under the inclusion of labels. -/
theorem complex_ripsInput :
    FiniteInput.complex D.ripsInput D.ripsInput_valid =
      (Rips.fullComplex (Fin N)).map Fin.val := by
  apply SetLike.ext
  intro t
  rw [mem_complex_ripsInput]
  change _ ↔ t ∈ (Rips.fullComplex (Fin N)).faces.image fun s => s.image Fin.val
  simp only [Set.mem_image, Finset.map_eq_image, Fin.valEmbedding_apply]
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact ⟨s, hs, rfl⟩
  · rintro ⟨s, hs, rfl⟩
    exact ⟨s, hs, rfl⟩

/-- The listed face of a nonempty set of labels. -/
def ripsFace (s : TotalFace (Rips.fullComplex (Fin N))) :
    TotalFace (FiniteInput.complex D.ripsInput D.ripsInput_valid) :=
  ⟨s.1.map Fin.valEmbedding, D.mem_complex_ripsInput.2 ⟨s.1, s.2, rfl⟩⟩

@[simp] theorem ripsFace_val (s : TotalFace (Rips.fullComplex (Fin N))) :
    (D.ripsFace s).1 = s.1.map Fin.valEmbedding := rfl

theorem ripsFace_bijective : Function.Bijective D.ripsFace := by
  constructor
  · intro s t h
    exact Subtype.ext (Finset.map_injective _ (congrArg Subtype.val h))
  · intro t
    obtain ⟨s, hs, h⟩ := D.mem_complex_ripsInput.1 t.2
    exact ⟨⟨s, hs⟩, Subtype.ext h.symm⟩

/-- The grade read by `FiniteInput.gradeFilter` at a face is the integer diameter of its
labels. -/
theorem gradeFilter_ripsFace_eq_diameter (s : TotalFace (Rips.fullComplex (Fin N))) :
    (FiniteInput.gradeFilter D.ripsInput D.ripsInput_valid).value (D.ripsFace s) =
      D.diameter s.1 := by
  have hface := FiniteInput.listFace_listEquiv_symm D.ripsInput D.ripsInput_valid
    (D.ripsFace s)
  exact D.snd_eq_diameter (List.get_mem _ _) (congrArg Subtype.val hface)

/-- Grade law: the grade read by `FiniteInput.gradeFilter` at a face is the value of the
existing Rips filter for `metric` at the corresponding face of the full complex. -/
theorem gradeFilter_ripsFace (hD : D.Valid) (s : TotalFace (Rips.fullComplex (Fin N))) :
    (((FiniteInput.gradeFilter D.ripsInput D.ripsInput_valid).value (D.ripsFace s) : ℤ) : ℝ) =
      (Rips.filter (D.metric hD)).value s := by
  rw [gradeFilter_ripsFace_eq_diameter, cast_diameter D hD, Rips.filter_value]

end DistanceTable

end TDA.Persistence.Reduction
