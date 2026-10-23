import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic

/-!
# Farthest-first nets in a finite metric space

Starting from a chosen vertex, each greedyPrefix grows by a vertex maximizing its distance
to that greedyPrefix. The construction stabilizes at the whole space. The next insertion
radius bounds the covering radius of the current greedyPrefix and separates all vertices
already inserted. The initial vertex is supplied separately: it has no finite
insertion radius.
-/

namespace TDA.Filtration.SparseRips.GreedyNet

noncomputable section

variable {V : Type*} [MetricSpace V]

local instance greedyNetDecidableEq : DecidableEq V := Classical.decEq V

/-- Distance to a finite set, with auxiliary value zero at the empty set. -/
def nearestDistance (s : Finset V) (x : V) : ℝ :=
  by
    classical
    exact if h : s.Nonempty then s.inf' h (dist x) else 0

theorem nearestDistance_le {s : Finset V} {x y : V} (hy : y ∈ s) :
    nearestDistance s x ≤ dist x y := by
  classical
  rw [nearestDistance, dif_pos (show s.Nonempty from ⟨y, hy⟩)]
  exact Finset.inf'_le _ hy

theorem exists_nearest {s : Finset V} (hs : s.Nonempty) (x : V) :
    ∃ y ∈ s, dist x y = nearestDistance s x := by
  classical
  obtain ⟨y, hy, hmin⟩ := s.exists_min_image (dist x) hs
  refine ⟨y, hy, le_antisymm ?_ (nearestDistance_le hy)⟩
  simp only [nearestDistance, dif_pos hs]
  exact Finset.le_inf' hs (dist x) (fun z hz => hmin z hz)

theorem nearestDistance_nonneg (s : Finset V) (x : V) :
    0 ≤ nearestDistance s x := by
  classical
  by_cases hs : s.Nonempty
  · obtain ⟨y, _, hy⟩ := exists_nearest hs x
    rw [← hy]
    exact dist_nonneg
  · simp [nearestDistance, hs]

@[simp] theorem nearestDistance_of_mem {s : Finset V} {x : V} (hx : x ∈ s) :
    nearestDistance s x = 0 :=
  le_antisymm (by simpa using nearestDistance_le (x := x) hx)
    (nearestDistance_nonneg s x)

theorem nearestDistance_pos {s : Finset V} (hs : s.Nonempty) {x : V} (hx : x ∉ s) :
    0 < nearestDistance s x := by
  obtain ⟨y, hy, heq⟩ := exists_nearest hs x
  rw [← heq]
  exact dist_pos.mpr (fun h => hx (h ▸ hy))

theorem nearestDistance_antitone {s t : Finset V} (hs : s.Nonempty) (hst : s ⊆ t)
    (x : V) : nearestDistance t x ≤ nearestDistance s x := by
  obtain ⟨y, hy, heq⟩ := exists_nearest hs x
  rw [← heq]
  exact nearestDistance_le (hst hy)

variable [Fintype V]

/-- A farthest vertex, selected using finiteness. Ties may be resolved arbitrarily. -/
def next (seed : V) (s : Finset V) : V :=
  Classical.choose (Finset.univ.exists_max_image (nearestDistance s)
    ⟨seed, Finset.mem_univ seed⟩)

theorem le_next (seed : V) (s : Finset V) (x : V) :
    nearestDistance s x ≤ nearestDistance s (next seed s) := by
  classical
  exact (Classical.choose_spec (Finset.univ.exists_max_image (nearestDistance s)
    ⟨seed, Finset.mem_univ seed⟩)).2 x (Finset.mem_univ x)

/-- Prefix zero contains just the immortal initial vertex. -/
def greedyPrefix (seed : V) : ℕ → Finset V
  | 0 => {seed}
  | n + 1 => insert (next seed (greedyPrefix seed n)) (greedyPrefix seed n)

@[simp] theorem prefix_zero (seed : V) : greedyPrefix seed 0 = {seed} := rfl

@[simp] theorem prefix_succ (seed : V) (n : ℕ) :
    greedyPrefix seed (n + 1) = insert (next seed (greedyPrefix seed n)) (greedyPrefix seed n) := rfl

theorem prefix_step (seed : V) (n : ℕ) : greedyPrefix seed n ⊆ greedyPrefix seed (n + 1) := by
  classical
  exact Finset.subset_insert _ _

theorem prefix_mono (seed : V) : Monotone (greedyPrefix seed) :=
  monotone_nat_of_le_succ (prefix_step seed)

theorem seed_mem_prefix (seed : V) (n : ℕ) : seed ∈ greedyPrefix seed n :=
  prefix_mono seed (Nat.zero_le n) (by simp)

theorem prefix_nonempty (seed : V) (n : ℕ) : (greedyPrefix seed n).Nonempty :=
  ⟨seed, seed_mem_prefix seed n⟩

/-- The farthest-first sequence starts with `seed`. Its meaningful indices are
strictly below the cardinality of the space. -/
def vertex (seed : V) : ℕ → V
  | 0 => seed
  | n + 1 => next seed (greedyPrefix seed n)

@[simp] theorem vertex_zero (seed : V) : vertex seed 0 = seed := rfl

@[simp] theorem vertex_succ (seed : V) (n : ℕ) :
    vertex seed (n + 1) = next seed (greedyPrefix seed n) := rfl

theorem mem_prefix_iff (seed : V) (n : ℕ) (x : V) :
    x ∈ greedyPrefix seed n ↔ ∃ i ≤ n, vertex seed i = x := by
  classical
  induction n with
  | zero => simp [eq_comm]
  | succ n ih =>
    rw [prefix_succ, Finset.mem_insert, ih]
    constructor
    · rintro (h | ⟨i, hi, rfl⟩)
      · exact ⟨n + 1, le_rfl, h.symm⟩
      · exact ⟨i, by omega, rfl⟩
    · rintro ⟨i, hi, heq⟩
      by_cases hin : i ≤ n
      · exact Or.inr ⟨i, hin, heq⟩
      · have hindex : i = n + 1 := by omega
        exact Or.inl (by simpa [hindex] using heq.symm)

/-- The next insertion radius is finite; the initial vertex has no such radius. -/
def radius (seed : V) (n : ℕ) : ℝ :=
  nearestDistance (greedyPrefix seed n) (next seed (greedyPrefix seed n))

theorem radius_nonneg (seed : V) (n : ℕ) : 0 ≤ radius seed n :=
  nearestDistance_nonneg _ _

theorem covering (seed : V) (n : ℕ) (x : V) :
    ∃ y ∈ greedyPrefix seed n, dist x y ≤ radius seed n := by
  obtain ⟨y, hy, heq⟩ := exists_nearest (prefix_nonempty seed n) x
  exact ⟨y, hy, heq.trans_le (le_next seed _ x)⟩

theorem next_not_mem (seed : V) {n : ℕ} (h : greedyPrefix seed n ≠ Finset.univ) :
    next seed (greedyPrefix seed n) ∉ greedyPrefix seed n := by
  classical
  obtain ⟨x, hx⟩ : ∃ x, x ∉ greedyPrefix seed n := by
    by_contra! hall
    exact h (Finset.eq_univ_of_forall hall)
  have hpos := (nearestDistance_pos (prefix_nonempty seed n) hx).trans_le
    (le_next seed (greedyPrefix seed n) x)
  intro hn
  rw [nearestDistance_of_mem hn] at hpos
  exact (lt_irrefl 0) hpos

/-- Insertion radii decrease, including the terminal zero radii after exhaustion. -/
theorem radius_antitone (seed : V) : Antitone (radius seed) := by
  apply antitone_nat_of_succ_le
  intro n
  exact (nearestDistance_antitone (prefix_nonempty seed n) (prefix_step seed n) _).trans
    (le_next seed _ _)

/-- Every greedyPrefix has the expected cardinality until all vertices have been inserted. -/
theorem card_prefix (seed : V) (n : ℕ) :
    (greedyPrefix seed n).card = min (n + 1) (Fintype.card V) := by
  classical
  have hcard : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨seed⟩
  induction n with
  | zero => simp; omega
  | succ n ih =>
    by_cases h : greedyPrefix seed n = Finset.univ
    · have hle : Fintype.card V ≤ n + 1 := by
        rw [h, Finset.card_univ] at ih
        omega
      simp [prefix_succ, h]
      omega
    · have hlt : (greedyPrefix seed n).card < Fintype.card V := by
        exact Finset.card_lt_card (Finset.ssubset_univ_iff.mpr h)
      rw [prefix_succ, Finset.card_insert_of_notMem (next_not_mem seed h), ih]
      omega

/-- Finiteness proves completion; no net structure is assumed as input. -/
theorem prefix_eq_univ (seed : V) {n : ℕ} (hn : Fintype.card V ≤ n + 1) :
    greedyPrefix seed n = Finset.univ := by
  classical
  apply (Finset.card_eq_iff_eq_univ _).mp
  rw [card_prefix]
  omega

/-- The constructed finite farthest-first sequence enumerates every vertex exactly once. -/
theorem vertex_bijective (seed : V) :
    Function.Bijective (fun i : Fin (Fintype.card V) => vertex seed i.val) := by
  classical
  apply (Fintype.bijective_iff_surjective_and_card _).mpr
  refine ⟨?_, by simp⟩
  intro x
  have hcard : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨seed⟩
  have hx : x ∈ greedyPrefix seed (Fintype.card V - 1) := by
    rw [prefix_eq_univ seed (by omega)]
    exact Finset.mem_univ x
  obtain ⟨i, hi, hix⟩ := (mem_prefix_iff seed _ x).mp hx
  exact ⟨⟨i, by omega⟩, hix⟩

/-- A greedy permutation obtained solely from the finite metric space and its initial vertex. -/
def enumeration (seed : V) : Fin (Fintype.card V) ≃ V :=
  Equiv.ofBijective _ (vertex_bijective seed)

@[simp] theorem enumeration_apply (seed : V) (i : Fin (Fintype.card V)) :
    enumeration seed i = vertex seed i.val := rfl

/-- All distinct vertices of a greedyPrefix are separated by the next insertion radius. -/
theorem separation (seed : V) (n : ℕ) {x y : V}
    (hx : x ∈ greedyPrefix seed n) (hy : y ∈ greedyPrefix seed n) (hne : x ≠ y) :
    radius seed n ≤ dist x y := by
  classical
  induction n with
  | zero => simp only [prefix_zero, Finset.mem_singleton] at hx hy; exact (hne (hx.trans hy.symm)).elim
  | succ n ih =>
    simp only [prefix_succ, Finset.mem_insert] at hx hy
    have hrad := radius_antitone seed (Nat.le_succ n)
    rcases hx with rfl | hx <;> rcases hy with rfl | hy
    · exact (hne rfl).elim
    · exact hrad.trans (nearestDistance_le hy)
    · rw [dist_comm]
      exact hrad.trans (nearestDistance_le hx)
    · exact hrad.trans (ih hx hy)

/-- The radius of the last inserted vertex separates the enlarged greedyPrefix. -/
theorem separation_succ (seed : V) (n : ℕ) {x y : V}
    (hx : x ∈ greedyPrefix seed (n + 1)) (hy : y ∈ greedyPrefix seed (n + 1)) (hne : x ≠ y) :
    radius seed n ≤ dist x y := by
  classical
  simp only [prefix_succ, Finset.mem_insert] at hx hy
  rcases hx with rfl | hx <;> rcases hy with rfl | hy
  · exact (hne rfl).elim
  · exact nearestDistance_le hy
  · rw [dist_comm]; exact nearestDistance_le hx
  · exact separation seed n hx hy hne

@[simp] theorem radius_eq_zero_of_full (seed : V) {n : ℕ}
    (hn : greedyPrefix seed n = Finset.univ) : radius seed n = 0 := by
  classical
  unfold radius
  exact nearestDistance_of_mem (hn ▸ Finset.mem_univ _)

/-- A finite threshold greedyPrefix exists even at threshold zero. -/
theorem exists_radius_le (seed : V) {δ : ℝ} (hδ : 0 ≤ δ) :
    ∃ n, radius seed n ≤ δ := by
  refine ⟨Fintype.card V, ?_⟩
  rw [radius_eq_zero_of_full seed (prefix_eq_univ seed (by omega))]
  exact hδ

/-- Stop immediately before the next insertion would have radius at most `δ`. -/
def cutoff (seed : V) (δ : ℝ) (hδ : 0 ≤ δ) : ℕ :=
  Nat.find (exists_radius_le seed hδ)

theorem radius_cutoff_le (seed : V) (δ : ℝ) (hδ : 0 ≤ δ) :
    radius seed (cutoff seed δ hδ) ≤ δ :=
  Nat.find_spec (exists_radius_le seed hδ)

theorem lt_radius_before_cutoff (seed : V) (δ : ℝ) (hδ : 0 ≤ δ) {n : ℕ}
    (hn : n < cutoff seed δ hδ) : δ < radius seed n :=
  lt_of_not_ge (Nat.find_min (exists_radius_le seed hδ) hn)

/-- The threshold net has closed covering radius `δ` and strict separation `δ`.
The strict inequality handles simultaneous deletion times without choosing a tie order. -/
theorem threshold_net (seed : V) (δ : ℝ) (hδ : 0 ≤ δ) :
    (∀ x, ∃ y ∈ greedyPrefix seed (cutoff seed δ hδ), dist x y ≤ δ) ∧
    (∀ x ∈ greedyPrefix seed (cutoff seed δ hδ),
      ∀ y ∈ greedyPrefix seed (cutoff seed δ hδ), x ≠ y → δ < dist x y) := by
  constructor
  · intro x
    obtain ⟨y, hy, hxy⟩ := covering seed (cutoff seed δ hδ) x
    exact ⟨y, hy, hxy.trans (radius_cutoff_le seed δ hδ)⟩
  · intro x hx y hy hne
    generalize hk : cutoff seed δ hδ = k at hx hy
    cases k with
    | zero =>
      simp only [prefix_zero, Finset.mem_singleton] at hx hy
      exact (hne (hx.trans hy.symm)).elim
    | succ n =>
      exact (lt_radius_before_cutoff seed δ hδ (by omega)).trans_le
        (separation_succ seed n hx hy hne)

/-- The first index at which a vertex occurs. This is zero exactly for `seed`. -/
def insertionIndex (seed x : V) : ℕ :=
  Nat.find (show ∃ n, x ∈ greedyPrefix seed n from
    ⟨Fintype.card V, by rw [prefix_eq_univ seed (by omega)]; exact Finset.mem_univ x⟩)

theorem mem_insertionIndex (seed x : V) : x ∈ greedyPrefix seed (insertionIndex seed x) :=
  by
    unfold insertionIndex
    exact Nat.find_spec (p := fun n => x ∈ greedyPrefix seed n) _

theorem not_mem_before_insertionIndex (seed x : V) {n : ℕ}
    (hn : n < insertionIndex seed x) : x ∉ greedyPrefix seed n :=
  Nat.find_min _ hn

@[simp] theorem insertionIndex_seed (seed : V) : insertionIndex seed seed = 0 := by
  unfold insertionIndex
  exact (Nat.find_eq_zero _).mpr (by simp)

/-- The insertion radius of the first vertex is `none`, interpreted as infinity.
All other vertices receive their actual positive finite insertion radius. -/
def insertionRadius (seed x : V) : Option ℝ :=
  if insertionIndex seed x = 0 then none
  else some (radius seed (insertionIndex seed x - 1))

@[simp] theorem insertionRadius_seed (seed : V) : insertionRadius seed seed = none := by
  simp [insertionRadius]

theorem insertionIndex_eq_zero_iff (seed x : V) : insertionIndex seed x = 0 ↔ x = seed := by
  constructor
  · intro h
    have hx := mem_insertionIndex seed x
    simpa [h] using hx
  · intro h; subst x; exact insertionIndex_seed seed

/-- Every point kept by the threshold net is either the initial vertex or was inserted
at radius strictly greater than the threshold. -/
theorem mem_threshold_iff (seed x : V) (δ : ℝ) (hδ : 0 ≤ δ) :
    x ∈ greedyPrefix seed (cutoff seed δ hδ) ↔
      x = seed ∨ δ < radius seed (insertionIndex seed x - 1) := by
  constructor
  · intro hx
    by_cases hxs : x = seed
    · exact Or.inl hxs
    · right
      have hindex : 0 < insertionIndex seed x := by
        have := (insertionIndex_eq_zero_iff seed x).not.mpr hxs
        omega
      have hle : insertionIndex seed x ≤ cutoff seed δ hδ := by
        by_contra! hn
        exact not_mem_before_insertionIndex seed x hn hx
      exact lt_radius_before_cutoff seed δ hδ (by omega)
  · rintro (hxs | hrad)
    · subst x; exact seed_mem_prefix seed _
    · by_cases hi : insertionIndex seed x ≤ cutoff seed δ hδ
      · exact prefix_mono seed hi (mem_insertionIndex seed x)
      · have hle : cutoff seed δ hδ ≤ insertionIndex seed x - 1 := by omega
        have hmono := radius_antitone seed hle
        have hcut := radius_cutoff_le seed δ hδ
        linarith

/-- The first occurrence of a vertex is its actual greedy enumeration entry. -/
theorem vertex_insertionIndex (seed x : V) : vertex seed (insertionIndex seed x) = x := by
  by_cases hx : x = seed
  · subst x; simp
  · have hi : 0 < insertionIndex seed x := by
      have := (insertionIndex_eq_zero_iff seed x).not.mpr hx
      omega
    have hnot := not_mem_before_insertionIndex seed x
      (show insertionIndex seed x - 1 < insertionIndex seed x by omega)
    have hmem := mem_insertionIndex seed x
    have heq : insertionIndex seed x = (insertionIndex seed x - 1) + 1 := by omega
    rw [heq, prefix_succ, Finset.mem_insert] at hmem
    rw [heq, vertex_succ]
    exact (hmem.resolve_right hnot).symm

theorem insertionIndex_injective (seed : V) : Function.Injective (insertionIndex seed) := by
  intro x y hxy
  rw [← vertex_insertionIndex seed x, ← vertex_insertionIndex seed y, hxy]

/-- Noninitial vertices have strictly positive insertion radii. -/
theorem insertionRadius_pos (seed x : V) (hxs : x ≠ seed) :
    0 < radius seed (insertionIndex seed x - 1) := by
  have hi : 0 < insertionIndex seed x := by
    have := (insertionIndex_eq_zero_iff seed x).not.mpr hxs
    omega
  have hnot := not_mem_before_insertionIndex seed x (show insertionIndex seed x - 1 <
    insertionIndex seed x by omega)
  have hx := mem_insertionIndex seed x
  have heq : insertionIndex seed x = (insertionIndex seed x - 1) + 1 := by omega
  rw [heq, prefix_succ, Finset.mem_insert] at hx
  have hxnext : x = next seed (greedyPrefix seed (insertionIndex seed x - 1)) :=
    hx.resolve_right hnot
  unfold radius
  rw [← hxnext]
  exact nearestDistance_pos (prefix_nonempty seed _) hnot

/-- Choose a point of the threshold net within its proved covering radius. -/
def netPoint (seed : V) (δ : ℝ) (hδ : 0 ≤ δ) (x : V) : V :=
  Classical.choose ((threshold_net seed δ hδ).1 x)

theorem netPoint_mem (seed : V) (δ : ℝ) (hδ : 0 ≤ δ) (x : V) :
    netPoint seed δ hδ x ∈ greedyPrefix seed (cutoff seed δ hδ) :=
  (Classical.choose_spec ((threshold_net seed δ hδ).1 x)).1

theorem dist_netPoint_le (seed : V) (δ : ℝ) (hδ : 0 ≤ δ) (x : V) :
    dist x (netPoint seed δ hδ x) ≤ δ :=
  (Classical.choose_spec ((threshold_net seed δ hδ).1 x)).2

end

end TDA.Filtration.SparseRips.GreedyNet
