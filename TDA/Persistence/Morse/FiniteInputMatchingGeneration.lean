import TDA.Persistence.Morse.FiniteInputMatching

/-!
# Generating certified matchings on finite inputs

For a finite integer-graded input `xs : FiniteInput.Input`, `generate xs` is a
`CertifiedMatching xs` built by one deterministic greedy pass. The pass runs over
`candidates xs`, the same-grade cover pairs of positions in lexicographic (lower, upper) order.
It starts from the empty matching `emptyCertified xs` and, at each candidate `p`, calls
`certify?` on the extended list `c.pairs ++ [p]` with the rank `candidateRank xs (c.pairs ++ [p])`.
If the checker accepts, the extended certificate becomes the new state; otherwise the state is
kept (`greedyStep`).

Since the state is a `CertifiedMatching` at every step, `generate` is total and needs no validity
hypothesis. Totality is not meaning: on an invalid input (`¬ Valid xs`) the result is a list-level
object only. The guarded entry point is `generate?`, which is `none` exactly when `¬ Valid xs`
(`generate?_eq_none_iff`) and `some (generate xs)` otherwise (`generate?_eq_some_iff`).
Evaluated, with all grades `0` and positions counted from `0`: the empty face listed
(`[(∅, 0), ({0}, 0)]`) gives the pair `(0, 1)` and no critical position; a list that is not
downward closed (`[({0, 1}, 0)]`) gives no pair and reports the edge as critical of dimension `0`;
a repeated face (`[({0}, 0), ({0}, 0), ({0, 1}, 0)]`) gives the pair `(0, 2)`, pairing one copy
of the vertex with the edge, and leaves the other copy critical; a coface listed first
(`[({0, 1}, 0), ({0}, 0), ({1}, 0)]`) gives the pair `(1, 0)`, pairing the vertex with the edge
listed before it. These values are collected in `docs/math/discrete-morse-matchings.md`, section
"Behaviour on invalid input". `generate_check` restates its certificate through `check`, and, for a valid input,
`generate_isFilteredAcyclicMatching` gives a filtered acyclic matching of the represented complex.
`greedyStep_pairs` and `generate_pairs_sublist` show that the generated pairs are a sublist of the
candidates, in candidate order.

## Source and convention digest

This module is a library derivation over `TDA.Persistence.Morse.FiniteInputMatching`, attributed
to no numbered result of Mischaikow and Nanda (register card `MN13` in `docs/math/references.md`).
Their `MorseReduce` (§5.1) is a different, coreduction-based algorithm and is background only.

`candidateRank` is not trusted: every rank it returns is re-checked by `certify?`. It is not
claimed to find a rank whenever the extended list is acyclic, so a rejected candidate is not
proved to reuse a face or close a cycle. No maximality, optimality, invariance under reordering
the input or runtime bound is stated.
-/

set_option autoImplicit false

namespace TDA.Persistence.Morse.MatchingInput

open TDA.Simplicial TDA.Filtration TDA.Persistence.Reduction FiniteInput

/-- Same-grade cover pairs, lexicographic in (lower, upper) position. -/
def candidates (xs : Input) : Pairs xs :=
  (List.finRange xs.length).flatMap fun i =>
    ((List.finRange xs.length).filter fun j =>
      decide (IsCover xs i j ∧ (xs.get i).2 = (xs.get j).2)).map fun j => (i, j)

/-- The candidates are exactly the same-grade cover pairs. -/
theorem mem_candidates_iff (xs : Input) (p : Fin xs.length × Fin xs.length) :
    p ∈ candidates xs ↔ IsCover xs p.1 p.2 ∧ (xs.get p.1).2 = (xs.get p.2).2 := by
  obtain ⟨i, j⟩ := p
  simp [candidates]

/-- No candidate is listed twice. -/
theorem candidates_nodup (xs : Input) : (candidates xs).Nodup := by
  refine List.nodup_flatMap.mpr ⟨fun i _ => ?_, ?_⟩
  · exact ((List.nodup_finRange _).filter _).map fun a b h => by simpa using h
  · refine (List.nodup_finRange _).pairwise_of_forall_ne fun a _ b _ hab => ?_
    intro p hp hq
    simp only [List.mem_map, List.mem_filter] at hp hq
    obtain ⟨_, _, rfl⟩ := hp
    obtain ⟨_, _, h⟩ := hq
    exact hab (congrArg Prod.fst h).symm

/-- A bound strictly above every face size of the input. -/
private def sizeBound (xs : Input) : ℕ := (xs.map fun e => e.1.card).sum + 1

/-- The empty matching, certified by the rank `N - #face` for a constant `N` above every face
size, which decreases with the face size. -/
def emptyCertified (xs : Input) : CertifiedMatching xs where
  pairs := []
  rank i := sizeBound xs - (xs.get i).1.card
  isMatching := by simp [IsMatching, endpoints]
  isTopologicalRank := by
    intro u v huv
    have hu : (xs.get u).1.card ≤ (xs.map fun e => e.1.card).sum :=
      List.le_sum_of_mem (List.mem_map.mpr ⟨xs.get u, List.get_mem _ _, rfl⟩)
    rcases huv with ⟨hc, -⟩ | h
    · have := hc.2
      simp only [sizeBound]
      omega
    · simp at h

/-- The empty certificate has no pairs. -/
theorem emptyCertified_pairs (xs : Input) : (emptyCertified xs).pairs = [] := rfl

/-- All cover pairs of positions, lexicographic in (lower, upper) position. -/
private def coverPairs (xs : Input) : Pairs xs :=
  (List.finRange xs.length).flatMap fun i =>
    ((List.finRange xs.length).filter fun j => decide (IsCover xs i j)).map fun j => (i, j)

/-- The rank tried for a pair list. Every cover pair gives an arrow, face to coface if it is
listed and coface to face otherwise; for a list of cover pairs these are the arrows of its
list-level diagram. A position gets the length of a longest chain of at most `xs.length`
consecutive arrows ending there, computed by `xs.length` relaxation rounds on a memoized list.
`greedyStep` re-checks this rank with `certify?`. -/
def candidateRank (xs : Input) (pairs : Pairs xs) : Fin xs.length → ℕ :=
  let edges : List (Fin xs.length × Fin xs.length) :=
    (coverPairs xs).map fun p => if p ∈ pairs then p else (p.2, p.1)
  let relax (r : List ℕ) : List ℕ :=
    (List.finRange xs.length).map fun v =>
      edges.foldl (fun acc e => if e.2 = v then max acc (r.getD e.1 0 + 1) else acc) 0
  let r := (relax)^[xs.length] (List.replicate xs.length 0)
  fun i => r.getD i 0

/-- Accept `p` exactly when `certify?` accepts the extended list with the candidate rank;
otherwise keep the current certificate. -/
def greedyStep (xs : Input) (c : CertifiedMatching xs) (p : Fin xs.length × Fin xs.length) :
    CertifiedMatching xs :=
  (certify? xs (c.pairs ++ [p]) (candidateRank xs (c.pairs ++ [p]))).getD c

/-- The generated certified matching: the greedy pass over `candidates xs`, starting from
`emptyCertified xs`. Total; meaningful only under `Valid xs`; use `generate?`. -/
def generate (xs : Input) : CertifiedMatching xs :=
  (candidates xs).foldl (greedyStep xs) (emptyCertified xs)

/-- A step appends the candidate or leaves the pairs unchanged. -/
theorem greedyStep_pairs (xs : Input) (c : CertifiedMatching xs)
    (p : Fin xs.length × Fin xs.length) :
    (greedyStep xs c p).pairs = c.pairs ++ [p] ∨ (greedyStep xs c p).pairs = c.pairs := by
  unfold greedyStep
  cases hc : certify? xs (c.pairs ++ [p]) (candidateRank xs (c.pairs ++ [p])) with
  | none => exact Or.inr rfl
  | some c' => exact Or.inl (certify?_eq_some hc).1

/-- The generated pairs are a sublist of the candidates, in candidate order. -/
theorem generate_pairs_sublist (xs : Input) : (generate xs).pairs.Sublist (candidates xs) := by
  have key : ∀ (l pre : Pairs xs) (c : CertifiedMatching xs), c.pairs.Sublist pre →
      (l.foldl (greedyStep xs) c).pairs.Sublist (pre ++ l) := by
    intro l
    induction l with
    | nil => intro pre c hc; simpa using hc
    | cons p l ih =>
      intro pre c hc
      rw [List.foldl_cons, show pre ++ p :: l = (pre ++ [p]) ++ l by simp]
      apply ih
      rcases greedyStep_pairs xs c p with h | h <;> rw [h]
      · exact hc.append (List.Sublist.refl _)
      · exact hc.trans (List.sublist_append_left _ _)
  simpa [generate] using
    key (candidates xs) [] (emptyCertified xs) (by simp [emptyCertified_pairs])

/-- The guarded generator: `some (generate xs)` on a valid input, and `none` otherwise. -/
def generate? (xs : Input) : Option (CertifiedMatching xs) :=
  if Valid xs then some (generate xs) else none

/-- The guarded generator returns `none` exactly when the input is not valid. -/
theorem generate?_eq_none_iff (xs : Input) : generate? xs = none ↔ ¬ Valid xs := by
  unfold generate?
  split_ifs with h <;> simp [h]

/-- The guarded generator returns `some c` exactly when the input is valid and `c` is
`generate xs`. -/
theorem generate?_eq_some_iff (xs : Input) (c : CertifiedMatching xs) :
    generate? xs = some c ↔ Valid xs ∧ c = generate xs := by
  unfold generate?
  split_ifs with h
  · simp [h, eq_comm]
  · simp [h]

/-- The checker accepts the generated pairs with the generated rank. -/
theorem generate_check (xs : Input) :
    check xs (generate xs).pairs (generate xs).rank = true :=
  (check_eq_true_iff _ _ _).mpr ⟨(generate xs).isMatching, (generate xs).isTopologicalRank⟩

/-- On a valid input, the generated pairs form a filtered acyclic matching. -/
theorem generate_isFilteredAcyclicMatching (xs : Input) (h : Valid xs) :
    IsFilteredAcyclicMatching (gradeFilter xs h) (toRel xs h (generate xs).pairs) :=
  (generate xs).isFilteredAcyclicMatching h

end TDA.Persistence.Morse.MatchingInput
