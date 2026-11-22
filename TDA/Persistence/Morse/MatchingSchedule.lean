import TDA.Persistence.Morse.IteratedCancellation
import TDA.Persistence.Morse.FiniteInputMatching
import TDA.Persistence.Morse.FilteredHomology

/-!
# The pivot schedule of a certified matching

For a finite integer-graded input `xs : FiniteInput.Input` and a `CertifiedMatching xs` `c`,
`c.schedule` lists the certified (lower, upper) position pairs sorted by the rank of the lower
face, by a stable insertion sort (`List.insertionSort`), so pairs of equal lower-face rank keep
their order in `c.pairs`. It is a permutation of `c.pairs` (`schedule_perm`) and is sorted by
non-decreasing lower-face rank (`schedule_pairwise_rank_le`).

Over `ZMod 2`, the entry `FiniteInput.boundary xs i j` is `1` exactly when position `i` is a
codimension-one face of position `j` with a nonempty lower face, and `0` otherwise
(`boundary_eq_coverIncidence`). So a nonzero entry is a cover (`isCover_of_boundary_ne_zero`),
and on a valid input every cover has coefficient `1` (`boundary_eq_one_of_isCover`).

If `boundary xs p.1 q.2 ≠ 0` for two distinct certified pairs `p` and `q`, then `(p.1, q.2)`
is an unmatched cover, so `MatchingInput.arrow` gives `q.1 → q.2 → p.1` and the certified rank
gives `c.rank q.1 < c.rank p.1` (`rank_lt_of_boundary_ne_zero`). Since the schedule is sorted by
non-decreasing lower-face rank, `p` never comes before `q`: on a valid input, `c.schedule` is a
pivot schedule for the boundary with the list grades (`isPivotSchedule_schedule`). Ties in the
rank are harmless, because the inequality above is strict.

Its critical generators are the certificate's critical positions (`mem_criticalSet_schedule`,
`card_critical_schedule`). `c.morseDifferential` is the reduced differential
`criticalDifferential (FiniteInput.boundary xs) c.schedule`; it takes no validity hypothesis and
is computable. On a valid input, `c.morseContraction h` is the filtered contraction
`FilteredContraction.ofSchedule` of the boundary complex onto it, and `c.morseHomologyIso h p` is
the induced isomorphism `FilteredContraction.sublevelHomologyIso` of grade-sublevel homology
persistence modules in degree `p`.

This module is a library derivation. It provides no simplicial bridge to `sublevelModule` and no
explicit gradient-path formula for the Morse differential.
-/

set_option autoImplicit false

namespace TDA.Persistence.Morse.MatchingInput

open TDA.Persistence.Reduction FiniteInput TDA.Persistence.Morse.Cancellation

/-! ## Boundary entries and covers -/

/-- The cover incidence of the listed faces over `ZMod 2`: `1` exactly when position `i` is a
codimension-one face of position `j` and the face at position `i` is nonempty. -/
def coverIncidence (xs : Input) : Matrix (Fin xs.length) (Fin xs.length) (ZMod 2) :=
  fun i j => if IsCover xs i j ∧ (xs.get i).1.Nonempty then 1 else 0

/-- The boundary entry of a face `s` in a face `t`, over `ZMod 2`. -/
private theorem boundary_entry (s t : Finset ℕ) :
    (if hc : t.card = s.card - 1 + 2 then
      ∑ a : Fin (s.card - 1 + 2),
        if t.erase (t.orderEmbOfFin hc a) = s then (-1 : ZMod 2) ^ (a : ℕ) else 0
    else 0) = if (s ⊆ t ∧ t.card = s.card + 1) ∧ s.Nonempty then 1 else 0 := by
  have hone : ∀ a : ℕ, (-1 : ZMod 2) ^ a = 1 := fun a => by
    rw [show (-1 : ZMod 2) = 1 from by decide, one_pow]
  by_cases hc : t.card = s.card - 1 + 2
  · simp only [hc, ↓reduceDIte, hone]
    by_cases hs : s ⊆ t ∧ s.Nonempty
    · have hcov : (s ⊆ t ∧ s.card - 1 + 2 = s.card + 1) ∧ s.Nonempty := by
        have := hs.2.card_pos
        exact ⟨⟨hs.1, by omega⟩, hs.2⟩
      simp only [hcov, and_self, ↓reduceIte]
      obtain ⟨hst, hne⟩ := hs
      have hcard : (t \ s).card = 1 := by
        rw [Finset.card_sdiff_of_subset hst]
        have := hne.card_pos
        omega
      obtain ⟨v, hv⟩ := Finset.card_eq_one.1 hcard
      have hmem : ∀ x, x ∈ t ∧ x ∉ s ↔ x = v := fun x => by
        rw [← Finset.mem_sdiff, hv, Finset.mem_singleton]
      obtain ⟨a₀, ha₀⟩ : v ∈ Set.range (t.orderEmbOfFin hc) := by
        rw [Finset.range_orderEmbOfFin]
        exact ((hmem v).2 rfl).1
      have hiff : ∀ a, t.erase (t.orderEmbOfFin hc a) = s ↔ a = a₀ := by
        intro a
        constructor
        · intro he
          apply (t.orderEmbOfFin hc).injective
          rw [ha₀]
          exact (hmem _).1 ⟨Finset.orderEmbOfFin_mem t hc a, fun h =>
            Finset.notMem_erase _ _ ((Finset.ext_iff.1 he _).2 h)⟩
        · rintro rfl
          rw [ha₀]
          ext x
          rw [Finset.mem_erase]
          constructor
          · rintro ⟨hx, hxt⟩
            by_contra hxs
            exact hx ((hmem x).1 ⟨hxt, hxs⟩)
          · intro hxs
            exact ⟨fun hx => ((hmem x).2 hx).2 hxs, hst hxs⟩
      simp only [hiff, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    · have hcov : ¬ ((s ⊆ t ∧ s.card - 1 + 2 = s.card + 1) ∧ s.Nonempty) :=
        fun h' => hs ⟨h'.1.1, h'.2⟩
      simp only [hcov, ↓reduceIte]
      apply Finset.sum_eq_zero
      intro a _
      have hne : t.erase (t.orderEmbOfFin hc a) ≠ s := by
        intro he
        apply hs
        refine ⟨he ▸ Finset.erase_subset _ _, ?_⟩
        rw [← Finset.card_pos, ← he,
          Finset.card_erase_of_mem (Finset.orderEmbOfFin_mem t hc a)]
        omega
      simp only [hne, ↓reduceIte]
  · have hcov : ¬ ((s ⊆ t ∧ t.card = s.card + 1) ∧ s.Nonempty) := fun h' => by
      have := h'.2.card_pos
      omega
    simp only [hc, ↓reduceDIte, hcov, ↓reduceIte]

/-- Over `ZMod 2`, the finite-input boundary is the cover incidence. -/
theorem boundary_eq_coverIncidence (xs : Input) : boundary xs = coverIncidence xs := by
  funext i j
  simp only [coverIncidence, IsCover]
  exact boundary_entry _ _

/-- A nonzero boundary entry is a cover. -/
theorem isCover_of_boundary_ne_zero {xs : Input} {i j : Fin xs.length}
    (h : boundary xs i j ≠ 0) : IsCover xs i j := by
  rw [boundary_eq_coverIncidence, coverIncidence] at h
  by_contra hc
  simp [hc] at h

/-- On a valid input, every cover has boundary coefficient `1`. -/
theorem boundary_eq_one_of_isCover {xs : Input} (h : Valid xs) {i j : Fin xs.length}
    (hc : IsCover xs i j) : boundary xs i j = 1 := by
  rw [boundary_eq_coverIncidence, coverIncidence,
    ite_eq_left_of_eq_true _ _ (eq_true ⟨hc, h.1 i⟩)]

/-- On a valid input, the nonzero boundary entries are exactly the covers. -/
theorem boundary_ne_zero_iff {xs : Input} (h : Valid xs) {i j : Fin xs.length} :
    boundary xs i j ≠ 0 ↔ IsCover xs i j :=
  ⟨isCover_of_boundary_ne_zero, fun hc => by
    rw [boundary_eq_one_of_isCover h hc]
    exact one_ne_zero⟩

namespace CertifiedMatching

variable {xs : Input}

/-! ## The schedule -/

/-- The certified pairs sorted by non-decreasing rank of the lower face, by a stable insertion
sort: pairs of equal lower-face rank keep their order in `c.pairs`. -/
def schedule (c : CertifiedMatching xs) : Pairs xs :=
  c.pairs.insertionSort fun p q => c.rank p.1 ≤ c.rank q.1

/-- The schedule is a permutation of the certified pairs. -/
theorem schedule_perm (c : CertifiedMatching xs) : c.schedule.Perm c.pairs :=
  List.perm_insertionSort _ _

/-- The schedule is sorted by non-decreasing rank of the lower face. -/
theorem schedule_pairwise_rank_le (c : CertifiedMatching xs) :
    c.schedule.Pairwise fun p q => c.rank p.1 ≤ c.rank q.1 := by
  have : Std.Total fun p q : Fin xs.length × Fin xs.length => c.rank p.1 ≤ c.rank q.1 :=
    ⟨fun _ _ => le_total _ _⟩
  have : IsTrans _ fun p q : Fin xs.length × Fin xs.length => c.rank p.1 ≤ c.rank q.1 :=
    ⟨fun _ _ _ => le_trans⟩
  exact List.pairwise_insertionSort _ _

/-- The endpoints of the schedule are those of the certified pairs, reordered. -/
theorem scheduleEndpoints_perm (c : CertifiedMatching xs) :
    (scheduleEndpoints c.schedule).Perm (endpoints c.pairs) :=
  c.schedule_perm.flatMap_right _

/-- Two certified pairs sharing an endpoint are equal. -/
private theorem eq_of_mem_endpoint (c : CertifiedMatching xs)
    {p q : Fin xs.length × Fin xs.length} (hp : p ∈ c.pairs) (hq : q ∈ c.pairs)
    {x : Fin xs.length} (hx : x = p.1 ∨ x = p.2) (hy : x = q.1 ∨ x = q.2) : p = q := by
  by_contra hne
  have : Std.Symm (Function.onFun List.Disjoint
      fun p : Fin xs.length × Fin xs.length => [p.1, p.2]) :=
    ⟨fun _ _ hab => hab.symm⟩
  have hd := (List.nodup_flatMap.mp c.isMatching.1).2.forall hp hq hne
  refine hd (a := x) ?_ ?_
  · rcases hx with rfl | rfl <;> simp
  · rcases hy with rfl | rfl <;> simp

/-- **The arrow chain.** If the lower face of a certified pair `p` has a nonzero coefficient
in the boundary of the upper face of another certified pair `q`, then the arrows
`q.1 → q.2 → p.1` give `c.rank q.1 < c.rank p.1`. -/
theorem rank_lt_of_boundary_ne_zero (c : CertifiedMatching xs)
    {p q : Fin xs.length × Fin xs.length} (hp : p ∈ c.pairs) (hq : q ∈ c.pairs) (hpq : p ≠ q)
    (h : boundary xs p.1 q.2 ≠ 0) : c.rank q.1 < c.rank p.1 := by
  have hcov := isCover_of_boundary_ne_zero h
  have hnot : (p.1, q.2) ∉ c.pairs := by
    intro hm
    have h1 := c.eq_of_mem_endpoint hm hp (x := p.1) (Or.inl rfl) (Or.inl rfl)
    have h2 := c.eq_of_mem_endpoint hm hq (x := q.2) (Or.inr rfl) (Or.inr rfl)
    exact hpq (h1.symm.trans h2)
  have a1 : arrow xs c.pairs q.1 q.2 := Or.inr (by simpa using hq)
  have a2 : arrow xs c.pairs q.2 p.1 := Or.inl ⟨hcov, hnot⟩
  exact (c.isTopologicalRank _ _ a1).trans (c.isTopologicalRank _ _ a2)

/-- **The certified schedule is a pivot schedule.** On a valid input, the certified pairs
sorted by the rank of the lower face satisfy the pivot invariant for the boundary with the list
grades. -/
theorem isPivotSchedule_schedule (c : CertifiedMatching xs) (h : Valid xs) :
    IsPivotSchedule (fun i => (xs.get i).2) (boundary xs) c.schedule := by
  have hN : (scheduleEndpoints c.schedule).Nodup :=
    c.scheduleEndpoints_perm.symm.nodup c.isMatching.1
  have hmem : ∀ p ∈ c.schedule, p ∈ c.pairs := fun p hp => c.schedule_perm.subset hp
  refine ⟨hN, fun p hp => ⟨boundary_eq_one_of_isCover h (c.isMatching.2.1 p (hmem p hp)),
    c.isMatching.2.2 p (hmem p hp)⟩, ?_⟩
  have hpn : c.pairs.Nodup := (List.nodup_flatMap.mp c.isMatching.1).2.imp fun {p _} hd he => by
    subst he
    exact hd (a := p.1) (by simp) (by simp)
  have hnd : c.schedule.Nodup := c.schedule_perm.symm.nodup hpn
  refine ((c.schedule_pairwise_rank_le.and hnd).imp_of_mem
    fun {p q} hp hq hpq => ?_)
  by_contra hne
  have := c.rank_lt_of_boundary_ne_zero (hmem p hp) (hmem q hq) hpq.2 hne
  omega

/-! ## Critical generators -/

/-- The critical generators of the schedule are the critical positions of the certificate. -/
theorem mem_criticalSet_schedule (c : CertifiedMatching xs) {i : Fin xs.length} :
    i ∈ criticalSet c.schedule ↔ i ∈ c.critical := by
  rw [mem_criticalSet, c.scheduleEndpoints_perm.mem_iff, mem_critical_iff]
  simp only [endpoints, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false, not_exists,
    not_and, Prod.forall]
  constructor
  · intro hc j
    exact ⟨fun hj => hc i j hj (Or.inl rfl), fun hj => hc j i hj (Or.inr rfl)⟩
  · rintro hc a b hab (rfl | rfl)
    · exact (hc b).1 hab
    · exact (hc a).2 hab

/-- There are as many critical generators of the schedule as critical positions. -/
theorem card_critical_schedule (c : CertifiedMatching xs) :
    Fintype.card (Critical c.schedule) = c.critical.length := by
  have hN : (scheduleEndpoints c.schedule).Nodup :=
    c.scheduleEndpoints_perm.symm.nodup c.isMatching.1
  rw [card_critical hN, Fintype.card_fin, c.schedule_perm.length_eq]
  have := c.critical_length_add
  omega

/-! ## The Morse complex of a certificate -/

/-- The Morse differential of the certificate: the reduced boundary on the critical generators
of its schedule. It takes no validity hypothesis and is computable. -/
def morseDifferential (c : CertifiedMatching xs) :
    Matrix (Critical c.schedule) (Critical c.schedule) (ZMod 2) :=
  criticalDifferential (boundary xs) c.schedule

/-- On a valid input, the filtered contraction of the boundary complex with its degrees and
list grades onto the Morse complex of the certificate. -/
def morseContraction (c : CertifiedMatching xs) (h : Valid xs) :
    FilteredContraction (degree xs) (fun i => (xs.get i).2) (boundary xs)
      (degree xs ∘ Subtype.val) ((fun i => (xs.get i).2) ∘ Subtype.val) c.morseDifferential :=
  FilteredContraction.ofSchedule (isFilteredDifferential_boundary xs h)
    (c.isPivotSchedule_schedule h)

/-- On a valid input, the Morse differential is a filtered differential for the inherited
degrees and list grades. -/
theorem isFilteredDifferential_morseDifferential (c : CertifiedMatching xs) (h : Valid xs) :
    IsFilteredDifferential (degree xs ∘ Subtype.val) ((fun i => (xs.get i).2) ∘ Subtype.val)
      c.morseDifferential :=
  (c.morseContraction h).isFilteredDifferential_target (isFilteredDifferential_boundary xs h)

/-- On a valid input, the Morse contraction induces, in every degree `p`, an isomorphism of
the grade-sublevel homology persistence modules of the boundary complex and of the Morse
complex. -/
noncomputable def morseHomologyIso (c : CertifiedMatching xs) (h : Valid xs) (p : ℕ) :
    sublevelHomologyPModule (degree xs) (fun i => (xs.get i).2) (boundary xs) p ≅
      sublevelHomologyPModule (degree xs ∘ Subtype.val) ((fun i => (xs.get i).2) ∘ Subtype.val)
        c.morseDifferential p :=
  (c.morseContraction h).sublevelHomologyIso p

end CertifiedMatching

end TDA.Persistence.Morse.MatchingInput
