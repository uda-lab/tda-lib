import TDA.Persistence.Morse.AcyclicMatching
import TDA.Persistence.Reduction.FiniteInput
import TDA.Persistence.Reduction.FiniteInputVertexMap

/-!
# Checking acyclic matchings on finite inputs

A finite integer-graded input `xs : FiniteInput.Input` lists its faces by position
`Fin xs.length`. A matching is supplied as a list of ordered (lower, upper) position pairs,
together with a rank certificate `rank : Fin xs.length → ℕ`. `check` decides whether the
pairs form an equal-grade matching (`IsMatching`) and whether the rank increases along every
arrow of the modified Hasse diagram on positions (`IsTopologicalRank`); `check_eq_true_iff`
states exactly this.

For a valid input, `toRel` transports the pairs to a relation on the actual faces of
`complex xs h` through `listEquiv xs h`. The transfer theorems identify the list-level
predicates with the semantic ones of `TDA.Persistence.Morse.AcyclicMatching`.
`exists_check_iff` and `exists_check_iff_isFilteredAcyclicMatching` show that some rank is
accepted exactly for a duplicate-free list whose relation is an equal-grade acyclic matching,
equivalently a filtered acyclic matching for the sublevels of `gradeFilter xs h`.

`CertifiedMatching` bundles accepted pairs with their rank and exposes the unmatched
(critical) positions in increasing order, with their dimension and original grade.

`check`, `IsMatching`, `IsTopologicalRank` and `criticalReport` work on the list alone and take
no validity hypothesis; their meaning for faces is stated only under `Valid xs`. On an invalid
input they return ordinary-looking values with no meaning for a complex. The guarded entry
points are `check?` and `criticalReport?`, which return `none` exactly when `¬ Valid xs`
(`check?_eq_none_iff`, `criticalReport?_eq_none_iff`) and otherwise the raw value
(`check?_eq_some_iff`, `criticalReport?_eq_some_iff`); `generate?` and `morseOccurrences?`
are their counterparts for generation and for the Morse run. For example, with `xs = [(∅, 0), ({0}, 0)]`, which lists the empty face, `check`
accepts the pair `(0, 1)` with a suitable rank and `criticalReport` lists no critical position, the empty face
having dimension `0` by subtraction in `ℕ`. See `docs/math/discrete-morse-matchings.md`,
section "Behaviour on invalid input".

## Source and convention digest

This module is a library derivation over the semantic layer, whose source is Mischaikow and
Nanda, *Morse Theory for Filtrations and Efficient Computation of Persistent Homology*,
Discrete Comput. Geom. 50 (2013), DOI 10.1007/s00454-013-9529-6 (register card `MN13` in
`docs/math/references.md`). No numbered result of the source is claimed here. Pairs are
ordered (lower, upper); a reversed pair is rejected, not normalised, and a repeated pair
counts as reuse of its faces. The arrow direction is the one of `Morse.arrow`: an unmatched
cover pair points from coface to face, a matched pair from face to coface. `check` does not
search for a rank, and no runtime bound is stated.
-/

set_option autoImplicit false

namespace TDA.Persistence.Morse.MatchingInput

open TDA.Simplicial TDA.Filtration TDA.Persistence.Reduction FiniteInput

/-- Ordered (lower, upper) pairs of list positions. -/
abbrev Pairs (xs : Input) := List (Fin xs.length × Fin xs.length)

/-- Position `i` is a codimension-one face of position `j`. -/
def IsCover (xs : Input) (i j : Fin xs.length) : Prop :=
  (xs.get i).1 ⊆ (xs.get j).1 ∧ (xs.get j).1.card = (xs.get i).1.card + 1

/-- Being a cover is decided by a finite subset test and a size comparison. -/
instance (xs : Input) (i j : Fin xs.length) : Decidable (IsCover xs i j) := by
  unfold IsCover
  infer_instance

/-- All `2·|pairs|` endpoints, in order. -/
def endpoints {xs : Input} (pairs : Pairs xs) : List (Fin xs.length) :=
  pairs.flatMap fun p => [p.1, p.2]

/-- Distinct endpoints, cover pairs in (lower, upper) order, equal grades. -/
def IsMatching (xs : Input) (pairs : Pairs xs) : Prop :=
  (endpoints pairs).Nodup ∧
  (∀ p ∈ pairs, IsCover xs p.1 p.2) ∧
  (∀ p ∈ pairs, (xs.get p.1).2 = (xs.get p.2).2)

/-- The list-level matching conditions are finite checks over the pair list. -/
instance (xs : Input) (pairs : Pairs xs) : Decidable (IsMatching xs pairs) := by
  unfold IsMatching
  infer_instance

/-- Unmatched cover arrows coface → face; matched pairs face → coface. -/
def arrow (xs : Input) (pairs : Pairs xs) (u v : Fin xs.length) : Prop :=
  (IsCover xs v u ∧ (v, u) ∉ pairs) ∨ (u, v) ∈ pairs

/-- An arrow between two positions is decided by a cover test and list membership. -/
instance (xs : Input) (pairs : Pairs xs) (u v : Fin xs.length) :
    Decidable (arrow xs pairs u v) := by
  unfold arrow
  infer_instance

/-- A rank strictly increasing along every arrow between positions. -/
def IsTopologicalRank (xs : Input) (pairs : Pairs xs) (rank : Fin xs.length → ℕ) :
    Prop :=
  ∀ u v : Fin xs.length, arrow xs pairs u v → rank u < rank v

/-- The rank condition quantifies over the finitely many pairs of positions. -/
instance (xs : Input) (pairs : Pairs xs) (rank : Fin xs.length → ℕ) :
    Decidable (IsTopologicalRank xs pairs rank) := by
  unfold IsTopologicalRank
  infer_instance

/-- The executable checker: the pairs form a list-level matching and `rank` is a
topological rank of the modified Hasse diagram on positions. Total; meaningful for faces only
under `Valid xs`; use `check?`. -/
def check (xs : Input) (pairs : Pairs xs) (rank : Fin xs.length → ℕ) : Bool :=
  decide (IsMatching xs pairs) && decide (IsTopologicalRank xs pairs rank)

/-- The checker accepts exactly list-level matchings with a topological rank. -/
theorem check_eq_true_iff (xs : Input) (pairs : Pairs xs) (rank : Fin xs.length → ℕ) :
    check xs pairs rank = true ↔ IsMatching xs pairs ∧ IsTopologicalRank xs pairs rank := by
  simp [check]

/-- The guarded checker: `check xs pairs rank` on a valid input, and `none` otherwise. -/
def check? (xs : Input) (pairs : Pairs xs) (rank : Fin xs.length → ℕ) : Option Bool :=
  if Valid xs then some (check xs pairs rank) else none

/-- The guarded checker returns `none` exactly when the input is not valid. -/
theorem check?_eq_none_iff (xs : Input) (pairs : Pairs xs) (rank : Fin xs.length → ℕ) :
    check? xs pairs rank = none ↔ ¬ Valid xs := by
  unfold check?
  split_ifs with h <;> simp [h]

/-- The guarded checker returns `some b` exactly when the input is valid and `check` returns `b`. -/
theorem check?_eq_some_iff (xs : Input) (pairs : Pairs xs) (rank : Fin xs.length → ℕ)
    (b : Bool) : check? xs pairs rank = some b ↔ Valid xs ∧ check xs pairs rank = b := by
  unfold check?
  split_ifs with h <;> simp [h]

/-- The semantic matching on the actual faces. -/
def toRel (xs : Input) (h : Valid xs) (pairs : Pairs xs) :
    TotalFace (complex xs h) → TotalFace (complex xs h) → Prop :=
  fun σ τ => ((listEquiv xs h).symm σ, (listEquiv xs h).symm τ) ∈ pairs

/-- On listed faces, the semantic relation is membership of the position pair. -/
theorem toRel_listFace (xs : Input) (h : Valid xs) (pairs : Pairs xs)
    (i j : Fin xs.length) :
    toRel xs h pairs (listFace xs h i) (listFace xs h j) ↔ (i, j) ∈ pairs := by
  simp [toRel]

/-- The list-level cover test is the cover relation of the listed faces. -/
theorem isCover_iff_covBy (xs : Input) (h : Valid xs) (i j : Fin xs.length) :
    IsCover xs i j ↔ (listFace xs h i).val ⋖ (listFace xs h j).val :=
  covBy_iff_subset_card.symm

/-- List-level arrows are the semantic arrows between the listed faces. -/
theorem arrow_iff (xs : Input) (h : Valid xs) (pairs : Pairs xs) (u v : Fin xs.length) :
    arrow xs pairs u v ↔
      Morse.arrow (toRel xs h pairs) (listFace xs h u) (listFace xs h v) := by
  simp only [arrow, Morse.arrow, toRel_listFace, isCover_iff_covBy xs h]

section Endpoints

variable {xs : Input} {pairs : Pairs xs}

private theorem fst_ne_snd_of_nodup (hN : (endpoints pairs).Nodup)
    {p : Fin xs.length × Fin xs.length} (hp : p ∈ pairs) : p.1 ≠ p.2 := by
  have := (List.nodup_flatMap.mp hN).1 p hp
  simpa using this

/-- With distinct endpoints, two pairs sharing an endpoint are equal. -/
private theorem eq_of_endpoint (hN : (endpoints pairs).Nodup)
    {p q : Fin xs.length × Fin xs.length} (hp : p ∈ pairs) (hq : q ∈ pairs)
    {x : Fin xs.length} (hx : x = p.1 ∨ x = p.2) (hy : x = q.1 ∨ x = q.2) : p = q := by
  by_contra hne
  have : Std.Symm (Function.onFun List.Disjoint
      fun p : Fin xs.length × Fin xs.length => [p.1, p.2]) :=
    ⟨fun _ _ hab => hab.symm⟩
  have hd := (List.nodup_flatMap.mp hN).2.forall hp hq hne
  refine hd (a := x) ?_ ?_
  · rcases hx with rfl | rfl <;> simp
  · rcases hy with rfl | rfl <;> simp

/-- Distinct endpoints from in-pair distinctness, no duplicate pair and disjoint pairs. -/
private theorem endpoints_nodup_of (hne : ∀ p ∈ pairs, p.1 ≠ p.2) (hN : pairs.Nodup)
    (hd : ∀ p ∈ pairs, ∀ q ∈ pairs, p ≠ q →
      p.1 ≠ q.1 ∧ p.1 ≠ q.2 ∧ p.2 ≠ q.1 ∧ p.2 ≠ q.2) :
    (endpoints pairs).Nodup := by
  refine List.nodup_flatMap.mpr ⟨fun p hp => by simpa using hne p hp, ?_⟩
  refine hN.pairwise_of_forall_ne fun p hp q hq hpq => ?_
  obtain ⟨h1, h2, h3, h4⟩ := hd p hp q hq hpq
  intro a ha hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hb
  rcases ha with rfl | rfl <;> rcases hb with h | h
  · exact h1 h
  · exact h2 h
  · exact h3 h
  · exact h4 h

private theorem mem_endpoints_iff_aux {x : Fin xs.length} :
    x ∈ endpoints pairs ↔ ∃ p ∈ pairs, x = p.1 ∨ x = p.2 := by
  simp [endpoints]

private theorem length_endpoints : (endpoints pairs).length = 2 * pairs.length := by
  induction pairs with
  | nil => rfl
  | cons p l ih =>
    simp only [endpoints, List.flatMap_cons, List.length_append, List.length_cons,
      List.length_nil] at ih ⊢
    omega

end Endpoints

/-- List-level matching = no duplicate pair + semantic matching + equal grades. -/
theorem isMatching_iff (xs : Input) (h : Valid xs) (pairs : Pairs xs) :
    IsMatching xs pairs ↔ pairs.Nodup ∧ Morse.IsMatching (toRel xs h pairs) ∧
      IsGradePreserving (gradeFilter xs h) (toRel xs h pairs) := by
  have hinj : ∀ i j : Fin xs.length, listFace xs h i = listFace xs h j → i = j :=
    fun i j hij => (listEquiv xs h).injective hij
  have hsurj : ∀ σ : TotalFace (complex xs h), ∃ i, listFace xs h i = σ :=
    fun σ => (listEquiv xs h).surjective σ
  constructor
  · rintro ⟨hN, hC, hG⟩
    refine ⟨?_, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · -- Distinct endpoints force distinct pairs.
      refine List.Pairwise.imp (R := Function.onFun List.Disjoint
        fun p : Fin xs.length × Fin xs.length => [p.1, p.2]) ?_ (List.nodup_flatMap.mp hN).2
      intro p q hpq heq
      subst heq
      exact hpq (a := p.1) (by simp) (by simp)
    · intro σ τ hστ
      obtain ⟨i, rfl⟩ := hsurj σ
      obtain ⟨j, rfl⟩ := hsurj τ
      exact (isCover_iff_covBy xs h i j).mp (hC _ ((toRel_listFace xs h pairs i j).mp hστ))
    · intro σ τ τ' h1 h2
      obtain ⟨i, rfl⟩ := hsurj σ
      obtain ⟨j, rfl⟩ := hsurj τ
      obtain ⟨j', rfl⟩ := hsurj τ'
      have := eq_of_endpoint hN ((toRel_listFace xs h pairs i j).mp h1)
        ((toRel_listFace xs h pairs i j').mp h2) (x := i) (Or.inl rfl) (Or.inl rfl)
      simp only [Prod.mk.injEq] at this
      rw [this.2]
    · intro σ σ' τ h1 h2
      obtain ⟨i, rfl⟩ := hsurj σ
      obtain ⟨i', rfl⟩ := hsurj σ'
      obtain ⟨j, rfl⟩ := hsurj τ
      have := eq_of_endpoint hN ((toRel_listFace xs h pairs i j).mp h1)
        ((toRel_listFace xs h pairs i' j).mp h2) (x := j) (Or.inr rfl) (Or.inr rfl)
      simp only [Prod.mk.injEq] at this
      rw [this.1]
    · intro σ τ ρ h1 h2
      obtain ⟨i, rfl⟩ := hsurj σ
      obtain ⟨j, rfl⟩ := hsurj τ
      obtain ⟨k, rfl⟩ := hsurj ρ
      have hp := (toRel_listFace xs h pairs i j).mp h1
      have hq := (toRel_listFace xs h pairs j k).mp h2
      have := eq_of_endpoint hN hp hq (x := j) (Or.inr rfl) (Or.inl rfl)
      simp only [Prod.mk.injEq] at this
      exact fst_ne_snd_of_nodup hN hp this.1
    · intro σ τ hστ
      obtain ⟨i, rfl⟩ := hsurj σ
      obtain ⟨j, rfl⟩ := hsurj τ
      rw [gradeFilter_listFace, gradeFilter_listFace]
      exact hG _ ((toRel_listFace xs h pairs i j).mp hστ)
  · rintro ⟨hN, hM, hG⟩
    have hC : ∀ p ∈ pairs, IsCover xs p.1 p.2 := fun p hp =>
      (isCover_iff_covBy xs h p.1 p.2).mpr (hM.covBy ((toRel_listFace xs h pairs _ _).mpr hp))
    have hrel : ∀ {i j : Fin xs.length}, (i, j) ∈ pairs →
        toRel xs h pairs (listFace xs h i) (listFace xs h j) :=
      fun hij => (toRel_listFace xs h pairs _ _).mpr hij
    refine ⟨endpoints_nodup_of ?_ hN ?_, hC, ?_⟩
    · intro p hp heq
      have := (hC p hp).2
      rw [heq] at this
      omega
    · rintro ⟨a, b⟩ hp ⟨c, d⟩ hq hpq
      refine ⟨?_, ?_, ?_, ?_⟩
      · rintro rfl
        exact hpq (by rw [hinj _ _ (hM.lower_unique (hrel hp) (hrel hq))])
      · rintro rfl
        exact hM.disjoint (hrel hq) (hrel hp)
      · rintro rfl
        exact hM.disjoint (hrel hp) (hrel hq)
      · rintro rfl
        exact hpq (by rw [hinj _ _ (hM.upper_unique (hrel hp) (hrel hq))])
    · intro p hp
      have := hG (hrel (i := p.1) (j := p.2) hp)
      rwa [gradeFilter_listFace, gradeFilter_listFace] at this

/-- The list-level rank condition is the semantic one, read through `listEquiv`. -/
theorem isTopologicalRank_iff (xs : Input) (h : Valid xs) (pairs : Pairs xs)
    (rank : Fin xs.length → ℕ) :
    IsTopologicalRank xs pairs rank ↔
      Morse.IsTopologicalRank (toRel xs h pairs) (rank ∘ (listEquiv xs h).symm) := by
  constructor
  · intro hr σ τ hστ
    obtain ⟨i, rfl⟩ := (listEquiv xs h).surjective σ
    obtain ⟨j, rfl⟩ := (listEquiv xs h).surjective τ
    simp only [listEquiv_apply, Function.comp_apply, listEquiv_symm_listFace] at hστ ⊢
    exact hr i j ((arrow_iff xs h pairs i j).mpr hστ)
  · intro hr u v huv
    have := hr _ _ ((arrow_iff xs h pairs u v).mp huv)
    simpa using this

/-- Some certificate is accepted exactly for duplicate-free equal-grade acyclic matchings. -/
theorem exists_check_iff (xs : Input) (h : Valid xs) (pairs : Pairs xs) :
    (∃ rank : Fin xs.length → ℕ, check xs pairs rank = true) ↔
      pairs.Nodup ∧ IsAcyclicMatching (toRel xs h pairs) ∧
        IsGradePreserving (gradeFilter xs h) (toRel xs h pairs) := by
  have : Fintype (TotalFace (complex xs h)) := faceFintype xs h
  have hrank : (∃ rank : Fin xs.length → ℕ, IsTopologicalRank xs pairs rank) ↔
      IsAcyclic (toRel xs h pairs) := by
    rw [isAcyclic_iff_exists_rank]
    constructor
    · rintro ⟨rank, hr⟩
      exact ⟨_, (isTopologicalRank_iff xs h pairs rank).mp hr⟩
    · rintro ⟨rank, hr⟩
      refine ⟨rank ∘ listEquiv xs h, (isTopologicalRank_iff xs h pairs _).mpr ?_⟩
      have : (rank ∘ listEquiv xs h) ∘ (listEquiv xs h).symm = rank := by
        funext σ
        simp
      rwa [this]
  simp only [check_eq_true_iff]
  rw [exists_and_left, hrank, isMatching_iff xs h pairs]
  constructor
  · rintro ⟨⟨hN, hM, hG⟩, hA⟩
    exact ⟨hN, ⟨hM, hA⟩, hG⟩
  · rintro ⟨hN, ⟨hM, hA⟩, hG⟩
    exact ⟨⟨hN, hM, hG⟩, hA⟩

/-- The same characterization, with the sublevel specialization of MN Def. 4.1 for the input
grade. -/
theorem exists_check_iff_isFilteredAcyclicMatching (xs : Input) (h : Valid xs)
    (pairs : Pairs xs) :
    (∃ rank : Fin xs.length → ℕ, check xs pairs rank = true) ↔
      pairs.Nodup ∧ IsFilteredAcyclicMatching (gradeFilter xs h) (toRel xs h pairs) := by
  rw [exists_check_iff xs h pairs, isFilteredAcyclicMatching_iff]

/-- A checked matching; it retains its rank certificate. -/
structure CertifiedMatching (xs : Input) where
  /-- The ordered (lower, upper) position pairs. -/
  pairs : Pairs xs
  /-- The rank certificate. -/
  rank : Fin xs.length → ℕ
  /-- The pairs form a list-level matching. -/
  isMatching : IsMatching xs pairs
  /-- The rank increases along every arrow between positions. -/
  isTopologicalRank : IsTopologicalRank xs pairs rank

/-- Run the checker and, on acceptance, bundle the pairs and rank with their proofs. -/
def certify? (xs : Input) (pairs : Pairs xs) (rank : Fin xs.length → ℕ) :
    Option (CertifiedMatching xs) :=
  if hc : IsMatching xs pairs ∧ IsTopologicalRank xs pairs rank then
    some ⟨pairs, rank, hc.1, hc.2⟩
  else none

/-- `certify?` succeeds exactly when the checker accepts. -/
theorem certify?_isSome_iff (xs : Input) (pairs : Pairs xs) (rank : Fin xs.length → ℕ) :
    (certify? xs pairs rank).isSome = true ↔ check xs pairs rank = true := by
  rw [check_eq_true_iff]
  unfold certify?
  split_ifs with hc <;> simp [hc]

/-- A certificate returned by `certify?` carries the supplied pairs and rank. -/
theorem certify?_eq_some {xs : Input} {pairs : Pairs xs} {rank : Fin xs.length → ℕ}
    {c : CertifiedMatching xs} (hc : certify? xs pairs rank = some c) :
    c.pairs = pairs ∧ c.rank = rank := by
  unfold certify? at hc
  split_ifs at hc
  cases hc
  exact ⟨rfl, rfl⟩

namespace CertifiedMatching

variable {xs : Input}

/-- The other face of the pair containing position `i`, if any. -/
def partner (c : CertifiedMatching xs) (i : Fin xs.length) : Option (Fin xs.length) :=
  c.pairs.findSome? fun p => if p.1 = i then some p.2 else if p.2 = i then some p.1 else none

private theorem findSome_step_eq_some {i j : Fin xs.length}
    {p : Fin xs.length × Fin xs.length}
    (hp : (if p.1 = i then some p.2 else if p.2 = i then some p.1 else none) = some j) :
    p = (i, j) ∨ p = (j, i) := by
  obtain ⟨a, b⟩ := p
  split_ifs at hp with h1 h2
  · cases hp
    simp only at h1
    subst h1
    exact Or.inl rfl
  · cases hp
    simp only at h2
    subst h2
    exact Or.inr rfl

/-- With distinct endpoints, each position has at most one partner. -/
private theorem partner_unique (c : CertifiedMatching xs) {i j j' : Fin xs.length}
    (hj : (i, j) ∈ c.pairs ∨ (j, i) ∈ c.pairs) (hj' : (i, j') ∈ c.pairs ∨ (j', i) ∈ c.pairs) :
    j = j' := by
  have hN := c.isMatching.1
  rcases hj with hj | hj <;> rcases hj' with hj' | hj'
  · have := eq_of_endpoint hN hj hj' (x := i) (Or.inl rfl) (Or.inl rfl)
    simp only [Prod.mk.injEq] at this
    exact this.2
  · have := eq_of_endpoint hN hj hj' (x := i) (Or.inl rfl) (Or.inr rfl)
    simp only [Prod.mk.injEq] at this
    exact this.2.trans this.1
  · have := eq_of_endpoint hN hj hj' (x := i) (Or.inr rfl) (Or.inl rfl)
    simp only [Prod.mk.injEq] at this
    exact this.1.trans this.2
  · have := eq_of_endpoint hN hj hj' (x := i) (Or.inr rfl) (Or.inr rfl)
    simp only [Prod.mk.injEq] at this
    exact this.1

/-- The partner is the other end of the pair containing `i`. -/
theorem partner_eq_some_iff (c : CertifiedMatching xs) (i j : Fin xs.length) :
    c.partner i = some j ↔ (i, j) ∈ c.pairs ∨ (j, i) ∈ c.pairs := by
  constructor
  · intro hc
    obtain ⟨p, hp, hpj⟩ := List.exists_of_findSome?_eq_some hc
    rcases findSome_step_eq_some hpj with rfl | rfl
    · exact Or.inl hp
    · exact Or.inr hp
  · intro hij
    cases hpi : c.partner i with
    | none =>
      exfalso
      rw [partner, List.findSome?_eq_none_iff] at hpi
      rcases hij with hij | hij
      · have := hpi _ hij
        simp at this
      · have := hpi _ hij
        split_ifs at this; simp_all
    | some j' =>
      obtain ⟨p, hp, hpj⟩ := List.exists_of_findSome?_eq_some hpi
      have hj' : (i, j') ∈ c.pairs ∨ (j', i) ∈ c.pairs := by
        rcases findSome_step_eq_some hpj with rfl | rfl
        · exact Or.inl hp
        · exact Or.inr hp
      rw [partner_unique c hij hj']

/-- Partnership is symmetric. -/
theorem partner_partner (c : CertifiedMatching xs) {i j : Fin xs.length}
    (hij : c.partner i = some j) : c.partner j = some i := by
  rw [partner_eq_some_iff] at hij ⊢
  exact hij.symm

/-- Unmatched positions in increasing order. -/
def critical (c : CertifiedMatching xs) : List (Fin xs.length) :=
  (List.finRange xs.length).filter fun i => (c.partner i).isNone

/-- The critical positions are listed in strictly increasing order. -/
theorem critical_pairwise_lt (c : CertifiedMatching xs) :
    c.critical.Pairwise (· < ·) :=
  (List.pairwise_lt_finRange xs.length).filter _

/-- No critical position is listed twice. -/
theorem critical_nodup (c : CertifiedMatching xs) : c.critical.Nodup :=
  (List.nodup_finRange xs.length).filter _

/-- The critical positions are exactly those in no pair. -/
theorem mem_critical_iff (c : CertifiedMatching xs) (i : Fin xs.length) :
    i ∈ c.critical ↔ ∀ j : Fin xs.length, (i, j) ∉ c.pairs ∧ (j, i) ∉ c.pairs := by
  simp only [critical, List.mem_filter, List.mem_finRange, true_and,
    Option.isNone_iff_eq_none, Option.eq_none_iff_forall_ne_some, ne_eq,
    partner_eq_some_iff, not_or]

/-- Every position is exactly one of: matched lower, matched upper, critical. -/
theorem trichotomy (c : CertifiedMatching xs) (i : Fin xs.length) :
    ((∃ j, (i, j) ∈ c.pairs) ∧ ¬ (∃ j, (j, i) ∈ c.pairs) ∧ i ∉ c.critical) ∨
    (¬ (∃ j, (i, j) ∈ c.pairs) ∧ (∃ j, (j, i) ∈ c.pairs) ∧ i ∉ c.critical) ∨
    (¬ (∃ j, (i, j) ∈ c.pairs) ∧ ¬ (∃ j, (j, i) ∈ c.pairs) ∧ i ∈ c.critical) := by
  have hcrit : i ∈ c.critical ↔
      ¬ (∃ j, (i, j) ∈ c.pairs) ∧ ¬ (∃ j, (j, i) ∈ c.pairs) := by
    rw [mem_critical_iff]
    constructor
    · intro hc
      exact ⟨fun ⟨j, hj⟩ => (hc j).1 hj, fun ⟨j, hj⟩ => (hc j).2 hj⟩
    · intro hc j
      exact ⟨fun hj => hc.1 ⟨j, hj⟩, fun hj => hc.2 ⟨j, hj⟩⟩
  have hboth : ¬ ((∃ j, (i, j) ∈ c.pairs) ∧ (∃ j, (j, i) ∈ c.pairs)) := by
    rintro ⟨⟨j, hj⟩, ⟨j', hj'⟩⟩
    have h1 := partner_unique c (Or.inl hj) (Or.inr hj')
    subst h1
    have := eq_of_endpoint c.isMatching.1 hj hj' (x := i) (Or.inl rfl) (Or.inr rfl)
    simp only [Prod.mk.injEq] at this
    exact fst_ne_snd_of_nodup c.isMatching.1 hj this.1
  rw [hcrit]
  by_cases hl : ∃ j, (i, j) ∈ c.pairs <;> by_cases hu : ∃ j, (j, i) ∈ c.pairs
  · exact absurd ⟨hl, hu⟩ hboth
  · exact Or.inl ⟨hl, hu, fun h => h.1 hl⟩
  · exact Or.inr (Or.inl ⟨hl, hu, fun h => h.2 hu⟩)
  · exact Or.inr (Or.inr ⟨hl, hu, hl, hu⟩)

/-- Counting: critical faces plus both faces of every pair account for all positions. -/
theorem critical_length_add (c : CertifiedMatching xs) :
    c.critical.length + 2 * c.pairs.length = xs.length := by
  have hN := c.isMatching.1
  have hmem : ∀ i : Fin xs.length, (c.partner i).isNone = !decide (i ∈ endpoints c.pairs) := by
    intro i
    have hcrit := mem_critical_iff c i
    simp only [critical, List.mem_filter, List.mem_finRange, true_and] at hcrit
    rw [Bool.eq_iff_iff, hcrit]
    simp only [Bool.not_eq_true', decide_eq_false_iff_not, mem_endpoints_iff_aux, not_exists,
      not_and, not_or]
    constructor
    · intro hc p hp
      obtain ⟨a, b⟩ := p
      refine ⟨?_, ?_⟩
      · rintro rfl
        exact (hc b).1 hp
      · rintro rfl
        exact (hc a).2 hp
    · intro hc j
      exact ⟨fun hj => (hc _ hj).1 rfl, fun hj => (hc _ hj).2 rfl⟩
  have hcr : c.critical =
      (List.finRange xs.length).filter fun i => !decide (i ∈ endpoints c.pairs) := by
    unfold critical
    exact List.filter_congr fun i _ => hmem i
  have hperm : ((List.finRange xs.length).filter fun i => decide (i ∈ endpoints c.pairs)).Perm
      (endpoints c.pairs) := by
    rw [List.perm_ext_iff_of_nodup ((List.nodup_finRange _).filter _) hN]
    intro a
    simp
  have hlen := List.length_eq_length_filter_add (l := List.finRange xs.length)
    fun i => decide (i ∈ endpoints c.pairs)
  rw [hperm.length_eq, length_endpoints, List.length_finRange] at hlen
  rw [hcr]
  omega

/-- (position, dimension, original grade) of each critical face. Total; meaningful only under
`Valid xs`; use `criticalReport?`. The dimension of a listed empty face is `0` by subtraction
in `ℕ`. -/
def criticalReport (c : CertifiedMatching xs) : List (Fin xs.length × ℕ × ℤ) :=
  c.critical.map fun i => (i, degree xs i, (xs.get i).2)

/-- The guarded report: `c.criticalReport` on a valid input, and `none` otherwise. -/
def criticalReport? (c : CertifiedMatching xs) : Option (List (Fin xs.length × ℕ × ℤ)) :=
  if Valid xs then some c.criticalReport else none

/-- The guarded report is `none` exactly when the input is not valid. -/
theorem criticalReport?_eq_none_iff (c : CertifiedMatching xs) :
    c.criticalReport? = none ↔ ¬ Valid xs := by
  unfold criticalReport?
  split_ifs with h <;> simp [h]

/-- The guarded report is `some r` exactly when the input is valid and `r` is `criticalReport`. -/
theorem criticalReport?_eq_some_iff (c : CertifiedMatching xs)
    (r : List (Fin xs.length × ℕ × ℤ)) :
    c.criticalReport? = some r ↔ Valid xs ∧ c.criticalReport = r := by
  unfold criticalReport?
  split_ifs with h <;> simp [h]

/-- The report lists the critical positions in order. -/
theorem criticalReport_map_fst (c : CertifiedMatching xs) :
    c.criticalReport.map Prod.fst = c.critical := by
  simp [criticalReport, Function.comp_def]

/-- A report entry is a critical position with its dimension and original grade. -/
theorem mem_criticalReport_iff (c : CertifiedMatching xs) (i : Fin xs.length) (d : ℕ)
    (g : ℤ) :
    (i, d, g) ∈ c.criticalReport ↔
      i ∈ c.critical ∧ d = (xs.get i).1.card - 1 ∧ g = (xs.get i).2 := by
  simp only [criticalReport, degree, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨a, ha, rfl, rfl, rfl⟩
    exact ⟨ha, rfl, rfl⟩
  · rintro ⟨hi, rfl, rfl⟩
    exact ⟨i, hi, rfl, rfl, rfl⟩

/-- The certified pairs form a filtered acyclic matching of the represented complex. -/
theorem isFilteredAcyclicMatching (c : CertifiedMatching xs) (h : Valid xs) :
    IsFilteredAcyclicMatching (gradeFilter xs h) (toRel xs h c.pairs) :=
  ((exists_check_iff_isFilteredAcyclicMatching xs h c.pairs).mp
    ⟨c.rank, (check_eq_true_iff xs c.pairs c.rank).mpr
      ⟨c.isMatching, c.isTopologicalRank⟩⟩).2

/-- The certificate, read on actual faces, is a semantic topological rank. -/
theorem isTopologicalRank_semantic (c : CertifiedMatching xs) (h : Valid xs) :
    Morse.IsTopologicalRank (toRel xs h c.pairs) (c.rank ∘ (listEquiv xs h).symm) :=
  (isTopologicalRank_iff xs h c.pairs c.rank).mp c.isTopologicalRank

/-- A critical position is a face in no pair of the semantic matching. -/
theorem mem_critical_iff_listFace (c : CertifiedMatching xs) (h : Valid xs)
    (i : Fin xs.length) :
    i ∈ c.critical ↔ ∀ τ : TotalFace (complex xs h),
      ¬ toRel xs h c.pairs (listFace xs h i) τ ∧ ¬ toRel xs h c.pairs τ (listFace xs h i) := by
  rw [mem_critical_iff]
  constructor
  · intro hc τ
    obtain ⟨j, rfl⟩ := (listEquiv xs h).surjective τ
    simp only [listEquiv_apply, toRel_listFace]
    exact hc j
  · intro hc j
    have := hc (listFace xs h j)
    simpa only [toRel_listFace] using this

end CertifiedMatching

end TDA.Persistence.Morse.MatchingInput
