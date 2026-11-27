import TDA.Persistence.DiagramBottleneck
import Mathlib.Combinatorics.Hall.Basic
import Mathlib.SetTheory.Cardinal.SchroederBernstein

/-!
# Combining finite partial injections into one occurrence matching

Two injections between selected occurrences can be combined into a partial
matching that covers both selected sides, provided every padded edge respects
the matching relation. The finite combinator below uses occurrence types
`α` and `β` in universe 0 (`Type`); the underlying `OccurrenceMatching`
structure remains universe-polymorphic. The auxiliary natural-number labels
used by Schröder–Bernstein are discarded; only original finite occurrence
indices are matched.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence.FiniteOccurrenceMatching

open Function
open scoped Classical

/- Even labels encode unmatched original occurrences; odd labels receive
padding. -/
private noncomputable def padded {α β : Type} [Fintype α] (P : α → Prop)
    (f : {a // P a} → β) : α ⊕ ℕ → β ⊕ ℕ
  | .inl a => if h : P a then .inl (f ⟨a, h⟩)
      else .inr (2 * (Fintype.equivFin α a).val)
  | .inr m => .inr (2 * m + 1)

private theorem padded_injective {α β : Type} [Fintype α] (P : α → Prop)
    (f : {a // P a} → β) (hf : Injective f) : Injective (padded P f) := by
  classical
  intro x y h
  cases x with
  | inl a =>
    cases y with
    | inl b =>
      by_cases ha : P a <;> by_cases hb : P b
      · simp only [padded, dif_pos ha, dif_pos hb, Sum.inl.injEq] at h
        exact congrArg Sum.inl (congrArg Subtype.val (hf h))
      · simp [padded, ha, hb] at h
      · simp [padded, ha, hb] at h
      · simp only [padded, dif_neg ha, dif_neg hb, Sum.inr.injEq] at h
        apply congrArg Sum.inl
        apply (Fintype.equivFin α).injective
        apply Fin.ext
        omega
    | inr m =>
      by_cases ha : P a
      · simp [padded, ha] at h
      · simp only [padded, dif_neg ha, Sum.inr.injEq] at h
        omega
  | inr m =>
    cases y with
    | inl b =>
      by_cases hb : P b
      · simp [padded, hb] at h
      · simp only [padded, dif_neg hb, Sum.inr.injEq] at h
        omega
    | inr l =>
      simp only [padded, Sum.inr.injEq] at h
      congr 1
      omega

private def paddedRelation {α β : Type} (P : α → Prop) (Q : β → Prop)
    (r : α → β → Prop) : α ⊕ ℕ → β ⊕ ℕ → Prop
  | .inl a, .inl b => r a b
  | .inl a, .inr _ => ¬ P a
  | .inr _, .inl b => ¬ Q b
  | .inr _, .inr _ => True

/-- Two relation-preserving injections on the selected occurrences determine
one partial occurrence matching that covers every selected occurrence on
both sides.

The occurrence types `α` and `β` are taken in `Type` (universe zero), although
`OccurrenceMatching` is universe-polymorphic: the proof pads both sides with `ℕ`. -/
theorem exists_two_sided {α β : Type} [Fintype α] [Fintype β]
    (P : α → Prop) (Q : β → Prop) (r : α → β → Prop)
    (f : {a // P a} → β) (hf : Injective f) (hfr : ∀ a, r a.val (f a))
    (g : {b // Q b} → α) (hg : Injective g) (hgr : ∀ b, r (g b) b.val) :
    ∃ M : OccurrenceMatching α β PEmpty.{1} PEmpty.{1},
      (∀ a b, M.finite a = some b → r a b) ∧
      (∀ a, P a → ∃ b, M.finite a = some b) ∧
      (∀ b, Q b → ∃ a, M.finite a = some b) := by
  classical
  have hp : ∀ a, paddedRelation P Q r a (padded P f a) := by
    rintro (a | m)
    · by_cases h : P a
      · simpa only [padded, dif_pos h, paddedRelation] using hfr ⟨a, h⟩
      · simp [padded, paddedRelation, h]
    · trivial
  have hq : ∀ b, paddedRelation P Q r (padded Q g b) b := by
    rintro (b | m)
    · by_cases h : Q b
      · simpa only [padded, dif_pos h, paddedRelation] using hgr ⟨b, h⟩
      · simp [padded, paddedRelation, h]
    · trivial
  obtain ⟨h, hbij, hr⟩ := Function.Embedding.schroeder_bernstein_of_rel
    (padded_injective P f hf) (padded_injective Q g hg) (paddedRelation P Q r) hp hq
  let σ : α → Option β := fun a => match h (.inl a) with
    | .inl b => some b
    | .inr _ => none
  have hs (a : α) (b : β) : σ a = some b ↔ h (.inl a) = .inl b := by
    cases hh : h (.inl a) <;> simp [σ, hh]
  refine ⟨⟨σ, ?_, Equiv.refl _⟩, ?_, ?_, ?_⟩
  · intro a a' b ha ha'
    exact Sum.inl.inj (hbij.1 ((hs a b).mp ha |>.trans ((hs a' b).mp ha').symm))
  · intro a b hab
    have hh := hr (.inl a)
    rw [(hs a b).mp hab] at hh
    exact hh
  · intro a ha
    have hh := hr (.inl a)
    cases he : h (.inl a) with
    | inl b => exact ⟨b, (hs a b).mpr he⟩
    | inr m =>
      rw [he] at hh
      exact False.elim (hh ha)
  · intro b hb
    obtain ⟨a, ha⟩ := hbij.2 (.inl b)
    have hh := hr a
    rw [ha] at hh
    cases a with
    | inl a => exact ⟨a, (hs a b).mpr ha⟩
    | inr m => exact False.elim (hh hb)

/-- The vertices related to at least one member of a selected finite set. -/
noncomputable def neighbors {α β : Type} [Fintype β] (r : α → β → Prop) (S : Finset α) :
    Finset β :=
  Finset.univ.filter fun b => ∃ a ∈ S, r a b

/-- Membership in the finite set of neighbours. -/
@[simp]
theorem mem_neighbors {α β : Type} [Fintype β] {r : α → β → Prop} {S : Finset α} {b : β} :
    b ∈ neighbors r S ↔ ∃ a ∈ S, r a b := by
  simp [neighbors]

private theorem hall_on_finset {α β : Type} [Fintype β]
    (L : Finset α) (r : α → β → Prop)
    (h : ∀ S : Finset α, S ⊆ L →
      S.card ≤ (neighbors r S).card) :
    ∃ f : L → β, Injective f ∧ ∀ a, r a.val (f a) := by
  classical
  apply (Fintype.all_card_le_filter_rel_iff_exists_injective
    (fun (a : L) b => r a.val b)).mp
  intro S
  let e : L ↪ α := ⟨Subtype.val, Subtype.val_injective⟩
  have hsub : S.map e ⊆ L := by
    intro a ha
    obtain ⟨a, _, rfl⟩ := Finset.mem_map.1 ha
    exact a.property
  simpa only [neighbors, Finset.card_map, Finset.mem_map, exists_exists_and_eq_and, e,
    Function.Embedding.coeFn_mk] using h (S.map e) hsub

/-- The Hall inequalities on subsets of `L` and `M` give one partial matching
along `r` covering both selected sets. Neighbours can be anywhere on the opposite side. -/
theorem exists_two_sided_of_hall {α β : Type} [Fintype α] [Fintype β]
    (r : α → β → Prop) (L : Finset α) (M : Finset β)
    (hL : ∀ S : Finset α, S ⊆ L →
      S.card ≤ (neighbors r S).card)
    (hM : ∀ S : Finset β, S ⊆ M →
      S.card ≤ (neighbors (fun b a => r a b) S).card) :
    ∃ σ : OccurrenceMatching α β PEmpty.{1} PEmpty.{1},
      (∀ a b, σ.finite a = some b → r a b) ∧
      (∀ a ∈ L, ∃ b, σ.finite a = some b) ∧
      (∀ b ∈ M, ∃ a, σ.finite a = some b) := by
  obtain ⟨f, hf, hfr⟩ := hall_on_finset L r hL
  obtain ⟨g, hg, hgr⟩ := hall_on_finset M (fun b a => r a b) hM
  exact exists_two_sided (· ∈ L) (· ∈ M) r f hf hfr g hg hgr

end TDA.Persistence.FiniteOccurrenceMatching
