import TDA.Persistence.RectangleHall
import TDA.Persistence.DiagramBottleneck
import Mathlib.Combinatorics.Hall.Basic
import Mathlib.SetTheory.Cardinal.SchroederBernstein

/-!
# Two-sided matchings of finite rectangle families

An occurrence matching at radius ρ pairs actually ρ-interleaved rectangle
modules and leaves only modules ρ-interleaved with zero unmatched. The finite
Hall inequality applied to an interleaving and its reverse supplies injections
on the two sets of 2ρ-significant occurrences. Relation-preserving
Schröder–Bernstein combines them into one partial matching covering both sets.

This is the finite bounded matching-existence conclusion of Bjerkevik's
Theorem 4.3. The auxiliary natural-number labels used in Schröder–Bernstein
are discarded; only the original finite occurrence indices are matched.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence.RectangleMatching

open CategoryTheory CategoryTheory.Limits CoordinateShift RectangleHall
open scoped TDA.Persistence NNReal ZeroObject Classical

variable {k : Type u} [Field k] {n : ℕ}

/-- A zero double-shift transition gives an actual interleaving with zero. -/
noncomputable def interleavingZero (R : Rectangle n) (ρ : ℝ≥0)
    (h : transition (ρ + ρ) (R.module (k := k)) = 0) :
    CoordinateInterleaving ρ (R.module (k := k)) 0 where
  φ := 0
  ψ := 0
  φ_ψ := by simp [h]
  ψ_φ := by exact Subsingleton.elim _ _

/-- The significance threshold includes endpoint decorations and ρ=0 exactly. -/
theorem interleaved_zero_iff (R : Rectangle n) (ρ : ℝ≥0) :
    Nonempty (CoordinateInterleaving ρ (R.module (k := k)) 0) ↔
      ¬ Significant (ρ + ρ) R := by
  rw [significant_iff_transition_ne_zero (k := k)]
  simp only [not_not]
  constructor
  · rintro ⟨I⟩
    have hφ : I.φ = 0 := by
      apply NatTrans.ext
      funext p
      exact (Functor.zero_obj (C := Fin n → ℝ) (D := ModuleCat.{u} k)
        (translation ρ p)).eq_of_tgt _ _
    simpa [hφ] using I.φ_ψ.symm
  · intro h
    exact ⟨interleavingZero R ρ h⟩

/-- A radius-ρ matching uses the existing partial occurrence injection, with
actual interleaving witnesses for pairs and for every deletion on either side. -/
structure IsMatching {ι κ : Type} (ρ : ℝ≥0)
    (R : ι → Rectangle n) (S : κ → Rectangle n)
    (M : OccurrenceMatching ι κ PEmpty.{1} PEmpty.{1}) : Prop where
  paired : ∀ i j, M.finite i = some j →
    Nonempty (CoordinateInterleaving ρ ((R i).module (k := k)) (S j).module)
  source_zero : ∀ i, M.finite i = none →
    Nonempty (CoordinateInterleaving ρ ((R i).module (k := k)) 0)
  target_zero : ∀ j, (∀ i, M.finite i ≠ some j) →
    Nonempty (CoordinateInterleaving ρ ((S j).module (k := k)) 0)

/-- Every significant source occurrence has a partner in an admissible matching. -/
theorem IsMatching.source_covered {ι κ : Type} {ρ : ℝ≥0}
    {R : ι → Rectangle n} {S : κ → Rectangle n}
    {M : OccurrenceMatching ι κ PEmpty.{1} PEmpty.{1}}
    (hM : IsMatching (k := k) ρ R S M) (i : ι)
    (hi : Significant (ρ + ρ) (R i)) : ∃ j, M.finite i = some j := by
  cases h : M.finite i with
  | some j => exact ⟨j, rfl⟩
  | none => exact False.elim ((interleaved_zero_iff (k := k) (R i) ρ).mp
      (hM.source_zero i h) hi)

/-- Every significant target occurrence is in the range of the same matching. -/
theorem IsMatching.target_covered {ι κ : Type} {ρ : ℝ≥0}
    {R : ι → Rectangle n} {S : κ → Rectangle n}
    {M : OccurrenceMatching ι κ PEmpty.{1} PEmpty.{1}}
    (hM : IsMatching (k := k) ρ R S M) (j : κ)
    (hj : Significant (ρ + ρ) (S j)) : ∃ i, M.finite i = some j := by
  classical
  by_contra h
  push Not at h
  exact (interleaved_zero_iff (k := k) (S j) ρ).mp (hM.target_zero j h) hj

/-- Hall's proved inequalities produce distinct admissible partners for every
significant source occurrence. These are outputs of the actual interleaving. -/
theorem exists_significant_injection (hn : 0 < n)
    {ι κ : Type} [Fintype ι] [Fintype κ]
    (R : ι → Rectangle n) (S : κ → Rectangle n) (ε : ℝ≥0)
    (I : CoordinateInterleaving ε (RectangleFamily.module (k := k) R)
      (RectangleFamily.module S)) :
    ∃ f : {i // Significant
        (RectangleStabilityGeometry.stabilityRadius n ε +
          RectangleStabilityGeometry.stabilityRadius n ε) (R i)} → κ,
      Function.Injective f ∧ ∀ i, Neighbor (k := k)
        (RectangleStabilityGeometry.stabilityRadius n ε) (R i.val) (S (f i)) := by
  classical
  apply (Fintype.all_card_le_filter_rel_iff_exists_injective
    (fun (i : {i // Significant
        (RectangleStabilityGeometry.stabilityRadius n ε +
          RectangleStabilityGeometry.stabilityRadius n ε) (R i)}) (j : κ) =>
      Neighbor (k := k) (RectangleStabilityGeometry.stabilityRadius n ε)
        (R i.val) (S j))).mp
  intro A
  let A' : Finset ι := A.image Subtype.val
  have hA : ∀ i ∈ A', Significant
      (RectangleStabilityGeometry.stabilityRadius n ε +
        RectangleStabilityGeometry.stabilityRadius n ε) (R i) := by
    intro i hi
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hi
    exact a.property
  have h := card_le_neighbors hn R S ε I A' hA
  have he : neighbors (k := k) R S A'
      (RectangleStabilityGeometry.stabilityRadius n ε) =
      Finset.univ.filter (fun j => ∃ a ∈ A, Neighbor (k := k)
        (RectangleStabilityGeometry.stabilityRadius n ε) (R a.val) (S j)) := by
    ext j
    simp [neighbors, A']
  rw [he, Finset.card_image_of_injective A Subtype.val_injective] at h
  exact h

-- Padding a one-sided injection leaves a disjoint set of labels for deletions.
-- Even labels encode unmatched original occurrences; odd labels receive padding.
private noncomputable def padded {α β : Type} [Fintype α] (P : α → Prop)
    (f : {a // P a} → β) : α ⊕ ℕ → β ⊕ ℕ
  | .inl a => if h : P a then .inl (f ⟨a, h⟩)
      else .inr (2 * (Fintype.equivFin α a).val)
  | .inr m => .inr (2 * m + 1)

private theorem padded_injective {α β : Type} [Fintype α] (P : α → Prop)
    (f : {a // P a} → β) (hf : Function.Injective f) :
    Function.Injective (padded P f) := by
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

private theorem exists_two_sided {α β : Type} [Fintype α] [Fintype β]
    (P : α → Prop) (Q : β → Prop) (r : α → β → Prop)
    (f : {a // P a} → β) (hf : Function.Injective f) (hfr : ∀ a, r a.val (f a))
    (g : {b // Q b} → α) (hg : Function.Injective g) (hgr : ∀ b, r (g b) b.val) :
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

/-- An actual ε-interleaving yields one radius-(2n−1)ε partial occurrence
matching, with actual zero interleavings for all unmatched occurrences on
both sides. No Hall or matching assumption is supplied to this theorem. -/
theorem exists_matching (hn : 0 < n)
    {ι κ : Type} [Fintype ι] [Fintype κ]
    (R : ι → Rectangle n) (S : κ → Rectangle n) (ε : ℝ≥0)
    (I : CoordinateInterleaving ε (RectangleFamily.module (k := k) R)
      (RectangleFamily.module S)) :
    ∃ M : OccurrenceMatching ι κ PEmpty.{1} PEmpty.{1},
      IsMatching (k := k) (RectangleStabilityGeometry.stabilityRadius n ε) R S M := by
  classical
  let ρ := RectangleStabilityGeometry.stabilityRadius n ε
  let P := fun i => Significant (ρ + ρ) (R i)
  let Q := fun j => Significant (ρ + ρ) (S j)
  obtain ⟨f, hf, hfr⟩ := exists_significant_injection hn R S ε I
  obtain ⟨g, hg, hgr⟩ := exists_significant_injection hn S R ε I.symm
  obtain ⟨M, hp, hs, ht⟩ := exists_two_sided P Q (fun i j =>
    Neighbor (k := k) ρ (R i) (S j)) f hf hfr g hg
    (fun j => (hgr j).elim (fun h => ⟨h.symm⟩))
  refine ⟨M, hp, ?_, ?_⟩
  · intro i hi
    apply (interleaved_zero_iff (k := k) (R i) ρ).mpr
    intro h
    obtain ⟨j, hj⟩ := hs i h
    simp [hi] at hj
  · intro j hj
    apply (interleaved_zero_iff (k := k) (S j) ρ).mpr
    intro h
    obtain ⟨i, hi⟩ := ht j h
    exact hj i hi

end TDA.Persistence.RectangleMatching
