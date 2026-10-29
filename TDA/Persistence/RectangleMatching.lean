import TDA.Persistence.RectangleHall
import TDA.Persistence.FiniteOccurrenceMatching
import TDA.Persistence.DiagramBottleneck
import Mathlib.Combinatorics.Hall.Basic

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
  obtain ⟨M, hp, hs, ht⟩ := FiniteOccurrenceMatching.exists_two_sided P Q (fun i j =>
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
