import TDA.Persistence.PersistenceMeasureMatching
import Mathlib.Combinatorics.Hall.Basic

/-!
# Finite matching in a persistence window

When every source occurrence has positive distance from the boundary of a finite
window, a sufficiently small closed-ball comparison gives equal capacity in each
source cluster. Finite Hall matching then matches all source occurrences. The reverse
closed-ball comparison also covers every target occurrence that stays inside the
window. Repeated point values are counted as separate tokens; target point values
need not be separated.
-/

universe u v

namespace TDA.Persistence.PersistenceMeasureWindowMatching

open TDA.Persistence

variable {I : Type u} {J : Type v} [Fintype I] [Fintype J]

/-- Source occurrences whose point value is exactly `p`. Repeated tokens remain
separate elements of the finite set. -/
noncomputable def pointFiber (x : I → ℝ × ℝ) (p : ℝ × ℝ) : Finset I := by
  classical
  exact Finset.univ.filter fun i => x i = p

/-- Occurrences in the closed maximum-norm ball about `p` of radius `r`. -/
noncomputable def pointBall (x : I → ℝ × ℝ) (p : ℝ × ℝ) (r : ℝ) : Finset I := by
  classical
  exact Finset.univ.filter fun i => dist (x i) p ≤ r

private theorem pointBall_zero (x : I → ℝ × ℝ) (p : ℝ × ℝ) :
    pointBall x p 0 = pointFiber x p := by
  classical
  ext i
  simp [pointBall, pointFiber, dist_eq_zero]

private theorem sourceBall_two_eq_fiber
    (x : I → ℝ × ℝ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hsep : ∀ i i', x i ≠ x i' → 2 * δ < dist (x i) (x i'))
    (p : ℝ × ℝ) (i₀ : I) (hi₀ : x i₀ = p) :
    pointBall x p (2 * δ) = pointFiber x p := by
  classical
  ext i
  simp only [pointBall, pointFiber, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hdist
    by_contra hne
    have hne' : x i ≠ x i₀ := by
      intro h
      exact hne (h.trans hi₀)
    have hs := hsep i i₀ hne'
    rw [hi₀] at hs
    linarith
  · intro h
    simpa [h, dist_self] using (show (0 : ℝ) ≤ 2 * δ by positivity)

private theorem sourceCluster_card_eq
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hsep : ∀ i i', x i ≠ x i' → 2 * δ < dist (x i) (x i'))
    (hxy0 : ∀ i, (pointBall x (x i) 0).card ≤ (pointBall y (x i) δ).card)
    (hyxδ : ∀ i, (pointBall y (x i) δ).card ≤ (pointBall x (x i) (2 * δ)).card)
    (i₀ : I) :
    (pointFiber x (x i₀)).card = (pointBall y (x i₀) δ).card := by
  have hxy0' := hxy0 i₀
  rw [pointBall_zero] at hxy0'
  have hyxδ' := hyxδ i₀
  have hx2 := sourceBall_two_eq_fiber x hδ hsep (x i₀) i₀ rfl
  rw [hx2] at hyxδ'
  exact le_antisymm (by simpa using hxy0') hyxδ'

/-- Sharp finite-window matching from the three closed-ball comparisons used by Hall.
Every source fiber has exactly the capacity of its target δ-ball, and every target
with exit greater than δ has a source δ-neighbor. If source point values are separated
by more than `2 * δ`, a finite Hall argument matches every source token injectively;
the exact cluster counts also force every target with exit greater than δ into the
image. No separation condition is imposed on target point values. -/
theorem exists_finite_window_matching_of_center_counts
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) (exit : ℝ × ℝ → ℝ) {δ : ℝ}
    (hδ : 0 ≤ δ)
    (hsepX : ∀ i i', x i ≠ x i' → 2 * δ < dist (x i) (x i'))
    (hxy0 : ∀ i, (pointBall x (x i) 0).card ≤ (pointBall y (x i) δ).card)
    (hyxδ : ∀ i, (pointBall y (x i) δ).card ≤ (pointBall x (x i) (2 * δ)).card)
    (hyx0 : ∀ j, δ < exit (y j) →
      (pointBall y (y j) 0).card ≤ (pointBall x (y j) δ).card) :
    ∃ f : I → J,
      Function.Injective f ∧
      (∀ i, dist (x i) (y (f i)) ≤ δ) ∧
      (∀ j, δ < exit (y j) → ∃ i, f i = j) := by
  classical
  have hcluster (p : ℝ × ℝ) (i₀ : I) (hi₀ : x i₀ = p) :
      (pointFiber x p).card = (pointBall y p δ).card := by
    subst p
    exact sourceCluster_card_eq x y hδ hsepX hxy0 hyxδ i₀
  have hHall : ∀ s : Finset I,
      s.card ≤ (Finset.univ.filter fun j => ∃ i ∈ s, dist (y j) (x i) ≤ δ).card := by
    intro s
    let P : Finset (ℝ × ℝ) := s.image x
    let N : ℝ × ℝ → Finset J := fun p => pointBall y p δ
    have hdis : (P : Set (ℝ × ℝ)).PairwiseDisjoint N := by
      intro p hp q hq hpq
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
      obtain ⟨i', hi', hiEq⟩ := Finset.mem_image.mp hq
      subst q
      apply Finset.disjoint_left.mpr
      intro j hj hj'
      have h1 := (Finset.mem_filter.mp hj).2
      have h2 := (Finset.mem_filter.mp hj').2
      have hdist := dist_triangle (x i) (y j) (x i')
      rw [dist_comm (x i) (y j)] at hdist
      have hsep := hsepX i i' (by
        intro heq
        apply hpq
        simpa [heq] using hiEq.symm)
      linarith
    calc
      s.card = ∑ p ∈ P, (s.filter fun i => x i = p).card :=
        Finset.card_eq_sum_card_image x s
      _ ≤ ∑ p ∈ P, (N p).card := by
        apply Finset.sum_le_sum
        intro p hp
        obtain ⟨i₀, hi₀, rfl⟩ := Finset.mem_image.mp hp
        have hsmall : (s.filter fun i => x i = x i₀).card ≤
            (pointFiber x (x i₀)).card := by
          apply Finset.card_le_card
          intro i hi
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2⟩
        exact hsmall.trans_eq (hcluster (x i₀) i₀ rfl)
      _ = (P.biUnion N).card := (Finset.card_biUnion hdis).symm
      _ = (Finset.univ.filter fun j => ∃ i ∈ s, dist (y j) (x i) ≤ δ).card := by
        congr 1
        ext j
        simp only [P, N, Finset.mem_biUnion, Finset.mem_image, pointBall,
          Finset.mem_filter, Finset.mem_univ, true_and]
        aesop
  obtain ⟨f, hf, hclose⟩ :=
    (Fintype.all_card_le_filter_rel_iff_exists_injective
      (fun i j => dist (y j) (x i) ≤ δ)).mp hHall
  refine ⟨f, hf, ?_, ?_⟩
  · intro i
    simpa only [dist_comm] using hclose i
  · intro j hj
    have hpositive : 0 < (pointBall x (y j) δ).card := by
      have hYpos : 0 < (pointFiber y (y j)).card := by
        apply Finset.card_pos.mpr
        exact ⟨j, by simp [pointFiber]⟩
      have h := hyx0 j hj
      rw [pointBall_zero] at h
      exact hYpos.trans_le (by simpa using h)
    obtain ⟨i, hi⟩ := Finset.card_pos.mp hpositive
    have hclose' : dist (x i) (y j) ≤ δ := by
      simpa [pointBall, dist_comm] using hi
    let A : Finset I := pointFiber x (x i)
    let B : Finset J := pointBall y (x i) δ
    have hA_image : A.image f = B := by
      have hsub : A.image f ⊆ B := by
        intro j' hj'
        obtain ⟨i', hi', rfl⟩ := Finset.mem_image.mp hj'
        have hci := hclose i'
        have hpoint : x i' = x i := (Finset.mem_filter.mp hi').2
        simpa [A, B, pointBall, hpoint, dist_comm] using hci
      have hAcard : A.card = B.card := by
        simpa [A, B] using hcluster (x i) i rfl
      apply Finset.eq_of_subset_of_card_le hsub
      rw [Finset.card_image_of_injective _ hf]
      exact hAcard.symm.le
    have hjB : j ∈ B := by
      simp [B, pointBall, dist_comm, hclose']
    have hjImage : j ∈ A.image f := hA_image.symm ▸ hjB
    obtain ⟨i', _, hi'⟩ := Finset.mem_image.mp hjImage
    exact ⟨i', hi'⟩

end TDA.Persistence.PersistenceMeasureWindowMatching
