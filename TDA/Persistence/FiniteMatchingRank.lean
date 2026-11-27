import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic.Linarith

/-!
# Rank and coordinate bounds for finite matchings

A product with triangular entries in score order and a nonzero diagonal gives a
cardinality bound even after removing middle indices that only contribute below the
diagonal. Coordinate bounds in one and two dimensions give the strict score comparison
that excludes such contributions.
-/

set_option autoImplicit false

namespace TDA.Persistence.FiniteMatchingRank

open scoped BigOperators

/-- If discarded middle indices only contribute from strictly smaller column scores,
the restricted product retains every entry at or above the diagonal in score order.
Its full rank bounds the number of kept indices from below. -/
theorem card_le_of_restricted_triangular_product
    {𝕜 S N : Type*} [Field 𝕜] [Fintype S] [Fintype N]
    (A : Matrix N S 𝕜) (B : Matrix S N 𝕜) (kept : Finset N) (score : S → ℝ)
    (hzero : ∀ k i, k ≠ i → score k ≤ score i → (B * A) k i = 0)
    (hdiag : ∀ i, (B * A) i i ≠ 0)
    (hdiscard : ∀ k i j, j ∉ kept → B k j * A j i ≠ 0 → score i < score k) :
    Fintype.card S ≤ Fintype.card ↥kept := by
  classical
  let A' : Matrix ↥kept S 𝕜 := A.submatrix Subtype.val id
  let B' : Matrix S ↥kept 𝕜 := B.submatrix id Subtype.val
  have hentry (k i : S) (h : score k ≤ score i) : (B' * A') k i = (B * A) k i := by
    simp only [Matrix.mul_apply, A', B', Matrix.submatrix_apply, id_eq]
    calc
      _ = ∑ j ∈ kept, B k j * A j i := Finset.sum_attach kept _
      _ = _ := Finset.sum_subset (Finset.subset_univ kept)
        (fun j _ hj => not_ne_iff.mp fun hn => (not_lt_of_ge h) (hdiscard k i j hj hn))
  have htri : (B' * A').BlockTriangular (OrderDual.toDual ∘ score) := by
    intro k i h
    have hki : score k < score i := h
    exact (hentry k i hki.le).trans (hzero k i (ne_of_lt hki ∘ congrArg score) hki.le)
  have hdet : (B' * A').det ≠ 0 := by
    rw [htri.det]
    apply Finset.prod_ne_zero_iff.mpr
    intro a _
    have hblock : (B' * A').toSquareBlock (OrderDual.toDual ∘ score) a =
        Matrix.diagonal (fun i => (B * A) i.val i.val) := by
      ext k i
      have heq : score k.val = score i.val := k.property.trans i.property.symm
      rw [show (B' * A').toSquareBlock _ a k i = (B' * A') k.val i.val from rfl,
        hentry _ _ heq.le]
      by_cases h : k = i
      · subst i
        rw [Matrix.diagonal_apply_eq]
      · rw [Matrix.diagonal_apply_ne _ h, hzero _ _ (fun he => h (Subtype.ext he)) heq.le]
    rw [hblock, Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => hdiag i.val
  calc
    Fintype.card S = (B' * A').rank := (Matrix.rank_of_det_ne_zero hdet).symm
    _ ≤ B'.rank := Matrix.rank_mul_le_left B' A'
    _ ≤ Fintype.card ↥kept := Matrix.rank_le_card_width B'

/-- In one coordinate, two directed steps outside the distance bound strictly increase
the coordinate. -/
theorem lt_of_abs_sub_gt {p q s ε : ℝ}
    (hp : p ≤ q + ε) (hs : q ≤ s + ε)
    (hpq : ε < |p - q|) (hqs : ε < |q - s|) : p < s := by
  rw [lt_abs] at hpq hqs
  rcases hpq with h | h <;> rcases hqs with h' | h' <;> linarith

/-- In two coordinates, two coordinatewise directed steps outside the sup-distance bound
strictly increase the coordinate sum. -/
theorem sum_lt_of_sup_abs_sub_gt {p q s : ℝ × ℝ} {ε : ℝ}
    (hp : p.1 ≤ q.1 + ε ∧ p.2 ≤ q.2 + ε)
    (hs : q.1 ≤ s.1 + ε ∧ q.2 ≤ s.2 + ε)
    (hpq : ε < max |p.1 - q.1| |p.2 - q.2|)
    (hqs : ε < max |q.1 - s.1| |q.2 - s.2|) : p.1 + p.2 < s.1 + s.2 := by
  simp only [lt_max_iff, lt_abs] at hpq hqs
  obtain ⟨hp₁, hp₂⟩ := hp
  obtain ⟨hs₁, hs₂⟩ := hs
  rcases hpq with (h | h) | (h | h) <;> rcases hqs with (h' | h') | (h' | h') <;> linarith

end TDA.Persistence.FiniteMatchingRank
