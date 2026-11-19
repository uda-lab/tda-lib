import Mathlib.Data.Nat.Log
import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Executable rank of rectangular F₂ matrices

For a matrix `M` with `m` rows and `n` columns over `ZMod 2`, `F2Matrix.imageFinset M` is the
finite set of images `M.mulVec v` of all `2 ^ n` source vectors, and `F2Matrix.rank M` is the
base-two logarithm of its cardinality. The image set is exactly the range of `M.mulVecLin`, a
vector space over a field with two elements, so it has `2 ^ r` elements for the range
dimension `r`; hence the executed number equals Mathlib's `Matrix.rank M`.

Both definitions are computable. There is no hypothesis on the shape: with no rows or no columns
the image set is a single vector and the rank is zero.

The procedure evaluates `2 ^ n` source vectors, each in `O(m * n)` field operations, and the
deduplication of the image list may compare up to `O(4 ^ n)` pairs of vectors. It is not an
elimination algorithm and carries no polynomial running-time bound.
-/

set_option autoImplicit false

namespace TDA.Persistence.Reduction.F2Matrix

variable {m n : ℕ}

/-- The images `M.mulVec v` of all source vectors `v : Fin n → ZMod 2`. -/
def imageFinset (M : Matrix (Fin m) (Fin n) (ZMod 2)) : Finset (Fin m → ZMod 2) :=
  Finset.univ.image M.mulVec

/-- The enumerated images are exactly the range of the linear map `M.mulVecLin`. -/
theorem mem_imageFinset (M : Matrix (Fin m) (Fin n) (ZMod 2)) (v : Fin m → ZMod 2) :
    v ∈ imageFinset M ↔ v ∈ LinearMap.range M.mulVecLin := by
  simp [imageFinset, LinearMap.mem_range]

/-- There are exactly `2 ^ r` distinct images, where `r` is the range dimension; the count
includes the zero vector. -/
theorem card_imageFinset (M : Matrix (Fin m) (Fin n) (ZMod 2)) :
    (imageFinset M).card = 2 ^ Module.finrank (ZMod 2) (LinearMap.range M.mulVecLin) := by
  classical
  let e : ↥(imageFinset M) ≃ LinearMap.range M.mulVecLin :=
    Equiv.subtypeEquivRight (mem_imageFinset M)
  calc
    (imageFinset M).card = Fintype.card (LinearMap.range M.mulVecLin) := by
      rw [← Fintype.card_coe]
      exact Fintype.card_congr e
    _ = _ := by rw [Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card]

/-- Executable rank of an F₂ matrix: the base-two logarithm of the number of distinct images.

Call it as `F2Matrix.rank M`. In dot notation, `M.rank` is Mathlib's noncomputable
`Matrix.rank`; `rank_eq_matrixRank` identifies the two values. -/
def rank (M : Matrix (Fin m) (Fin n) (ZMod 2)) : ℕ :=
  Nat.log 2 (imageFinset M).card

/-- The executed rank is the dimension of the range of `M.mulVecLin`. -/
theorem rank_eq_finrank_range (M : Matrix (Fin m) (Fin n) (ZMod 2)) :
    rank M = Module.finrank (ZMod 2) (LinearMap.range M.mulVecLin) := by
  rw [rank, card_imageFinset]
  exact Nat.log_pow (b := 2) (by decide) _

/-- The executed rank agrees with Mathlib's `Matrix.rank`. -/
theorem rank_eq_matrixRank (M : Matrix (Fin m) (Fin n) (ZMod 2)) :
    rank M = Matrix.rank M :=
  rank_eq_finrank_range M

/-- For a linear map between coordinate spaces, the executed rank of its matrix is the
dimension of its range. -/
theorem rank_toMatrix' (f : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2)) :
    rank (LinearMap.toMatrix' f) = Module.finrank (ZMod 2) (LinearMap.range f) := by
  rw [rank_eq_finrank_range, ← Matrix.toLin'_apply', Matrix.toLin'_toMatrix']

/-- Rank–nullity for the executed rank: together with the kernel dimension it gives the number
of columns. -/
theorem rank_add_finrank_ker (M : Matrix (Fin m) (Fin n) (ZMod 2)) :
    rank M + Module.finrank (ZMod 2) (LinearMap.ker M.mulVecLin) = n := by
  have h := M.mulVecLin.finrank_range_add_finrank_ker
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h
  rw [rank_eq_finrank_range]
  exact h

/-- The executed rank is at most the number of columns. -/
theorem rank_le_width (M : Matrix (Fin m) (Fin n) (ZMod 2)) : rank M ≤ n := by
  rw [rank_eq_matrixRank]
  exact Matrix.rank_le_width M

/-- The executed rank is at most the number of rows. -/
theorem rank_le_height (M : Matrix (Fin m) (Fin n) (ZMod 2)) : rank M ≤ m := by
  rw [rank_eq_matrixRank]
  exact Matrix.rank_le_height M

end TDA.Persistence.Reduction.F2Matrix
