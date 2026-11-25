import TDA.Persistence.Reduction.F2MatrixRank
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Executed ranks of small F₂ matrices

Degenerate shapes, both rectangular orientations, repeated columns and a matrix that is
rank-deficient in both directions. The last examples derive statements about Mathlib's
`Matrix.rank` and about kernels from the executed values.
-/

set_option autoImplicit false

namespace TDA.Persistence.Reduction.F2Matrix.Examples

/-- With no rows every source vector has the same empty image. -/
theorem zero_rows : rank (0 : Matrix (Fin 0) (Fin 3) (ZMod 2)) = 0 := by decide +kernel

/-- With no columns the single empty source vector has the zero image. -/
theorem zero_columns : rank (0 : Matrix (Fin 3) (Fin 0) (ZMod 2)) = 0 := by decide +kernel

/-- A zero map between nonzero spaces. -/
theorem zero_matrix : rank (0 : Matrix (Fin 2) (Fin 3) (ZMod 2)) = 0 := by decide +kernel

/-- The identity has full rank. -/
theorem identity : rank (1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) = 3 := by decide +kernel

/-- A wide matrix of full row rank. -/
def wide : Matrix (Fin 2) (Fin 3) (ZMod 2) := !![1, 0, 1; 0, 1, 1]

theorem wide_rank : rank wide = 2 := by decide +kernel

/-- A tall matrix of full column rank. -/
def tall : Matrix (Fin 3) (Fin 2) (ZMod 2) := !![1, 0; 0, 1; 1, 1]

theorem tall_rank : rank tall = 2 := by decide +kernel

/-- Three equal nonzero columns. -/
def repeated : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![1, 1, 1; 0, 0, 0; 1, 1, 1]

theorem repeated_rank : rank repeated = 1 := by decide +kernel

/-- Distinct columns `e₀`, `e₁` and `e₀ + e₁`: the rank is smaller than both dimensions. -/
def dependent : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![1, 0, 1; 0, 1, 1; 0, 0, 0]

theorem dependent_rank : rank dependent = 2 := by decide +kernel

/-- The executed value determines Mathlib's rank of the dependent-column matrix. -/
theorem dependent_matrixRank : Matrix.rank dependent = 2 := by
  rw [← rank_eq_matrixRank]
  exact dependent_rank

/-- The dependent-column matrix has a one-dimensional kernel and is not injective. -/
theorem dependent_ker :
    Module.finrank (ZMod 2) (LinearMap.ker dependent.mulVecLin) = 1 ∧
      ¬ Function.Injective dependent.mulVecLin := by
  have h := rank_add_finrank_ker dependent
  rw [dependent_rank] at h
  have hk : Module.finrank (ZMod 2) (LinearMap.ker dependent.mulVecLin) = 1 := by omega
  refine ⟨hk, fun hinj => ?_⟩
  rw [LinearMap.ker_eq_bot.mpr hinj, finrank_bot] at hk
  omega

/-- The tall matrix has trivial kernel, so it is injective, while its rank is below its height. -/
theorem tall_injective :
    Function.Injective tall.mulVecLin ∧ Matrix.rank tall < 3 := by
  have h := rank_add_finrank_ker tall
  rw [tall_rank] at h
  have hk : Module.finrank (ZMod 2) (LinearMap.ker tall.mulVecLin) = 0 := by omega
  refine ⟨LinearMap.ker_eq_bot.mp (Submodule.finrank_eq_zero.mp hk), ?_⟩
  rw [← rank_eq_matrixRank, tall_rank]
  decide

end TDA.Persistence.Reduction.F2Matrix.Examples
