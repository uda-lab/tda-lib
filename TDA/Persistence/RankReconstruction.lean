import TDA.Persistence.RankInvariant
import Mathlib.Algebra.BigOperators.Intervals

universe u
namespace TDA.Persistence
open scoped BigOperators
variable {N : ℕ} {k : Type u} [Field k]
variable (M : PModule.{u,0,u} k (Fin N))
variable [∀ i : Fin N, FiniteDimensional k (M.obj i)]

private theorem death_telescope (r : ℤ → ℤ → ℤ) (x c d : ℕ)
    (hcd : c ≤ d) :
    (∑ y ∈ Finset.Ioc c d,
      (r x ((y : ℤ) - 1) - r ((x : ℤ) - 1) ((y : ℤ) - 1) -
        r x y + r ((x : ℤ) - 1) y)) =
      (r x c - r ((x : ℤ) - 1) c) -
        (r x d - r ((x : ℤ) - 1) d) := by
  let F : ℕ → ℤ := fun n =>
    -(r x ((n : ℤ) - 1) - r ((x : ℤ) - 1) ((n : ℤ) - 1))
  have h := Finset.sum_Ico_sub F (show c + 1 ≤ d + 1 by omega)
  rw [Finset.Ico_add_one_add_one_eq_Ioc] at h
  convert h using 1
  · apply Finset.sum_congr rfl
    intro y hy
    dsimp [F]
    have hc : (y : ℤ) + 1 - 1 = (y : ℤ) := by omega
    rw [hc]
    ring
  · dsimp [F]
    have hc : (c : ℤ) + 1 - 1 = (c : ℤ) := by omega
    have hd : (d : ℤ) + 1 - 1 = (d : ℤ) := by omega
    rw [hc, hd]
    ring

private theorem birth_telescope (r : ℤ → ℤ → ℤ) (a b : ℕ) (t : ℤ)
    (hab : a ≤ b) :
    (∑ x ∈ Finset.Icc a b, (r x t - r ((x : ℤ) - 1) t)) =
      r b t - r ((a : ℤ) - 1) t := by
  let F : ℕ → ℤ := fun n => r ((n : ℤ) - 1) t
  have h := Finset.sum_Icc_sub hab F
  convert h using 1
  · apply Finset.sum_congr rfl
    intro x hx
    dsimp [F]
    have hc : (x : ℤ) + 1 - 1 = (x : ℤ) := by omega
    rw [hc]
  · dsimp [F]
    have hc : (b : ℤ) + 1 - 1 = (b : ℤ) := by omega
    rw [hc]

private theorem rectangle_telescope (r : ℤ → ℤ → ℤ)
    (a b c d : ℕ) (hab : a ≤ b) (hcd : c ≤ d) :
    (∑ x ∈ Finset.Icc a b, ∑ y ∈ Finset.Ioc c d,
      (r x ((y : ℤ) - 1) - r ((x : ℤ) - 1) ((y : ℤ) - 1) -
        r x y + r ((x : ℤ) - 1) y)) =
      r b c - r ((a : ℤ) - 1) c - r b d + r ((a : ℤ) - 1) d := by
  calc
    _ = ∑ x ∈ Finset.Icc a b,
        ((r x c - r ((x : ℤ) - 1) c) -
          (r x d - r ((x : ℤ) - 1) d)) := by
      apply Finset.sum_congr rfl
      intro x hx
      exact death_telescope r x c d hcd
    _ = _ := by
      rw [Finset.sum_sub_distrib,
        birth_telescope r a b c hab, birth_telescope r a b d hab]
      ring

theorem moduleMultiplicityInteger_sum_rectangle
    (a b c d : ℕ) (hab : a ≤ b) (hbc : b ≤ c)
    (hcd : c ≤ d) (hd : d ≤ N) :
    (∑ x ∈ Finset.Icc a b, ∑ y ∈ Finset.Ioc c d,
      moduleMultiplicityInteger M x y) =
      moduleRankInteger M (b : ℤ) (c : ℤ) -
      moduleRankInteger M ((a : ℤ) - 1) (c : ℤ) -
      moduleRankInteger M (b : ℤ) (d : ℤ) +
      moduleRankInteger M ((a : ℤ) - 1) (d : ℤ) := by
  clear hbc hd
  exact rectangle_telescope (moduleRankInteger M) a b c d hab hcd

theorem structureMapRank_eq_sum_moduleMultiplicityInteger
    (i j : Fin N) (hij : i ≤ j) :
    (structureMapRank M i j hij : ℤ) =
      ∑ b ∈ Finset.range (i.val + 1), ∑ d ∈ Finset.Ioc j.val N,
        moduleMultiplicityInteger M b d := by
  have h := moduleMultiplicityInteger_sum_rectangle M 0 i.val j.val N
    (Nat.zero_le _) (Fin.le_iff_val_le_val.mp hij) (Nat.le_of_lt j.isLt) (le_refl N)
  rw [← Nat.range_succ_eq_Icc_zero] at h
  have hsource := moduleRankInteger_neg_one M (j.val : ℤ)
  have hsourceN := moduleRankInteger_neg_one M (N : ℤ)
  have htarget := moduleRankInteger_at_size M (i.val : ℤ)
  have hrank := moduleRankInteger_fin M i j hij
  conv at h => rhs; simp only [Nat.cast_zero, zero_sub]
  rw [hsource, hsourceN, htarget, hrank] at h
  conv at h => rhs; simp only [sub_zero, add_zero]
  exact h.symm

end TDA.Persistence
