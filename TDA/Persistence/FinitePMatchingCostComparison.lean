import TDA.Persistence.FinitePBoundaryTransport
import Mathlib.Analysis.MeanInequalitiesPow

/-!
# Finite p and first-order distance comparison

For real `p ≥ 1`, the unnormalized unit-occurrence optima satisfy
`dₚ ≤ d₁ ≤ N^(1 - 1/p) dₚ`, where `N` counts both occurrence families.
The proof uses the charge vector of each matching, then chooses a minimizer
separately for each inequality. Plan optima inherit the comparison from their
proved equality with matching optima; fractional candidates are not compared.

The algebra applies to arbitrary real pairs. Its persistence interpretation uses
positive lifetimes, finite deaths, unit mass and the maximum ground norm, with
no essential occurrences. Empty occurrence types are included.
-/

noncomputable section
namespace TDA.Persistence
open scoped Classical

private theorem sum_rpow_le_rpow_sum {K : Type*} (s : Finset K) (f : K → ℝ)
    {p : ℝ} (hp : 1 ≤ p) (hf : ∀ k ∈ s, 0 ≤ f k) :
    ∑ k ∈ s, f k ^ p ≤ (∑ k ∈ s, f k) ^ p := by
  induction s using Finset.induction_on with
  | empty => simp [Real.zero_rpow (ne_of_gt (lt_of_lt_of_le zero_lt_one hp))]
  | @insert k s hk ih =>
    have hfs : ∀ i ∈ s, 0 ≤ f i := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    rw [Finset.sum_insert hk, Finset.sum_insert hk]
    calc
      _ ≤ f k ^ p + (∑ i ∈ s, f i) ^ p := add_le_add le_rfl (ih hfs)
      _ ≤ _ := Real.add_rpow_le_rpow_add (hf k (Finset.mem_insert_self k s))
        (Finset.sum_nonneg hfs) hp

private theorem root_sum_rpow_le_sum {K : Type*} [Fintype K] (f : K → ℝ)
    {p : ℝ} (hp : 1 ≤ p) (hf : ∀ k, 0 ≤ f k) :
    (∑ k, f k ^ p) ^ p⁻¹ ≤ ∑ k, f k := by
  have h := Real.rpow_le_rpow
    (Finset.sum_nonneg fun k _ => Real.rpow_nonneg (hf k) p)
    (sum_rpow_le_rpow_sum Finset.univ f hp (fun k _ => hf k))
    (inv_nonneg.mpr (le_trans zero_le_one hp))
  simpa only [Real.rpow_rpow_inv (Finset.sum_nonneg fun k _ => hf k)
    (ne_of_gt (lt_of_lt_of_le zero_lt_one hp))] using h

private theorem sum_le_card_rpow_mul_root {K : Type*} [Fintype K] (f : K → ℝ)
    {p : ℝ} (hp : 1 ≤ p) (hf : ∀ k, 0 ≤ f k) :
    ∑ k, f k ≤ (Fintype.card K : ℝ) ^ (1 - p⁻¹) * (∑ k, f k ^ p) ^ p⁻¹ := by
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hp)
  have h := Real.rpow_le_rpow
    (Real.rpow_nonneg (Finset.sum_nonneg fun k _ => hf k) p)
    (Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg Finset.univ hp (fun k _ => hf k))
    (inv_nonneg.mpr (le_trans zero_le_one hp))
  rw [Real.rpow_rpow_inv (Finset.sum_nonneg fun k _ => hf k) hp0,
    Real.mul_rpow (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      (Finset.sum_nonneg fun k _ => Real.rpow_nonneg (hf k) p),
    ← Real.rpow_mul (Nat.cast_nonneg _)] at h
  have hexp : (p - 1) * p⁻¹ = 1 - p⁻¹ := by field_simp
  simpa only [Finset.card_univ, hexp] using h

namespace OccurrenceMatching
variable {I J : Type*} [Fintype I] [Fintype J]

-- A pair is charged at its source only. Selected targets contribute zero.
private def comparisonCharge (M : OccurrenceMatching I J PEmpty.{1} PEmpty.{1})
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) : I ⊕ J → ℝ
  | .inl i => match M.finite i with
    | some j => (finitePairCost (x i) (y j)).toReal
    | none => (diagonalCost (x i)).toReal
  | .inr j => if ∃ i, M.finite i = some j then 0 else (diagonalCost (y j)).toReal

omit [Fintype J] in
private theorem comparisonCharge_nonneg
    (M : OccurrenceMatching I J PEmpty.{1} PEmpty.{1})
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) (k : I ⊕ J) :
    0 ≤ comparisonCharge M x y k := by
  cases k with
  | inl i =>
    change 0 ≤ match M.finite i with
      | some j => (finitePairCost (x i) (y j)).toReal
      | none => (diagonalCost (x i)).toReal
    cases M.finite i <;> exact ENNReal.toReal_nonneg
  | inr j =>
    simp only [comparisonCharge]
    split_ifs
    · exact le_rfl
    · exact ENNReal.toReal_nonneg

private theorem totalFinitePowerCost_eq_comparisonCharges
    (M : OccurrenceMatching I J PEmpty.{1} PEmpty.{1}) {p : ℝ} (hp : p ≠ 0)
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    M.totalFinitePowerCost p x y = ∑ k, comparisonCharge M x y k ^ p := by
  rw [Fintype.sum_sum_type]
  unfold totalFinitePowerCost totalBoundaryCost
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    cases h : M.finite i <;> simp only [comparisonCharge, h]
  · apply Finset.sum_congr rfl
    intro j _
    simp only [comparisonCharge]
    split_ifs <;> simp only [Real.zero_rpow hp]

private theorem totalFiniteCost_eq_comparisonCharges
    (M : OccurrenceMatching I J PEmpty.{1} PEmpty.{1})
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    M.totalFiniteCost x y = ∑ k, comparisonCharge M x y k := by
  simpa only [totalFinitePowerCost_one, Real.rpow_one] using
    M.totalFinitePowerCost_eq_comparisonCharges one_ne_zero x y

private theorem root_totalFinitePowerCost_le_totalFiniteCost
    (M : OccurrenceMatching I J PEmpty.{1} PEmpty.{1}) {p : ℝ} (hp : 1 ≤ p)
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    M.totalFinitePowerCost p x y ^ p⁻¹ ≤ M.totalFiniteCost x y := by
  rw [M.totalFinitePowerCost_eq_comparisonCharges
    (ne_of_gt (lt_of_lt_of_le zero_lt_one hp)), M.totalFiniteCost_eq_comparisonCharges]
  exact root_sum_rpow_le_sum _ hp (M.comparisonCharge_nonneg x y)

private theorem totalFiniteCost_le_card_rpow_mul_root
    (M : OccurrenceMatching I J PEmpty.{1} PEmpty.{1}) {p : ℝ} (hp : 1 ≤ p)
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    M.totalFiniteCost x y ≤ ((Fintype.card I + Fintype.card J : ℕ) : ℝ) ^ (1 - p⁻¹) *
      M.totalFinitePowerCost p x y ^ p⁻¹ := by
  rw [M.totalFinitePowerCost_eq_comparisonCharges
    (ne_of_gt (lt_of_lt_of_le zero_lt_one hp)), M.totalFiniteCost_eq_comparisonCharges]
  simpa only [Fintype.card_sum] using
    sum_le_card_rpow_mul_root _ hp (M.comparisonCharge_nonneg x y)

end OccurrenceMatching
variable {I J : Type*} [Fintype I] [Fintype J]

/-- Use a first-order minimizer to bound the rooted p minimum. -/
theorem finitePMatchingCost_le_firstOrder {p : ℝ} (hp : 1 ≤ p)
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    finitePMatchingCost p x y ≤ finiteFirstOrderMatchingCost x y := by
  obtain ⟨M, hM⟩ := exists_minimizing_occurrenceMatching x y
  exact (finitePMatchingCost_le_matching hp x y M).trans
    ((M.root_totalFinitePowerCost_le_totalFiniteCost hp x y).trans_eq hM)

/-- Use a p minimizer; the cardinal factor counts both label families, including empties. -/
theorem finiteFirstOrderMatchingCost_le_card_rpow_mul_p {p : ℝ} (hp : 1 ≤ p)
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    finiteFirstOrderMatchingCost x y ≤
      ((Fintype.card I + Fintype.card J : ℕ) : ℝ) ^ (1 - p⁻¹) * finitePMatchingCost p x y := by
  obtain ⟨M, hM⟩ := exists_minimizing_pMatching p x y
  exact (finiteFirstOrderMatchingCost_le_totalFiniteCost x y M).trans
    (by simpa only [hM] using M.totalFiniteCost_le_card_rpow_mul_root hp x y)

/-- Comparison of actual finite-real-plan optima, via the proved assignment equality. -/
theorem finitePBoundaryTransportCost_le_firstOrder {p : ℝ} (hp : 1 ≤ p)
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    finitePBoundaryTransportCost p x y ≤ finiteFirstOrderBoundaryTransportCost x y := by
  rw [finitePBoundaryTransportCost_eq_matchingCost,
    finiteFirstOrderBoundaryTransportCost_eq_matchingCost]
  exact finitePMatchingCost_le_firstOrder hp x y

/-- The cardinal upper comparison holds for optimized real plans, without a chosen plan. -/
theorem finiteFirstOrderBoundaryTransportCost_le_card_rpow_mul_p {p : ℝ} (hp : 1 ≤ p)
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    finiteFirstOrderBoundaryTransportCost x y ≤
      ((Fintype.card I + Fintype.card J : ℕ) : ℝ) ^ (1 - p⁻¹) *
        finitePBoundaryTransportCost p x y := by
  rw [finitePBoundaryTransportCost_eq_matchingCost,
    finiteFirstOrderBoundaryTransportCost_eq_matchingCost]
  exact finiteFirstOrderMatchingCost_le_card_rpow_mul_p hp x y

end TDA.Persistence
