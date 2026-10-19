import TDA.Persistence.FinitePBoundaryTransport
import Mathlib.Analysis.MeanInequalitiesPow

/-!
# Comparison of finite real-exponent distances

For real `p ≥ 1`, the unnormalized unit-occurrence optima satisfy
`dₚ ≤ d₁ ≤ N^(1 - 1/p) dₚ`, where `N` counts both occurrence families.
The proof uses the charge vector of each matching, then chooses a minimizer
separately for each inequality. Plan optima inherit the comparison from their
proved equality with matching optima; fractional candidates are not compared.

The algebra applies to arbitrary real pairs. Its persistence interpretation uses
positive lifetimes, finite deaths, unit mass and the maximum ground norm, with
no essential occurrences. Empty occurrence types are included.

For `1 ≤ r ≤ s`, the same charge vector gives
`dₛ ≤ dᵣ ≤ N^(1/r - 1/s) dₛ`. Apply the first-order vector estimates
to the charges raised to `r`, at exponent `s/r`, and then take the `r` root.
The ground norm remains fixed as the exponent changes.
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

-- Nonnegative bases suffice for power composition, including empty sums and N=0.
private theorem root_sum_rpow_comparison {K : Type*} [Fintype K] (f : K → ℝ)
    {r s : ℝ} (hr : 1 ≤ r) (hrs : r ≤ s) (hf : ∀ k, 0 ≤ f k) :
    (∑ k, f k ^ s) ^ s⁻¹ ≤ (∑ k, f k ^ r) ^ r⁻¹ ∧
      (∑ k, f k ^ r) ^ r⁻¹ ≤
        (Fintype.card K : ℝ) ^ (r⁻¹ - s⁻¹) * (∑ k, f k ^ s) ^ s⁻¹ := by
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hspos : 0 < s := lt_of_lt_of_le hrpos hrs
  have hq : 1 ≤ s / r := (le_div_iff₀ hrpos).mpr (by simpa using hrs)
  have hmul : r * (s / r) = s := by field_simp
  have hinv : (s / r)⁻¹ * r⁻¹ = s⁻¹ := by
    field_simp
  have hexp : (1 - (s / r)⁻¹) * r⁻¹ = r⁻¹ - s⁻¹ := by
    rw [sub_mul, one_mul, hinv]
  have hpowers : ∑ k, (f k ^ r) ^ (s / r) = ∑ k, f k ^ s := by
    apply Finset.sum_congr rfl
    intro k _
    rw [← Real.rpow_mul (hf k), hmul]
  have hsum : 0 ≤ ∑ k, f k ^ s :=
    Finset.sum_nonneg fun k _ => Real.rpow_nonneg (hf k) s
  constructor
  · have h := Real.rpow_le_rpow
      (Real.rpow_nonneg (Finset.sum_nonneg fun k _ =>
        Real.rpow_nonneg (Real.rpow_nonneg (hf k) r) (s / r)) _)
      (root_sum_rpow_le_sum (fun k => f k ^ r) hq
        (fun k => Real.rpow_nonneg (hf k) r)) (inv_nonneg.mpr hrpos.le)
    rw [hpowers, ← Real.rpow_mul hsum, hinv] at h
    exact h
  · have h := Real.rpow_le_rpow
      (Finset.sum_nonneg fun k _ => Real.rpow_nonneg (hf k) r)
      (sum_le_card_rpow_mul_root (fun k => f k ^ r) hq
        (fun k => Real.rpow_nonneg (hf k) r)) (inv_nonneg.mpr hrpos.le)
    rw [hpowers, Real.mul_rpow (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      (Real.rpow_nonneg hsum _), ← Real.rpow_mul (Nat.cast_nonneg _), hexp,
      ← Real.rpow_mul hsum, hinv] at h
    exact h

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

private theorem root_totalFinitePowerCost_comparison
    (M : OccurrenceMatching I J PEmpty.{1} PEmpty.{1}) {r s : ℝ}
    (hr : 1 ≤ r) (hrs : r ≤ s) (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    M.totalFinitePowerCost s x y ^ s⁻¹ ≤ M.totalFinitePowerCost r x y ^ r⁻¹ ∧
      M.totalFinitePowerCost r x y ^ r⁻¹ ≤
        ((Fintype.card I + Fintype.card J : ℕ) : ℝ) ^ (r⁻¹ - s⁻¹) *
          M.totalFinitePowerCost s x y ^ s⁻¹ := by
  rw [M.totalFinitePowerCost_eq_comparisonCharges
    (ne_of_gt (lt_of_lt_of_le zero_lt_one (hr.trans hrs))),
    M.totalFinitePowerCost_eq_comparisonCharges (ne_of_gt (lt_of_lt_of_le zero_lt_one hr))]
  simpa only [Fintype.card_sum] using
    root_sum_rpow_comparison _ hr hrs (M.comparisonCharge_nonneg x y)

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

/-- Changing the exponent may change the optimizer; use a minimizer at `r`. -/
theorem finitePMatchingCost_le_of_exponent_le {r s : ℝ} (hr : 1 ≤ r) (hrs : r ≤ s)
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    finitePMatchingCost s x y ≤ finitePMatchingCost r x y := by
  obtain ⟨M, hM⟩ := exists_minimizing_pMatching r x y
  exact (finitePMatchingCost_le_matching (hr.trans hrs) x y M).trans
    ((M.root_totalFinitePowerCost_comparison hr hrs x y).1.trans_eq hM)

/-- Use a separate minimizer at `s`; both occurrence families count in the factor. -/
theorem finitePMatchingCost_le_card_rpow_mul_of_exponent_le {r s : ℝ}
    (hr : 1 ≤ r) (hrs : r ≤ s) (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    finitePMatchingCost r x y ≤
      ((Fintype.card I + Fintype.card J : ℕ) : ℝ) ^ (r⁻¹ - s⁻¹) *
        finitePMatchingCost s x y := by
  obtain ⟨M, hM⟩ := exists_minimizing_pMatching s x y
  exact (finitePMatchingCost_le_matching hr x y M).trans
    (by simpa only [hM] using (M.root_totalFinitePowerCost_comparison hr hrs x y).2)

/-- Antitonicity of the actual real-plan optimum, with linear transported masses. -/
theorem finitePBoundaryTransportCost_le_of_exponent_le {r s : ℝ}
    (hr : 1 ≤ r) (hrs : r ≤ s) (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    finitePBoundaryTransportCost s x y ≤ finitePBoundaryTransportCost r x y := by
  rw [finitePBoundaryTransportCost_eq_matchingCost, finitePBoundaryTransportCost_eq_matchingCost]
  exact finitePMatchingCost_le_of_exponent_le hr hrs x y

/-- The finite cardinal comparison concerns optimized plans, including empty families. -/
theorem finitePBoundaryTransportCost_le_card_rpow_mul_of_exponent_le {r s : ℝ}
    (hr : 1 ≤ r) (hrs : r ≤ s) (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    finitePBoundaryTransportCost r x y ≤
      ((Fintype.card I + Fintype.card J : ℕ) : ℝ) ^ (r⁻¹ - s⁻¹) *
        finitePBoundaryTransportCost s x y := by
  rw [finitePBoundaryTransportCost_eq_matchingCost, finitePBoundaryTransportCost_eq_matchingCost]
  exact finitePMatchingCost_le_card_rpow_mul_of_exponent_le hr hrs x y

/-- The unnormalized unit-occurrence matching distance decreases on real exponents ≥ 1. -/
theorem finitePMatchingCost_antitoneOn (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    AntitoneOn (fun p : ℝ => finitePMatchingCost p x y) (Set.Ici 1) := by
  intro r hr s _ hrs
  exact finitePMatchingCost_le_of_exponent_le hr hrs x y

/-- The actual finite real-plan distance decreases on real exponents ≥ 1. -/
theorem finitePBoundaryTransportCost_antitoneOn (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    AntitoneOn (fun p : ℝ => finitePBoundaryTransportCost p x y) (Set.Ici 1) := by
  intro r hr s _ hrs
  exact finitePBoundaryTransportCost_le_of_exponent_le hr hrs x y

end TDA.Persistence
