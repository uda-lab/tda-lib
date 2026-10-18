import TDA.Persistence.FinitePBoundaryTransport
import TDA.Persistence.DiagramBottleneckScaling

/-!
# Common diagonal translation and scaling of finite p-costs

At real exponents `p ≥ 1`, adding the same real number to every birth and death
preserves finite matching and boundary-reservoir costs. Multiplying all coordinates
by `a ≥ 0` multiplies the powered optimum by `a ^ p` and its root by `a`.

These are definition-derived extensions of the finite, unit-occurrence cost model.
The raw-coordinate scaling law includes zero: pairs then lie on the diagonal and
have zero cost. It does not extend the positive-lifetime operation `Diagram.scale`
to zero. A common diagonal translation preserves positive lifetimes for every real
shift; an arbitrary plane translation need not preserve boundary costs.
-/

noncomputable section
namespace TDA.Persistence
open scoped Classical

variable {I J : Type*} [Fintype I] [Fintype J]

namespace OccurrenceMatching

/-- Moving every coordinate along the diagonal preserves every matching charge. -/
theorem totalFinitePowerCost_translate
    (M : OccurrenceMatching I J PEmpty.{1} PEmpty.{1}) (p : ℝ)
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) (t : ℝ) :
    M.totalFinitePowerCost p (Prod.map (· + t) (· + t) ∘ x)
      (Prod.map (· + t) (· + t) ∘ y) = M.totalFinitePowerCost p x y := by
  simp only [totalFinitePowerCost, finitePairCost, diagonalCost,
    Function.comp_apply, Prod.map_fst, Prod.map_snd, add_sub_add_right_eq_sub]

/-- Scaling coordinates scales the powered coefficients, leaving label masses unchanged. -/
theorem totalFinitePowerCost_scale
    (M : OccurrenceMatching I J PEmpty.{1} PEmpty.{1}) (p : ℝ)
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) {a : ℝ} (ha : 0 ≤ a) :
    M.totalFinitePowerCost p (scaleFinitePair a ∘ x) (scaleFinitePair a ∘ y) =
      a ^ p * M.totalFinitePowerCost p x y := by
  unfold totalFinitePowerCost totalBoundaryCost
  simp only [Function.comp_apply, finitePairCost_scale _ _ ha, diagonalCost_scale _ ha,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal ha,
    Real.mul_rpow ha ENNReal.toReal_nonneg]
  rw [mul_add, Finset.mul_sum, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    cases M.finite i <;> rfl
  · apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> simp

end OccurrenceMatching

/-- Common diagonal translation preserves the attained powered matching minimum. -/
theorem finitePowerMatchingCost_translate (p : ℝ)
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) (t : ℝ) :
    finitePowerMatchingCost p (Prod.map (· + t) (· + t) ∘ x)
      (Prod.map (· + t) (· + t) ∘ y) = finitePowerMatchingCost p x y := by
  unfold finitePowerMatchingCost
  exact iInf_congr fun M => M.totalFinitePowerCost_translate p x y t

/-- Common diagonal translation preserves the rooted finite matching cost. -/
theorem finitePMatchingCost_translate (p : ℝ)
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) (t : ℝ) :
    finitePMatchingCost p (Prod.map (· + t) (· + t) ∘ x)
      (Prod.map (· + t) (· + t) ∘ y) = finitePMatchingCost p x y := by
  simp only [finitePMatchingCost, finitePowerMatchingCost_translate]

/-- Nonnegative scaling commutes with the powered minimum, including at scale zero. -/
theorem finitePowerMatchingCost_scale (p : ℝ)
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) {a : ℝ} (ha : 0 ≤ a) :
    finitePowerMatchingCost p (scaleFinitePair a ∘ x) (scaleFinitePair a ∘ y) =
      a ^ p * finitePowerMatchingCost p x y := by
  obtain ⟨M, hM⟩ := exists_minimizing_powerMatching p x y
  obtain ⟨N, hN⟩ := exists_minimizing_powerMatching p
    (scaleFinitePair a ∘ x) (scaleFinitePair a ∘ y)
  apply le_antisymm
  · calc
      _ ≤ M.totalFinitePowerCost p (scaleFinitePair a ∘ x) (scaleFinitePair a ∘ y) :=
        finitePowerMatchingCost_le_matching _ _ _ M
      _ = _ := by rw [M.totalFinitePowerCost_scale p x y ha, hM]
  · calc
      _ ≤ a ^ p * N.totalFinitePowerCost p x y :=
        mul_le_mul_of_nonneg_left (finitePowerMatchingCost_le_matching _ _ _ N)
          (Real.rpow_nonneg ha p)
      _ = _ := by rw [← N.totalFinitePowerCost_scale p x y ha, hN]

/-- A nonnegative coordinate scale multiplies the real-p rooted distance by that scale. -/
theorem finitePMatchingCost_scale {p : ℝ} (hp : 1 ≤ p)
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) {a : ℝ} (ha : 0 ≤ a) :
    finitePMatchingCost p (scaleFinitePair a ∘ x) (scaleFinitePair a ∘ y) =
      a * finitePMatchingCost p x y := by
  have hp0 : p ≠ 0 := ne_of_gt (zero_lt_one.trans_le hp)
  rw [finitePMatchingCost, finitePowerMatchingCost_scale p x y ha,
    Real.mul_rpow (Real.rpow_nonneg ha p) (finitePowerMatchingCost_nonneg p x y),
    Real.rpow_rpow_inv ha hp0]
  rfl

/-- Common diagonal translation preserves the powered finite real-plan optimum. -/
theorem finitePowerBoundaryTransportCost_translate (p : ℝ)
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) (t : ℝ) :
    finitePowerBoundaryTransportCost p (Prod.map (· + t) (· + t) ∘ x)
      (Prod.map (· + t) (· + t) ∘ y) = finitePowerBoundaryTransportCost p x y := by
  simp only [finitePowerBoundaryTransportCost_eq_matchingCost,
    finitePowerMatchingCost_translate]

/-- Common diagonal translation preserves the rooted finite real-plan optimum. -/
theorem finitePBoundaryTransportCost_translate (p : ℝ)
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) (t : ℝ) :
    finitePBoundaryTransportCost p (Prod.map (· + t) (· + t) ∘ x)
      (Prod.map (· + t) (· + t) ∘ y) = finitePBoundaryTransportCost p x y := by
  simp only [finitePBoundaryTransportCost_eq_matchingCost, finitePMatchingCost_translate]

/-- Scaling multiplies the powered finite real-plan optimum by the powered scale. -/
theorem finitePowerBoundaryTransportCost_scale (p : ℝ)
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) {a : ℝ} (ha : 0 ≤ a) :
    finitePowerBoundaryTransportCost p (scaleFinitePair a ∘ x) (scaleFinitePair a ∘ y) =
      a ^ p * finitePowerBoundaryTransportCost p x y := by
  simp only [finitePowerBoundaryTransportCost_eq_matchingCost,
    finitePowerMatchingCost_scale p x y ha]

/-- Scaling multiplies the rooted finite real-plan optimum by the nonnegative scale. -/
theorem finitePBoundaryTransportCost_scale {p : ℝ} (hp : 1 ≤ p)
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) {a : ℝ} (ha : 0 ≤ a) :
    finitePBoundaryTransportCost p (scaleFinitePair a ∘ x) (scaleFinitePair a ∘ y) =
      a * finitePBoundaryTransportCost p x y := by
  simp only [finitePBoundaryTransportCost_eq_matchingCost, finitePMatchingCost_scale hp x y ha]

end TDA.Persistence
