import TDA.Persistence.FiniteMatchingCost
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Finite matching costs for real exponents

Pair and boundary distances are raised to a real exponent before summing. The
finite matching family contains the all-unmatched matching, so its infimum is an
attained minimum. At exponents at least one, taking the reciprocal-power root
after minimizing agrees with minimizing the rooted candidate costs.

The supporting powered algebra is defined for real exponents; the persistence
interpretation uses `1 ≤ p`, positive lifetimes, finite deaths and unit mass per
occurrence. `FinitePMatchingCostLaws` supplies rooted distance laws for `1 ≤ p`.
No quotient or metric-space instance on raw occurrence presentations is supplied.
-/

noncomputable section
namespace TDA.Persistence
open scoped Classical

namespace OccurrenceMatching
variable {I J : Type*} [Fintype I] [Fintype J]

/-- Unnormalized sum of powered pair/deletion/insertion distances.
Occurrence multiplicity is unchanged by the exponent. -/
def totalFinitePowerCost (M : OccurrenceMatching I J PEmpty.{1} PEmpty.{1})
    (p : ℝ) (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) : ℝ :=
  M.totalBoundaryCost (fun i j => (finitePairCost (x i) (y j)).toReal ^ p)
    (fun i => (diagonalCost (x i)).toReal ^ p) (fun j => (diagonalCost (y j)).toReal ^ p)

theorem totalFinitePowerCost_nonneg (M : OccurrenceMatching I J PEmpty.{1} PEmpty.{1})
    (p : ℝ) (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) : 0 ≤ M.totalFinitePowerCost p x y :=
  M.totalBoundaryCost_nonneg _ _ _
    (fun _ _ => Real.rpow_nonneg ENNReal.toReal_nonneg _)
    (fun _ => Real.rpow_nonneg ENNReal.toReal_nonneg _)
    (fun _ => Real.rpow_nonneg ENNReal.toReal_nonneg _)

@[simp] theorem totalFinitePowerCost_one (M : OccurrenceMatching I J PEmpty.{1} PEmpty.{1})
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    M.totalFinitePowerCost 1 x y = M.totalFiniteCost x y := by
  unfold totalFinitePowerCost totalBoundaryCost totalFiniteCost
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    cases M.finite i <;> simp only [Real.rpow_one]
  · simp only [Real.rpow_one]

/-- Transporting labels preserves each powered coefficient and the complete sum. -/
theorem totalFinitePowerCost_relabel {I' J' : Type*} [Fintype I'] [Fintype J']
    (u : I' ≃ I) (v : J' ≃ J) (M : OccurrenceMatching I J PEmpty.{1} PEmpty.{1})
    (p : ℝ) (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    (M.relabel u v (Equiv.refl _) (Equiv.refl _)).totalFinitePowerCost p (x ∘ u) (y ∘ v) =
      M.totalFinitePowerCost p x y :=
  totalBoundaryCost_relabel u v M
    (fun i j => (finitePairCost (x i) (y j)).toReal ^ p)
    (fun i => (diagonalCost (x i)).toReal ^ p)
    (fun j => (diagonalCost (y j)).toReal ^ p)

end OccurrenceMatching

variable {I J : Type*} [Fintype I] [Fintype J]

/-- Attained powered matching minimum, before taking a reciprocal-power root. -/
def finitePowerMatchingCost (p : ℝ) (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) : ℝ :=
  ⨅ M : OccurrenceMatching I J PEmpty.{1} PEmpty.{1}, M.totalFinitePowerCost p x y

/-- Root of the optimized powered sum; the PD exponent domain is `1 ≤ p`. -/
def finitePMatchingCost (p : ℝ) (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) : ℝ :=
  finitePowerMatchingCost p x y ^ p⁻¹

theorem exists_minimizing_powerMatching (p : ℝ) (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    ∃ M : OccurrenceMatching I J PEmpty.{1} PEmpty.{1},
      M.totalFinitePowerCost p x y = finitePowerMatchingCost p x y := by
  let : Nonempty (OccurrenceMatching I J PEmpty.{1} PEmpty.{1}) :=
    occurrenceMatching_nonempty_iff.mpr (by simp)
  exact exists_eq_ciInf_of_finite

theorem finitePowerMatchingCost_le_matching (p : ℝ) (x : I → ℝ × ℝ) (y : J → ℝ × ℝ)
    (M : OccurrenceMatching I J PEmpty.{1} PEmpty.{1}) :
    finitePowerMatchingCost p x y ≤ M.totalFinitePowerCost p x y :=
  ciInf_le ⟨0, by rintro _ ⟨N, rfl⟩; exact N.totalFinitePowerCost_nonneg p x y⟩ M

theorem le_finitePowerMatchingCost_iff (p : ℝ) (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) (c : ℝ) :
    c ≤ finitePowerMatchingCost p x y ↔
      ∀ M : OccurrenceMatching I J PEmpty.{1} PEmpty.{1}, c ≤ M.totalFinitePowerCost p x y := by
  constructor
  · intro h M
    exact h.trans (finitePowerMatchingCost_le_matching p x y M)
  · intro h
    obtain ⟨M, hM⟩ := exists_minimizing_powerMatching p x y
    exact hM ▸ h M

theorem finitePowerMatchingCost_nonneg (p : ℝ) (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    0 ≤ finitePowerMatchingCost p x y :=
  (le_finitePowerMatchingCost_iff p x y 0).mpr fun M => M.totalFinitePowerCost_nonneg p x y

theorem finitePMatchingCost_nonneg (p : ℝ) (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    0 ≤ finitePMatchingCost p x y := Real.rpow_nonneg (finitePowerMatchingCost_nonneg p x y) _

/-- A rooted candidate bounds the rooted minimum; coefficients were optimized first. -/
theorem finitePMatchingCost_le_matching {p : ℝ} (hp : 1 ≤ p)
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ)
    (M : OccurrenceMatching I J PEmpty.{1} PEmpty.{1}) :
    finitePMatchingCost p x y ≤ M.totalFinitePowerCost p x y ^ p⁻¹ :=
  Real.rpow_le_rpow (finitePowerMatchingCost_nonneg p x y)
    (finitePowerMatchingCost_le_matching p x y M) (inv_nonneg.mpr (le_trans zero_le_one hp))

/-- The matching attaining the powered minimum also realizes its reciprocal-power root. -/
theorem exists_minimizing_pMatching (p : ℝ) (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    ∃ M : OccurrenceMatching I J PEmpty.{1} PEmpty.{1},
      M.totalFinitePowerCost p x y ^ p⁻¹ = finitePMatchingCost p x y := by
  obtain ⟨M, hM⟩ := exists_minimizing_powerMatching p x y
  exact ⟨M, by rw [hM]; rfl⟩

/-- Attainment justifies placing the root inside the infimum, without a limit argument. -/
theorem finitePMatchingCost_eq_iInf {p : ℝ} (hp : 1 ≤ p)
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    finitePMatchingCost p x y =
      ⨅ M : OccurrenceMatching I J PEmpty.{1} PEmpty.{1}, M.totalFinitePowerCost p x y ^ p⁻¹ := by
  let : Nonempty (OccurrenceMatching I J PEmpty.{1} PEmpty.{1}) :=
    occurrenceMatching_nonempty_iff.mpr (by simp)
  have hbd : BddBelow (Set.range fun M : OccurrenceMatching I J PEmpty.{1} PEmpty.{1} =>
      M.totalFinitePowerCost p x y ^ p⁻¹) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨M, rfl⟩
    exact Real.rpow_nonneg (M.totalFinitePowerCost_nonneg p x y) _
  apply le_antisymm
  · exact le_ciInf fun M => finitePMatchingCost_le_matching hp x y M
  · obtain ⟨M, hM⟩ := exists_minimizing_pMatching p x y
    exact (ciInf_le hbd M).trans_eq hM

@[simp] theorem finitePowerMatchingCost_one (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    finitePowerMatchingCost 1 x y = finiteFirstOrderMatchingCost x y := by
  simp only [finitePowerMatchingCost, OccurrenceMatching.totalFinitePowerCost_one,
    finiteFirstOrderMatchingCost]

@[simp] theorem finitePMatchingCost_one (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    finitePMatchingCost 1 x y = finiteFirstOrderMatchingCost x y := by
  simp [finitePMatchingCost]

theorem finitePowerMatchingCost_of_isEmpty_right [IsEmpty J]
    (p : ℝ) (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    finitePowerMatchingCost p x y = ∑ i, (diagonalCost (x i)).toReal ^ p := by
  obtain ⟨M, hM⟩ := exists_minimizing_powerMatching p x y
  have hn (i : I) : M.finite i = none := by
    cases h : M.finite i with
    | none => rfl
    | some j => exact isEmptyElim j
  rw [← hM]
  simp [OccurrenceMatching.totalFinitePowerCost, OccurrenceMatching.totalBoundaryCost, hn]

theorem finitePowerMatchingCost_of_isEmpty_left [IsEmpty I]
    (p : ℝ) (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    finitePowerMatchingCost p x y = ∑ j, (diagonalCost (y j)).toReal ^ p := by
  obtain ⟨M, hM⟩ := exists_minimizing_powerMatching p x y
  rw [← hM]
  simp [OccurrenceMatching.totalFinitePowerCost, OccurrenceMatching.totalBoundaryCost]

@[simp] theorem finitePowerMatchingCost_empty [IsEmpty I] [IsEmpty J]
    (p : ℝ) (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) : finitePowerMatchingCost p x y = 0 := by
  rw [finitePowerMatchingCost_of_isEmpty_right]; exact Fintype.sum_empty _

theorem finitePMatchingCost_of_isEmpty_right [IsEmpty J]
    (p : ℝ) (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    finitePMatchingCost p x y = (∑ i, (diagonalCost (x i)).toReal ^ p) ^ p⁻¹ := by
  rw [finitePMatchingCost, finitePowerMatchingCost_of_isEmpty_right]

theorem finitePMatchingCost_of_isEmpty_left [IsEmpty I]
    (p : ℝ) (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    finitePMatchingCost p x y = (∑ j, (diagonalCost (y j)).toReal ^ p) ^ p⁻¹ := by
  rw [finitePMatchingCost, finitePowerMatchingCost_of_isEmpty_left]

@[simp] theorem finitePMatchingCost_empty [IsEmpty I] [IsEmpty J]
    {p : ℝ} (hp : 1 ≤ p) (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    finitePMatchingCost p x y = 0 := by
  rw [finitePMatchingCost, finitePowerMatchingCost_empty]
  exact Real.zero_rpow (inv_ne_zero (ne_of_gt (lt_of_lt_of_le zero_lt_one hp)))

theorem finitePowerMatchingCost_reindex {I' J' : Type*} [Fintype I'] [Fintype J']
    (u : I' ≃ I) (v : J' ≃ J) (p : ℝ) (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    finitePowerMatchingCost p (x ∘ u) (y ∘ v) = finitePowerMatchingCost p x y := by
  apply le_antisymm
  · obtain ⟨M, hM⟩ := exists_minimizing_powerMatching p x y
    calc
      _ ≤ (M.relabel u v (Equiv.refl _) (Equiv.refl _)).totalFinitePowerCost
          p (x ∘ u) (y ∘ v) := finitePowerMatchingCost_le_matching _ _ _ _
      _ = _ := by rw [M.totalFinitePowerCost_relabel, hM]
  · obtain ⟨N, hN⟩ := exists_minimizing_powerMatching p (x ∘ u) (y ∘ v)
    obtain ⟨M, hM⟩ :=
      (OccurrenceMatching.relabelEquiv u v (Equiv.refl PEmpty.{1})
        (Equiv.refl PEmpty.{1})).surjective N
    have hcost := M.totalFinitePowerCost_relabel u v p x y
    change M.relabel u v (Equiv.refl _) (Equiv.refl _) = N at hM
    rw [hM] at hcost
    calc
      _ ≤ M.totalFinitePowerCost p x y := finitePowerMatchingCost_le_matching _ _ _ _
      _ = _ := hcost.symm.trans hN

theorem finitePMatchingCost_reindex {I' J' : Type*} [Fintype I'] [Fintype J']
    (u : I' ≃ I) (v : J' ≃ J) (p : ℝ) (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    finitePMatchingCost p (x ∘ u) (y ∘ v) = finitePMatchingCost p x y := by
  simp only [finitePMatchingCost, finitePowerMatchingCost_reindex]

/-- For one occurrence on each side, pairing and deleting both are the two candidates. -/
theorem finitePowerMatchingCost_singleton (p : ℝ) (x y : ℝ × ℝ) :
    finitePowerMatchingCost p (fun _ : Fin 1 => x) (fun _ : Fin 1 => y) =
      min ((finitePairCost x y).toReal ^ p)
        ((diagonalCost x).toReal ^ p + (diagonalCost y).toReal ^ p) := by
  let pair : OccurrenceMatching (Fin 1) (Fin 1) PEmpty.{1} PEmpty.{1} :=
    ⟨fun i => some i, by intro i i' j hi hi'; simpa using hi.trans hi'.symm, Equiv.refl _⟩
  let delete : OccurrenceMatching (Fin 1) (Fin 1) PEmpty.{1} PEmpty.{1} :=
    ⟨fun _ => none, by simp, Equiv.refl _⟩
  apply le_antisymm
  · apply le_min
    · simpa [pair, OccurrenceMatching.totalFinitePowerCost, OccurrenceMatching.totalBoundaryCost]
        using finitePowerMatchingCost_le_matching p (fun _ => x) (fun _ => y) pair
    · simpa [delete, OccurrenceMatching.totalFinitePowerCost, OccurrenceMatching.totalBoundaryCost]
        using finitePowerMatchingCost_le_matching p (fun _ => x) (fun _ => y) delete
  · apply (le_finitePowerMatchingCost_iff p _ _ _).mpr
    intro M
    cases h : M.finite 0 with
    | none =>
      have hf (i : Fin 1) : M.finite i = none := by
        have hi : i = 0 := Subsingleton.elim _ _
        simpa only [hi] using h
      simp [OccurrenceMatching.totalFinitePowerCost, OccurrenceMatching.totalBoundaryCost, hf]
    | some j =>
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      have hf (i : Fin 1) : M.finite i = some 0 := by
        have hi : i = 0 := Subsingleton.elim _ _
        simpa only [hi] using h
      simp [OccurrenceMatching.totalFinitePowerCost, OccurrenceMatching.totalBoundaryCost, hf]

end TDA.Persistence
