import TDA.Persistence.FinitePMatchingCost
import TDA.Persistence.FiniteBoundaryTransport

/-!
# Finite boundary transport with real matching exponents

Costs raise geometric distances to `p`, while real mass coefficients and boundary
residuals remain linear. The existing assignment/Birkhoff bridge proves equality
with the powered partial-matching minimum. At `1 ≤ p`, the rooted optimum also
minimizes rooted candidate costs. A minimizing incidence plan is constructed from
an actual powered-cost minimizing matching; first-order optimizers are not reused.

These are finite unit-occurrence reservoir matrices. The maximum ground norm is
independent of the real matching exponent. The finite cost-matrix adaptation of
Divol–Lacombe and Lacombe–Cuturi–Oudot does not identify all Radon couplings or
supply general-exponent metric laws.
-/

noncomputable section
namespace TDA.Persistence
open scoped Classical

namespace FiniteBoundaryPlan
variable {I J : Type*} [Fintype I] [Fintype J]

/-- Power only the distance coefficients; transported and residual masses stay linear. -/
def powerCost (a : FiniteBoundaryPlan I J) (p : ℝ)
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) : ℝ :=
  a.linearCost (fun i j => (finitePairCost (x i) (y j)).toReal ^ p)
    (fun i => (diagonalCost (x i)).toReal ^ p) (fun j => (diagonalCost (y j)).toReal ^ p)

theorem powerCost_nonneg (a : FiniteBoundaryPlan I J) (p : ℝ)
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) : 0 ≤ a.powerCost p x y :=
  a.linearCost_nonneg _ _ _
    (fun _ _ => Real.rpow_nonneg ENNReal.toReal_nonneg _)
    (fun _ => Real.rpow_nonneg ENNReal.toReal_nonneg _)
    (fun _ => Real.rpow_nonneg ENNReal.toReal_nonneg _)

@[simp] theorem powerCost_one (a : FiniteBoundaryPlan I J)
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) : a.powerCost 1 x y = a.cost x y := by
  simp only [powerCost, linearCost, Real.rpow_one, cost]

theorem powerCost_ofMatching (M : OccurrenceMatching I J PEmpty.{1} PEmpty.{1}) (p : ℝ)
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    (ofMatching M).powerCost p x y = M.totalFinitePowerCost p x y :=
  linearCost_ofMatching M _ _ _

/-- A genuine partial matching is no more expensive than any fractional real plan. -/
theorem exists_powerMatching_cost_le (a : FiniteBoundaryPlan I J) (p : ℝ)
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    ∃ M : OccurrenceMatching I J PEmpty.{1} PEmpty.{1},
      M.totalFinitePowerCost p x y ≤ a.powerCost p x y :=
  a.exists_matching_linearCost_le _ _ _

theorem matchingPowerCost_le_powerCost (a : FiniteBoundaryPlan I J) (p : ℝ)
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    finitePowerMatchingCost p x y ≤ a.powerCost p x y := by
  obtain ⟨M, hM⟩ := a.exists_powerMatching_cost_le p x y
  exact (finitePowerMatchingCost_le_matching p x y M).trans hM

end FiniteBoundaryPlan

variable {I J : Type*} [Fintype I] [Fintype J]

/-- Real infimum of powered costs over every feasible finite reservoir matrix. -/
def finitePowerBoundaryTransportCost (p : ℝ) (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) : ℝ :=
  ⨅ a : FiniteBoundaryPlan I J, a.powerCost p x y

/-- Reciprocal-power root after optimization. Its PD exponent domain is `1 ≤ p`. -/
def finitePBoundaryTransportCost (p : ℝ) (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) : ℝ :=
  finitePowerBoundaryTransportCost p x y ^ p⁻¹

theorem finitePowerBoundaryTransportCost_le_plan (p : ℝ)
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) (a : FiniteBoundaryPlan I J) :
    finitePowerBoundaryTransportCost p x y ≤ a.powerCost p x y :=
  ciInf_le ⟨0, by rintro _ ⟨b, rfl⟩; exact b.powerCost_nonneg p x y⟩ a

/-- Finite assignment equality, with the matching exponent independent of ground norm. -/
theorem finitePowerBoundaryTransportCost_eq_matchingCost (p : ℝ)
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    finitePowerBoundaryTransportCost p x y = finitePowerMatchingCost p x y := by
  apply le_antisymm
  · obtain ⟨M, hM⟩ := exists_minimizing_powerMatching p x y
    calc
      _ ≤ (FiniteBoundaryPlan.ofMatching M).powerCost p x y :=
        finitePowerBoundaryTransportCost_le_plan _ _ _ _
      _ = _ := by rw [FiniteBoundaryPlan.powerCost_ofMatching, hM]
  · exact le_ciInf fun a => a.matchingPowerCost_le_powerCost p x y

theorem finitePowerBoundaryTransportCost_nonneg (p : ℝ)
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) : 0 ≤ finitePowerBoundaryTransportCost p x y := by
  rw [finitePowerBoundaryTransportCost_eq_matchingCost]
  exact finitePowerMatchingCost_nonneg p x y

/-- Some integral incidence plan attains the optimum; fractional optima can coexist. -/
theorem exists_minimizing_powerBoundaryPlan (p : ℝ) (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    ∃ M : OccurrenceMatching I J PEmpty.{1} PEmpty.{1},
      (FiniteBoundaryPlan.ofMatching M).powerCost p x y = finitePowerBoundaryTransportCost p x y := by
  obtain ⟨M, hM⟩ := exists_minimizing_powerMatching p x y
  exact ⟨M, by rw [FiniteBoundaryPlan.powerCost_ofMatching,
    finitePowerBoundaryTransportCost_eq_matchingCost, hM]⟩

theorem finitePBoundaryTransportCost_eq_matchingCost (p : ℝ)
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    finitePBoundaryTransportCost p x y = finitePMatchingCost p x y := by
  simp only [finitePBoundaryTransportCost, finitePMatchingCost,
    finitePowerBoundaryTransportCost_eq_matchingCost]

theorem finitePBoundaryTransportCost_nonneg (p : ℝ)
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) : 0 ≤ finitePBoundaryTransportCost p x y :=
  Real.rpow_nonneg (finitePowerBoundaryTransportCost_nonneg p x y) _

theorem finitePBoundaryTransportCost_le_plan {p : ℝ} (hp : 1 ≤ p)
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) (a : FiniteBoundaryPlan I J) :
    finitePBoundaryTransportCost p x y ≤ a.powerCost p x y ^ p⁻¹ :=
  Real.rpow_le_rpow (finitePowerBoundaryTransportCost_nonneg p x y)
    (finitePowerBoundaryTransportCost_le_plan p x y a)
    (inv_nonneg.mpr (le_trans zero_le_one hp))

/-- The same incidence plan attains the rooted optimum. -/
theorem exists_minimizing_pBoundaryPlan (p : ℝ) (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    ∃ M : OccurrenceMatching I J PEmpty.{1} PEmpty.{1},
      (FiniteBoundaryPlan.ofMatching M).powerCost p x y ^ p⁻¹ = finitePBoundaryTransportCost p x y := by
  obtain ⟨M, hM⟩ := exists_minimizing_powerBoundaryPlan p x y
  exact ⟨M, by rw [hM]; rfl⟩

/-- Attainment and root monotonicity identify the infimum of rooted plan costs. -/
theorem finitePBoundaryTransportCost_eq_iInf {p : ℝ} (hp : 1 ≤ p)
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    finitePBoundaryTransportCost p x y = ⨅ a : FiniteBoundaryPlan I J, a.powerCost p x y ^ p⁻¹ := by
  have hbd : BddBelow (Set.range fun a : FiniteBoundaryPlan I J => a.powerCost p x y ^ p⁻¹) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨a, rfl⟩
    exact Real.rpow_nonneg (a.powerCost_nonneg p x y) _
  apply le_antisymm
  · exact le_ciInf fun a => finitePBoundaryTransportCost_le_plan hp x y a
  · obtain ⟨M, hM⟩ := exists_minimizing_pBoundaryPlan p x y
    exact (ciInf_le hbd (FiniteBoundaryPlan.ofMatching M)).trans_eq hM

@[simp] theorem finitePowerBoundaryTransportCost_one
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    finitePowerBoundaryTransportCost 1 x y = finiteFirstOrderBoundaryTransportCost x y := by
  rw [finitePowerBoundaryTransportCost_eq_matchingCost, finitePowerMatchingCost_one,
    finiteFirstOrderBoundaryTransportCost_eq_matchingCost]

@[simp] theorem finitePBoundaryTransportCost_one
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    finitePBoundaryTransportCost 1 x y = finiteFirstOrderBoundaryTransportCost x y := by
  simp [finitePBoundaryTransportCost]

theorem finitePowerBoundaryTransportCost_of_isEmpty_right [IsEmpty J]
    (p : ℝ) (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    finitePowerBoundaryTransportCost p x y = ∑ i, (diagonalCost (x i)).toReal ^ p := by
  rw [finitePowerBoundaryTransportCost_eq_matchingCost, finitePowerMatchingCost_of_isEmpty_right]

theorem finitePowerBoundaryTransportCost_of_isEmpty_left [IsEmpty I]
    (p : ℝ) (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    finitePowerBoundaryTransportCost p x y = ∑ j, (diagonalCost (y j)).toReal ^ p := by
  rw [finitePowerBoundaryTransportCost_eq_matchingCost, finitePowerMatchingCost_of_isEmpty_left]

@[simp] theorem finitePowerBoundaryTransportCost_empty [IsEmpty I] [IsEmpty J]
    (p : ℝ) (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) : finitePowerBoundaryTransportCost p x y = 0 := by
  rw [finitePowerBoundaryTransportCost_of_isEmpty_right]; exact Fintype.sum_empty _

theorem finitePBoundaryTransportCost_of_isEmpty_right [IsEmpty J]
    (p : ℝ) (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    finitePBoundaryTransportCost p x y = (∑ i, (diagonalCost (x i)).toReal ^ p) ^ p⁻¹ := by
  rw [finitePBoundaryTransportCost, finitePowerBoundaryTransportCost_of_isEmpty_right]

theorem finitePBoundaryTransportCost_of_isEmpty_left [IsEmpty I]
    (p : ℝ) (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    finitePBoundaryTransportCost p x y = (∑ j, (diagonalCost (y j)).toReal ^ p) ^ p⁻¹ := by
  rw [finitePBoundaryTransportCost, finitePowerBoundaryTransportCost_of_isEmpty_left]

@[simp] theorem finitePBoundaryTransportCost_empty [IsEmpty I] [IsEmpty J]
    {p : ℝ} (hp : 1 ≤ p) (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    finitePBoundaryTransportCost p x y = 0 := by
  rw [finitePBoundaryTransportCost_eq_matchingCost]
  exact finitePMatchingCost_empty hp x y

theorem finitePowerBoundaryTransportCost_reindex {I' J' : Type*} [Fintype I'] [Fintype J']
    (u : I' ≃ I) (v : J' ≃ J) (p : ℝ) (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    finitePowerBoundaryTransportCost p (x ∘ u) (y ∘ v) = finitePowerBoundaryTransportCost p x y := by
  simp only [finitePowerBoundaryTransportCost_eq_matchingCost, finitePowerMatchingCost_reindex]

theorem finitePBoundaryTransportCost_reindex {I' J' : Type*} [Fintype I'] [Fintype J']
    (u : I' ≃ I) (v : J' ≃ J) (p : ℝ) (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    finitePBoundaryTransportCost p (x ∘ u) (y ∘ v) = finitePBoundaryTransportCost p x y := by
  simp only [finitePBoundaryTransportCost, finitePowerBoundaryTransportCost_reindex]

end TDA.Persistence
