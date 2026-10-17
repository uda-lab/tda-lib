import TDA.Persistence.CechSupNormDiagram
import TDA.Persistence.CechStabilityExamples
import TDA.Filtration.CechSupNormExamples

set_option autoImplicit false

/-!
# Sup-norm Čech diagram fixtures

The fixtures test the actual `Cech.filter`, `Rips.filter`, `dgm`, `Diagram.scale` and
`bottleneck` definitions. Two points on the line and the merged triangle in the sup-norm
plane have actual Čech diagrams equal to their halved actual Rips diagrams in every degree,
and the scaled Rips values at the top faces agree with the merged Čech values. For one point
moved by one on the line, the halving law with Rips stability gives the bound `1/2`, sharper
than the merged displacement bound `1`.
-/

namespace TDA.Persistence.Cech.SupNormDiagramExamples

open TDA.Filtration
open scoped ENNReal

/-! ### Two points on the line -/

namespace TwoPoints

open TDA.Filtration.Cech.Examples.TwoPoints

/-- The actual Čech diagram of the points `0, 2` is the halved Rips diagram, for every
field and degree. -/
theorem dgm_eq (k : Type) [Field k] (n : ℕ) :
    dgm k (Cech.filter pts) n =
      (dgm k (Rips.filter metric) n).scale 2⁻¹ (inv_pos.2 zero_lt_two) :=
  dgm_eq_scale_rips_real k metric pts metric_dist n

/-- The halved Rips value of the edge is `2⁻¹ * 2 = 1`, the merged Čech value. -/
theorem scaled_edge_value :
    ((Rips.filter metric).scale 2⁻¹ (inv_pos.2 zero_lt_two)).value edgeFace = 1 ∧
      ((Rips.filter metric).scale 2⁻¹ (inv_pos.2 zero_lt_two)).value edgeFace =
        (Cech.filter pts).value edgeFace := by
  have h : ((Rips.filter metric).scale 2⁻¹ (inv_pos.2 zero_lt_two)).value edgeFace = 1 := by
    rw [FilterFunction.scale_value, rips_value]
    norm_num
  exact ⟨h, h.trans cech_value.symm⟩

end TwoPoints

/-! ### The triangle in the sup-norm plane -/

namespace Triangle

open TDA.Filtration.Cech.SupNormExamples.Triangle

/-- The actual Čech diagram of the sup-norm triangle is the halved Rips diagram in every
degree. -/
theorem dgm_eq (k : Type) [Field k] (n : ℕ) :
    dgm k (Cech.filter pts) n =
      (dgm k (Rips.filter metric) n).scale 2⁻¹ (inv_pos.2 zero_lt_two) :=
  dgm_eq_scale_rips k metric pts metric_dist n

/-- Degree zero. -/
theorem dgm_eq_zero (k : Type) [Field k] :
    dgm k (Cech.filter pts) 0 =
      (dgm k (Rips.filter metric) 0).scale 2⁻¹ (inv_pos.2 zero_lt_two) :=
  dgm_eq k 0

/-- Degree one. -/
theorem dgm_eq_one (k : Type) [Field k] :
    dgm k (Cech.filter pts) 1 =
      (dgm k (Rips.filter metric) 1).scale 2⁻¹ (inv_pos.2 zero_lt_two) :=
  dgm_eq k 1

/-- The halved Rips value of the triangle is `2⁻¹ * 2 = 1`, the merged Čech value. -/
theorem scaled_tri_value :
    ((Rips.filter metric).scale 2⁻¹ (inv_pos.2 zero_lt_two)).value triFace = 1 ∧
      ((Rips.filter metric).scale 2⁻¹ (inv_pos.2 zero_lt_two)).value triFace =
        (Cech.filter pts).value triFace := by
  have h : ((Rips.filter metric).scale 2⁻¹ (inv_pos.2 zero_lt_two)).value triFace = 1 := by
    rw [FilterFunction.scale_value, rips_value]
    norm_num
  exact ⟨h, h.trans cech_value.symm⟩

/-- The filter identity evaluated at the triangle. -/
theorem filter_identity_tri :
    (Cech.filter pts).value triFace =
      ((Rips.filter metric).scale 2⁻¹ (inv_pos.2 zero_lt_two)).value triFace := by
  rw [← filter_eq_scale_rips metric pts metric_dist]

end Triangle

/-! ### One point moved by one: a sharper bound -/

namespace MovedPoint

open TDA.Persistence.Cech.Examples.MovedPoint

/-- The halving identity for the moved configuration, in every degree. -/
theorem bottleneck_eq_half (n : ℕ) :
    bottleneck (dgm ℚ (Cech.filter p) n) (dgm ℚ (Cech.filter q) n) =
      ENNReal.ofReal 2⁻¹ *
        bottleneck (dgm ℚ (Rips.filter TDA.Filtration.Cech.Examples.TwoPoints.metric) n)
          (dgm ℚ (Rips.filter metricQ) n) :=
  bottleneck_dgm_eq_half_rips_real ℚ _ _ p q
    TDA.Filtration.Cech.Examples.TwoPoints.metric_dist metricQ_dist n

/-- The two label metrics differ by at most `1` on each of the four label pairs. -/
theorem pairwiseDiscrepancy_le :
    Rips.pairwiseDiscrepancy TDA.Filtration.Cech.Examples.TwoPoints.metric metricQ ≤ 1 := by
  classical
  unfold Rips.pairwiseDiscrepancy
  refine (Finset.fold_max_le _).mpr ⟨zero_le_one, ?_⟩
  rintro ⟨v, w⟩ _
  change |dist (TDA.Filtration.Cech.Examples.TwoPoints.pts v)
      (TDA.Filtration.Cech.Examples.TwoPoints.pts w) - dist (q v) (q w)| ≤ 1
  fin_cases v <;> fin_cases w <;>
    norm_num [TDA.Filtration.Cech.Examples.TwoPoints.pts, q, Real.dist_eq]

/-- The halving law gives the bound `1/2` in every degree. -/
theorem bottleneck_le_half (n : ℕ) :
    bottleneck (dgm ℚ (Cech.filter p) n) (dgm ℚ (Cech.filter q) n) ≤ ENNReal.ofReal (1 / 2) :=
  (bottleneck_dgm_le_half_pairwiseDiscrepancy_real ℚ _ _ p q
    TDA.Filtration.Cech.Examples.TwoPoints.metric_dist metricQ_dist n).trans
    (ENNReal.ofReal_le_ofReal (by linarith [pairwiseDiscrepancy_le]))

/-- The bound `1/2` is strictly below the merged displacement bound `1`. -/
theorem half_lt_one : ENNReal.ofReal (1 / 2) < 1 := by
  rw [← ENNReal.ofReal_one]
  exact (ENNReal.ofReal_lt_ofReal_iff one_pos).2 (by norm_num)

end MovedPoint

end TDA.Persistence.Cech.SupNormDiagramExamples
