import TDA.Persistence.CechStability
import TDA.Filtration.CechExamples
import TDA.Filtration.CechDisplacementExamples

set_option autoImplicit false

/-!
# Čech diagram stability fixtures

One point of a two-point configuration on the line moves by one, which changes the edge's
Čech value by only `1/2` while the diagrams stay within the displacement. The three-point
family on which the Čech and Rips face estimates are attained gives diagram bounds `1` and
`2`. Zero displacement and the empty carrier give equal diagrams in every degree.
-/

namespace TDA.Persistence.Cech.Examples

open TDA.Filtration TDA.Simplicial

/-! ### One point moved by one on the line -/

namespace MovedPoint

/-- The labelled points `0, 2`. -/
abbrev p : Fin 2 → ℝ := Cech.Examples.TwoPoints.pts

/-- The second point moved to `3`. -/
def q : Fin 2 → ℝ := ![0, 3]

theorem q_injective : Function.Injective q := by
  intro i j h
  fin_cases i <;> fin_cases j <;> first | rfl | norm_num [q] at h

/-- The label metric induced by `q`. -/
noncomputable abbrev metricQ : MetricSpace (Fin 2) :=
  MetricSpace.induced q q_injective inferInstance

theorem metricQ_dist (v w : Fin 2) : metricQ.dist v w = dist (q v) (q w) := rfl

theorem displacement_eq : Cech.displacement p q = 1 := by
  apply le_antisymm
  · refine (Cech.displacement_le_iff p q 1).2 ⟨zero_le_one, fun v => ?_⟩
    fin_cases v <;> norm_num [Cech.Examples.TwoPoints.pts, q, Real.dist_eq]
  · have h := Cech.dist_le_displacement p q 1
    norm_num [Cech.Examples.TwoPoints.pts, q, Real.dist_eq] at h
    exact h

/-- The edge joining the two labels, as a face. -/
abbrev edgeFace : TotalFace (Rips.fullComplex (Fin 2)) := Cech.Examples.TwoPoints.edgeFace

theorem cech_value_p : (Cech.filter p).value edgeFace = 1 :=
  Cech.Examples.TwoPoints.cech_value

theorem edge_mem_complex_q : Cech.Examples.TwoPoints.edge ∈ Cech.complex q (3 / 2) := by
  refine (Cech.mem_complex_iff _ _ _).2 ⟨Cech.Examples.TwoPoints.edge_nonempty, 3 / 2, ?_⟩
  intro v hv
  simp only [Cech.Examples.TwoPoints.edge, Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl <;> norm_num [q, Real.dist_eq, abs_of_pos]

theorem rips_value_q : (Rips.filter metricQ).value edgeFace = 3 := by
  rw [Rips.filter_value]
  change Rips.diameter metricQ {0, 1} = 3
  rw [Rips.diameter_pair, metricQ_dist]
  norm_num [q, Real.dist_eq]

theorem cech_value_q : (Cech.filter q).value edgeFace = 3 / 2 := by
  apply le_antisymm
  · exact (FilterFunction.mem_sublevel_iff_of_mem _ _ _).1
      (Cech.complex_le_sublevel q (3 / 2) edge_mem_complex_q)
  · have h := Cech.rips_le_two_mul_filter_value metricQ q metricQ_dist edgeFace
    rw [rips_value_q] at h
    linarith

/-- The value change is strictly below the displacement: the face estimate is not sharp here. -/
theorem abs_cech_value_sub_lt_displacement :
    |(Cech.filter p).value edgeFace - (Cech.filter q).value edgeFace| <
      Cech.displacement p q := by
  rw [cech_value_p, cech_value_q, displacement_eq]
  norm_num [abs_of_neg]

theorem bottleneck_le (n : ℕ) :
    bottleneck (dgm ℚ (Cech.filter p) n) (dgm ℚ (Cech.filter q) n) ≤ 1 := by
  simpa only [displacement_eq, ENNReal.ofReal_one] using
    bottleneck_dgm_le_displacement ℚ p q n

end MovedPoint

/-! ### Diagram bounds on the three-point family -/

namespace ThreePoints

open Cech.DisplacementExamples.ThreePoints

theorem cech_bottleneck_le (n : ℕ) :
    bottleneck (dgm ℚ (Cech.filter p) n) (dgm ℚ (Cech.filter q) n) ≤ 1 := by
  simpa only [displacement_eq, ENNReal.ofReal_one] using
    bottleneck_dgm_le_displacement ℚ p q n

theorem rips_bottleneck_le (n : ℕ) :
    bottleneck (dgm ℚ (Rips.filter metricP) n) (dgm ℚ (Rips.filter metricQ) n) ≤ 2 := by
  have h := bottleneck_rips_dgm_le_two_mul_displacement ℚ metricP metricQ p q
    metricP_dist metricQ_dist n
  rw [displacement_eq, mul_one, ENNReal.ofReal_ofNat] at h
  exact h

end ThreePoints

/-! ### Zero displacement and the empty carrier -/

theorem self_displacement (p : Fin 2 → ℝ) : Cech.displacement p p = 0 :=
  Cech.displacement_self p

theorem bottleneck_self_eq_zero (p : Fin 2 → ℝ) (n : ℕ) :
    bottleneck (dgm ℚ (Cech.filter p) n) (dgm ℚ (Cech.filter p) n) = 0 := by
  apply le_antisymm _ zero_le
  simpa only [Cech.displacement_self, ENNReal.ofReal_zero] using
    bottleneck_dgm_le_displacement ℚ p p n

theorem empty_displacement (p q : Fin 0 → ℝ) : Cech.displacement p q = 0 :=
  Cech.displacement_of_isEmpty p q

theorem empty_bottleneck (p q : Fin 0 → ℝ) (n : ℕ) :
    bottleneck (dgm ℚ (Cech.filter p) n) (dgm ℚ (Cech.filter q) n) = 0 := by
  apply le_antisymm _ zero_le
  simpa only [Cech.displacement_of_isEmpty, ENNReal.ofReal_zero] using
    bottleneck_dgm_le_displacement ℚ p q n

end TDA.Persistence.Cech.Examples
