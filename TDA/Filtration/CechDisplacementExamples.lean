import TDA.Filtration.CechDisplacement

set_option autoImplicit false

/-!
# Same-label Čech displacement fixtures

The fixtures test the `Cech.radiusAt`, `Cech.filter`, `Cech.displacement` and
`Rips` definitions: three points on the line where the Čech change attains the
displacement and the Rips change attains twice it, two labellings of the same image with
positive displacement, and the failure of the radius estimate on the empty set for a
negative bound.
-/

universe w v

namespace TDA.Filtration.Cech.DisplacementExamples

open TDA.Simplicial

/-! ### Three points: Čech moves by exactly `δ`, Rips by exactly `2 * δ` -/

namespace ThreePoints

/-- The labelled points `0, 1, 2` on the real line. -/
def p : Fin 3 → ℝ := ![0, 1, 2]

/-- The outer points moved outward by one: `-1, 1, 3`. -/
def q : Fin 3 → ℝ := ![-1, 1, 3]

@[simp] theorem p_zero : p 0 = 0 := rfl
@[simp] theorem p_two : p 2 = 2 := rfl
@[simp] theorem q_zero : q 0 = -1 := rfl
@[simp] theorem q_two : q 2 = 3 := rfl

theorem p_injective : Function.Injective p := by
  intro i j h
  fin_cases i <;> fin_cases j <;> first | rfl | norm_num [p] at h

theorem q_injective : Function.Injective q := by
  intro i j h
  fin_cases i <;> fin_cases j <;> first | rfl | norm_num [q] at h

/-- The label metric induced by `p`. -/
noncomputable abbrev metricP : MetricSpace (Fin 3) :=
  MetricSpace.induced p p_injective inferInstance

/-- The label metric induced by `q`. -/
noncomputable abbrev metricQ : MetricSpace (Fin 3) :=
  MetricSpace.induced q q_injective inferInstance

theorem metricP_dist (v w : Fin 3) : metricP.dist v w = dist (p v) (p w) := rfl

theorem metricQ_dist (v w : Fin 3) : metricQ.dist v w = dist (q v) (q w) := rfl

theorem displacement_eq : displacement p q = 1 := by
  apply le_antisymm
  · refine (displacement_le_iff p q 1).2 ⟨zero_le_one, fun v => ?_⟩
    fin_cases v <;> norm_num [p, q, Real.dist_eq]
  · have h := dist_le_displacement p q 0
    norm_num [p, q, Real.dist_eq] at h
    exact h

/-- The triangle on all three labels. -/
def tri : TotalFace (Rips.fullComplex (Fin 3)) := ⟨Finset.univ, Finset.univ_nonempty⟩

theorem cech_value_p : (filter p).value tri = 1 := by
  apply le_antisymm
  · refine (filter_value_le_radiusAt p tri 1).trans
      ((radiusAt_le_iff p 1 _ 1).2 ⟨zero_le_one, fun v _ => ?_⟩)
    fin_cases v <;> norm_num [p, Real.dist_eq]
  · have h := rips_le_two_mul_filter_value metricP p metricP_dist tri
    have hd : metricP.dist 0 2 ≤ (Rips.filter metricP).value tri :=
      Rips.dist_le_diameter metricP (Finset.mem_univ _) (Finset.mem_univ _)
    rw [metricP_dist, p_zero, p_two, Real.dist_eq] at hd
    rw [Rips.filter_value] at h
    norm_num at hd
    linarith

theorem cech_value_q : (filter q).value tri = 2 := by
  apply le_antisymm
  · refine (filter_value_le_radiusAt q tri 1).trans
      ((radiusAt_le_iff q 1 _ 2).2 ⟨zero_le_two, fun v _ => ?_⟩)
    fin_cases v <;> norm_num [q, Real.dist_eq]
  · have h := rips_le_two_mul_filter_value metricQ q metricQ_dist tri
    have hd : metricQ.dist 0 2 ≤ (Rips.filter metricQ).value tri :=
      Rips.dist_le_diameter metricQ (Finset.mem_univ _) (Finset.mem_univ _)
    rw [metricQ_dist, q_zero, q_two, Real.dist_eq] at hd
    rw [Rips.filter_value] at h
    norm_num at hd
    linarith

/-- The displacement-form Čech face estimate is attained. -/
theorem abs_cech_value_sub_eq_displacement :
    |(filter p).value tri - (filter q).value tri| = displacement p q := by
  rw [cech_value_p, cech_value_q, displacement_eq]
  norm_num

theorem rips_value_p : Rips.diameter metricP Finset.univ = 2 := by
  apply le_antisymm
  · refine (Rips.diameter_le_iff metricP _ 2).2 ⟨zero_le_two, fun v _ w _ => ?_⟩
    rw [metricP_dist]
    fin_cases v <;> fin_cases w <;> norm_num [p, Real.dist_eq]
  · have hd := Rips.dist_le_diameter metricP (Finset.mem_univ (0 : Fin 3))
      (Finset.mem_univ (2 : Fin 3))
    rw [metricP_dist, p_zero, p_two, Real.dist_eq] at hd
    norm_num at hd
    exact hd

theorem rips_value_q : Rips.diameter metricQ Finset.univ = 4 := by
  apply le_antisymm
  · refine (Rips.diameter_le_iff metricQ _ 4).2 ⟨by norm_num, fun v _ w _ => ?_⟩
    rw [metricQ_dist]
    fin_cases v <;> fin_cases w <;> norm_num [q, Real.dist_eq]
  · have hd := Rips.dist_le_diameter metricQ (Finset.mem_univ (0 : Fin 3))
      (Finset.mem_univ (2 : Fin 3))
    rw [metricQ_dist, q_zero, q_two, Real.dist_eq] at hd
    norm_num at hd
    exact hd

/-- The Rips face estimate in displacement form is attained. -/
theorem abs_rips_value_sub_eq_two_mul_displacement :
    |Rips.diameter metricP Finset.univ - Rips.diameter metricQ Finset.univ| =
      2 * displacement p q := by
  rw [rips_value_p, rips_value_q, displacement_eq]
  norm_num

/-- The Rips comparison `pairwiseDiscrepancy ≤ 2 * displacement` is attained. -/
theorem pairwiseDiscrepancy_eq : Rips.pairwiseDiscrepancy metricP metricQ = 2 := by
  apply le_antisymm
  · have h := pairwiseDiscrepancy_le_two_mul_displacement metricP metricQ p q
      metricP_dist metricQ_dist
    rw [displacement_eq] at h
    linarith
  · have h := Rips.abs_dist_sub_le_pairwiseDiscrepancy metricP metricQ 0 2
    rw [metricP_dist, metricQ_dist, p_zero, p_two, q_zero, q_two, Real.dist_eq,
      Real.dist_eq] at h
    norm_num at h
    exact h

theorem pairwiseDiscrepancy_eq_two_mul_displacement :
    Rips.pairwiseDiscrepancy metricP metricQ = 2 * displacement p q := by
  rw [pairwiseDiscrepancy_eq, displacement_eq]
  norm_num

/-- On this family Čech values are strictly more stable than Rips values. -/
theorem cech_change_lt_rips_change :
    |(filter p).value tri - (filter q).value tri| <
      |(Rips.filter metricP).value tri - (Rips.filter metricQ).value tri| := by
  rw [Rips.filter_value, Rips.filter_value]
  change _ < |Rips.diameter metricP Finset.univ - Rips.diameter metricQ Finset.univ|
  rw [cech_value_p, cech_value_q, rips_value_p, rips_value_q]
  norm_num

end ThreePoints

/-! ### Same image, positive displacement -/

namespace Swap

/-- The labelled points `0, 2`. -/
def p : Fin 2 → ℝ := ![0, 2]

/-- The same two points with the labels exchanged. -/
def q : Fin 2 → ℝ := ![2, 0]

theorem range_eq : Set.range p = Set.range q := by
  ext x
  simp only [Set.mem_range, Fin.exists_fin_two, p, q, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  tauto

/-- The images agree, yet the same-label displacement is positive. -/
theorem displacement_eq : displacement p q = 2 := by
  apply le_antisymm
  · refine (displacement_le_iff p q 2).2 ⟨zero_le_two, fun v => ?_⟩
    fin_cases v <;> norm_num [p, q, Real.dist_eq]
  · have h := dist_le_displacement p q 0
    norm_num [p, q, Real.dist_eq] at h
    exact h

end Swap

/-! ### The sign condition of the radius estimate cannot be dropped -/

section EmptySeed

variable {X : Type w} {V : Type v} [PseudoMetricSpace X]

@[simp] theorem radiusAt_empty (p : V → X) (x : X) : radiusAt p x ∅ = 0 := by
  rw [radiusAt, Finset.fold_empty]

/-- On the empty set the displacement hypothesis holds vacuously for `ε = -1`, but the radius
estimate fails. -/
theorem radiusAt_estimate_fails_of_neg (p q : V → X) (x : X) :
    (∀ v ∈ (∅ : Finset V), dist (p v) (q v) ≤ -1) ∧
      ¬ radiusAt p x ∅ ≤ radiusAt q x ∅ + -1 := by
  refine ⟨fun v hv => absurd hv (Finset.notMem_empty v), ?_⟩
  rw [radiusAt_empty, radiusAt_empty]
  norm_num

end EmptySeed

end TDA.Filtration.Cech.DisplacementExamples
