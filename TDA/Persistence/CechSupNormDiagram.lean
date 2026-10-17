import TDA.Persistence.DiagramBottleneckScaling
import TDA.Filtration.CechSupNorm
import TDA.Persistence.RipsStability

set_option autoImplicit false

/-!
# Sup-norm Čech diagrams are halved Rips diagrams

In the sup-metric product `ι → ℝ`, every Čech value is half the Rips value under
distance-compatible label metrics. Hence the Čech filter is the Rips filter scaled by `2⁻¹`,
the actual Čech diagram is the actual Rips diagram with every finite coordinate halved, in
every degree and over every field, and the Čech bottleneck distance is half the Rips one.
Rips metric stability then bounds the Čech diagrams by half the pairwise discrepancy.
The line `ℝ` has the same filter and diagram identities, through the merged line value
identity.

The ambient metric is mathlib's sup metric on `ι → ℝ`, not `EuclideanSpace ℝ ι`, and the
index type may be empty. These are library consequences of the merged identity
`Čech_r = Rips_{2r}`; no external theorem is exported.
-/

universe u w

namespace TDA.Persistence.Cech

open TDA.Filtration

variable {V : Type u} {ι : Type w} [Fintype ι]

/-- The sup-norm Čech filter is the Rips filter scaled by `2⁻¹`. -/
theorem filter_eq_scale_rips (d : MetricSpace V) (p : V → ι → ℝ)
    (hd : ∀ v w, d.dist v w = dist (p v) (p w)) :
    Cech.filter p = (Rips.filter d).scale 2⁻¹ (inv_pos.2 zero_lt_two) := by
  ext s
  rw [FilterFunction.scale_value, Cech.filter_value_eq_rips_div_two d p hd s, div_eq_inv_mul]

/-- The Rips filter is the sup-norm Čech filter scaled by `2`. -/
theorem rips_eq_scale_filter (d : MetricSpace V) (p : V → ι → ℝ)
    (hd : ∀ v w, d.dist v w = dist (p v) (p w)) :
    Rips.filter d = (Cech.filter p).scale 2 zero_lt_two := by
  ext s
  rw [FilterFunction.scale_value, Cech.filter_value_eq_rips_div_two d p hd s]
  ring

/-- On the line, the Čech filter is the Rips filter scaled by `2⁻¹`. -/
theorem filter_eq_scale_rips_real (d : MetricSpace V) (q : V → ℝ)
    (hd : ∀ v w, d.dist v w = dist (q v) (q w)) :
    Cech.filter q = (Rips.filter d).scale 2⁻¹ (inv_pos.2 zero_lt_two) := by
  ext s
  rw [FilterFunction.scale_value, Cech.filter_value_eq_rips_div_two_real d q hd s,
    div_eq_inv_mul]

section Diagrams

variable [LinearOrder V] [Fintype V] (k : Type u) [Field k]

/-- The actual sup-norm Čech diagram is the actual Rips diagram with every finite
coordinate halved, in every degree. -/
theorem dgm_eq_scale_rips (d : MetricSpace V) (p : V → ι → ℝ)
    (hd : ∀ v w, d.dist v w = dist (p v) (p w)) (n : ℕ) :
    dgm k (Cech.filter p) n =
      (dgm k (Rips.filter d) n).scale 2⁻¹ (inv_pos.2 zero_lt_two) := by
  rw [filter_eq_scale_rips d p hd]
  exact dgm_scale k (Rips.filter d) n _

/-- On the line, the actual Čech diagram is the halved actual Rips diagram. -/
theorem dgm_eq_scale_rips_real (d : MetricSpace V) (q : V → ℝ)
    (hd : ∀ v w, d.dist v w = dist (q v) (q w)) (n : ℕ) :
    dgm k (Cech.filter q) n =
      (dgm k (Rips.filter d) n).scale 2⁻¹ (inv_pos.2 zero_lt_two) := by
  rw [filter_eq_scale_rips_real d q hd]
  exact dgm_scale k (Rips.filter d) n _

/-- The sup-norm Čech bottleneck distance is half the Rips one. -/
theorem bottleneck_dgm_eq_half_rips (d e : MetricSpace V) (p q : V → ι → ℝ)
    (hd : ∀ v w, d.dist v w = dist (p v) (p w))
    (he : ∀ v w, e.dist v w = dist (q v) (q w)) (n : ℕ) :
    bottleneck (dgm k (Cech.filter p) n) (dgm k (Cech.filter q) n) =
      ENNReal.ofReal 2⁻¹ *
        bottleneck (dgm k (Rips.filter d) n) (dgm k (Rips.filter e) n) := by
  rw [filter_eq_scale_rips d p hd, filter_eq_scale_rips e q he]
  exact bottleneck_dgm_scale k (Rips.filter d) (Rips.filter e) n _

/-- Rips metric stability bounds the sup-norm Čech diagrams by half the pairwise
discrepancy of the label metrics. -/
theorem bottleneck_dgm_le_half_pairwiseDiscrepancy (d e : MetricSpace V) (p q : V → ι → ℝ)
    (hd : ∀ v w, d.dist v w = dist (p v) (p w))
    (he : ∀ v w, e.dist v w = dist (q v) (q w)) (n : ℕ) :
    bottleneck (dgm k (Cech.filter p) n) (dgm k (Cech.filter q) n) ≤
      ENNReal.ofReal (Rips.pairwiseDiscrepancy d e / 2) := by
  rw [bottleneck_dgm_eq_half_rips k d e p q hd he n]
  calc
    ENNReal.ofReal 2⁻¹ *
          bottleneck (dgm k (Rips.filter d) n) (dgm k (Rips.filter e) n) ≤
        ENNReal.ofReal 2⁻¹ * ENNReal.ofReal (Rips.pairwiseDiscrepancy d e) :=
      mul_le_mul_right (Rips.bottleneck_dgm_le_pairwiseDiscrepancy k d e n) _
    _ = ENNReal.ofReal (Rips.pairwiseDiscrepancy d e / 2) := by
      rw [← ENNReal.ofReal_mul (by norm_num), inv_mul_eq_div]

end Diagrams

end TDA.Persistence.Cech
