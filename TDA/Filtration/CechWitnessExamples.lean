import TDA.Filtration.CechSupNorm
import Mathlib.Order.Interval.Set.ProjIcc

set_option autoImplicit false

/-!
# Witness-space change fixtures

The fixtures test the actual `Cech.complex` and `Cech.filter` definitions. The intrinsic
Čech complex of two points on the line loses the edge that the ambient complex has at
radius `1`, so the witness-space inclusion is strict. A convex subspace with the nearest
point projection loses nothing, and the identity witness map is the trivial control.
-/

universe u v

namespace TDA.Filtration.Cech.WitnessExamples

open TDA.Simplicial

/-! ### The intrinsic complex of two points is strictly smaller -/

namespace Intrinsic

/-- The labelled points `0` and `2` on the line. -/
def q : Fin 2 → ℝ := ![0, 2]

theorem q_injective : Function.Injective q := by
  intro i j h
  fin_cases i <;> fin_cases j <;> first | rfl | norm_num [q] at h

/-- The label metric induced by the two points. -/
noncomputable abbrev metric : MetricSpace (Fin 2) :=
  MetricSpace.induced q q_injective inferInstance

theorem metric_dist (v w : Fin 2) : metric.dist v w = dist (q v) (q w) := rfl

/-- The intrinsic labels induce the same label metric. -/
theorem metric_dist_intrinsic (v w : Fin 2) :
    metric.dist v w = dist (Set.rangeFactorization q v) (Set.rangeFactorization q w) := rfl

def edge : Finset (Fin 2) := {0, 1}

theorem edge_nonempty : edge.Nonempty := ⟨0, by simp [edge]⟩

def edgeFace : TotalFace (Rips.fullComplex (Fin 2)) := ⟨edge, edge_nonempty⟩

theorem rips_value : (Rips.filter metric).value edgeFace = 2 := by
  rw [Rips.filter_value]
  change Rips.diameter metric {0, 1} = 2
  rw [Rips.diameter_pair, metric_dist]
  norm_num [q, Real.dist_eq]

/-- The ambient edge is present at radius `1`, witnessed by the midpoint. -/
theorem edge_mem_complex_one : edge ∈ complex q 1 := by
  refine (mem_complex_iff _ _ _).2 ⟨edge_nonempty, 1, ?_⟩
  intro v hv
  simp only [edge, Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl <;> norm_num [q, Real.dist_eq]

/-- Every intrinsic witness is one of the two labels, at distance `2` from the other. -/
theorem exists_far (x : Set.range q) : ∃ v ∈ edge, 2 ≤ dist x (Set.rangeFactorization q v) := by
  obtain ⟨_, j, rfl⟩ := x
  fin_cases j
  · exact ⟨1, by simp [edge], by norm_num [Subtype.dist_eq, q, Real.dist_eq]⟩
  · exact ⟨0, by simp [edge], by norm_num [Subtype.dist_eq, q, Real.dist_eq]⟩

/-- The intrinsic edge is absent at radius `1`. -/
theorem edge_not_mem_intrinsic_one : edge ∉ complex (Set.rangeFactorization q) 1 := by
  intro h
  obtain ⟨-, x, hx⟩ := (mem_complex_iff _ _ _).1 h
  obtain ⟨v, hv, hfar⟩ := exists_far x
  linarith [hx v hv]

/-- The ambient edge value is `1`. -/
theorem cech_value : (filter q).value edgeFace = 1 := by
  rw [filter_value_eq_rips_div_two_real metric q metric_dist, rips_value]
  norm_num

/-- The intrinsic edge value is `2`. -/
theorem intrinsic_value : (filter (Set.rangeFactorization q)).value edgeFace = 2 := by
  apply le_antisymm
  · have h := filter_value_le_rips metric (Set.rangeFactorization q) metric_dist_intrinsic
      edgeFace
    rwa [rips_value] at h
  · have : Nonempty (Set.range q) := ⟨Set.rangeFactorization q 0⟩
    refine le_ciInf fun x => ?_
    obtain ⟨v, hv, hfar⟩ := exists_far x
    exact hfar.trans (dist_le_radiusAt _ x hv)

/-- The intrinsic-to-ambient value comparison is strict on this face. -/
theorem cech_value_lt_intrinsic :
    (filter q).value edgeFace < (filter (Set.rangeFactorization q)).value edgeFace := by
  rw [cech_value, intrinsic_value]
  norm_num

/-- The intrinsic-to-ambient complex inclusion is strict at radius `1`. -/
theorem intrinsic_lt_complex : complex (Set.rangeFactorization q) 1 < complex q 1 :=
  lt_of_le_not_ge (complex_rangeFactorization_le q 1)
    fun h => edge_not_mem_intrinsic_one (h edge_mem_complex_one)

end Intrinsic

/-! ### A convex subspace loses no face -/

namespace Interval

/-- The closed interval `[0, 2]`. -/
abbrev W : Set ℝ := Set.Icc 0 2

/-- The labels `0` and `2` in the interval. -/
def p : Fin 2 → W := ![⟨0, by norm_num⟩, ⟨2, by norm_num⟩]

/-- The nearest-point projection onto the interval. -/
noncomputable def g : ℝ → W := Set.projIcc 0 2 (by norm_num)

theorem lipschitzWith_g : LipschitzWith 1 g := LipschitzWith.projIcc _

theorem g_val (v : Fin 2) : g (Subtype.val (p v)) = p v := Set.projIcc_val _ _

/-- At every radius, the interval and the ambient line give the same Čech complex. -/
theorem complex_val_eq (r : ℝ) : complex (Subtype.val ∘ p) r = complex p r :=
  complex_comp_eq_of_retraction isometry_subtype_coe lipschitzWith_g g_val r

theorem filter_val_value_eq (s : TotalFace (Rips.fullComplex (Fin 2))) :
    (filter (Subtype.val ∘ p)).value s = (filter p).value s :=
  filter_comp_value_eq_of_retraction isometry_subtype_coe lipschitzWith_g g_val s

theorem val_p_injective : Function.Injective (Subtype.val ∘ p) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> first | rfl | norm_num [p] at h

noncomputable abbrev metric : MetricSpace (Fin 2) :=
  MetricSpace.induced (Subtype.val ∘ p) val_p_injective inferInstance

theorem metric_dist (v w : Fin 2) :
    metric.dist v w = dist ((Subtype.val ∘ p) v) ((Subtype.val ∘ p) w) := rfl

def edge : Finset (Fin 2) := {0, 1}

def edgeFace : TotalFace (Rips.fullComplex (Fin 2)) := ⟨edge, ⟨0, by simp [edge]⟩⟩

/-- The edge value in the interval is `1`. -/
theorem value_eq_one : (filter p).value edgeFace = 1 := by
  rw [← filter_val_value_eq, filter_value_eq_rips_div_two_real metric _ metric_dist,
    Rips.filter_value]
  change Rips.diameter metric {0, 1} / 2 = 1
  rw [Rips.diameter_pair, metric_dist]
  norm_num [p, Real.dist_eq]

/-- Unlike the intrinsic complex of the two endpoints, the interval keeps the edge at `1`. -/
theorem edge_mem_complex_one : edge ∈ complex p 1 := by
  rw [← complex_val_eq]
  refine (mem_complex_iff _ _ _).2 ⟨⟨0, by simp [edge]⟩, 1, ?_⟩
  intro v hv
  simp only [edge, Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl <;> norm_num [p, Real.dist_eq]

end Interval

/-! ### The identity witness map -/

section Identity

variable {X : Type u} {V : Type v} [PseudoMetricSpace X]

theorem complex_id_comp (p : V → X) (r : ℝ) : complex (id ∘ p) r = complex p r :=
  complex_comp_eq_of_retraction isometry_id LipschitzWith.id (p := p) (fun _ => rfl) r

theorem filter_id_comp_value (p : V → X) (s : TotalFace (Rips.fullComplex V)) :
    (filter (id ∘ p)).value s = (filter p).value s :=
  filter_comp_value_eq_of_retraction isometry_id LipschitzWith.id (p := p) (fun _ => rfl) s

end Identity

end TDA.Filtration.Cech.WitnessExamples
