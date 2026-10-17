import TDA.Filtration.Cech
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.FiniteDimension

set_option autoImplicit false

/-!
# Čech complex and Rips/Čech sandwich fixtures

The fixtures test the actual `Cech.complex` and `Cech.filter` definitions: a closed boundary
on the line with a sharp lower value bound, an acute planar triangle on which both sandwich
inclusions are strict, the failure of attainment in the punctured line, repeated labels, and
empty negative-radius stages.
-/

universe u v

namespace TDA.Filtration.Cech.Examples

open TDA.Simplicial

/-! ### Two points on the line -/

namespace TwoPoints

/-- The labelled points `0` and `2` on the real line. -/
def pts : Fin 2 → ℝ := ![0, 2]

theorem pts_injective : Function.Injective pts := by
  intro i j h
  fin_cases i <;> fin_cases j <;> first | rfl | norm_num [pts] at h

/-- The label metric induced by the two points. -/
noncomputable abbrev metric : MetricSpace (Fin 2) :=
  MetricSpace.induced pts pts_injective inferInstance

theorem metric_dist (v w : Fin 2) : metric.dist v w = dist (pts v) (pts w) := rfl

/-- The edge joining the two labels. -/
def edge : Finset (Fin 2) := {0, 1}

theorem edge_nonempty : edge.Nonempty := ⟨0, by simp [edge]⟩

/-- The edge as an actual face of the full complex. -/
def edgeFace : TotalFace (Rips.fullComplex (Fin 2)) := ⟨edge, edge_nonempty⟩

theorem dist_pts : dist (pts 0) (pts 1) = 2 := by
  norm_num [pts, Real.dist_eq]

/-- The closed boundary: the midpoint witnesses the edge at radius exactly one. -/
theorem edge_mem_complex_one : edge ∈ complex pts 1 := by
  refine (mem_complex_iff _ _ _).2 ⟨edge_nonempty, 1, ?_⟩
  intro v hv
  simp only [edge, Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl <;> norm_num [pts, Real.dist_eq]

theorem edge_not_mem_complex {r : ℝ} (hr : r < 1) : edge ∉ complex pts r := by
  intro h
  have h2 := dist_le_two_mul_of_mem_complex pts h (v := 0) (w := 1)
    (by simp [edge]) (by simp [edge])
  rw [dist_pts] at h2
  linarith

theorem edge_not_mem_rips_one : edge ∉ (Rips.filter metric).sublevel 1 := by
  intro h
  have h1 := ((Rips.mem_sublevel_iff _ _ _).1 h).2 0 (by simp [edge]) 1 (by simp [edge])
  rw [metric_dist, dist_pts] at h1
  norm_num at h1

theorem edge_mem_rips_two : edge ∈ (Rips.filter metric).sublevel 2 := by
  refine (Rips.mem_sublevel_iff _ _ _).2 ⟨edge_nonempty, ?_⟩
  intro v hv w hw
  rw [metric_dist]
  simp only [edge, Finset.mem_insert, Finset.mem_singleton] at hv hw
  rcases hv with rfl | rfl <;> rcases hw with rfl | rfl <;> norm_num [pts, Real.dist_eq]

theorem rips_value : (Rips.filter metric).value edgeFace = 2 := by
  rw [Rips.filter_value]
  change Rips.diameter metric {0, 1} = 2
  rw [Rips.diameter_pair, metric_dist, dist_pts]

theorem cech_value : (filter pts).value edgeFace = 1 := by
  apply le_antisymm
  · exact (FilterFunction.mem_sublevel_iff_of_mem _ _ _).1
      (complex_le_sublevel pts 1 edge_mem_complex_one)
  · have h := rips_le_two_mul_filter_value metric pts metric_dist edgeFace
    rw [rips_value] at h
    linarith

/-- The lower value bound `rips ≤ 2 * čech` is attained. -/
theorem rips_value_eq_two_mul_cech_value :
    (Rips.filter metric).value edgeFace = 2 * (filter pts).value edgeFace := by
  rw [rips_value, cech_value]
  norm_num

end TwoPoints

/-! ### An acute triangle in the Euclidean plane -/

namespace Triangle

/-- The vertices `(0,0)`, `(2,0)` and `(1,2)` of an acute triangle with circumradius `5/4`. -/
noncomputable def pts : Fin 3 → EuclideanSpace ℝ (Fin 2) :=
  ![!₂[0, 0], !₂[2, 0], !₂[1, 2]]

@[simp] theorem pts_zero : pts 0 = !₂[0, 0] := rfl
@[simp] theorem pts_one : pts 1 = !₂[2, 0] := rfl
@[simp] theorem pts_two : pts 2 = !₂[1, 2] := rfl

theorem dist_sq (x y : EuclideanSpace ℝ (Fin 2)) :
    dist x y ^ 2 = (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 := by
  rw [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two, Real.dist_eq, Real.dist_eq, sq_abs, sq_abs]

theorem dist_le_of_sq_le {x y : EuclideanSpace ℝ (Fin 2)} {c : ℝ} (hc : 0 ≤ c)
    (h : (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 ≤ c ^ 2) : dist x y ≤ c := by
  rw [← dist_sq] at h
  exact (pow_le_pow_iff_left₀ dist_nonneg hc two_ne_zero).1 h

theorem sq_le_of_dist_le {x y : EuclideanSpace ℝ (Fin 2)} {c : ℝ} (h : dist x y ≤ c) :
    (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 ≤ c ^ 2 := by
  rw [← dist_sq]
  exact pow_le_pow_left₀ dist_nonneg h 2

theorem pts_injective : Function.Injective pts := by
  intro i j h
  have h0 : pts i 0 = pts j 0 := congrArg (fun z : EuclideanSpace ℝ (Fin 2) => z 0) h
  have hx : ∀ k : Fin 3, pts k 0 = ![0, 2, 1] k := by
    intro k
    fin_cases k <;> rfl
  rw [hx, hx] at h0
  fin_cases i <;> fin_cases j <;> first | rfl | norm_num at h0

/-- The label metric induced by the three vertices. -/
noncomputable abbrev metric : MetricSpace (Fin 3) :=
  MetricSpace.induced pts pts_injective inferInstance

theorem metric_dist (v w : Fin 3) : metric.dist v w = dist (pts v) (pts w) := rfl

/-- The three edges and the triangle. -/
def edge01 : Finset (Fin 3) := {0, 1}
def edge02 : Finset (Fin 3) := {0, 2}
def edge12 : Finset (Fin 3) := {1, 2}
def tri : Finset (Fin 3) := {0, 1, 2}

theorem edge01_mem_complex : edge01 ∈ complex pts (6 / 5) := by
  refine (mem_complex_iff _ _ _).2 ⟨⟨0, by simp [edge01]⟩, !₂[1, 0], ?_⟩
  intro v hv
  simp only [edge01, Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl <;>
    exact dist_le_of_sq_le (by norm_num) (by norm_num [pts_zero, pts_one, pts_two])

theorem edge02_mem_complex : edge02 ∈ complex pts (6 / 5) := by
  refine (mem_complex_iff _ _ _).2 ⟨⟨0, by simp [edge02]⟩, !₂[1 / 2, 1], ?_⟩
  intro v hv
  simp only [edge02, Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl <;>
    exact dist_le_of_sq_le (by norm_num) (by norm_num [pts_zero, pts_one, pts_two])

theorem edge12_mem_complex : edge12 ∈ complex pts (6 / 5) := by
  refine (mem_complex_iff _ _ _).2 ⟨⟨1, by simp [edge12]⟩, !₂[3 / 2, 1], ?_⟩
  intro v hv
  simp only [edge12, Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl <;>
    exact dist_le_of_sq_le (by norm_num) (by norm_num [pts_zero, pts_one, pts_two])

/-- No point is within `6/5` of all three vertices: a weighted sum of squared distances
equals `|x - (1, 3/4)|² + 25/16`, and `25/16 > 36/25`. -/
theorem tri_not_mem_complex : tri ∉ complex pts (6 / 5) := by
  intro h
  obtain ⟨-, x, hx⟩ := (mem_complex_iff _ _ _).1 h
  have ha := sq_le_of_dist_le (hx 0 (by simp [tri]))
  have hb := sq_le_of_dist_le (hx 1 (by simp [tri]))
  have hc := sq_le_of_dist_le (hx 2 (by simp [tri]))
  norm_num [pts_zero, pts_one, pts_two] at ha hb hc
  nlinarith [sq_nonneg (x 0 - 1), sq_nonneg (x 1 - 3 / 4)]

theorem tri_mem_rips : tri ∈ (Rips.filter metric).sublevel (12 / 5) := by
  refine (Rips.mem_sublevel_iff _ _ _).2 ⟨⟨0, by simp [tri]⟩, ?_⟩
  intro v hv w hw
  rw [metric_dist]
  simp only [tri, Finset.mem_insert, Finset.mem_singleton] at hv hw
  rcases hv with rfl | rfl | rfl <;> rcases hw with rfl | rfl | rfl <;>
    exact dist_le_of_sq_le (by norm_num) (by norm_num [pts_zero, pts_one, pts_two])

private theorem not_le_of_sq {v w : Fin 3} (h : (6 / 5 : ℝ) ^ 2 <
    (pts v 0 - pts w 0) ^ 2 + (pts v 1 - pts w 1) ^ 2) : ¬ metric.dist v w ≤ 6 / 5 :=
  fun hle => absurd (sq_le_of_dist_le (metric_dist v w ▸ hle)) (not_le.2 h)

theorem edge01_not_mem_rips : edge01 ∉ (Rips.filter metric).sublevel (6 / 5) := fun h =>
  not_le_of_sq (by norm_num [pts_zero, pts_one, pts_two])
    (((Rips.mem_sublevel_iff _ _ _).1 h).2 0 (by simp [edge01]) 1 (by simp [edge01]))

theorem edge02_not_mem_rips : edge02 ∉ (Rips.filter metric).sublevel (6 / 5) := fun h =>
  not_le_of_sq (by norm_num [pts_zero, pts_one, pts_two])
    (((Rips.mem_sublevel_iff _ _ _).1 h).2 0 (by simp [edge02]) 2 (by simp [edge02]))

theorem edge12_not_mem_rips : edge12 ∉ (Rips.filter metric).sublevel (6 / 5) := fun h =>
  not_le_of_sq (by norm_num [pts_zero, pts_one, pts_two])
    (((Rips.mem_sublevel_iff _ _ _).1 h).2 1 (by simp [edge12]) 2 (by simp [edge12]))

/-- The first sandwich inclusion is strict on this family. -/
theorem rips_lt_complex : (Rips.filter metric).sublevel (6 / 5) < complex pts (6 / 5) :=
  lt_of_le_not_ge (ripsSublevel_le_complex metric pts metric_dist _)
    fun h => edge01_not_mem_rips (h edge01_mem_complex)

/-- The second sandwich inclusion is strict on this family. -/
theorem complex_lt_rips : complex pts (6 / 5) < (Rips.filter metric).sublevel (2 * (6 / 5)) :=
  lt_of_le_not_ge (complex_le_ripsSublevel_two_mul metric pts metric_dist _)
    fun h => tri_not_mem_complex (h (by norm_num; exact tri_mem_rips))

end Triangle

/-! ### Attainment fails in the punctured line -/

namespace Punctured

/-- The labelled points `-1` and `1` in the punctured line, which is not proper. -/
def pts : Fin 2 → {x : ℝ // x ≠ 0} := ![⟨-1, by norm_num⟩, ⟨1, by norm_num⟩]

theorem pts_injective : Function.Injective pts := by
  intro i j h
  have h0 := congrArg Subtype.val h
  fin_cases i <;> fin_cases j <;> first | rfl | norm_num [pts] at h0

noncomputable abbrev metric : MetricSpace (Fin 2) :=
  MetricSpace.induced pts pts_injective inferInstance

theorem metric_dist (v w : Fin 2) : metric.dist v w = dist (pts v) (pts w) := rfl

def edge : Finset (Fin 2) := {0, 1}

theorem edge_nonempty : edge.Nonempty := ⟨0, by simp [edge]⟩

def edgeFace : TotalFace (Rips.fullComplex (Fin 2)) := ⟨edge, edge_nonempty⟩

/-- The only common point of the two closed unit balls in `ℝ` is the missing origin. -/
theorem edge_not_mem_complex_one : edge ∉ complex pts 1 := by
  intro h
  obtain ⟨-, x, hx⟩ := (mem_complex_iff _ _ _).1 h
  have h0 := hx 0 (by simp [edge])
  have h1 := hx 1 (by simp [edge])
  simp only [Subtype.dist_eq, Real.dist_eq, pts] at h0 h1
  norm_num at h0 h1
  obtain ⟨h0l, h0r⟩ := abs_le.1 h0
  obtain ⟨h1l, h1r⟩ := abs_le.1 h1
  exact x.2 (by linarith)

theorem cech_value : (filter pts).value edgeFace = 1 := by
  apply le_antisymm
  · by_contra hlt
    rw [not_le] at hlt
    set ε := (filter pts).value edgeFace - 1 with hε
    have hpos : (0 : ℝ) < ε / 2 := by linarith
    have hup := filter_value_le_radiusAt pts edgeFace ⟨ε / 2, hpos.ne'⟩
    have hrad : radiusAt pts ⟨ε / 2, hpos.ne'⟩ edge ≤ 1 + ε / 2 := by
      refine (radiusAt_le_iff _ _ _ _).2 ⟨by linarith, fun v hv => ?_⟩
      simp only [edge, Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl <;>
        · simp only [Subtype.dist_eq, Real.dist_eq, pts]
          norm_num
          rw [abs_le]
          constructor <;> linarith
    have : (filter pts).value edgeFace ≤ 1 + ε / 2 := hup.trans hrad
    linarith
  · have h := rips_le_two_mul_filter_value metric pts metric_dist edgeFace
    have hr : (Rips.filter metric).value edgeFace = 2 := by
      rw [Rips.filter_value]
      change Rips.diameter metric {0, 1} = 2
      rw [Rips.diameter_pair, metric_dist]
      norm_num [pts, Subtype.dist_eq, Real.dist_eq]
    rw [hr] at h
    linarith

theorem edge_mem_sublevel_one : edge ∈ (filter pts).sublevel 1 :=
  (FilterFunction.mem_sublevel_iff_of_mem _ _ edgeFace).2 cech_value.le

/-- Without `ProperSpace`, the sublevel can be strictly larger than the Čech complex. -/
theorem sublevel_ne_complex : (filter pts).sublevel 1 ≠ complex pts 1 := fun h =>
  edge_not_mem_complex_one (h ▸ edge_mem_sublevel_one)

end Punctured

/-! ### Repeated labels -/

namespace Repeated

/-- Two distinct labels at the same point. -/
def pts : Fin 2 → ℝ := fun _ => 0

def edge : Finset (Fin 2) := {0, 1}

theorem edge_card : edge.card = 2 := rfl

def edgeFace : TotalFace (Rips.fullComplex (Fin 2)) := ⟨edge, ⟨0, by simp [edge]⟩⟩

theorem edge_mem_complex_zero : edge ∈ complex pts 0 :=
  mem_complex_of_pairwise pts ⟨0, by simp [edge]⟩ fun _ _ _ _ => by simp [pts]

theorem cech_value : (filter pts).value edgeFace = 0 :=
  le_antisymm ((FilterFunction.mem_sublevel_iff_of_mem _ _ _).1
    (complex_le_sublevel pts 0 edge_mem_complex_zero)) (filter_value_nonneg pts edgeFace)

end Repeated

/-! ### Negative radii -/

section Negative

variable {X : Type u} {V : Type v} [PseudoMetricSpace X]

theorem complex_neg_one_eq_bot (p : V → X) : complex p (-1) = ⊥ :=
  complex_eq_bot_of_neg p (by norm_num)

theorem singleton_not_mem_complex_neg_one (p : V → X) (v : V) :
    ({v} : Finset V) ∉ complex p (-1) := fun h => by
  have := (singleton_mem_complex_iff p (-1) v).1 h
  norm_num at this

end Negative

end TDA.Filtration.Cech.Examples
