import TDA.Filtration.CechSupNorm
import TDA.Filtration.CechExamples

set_option autoImplicit false

/-!
# Sup-norm Čech/Rips equality fixtures

The fixtures test the actual `Cech.complex` and `Cech.filter` definitions in the sup-norm
plane `Fin 2 → ℝ`: the vertices of the merged Euclidean triangle fixture now span a face at
radius `1`, witnessed by the coordinatewise Helly point, and the Čech value is exactly half
the Rips value. A diagonal pair, the line read as `Fin 1 → ℝ`, and the empty index type
complete the list.
-/

namespace TDA.Filtration.Cech.SupNormExamples

open TDA.Simplicial

/-- Sup distances in the plane, bounded coordinatewise. -/
theorem dist_le_of_coord {x y : Fin 2 → ℝ} {c : ℝ} (hc : 0 ≤ c) (h0 : |x 0 - y 0| ≤ c)
    (h1 : |x 1 - y 1| ≤ c) : dist x y ≤ c :=
  (dist_pi_le_iff hc).2 (Fin.forall_fin_two.2 ⟨by rwa [Real.dist_eq], by rwa [Real.dist_eq]⟩)

/-- Sup distances in the plane, bounded below by any coordinate. -/
theorem coord_le_dist (x y : Fin 2 → ℝ) (i : Fin 2) : |x i - y i| ≤ dist x y := by
  rw [← Real.dist_eq]
  exact dist_le_pi_dist x y i

/-! ### The triangle in the sup-norm plane -/

namespace Triangle

/-- The vertices `(0,0)`, `(2,0)` and `(1,2)`, as in the merged Euclidean fixture. -/
def pts : Fin 3 → Fin 2 → ℝ := ![![0, 0], ![2, 0], ![1, 2]]

@[simp] theorem pts_zero : pts 0 = ![0, 0] := rfl
@[simp] theorem pts_one : pts 1 = ![2, 0] := rfl
@[simp] theorem pts_two : pts 2 = ![1, 2] := rfl
@[simp] theorem pts_mk_two : pts ⟨2, by decide⟩ = ![1, 2] := rfl

theorem pts_injective : Function.Injective pts := by
  intro i j h
  have h0 : pts i 0 = pts j 0 := congrFun h 0
  have hx : ∀ k : Fin 3, pts k 0 = ![0, 2, 1] k := by
    intro k
    fin_cases k <;> rfl
  rw [hx, hx] at h0
  fin_cases i <;> fin_cases j <;> first | rfl | norm_num at h0

/-- The label metric induced by the three vertices. -/
noncomputable abbrev metric : MetricSpace (Fin 3) :=
  MetricSpace.induced pts pts_injective inferInstance

theorem metric_dist (v w : Fin 3) : metric.dist v w = dist (pts v) (pts w) := rfl

/-- All pairwise sup distances are at most `2`. -/
theorem dist_pts_le (v w : Fin 3) : dist (pts v) (pts w) ≤ 2 := by
  fin_cases v <;> fin_cases w <;>
    exact dist_le_of_coord (by norm_num) (by norm_num [abs_le])
      (by norm_num [abs_le])

theorem dist_pts_zero_one : dist (pts 0) (pts 1) = 2 := by
  refine le_antisymm (dist_pts_le 0 1) ?_
  have := coord_le_dist (pts 0) (pts 1) 0
  norm_num at this
  exact this

/-- The triangle. -/
def tri : Finset (Fin 3) := {0, 1, 2}

theorem tri_nonempty : tri.Nonempty := ⟨0, by simp [tri]⟩

/-- The triangle as an actual face of the full complex. -/
def triFace : TotalFace (Rips.fullComplex (Fin 3)) := ⟨tri, tri_nonempty⟩

/-- The coordinatewise Helly point of the triangle at radius `1` is `(1, 1)`. -/
theorem supNormWitness_tri : supNormWitness pts 1 tri tri_nonempty = ![1, 1] := by
  funext i
  fin_cases i <;>
    norm_num [supNormWitness, tri, Finset.sup'_insert, Finset.sup'_singleton]

/-- The triangle is a face at radius `1`, witnessed by `(1, 1)`. -/
theorem tri_mem_complex_one : tri ∈ complex pts 1 := by
  refine (mem_complex_iff _ _ _).2 ⟨tri_nonempty, ![1, 1], ?_⟩
  intro v hv
  simp only [tri, Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl | rfl <;>
    exact dist_le_of_coord (by norm_num) (by norm_num [abs_le])
      (by norm_num [abs_le])

theorem tri_not_mem_complex {r : ℝ} (hr : r < 1) : tri ∉ complex pts r := by
  intro h
  have h2 := dist_le_two_mul_of_mem_complex pts h (v := 0) (w := 1)
    (by simp [tri]) (by simp [tri])
  rw [dist_pts_zero_one] at h2
  linarith

theorem rips_value : (Rips.filter metric).value triFace = 2 := by
  rw [Rips.filter_value]
  apply le_antisymm
  · exact (Rips.diameter_le_iff _ _ _).2
      ⟨by norm_num, fun v _ w _ => (metric_dist v w).trans_le (dist_pts_le v w)⟩
  · have := Rips.dist_le_diameter metric (s := tri) (v := 0) (w := 1)
      (by simp [tri]) (by simp [tri])
    rwa [metric_dist, dist_pts_zero_one] at this

/-- The Čech value of the triangle is exactly `1`, half its Rips value. -/
theorem cech_value : (filter pts).value triFace = 1 := by
  rw [filter_value_eq_rips_div_two metric pts metric_dist, rips_value]
  norm_num

/-! #### The complex equality instance -/

theorem complex_one_eq_ripsSublevel_two : complex pts 1 = (Rips.filter metric).sublevel 2 := by
  have h := complex_eq_ripsSublevel_two_mul metric pts metric_dist 1
  rwa [mul_one] at h

/-- Unlike the Euclidean triangle (`Cech.Examples.Triangle.tri_not_mem_complex`), the
sup-norm triangle is a face at radius `6/5`. -/
theorem tri_mem_complex_six_fifths : tri ∈ complex pts (6 / 5) :=
  complex_mono pts (by norm_num) tri_mem_complex_one

theorem euclidean_contrast :
    tri ∈ complex pts (6 / 5) ∧
      Examples.Triangle.tri ∉ complex Examples.Triangle.pts (6 / 5) :=
  ⟨tri_mem_complex_six_fifths, Examples.Triangle.tri_not_mem_complex⟩

end Triangle

/-! ### A diagonal pair -/

namespace Diagonal

/-- The points `(0,0)` and `(2,2)` in the sup-norm plane. -/
def pts : Fin 2 → Fin 2 → ℝ := ![![0, 0], ![2, 2]]

theorem pts_injective : Function.Injective pts := by
  intro i j h
  have h0 : pts i 0 = pts j 0 := congrFun h 0
  fin_cases i <;> fin_cases j <;> first | rfl | norm_num [pts] at h0

noncomputable abbrev metric : MetricSpace (Fin 2) :=
  MetricSpace.induced pts pts_injective inferInstance

theorem metric_dist (v w : Fin 2) : metric.dist v w = dist (pts v) (pts w) := rfl

/-- The sup distance of the diagonal pair is `2`. -/
theorem dist_pts : dist (pts 0) (pts 1) = 2 := by
  apply le_antisymm
  · exact dist_le_of_coord (by norm_num) (by norm_num [pts]) (by norm_num [pts])
  · have := coord_le_dist (pts 0) (pts 1) 0
    norm_num [pts] at this
    exact this

def edge : Finset (Fin 2) := {0, 1}

theorem edge_nonempty : edge.Nonempty := ⟨0, by simp [edge]⟩

def edgeFace : TotalFace (Rips.fullComplex (Fin 2)) := ⟨edge, edge_nonempty⟩

/-- The edge is a face at radius `1`, witnessed by `(1, 1)`. -/
theorem edge_mem_complex_one : edge ∈ complex pts 1 := by
  refine (mem_complex_iff _ _ _).2 ⟨edge_nonempty, ![1, 1], ?_⟩
  intro v hv
  simp only [edge, Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl <;>
    exact dist_le_of_coord (by norm_num) (by norm_num [pts]) (by norm_num [pts])

theorem rips_value : (Rips.filter metric).value edgeFace = 2 := by
  rw [Rips.filter_value]
  change Rips.diameter metric {0, 1} = 2
  rw [Rips.diameter_pair, metric_dist, dist_pts]

theorem cech_value : (filter pts).value edgeFace = 1 := by
  rw [filter_value_eq_rips_div_two metric pts metric_dist, rips_value]
  norm_num

end Diagonal

/-! ### The line as a one-coordinate product -/

namespace Line

/-- The labelled points `0` and `2` on the line. -/
def q : Fin 2 → ℝ := ![0, 2]

/-- The same points as constant maps `Fin 1 → ℝ`. -/
def q₁ (v : Fin 2) : Fin 1 → ℝ := fun _ => q v

/-- The constant embedding of the line into `Fin 1 → ℝ`. -/
def embed (x : ℝ) : Fin 1 → ℝ := fun _ => x

theorem isometry_embed : Isometry embed :=
  Isometry.of_dist_eq fun x y => dist_pi_const x y

theorem lipschitzWith_eval_zero : LipschitzWith 1 fun y : Fin 1 → ℝ => y 0 :=
  LipschitzWith.mk_one fun x y => dist_le_pi_dist x y 0

theorem q₁_eq : q₁ = embed ∘ q := rfl

/-- The line and its one-coordinate product have the same Čech values on every face. -/
theorem value_eq (s : TotalFace (Rips.fullComplex (Fin 2))) :
    (filter q).value s = (filter q₁).value s := by
  rw [q₁_eq]
  exact (filter_comp_value_eq_of_retraction isometry_embed lipschitzWith_eval_zero
    (fun _ => rfl) s).symm

theorem q_eq_twoPoints : q = Examples.TwoPoints.pts := rfl

/-- The edge value is `1` on the line, by the line corollary. -/
theorem cech_value : (filter q).value Examples.TwoPoints.edgeFace = 1 := by
  rw [filter_value_eq_rips_div_two_real Examples.TwoPoints.metric q
    Examples.TwoPoints.metric_dist, Examples.TwoPoints.rips_value]
  norm_num

/-- The edge value is `1` in the one-coordinate product as well. -/
theorem cech_value₁ : (filter q₁).value Examples.TwoPoints.edgeFace = 1 :=
  (value_eq _).symm.trans cech_value

/-- Both agree with the merged two-point fixture. -/
theorem cech_value_eq_twoPoints :
    (filter q₁).value Examples.TwoPoints.edgeFace =
      (filter Examples.TwoPoints.pts).value Examples.TwoPoints.edgeFace := by
  rw [cech_value₁, Examples.TwoPoints.cech_value]

end Line

/-! ### The empty index type -/

namespace EmptyIndex

/-- With no coordinates, every nonempty label set is a face at every nonnegative radius. -/
theorem mem_complex {V : Type*} (p : V → Fin 0 → ℝ) {r : ℝ} (hr : 0 ≤ r) {s : Finset V}
    (hs : s.Nonempty) : s ∈ complex p r :=
  (mem_complex_iff_pairwise p r s).2 ⟨hs, fun v _ w _ => by
    rw [Subsingleton.elim (p v) (p w), dist_self]
    linarith⟩

end EmptyIndex

end TDA.Filtration.Cech.SupNormExamples
