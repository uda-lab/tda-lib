import TDA.Persistence.RipsGromovHausdorff
import TDA.Persistence.LogScaleDiagramComparisonExamples
import TDA.Persistence.TriangleCechRipsExamples

/-! Finite GH–Rips consumers with unequal cardinalities, essential bars and sampling. -/

namespace TDA.Persistence.Rips.GromovHausdorffExamples

open TDA.Filtration TDA.Filtration.Cech.Examples Set Metric GromovHausdorff
open LogScaleDiagramComparisonExamples TriangleCechRipsExamples
open scoped ENNReal

noncomputable section

local instance twoMetric : MetricSpace (Fin 2) := TwoPoints.metric
local instance threeMetric : MetricSpace (Fin 3) := Triangle.metric

/-- Different finite cardinalities are accepted directly by the GH endpoint. -/
theorem two_triangle_gh_bound (k : Type) [Field k] (n : ℕ) :
    bottleneck (diagram k (Fin 2) n) (diagram k (Fin 3) n) ≤
      ENNReal.ofReal (2 * ghDist (Fin 2) (Fin 3)) :=
  bottleneck_diagram_le_two_mul_ghDist k _ _ n

/-- The new entry point is the existing two-point diagram, including its
essential occurrence and finite death at the edge's diameter time two. -/
theorem two_points_diagram :
    (diagram (ZMod 2) (Fin 2) 0).points =
      {((0 : ℝ), (⊤ : WithTop ℝ)), (0, ((2 : ℝ) : WithTop ℝ))} := by
  rw [diagram_eq_dgm]
  exact twoPoints_rips_dgm_zero

private theorem triangle_diagram :
    (diagram (ZMod 2) (Fin 3) 0).points =
      {((0 : ℝ), (⊤ : WithTop ℝ)), (0, ((2 : ℝ) : WithTop ℝ)),
        (0, ((Real.sqrt 5 : ℝ) : WithTop ℝ))} := by
  rw [diagram_eq_dgm]
  exact triangle_rips_dgm_zero

/-- The two-point and triangle discrepancy is genuinely positive: their essential
bar agrees, while their finite occurrence counts are one and two. -/
theorem two_triangle_positive_discrepancy :
    0 < bottleneck (diagram (ZMod 2) (Fin 2) 0) (diagram (ZMod 2) (Fin 3) 0) := by
  apply pos_iff_ne_zero.mpr
  intro h
  have he := (bottleneck_eq_zero_iff _ _).mp h
  have hc := congrArg (fun D : Diagram ℝ => D.points.card) he
  rw [two_points_diagram, triangle_diagram] at hc
  norm_num at hc

/-- The preceding positive discrepancy is between finite parts; the essential
occurrences on both inputs are the same bar born at zero. -/
theorem two_triangle_same_essential :
    essentialPart (diagram (ZMod 2) (Fin 2) 0).points = {0} ∧
      essentialPart (diagram (ZMod 2) (Fin 3) 0).points = {0} := by
  constructor
  · rw [two_points_diagram]
    rfl
  · rw [triangle_diagram]
    rfl

/-- Diameter rather than ball radius controls the finite death. -/
theorem diameter_scale_control :
    Rips.diameter TwoPoints.metric {0, 1} = 2 ∧
      {0, 1} ∉ (Rips.filter TwoPoints.metric).sublevel 1 := by
  constructor
  · rw [Rips.diameter_pair, TwoPoints.metric_dist, TwoPoints.dist_pts]
  · exact TwoPoints.edge_not_mem_rips_one

private def midpoint (_ : Unit) : ℝ := 1

private theorem midpoint_isometry : Isometry midpoint := by
  apply Isometry.of_dist_eq
  intro x y
  cases x
  cases y
  simp [midpoint]

private theorem two_isometry : Isometry TwoPoints.pts :=
  Isometry.of_dist_eq TwoPoints.metric_dist

private theorem midpoint_hausdorff_le_one :
    hausdorffDist (range midpoint) (range TwoPoints.pts) ≤ 1 := by
  apply hausdorffDist_le_of_mem_dist (by norm_num)
  · rintro x ⟨u, rfl⟩
    exact ⟨TwoPoints.pts 0, mem_range_self _, by norm_num [midpoint, TwoPoints.pts, Real.dist_eq]⟩
  · rintro x ⟨i, rfl⟩
    refine ⟨midpoint (), mem_range_self _, ?_⟩
    fin_cases i <;> norm_num [midpoint, TwoPoints.pts, Real.dist_eq]

/-- A finite sample consisting of the midpoint compares with both endpoints in
an ambient space that is neither finite nor compact. -/
theorem midpoint_sampling_bound (k : Type) [Field k] (n : ℕ) :
    bottleneck (diagram k Unit n) (diagram k (Fin 2) n) ≤ 2 := by
  simpa using bottleneck_diagram_le_two_mul_of_hausdorffDist_le k
    midpoint_isometry two_isometry midpoint_hausdorff_le_one n

/-- The geometric construction really supplies a many-to-one correspondence:
both distinct endpoints relate to the single midpoint, with distortion at most two. -/
theorem midpoint_many_to_one :
    ∃ C : SetRel Unit (Fin 2), ((), 0) ∈ C ∧ ((), 1) ∈ C ∧
      ∀ x x' y y', (x, y) ∈ C → (x', y') ∈ C → |dist x x' - dist y y'| ≤ 2 := by
  obtain ⟨C, _, hI, hdist⟩ :=
    exists_relation_distortion_le_hausdorffDist midpoint_isometry two_isometry
  obtain ⟨x, hx⟩ := hI 0
  obtain ⟨x', hx'⟩ := hI 1
  refine ⟨C, ?_, ?_, ?_⟩
  · simpa only [SetRel.mem_inv, Subsingleton.elim x ()] using hx
  · simpa only [SetRel.mem_inv, Subsingleton.elim x' ()] using hx'
  · intro a b y y' ha hb
    exact (hdist a b y y' ha hb).trans (by linarith [midpoint_hausdorff_le_one])

/-- A coefficient field in a larger universe needs no change to the finite spaces. -/
theorem lifted_field_gh_bound (n : ℕ) :
    bottleneck (diagram (ULift.{1} ℚ) (Fin 2) n) (diagram (ULift.{1} ℚ) (Fin 3) n) ≤
      ENNReal.ofReal (2 * ghDist (Fin 2) (Fin 3)) :=
  bottleneck_diagram_le_two_mul_ghDist _ _ _ n

private def reversedPoints : Bool → ℝ := fun b => if b then 0 else 2

private theorem reversedPoints_injective : Function.Injective reversedPoints := by
  intro b c h
  cases b <;> cases c <;> first | rfl | norm_num [reversedPoints] at h

local instance reversedMetric : MetricSpace Bool :=
  MetricSpace.induced reversedPoints reversedPoints_injective inferInstance

private def reversedEquiv : Fin 2 ≃ᵢ Bool where
  toEquiv := finTwoEquiv.trans Equiv.boolNot
  isometry_toFun := by
    apply Isometry.of_dist_eq
    intro i j
    have hv (a : Fin 2) : reversedPoints ((finTwoEquiv.trans Equiv.boolNot) a) =
        TwoPoints.pts a := by fin_cases a <;> rfl
    change dist (reversedPoints ((finTwoEquiv.trans Equiv.boolNot) i))
      (reversedPoints ((finTwoEquiv.trans Equiv.boolNot) j)) = TwoPoints.metric.dist i j
    rw [hv, hv, TwoPoints.metric_dist]

/-- The relabelling reverses the order of the two vertices. -/
theorem reversedEquiv_not_monotone : ¬ Monotone (reversedEquiv : Fin 2 → Bool) := by
  intro h
  have hh := h (show (0 : Fin 2) ≤ 1 by decide)
  change true ≤ false at hh
  exact (by decide : ¬ (true ≤ false)) hh

/-- Diagrams agree across the explicitly non-order-preserving isometry. -/
theorem reversed_labels_same_diagram (k : Type) [Field k] (n : ℕ) :
    diagram k (Fin 2) n = diagram k Bool n := by
  exact diagram_eq_of_isometryEquiv k reversedEquiv n

/-- Isometric relabelling really realizes zero bottleneck discrepancy. -/
theorem reversed_labels_zero_bottleneck (k : Type) [Field k] (n : ℕ) :
    bottleneck (diagram k (Fin 2) n) (diagram k Bool n) = 0 := by
  rw [reversed_labels_same_diagram]
  exact bottleneck_self _

end
end TDA.Persistence.Rips.GromovHausdorffExamples
