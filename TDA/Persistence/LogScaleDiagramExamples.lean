import TDA.Persistence.LogScaleDiagram
import TDA.Persistence.CechRipsInterleavingExamples
import TDA.Persistence.SublevelConstructibleExamples
import TDA.Persistence.DiagramBottleneckLaws

set_option autoImplicit false

/-!
# Fixtures for log-scale diagrams

The log-scale results are instantiated on the two-point and Euclidean-triangle Čech and Rips
filters and on the certified filled and hollow triangles with their dimension grading cast to
`ℝ`. At the log time `log (6/5)` the triangle Rips sublevel has only vertices, while the three
Čech edges are present and the Čech 2-face is not. Above the dimension, the two-point
log-scale diagrams are empty. Two negative controls refute constructibility in degree `0` on
every grid and positivity of a Čech filter with repeated labels.
-/

namespace TDA.Persistence.LogScaleDiagramExamples

open CategoryTheory CategoryTheory.Limits TDA.Simplicial TDA.Filtration TDA.Persistence
open TDA.Persistence.FiniteConstructible TDA.Persistence.SublevelConstructibleExamples
open TDA.Filtration.Cech.Examples
open scoped NNReal ENNReal

/-! ### Positivity of the metric fixtures -/

theorem twoPoints_rips_positive : PositiveOnEdges (Rips.filter TwoPoints.metric) :=
  positiveOnEdges_rips _

theorem twoPoints_cech_positive : PositiveOnEdges (Cech.filter TwoPoints.pts) :=
  Cech.positiveOnEdges_cech TwoPoints.metric TwoPoints.pts TwoPoints.metric_dist

theorem triangle_rips_positive : PositiveOnEdges (Rips.filter Triangle.metric) :=
  positiveOnEdges_rips _

theorem triangle_cech_positive : PositiveOnEdges (Cech.filter Triangle.pts) :=
  Cech.positiveOnEdges_cech Triangle.metric Triangle.pts Triangle.metric_dist

/-! ### Triangle constructibility and the Čech–Rips comparison -/

/-- In every degree `n ≥ 1`, the log-scale triangle Rips module is constructible on its
positive-log grid. -/
theorem triangle_rips_isConstructible {n : ℕ} (hn : 1 ≤ n) :
    IsConstructible (logGrid (Rips.filter Triangle.metric))
      (logModule (ZMod 2) (Rips.filter Triangle.metric) n) :=
  logModule_isConstructible (ZMod 2) n hn triangle_rips_positive

/-- In every degree `n ≥ 1`, the log-scale triangle Čech module is constructible on its
positive-log grid. -/
theorem triangle_cech_isConstructible {n : ℕ} (hn : 1 ≤ n) :
    IsConstructible (logGrid (Cech.filter Triangle.pts))
      (logModule (ZMod 2) (Cech.filter Triangle.pts) n) :=
  logModule_isConstructible (ZMod 2) n hn triangle_cech_positive

/-- The log-scale triangle Rips and Čech diagrams are within `log 2` in every degree `n ≥ 1`. -/
theorem triangle_bottleneck_le {n : ℕ} (hn : 1 ≤ n) :
    bottleneck (logDgm (ZMod 2) (Rips.filter Triangle.metric) n)
        (logDgm (ZMod 2) (Cech.filter Triangle.pts) n) ≤ ENNReal.ofReal (Real.log 2) :=
  Cech.bottleneck_logDgm_rips_cech_le (ZMod 2) Triangle.metric Triangle.pts
    Triangle.metric_dist hn

/-- The log-scale two-point Rips and Čech diagrams over `ZMod 2` are within `log 2` in every
degree `n ≥ 1`. -/
theorem twoPoints_bottleneck_le_zmod {n : ℕ} (hn : 1 ≤ n) :
    bottleneck (logDgm (ZMod 2) (Rips.filter TwoPoints.metric) n)
        (logDgm (ZMod 2) (Cech.filter TwoPoints.pts) n) ≤ ENNReal.ofReal (Real.log 2) :=
  Cech.bottleneck_logDgm_rips_cech_le (ZMod 2) TwoPoints.metric TwoPoints.pts
    TwoPoints.metric_dist hn

/-- The log-scale two-point Rips and Čech diagrams over `ℚ` are within `log 2` in every degree
`n ≥ 1`. -/
theorem twoPoints_bottleneck_le_rat {n : ℕ} (hn : 1 ≤ n) :
    bottleneck (logDgm ℚ (Rips.filter TwoPoints.metric) n)
        (logDgm ℚ (Cech.filter TwoPoints.pts) n) ≤ ENNReal.ofReal (Real.log 2) :=
  Cech.bottleneck_logDgm_rips_cech_le ℚ TwoPoints.metric TwoPoints.pts
    TwoPoints.metric_dist hn

/-! ### The triangle at the log time `log (6/5)` -/

/-- No face with two vertices lies in the triangle Rips sublevel at `6/5`. -/
theorem triangle_rips_card_le_one :
    ∀ s ∈ (Rips.filter Triangle.metric).sublevel (6 / 5), s.card ≤ 1 := by
  intro s hs
  by_contra hcard
  obtain ⟨v, hv, w, hw, hvw⟩ := Finset.one_lt_card.1 (show 1 < s.card by omega)
  have hpair : ({v, w} : Finset (Fin 3)) ∈ (Rips.filter Triangle.metric).sublevel (6 / 5) := by
    rw [Rips.mem_sublevel_iff] at hs ⊢
    refine ⟨⟨v, by simp⟩, ?_⟩
    intro a ha b hb
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> apply hs.2 <;> assumption
  have key : ({v, w} : Finset (Fin 3)) = Triangle.edge01 ∨
      ({v, w} : Finset (Fin 3)) = Triangle.edge02 ∨
      ({v, w} : Finset (Fin 3)) = Triangle.edge12 ∨ v = w := by
    fin_cases v <;> fin_cases w <;> decide
  rcases key with h | h | h | h
  · exact Triangle.edge01_not_mem_rips (h ▸ hpair)
  · exact Triangle.edge02_not_mem_rips (h ▸ hpair)
  · exact Triangle.edge12_not_mem_rips (h ▸ hpair)
  · exact hvw h

/-- The degree-1 log-scale triangle Rips module vanishes at the log time `log (6/5)`. -/
theorem triangle_rips_isZero_log :
    IsZero ((logModule (ZMod 2) (Rips.filter Triangle.metric) 1).obj (Real.log (6 / 5))) := by
  change IsZero (simplicialHomology
    ((Rips.filter Triangle.metric).sublevel (Real.exp (Real.log (6 / 5)))) (ZMod 2) 1)
  rw [Real.exp_log (by norm_num)]
  exact isZero_simplicialHomology_of_card_le_one (ZMod 2) triangle_rips_card_le_one le_rfl

/-- At the log time `log (6/5)` the three triangle Čech edges are present. -/
theorem triangle_cech_edges_mem_log :
    Triangle.edge01 ∈ (Cech.filter Triangle.pts).sublevel (Real.exp (Real.log (6 / 5))) ∧
      Triangle.edge02 ∈ (Cech.filter Triangle.pts).sublevel (Real.exp (Real.log (6 / 5))) ∧
      Triangle.edge12 ∈ (Cech.filter Triangle.pts).sublevel (Real.exp (Real.log (6 / 5))) := by
  rw [Real.exp_log (by norm_num)]
  exact ⟨Cech.complex_le_sublevel _ _ Triangle.edge01_mem_complex,
    Cech.complex_le_sublevel _ _ Triangle.edge02_mem_complex,
    Cech.complex_le_sublevel _ _ Triangle.edge12_mem_complex⟩

/-- At the log time `log (6/5)` the triangle Čech 2-face is absent. -/
theorem triangle_cech_tri_not_mem_log :
    Triangle.tri ∉ (Cech.filter Triangle.pts).sublevel (Real.exp (Real.log (6 / 5))) := by
  rw [Real.exp_log (by norm_num), Cech.sublevel_eq_complex]
  exact Triangle.tri_not_mem_complex

/-! ### Degrees above the dimension -/

/-- On two vertices no face has `n + 1 ≥ 3` vertices. -/
private theorem face_isEmpty_fin_two (K : PreAbstractSimplicialComplex (Fin 2)) {n : ℕ}
    (hn : 2 ≤ n) : IsEmpty (Face K n) :=
  ⟨fun σ => by
    have h1 := Finset.card_le_univ σ.1
    have h2 := σ.2.2
    simp only [Fintype.card_fin] at h1
    omega⟩

/-- Every log-scale module of a filter on the two-vertex full complex vanishes in degrees
`n ≥ 2`. -/
theorem twoPoints_logModule_isZero (f : FilterFunction (Rips.fullComplex (Fin 2)) ℝ) {n : ℕ}
    (hn : 2 ≤ n) (t : ℝ) : IsZero ((logModule (ZMod 2) f n).obj t) := by
  change IsZero (simplicialHomology (f.sublevel (Real.exp t)) (ZMod 2) n)
  have := face_isEmpty_fin_two (f.sublevel (Real.exp t)) hn
  exact isZero_simplicialHomology_of_isEmpty_face (ZMod 2) n

/-- Every log-scale diagram of a filter on the two-vertex full complex is empty in degrees
`n ≥ 2`. -/
theorem twoPoints_logDgm_points (f : FilterFunction (Rips.fullComplex (Fin 2)) ℝ) {n : ℕ}
    (hn : 2 ≤ n) : (logDgm (ZMod 2) f n).points = 0 := by
  have hM : IsConstructible emptyGrid (logModule (ZMod 2) f n) :=
    (isConstructible_empty_iff _ _).2 (twoPoints_logModule_isZero f hn)
  have hr : Refines emptyGrid (logGrid f) := by
    rintro _ ⟨i, -⟩
    exact Fin.elim0 i
  have h := moduleDiagram_refinement (logModule (ZMod 2) f n) hr hM (fun i => Fin.elim0 i)
  exact (congrArg Diagram.points h).trans (moduleDiagram_empty_grid _ _)

theorem twoPoints_rips_logDgm_points {n : ℕ} (hn : 2 ≤ n) :
    (logDgm (ZMod 2) (Rips.filter TwoPoints.metric) n).points = 0 :=
  twoPoints_logDgm_points _ hn

theorem twoPoints_cech_logDgm_points {n : ℕ} (hn : 2 ≤ n) :
    (logDgm (ZMod 2) (Cech.filter TwoPoints.pts) n).points = 0 :=
  twoPoints_logDgm_points _ hn

/-- In degrees `n ≥ 2` the two-point log-scale Rips and Čech diagrams are at bottleneck
distance `0`. -/
theorem twoPoints_bottleneck_eq_zero {n : ℕ} (hn : 2 ≤ n) :
    bottleneck (logDgm (ZMod 2) (Rips.filter TwoPoints.metric) n)
      (logDgm (ZMod 2) (Cech.filter TwoPoints.pts) n) = 0 := by
  rw [Diagram.ext ((twoPoints_rips_logDgm_points hn).trans (twoPoints_cech_logDgm_points hn).symm)]
  exact bottleneck_self _

/-! ### Dimension filters -/

theorem filledReal_positive : PositiveOnEdges filledReal := by
  intro σ hσ
  change (0 : ℝ) < ((σ.val.card - 1 : ℕ) : ℝ)
  exact_mod_cast (show 0 < σ.val.card - 1 by omega)

theorem hollowReal_positive : PositiveOnEdges hollowReal := by
  intro σ hσ
  change (0 : ℝ) < ((σ.val.card - 1 : ℕ) : ℝ)
  exact_mod_cast (show 0 < σ.val.card - 1 by omega)

theorem filledReal_isConstructible :
    IsConstructible (logGrid filledReal) (logModule (ZMod 2) filledReal 1) :=
  logModule_isConstructible (ZMod 2) 1 le_rfl filledReal_positive

theorem hollowReal_isConstructible :
    IsConstructible (logGrid hollowReal) (logModule (ZMod 2) hollowReal 1) :=
  logModule_isConstructible (ZMod 2) 1 le_rfl hollowReal_positive

/-- Scaling the filled triangle by `2` moves its degree-1 log-scale diagram by at most
`log 2`. -/
theorem filledReal_scale_bottleneck_le :
    bottleneck (logDgm (ZMod 2) (filledReal.scale 2 two_pos) 1) (logDgm (ZMod 2) filledReal 1) ≤
      ENNReal.ofReal (Real.log 2) := by
  refine bottleneck_logDgm_le_log (ZMod 2) le_rfl one_le_two (fun s => ?_) (fun s => ?_)
    filledReal_positive
  · rw [FilterFunction.scale_value]
    have h : (0 : ℝ) ≤ filledReal.value s := by
      change (0 : ℝ) ≤ ((s.val.card - 1 : ℕ) : ℝ)
      exact Nat.cast_nonneg _
    linarith
  · rw [FilterFunction.scale_value]

/-! ### Negative control: degree `0` -/

/-- The vertex `{0}` of the two-vertex full complex. -/
def vertexFace : TotalFace (Rips.fullComplex (Fin 2)) := ⟨{0}, Finset.singleton_nonempty 0⟩

theorem vertexFace_card : vertexFace.val.card = 1 := Finset.card_singleton _

theorem rips_vertexFace_value : (Rips.filter TwoPoints.metric).value vertexFace = 0 :=
  Rips.diameter_singleton _ _

theorem cech_vertexFace_value_nonpos : (Cech.filter TwoPoints.pts).value vertexFace ≤ 0 :=
  (Cech.filter_value_le_rips TwoPoints.metric TwoPoints.pts TwoPoints.metric_dist
    vertexFace).trans rips_vertexFace_value.le

/-- On every finite grid, the degree-0 log-scale two-point Rips module is not constructible. -/
theorem twoPoints_rips_not_isConstructible_zero {m : ℕ} (c : Fin m ↪o ℝ) :
    ¬ IsConstructible c (logModule (ZMod 2) (Rips.filter TwoPoints.metric) 0) :=
  not_isConstructible_logModule_zero (ZMod 2) c vertexFace vertexFace_card
    rips_vertexFace_value.le

/-- On every finite grid, the degree-0 log-scale two-point Čech module is not constructible. -/
theorem twoPoints_cech_not_isConstructible_zero {m : ℕ} (c : Fin m ↪o ℝ) :
    ¬ IsConstructible c (logModule (ZMod 2) (Cech.filter TwoPoints.pts) 0) :=
  not_isConstructible_logModule_zero (ZMod 2) c vertexFace vertexFace_card
    cech_vertexFace_value_nonpos

/-- In particular the positive-log grid fails in degree `0`. -/
theorem twoPoints_rips_not_isConstructible_logGrid_zero :
    ¬ IsConstructible (logGrid (Rips.filter TwoPoints.metric))
      (logModule (ZMod 2) (Rips.filter TwoPoints.metric) 0) :=
  twoPoints_rips_not_isConstructible_zero _

theorem twoPoints_cech_not_isConstructible_logGrid_zero :
    ¬ IsConstructible (logGrid (Cech.filter TwoPoints.pts))
      (logModule (ZMod 2) (Cech.filter TwoPoints.pts) 0) :=
  twoPoints_cech_not_isConstructible_zero _

/-! ### Negative control: repeated labels -/

/-- Two distinct labels at one point give a Čech edge of value `0`, so positivity fails; no
label metric is compatible with this configuration. -/
theorem repeated_not_positive : ¬ PositiveOnEdges (Cech.filter Repeated.pts) := by
  intro h
  have := h Repeated.edgeFace Repeated.edge_card.ge
  rw [Repeated.cech_value] at this
  exact lt_irrefl 0 this

end TDA.Persistence.LogScaleDiagramExamples
