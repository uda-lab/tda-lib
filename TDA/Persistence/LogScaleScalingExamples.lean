import TDA.Persistence.LogScaleScaling
import TDA.Persistence.LogScaleDiagramComparisonExamples
import TDA.Persistence.LogScaleDiagramExamples
import TDA.Filtration.CechExamples

set_option autoImplicit false

/-!
# Fixtures for log-scale scaling and translation

These fixtures cover positive and negative log shifts, the identity control, the scaled
two-point configuration, scale invariance, the negative control where scaling cannot create
positivity, and translation preserving an infinite bottleneck.
-/

namespace TDA.Persistence.LogScaleScalingExamples

open CategoryTheory CategoryTheory.Limits TDA.Simplicial TDA.Filtration TDA.Persistence
open TDA.Persistence.Examples
open TDA.Persistence.FiniteConstructible
open TDA.Persistence.SublevelConstructibleExamples
open TDA.Persistence.LogScaleDiagramExamples
open TDA.Persistence.LogScaleDiagramComparisonExamples
open TDA.Persistence.Reduction.Examples
open TDA.Filtration.Cech.Examples
open scoped NNReal ENNReal

/-! ### Positive and identity shifts -/

/-- Scaling the filled triangle by `2` translates its degree-one log bar by `log 2`. -/
theorem filledReal_scale_two_logDgm_one :
    (logDgm (ZMod 2) (filledReal.scale 2 two_pos) 1).points =
      {(Real.log 2, ((Real.log 2 + Real.log 2 : ℝ) : WithTop ℝ))} := by
  rw [logDgm_scale_points (ZMod 2) le_rfl filledReal filledReal_positive two_pos,
    filledReal_logDgm_one]
  simp [translateDiagramPoint, add_comm]

/-- The general log-scale scaling law specializes at `c = 1` to an identity. -/
theorem logDgm_scale_one (k : Type) [Field k] {n : ℕ} (hn : 1 ≤ n)
    {V : Type} [LinearOrder V] {K : PreAbstractSimplicialComplex V}
    [Fintype (TDA.Simplicial.TotalFace K)] (f : FilterFunction K ℝ)
    (hf : PositiveOnEdges f) :
    logDgm k (f.scale 1 one_pos) n = logDgm k f n := by
  rw [logDgm_scale k hn f hf one_pos, Real.log_one, translateDiagram_zero]

/-- The identity control for the filled triangle agrees with `FilterFunction.scale_one`. -/
theorem filledReal_logDgm_scale_one :
    logDgm (ZMod 2) (filledReal.scale 1 one_pos) 1 =
      logDgm (ZMod 2) filledReal 1 := by
  exact logDgm_scale_one (ZMod 2) le_rfl filledReal filledReal_positive

/-- The identity control for the hollow triangle agrees with `FilterFunction.scale_one`. -/
theorem hollowReal_logDgm_scale_one :
    logDgm (ZMod 2) (hollowReal.scale 1 one_pos) 1 =
      logDgm (ZMod 2) hollowReal 1 := by
  exact logDgm_scale_one (ZMod 2) le_rfl hollowReal hollowReal_positive

/-! ### Negative shifts -/

/-- Scaling the filled triangle by `1/2` produces a negative log birth. -/
theorem filledReal_scale_half_logDgm_one :
    (logDgm (ZMod 2) (filledReal.scale (1 / 2 : ℝ) (by norm_num)) 1).points =
      {(-Real.log 2, ((0 : ℝ) : WithTop ℝ))} := by
  have hlog : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
    rw [one_div, Real.log_inv]
  rw [logDgm_scale_points (ZMod 2) le_rfl filledReal filledReal_positive
    (by norm_num : (0 : ℝ) < 1 / 2), filledReal_logDgm_one]
  simp [translateDiagramPoint, hlog, add_comm]

/-- Scaling the hollow triangle by `1/2` translates its essential bar negatively. -/
theorem hollowReal_scale_half_logDgm_one :
    (logDgm (ZMod 2) (hollowReal.scale (1 / 2 : ℝ) (by norm_num)) 1).points =
      {(-Real.log 2, (⊤ : WithTop ℝ))} := by
  have hlog : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
    rw [one_div, Real.log_inv]
  rw [logDgm_scale_points (ZMod 2) le_rfl hollowReal hollowReal_positive
    (by norm_num : (0 : ℝ) < 1 / 2), hollowReal_logDgm_one]
  simp [translateDiagramPoint, hlog]

/-- The birth in the half-scaled filled fixture is strictly negative. -/
theorem filledReal_scale_half_birth_neg : -Real.log 2 < 0 := by
  exact neg_lt_zero.mpr (Real.log_pos one_lt_two)

/-! ### Scaled two-point configuration -/

/-- The two-point configuration obtained by multiplying both ambient points by `2`. -/
def scaledPts : Fin 2 → ℝ := fun v => (2 : ℝ) • TwoPoints.pts v

/-- The scaled two-point configuration is the literal vector `[0, 4]`. -/
theorem scaledPts_eq : scaledPts = ![0, 4] := by
  funext v
  fin_cases v <;> norm_num [scaledPts, TwoPoints.pts, smul_eq_mul]

private theorem scaledPts_injective : Function.Injective scaledPts := by
  rw [scaledPts_eq]
  intro i j h
  fin_cases i <;> fin_cases j <;> first | rfl | norm_num at h

/-- The label metric induced by the scaled two-point configuration. -/
noncomputable abbrev scaledMetric : MetricSpace (Fin 2) :=
  MetricSpace.induced scaledPts scaledPts_injective inferInstance

/-- Distances in `scaledMetric` are twice the original two-point distances. -/
theorem scaledMetric_dist (v w : Fin 2) :
    scaledMetric.dist v w = 2 * TwoPoints.metric.dist v w := by
  change dist (scaledPts v) (scaledPts w) = 2 * dist (TwoPoints.pts v) (TwoPoints.pts w)
  simp only [scaledPts, smul_eq_mul, Real.dist_eq]
  rw [← mul_sub, abs_mul, abs_of_pos (two_pos : (0 : ℝ) < 2)]

/-- The scaled Rips filter is the positive scaling of the original Rips filter. -/
theorem scaled_rips_eq :
    Rips.filter scaledMetric = (Rips.filter TwoPoints.metric).scale 2 two_pos := by
  exact Rips.filter_eq_scale_of_dist TwoPoints.metric scaledMetric two_pos scaledMetric_dist

/-- The scaled Čech filter is the positive scaling of the original Čech filter. -/
theorem scaled_cech_eq :
    Cech.filter scaledPts = (Cech.filter TwoPoints.pts).scale 2 two_pos := by
  exact Cech.filter_smul TwoPoints.pts two_pos

/-- The scaled two-point Rips log diagram is empty in every degree `n ≥ 1`. -/
theorem scaled_rips_logDgm_pos {n : ℕ} (hn : 1 ≤ n) :
    (logDgm (ZMod 2) (Rips.filter scaledMetric) n).points = 0 := by
  rw [scaled_rips_eq,
    logDgm_scale_points (ZMod 2) hn (Rips.filter TwoPoints.metric)
      twoPoints_rips_positive two_pos,
    twoPoints_rips_logDgm_pos hn, Multiset.map_zero]

/-- The scaled two-point Čech log diagram is empty in every degree `n ≥ 1`. -/
theorem scaled_cech_logDgm_pos {n : ℕ} (hn : 1 ≤ n) :
    (logDgm (ZMod 2) (Cech.filter scaledPts) n).points = 0 := by
  rw [scaled_cech_eq,
    logDgm_scale_points (ZMod 2) hn (Cech.filter TwoPoints.pts)
      twoPoints_cech_positive two_pos,
    twoPoints_cech_logDgm_pos hn, Multiset.map_zero]

/-- The scaled two-point Rips--Čech log bottleneck equals the unscaled one. -/
theorem scaled_bottleneck_eq {n : ℕ} (hn : 1 ≤ n) :
    bottleneck (logDgm (ZMod 2) (Rips.filter scaledMetric) n)
        (logDgm (ZMod 2) (Cech.filter scaledPts) n) =
      bottleneck (logDgm (ZMod 2) (Rips.filter TwoPoints.metric) n)
        (logDgm (ZMod 2) (Cech.filter TwoPoints.pts) n) := by
  exact Cech.bottleneck_logDgm_rips_cech_scale (ZMod 2) TwoPoints.metric scaledMetric
    TwoPoints.pts two_pos TwoPoints.metric_dist scaledMetric_dist hn

/-- The scaled two-point Rips--Čech bottleneck retains the direct `log 2` bound. -/
theorem scaled_bottleneck_le_log_two {n : ℕ} (hn : 1 ≤ n) :
    bottleneck (logDgm (ZMod 2) (Rips.filter scaledMetric) n)
        (logDgm (ZMod 2) (Cech.filter scaledPts) n) ≤
      ENNReal.ofReal (Real.log 2) := by
  have hd : ∀ v w, scaledMetric.dist v w = dist (scaledPts v) (scaledPts w) := by
    intro v w
    rfl
  simpa using
    (Cech.bottleneck_logDgm_rips_cech_le (ZMod 2) scaledMetric scaledPts
      hd hn)

/-! ### Invariance and negative control -/

/-- Scaling the filled and hollow fixtures by `3` preserves their log bottleneck. -/
theorem filled_hollow_scale_three :
    bottleneck (logDgm (ZMod 2) (filledReal.scale 3 (by norm_num)) 1)
        (logDgm (ZMod 2) (hollowReal.scale 3 (by norm_num)) 1) =
      bottleneck (logDgm (ZMod 2) filledReal 1)
        (logDgm (ZMod 2) hollowReal 1) := by
  rw [logDgm_scale (ZMod 2) le_rfl filledReal filledReal_positive (by norm_num),
    logDgm_scale (ZMod 2) le_rfl hollowReal hollowReal_positive (by norm_num)]
  exact bottleneck_translateDiagram _ _ _

/-- Positive scaling cannot repair the repeated-label Čech positivity failure. -/
theorem repeated_scale_not_positive {c : ℝ} (hc : 0 < c) :
    ¬ PositiveOnEdges ((Cech.filter Repeated.pts).scale c hc) := by
  rw [positiveOnEdges_scale_iff hc]
  exact repeated_not_positive

/-! ### Infinite bottleneck -/

/-- One essential birth at `0`, represented as one essential ordered coordinate. -/
noncomputable abbrev essentialOne : Diagram ℝ :=
  orderedQ 0 1 (Fin.elim0, fun _ => 0)

/-- The empty diagram used for the infinite-bottleneck fixture. -/
noncomputable abbrev emptyDiagram : Diagram ℝ :=
  orderedQ 0 0 (Fin.elim0, Fin.elim0)

/-- Different essential counts give an infinite bottleneck in the F7 fixture.

The empty diagram is used in place of `0 : Diagram ℝ`, for which this API has no instance. -/
theorem bottleneck_essentialOne_zero : bottleneck essentialOne emptyDiagram = ⊤ := by
  rw [bottleneck_eq_top_iff]
  simp [essentialPart_orderedQ]

/-- A common translation preserves the infinite bottleneck, including `⊤`. -/
theorem bottleneck_translate_essentialOne :
    bottleneck (translateDiagram essentialOne (Real.log 2))
        (translateDiagram emptyDiagram (Real.log 2)) = ⊤ := by
  rw [bottleneck_translateDiagram, bottleneck_essentialOne_zero]

end TDA.Persistence.LogScaleScalingExamples
