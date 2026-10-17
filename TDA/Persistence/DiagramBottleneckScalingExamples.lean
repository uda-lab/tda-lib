import TDA.Persistence.DiagramBottleneckScaling
import TDA.Persistence.FiniteFilterStabilitySingletonExamples

set_option autoImplicit false

/-!
# Positive scaling fixtures

The fixtures test the actual `Diagram.scale`, `FilterFunction.scale`, `dgm` and
`bottleneck` definitions. Scaling the merged one-vertex filter multiplies its sharp
bottleneck distance by `c`, and the result agrees with the merged sharp value. Translation
moves a vertex at zero by one, while scaling fixes it. Diagrams with different essential
counts stay at distance `⊤` after scaling, and scaling by `2` and then `2⁻¹` returns every
real diagram.
-/

namespace TDA.Persistence.ScalingExamples

open TDA.Filtration StabilityExamples
open scoped ENNReal

/-! ### Round trip -/

/-- Scaling by `2` and then by `2⁻¹` returns the diagram. -/
theorem diagram_scale_round_trip (D : Diagram ℝ) :
    (D.scale 2 two_pos).scale 2⁻¹ (inv_pos.2 two_pos) = D := by
  rw [Diagram.scale_scale]
  convert Diagram.scale_one D using 2
  norm_num

/-! ### The one-vertex filter -/

/-- Scaling the one-vertex filter at `a` gives the one-vertex filter at `c * a`. -/
theorem vertexFilter_scale (a : ℝ) {c : ℝ} (hc : 0 < c) :
    (vertexFilter a).scale c hc = vertexFilter (c * a) := by
  ext s
  rfl

/-- Positive scaling multiplies the sharp one-vertex distance by `c`. -/
theorem vertex_bottleneck_scale (a b : ℝ) {c : ℝ} (hc : 0 < c) :
    bottleneck (dgm (ZMod 2) (vertexFilter (c * a)) 0)
        (dgm (ZMod 2) (vertexFilter (c * b)) 0) =
      ENNReal.ofReal c * ENNReal.ofReal |a - b| := by
  rw [← vertexFilter_scale a hc, ← vertexFilter_scale b hc, bottleneck_dgm_scale,
    vertex_bottleneck_sharp]

/-- The scaling law agrees with the merged sharp value at the scaled grades. -/
theorem vertex_bottleneck_scale_agrees (a b : ℝ) {c : ℝ} (hc : 0 < c) :
    ENNReal.ofReal c * ENNReal.ofReal |a - b| = ENNReal.ofReal |c * a - c * b| := by
  rw [← ENNReal.ofReal_mul hc.le, ← mul_sub, abs_mul, abs_of_pos hc]

theorem vertex_bottleneck_scale_eq_sharp (a b : ℝ) {c : ℝ} (hc : 0 < c) :
    bottleneck (dgm (ZMod 2) (vertexFilter (c * a)) 0)
        (dgm (ZMod 2) (vertexFilter (c * b)) 0) =
      ENNReal.ofReal |c * a - c * b| := by
  rw [vertex_bottleneck_scale a b hc, vertex_bottleneck_scale_agrees a b hc]

/-! ### Translation versus scaling -/

theorem translate_vertexFilter_zero :
    translateFilterFunction (vertexFilter 0) 1 = vertexFilter 1 := by
  ext s
  change (0 : ℝ) + 1 = 1
  norm_num

/-- Translating the vertex at zero by one moves its diagram by exactly one. -/
theorem translate_vertex_distance :
    bottleneck (dgm (ZMod 2) (vertexFilter 0) 0)
      (dgm (ZMod 2) (translateFilterFunction (vertexFilter 0) 1) 0) = 1 := by
  rw [translate_vertexFilter_zero, vertex_bottleneck_sharp]
  norm_num

/-- Scaling fixes the vertex at zero. -/
theorem scale_vertexFilter_zero {c : ℝ} (hc : 0 < c) :
    (vertexFilter 0).scale c hc = vertexFilter 0 := by
  rw [vertexFilter_scale, mul_zero]

/-- Scaling the vertex at zero leaves its diagram at distance zero. -/
theorem scale_vertex_distance {c : ℝ} (hc : 0 < c) :
    bottleneck (dgm (ZMod 2) (vertexFilter 0) 0)
      (dgm (ZMod 2) ((vertexFilter 0).scale c hc) 0) = 0 := by
  rw [scale_vertexFilter_zero, vertex_bottleneck_sharp]
  simp

/-- The translation bridges on the one-vertex filter and its actual diagram. -/
theorem vertex_translate_eq_map (a c : ℝ) :
    translateFilterFunction (vertexFilter a) c =
        (vertexFilter a).map (OrderIso.addRight c).toOrderEmbedding ∧
      dgm (ZMod 2) (translateFilterFunction (vertexFilter a) c) 0 =
        (dgm (ZMod 2) (vertexFilter a) 0).map (OrderIso.addRight c).toOrderEmbedding := by
  refine ⟨translateFilterFunction_eq_map _ c, ?_⟩
  rw [dgm_translateFilterFunction, translateDiagram_eq_map]

/-! ### Infinite distance -/

/-- One essential birth at `1`. -/
noncomputable abbrev essentialOne : Diagram ℝ := orderedQ 0 1 (Fin.elim0, fun _ => 1)

/-- The empty diagram. -/
noncomputable abbrev emptyDiagram : Diagram ℝ := orderedQ 0 0 (Fin.elim0, Fin.elim0)

theorem bottleneck_essentialOne_empty : bottleneck essentialOne emptyDiagram = ⊤ := by
  rw [bottleneck_eq_top_iff]
  simp [essentialPart_orderedQ]

/-- Scaling keeps different essential counts at distance `⊤`. -/
theorem bottleneck_scale_essentialOne_empty {c : ℝ} (hc : 0 < c) :
    bottleneck (essentialOne.scale c hc) (emptyDiagram.scale c hc) = ⊤ := by
  rw [bottleneck_scale _ _ hc, bottleneck_essentialOne_empty,
    ENNReal.mul_top (ENNReal.ofReal_pos.2 hc).ne']

end TDA.Persistence.ScalingExamples
