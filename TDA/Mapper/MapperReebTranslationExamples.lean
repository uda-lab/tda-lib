import TDA.Mapper.MapperReebTranslation
import TDA.Mapper.MapperReebPerturbationExamples
import TDA.Mapper.RefinementHomologyInterleavingExamples
import TDA.Reeb.GraphCycleObstructionExamples

/-!
# Translation of categorical Mapper reconstructions: fixtures

T1. On the single edge with heights `(0, 2)`, along the covers of
`nonconstant_edge_convergent_reconstructions`, every reconstruction is at distance exactly `1`
from the reconstruction of the translate by `1` over the translated cover.

T2. Translation by `0` gives distance `0` for the Mapper reconstructions of the single edge and
for the interval components of `x ↦ 4x` on the unit interval.

T3. The exact Reeb distance `|c|` of a vertical translate, derived through the interval
components, on the triangle (a cycle) and on two disjoint edges (a disconnected graph).

T4. On the unit interval, the interval components of `x ↦ 4x` and `x ↦ 4x + 3` are at
interleaving distance exactly `3`.

N1. With empty covers of a nonempty graph, the reconstructions of `h` and `h + 1` are both empty
and at distance `0`, the resolutions are `0`, and the Reeb quotients are at distance `1`. Neither
the active-member hypothesis of the exact translation distance nor the coverage hypothesis of
`geometricInterleavingDistance_graphPLReebGraph_le_mapperReeb_add` can be dropped.
-/

open Set Filter
open scoped NNReal ENNReal Topology unitInterval

namespace TDA.Mapper.MapperReebTranslationExamples

open TDA.Reeb TDA.Reeb.OpenInterval TDA.Reeb.GraphPL TDA.Reeb.GraphRealization
open TDA.Mapper.GraphPL
open TDA.Reeb.Examples.GraphPL (h02)
open TDA.Reeb.Examples.GraphRealization (edgeGraph twoEdges)
open TDA.Reeb.Examples.GraphCycleObstruction (triangle)
open TDA.Mapper.MapperReebApproximationExamples (nonconstant_edge_convergent_reconstructions)
open TDA.Mapper.GraphPLReebStabilityExamples (twoEdgesHeight)
open TDA.Mapper.RefinementHomologyInterleavingExamples (scaleMap)

noncomputable section

/-! ## T1. Exact distance at every finite resolution -/

/-- Along the covers of `nonconstant_edge_convergent_reconstructions`, the reconstruction of the
edge with heights `(0, 2)` and that of its translate by `1` over the translated cover are at
distance exactly `1` at every stage; the limit in `translation_limit` is this constant value. -/
theorem translation_exact :
    ∃ n : ℕ → ℕ, ∃ a b : ∀ t, Fin (n t) → ℝ,
      (∀ t x, ∃ i, plHeight edgeGraph h02 x ∈ ioo (a t i) (b t i)) ∧
      (∀ t x, ∃ i, plHeight edgeGraph (fun v => h02 v + 1) x ∈
        ioo (a t i + 1) (b t i + 1)) ∧
      ∀ t, RGraph.geometricInterleavingDistance
        (graphPLMapperReconstruction edgeGraph h02 (a t) (b t))
        (graphPLMapperReconstruction edgeGraph (fun v => h02 v + 1)
          (fun i => a t i + 1) (fun i => b t i + 1)) = 1 := by
  obtain ⟨n, a, b, hcov, -⟩ := nonconstant_edge_convergent_reconstructions
  refine ⟨n, a, b, hcov, fun t x => ?_, fun t => ?_⟩
  · obtain ⟨i, hi⟩ := hcov t x
    refine ⟨i, ?_⟩
    rw [plHeight_add_const_apply]
    exact ⟨by linarith [hi.1], by linarith [hi.2]⟩
  · rw [geometricInterleavingDistance_graphPLMapperReconstruction_add_const_of_covers
      edgeGraph h02 (a t) (b t) 1 (hcov t), abs_one, ENNReal.ofReal_one]

/-! ## T2. Translation by zero -/

private theorem bddBelow_range_scaleMap : BddBelow (range (scaleMap 4)) :=
  ⟨0, by rintro _ ⟨x, rfl⟩; exact mul_nonneg (by norm_num) x.2.1⟩

/-- Translation by `0` gives distance `0` at the Mapper and interval-component levels. -/
theorem zero_translation {ι : Type} [Finite ι] (a b : ι → ℝ)
    (hcov : ∀ x, ∃ i, plHeight edgeGraph h02 x ∈ ioo (a i) (b i)) :
    RGraph.geometricInterleavingDistance (graphPLMapperReconstruction edgeGraph h02 a b)
        (graphPLMapperReconstruction edgeGraph (fun v => h02 v + 0) (fun i => a i + 0)
          (fun i => b i + 0)) = 0 ∧
      interleavingDistance (intervalComponents (scaleMap 4))
        (intervalComponents (scaleMap 4 + ContinuousMap.const I 0)) = 0 := by
  refine ⟨?_, ?_⟩
  · rw [geometricInterleavingDistance_graphPLMapperReconstruction_add_const_of_covers
      edgeGraph h02 a b 0 hcov, abs_zero, ENNReal.ofReal_zero]
  · rw [interleavingDistance_intervalComponents_add_const _ bddBelow_range_scaleMap,
      nnnorm_zero, ENNReal.coe_zero]

/-! ## T3. The Reeb distance through the interval components -/

/-- The Reeb distance of a vertical translate on a finite nonempty vertex type, derived from the
exact translation distance of the interval components. -/
theorem graphPLReebGraph_add_const_via_intervalComponents {V : Type} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (h : V → ℝ) (c : ℝ) :
    RGraph.geometricInterleavingDistance (graphPLReebGraph G h)
      (graphPLReebGraph G fun v => h v + c) = ENNReal.ofReal |c| := by
  have : Nonempty (Realization G) := ⟨vertex G (Classical.arbitrary V)⟩
  have hbdd : BddBelow (range (plHeight G h)) := by
    refine ⟨Finset.univ.inf' Finset.univ_nonempty h, ?_⟩
    rintro _ ⟨x, rfl⟩
    exact (plHeight_mem_Icc_of_forall (M := Finset.univ.sup' Finset.univ_nonempty h)
      (fun w => ⟨Finset.inf'_le _ (Finset.mem_univ w), Finset.le_sup' _ (Finset.mem_univ w)⟩)
      x).1
  rw [geometricInterleavingDistance_graphPLReebGraph, plHeight_add_const,
    interleavingDistance_intervalComponents_add_const _ hbdd, ← Real.enorm_eq_ofReal_abs]
  rfl

/-- On the triangle, a cycle, the cosheaf derivation gives the Reeb distance `|c|`. -/
theorem triangle_add_const_via_intervalComponents (c : ℝ) :
    RGraph.geometricInterleavingDistance (graphPLReebGraph triangle fun v => (v : ℝ))
      (graphPLReebGraph triangle fun v => (v : ℝ) + c) = ENNReal.ofReal |c| :=
  graphPLReebGraph_add_const_via_intervalComponents triangle _ c

/-- On two disjoint edges, a disconnected graph, the cosheaf derivation gives the Reeb distance
`|c|`. -/
theorem twoEdges_add_const_via_intervalComponents (c : ℝ) :
    RGraph.geometricInterleavingDistance (graphPLReebGraph twoEdges twoEdgesHeight)
      (graphPLReebGraph twoEdges fun v => twoEdgesHeight v + c) = ENNReal.ofReal |c| :=
  graphPLReebGraph_add_const_via_intervalComponents twoEdges _ c

/-! ## T4. A continuous map on the unit interval -/

/-- The interval components of `x ↦ 4x` and `x ↦ 4x + 3` on the unit interval are at
interleaving distance exactly `3`. -/
theorem scaleMap_translation :
    interleavingDistance (intervalComponents (scaleMap 4))
      (intervalComponents (scaleMap 4 + ContinuousMap.const I 3)) = 3 := by
  rw [interleavingDistance_intervalComponents_add_const _ bddBelow_range_scaleMap,
    show ‖(3 : ℝ)‖₊ = 3 from NNReal.eq (by simp)]
  norm_num

/-! ## N1. No active member -/

/-- Empty covers of a nonempty graph: the reconstructions of `h` and `h + 1` are at distance `0`
with resolutions `0`, while the Reeb quotients are at distance `1`. -/
theorem empty_cover_translation {V : Type} [Fintype V] [Nonempty V] (G : SimpleGraph V)
    (h : V → ℝ) (a b : Empty → ℝ) :
    RGraph.geometricInterleavingDistance (graphPLMapperReconstruction G h a b)
        (graphPLMapperReconstruction G (fun v => h v + 1) (fun i => a i + 1)
          (fun i => b i + 1)) = 0 ∧
      coverResolution a b = 0 ∧
      RGraph.geometricInterleavingDistance (graphPLReebGraph G h)
        (graphPLReebGraph G fun v => h v + 1) = 1 ∧
      ¬ RGraph.geometricInterleavingDistance (graphPLReebGraph G h)
          (graphPLReebGraph G fun v => h v + 1) ≤
        RGraph.geometricInterleavingDistance (graphPLMapperReconstruction G h a b)
          (graphPLMapperReconstruction G (fun v => h v + 1) (fun i => a i + 1)
            (fun i => b i + 1)) +
          (coverResolution a b : ℝ≥0∞) +
          coverResolution (fun i => a i + 1) (fun i => b i + 1) := by
  have h0 := geometricInterleavingDistance_graphPLMapperReconstruction_of_isEmpty G h
    (fun v => h v + 1) a b (fun i => a i + 1) (fun i => b i + 1)
  have hres : ∀ a b : Empty → ℝ, coverResolution a b = 0 := fun a b => by
    unfold coverResolution
    simp
  have hReeb : RGraph.geometricInterleavingDistance (graphPLReebGraph G h)
      (graphPLReebGraph G fun v => h v + 1) = 1 := by
    rw [geometricInterleavingDistance_graphPLReebGraph_add_const, abs_one, ENNReal.ofReal_one]
  refine ⟨h0, hres a b, hReeb, ?_⟩
  rw [hReeb, h0, hres, hres]
  simp

end

end TDA.Mapper.MapperReebTranslationExamples
