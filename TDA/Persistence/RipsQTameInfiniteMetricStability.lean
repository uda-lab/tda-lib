import TDA.Persistence.QTameDiagramStability
import TDA.Persistence.RipsQTameBottleneck
import TDA.Persistence.RipsGromovHausdorff
import Mathlib.Topology.MetricSpace.GromovHausdorff

/-!
# Metric stability of q-tame Rips diagrams

The sharp factor-two q-tame diagram estimate composes generic diagram stability
with the shared Rips module-interleaving bound at the same Hausdorff scale. Compact
Gromov--Hausdorff stability and convergence of finite samples to an infinite target
are concrete consumers of that estimate.
-/

universe u v w z

namespace TDA.Persistence.Rips

open TDA.Filtration TDA.Persistence TDA.Persistence.RectangleMeasure MeasureTheory Metric Set GromovHausdorff
open scoped ENNReal NNReal Topology

noncomputable section

/-- The represented finite-birth decorated q-tame diagram is invariant under a persistence-module
isomorphism. Both finite-death rectangle contents and the essential birth boundary are
preserved by the zero-interleaving inequalities in the two directions.
-/
theorem ofQModule_eq_of_iso
    {k : Type*} [Field k] {M N : PModule k ℝ}
    (e : M ≅ N) (hM : M.QTame) (hN : N.QTame) :
    LocallyFiniteDecoratedDiagram.ofQModule hM =
      LocallyFiniteDecoratedDiagram.ofQModule hN := by
  exact LocallyFiniteDecoratedDiagram.ofQModule_eq_of_iso e hM hN

/-- Isometrically equivalent vertex spaces have identical q-tame Rips diagrams,
even when their auxiliary linear orders are unrelated.
-/
theorem qTameLocallyFiniteDiagram_eq_of_isometryEquiv
    {X Y : Type u} [LinearOrder X] [MetricSpace X]
    [LinearOrder Y] [MetricSpace Y]
    (k : Type v) [Field k] (e : X ≃ᵢ Y)
    (hX : TotallyBounded (Set.univ : Set X))
    (hY : TotallyBounded (Set.univ : Set Y)) (n : ℕ) :
    qTameLocallyFiniteDiagram (X := X) k hX n =
      qTameLocallyFiniteDiagram (X := Y) k hY n := by
  exact ofQModule_eq_of_iso
    (sublevelModuleIsoOfIsometryEquiv (X := X) k e n)
    (qTame_of_totallyBounded k hX n) (qTame_of_totallyBounded k hY n)

/-- The complete locally finite q-tame Rips diagrams of nonempty totally bounded
spaces obey the sharp factor-two ambient Hausdorff bound. The proof composes generic
q-tame diagram stability with the shared Rips module bound; total boundedness passes
to each isometric image.
-/
theorem qTameLocallyFiniteDiagram_bottleneck_le_of_hausdorffDist
    {X Y : Type u} {Z : Type v}
    [LinearOrder X] [MetricSpace X] [Nonempty X]
    [LinearOrder Y] [MetricSpace Y] [Nonempty Y] [MetricSpace Z]
    {f : X → Z} {g : Y → Z} (hf : Isometry f) (hg : Isometry g)
    (hX : TotallyBounded (Set.univ : Set X))
    (hY : TotallyBounded (Set.univ : Set Y))
    (k : Type z) [Field k] (n : ℕ) :
    (qTameLocallyFiniteDiagram (X := X) k hX n).bottleneck
      (qTameLocallyFiniteDiagram (X := Y) k hY n) ≤
      ENNReal.ofReal (2 * Metric.hausdorffDist (Set.range f) (Set.range g)) := by
  have hXrange : TotallyBounded (Set.range f) := by
    rw [← Set.image_univ]
    exact (totallyBounded_image_iff hf.isUniformInducing).2 hX
  have hYrange : TotallyBounded (Set.range g) := by
    rw [← Set.image_univ]
    exact (totallyBounded_image_iff hg.isUniformInducing).2 hY
  calc
    _ ≤ realInterleavingDistance
        (sublevelModule k (Rips.filter (inferInstance : MetricSpace X)) n)
        (sublevelModule k (Rips.filter (inferInstance : MetricSpace Y)) n) := by
      simpa only [qTameLocallyFiniteDiagram] using
        LocallyFiniteDecoratedDiagram.qTame_bottleneck_le_realInterleavingDistance
          (qTame_of_totallyBounded k hX n) (qTame_of_totallyBounded k hY n)
    _ ≤ _ :=
      realInterleavingDistance_le_two_mul_hausdorffDist_of_totallyBounded
        k hf hg hXrange hYrange n

/-- Compact nonempty metric spaces inherit the factor-two Rips bottleneck
bound from their optimal compact Gromov--Hausdorff coupling. The isometries
into the coupling ambient need not preserve the chosen auxiliary vertex orders.
-/
theorem qTameLocallyFiniteDiagram_bottleneck_le_two_mul_ghDist
    {X Y : Type u}
    [LinearOrder X] [MetricSpace X] [CompactSpace X] [Nonempty X]
    [LinearOrder Y] [MetricSpace Y] [CompactSpace Y] [Nonempty Y]
    (k : Type v) [Field k] (n : ℕ) :
    (qTameLocallyFiniteDiagram (X := X) k
        (isCompact_univ.totallyBounded : TotallyBounded (Set.univ : Set X)) n).bottleneck
      (qTameLocallyFiniteDiagram (X := Y) k
        (isCompact_univ.totallyBounded : TotallyBounded (Set.univ : Set Y)) n) ≤
      ENNReal.ofReal (2 * ghDist X Y) := by
  simpa only [hausdorffDist_optimal] using
    qTameLocallyFiniteDiagram_bottleneck_le_of_hausdorffDist
      (isometry_optimalGHInjl X Y) (isometry_optimalGHInjr X Y)
      (isCompact_univ.totallyBounded : TotallyBounded (Set.univ : Set X))
      (isCompact_univ.totallyBounded : TotallyBounded (Set.univ : Set Y)) k n

/-- Finite samples with varying carriers and cardinalities converge in diagram
bottleneck distance to the q-tame diagram of a nonempty totally bounded target,
provided their isometric images converge to the target image in Hausdorff distance.
-/
theorem tendsto_qTameLocallyFiniteDiagram_bottleneck_of_hausdorffDist_tendsto_zero
    (k : Type w) [Field k] {ι : Type*} {l : Filter ι}
    (X : ι → Type u) (Y : Type u) {Z : Type v}
    [∀ i, Fintype (X i)] [∀ i, LinearOrder (X i)]
    [LinearOrder Y] [MetricSpace Y] [Nonempty Y]
    [∀ i, MetricSpace (X i)] [∀ i, Nonempty (X i)] [MetricSpace Z]
    {f : ∀ i, X i → Z} {g : Y → Z}
    (hf : ∀ i, Isometry (f i)) (hg : Isometry g)
    (hY : TotallyBounded (Set.univ : Set Y))
    (h : Filter.Tendsto
      (fun i => Metric.hausdorffDist (Set.range (f i)) (Set.range g)) l (𝓝 0))
    (n : ℕ) :
    Filter.Tendsto
      (fun i =>
        (qTameLocallyFiniteDiagram (X := X i) k
          (Set.finite_univ.totallyBounded : TotallyBounded (Set.univ : Set (X i))) n).bottleneck
          (qTameLocallyFiniteDiagram (X := Y) k hY n))
      l (𝓝 0) := by
  have hlim : Filter.Tendsto
      (fun i => ENNReal.ofReal
        (2 * Metric.hausdorffDist (Set.range (f i)) (Set.range g))) l (𝓝 0) := by
    simpa only [mul_zero, ENNReal.ofReal_zero] using
      ENNReal.tendsto_ofReal (h.const_mul 2)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ => bot_le) (fun i => by
      exact qTameLocallyFiniteDiagram_bottleneck_le_of_hausdorffDist
        (hf i) hg
        (Set.finite_univ.totallyBounded : TotallyBounded (Set.univ : Set (X i)))
        hY k n)

end
end TDA.Persistence.Rips
