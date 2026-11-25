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

Client-facing forms of the compact bound: threshold statements over `ENNReal.ofReal`, an
order-free diagram `qTameLocallyFiniteDiagramOrderFree` that equals the diagram of every linear
order on the space and needs no `LinearOrder` instance, and event inclusions for outcome-dependent
metrics. The two carrier types of the compact bound must lie in one universe, because the Rips
homology modules of a carrier in `Type u` live in `ModuleCat.{max u v}` and the interleaving
machinery compares modules of one such universe. A client models its carriers in one universe from
the start, for example a finite sample as `ULift.{u} (Fin m)` against a target in `Type u`. No
cross-universe isometry invariance is stated, so the diagram of a space in `Type v` is not
identified with that of its `ULift` in a larger universe.
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

/-- Threshold form of the compact Gromov--Hausdorff bound: a diagram bottleneck distance
strictly above `ENNReal.ofReal ε` forces `ε / 2 < ghDist X Y`. No sign condition on `ε` is needed,
and the diagrams are the ones of the explicit orders carried by `X` and `Y`. -/
theorem half_lt_ghDist_of_ofReal_lt_qTameLocallyFiniteDiagram_bottleneck
    {X Y : Type u}
    [LinearOrder X] [MetricSpace X] [CompactSpace X] [Nonempty X]
    [LinearOrder Y] [MetricSpace Y] [CompactSpace Y] [Nonempty Y]
    (k : Type v) [Field k] (n : ℕ) {ε : ℝ}
    (h : ENNReal.ofReal ε <
      (qTameLocallyFiniteDiagram (X := X) k
        (isCompact_univ.totallyBounded : TotallyBounded (Set.univ : Set X)) n).bottleneck
      (qTameLocallyFiniteDiagram (X := Y) k
        (isCompact_univ.totallyBounded : TotallyBounded (Set.univ : Set Y)) n)) :
    ε / 2 < ghDist X Y := by
  have h2 := h.trans_le (qTameLocallyFiniteDiagram_bottleneck_le_two_mul_ghDist
    (X := X) (Y := Y) k n)
  rw [ENNReal.ofReal_lt_ofReal_iff'] at h2
  linarith [h2.1]

/-- Contrapositive of the threshold form: `ghDist X Y ≤ ε / 2` bounds the diagram bottleneck
distance by `ENNReal.ofReal ε`. -/
theorem qTameLocallyFiniteDiagram_bottleneck_le_ofReal_of_ghDist_le_half
    {X Y : Type u}
    [LinearOrder X] [MetricSpace X] [CompactSpace X] [Nonempty X]
    [LinearOrder Y] [MetricSpace Y] [CompactSpace Y] [Nonempty Y]
    (k : Type v) [Field k] (n : ℕ) {ε : ℝ} (h : ghDist X Y ≤ ε / 2) :
    (qTameLocallyFiniteDiagram (X := X) k
        (isCompact_univ.totallyBounded : TotallyBounded (Set.univ : Set X)) n).bottleneck
      (qTameLocallyFiniteDiagram (X := Y) k
        (isCompact_univ.totallyBounded : TotallyBounded (Set.univ : Set Y)) n) ≤
      ENNReal.ofReal ε :=
  (qTameLocallyFiniteDiagram_bottleneck_le_two_mul_ghDist (X := X) (Y := Y) k n).trans
    (ENNReal.ofReal_le_ofReal (by linarith))

/-- The q-tame Rips diagram does not depend on the auxiliary vertex order: two linear orders on
the same metric space give equal diagrams. The proof is the isometry invariance for the identity
equivalence. -/
theorem qTameLocallyFiniteDiagram_congr_linearOrder
    {X : Type u} [MetricSpace X] (o₁ o₂ : LinearOrder X)
    (k : Type v) [Field k] (hX : TotallyBounded (Set.univ : Set X)) (n : ℕ) :
    @qTameLocallyFiniteDiagram X o₁ _ k _ hX n =
      @qTameLocallyFiniteDiagram X o₂ _ k _ hX n :=
  @qTameLocallyFiniteDiagram_eq_of_isometryEquiv X X o₁ _ o₂ _ k _ (IsometryEquiv.refl X) hX hX n

/-- The q-tame Rips diagram of a totally bounded metric space, with the auxiliary vertex order
chosen classically (the well-ordering `WellOrderingRel`). It needs no `LinearOrder` instance. The
space is an explicit argument. By `qTameLocallyFiniteDiagramOrderFree_eq` it agrees with
`qTameLocallyFiniteDiagram` for every linear order on the space, so the choice is immaterial. -/
def qTameLocallyFiniteDiagramOrderFree (X : Type u) [MetricSpace X]
    (k : Type v) [Field k] (hX : TotallyBounded (Set.univ : Set X)) (n : ℕ) :
    LocallyFiniteDecoratedDiagram :=
  letI : LinearOrder X := IsWellOrder.linearOrder WellOrderingRel
  qTameLocallyFiniteDiagram (X := X) k hX n

/-- The order-free diagram equals the diagram of any supplied linear order. -/
theorem qTameLocallyFiniteDiagramOrderFree_eq
    (X : Type u) [LinearOrder X] [MetricSpace X]
    (k : Type v) [Field k] (hX : TotallyBounded (Set.univ : Set X)) (n : ℕ) :
    qTameLocallyFiniteDiagramOrderFree X k hX n = qTameLocallyFiniteDiagram (X := X) k hX n :=
  qTameLocallyFiniteDiagram_congr_linearOrder _ _ k hX n

/-- The order-free diagram is invariant under isometric equivalence. -/
theorem qTameLocallyFiniteDiagramOrderFree_eq_of_isometryEquiv
    {X Y : Type u} [MetricSpace X] [MetricSpace Y]
    (k : Type v) [Field k] (e : X ≃ᵢ Y)
    (hX : TotallyBounded (Set.univ : Set X))
    (hY : TotallyBounded (Set.univ : Set Y)) (n : ℕ) :
    qTameLocallyFiniteDiagramOrderFree X k hX n = qTameLocallyFiniteDiagramOrderFree Y k hY n :=
  letI : LinearOrder X := IsWellOrder.linearOrder WellOrderingRel
  letI : LinearOrder Y := IsWellOrder.linearOrder WellOrderingRel
  qTameLocallyFiniteDiagram_eq_of_isometryEquiv k e hX hY n

/-- Order-free form of the compact Gromov--Hausdorff stability bound: no `LinearOrder`
instance is needed on either nonempty compact metric space. -/
theorem qTameLocallyFiniteDiagramOrderFree_bottleneck_le_two_mul_ghDist
    {X Y : Type u} [MetricSpace X] [CompactSpace X] [Nonempty X]
    [MetricSpace Y] [CompactSpace Y] [Nonempty Y]
    (k : Type v) [Field k] (n : ℕ) :
    (qTameLocallyFiniteDiagramOrderFree X k
        (isCompact_univ.totallyBounded : TotallyBounded (Set.univ : Set X)) n).bottleneck
      (qTameLocallyFiniteDiagramOrderFree Y k
        (isCompact_univ.totallyBounded : TotallyBounded (Set.univ : Set Y)) n) ≤
      ENNReal.ofReal (2 * ghDist X Y) :=
  letI : LinearOrder X := IsWellOrder.linearOrder WellOrderingRel
  letI : LinearOrder Y := IsWellOrder.linearOrder WellOrderingRel
  qTameLocallyFiniteDiagram_bottleneck_le_two_mul_ghDist (X := X) (Y := Y) k n

/-- Order-free threshold form: a diagram bottleneck distance above `ENNReal.ofReal ε` forces
`ε / 2 < ghDist X Y`, with no sign condition on `ε` and no order instance. -/
theorem half_lt_ghDist_of_ofReal_lt_qTameLocallyFiniteDiagramOrderFree_bottleneck
    {X Y : Type u} [MetricSpace X] [CompactSpace X] [Nonempty X]
    [MetricSpace Y] [CompactSpace Y] [Nonempty Y]
    (k : Type v) [Field k] (n : ℕ) {ε : ℝ}
    (h : ENNReal.ofReal ε <
      (qTameLocallyFiniteDiagramOrderFree X k
        (isCompact_univ.totallyBounded : TotallyBounded (Set.univ : Set X)) n).bottleneck
      (qTameLocallyFiniteDiagramOrderFree Y k
        (isCompact_univ.totallyBounded : TotallyBounded (Set.univ : Set Y)) n)) :
    ε / 2 < ghDist X Y := by
  have h2 := h.trans_le
    (qTameLocallyFiniteDiagramOrderFree_bottleneck_le_two_mul_ghDist (X := X) (Y := Y) k n)
  rw [ENNReal.ofReal_lt_ofReal_iff'] at h2
  linarith [h2.1]

/-- Event inclusion for a family of compact nonempty spaces `X ω` and a fixed compact nonempty
target `Y`: the outcomes whose order-free Rips diagram is farther than `ε` from the target
diagram lie among those whose Gromov--Hausdorff distance exceeds `ε / 2`. No measurability,
positivity of `ε`, or order is assumed, so `MeasureTheory.measure_mono` transfers any bound on
the second set to the first. -/
theorem setOf_ofReal_lt_bottleneck_subset_setOf_half_lt_ghDist
    {Ω : Type w} (X : Ω → Type u) {Y : Type u}
    [∀ ω, MetricSpace (X ω)] [∀ ω, CompactSpace (X ω)] [∀ ω, Nonempty (X ω)]
    [MetricSpace Y] [CompactSpace Y] [Nonempty Y]
    (k : Type v) [Field k] (n : ℕ) (ε : ℝ) :
    {ω | ENNReal.ofReal ε <
        (qTameLocallyFiniteDiagramOrderFree (X ω) k
          (isCompact_univ.totallyBounded : TotallyBounded (Set.univ : Set (X ω))) n).bottleneck
          (qTameLocallyFiniteDiagramOrderFree Y k
            (isCompact_univ.totallyBounded : TotallyBounded (Set.univ : Set Y)) n)} ⊆
      {ω | ε / 2 < ghDist (X ω) Y} :=
  fun _ h =>
    half_lt_ghDist_of_ofReal_lt_qTameLocallyFiniteDiagramOrderFree_bottleneck k n h

/-- Event inclusion for an outcome-dependent metric on one fixed nonempty finite carrier `S`,
installed per outcome by `d ω`, against a fixed compact nonempty target `Y`. The carrier needs no
order and its compactness comes from finiteness. -/
theorem setOf_ofReal_lt_bottleneck_subset_setOf_half_lt_ghDist_of_finite
    {Ω : Type w} {S : Type u} [Finite S] [Nonempty S] (d : Ω → MetricSpace S)
    {Y : Type u} [MetricSpace Y] [CompactSpace Y] [Nonempty Y]
    (k : Type v) [Field k] (n : ℕ) (ε : ℝ) :
    {ω | letI := d ω
      ENNReal.ofReal ε <
        (qTameLocallyFiniteDiagramOrderFree S k
          (Set.finite_univ.totallyBounded : TotallyBounded (Set.univ : Set S)) n).bottleneck
          (qTameLocallyFiniteDiagramOrderFree Y k
            (isCompact_univ.totallyBounded : TotallyBounded (Set.univ : Set Y)) n)} ⊆
      {ω | letI := d ω
        ε / 2 < ghDist S Y} := by
  intro ω h
  let _ := d ω
  exact half_lt_ghDist_of_ofReal_lt_qTameLocallyFiniteDiagramOrderFree_bottleneck
    (X := S) (Y := Y) k n h

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
