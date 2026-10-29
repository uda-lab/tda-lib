import TDA.Persistence.RipsQTameBottleneck
import TDA.Persistence.RipsGromovHausdorff
import Mathlib.Topology.MetricSpace.GromovHausdorff

/-!
# Metric stability of q-tame Rips diagrams

The strict-slack Hausdorff interleaving bound for totally bounded spaces passes to
the sharp factor-two bound by taking the infimum over positive slack. Compact
Gromov--Hausdorff stability and convergence of finite samples to an infinite target
are concrete consumers of that estimate.
-/

universe u v w z

namespace TDA.Persistence.Rips

open TDA.Filtration TDA.Persistence TDA.Persistence.RectangleMeasure MeasureTheory Metric Set GromovHausdorff
open scoped ENNReal NNReal Topology

noncomputable section

set_option maxHeartbeats 1000000 in
private theorem hausdorffEDist_ne_top_of_isometric_totallyBounded
    {X Y : Type u} {Z : Type v}
    [MetricSpace X] [MetricSpace Y] [MetricSpace Z]
    [Nonempty X] [Nonempty Y]
    {f : X → Z} {g : Y → Z} (hf : Isometry f) (hg : Isometry g)
    (hX : TotallyBounded (Set.univ : Set X))
    (hY : TotallyBounded (Set.univ : Set Y)) :
    Metric.hausdorffEDist (Set.range f) (Set.range g) ≠ ⊤ := by
  have hfrange : Set.range f = f '' Set.univ := by
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, Set.mem_univ x, rfl⟩
    · rintro ⟨x, _, rfl⟩
      exact ⟨x, rfl⟩
  have hgrange : Set.range g = g '' Set.univ := by
    ext z
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y, Set.mem_univ y, rfl⟩
    · rintro ⟨y, _, rfl⟩
      exact ⟨y, rfl⟩
  have hfb : Bornology.IsBounded (Set.range f) := by
    rw [hfrange]
    exact hf.lipschitz.isBounded_image hX.isBounded
  have hgb : Bornology.IsBounded (Set.range g) := by
    rw [hgrange]
    exact hg.lipschitz.isBounded_image hY.isBounded
  exact Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded
    (range_nonempty f) (range_nonempty g) hfb hgb

private theorem contentMultiplicity_eq_of_values_eq
    {X : Type*} {C : Set (Set X)} {m₁ m₂ : AddContent ℕ C}
    (hval : ∀ U ∈ C, m₁ U = m₂ U) (x : X) :
    contentMultiplicity m₁ x = contentMultiplicity m₂ x := by
  unfold contentMultiplicity
  congr 1
  ext n
  constructor
  · rintro ⟨U, hU, hxU, hn⟩
    exact ⟨U, hU, hxU, (hval U hU).symm.trans hn⟩
  · rintro ⟨U, hU, hxU, hn⟩
    exact ⟨U, hU, hxU, (hval U hU).trans hn⟩

private theorem persistenceMeasureValue_eq_of_interleavingIso
    {k : Type*} [Field k] {M N : PModule k ℝ}
    (e : M ≅ N) (hM : M.QTame) (hN : N.QTame)
    {a b c d : ℝ} (hab : a ≤ b) (hbc : b < c) (hcd : c ≤ d) :
    persistenceMeasureValue M hab hbc.le hcd =
      persistenceMeasureValue N hab hbc.le hcd := by
  let i := RealInterleaving.ofIso e
  have hMN := i.persistenceMeasureValue_box_le_of_qTame hN hab hcd
    (by simpa using (sub_pos.mpr hbc))
  have hNM := i.symm.persistenceMeasureValue_box_le_of_qTame hM hab hcd
    (by simpa using (sub_pos.mpr hbc))
  exact le_antisymm (by simpa using hMN) (by simpa using hNM)

private theorem essentialMeasureValue_eq_of_interleavingIso
    {k : Type*} [Field k] {M N : PModule k ℝ}
    (e : M ≅ N) (hM : M.QTame) (hN : N.QTame)
    {a b : ℝ} (hab : a ≤ b) :
    essentialMeasureValue M hab = essentialMeasureValue N hab := by
  let i := RealInterleaving.ofIso e
  have hMN := i.essentialMeasureValue_box_le_of_qTame hN hab
  have hNM := i.symm.essentialMeasureValue_box_le_of_qTame hM hab
  exact le_antisymm (by simpa using hMN) (by simpa using hNM)

private theorem moduleRectangleValue_eq_of_interleavingIso
    {k : Type*} [Field k] {M N : PModule k ℝ}
    (e : M ≅ N) (hM : M.QTame) (hN : N.QTame)
    (U : Set (Cut ℝ × Cut ℝ)) :
    moduleRectangleValue M U = moduleRectangleValue N U := by
  by_cases hU : U = ∅
  · simp [moduleRectangleValue, hU]
  · simp only [moduleRectangleValue, if_neg hU]
    let I := rectangleCellBox U
    by_cases hsep : I.upper 0 < I.lower 1
    · rw [persistenceBoxValue_of_separated M I hsep,
        persistenceBoxValue_of_separated N I hsep]
      have hMN := (RealInterleaving.ofIso e).persistenceMeasureValue_box_le_of_qTame
        hN (I.lower_lt_upper 0).le (I.lower_lt_upper 1).le
        (by simpa using (sub_pos.mpr hsep))
      have hNM := (RealInterleaving.ofIso e).symm.persistenceMeasureValue_box_le_of_qTame
        hM (I.lower_lt_upper 0).le (I.lower_lt_upper 1).le
        (by simpa using (sub_pos.mpr hsep))
      exact le_antisymm (by simpa using hMN) (by simpa using hNM)
    · simp [persistenceBoxValue, I, hsep]

private theorem moduleDiagramMultiplicity_eq_of_interleavingIso
    {k : Type*} [Field k] {M N : PModule k ℝ}
    (e : M ≅ N) (hM : M.QTame) (hN : N.QTame)
    (p : Cut ℝ × Cut ℝ) :
    moduleDiagramMultiplicity M hM p = moduleDiagramMultiplicity N hN p := by
  apply contentMultiplicity_eq_of_values_eq
  intro U hU
  change moduleRectangleValue M U = moduleRectangleValue N U
  exact moduleRectangleValue_eq_of_interleavingIso e hM hN U

private theorem moduleEssentialMultiplicity_eq_of_interleavingIso
    {k : Type*} [Field k] {M N : PModule k ℝ}
    (e : M ≅ N) (hM : M.QTame) (hN : N.QTame)
    (birth : Cut ℝ) :
    moduleEssentialMultiplicity M hM birth = moduleEssentialMultiplicity N hN birth := by
  apply contentMultiplicity_eq_of_values_eq
  intro U hU
  obtain ⟨a, b, hab, rfl⟩ := hU
  rw [essentialCutContent_apply M hM hab, essentialCutContent_apply N hN hab]
  exact essentialMeasureValue_eq_of_interleavingIso e hM hN hab

/-- The represented finite-birth decorated q-tame diagram is invariant under a persistence-module
isomorphism. Both finite-death rectangle contents and the essential birth boundary are
preserved by the zero-interleaving inequalities in the two directions.
-/
theorem ofQModule_eq_of_iso
    {k : Type*} [Field k] {M N : PModule k ℝ}
    (e : M ≅ N) (hM : M.QTame) (hN : N.QTame) :
    LocallyFiniteDecoratedDiagram.ofQModule hM =
      LocallyFiniteDecoratedDiagram.ofQModule hN := by
  apply LocallyFiniteDecoratedDiagram.ext
  funext p
  by_cases hInf : p.2 = infinityCut
  · have hess := moduleEssentialMultiplicity_eq_of_interleavingIso e hM hN p.1
    simp [LocallyFiniteDecoratedDiagram.ofQModule, moduleExtendedDiagramMultiplicity,
      hInf, hess]
  · have hfin := moduleDiagramMultiplicity_eq_of_interleavingIso e hM hN p
    simp [LocallyFiniteDecoratedDiagram.ofQModule, moduleExtendedDiagramMultiplicity,
      hInf, hfin]

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
spaces obey the sharp factor-two ambient Hausdorff bound. Near points need not
attain the Hausdorff infimum: the proof allows every positive slack and then
passes to its infimum in `ℝ≥0∞`.
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
  let δ : ℝ≥0 := ⟨2 * Metric.hausdorffDist (Set.range f) (Set.range g),
    mul_nonneg (by norm_num) hausdorffDist_nonneg⟩
  have hfin := hausdorffEDist_ne_top_of_isometric_totallyBounded hf hg hX hY
  calc
    _ ≤ (δ : ℝ≥0∞) := by
      apply ENNReal.le_of_forall_pos_le_add
      intro η hη _
      have hε : 2 * Metric.hausdorffDist (Set.range f) (Set.range g) <
          ((δ + η : ℝ≥0) : ℝ) := by
        change 2 * Metric.hausdorffDist (Set.range f) (Set.range g) <
          2 * Metric.hausdorffDist (Set.range f) (Set.range g) + (η : ℝ)
        exact lt_add_of_pos_right _ hη
      simpa only [ENNReal.ofReal_coe_nnreal, ENNReal.coe_add] using
        (qTameLocallyFiniteDiagram_bottleneck_le_of_hausdorff_lt
          hf hg hfin hε hX hY k n)
    _ = _ := by
      rw [ENNReal.coe_nnreal_eq δ]
      rw [show (δ : ℝ) = 2 * Metric.hausdorffDist (Set.range f) (Set.range g) by rfl]

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
