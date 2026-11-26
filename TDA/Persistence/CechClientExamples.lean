import TDA.Persistence.CechStability
import TDA.Persistence.CechHausdorff
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

/-!
# Client statements of finite Čech perturbation and resampling stability

Regression fixtures for #1245, family 1 of the downstream-use audit (#1207). Each statement is
written as a downstream client writes it: the file opens no scope and declares no instance, and
imports only the two public stability modules and mathlib measure theory.

* Noise: a labelled cloud on `Fin m` whose points move by at most `ε`, the threshold form, the
  event inclusion for an outcome-dependent cloud and the tail transfer by measure monotonicity.
* Resampling: two samples of different sizes compared through the Hausdorff distance of their
  ranges, and the threshold form.
* Finite subsets of a space with no order, with a classically chosen label order; the diagram
  does not depend on that choice.
* Labels lifted to the coefficient field's universe with `ULift`.
-/

universe u w

namespace TDA.Persistence.CechClientExamples

/-- Moving every point of a cloud by at most `ε` moves its Čech diagrams by at most `ε`. -/
theorem noise_bottleneck_le {Z : Type w} [PseudoMetricSpace Z] {m : ℕ} (k : Type) [Field k]
    (p q : Fin m → Z) {ε : ℝ} (hε : 0 ≤ ε) (h : ∀ i, dist (p i) (q i) ≤ ε) (n : ℕ) :
    TDA.Persistence.bottleneck
        (TDA.Persistence.dgm k (TDA.Filtration.Cech.filter p) n)
        (TDA.Persistence.dgm k (TDA.Filtration.Cech.filter q) n) ≤ ENNReal.ofReal ε :=
  TDA.Persistence.Cech.bottleneck_dgm_le_of_dist_le k p q hε h n

/-- The threshold form, for every real `ε`. -/
theorem exists_moved_of_lt_bottleneck {Z : Type w} [PseudoMetricSpace Z] {m : ℕ}
    (k : Type) [Field k] (p q : Fin m → Z) {ε : ℝ} (n : ℕ)
    (h : ENNReal.ofReal ε <
      TDA.Persistence.bottleneck
        (TDA.Persistence.dgm k (TDA.Filtration.Cech.filter p) n)
        (TDA.Persistence.dgm k (TDA.Filtration.Cech.filter q) n)) :
    ∃ i, ε < dist (p i) (q i) :=
  TDA.Persistence.Cech.exists_lt_dist_of_ofReal_lt_bottleneck_dgm k p q n h

/-- The diagram error event of an outcome-dependent cloud lies inside the event that some
point is far from its target. No measurability is used. -/
theorem diagramErrorEvent_subset {Ω : Type*} {Z : Type w} [PseudoMetricSpace Z] {m : ℕ}
    (k : Type) [Field k] (p : Ω → Fin m → Z) (q : Fin m → Z) (ε : ℝ) (n : ℕ) :
    {ω | ENNReal.ofReal ε <
        TDA.Persistence.bottleneck
          (TDA.Persistence.dgm k (TDA.Filtration.Cech.filter (p ω)) n)
          (TDA.Persistence.dgm k (TDA.Filtration.Cech.filter q) n)} ⊆
      {ω | ∃ i, ε < dist (p ω i) (q i)} :=
  fun _ h => TDA.Persistence.Cech.exists_lt_dist_of_ofReal_lt_bottleneck_dgm k _ q n h

/-- A tail estimate for the point error transfers to the diagrams, for any measure. -/
theorem measure_diagramErrorEvent_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) {Z : Type w} [PseudoMetricSpace Z] {m : ℕ}
    (k : Type) [Field k] (p : Ω → Fin m → Z) (q : Fin m → Z) (ε : ℝ) (n : ℕ) {δ : ENNReal}
    (h : μ {ω | ∃ i, ε < dist (p ω i) (q i)} ≤ δ) :
    μ {ω | ENNReal.ofReal ε <
        TDA.Persistence.bottleneck
          (TDA.Persistence.dgm k (TDA.Filtration.Cech.filter (p ω)) n)
          (TDA.Persistence.dgm k (TDA.Filtration.Cech.filter q) n)} ≤ δ :=
  (MeasureTheory.measure_mono (diagramErrorEvent_subset k p q ε n)).trans h

/-- Two samples of different sizes: the diagrams differ by at most the Hausdorff distance of
the two ranges. -/
theorem resample_bottleneck_le {Z : Type w} [MetricSpace Z] {m l : ℕ} [NeZero m] [NeZero l]
    (k : Type) [Field k] (p : Fin m → Z) (q : Fin l → Z) (n : ℕ) :
    TDA.Persistence.bottleneck
        (TDA.Persistence.dgm k (TDA.Filtration.Cech.filter p) n)
        (TDA.Persistence.dgm k (TDA.Filtration.Cech.filter q) n) ≤
      ENNReal.ofReal (Metric.hausdorffDist (Set.range p) (Set.range q)) :=
  TDA.Persistence.Cech.bottleneck_dgm_le_hausdorffDist k p q n

/-- The threshold form of the resampling bound, for every real `ε`. -/
theorem lt_hausdorffDist_of_lt_bottleneck {Z : Type w} [MetricSpace Z] {m l : ℕ}
    [NeZero m] [NeZero l] (k : Type) [Field k] (p : Fin m → Z) (q : Fin l → Z) {ε : ℝ} (n : ℕ)
    (h : ENNReal.ofReal ε <
      TDA.Persistence.bottleneck
        (TDA.Persistence.dgm k (TDA.Filtration.Cech.filter p) n)
        (TDA.Persistence.dgm k (TDA.Filtration.Cech.filter q) n)) :
    ε < Metric.hausdorffDist (Set.range p) (Set.range q) :=
  TDA.Persistence.Cech.lt_hausdorffDist_of_ofReal_lt_bottleneck_dgm k p q n h

/-- Finite nonempty subsets of a space that carries no order, labelled by themselves with a
classically chosen order. -/
theorem finset_bottleneck_le_hausdorffDist {Z : Type} [MetricSpace Z] (k : Type) [Field k]
    (P Q : Finset Z) (hP : P.Nonempty) (hQ : Q.Nonempty) (n : ℕ) :
    letI : LinearOrder P := IsWellOrder.linearOrder WellOrderingRel
    letI : LinearOrder Q := IsWellOrder.linearOrder WellOrderingRel
    TDA.Persistence.bottleneck
        (TDA.Persistence.dgm k (TDA.Filtration.Cech.filter (fun x : P => (x : Z))) n)
        (TDA.Persistence.dgm k (TDA.Filtration.Cech.filter (fun x : Q => (x : Z))) n) ≤
      ENNReal.ofReal (Metric.hausdorffDist (P : Set Z) (Q : Set Z)) := by
  let _ : LinearOrder P := IsWellOrder.linearOrder WellOrderingRel
  let _ : LinearOrder Q := IsWellOrder.linearOrder WellOrderingRel
  have := hP.to_subtype
  have := hQ.to_subtype
  simpa using TDA.Persistence.Cech.bottleneck_dgm_le_hausdorffDist k
    (fun x : P => (x : Z)) (fun x : Q => (x : Z)) n

/-- The diagram of a finite subset does not depend on the order chosen for its labels. -/
theorem finset_dgm_eq_of_linearOrder {Z : Type} [MetricSpace Z] (k : Type) [Field k]
    (P : Finset Z) (o₁ o₂ : LinearOrder P) (n : ℕ) :
    (letI := o₁; TDA.Persistence.dgm k (TDA.Filtration.Cech.filter (fun x : P => (x : Z))) n) =
      (letI := o₂;
        TDA.Persistence.dgm k (TDA.Filtration.Cech.filter (fun x : P => (x : Z))) n) :=
  TDA.Persistence.Cech.dgm_eq_of_linearOrder o₁ o₂ k _ n

/-- Reversing the labels of a cloud on `Fin m` does not change its diagrams. -/
theorem dgm_comp_rev {Z : Type w} [MetricSpace Z] {m : ℕ} (k : Type) [Field k]
    (p : Fin m → Z) (n : ℕ) :
    TDA.Persistence.dgm k (TDA.Filtration.Cech.filter (p ∘ Fin.revPerm)) n =
      TDA.Persistence.dgm k (TDA.Filtration.Cech.filter p) n :=
  TDA.Persistence.Cech.dgm_eq_of_range_eq k _ p (Fin.revPerm.surjective.range_comp p) n

/-- Coefficients in any universe: the labels are lifted to the field's universe. -/
theorem noise_bottleneck_le_ulift {Z : Type w} [PseudoMetricSpace Z] {m : ℕ}
    (k : Type u) [Field k] (p q : ULift.{u} (Fin m) → Z) {ε : ℝ} (hε : 0 ≤ ε)
    (h : ∀ i, dist (p i) (q i) ≤ ε) (n : ℕ) :
    TDA.Persistence.bottleneck
        (TDA.Persistence.dgm k (TDA.Filtration.Cech.filter p) n)
        (TDA.Persistence.dgm k (TDA.Filtration.Cech.filter q) n) ≤ ENNReal.ofReal ε :=
  TDA.Persistence.Cech.bottleneck_dgm_le_of_dist_le k p q hε h n

end TDA.Persistence.CechClientExamples
