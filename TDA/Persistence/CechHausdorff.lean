import TDA.Persistence.CechRelationInterleaving
import TDA.Persistence.DiagramBottleneckLaws
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Finite ambient Čech Hausdorff stability and sampling

Finite configurations may have different label counts and repeated points. Their full
radius-filter diagrams differ by at most the Hausdorff distance of their ranges, in
every degree. The fixed ambient space supplies the possible centers. Its properness
is unnecessary: finite ranges supply nearest points for the label correspondence,
while the face-value argument never chooses a minimizing center.

Sampling bounds use extended Hausdorff distance, so an unbounded or empty target does
not acquire a spurious real-valued error of zero. The target itself needs no diagram.
-/

universe u v w

namespace TDA.Persistence.Cech

open TDA.Filtration Set Metric
open scoped NNReal ENNReal

noncomputable section

/-- Finite nonempty configurations admit a total closed Hausdorff correspondence.
No metric on labels, injectivity or equal cardinality is required. -/
theorem exists_relation_dist_le_hausdorffDist
    {Z : Type w} [MetricSpace Z] {V : Type u} {W : Type v}
    [Fintype V] [Fintype W] [Nonempty V] [Nonempty W]
    (p : V → Z) (q : W → Z) :
    ∃ C : SetRel V W,
      Relator.LeftTotal (fun v w => (v, w) ∈ C) ∧
      Relator.LeftTotal (fun w v => (w, v) ∈ C.inv) ∧
      ∀ v w, (v, w) ∈ C → dist (p v) (q w) ≤ hausdorffDist (range p) (range q) := by
  let r := hausdorffDist (range p) (range q)
  let C : SetRel V W := {vw | dist (p vw.1) (q vw.2) ≤ r}
  have hp := (Set.finite_range p).isCompact
  have hq := (Set.finite_range q).isCompact
  have hfin : hausdorffEDist (range p) (range q) ≠ ⊤ :=
    hausdorffEDist_ne_top_of_nonempty_of_bounded (range_nonempty _) (range_nonempty _)
      hp.isBounded hq.isBounded
  refine ⟨C, ?_, ?_, fun _ _ h => h⟩
  · intro v
    obtain ⟨_, ⟨w, rfl⟩, hw⟩ := hq.exists_infDist_eq_dist (range_nonempty q) (p v)
    refine ⟨w, ?_⟩
    change dist (p v) (q w) ≤ r
    rw [← hw]
    exact infDist_le_hausdorffDist_of_mem (mem_range_self v) hfin
  · intro w
    obtain ⟨_, ⟨v, rfl⟩, hv⟩ := hp.exists_infDist_eq_dist (range_nonempty p) (q w)
    refine ⟨v, ?_⟩
    change dist (p v) (q w) ≤ r
    rw [dist_comm, ← hv]
    dsimp only [r]
    rw [hausdorffDist_comm]
    exact infDist_le_hausdorffDist_of_mem (mem_range_self w)
      (by simpa only [hausdorffEDist_comm] using hfin)

section Ordered

variable {Z : Type w} [MetricSpace Z] {V W : Type u}
variable [LinearOrder V] [LinearOrder W] [Fintype V] [Fintype W]
variable (k : Type u) [Field k] (p : V → Z) (q : W → Z)

/-- Ambient Hausdorff stability for full finite Čech radius-filter diagrams, with
constant one at radius scale and all essential bars retained. -/
theorem bottleneck_dgm_le_hausdorffDist [Nonempty V] [Nonempty W] (n : ℕ) :
    bottleneck (dgm k (Cech.filter p) n) (dgm k (Cech.filter q) n) ≤
      ENNReal.ofReal (hausdorffDist (range p) (range q)) := by
  obtain ⟨C, hCT, hIT, h⟩ := exists_relation_dist_le_hausdorffDist p q
  let ε : ℝ≥0 := ⟨hausdorffDist (range p) (range q), hausdorffDist_nonneg⟩
  calc
    _ ≤ (ε : ℝ≥0∞) := bottleneck_dgm_le_of_relation (C := C) (ε := ε)
      p q hCT hIT h k n
    _ = _ := ENNReal.coe_nnreal_eq ε

/-- Extended Hausdorff sampling bounds retain the distinction between infinity and zero. -/
theorem bottleneck_dgm_le_hausdorffEDist [Nonempty V] [Nonempty W] (n : ℕ) :
    bottleneck (dgm k (Cech.filter p) n) (dgm k (Cech.filter q) n) ≤
      hausdorffEDist (range p) (range q) := by
  have hfin : hausdorffEDist (range p) (range q) ≠ ⊤ :=
    hausdorffEDist_ne_top_of_nonempty_of_bounded (range_nonempty _) (range_nonempty _)
      (Set.finite_range p).isCompact.isBounded (Set.finite_range q).isCompact.isBounded
  simpa only [hausdorffDist, ENNReal.ofReal_toReal hfin] using
    bottleneck_dgm_le_hausdorffDist k p q n

/-- A finite sample error controls its discrepancy from any other finite configuration. -/
theorem bottleneck_dgm_le_of_hausdorffEDist_le [Nonempty V] [Nonempty W]
    {ε : ℝ≥0∞} (h : hausdorffEDist (range p) (range q) ≤ ε) (n : ℕ) :
    bottleneck (dgm k (Cech.filter p) n) (dgm k (Cech.filter q) n) ≤ ε :=
  (bottleneck_dgm_le_hausdorffEDist k p q n).trans h

/-- Two finite samples of one possibly infinite target have diagram discrepancy at
most the sum of their extended Hausdorff errors. No target diagram is constructed. -/
theorem bottleneck_dgm_le_sampling_errors [Nonempty V] [Nonempty W]
    (target : Set Z) {α β : ℝ≥0∞}
    (hp : hausdorffEDist (range p) target ≤ α)
    (hq : hausdorffEDist (range q) target ≤ β) (n : ℕ) :
    bottleneck (dgm k (Cech.filter p) n) (dgm k (Cech.filter q) n) ≤ α + β := by
  apply (bottleneck_dgm_le_hausdorffEDist k p q n).trans
  exact hausdorffEDist_triangle.trans (add_le_add hp (hausdorffEDist_comm.trans_le hq))

/-- Different multiplicities of coincident labels do not change the full diagram.
This also covers two empty configurations. -/
theorem dgm_eq_of_range_eq (h : range p = range q) (n : ℕ) :
    dgm k (Cech.filter p) n = dgm k (Cech.filter q) n := by
  let C : SetRel V W := {vw | p vw.1 = q vw.2}
  have hCT : Relator.LeftTotal (fun v w => (v, w) ∈ C) := by
    intro v
    have hv : p v ∈ range q := h ▸ mem_range_self v
    obtain ⟨w, hw⟩ := hv
    exact ⟨w, hw.symm⟩
  have hIT : Relator.LeftTotal (fun w v => (w, v) ∈ C.inv) := by
    intro w
    have hw : q w ∈ range p := h.symm ▸ mem_range_self w
    obtain ⟨v, hv⟩ := hw
    exact ⟨v, hv⟩
  apply (bottleneck_eq_zero_iff _ _).mp
  apply le_antisymm _ zero_le
  have hb := bottleneck_dgm_le_of_relation (C := C) (ε := 0) p q hCT hIT
    (by intro v w hvw; change p v = q w at hvw; simp [hvw]) k n
  simpa only [ENNReal.coe_zero] using hb

end Ordered

end
end TDA.Persistence.Cech
