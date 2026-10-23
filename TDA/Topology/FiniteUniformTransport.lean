import TDA.Topology.FiniteUniformProkhorov
/-!
# Transport of finite uniform ambient Prokhorov costs

Shrinking cross distances between two finite labelled samples contracts their
ambient Prokhorov cost. In particular, an isometric replacement of their joint
support preserves the cost exactly, including multiplicities.
-/

set_option autoImplicit false
open scoped ENNReal
universe u v w z
namespace TDA.Topology.MeasureBifiltration
open MeasureTheory Metric
variable {X : Type u} {Y : Type v} {V : Type w} {W : Type z}
variable [MeasurableSpace X] [MeasurableSpace Y]
variable [Fintype V] [Nonempty V]

/-- Labelwise set membership transports finite uniform masses. -/
theorem uniformMeasure_apply_le_of_label_mem (p : V → X) (q : V → Y)
    {A : Set X} {B : Set Y} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (h : ∀ v, p v ∈ A → q v ∈ B) : uniformMeasure p A ≤ uniformMeasure q B := by
  classical
  have hc : labelCount p A ≤ labelCount q B := by
    unfold labelCount
    apply Finset.card_le_card
    intro v hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h v (Finset.mem_filter.mp hv).2⟩
  rw [uniformMeasure_apply p hA, uniformMeasure_apply q hB]
  gcongr

variable [MetricSpace X] [OpensMeasurableSpace X] [MetricSpace Y] [OpensMeasurableSpace Y]
variable [Fintype W] [Nonempty W]

/-- Cross distances alone control transport of ambient Prokhorov cost between
two finite labelled uniform laws. -/
theorem levyProkhorovDist_uniform_le_of_cross_dist_le
    (p : V → X) (q : W → X) (p' : V → Y) (q' : W → Y)
    (hcross : ∀ v w, dist (p v) (q w) ≤ dist (p' v) (q' w)) :
    levyProkhorovDist (uniformMeasure p) (uniformMeasure q) ≤
      levyProkhorovDist (uniformMeasure p') (uniformMeasure q') := by
  classical
  apply levyProkhorovDist_le_of_forall_le _ _ ENNReal.toReal_nonneg
  intro ε A hε hA
  have hεpos : 0 < ε := ENNReal.toReal_nonneg.trans_lt hε
  let B := p' '' (p ⁻¹' A)
  have hB : MeasurableSet B := ((Set.toFinite (p ⁻¹' A)).image p').measurableSet
  have hleft : uniformMeasure p A ≤ uniformMeasure p' B :=
    uniformMeasure_apply_le_of_label_mem p p' hA hB (fun v hv => ⟨v, hv, rfl⟩)
  have hright : uniformMeasure q' (thickening ε B) ≤ uniformMeasure q (thickening ε A) := by
    apply uniformMeasure_apply_le_of_label_mem q' q isOpen_thickening.measurableSet
      isOpen_thickening.measurableSet
    intro w hw
    obtain ⟨z, hz, hd⟩ := mem_thickening_iff.mp hw
    obtain ⟨v, hv, rfl⟩ := hz
    apply mem_thickening_iff.mpr
    refine ⟨p v, hv, ?_⟩
    have hc : dist (q w) (p v) ≤ dist (q' w) (p' v) := by
      simpa only [dist_comm] using hcross v w
    exact hc.trans_lt hd
  have hLP : levyProkhorovEDist (uniformMeasure p') (uniformMeasure q') < ENNReal.ofReal ε :=
    (ENNReal.lt_ofReal_iff_toReal_lt (levyProkhorovEDist_ne_top _ _)).2 hε
  have hm := left_measure_le_of_levyProkhorovEDist_lt hLP hB
  rw [ENNReal.toReal_ofReal hεpos.le] at hm
  exact hleft.trans (hm.trans (add_le_add hright le_rfl))

/-- Extended-distance form of cross-distance contraction. -/
theorem levyProkhorovEDist_uniform_le_of_cross_dist_le
    (p : V → X) (q : W → X) (p' : V → Y) (q' : W → Y)
    (hcross : ∀ v w, dist (p v) (q w) ≤ dist (p' v) (q' w)) :
    levyProkhorovEDist (uniformMeasure p) (uniformMeasure q) ≤
      levyProkhorovEDist (uniformMeasure p') (uniformMeasure q') := by
  have h := ENNReal.ofReal_le_ofReal
    (levyProkhorovDist_uniform_le_of_cross_dist_le p q p' q' hcross)
  simpa only [levyProkhorovDist,
    ENNReal.ofReal_toReal (levyProkhorovEDist_ne_top (uniformMeasure p) (uniformMeasure q)),
    ENNReal.ofReal_toReal (levyProkhorovEDist_ne_top (uniformMeasure p') (uniformMeasure q'))] using h

/-- Isometric finite-support replacement preserves the exact ambient
Prokhorov cost, including when the labels have multiplicities. -/
theorem levyProkhorovEDist_uniform_eq_of_cross_dist_eq
    (p : V → X) (q : W → X) (p' : V → Y) (q' : W → Y)
    (hcross : ∀ v w, dist (p v) (q w) = dist (p' v) (q' w)) :
    levyProkhorovEDist (uniformMeasure p) (uniformMeasure q) =
      levyProkhorovEDist (uniformMeasure p') (uniformMeasure q') := by
  exact le_antisymm
    (levyProkhorovEDist_uniform_le_of_cross_dist_le p q p' q' (fun v w => (hcross v w).le))
    (levyProkhorovEDist_uniform_le_of_cross_dist_le p' q' p q (fun v w => (hcross v w).ge))
/-- For finite uniform laws, testing closed sets is sufficient to bound
mathlib's measurable-set Prokhorov distance. -/
theorem levyProkhorovDist_uniform_le_of_isClosed (p : V → X) (q : W → X)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (h : ∀ ε A, δ < ε → IsClosed A →
      uniformMeasure p A ≤ uniformMeasure q (thickening ε A) + ENNReal.ofReal ε) :
    levyProkhorovDist (uniformMeasure p) (uniformMeasure q) ≤ δ := by
  classical
  apply levyProkhorovDist_le_of_forall_le _ _ hδ
  intro ε A hε hA
  let B := p '' (p ⁻¹' A)
  have hB : IsClosed B := ((Set.toFinite (p ⁻¹' A)).image p).isClosed
  have hBA : B ⊆ A := by
    rintro _ ⟨v, hv, rfl⟩
    exact hv
  have hm : uniformMeasure p A ≤ uniformMeasure p B :=
    uniformMeasure_apply_le_of_label_mem p p hA hB.measurableSet
      (fun v hv => ⟨v, hv, rfl⟩)
  exact hm.trans ((h ε B hε hB).trans
    (add_le_add (measure_mono (thickening_subset_of_subset ε hBA)) le_rfl))

end TDA.Topology.MeasureBifiltration
