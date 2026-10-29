import TDA.Topology.MeasureBifiltration

/-!
# Finite uniform measures under outlier insertion

Adding labels changes the ambient Lévy–Prokhorov distance by at most their
fraction of the enlarged sample, independently of their positions. The estimate
also yields an actual restricted-index interleaving of multicover spaces.
-/

set_option autoImplicit false
open scoped NNReal ENNReal
universe u v w
namespace TDA.Topology.MeasureBifiltration
open MeasureTheory Metric CategoryTheory

variable {X : Type u} {V : Type v} {W : Type w}

/-- A label count is at most the finite carrier size. -/
theorem labelCount_le_card [Fintype V] (p : V → X) (A : Set X) :
    labelCount p A ≤ Fintype.card V := by
  classical
  simpa [labelCount] using Finset.card_filter_le (Finset.univ : Finset V) (fun v => p v ∈ A)

/-- Passing from a labelled subcollection to the full collection increases
unnormalized counts, without a condition on the locations of extra labels. -/
theorem labelCount_comp_embedding_le [Fintype V] [Fintype W]
    (i : V ↪ W) (p : W → X) (A : Set X) :
    labelCount (p ∘ i) A ≤ labelCount p A := by
  classical
  have hsub : ((Finset.univ.filter (fun v => p (i v) ∈ A)).map i) ⊆
      Finset.univ.filter (fun w => p w ∈ A) := by
    intro w hw
    obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hw
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hv).2⟩
  simpa [labelCount, Function.comp_def] using Finset.card_le_card hsub

variable [MetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
variable [Fintype V] [Nonempty V] [Fintype W] [Nonempty W]

omit [MetricSpace X] [OpensMeasurableSpace X] in
/-- The normalized mass of a subcollection exceeds that of the enlarged
collection by at most the missing fraction of labels. -/
theorem uniformMeasure_real_comp_embedding_le (i : V ↪ W) (p : W → X)
    {A : Set X} (hA : MeasurableSet A) :
    (uniformMeasure (p ∘ i)).real A ≤ (uniformMeasure p).real A +
      ((Fintype.card W : ℝ) - Fintype.card V) / Fintype.card W := by
  have hn : 0 < (Fintype.card V : ℝ) := by exact_mod_cast Fintype.card_pos
  have hN : 0 < (Fintype.card W : ℝ) := by exact_mod_cast Fintype.card_pos
  have hnN : (Fintype.card V : ℝ) ≤ Fintype.card W := by
    exact_mod_cast Fintype.card_le_of_injective i i.injective
  have hab : (labelCount (p ∘ i) A : ℝ) ≤ labelCount p A := by
    exact_mod_cast labelCount_comp_embedding_le i p A
  have han : (labelCount (p ∘ i) A : ℝ) ≤ Fintype.card V := by
    exact_mod_cast labelCount_le_card (p ∘ i) A
  rw [uniformMeasure_real _ hA, uniformMeasure_real _ hA, ← add_div]
  apply (div_le_div_iff₀ hn hN).2
  have hmul := mul_le_mul_of_nonneg_right hab hn.le
  have hprod := mul_nonneg (sub_nonneg.mpr hnN) (sub_nonneg.mpr han)
  nlinarith

/-- Enlarging a finite uniform sample costs at most the outlier mass in
ambient Prokhorov distance, regardless of how far the added labels lie. -/
theorem levyProkhorovDist_uniform_embedding_le (i : V ↪ W) (p : W → X) :
    levyProkhorovDist (uniformMeasure (p ∘ i)) (uniformMeasure p) ≤
      ((Fintype.card W : ℝ) - Fintype.card V) / Fintype.card W := by
  have hnN : (Fintype.card V : ℝ) ≤ Fintype.card W := by
    exact_mod_cast Fintype.card_le_of_injective i i.injective
  have hδ : 0 ≤ ((Fintype.card W : ℝ) - Fintype.card V) / Fintype.card W :=
    div_nonneg (sub_nonneg.mpr hnN) (by positivity)
  apply levyProkhorovDist_le_of_forall_le _ _ hδ
  intro ε A hε hA
  have hεpos : 0 < ε := hδ.trans_lt hε
  have hm := uniformMeasure_real_comp_embedding_le i p hA
  calc
    uniformMeasure (p ∘ i) A = ENNReal.ofReal ((uniformMeasure (p ∘ i)).real A) :=
      (ofReal_measureReal).symm
    _ ≤ ENNReal.ofReal ((uniformMeasure p).real A + ε) :=
      ENNReal.ofReal_le_ofReal (by linarith)
    _ = uniformMeasure p A + ENNReal.ofReal ε := by
      rw [ENNReal.ofReal_add (measureReal_nonneg) hεpos.le, ofReal_measureReal]
    _ ≤ uniformMeasure p (thickening ε A) + ENNReal.ofReal ε :=
      add_le_add (measure_mono (self_subset_thickening hεpos A)) le_rfl

/-- The extended-distance version of the same ambient outlier estimate. -/
theorem levyProkhorovEDist_uniform_embedding_le (i : V ↪ W) (p : W → X) :
    levyProkhorovEDist (uniformMeasure (p ∘ i)) (uniformMeasure p) ≤
      ENNReal.ofReal (((Fintype.card W : ℝ) - Fintype.card V) / Fintype.card W) := by
  have h := ENNReal.ofReal_le_ofReal (levyProkhorovDist_uniform_embedding_le i p)
  simpa only [levyProkhorovDist, ENNReal.ofReal_toReal (levyProkhorovEDist_ne_top _ _)] using h

/-- The outlier fraction directly gives an interleaving of the two actual
multicover diagrams for every larger parameter. -/
noncomputable def uniformOutlierInterleaving (i : V ↪ W) (p : W → X) (δ : ℝ≥0)
    (hδ : ((Fintype.card W : ℝ) - Fintype.card V) / Fintype.card W < δ) :
    InterleavingIndex δ ⥤ TopCat.{u} :=
  topologicalInterleaving (uniformMeasure (p ∘ i)) (uniformMeasure p) δ (by
    have hnN : (Fintype.card V : ℝ) ≤ Fintype.card W := by
      exact_mod_cast Fintype.card_le_of_injective i i.injective
    have hn : 0 ≤ ((Fintype.card W : ℝ) - Fintype.card V) / Fintype.card W :=
      div_nonneg (sub_nonneg.mpr hnN) (by positivity)
    exact (levyProkhorovEDist_uniform_embedding_le i p).trans_lt
      ((ENNReal.ofReal_lt_coe_iff hn).2 hδ))

/-- The outlier interleaving restricts exactly to the original uniform sample. -/
theorem uniformOutlierInterleaving_left (i : V ↪ W) (p : W → X) (δ : ℝ≥0)
    (hδ : ((Fintype.card W : ℝ) - Fintype.card V) / Fintype.card W < δ) :
    (copy δ false).toFunctor ⋙ uniformOutlierInterleaving i p δ hδ =
      topologicalDiagram (uniformMeasure (p ∘ i)) := rfl

/-- The other restriction is the sample with all additional labels. -/
theorem uniformOutlierInterleaving_right (i : V ↪ W) (p : W → X) (δ : ℝ≥0)
    (hδ : ((Fintype.card W : ℝ) - Fintype.card V) / Fintype.card W < δ) :
    (copy δ true).toFunctor ⋙ uniformOutlierInterleaving i p δ hδ =
      topologicalDiagram (uniformMeasure p) := rfl

end TDA.Topology.MeasureBifiltration
