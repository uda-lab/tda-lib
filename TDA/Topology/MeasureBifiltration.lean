import TDA.Filtration.SubdivisionRips
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.Topology.Category.TopCat.Basic

/-!
# Measure bifiltrations on the restricted positive index

The measure stage consists of centers whose open ball has mass at least `k`.
The two-copy index below is Definition 2.32 of Blumberg–Lesnick: a cross arrow
exists only when its target has positive coordinates and lies after the
ambient translation `(k,r) ↦ (k-δ,r+δ)`. It never adds a stage at nonpositive
mass. Prokhorov's measurable-set inequalities give all its cross inclusions.
-/

open scoped NNReal ENNReal

universe u
namespace TDA.Topology.MeasureBifiltration

open MeasureTheory Metric CategoryTheory
open TDA.Filtration.SubdivisionRips

/-- The two copies of the positive index used by a restricted interleaving. -/
structure InterleavingIndex (_δ : ℝ≥0) where
  /-- The positive density-radius parameter. -/
  point : Index
  /-- Which of the two diagrams contains the object. -/
  side : Bool

/-- The cross-copy penalty is `δ`; within one copy it is zero. -/
def penalty (δ : ℝ≥0) (a b : Bool) : ℝ := if a = b then 0 else δ

/-- Arrows are precisely the ambient shifted inequalities, with both endpoints
in the positive index. -/
instance interleavingIndexPreorder (δ : ℝ≥0) : Preorder (InterleavingIndex δ) where
  le p q := mass q.point + penalty δ p.side q.side ≤ mass p.point ∧
    radius p.point + penalty δ p.side q.side ≤ radius q.point
  le_refl p := by simp [penalty]
  le_trans p q r hpq hqr := by
    have hδ := δ.coe_nonneg
    rcases p with ⟨p, a⟩
    rcases q with ⟨q, b⟩
    rcases r with ⟨r, c⟩
    cases a <;> cases b <;> cases c <;>
      simp only [penalty, Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte] at * <;>
      constructor <;> linarith [hpq.1, hpq.2, hqr.1, hqr.2]

/-- Characteristic arrow inequalities for the two-copy preorder. -/
@[simp] theorem interleavingIndex_le_iff (δ : ℝ≥0) (p q : InterleavingIndex δ) :
    p ≤ q ↔ mass q.point + penalty δ p.side q.side ≤ mass p.point ∧
      radius p.point + penalty δ p.side q.side ≤ radius q.point := Iff.rfl

/-- The original index embeds as either copy of the interleaving category. -/
def copy (δ : ℝ≥0) (b : Bool) : Index →o InterleavingIndex δ where
  toFun p := ⟨p, b⟩
  monotone' := by
    intro p q hpq
    simpa [interleavingIndex_le_iff, penalty] using hpq

/-- For distinct copies this is exactly the restricted translation criterion. -/
theorem cross_le_iff (δ : ℝ≥0) (p q : Index) :
    (⟨p, false⟩ : InterleavingIndex δ) ≤ ⟨q, true⟩ ↔
      mass q ≤ mass p - δ ∧ radius p + δ ≤ radius q := by
  change mass q + penalty δ false true ≤ mass p ∧ _ ↔ _
  simp only [penalty, Bool.false_eq_true, ↓reduceIte]
  constructor <;> rintro ⟨h, h'⟩ <;> exact ⟨by linarith, h'⟩

variable {X : Type u} [MetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]

/-- Centers of balls of radius `r` whose measure is at least `k`. -/
def stage (μ : Measure X) (p : Index) : Set X :=
  {x | mass p ≤ μ.real (ball x (radius p))}

omit [OpensMeasurableSpace X] in
/-- Ordinary structure arrows are inclusions of subsets of the same ambient space. -/
theorem stage_mono (μ : Measure X) [IsFiniteMeasure μ] {p q : Index} (hpq : p ≤ q) :
    stage μ p ⊆ stage μ q := by
  intro x hx
  exact hpq.1.trans (hx.trans (measureReal_mono (μ := μ) (ball_subset_ball (x := x) hpq.2)))

/-- The measurable-set Prokhorov inequality controls open balls with the
additive radius shift. No compactness or properness assumption is needed. -/
theorem ball_mass_le (μ ν : Measure X) [IsFiniteMeasure ν]
    (δ : ℝ≥0) (h : levyProkhorovEDist μ ν < (δ : ℝ≥0∞)) (x : X) (r : ℝ) :
    μ.real (ball x r) ≤ ν.real (ball x (r + δ)) + δ := by
  have hP := left_measure_le_of_levyProkhorovEDist_lt h (B := ball x r) measurableSet_ball
  simp only [ENNReal.coe_toReal] at hP
  have hsub : thickening (δ : ℝ) (ball x r) ⊆ ball x (r + δ) := by
    intro y hy
    obtain ⟨z, hz, hyz⟩ := mem_thickening_iff.mp hy
    rw [mem_ball] at hz ⊢
    calc dist y x ≤ dist y z + dist z x := dist_triangle _ _ _
      _ < (δ : ℝ) + r := add_lt_add hyz hz
      _ = r + δ := add_comm _ _
  have hle : μ (ball x r) ≤ ν (ball x (r + δ)) + (δ : ℝ≥0∞) := by
    exact hP.trans (add_le_add (measure_mono (μ := ν) hsub) le_rfl)
  have ht := ENNReal.toReal_mono (by finiteness) hle
  simpa only [ENNReal.toReal_add (measure_ne_top _ _) ENNReal.coe_ne_top,
    ENNReal.coe_toReal, Measure.real] using ht

/-- Every cross arrow gives a concrete inclusion. This statement also covers
arrows whose target lies strictly beyond the translated source. -/
theorem stage_cross (μ ν : Measure X) [IsFiniteMeasure ν]
    (δ : ℝ≥0) (h : levyProkhorovEDist μ ν < (δ : ℝ≥0∞))
    {p q : Index} (hpq : mass q ≤ mass p - δ ∧ radius p + δ ≤ radius q) :
    stage μ p ⊆ stage ν q := by
  intro x hx
  have hm := ball_mass_le μ ν δ h x (radius p)
  have hn : ν.real (ball x (radius p + δ)) ≤ ν.real (ball x (radius q)) :=
    measureReal_mono (μ := ν) (ball_subset_ball (x := x) hpq.2)
  change mass q ≤ ν.real (ball x (radius q))
  change mass p ≤ μ.real (ball x (radius p)) at hx
  linarith [hpq.1]

/-- A measure bifiltration as a diagram of actual center spaces and inclusions. -/
def diagram (μ : Measure X) [IsFiniteMeasure μ] : Index ⥤ Type u where
  obj p := stage μ p
  map f := TypeCat.ofHom fun x => ⟨x.val, stage_mono μ (leOfHom f) x.property⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The single diagram on Definition 2.32's two-copy category witnessing the
Prokhorov interleaving. Functoriality proves all mixed naturality and composite
conditions simultaneously, using actual inclusion functions. -/
def interleavingDiagram (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (δ : ℝ≥0) (h : levyProkhorovEDist μ ν < (δ : ℝ≥0∞)) :
    InterleavingIndex δ ⥤ Type u where
  obj p := stage (if p.side then ν else μ) p.point
  map {p q} f := TypeCat.ofHom fun x => by
    refine ⟨x.val, ?_⟩
    have hpq := leOfHom f
    rcases p with ⟨p, a⟩
    rcases q with ⟨q, b⟩
    cases a <;> cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] at *
    · exact stage_mono μ (by simpa [interleavingIndex_le_iff, penalty] using hpq) x.property
    · exact stage_cross μ ν δ h ((cross_le_iff δ p q).mp hpq) x.property
    · apply stage_cross ν μ δ (by simpa [levyProkhorovEDist_comm] using h) ?_ x.property
      change mass q + penalty δ true false ≤ mass p ∧ _ at hpq
      simpa [penalty, sub_eq_add_neg, le_sub_iff_add_le] using hpq
    · exact stage_mono ν (by simpa [interleavingIndex_le_iff, penalty] using hpq) x.property
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The first copy recovers the original measure diagram exactly. -/
theorem interleavingDiagram_left (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (δ : ℝ≥0) (h : levyProkhorovEDist μ ν < (δ : ℝ≥0∞)) :
    (copy δ false).toFunctor ⋙ interleavingDiagram μ ν δ h = diagram μ := rfl

/-- The second copy recovers the other measure diagram exactly. -/
theorem interleavingDiagram_right (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (δ : ℝ≥0) (h : levyProkhorovEDist μ ν < (δ : ℝ≥0∞)) :
    (copy δ true).toFunctor ⋙ interleavingDiagram μ ν δ h = diagram ν := rfl

/-- The same measure bifiltration as a diagram of topological subspaces. -/
def topologicalDiagram (μ : Measure X) [IsFiniteMeasure μ] : Index ⥤ TopCat.{u} where
  obj p := TopCat.of (stage μ p)
  map f := TopCat.ofHom ⟨((diagram μ).map f).hom,
    continuous_subtype_val.subtype_mk _⟩
  map_id _ := by ext; rfl
  map_comp _ _ := by ext; rfl

/-- The Prokhorov interleaving consists of continuous subspace inclusions,
so it is also an interleaving of spaces in the source's category `Top`. -/
def topologicalInterleaving (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (δ : ℝ≥0) (h : levyProkhorovEDist μ ν < (δ : ℝ≥0∞)) :
    InterleavingIndex δ ⥤ TopCat.{u} where
  obj p := TopCat.of (stage (if p.side then ν else μ) p.point)
  map f := TopCat.ofHom ⟨((interleavingDiagram μ ν δ h).map f).hom,
    continuous_subtype_val.subtype_mk _⟩
  map_id _ := by ext; rfl
  map_comp _ _ := by ext; rfl

/-- The topological interleaving restricts to its first measure diagram. -/
theorem topologicalInterleaving_left (μ ν : Measure X)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (δ : ℝ≥0)
    (h : levyProkhorovEDist μ ν < (δ : ℝ≥0∞)) :
    (copy δ false).toFunctor ⋙ topologicalInterleaving μ ν δ h = topologicalDiagram μ := rfl

/-- The topological interleaving restricts to its second measure diagram. -/
theorem topologicalInterleaving_right (μ ν : Measure X)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (δ : ℝ≥0)
    (h : levyProkhorovEDist μ ν < (δ : ℝ≥0∞)) :
    (copy δ true).toFunctor ⋙ topologicalInterleaving μ ν δ h = topologicalDiagram ν := rfl

section Uniform

variable {V : Type*} [Fintype V] [Nonempty V]

/-- Push the finite uniform law into the common ambient metric space. Repeated
labels retain their multiplicity in this probability measure. -/
noncomputable def uniformMeasure (p : V → X) : Measure X :=
  ((PMF.uniformOfFintype V).map p).toMeasure

instance uniformMeasure_probability (p : V → X) : IsProbabilityMeasure (uniformMeasure p) := by
  unfold uniformMeasure
  infer_instance

/-- The number of labels lying in an ambient set. -/
noncomputable def labelCount (p : V → X) (A : Set X) : ℕ := by
  classical
  exact (Finset.univ.filter (fun v => p v ∈ A)).card

omit [MetricSpace X] [OpensMeasurableSpace X] in
/-- The ambient measure is exactly normalized counting of labels. -/
theorem uniformMeasure_apply (p : V → X) {A : Set X} (hA : MeasurableSet A) :
    uniformMeasure p A =
      (labelCount p A : ℝ≥0∞) / Fintype.card V := by
  classical
  let : MeasurableSpace V := ⊤
  rw [uniformMeasure, PMF.toMeasure_map_apply p (PMF.uniformOfFintype V) A
    (measurable_of_finite p) hA]
  let : Fintype (p ⁻¹' A) := Fintype.ofFinite _
  rw [PMF.toMeasure_uniformOfFintype_apply (p ⁻¹' A)
    ((measurable_of_finite p) hA)]
  simp only [Fintype.card_subtype, Set.mem_preimage, labelCount]

omit [MetricSpace X] [OpensMeasurableSpace X] in
/-- In real-valued form, the mass is the same cardinality ratio as the
normalized subdivision threshold. -/
theorem uniformMeasure_real (p : V → X) {A : Set X} (hA : MeasurableSet A) :
    (uniformMeasure p).real A =
      (labelCount p A : ℝ) / Fintype.card V := by
  classical
  rw [Measure.real, uniformMeasure_apply p hA, ENNReal.toReal_div]
  simp

/-- Concrete finite uniform measures inherit the entire restricted-index
interleaving, with inclusion maps and all mixed functoriality laws. -/
noncomputable def uniformInterleavingDiagram {W : Type*} [Fintype W] [Nonempty W]
    (p : V → X) (q : W → X) (δ : ℝ≥0)
    (h : levyProkhorovEDist (uniformMeasure p) (uniformMeasure q) < (δ : ℝ≥0∞)) :
    InterleavingIndex δ ⥤ Type u :=
  interleavingDiagram (uniformMeasure p) (uniformMeasure q) δ h

end Uniform

end TDA.Topology.MeasureBifiltration
