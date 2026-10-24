import TDA.Persistence.RipsQTame
import TDA.Persistence.PersistenceMeasureExtendedDiagram
import TDA.Persistence.PersistenceMeasureDiagramCountability

/-!
# Decorated persistence diagram of a totally bounded Rips space

The q-tame closed-diameter Rips module has a canonical locally finite decorated
multiplicity, extracted from its actual persistence measure. Rectangle and tail
counts below refer to the Rips homology module itself, in every degree. No
finite-dimensional fiber or finite-vertex assumption is used.
-/

universe u v

namespace TDA.Persistence.Rips

open Set TDA.Filtration TDA.Persistence.RectangleMeasure

variable {X : Type u} [LinearOrder X] [MetricSpace X]

/-- Decorated finite and essential occurrences of the closed-diameter Rips
homology of a totally bounded space. The value is independent of any choice
of finite net used to prove q-tameness. -/
noncomputable def qTameDiagramMultiplicity (k : Type v) [Field k]
    (hX : TotallyBounded (univ : Set X)) (n : ℕ) (p : Cut ℝ × Cut ℝ) : ℕ :=
  moduleExtendedDiagramMultiplicity
    (sublevelModule k (Rips.filter (inferInstance : MetricSpace X)) n)
    (qTame_of_totallyBounded k hX n) p

/-- The Rips diagram counts the actual finite-death image-and-kernel quotient
on every separated rectangle, with its endpoint decorations retained. -/
theorem qTameDiagramMultiplicity_rectangle_counts (k : Type v) [Field k]
    (hX : TotallyBounded (univ : Set X)) (n : ℕ)
    (a b c d : ℝ) (hab : a < b) (hbc : b < c) (hcd : c < d) :
    ∃ S : Finset (Cut ℝ × Cut ℝ),
      (∀ p, p ∈ S ↔ p ∈ rectangleCell a b c d ∧
        0 < qTameDiagramMultiplicity k hX n p) ∧
      persistenceMeasureValue
        (sublevelModule k (Rips.filter (inferInstance : MetricSpace X)) n)
        hab.le hbc.le hcd.le =
        ∑ p ∈ S, qTameDiagramMultiplicity k hX n p := by
  exact moduleExtendedDiagramMultiplicity_rectangle_counts
    (sublevelModule k (Rips.filter (inferInstance : MetricSpace X)) n)
    (qTame_of_totallyBounded k hX n) a b c d hab hbc hcd

/-- Death-at-infinity occurrences count the actual Rips essential birth strip. -/
theorem qTameDiagramMultiplicity_essential_counts (k : Type v) [Field k]
    (hX : TotallyBounded (univ : Set X)) (n : ℕ)
    {a b : ℝ} (hab : a ≤ b) :
    ∃ S : Finset (Cut ℝ),
      (∀ birth, birth ∈ S ↔ birth ∈ cutCell a b ∧
        0 < qTameDiagramMultiplicity k hX n (birth, infinityCut)) ∧
      essentialMeasureValue
        (sublevelModule k (Rips.filter (inferInstance : MetricSpace X)) n) hab =
        ∑ birth ∈ S, qTameDiagramMultiplicity k hX n (birth, infinityCut) := by
  exact moduleExtendedDiagramMultiplicity_essential_counts
    (sublevelModule k (Rips.filter (inferInstance : MetricSpace X)) n)
    (qTame_of_totallyBounded k hX n) hab

/-- Tail rectangles include all Rips occurrences surviving a finite death
threshold, including the death-at-infinity boundary. Their count is the
original finite-target image quotient dimension. -/
theorem qTameDiagramMultiplicity_tail_counts (k : Type v) [Field k]
    (hX : TotallyBounded (univ : Set X)) (n : ℕ)
    (a b c : ℝ) (hab : a < b) (hbc : b < c) :
    ∃ S : Finset (Cut ℝ × Cut ℝ),
      (∀ p, p ∈ S ↔ p ∈ tailRectangleCell a b c ∧
        0 < qTameDiagramMultiplicity k hX n p) ∧
      persistenceTailMeasureValue
        (sublevelModule k (Rips.filter (inferInstance : MetricSpace X)) n)
        hab.le hbc.le =
        ∑ p ∈ S, qTameDiagramMultiplicity k hX n p := by
  exact moduleExtendedDiagramMultiplicity_tail_counts
    (sublevelModule k (Rips.filter (inferInstance : MetricSpace X)) n)
    (qTame_of_totallyBounded k hX n) a b c hab hbc

/-- Every separated Rips tail rectangle, including neighborhoods of infinity,
has only finitely many positive decorated occurrences. -/
theorem qTameDiagramMultiplicity_tail_locally_finite (k : Type v) [Field k]
    (hX : TotallyBounded (univ : Set X)) (n : ℕ)
    (a b c : ℝ) (hab : a < b) (hbc : b < c) :
    Set.Finite {p | p ∈ tailRectangleCell a b c ∧
      0 < qTameDiagramMultiplicity k hX n p} := by
  exact moduleExtendedDiagramMultiplicity_tail_locally_finite
    (sublevelModule k (Rips.filter (inferInstance : MetricSpace X)) n)
    (qTame_of_totallyBounded k hX n) a b c hab hbc

/-- The decorated Rips diagram has countable global positive support, although
its degree-zero fiber at time zero may be infinite-dimensional. -/
theorem qTameDiagramMultiplicity_countable_support (k : Type v) [Field k]
    (hX : TotallyBounded (univ : Set X)) (n : ℕ) :
    Set.Countable {p | 0 < qTameDiagramMultiplicity k hX n p} := by
  exact moduleExtendedDiagramMultiplicity_countable_support
    (sublevelModule k (Rips.filter (inferInstance : MetricSpace X)) n)
    (qTame_of_totallyBounded k hX n)

end TDA.Persistence.Rips
