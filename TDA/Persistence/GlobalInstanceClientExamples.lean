import TDA.Persistence.CechFinitePBottleneckAllDegreesExamples
import TDA.Persistence.CoordinateGrid
import TDA.Persistence.FiniteInjectivePresentation
import TDA.Persistence.FiniteInjectiveRankDimensionExamples
import TDA.Filtration.CriticalValuesExamples
import TDA.Persistence.FiniteLatticeComplementCardinality
import TDA.Persistence.GeneratedUpsetResolutionExamples
import TDA.Persistence.RipsQTameInfiniteMetricStabilityExamples
import TDA.Persistence.RipsSampling
import TDA.Persistence.SublevelDiagramExamples
import TDA.Persistence.SublevelDiagramTransportExamples

/-!
# Client view of the instances of the persistence modules

Regression fixtures for #1288, family 13 of the downstream-use audit (#1207). A client that
imports the modules below sees the instances of mathlib on finite products, empty metric
spaces, categories of preorders and options; the instances that those modules declare for their
own statements and examples are local to their files.

* `Fintype (Fin 3 → Bool)` is mathlib's `Pi.instFintype` and computes.
* `Fintype`, `OrderBot` and `OrderTop` are not supplied for an arbitrary finite family of
  linear orders.
* `PseudoMetricSpace Empty` is the metric space structure of mathlib.
* `Category (Bool × Bool)` is the product category of mathlib.
* Membership of a face of `Fin 2` in the top complex has no `Decidable` instance.
* `Option (Fin 3)` carries no `LinearOrder`, `MetricSpace` or `PseudoMetricSpace` instance.

Family 14 (#1291):

* `Fintype (∀ i : Fin n, {x : ℝ // x ∈ G i})` is `Pi.instFintype`, and `Fintype.card` and
  `Finset.univ` of this type compute in client definitions.
* `Fintype (Set.range t)` under `[DecidableEq X]` is `Set.fintypeRange`; without decidable
  equality on `X` it has no instance.
* `Fintype (Σ p : P, Fin (Module.finrank k (M.obj p)))` under `[Fintype P]` is `Sigma.instFintype`.
-/

namespace TDA.Persistence.GlobalInstanceClientExamples

example : (inferInstance : Fintype (Fin 3 → Bool)) = Pi.instFintype := rfl

example : Fintype.card (Fin 3 → Bool) = 8 := by decide

/-- The universe of functions `Fin 3 → Bool` is a computable finite set. -/
def functionUniverse : Finset (Fin 3 → Bool) := Finset.univ

example : functionUniverse.card = 8 := by decide

example {ι : Type} [Fintype ι] {T : ι → Type} [∀ i, LinearOrder (T i)] [∀ i, Finite (T i)]
    (_i : ι) : True := by
  fail_if_success have : Fintype (T _i) := inferInstance
  trivial

example {ι : Type} [Fintype ι] {T : ι → Type} [∀ i, LinearOrder (T i)] [∀ i, Finite (T i)]
    [∀ i, Nonempty (T i)] (_i : ι) : True := by
  fail_if_success have : OrderBot (T _i) := inferInstance
  fail_if_success have : OrderTop (T _i) := inferInstance
  trivial

example : (inferInstance : PseudoMetricSpace Empty) =
    (inferInstance : MetricSpace Empty).toPseudoMetricSpace := rfl

example : (inferInstance : CategoryTheory.Category (Bool × Bool)) =
    CategoryTheory.uniformProd Bool Bool := rfl

example : True := by
  fail_if_success have : LinearOrder (Option (Fin 3)) := inferInstance
  trivial

example : True := by
  fail_if_success have : MetricSpace (Option (Fin 3)) := inferInstance
  trivial

example : True := by
  fail_if_success have : PseudoMetricSpace (Option (Fin 3)) := inferInstance
  trivial

example (_s : Finset (Fin 2)) : True := by
  fail_if_success have : Decidable (_s ∈ (⊤ : PreAbstractSimplicialComplex (Fin 2))) :=
    inferInstance
  trivial

/-- The number of points of a coordinate grid in the plane. -/
def gridCard (G : CoordinateGrid 2) : ℕ := Fintype.card (∀ i : Fin 2, {x : ℝ // x ∈ G i})

/-- The points of a coordinate grid in the plane. -/
def gridPoints (G : CoordinateGrid 2) : Finset (∀ i : Fin 2, {x : ℝ // x ∈ G i}) := Finset.univ

example {n : ℕ} (G : CoordinateGrid n) :
    (inferInstance : Fintype (∀ i : Fin n, {x : ℝ // x ∈ G i})) = Pi.instFintype := rfl

/-- The number of values of a triple. -/
def rangeCard {X : Type} [DecidableEq X] (t : Fin 3 → X) : ℕ := Fintype.card (Set.range t)

example : Fintype.card (Set.range (fun i : Fin 3 => i.val)) = 3 := by decide

example {X : Type} [DecidableEq X] {n : ℕ} (t : Fin n → X) :
    (inferInstance : Fintype (Set.range t)) = Set.fintypeRange t := rfl

example {X : Type} {n : ℕ} (_t : Fin n → X) : True := by
  fail_if_success have : Fintype (Set.range _t) := inferInstance
  trivial

example {X : Type} [MetricSpace X] [DecidableEq X] (k : Type) [Field k] {n : ℕ} (t : Fin n → X)
    (d : ℕ) :
    Rips.sampleDiagram k t d = Rips.diagram k (Set.range t) d :=
  Rips.sampleDiagram_eq_diagram k t d

example {k : Type} [Field k] {P : Type} [PartialOrder P] [Fintype P] (M : PModule k P) :
    (inferInstance : Fintype (Σ p : P, Fin (Module.finrank k (M.obj p)))) =
      Sigma.instFintype := rfl

example {k : Type} [Field k] {P : Type} [PartialOrder P] [Fintype P] (M : PModule k P) :
    Fintype.card (Σ p : P, Fin (Module.finrank k (M.obj p))) =
      ∑ p : P, Module.finrank k (M.obj p) := by
  simp [Fintype.card_sigma]

end TDA.Persistence.GlobalInstanceClientExamples
