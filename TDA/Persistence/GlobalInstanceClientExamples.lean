import TDA.Persistence.CechFinitePBottleneckAllDegreesExamples
import TDA.Persistence.FiniteInjectiveRankDimensionExamples
import TDA.Persistence.FiniteLatticeComplementCardinality
import TDA.Persistence.GeneratedUpsetResolutionExamples
import TDA.Persistence.RipsQTameInfiniteMetricStabilityExamples

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
* `Option (Fin 3)` carries no `LinearOrder`, `MetricSpace` or `PseudoMetricSpace` instance.
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

end TDA.Persistence.GlobalInstanceClientExamples
