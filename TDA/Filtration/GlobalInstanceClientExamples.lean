import TDA.Filtration.CriticalValuesExamples
import TDA.Filtration.SparseRips.H1Examples

/-!
# Client view of the instances of the filtration fixtures

Regression fixtures for #1288, family 13 of the downstream-use audit (#1207). A client that
imports the fixture modules of the filtration area sees the instances of mathlib and of the
library only; the metric on `Fin 4` and the decidable membership in the top complex on `Fin 2`
that those fixtures use for their own examples are local to their files.

* `Fin 4` carries no `MetricSpace`, `PseudoMetricSpace` or `Dist` instance.
* Membership of a face of `Fin 2` in the top complex has no `Decidable` instance.
-/

namespace TDA.Filtration.GlobalInstanceClientExamples

example : True := by
  fail_if_success have : MetricSpace (Fin 4) := inferInstance
  trivial

example : True := by
  fail_if_success have : PseudoMetricSpace (Fin 4) := inferInstance
  trivial

example : True := by
  fail_if_success have : Dist (Fin 4) := inferInstance
  trivial

example (_s : Finset (Fin 2)) : True := by
  fail_if_success have : Decidable (_s ∈ (⊤ : PreAbstractSimplicialComplex (Fin 2))) :=
    inferInstance
  trivial

end TDA.Filtration.GlobalInstanceClientExamples
