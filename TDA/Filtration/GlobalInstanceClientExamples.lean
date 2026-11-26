import TDA.Filtration.SparseRips.H1Examples

/-!
# Client view of the metric fixture of the sparse Rips examples

Regression fixture for #1288, family 13 of the downstream-use audit (#1207). A client that
imports `TDA.Filtration.SparseRips.H1Examples` sees the instances of mathlib and of the library
only; the metric on `Fin 4` that the module uses for its own examples is local to its file.

* `Fin 4` carries no `MetricSpace`, `PseudoMetricSpace` or `Dist` instance.
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

end TDA.Filtration.GlobalInstanceClientExamples
