import TDA.Filtration.SparseRips.FaceEntryFilter
import TDA.Filtration.SparseRips.Approximation
import TDA.Persistence.ConstructibleIsometry

/-!
# Sparse Rips positive-degree log-diagram approximation

The attained finite filter presents the sparse complex exactly. In positive
degrees its log diagram is therefore the diagram of the sparse homology module,
and the proved multiplicative interleaving induces a cost-bounded matching to
the ordinary diameter-scale Rips diagram. Degree zero remains at the module
level because its zero-born classes have no finite log grid.
-/

namespace TDA.Filtration.SparseRips

open TDA.Simplicial TDA.Filtration TDA.Persistence CategoryTheory
open scoped NNReal ENNReal

noncomputable section

universe u

variable {V : Type u} [MetricSpace V] [Fintype V] [LinearOrder V]

/-- The constructed filter's log module is literally the sparse inclusion
filtration's homology after exponential reindexing. -/
theorem sparseFilter_logModule_eq (k : Type u) [Field k] (seed : V)
    {η : ℝ} (hη : 0 < η) (hη' : η ≤ 1 / 3) (n : ℕ) :
    logModule k (sparseFilter seed η) n =
      simplicialHomologyPModule k
        (Filtration.reindex expHom (sparseFiltration seed η)) n := by
  change simplicialHomologyPModule k
      (Filtration.reindex expHom (sparseFilter seed η).sublevelFiltration) n = _
  rw [sparseFilter_sublevelFiltration_eq seed hη hη']

/-- For every positive degree, the *actual finite sparse filter's* diagram
is within `log c` of diameter-scale Rips, where `c = (1-2η)⁻¹`. -/
theorem sparseLogDiagram_bottleneck_le (k : Type u) [Field k] (seed : V)
    {η : ℝ} (hη : 0 < η) (hη' : η ≤ 1 / 3)
    {n : ℕ} (hn : 1 ≤ n) :
    bottleneck (logDgm k (sparseFilter seed η) n)
      (logDgm k (Rips.filter (V := V) inferInstance) n) ≤
        ENNReal.ofReal (Real.log (approximationFactor η)) := by
  let f := sparseFilter seed η
  let g := Rips.filter (V := V) inferInstance
  have hi : RealInterleaving (logParam (approximationFactor η))
      (logModule k f n) (logModule k g n) := by
    rw [sparseFilter_logModule_eq k seed hη hη' n]
    exact sparseRipsLogInterleaving k seed hη hη' n
  have hs := logModule_isConstructible k n hn
    (sparseFilter_positiveOnEdges seed hη hη')
  have hg := logModule_isConstructible k n hn
    (positiveOnEdges_rips (V := V) inferInstance)
  have hbound := FiniteConstructible.bottleneck_le_of_interleaving
    hs hg
    (fun i => logModule_finiteDimensional k n f (logGrid f i))
    (fun i => logModule_finiteDimensional k n g (logGrid g i)) hi
  change bottleneck (logDgm k f n) (logDgm k g n) ≤ _
  have hc := one_le_approximationFactor hη hη'
  rw [← coe_logParam hc, ENNReal.ofReal_coe_nnreal]
  simpa only [logDgm, f, g] using hbound

end

end TDA.Filtration.SparseRips
