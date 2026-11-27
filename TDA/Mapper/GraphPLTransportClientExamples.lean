import TDA.Mapper.GraphPLTransport

/-!
# Client statements of the graph-PL transport companions

Regression fixtures for #1301, family 15 of the downstream-use audit (#1207). The vertex type is
`ULift.{1} (Fin 4)`, a finite type in universe `1`, with `Equiv.ulift` to `Fin 4`. Each statement
is a plain application of a companion of `TDA/Mapper/GraphPLTransport.lean`.

* A vertex budget bounds the distance of the graph-PL Reeb graphs.
* The distance is at most the uniform extended distance of the vertex heights.
* Finite-cover Mapper reconstructions exist at any positive geometric error.
-/

namespace TDA.Mapper.GraphPLTransportClientExamples

open TDA.Reeb TDA.Reeb.GraphPL TDA.Reeb.OpenInterval TDA.Mapper.GraphPL
open scoped NNReal ENNReal

/-- A vertex budget on `ULift.{1} (Fin 4)` bounds the geometric interleaving distance of the
graph-PL Reeb graphs of the transported graph. -/
theorem ulift_fin_four_le (G : SimpleGraph (ULift.{1} (Fin 4))) (h g : ULift.{1} (Fin 4) → ℝ)
    {ε : ℝ≥0} (hhg : ∀ v, |h v - g v| ≤ ε) :
    RGraph.geometricInterleavingDistance
      (graphPLReebGraph (G.comap Equiv.ulift.symm) (h ∘ Equiv.ulift.symm))
      (graphPLReebGraph (G.comap Equiv.ulift.symm) (g ∘ Equiv.ulift.symm)) ≤ ε :=
  graphPLReebGraph_le_of_equiv Equiv.ulift G hhg

/-- The distance is at most the uniform extended distance of the vertex heights on
`ULift.{1} (Fin 4)`. -/
theorem ulift_fin_four_le_edist (G : SimpleGraph (ULift.{1} (Fin 4)))
    (h g : ULift.{1} (Fin 4) → ℝ) :
    RGraph.geometricInterleavingDistance
      (graphPLReebGraph (G.comap Equiv.ulift.symm) (h ∘ Equiv.ulift.symm))
      (graphPLReebGraph (G.comap Equiv.ulift.symm) (g ∘ Equiv.ulift.symm)) ≤
      edist (UniformFun.ofFun h) (UniformFun.ofFun g) :=
  graphPLReebGraph_le_edist_of_equiv Equiv.ulift G h g

/-- Mapper reconstructions at any positive error for a graph on `ULift.{1} (Fin 4)`. -/
theorem ulift_fin_four_mapperReconstruction (G : SimpleGraph (ULift.{1} (Fin 4)))
    (h : ULift.{1} (Fin 4) → ℝ) {r : ℝ} (hr : 0 < r) :
    ∃ n : ℕ, ∃ a b : Fin n → ℝ,
      (∀ x, ∃ i, plHeight (G.comap Equiv.ulift.symm) (h ∘ Equiv.ulift.symm) x ∈
        ioo (a i) (b i)) ∧
      RGraph.geometricInterleavingDistance
        (graphPLMapperReconstruction (G.comap Equiv.ulift.symm) (h ∘ Equiv.ulift.symm) a b)
        (graphPLReebGraph (G.comap Equiv.ulift.symm) (h ∘ Equiv.ulift.symm)) ≤
        (Real.toNNReal r : ℝ≥0∞) :=
  exists_graphPLMapperReconstruction_error_le_of_equiv Equiv.ulift G h hr

end TDA.Mapper.GraphPLTransportClientExamples
