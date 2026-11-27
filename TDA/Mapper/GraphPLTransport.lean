import TDA.Mapper.MapperReebApproximation
import TDA.Mapper.GraphPLReebStability

/-!
# Graph-PL Reeb statements for vertex types outside universe `0`

The graph-PL Reeb graph `graphPLReebGraph G h` and the Mapper reconstruction
`graphPLMapperReconstruction G h a b` are objects over `Over (TopCat.of ℝ)`, so their vertex type
`V` is a type in universe `0`. For a vertex type `V : Type u` and an equivalence `e : V ≃ W` with
`W : Type` finite, the same statements hold for the graph `G.comap e.symm` on `W` with heights
`h ∘ e.symm`.

* `graphPLReebGraph_le_of_equiv`: a vertex budget `|h v - g v| ≤ ε` bounds the geometric
  interleaving distance of the graph-PL Reeb graphs.
* `graphPLReebGraph_le_edist_of_equiv`: the distance is at most the uniform extended distance of
  the vertex heights `h`, `g` on `V`.
* `exists_graphPLMapperReconstruction_error_le_of_equiv`: finite bounded interval covers give
  categorical Mapper reconstructions at any positive geometric error.
-/

open Set
open scoped NNReal ENNReal

universe u

namespace TDA.Mapper

open TDA.Reeb TDA.Reeb.GraphPL TDA.Reeb.OpenInterval TDA.Reeb.RGraph TDA.Mapper.GraphPL

/-- A vertex budget `ε` bounds the geometric interleaving distance of the graph-PL Reeb graphs
of a graph on `V : Type u`, transported to a finite `W : Type` along `e : V ≃ W`. -/
theorem GraphPL.graphPLReebGraph_le_of_equiv {V : Type u} {W : Type} [Finite W] (e : V ≃ W)
    (G : SimpleGraph V) {h g : V → ℝ} {ε : ℝ≥0} (hhg : ∀ v, |h v - g v| ≤ ε) :
    geometricInterleavingDistance (graphPLReebGraph (G.comap e.symm) (h ∘ e.symm))
      (graphPLReebGraph (G.comap e.symm) (g ∘ e.symm)) ≤ ε :=
  geometricInterleavingDistance_graphPLReebGraph_le _ fun w => hhg (e.symm w)

/-- The geometric interleaving distance of the transported graph-PL Reeb graphs is at most the
uniform extended distance of the vertex heights on `V : Type u`. -/
theorem GraphPL.graphPLReebGraph_le_edist_of_equiv {V : Type u} {W : Type} [Finite W]
    (e : V ≃ W) (G : SimpleGraph V) (h g : V → ℝ) :
    geometricInterleavingDistance (graphPLReebGraph (G.comap e.symm) (h ∘ e.symm))
      (graphPLReebGraph (G.comap e.symm) (g ∘ e.symm)) ≤
      edist (UniformFun.ofFun h) (UniformFun.ofFun g) := by
  refine (geometricInterleavingDistance_graphPLReebGraph_le_edist_ofFun _ _ _).trans ?_
  rw [UniformFun.edist_def, UniformFun.edist_def]
  refine iSup_le fun w => ?_
  simpa using le_iSup (fun v => edist (h v) (g v)) (e.symm w)

/-- Every finite graph-PL input on a vertex type `V : Type u`, transported along `e : V ≃ W` to a
finite `W : Type`, admits categorical Mapper reconstruction at any positive geometric error. -/
theorem exists_graphPLMapperReconstruction_error_le_of_equiv {V : Type u} {W : Type} [Finite W]
    (e : V ≃ W) (G : SimpleGraph V) (h : V → ℝ) {r : ℝ} (hr : 0 < r) :
    ∃ n : ℕ, ∃ a b : Fin n → ℝ,
      (∀ x, ∃ i, plHeight (G.comap e.symm) (h ∘ e.symm) x ∈ ioo (a i) (b i)) ∧
      RGraph.geometricInterleavingDistance
        (graphPLMapperReconstruction (G.comap e.symm) (h ∘ e.symm) a b)
        (GraphPL.graphPLReebGraph (G.comap e.symm) (h ∘ e.symm)) ≤
        (Real.toNNReal r : ℝ≥0∞) :=
  exists_graphPLMapperReconstruction_error_le _ _ hr

end TDA.Mapper
