import TDA.Mapper.GraphPLConstructible
import TDA.Reeb.ConstructiblePerturbation
import TDA.Reeb.GraphPLVertexPerturbation

/-!
# Stability of graph-PL Reeb quotients under vertex-height perturbation

Fix a finite simple graph `G` on `V : Type` and two vertex-height functions `h g : V → ℝ`. The
geometric interleaving distance of the graph-PL Reeb quotients `graphPLReebGraph G h` and
`graphPLReebGraph G g` equals the interleaving distance of the interval-component precosheaves of
the piecewise-linear heights (`geometricInterleavingDistance_graphPLReebGraph`). The vertex-height
bound for the latter (`TDA.Reeb.GraphPL.interleavingDistance_intervalComponents_plHeight_le`)
therefore transfers to the quotients:

* a vertex budget `|h v - g v| ≤ ε` gives distance at most `ε`
  (`geometricInterleavingDistance_graphPLReebGraph_le`);
* the distance is at most the uniform extended distance of the vertex heights on `V →ᵤ ℝ`
  (`geometricInterleavingDistance_graphPLReebGraph_le_edist_ofFun`, using
  `TDA.Reeb.interleavingDistance_intervalComponents_le_edist`);
* for `[Fintype V]` the distance is at most the product extended distance `edist h g`
  (`geometricInterleavingDistance_graphPLReebGraph_le_edist`).

The graph is fixed, and no other hypothesis is made on the heights: the order and number of
distinct vertex heights may change, and horizontal edges may appear or disappear. The bound is an
inequality: reversing the two endpoint heights of a single edge gives isomorphic quotients at
distance `0`, although `edist h g = 1`. The height range of `graphPLReebGraph G h` is the range of
`plHeight G h` (`heightRange_graphPLReebGraph`), which gives the lower bounds used by the
exactness fixtures. The general perturbation step is
de Silva–Munch–Patel, Theorem 4.6(i); the graph-PL consumer is a library result.
-/

namespace TDA.Mapper.GraphPL

open Set
open TDA.Reeb TDA.Reeb.GraphPL TDA.Reeb.RGraph
open scoped NNReal ENNReal

variable {V : Type} (G : SimpleGraph V)

/-- The height range of the graph-PL Reeb quotient is the range of the piecewise-linear height. -/
theorem heightRange_graphPLReebGraph [Finite V] (h : V → ℝ) :
    heightRange (graphPLReebGraph G h) = range (plHeight G h) := by
  rw [← quotientRGraphFunctor_obj_graphPLSpace, heightRange_quotientRGraphFunctor_obj]
  rfl

/-- The geometric interleaving distance of the graph-PL Reeb quotients is at most the uniform
extended distance of the vertex heights. -/
theorem geometricInterleavingDistance_graphPLReebGraph_le_edist_ofFun [Finite V] (h g : V → ℝ) :
    geometricInterleavingDistance (graphPLReebGraph G h) (graphPLReebGraph G g) ≤
      edist (UniformFun.ofFun h) (UniformFun.ofFun g) := by
  rw [geometricInterleavingDistance_graphPLReebGraph]
  exact interleavingDistance_intervalComponents_plHeight_le_edist_ofFun G h g

/-- The geometric interleaving distance of the graph-PL Reeb quotients is at most the product
extended distance of the vertex heights. -/
theorem geometricInterleavingDistance_graphPLReebGraph_le_edist [Fintype V] (h g : V → ℝ) :
    geometricInterleavingDistance (graphPLReebGraph G h) (graphPLReebGraph G g) ≤ edist h g := by
  rw [geometricInterleavingDistance_graphPLReebGraph]
  exact interleavingDistance_intervalComponents_plHeight_le_edist G h g

variable [Finite V] {h g : V → ℝ}

/-- A vertex budget `ε` bounds the geometric interleaving distance of the graph-PL Reeb
quotients. -/
theorem geometricInterleavingDistance_graphPLReebGraph_le {ε : ℝ≥0}
    (hhg : ∀ v, |h v - g v| ≤ ε) :
    geometricInterleavingDistance (graphPLReebGraph G h) (graphPLReebGraph G g) ≤ ε := by
  rw [geometricInterleavingDistance_graphPLReebGraph]
  exact interleavingDistance_intervalComponents_plHeight_le G hhg

end TDA.Mapper.GraphPL
