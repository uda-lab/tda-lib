import TDA.Reeb.HeightMapPair
import TDA.Mapper.GraphPLReebQuotient

/-!
# Graph-PL Reeb distance from height-map pairs

For finite graphs on vertex types in `Type`, a `HeightMapPair` between their piecewise-linear
heights bounds the geometric interleaving distance of their graph-PL Reeb quotients. The bound
uses the equality between geometric distance and interval-component interleaving distance for
these quotients. It does not construct a map between the quotient graph objects or a Mapper
comparison. -/

namespace TDA.Mapper.GraphPL

open TDA.Reeb
open TDA.Reeb.GraphPL
open TDA.Reeb.RGraph
open scoped NNReal ENNReal

/-- A height-map pair between two finite graph-PL spaces bounds the geometric interleaving
distance of their Reeb quotients by its parameter. -/
theorem geometricInterleavingDistance_graphPLReebGraph_le_of_heightMapPair
    {V V' : Type} [Finite V] [Finite V'] {G : SimpleGraph V} {G' : SimpleGraph V'}
    {h : V → ℝ} {h' : V' → ℝ} {ε : ℝ≥0}
    (P : HeightMapPair (plHeight G h) (plHeight G' h') ε) :
    geometricInterleavingDistance (graphPLReebGraph G h) (graphPLReebGraph G' h') ≤ ε := by
  rw [geometricInterleavingDistance_graphPLReebGraph G h G' h']
  exact P.interleavingDistance_le

end TDA.Mapper.GraphPL
