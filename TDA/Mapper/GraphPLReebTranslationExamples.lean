import TDA.Mapper.GraphPLReebStabilityExamples
import TDA.Reeb.RGraphTranslation
import TDA.Reeb.GraphPLHeightExamples

/-!
# Translation of graph-PL Reeb quotients: fixtures

P1. On the single edge with heights `(0, 2)`, the Reeb quotient of the heights `(1, 3)` is the
translate by `1` of the Reeb quotient of `(0, 2)`, through the commutation of the Reeb quotient
with translation and `plHeight_add_const`. The exact self-translation distance then gives distance
`1`, the value of `geometricInterleavingDistance_graphPLReebGraph_add_const` on this instance.

P2. The flat and tilted single edges `(0, 0)` and `(0, 1)` are at distance `1`; their translates by
`5` are still at distance `1`.

The single edge with heights `(0, 1)` and its reversal `(1, 0)` are at distance `0`
(`reversal_geometricInterleavingDistance`) although the heights are not related by a translation;
the exact distance `|c|` concerns a graph object and its own translate only.
-/

open CategoryTheory
open scoped ENNReal

namespace TDA.Mapper.GraphPLReebTranslationExamples

open TDA.Reeb TDA.Reeb.RGraph TDA.Reeb.GraphPL TDA.Reeb.GraphRealization
open TDA.Mapper.GraphPL
open TDA.Reeb.Examples.GraphPL (h02)
open TDA.Reeb.Examples.GraphRealization (edgeGraph)
open TDA.Reeb.Examples.GraphPLVertexPerturbation (flat tilted)
open TDA.Mapper.GraphPLReebStabilityExamples (flat_tilted_geometricInterleavingDistance)

noncomputable section

/-! ## P1. The single edge `(0, 2)` and its translate by `1` -/

/-- The Reeb quotient of the heights `(1, 3)` is the translate by `1` of that of `(0, 2)`. -/
def edgeTranslateIso :
    graphPLReebGraph edgeGraph (fun v => h02 v + 1) ≅
      (translateRGraph 1).obj (graphPLReebGraph edgeGraph h02) :=
  let e : graphPLOver edgeGraph (fun v => h02 v + 1) ≅
      (translateOver 1).obj (graphPLOver edgeGraph h02) :=
    Over.isoMk (Iso.refl _) (by
      ext x
      exact (plHeight_add_const_apply edgeGraph h02 1 x).symm)
  IsRGraph.isoMk <|
    (ReebQuotient.quotientFunctor ℝ).mapIso e ≪≫
      (quotientTranslateIso 1).app (graphPLOver edgeGraph h02)

/-- The Reeb quotients of `(0, 2)` and `(1, 3)` are at distance `1`, from the exact
self-translation distance. -/
theorem edge_translate_distance :
    geometricInterleavingDistance (graphPLReebGraph edgeGraph h02)
      (graphPLReebGraph edgeGraph fun v => h02 v + 1) = 1 := by
  rw [geometricInterleavingDistance_congr_right _ edgeTranslateIso,
    geometricInterleavingDistance_translateRGraph_self _
      ⟨ReebQuotient.mk _ (vertex edgeGraph false)⟩ 1, abs_one, ENNReal.ofReal_one]

/-! ## P2. The flat and tilted edges translated by `5` -/

/-- The translates by `5` of the flat and tilted single edges are at distance `1`. -/
theorem flat_tilted_translate_distance :
    geometricInterleavingDistance ((translateRGraph 5).obj (graphPLReebGraph edgeGraph flat))
      ((translateRGraph 5).obj (graphPLReebGraph edgeGraph tilted)) = 1 := by
  rw [geometricInterleavingDistance_translateRGraph]
  exact flat_tilted_geometricInterleavingDistance.2.2.2.2

end

end TDA.Mapper.GraphPLReebTranslationExamples
