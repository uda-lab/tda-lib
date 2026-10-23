import TDA.Mapper.GraphPLReebStability
import TDA.Mapper.UniformCover
import Mathlib.Algebra.Order.Group.Finset

/-!
# Extremal vertex heights and the graph-PL Reeb distance

Fix a simple graph `G` on a finite nonempty `V : Type` and vertex heights `h g : V → ℝ`. The
attained range of `plHeight G h` has supremum `Finset.univ.sup' _ h` and infimum
`Finset.univ.inf' _ h` (`sSup_range_plHeight`, `sInf_range_plHeight`): vertices attain both, and
`plHeight_mem_Icc_of_forall` bounds every point. With `heightRange_graphPLReebGraph` and the
real-line bounds `ofReal_abs_sSup_sub_le_hausdorffEDist` and
`ofReal_abs_sInf_sub_le_hausdorffEDist`, the geometric interleaving distance of
`graphPLReebGraph G h` and `graphPLReebGraph G g` is at least the displacement of the maximal
vertex heights and at least the displacement of the minimal vertex heights.

Together with the upper bound `edist h g`, the distance equals `edist h g` whenever one extremal
displacement attains it. This holds for every vertical translation `fun v => h v + c`, whose
distance from `h` is `ENNReal.ofReal |c|`, for any graph, connected or not. For an empty vertex
type the distance is `0`.

The distance is not claimed to equal `edist h g` in general; exactness is conditional on the
stated hypothesis.
-/

namespace TDA.Mapper.GraphPL

open Set
open TDA.Reeb TDA.Reeb.GraphPL TDA.Reeb.RGraph
open scoped ENNReal

variable {V : Type} (G : SimpleGraph V)

section Extremal

variable [Fintype V] [Nonempty V] (h g : V → ℝ)

/-- The supremum of the attained range of a graph-PL height is the maximal vertex height. -/
theorem sSup_range_plHeight :
    sSup (range (plHeight G h)) = Finset.univ.sup' Finset.univ_nonempty h := by
  apply IsGreatest.csSup_eq
  obtain ⟨v, -, hv⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty h
  refine ⟨⟨GraphRealization.vertex G v, by simpa using hv.symm⟩, ?_⟩
  rintro _ ⟨x, rfl⟩
  exact (plHeight_mem_Icc_of_forall (m := Finset.univ.inf' Finset.univ_nonempty h)
    (M := Finset.univ.sup' Finset.univ_nonempty h)
    (fun w => ⟨Finset.inf'_le _ (Finset.mem_univ w), Finset.le_sup' _ (Finset.mem_univ w)⟩) x).2

/-- The infimum of the attained range of a graph-PL height is the minimal vertex height. -/
theorem sInf_range_plHeight :
    sInf (range (plHeight G h)) = Finset.univ.inf' Finset.univ_nonempty h := by
  apply IsLeast.csInf_eq
  obtain ⟨v, -, hv⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty h
  refine ⟨⟨GraphRealization.vertex G v, by simpa using hv.symm⟩, ?_⟩
  rintro _ ⟨x, rfl⟩
  exact (plHeight_mem_Icc_of_forall (m := Finset.univ.inf' Finset.univ_nonempty h)
    (M := Finset.univ.sup' Finset.univ_nonempty h)
    (fun w => ⟨Finset.inf'_le _ (Finset.mem_univ w), Finset.le_sup' _ (Finset.mem_univ w)⟩) x).1

private theorem nonempty_heightRange :
    (heightRange (graphPLReebGraph G h)).Nonempty := by
  rw [heightRange_graphPLReebGraph]
  exact range_nonempty_iff_nonempty.2 ⟨GraphRealization.vertex G (Classical.arbitrary V)⟩

/-- The displacement of the maximal vertex heights bounds the geometric interleaving distance
of the graph-PL Reeb quotients from below. -/
theorem ofReal_abs_sup'_sub_le_geometricInterleavingDistance_graphPLReebGraph :
    ENNReal.ofReal |Finset.univ.sup' Finset.univ_nonempty h -
        Finset.univ.sup' Finset.univ_nonempty g| ≤
      geometricInterleavingDistance (graphPLReebGraph G h) (graphPLReebGraph G g) := by
  have key := ofReal_abs_sSup_sub_le_hausdorffEDist (nonempty_heightRange G h)
    (nonempty_heightRange G g) (bddAbove_heightRange _) (bddAbove_heightRange _)
  rw [heightRange_graphPLReebGraph, heightRange_graphPLReebGraph, sSup_range_plHeight,
    sSup_range_plHeight] at key
  refine key.trans ?_
  have := hausdorffEDist_heightRange_le_geometricInterleavingDistance
    (graphPLReebGraph G h) (graphPLReebGraph G g)
  rwa [heightRange_graphPLReebGraph, heightRange_graphPLReebGraph] at this

/-- The displacement of the minimal vertex heights bounds the geometric interleaving distance
of the graph-PL Reeb quotients from below. -/
theorem ofReal_abs_inf'_sub_le_geometricInterleavingDistance_graphPLReebGraph :
    ENNReal.ofReal |Finset.univ.inf' Finset.univ_nonempty h -
        Finset.univ.inf' Finset.univ_nonempty g| ≤
      geometricInterleavingDistance (graphPLReebGraph G h) (graphPLReebGraph G g) := by
  have key := ofReal_abs_sInf_sub_le_hausdorffEDist (nonempty_heightRange G h)
    (nonempty_heightRange G g) (bddBelow_heightRange _) (bddBelow_heightRange _)
  rw [heightRange_graphPLReebGraph, heightRange_graphPLReebGraph, sInf_range_plHeight,
    sInf_range_plHeight] at key
  refine key.trans ?_
  have := hausdorffEDist_heightRange_le_geometricInterleavingDistance
    (graphPLReebGraph G h) (graphPLReebGraph G g)
  rwa [heightRange_graphPLReebGraph, heightRange_graphPLReebGraph] at this

/-- The larger of the two extremal displacements bounds the geometric interleaving distance of
the graph-PL Reeb quotients from below. -/
theorem max_ofReal_abs_sub_le_geometricInterleavingDistance_graphPLReebGraph :
    max (ENNReal.ofReal |Finset.univ.sup' Finset.univ_nonempty h -
        Finset.univ.sup' Finset.univ_nonempty g|)
      (ENNReal.ofReal |Finset.univ.inf' Finset.univ_nonempty h -
        Finset.univ.inf' Finset.univ_nonempty g|) ≤
      geometricInterleavingDistance (graphPLReebGraph G h) (graphPLReebGraph G g) :=
  max_le (ofReal_abs_sup'_sub_le_geometricInterleavingDistance_graphPLReebGraph G h g)
    (ofReal_abs_inf'_sub_le_geometricInterleavingDistance_graphPLReebGraph G h g)

variable {G h g}

/-- If the displacement of the maximal vertex heights is the vertex sup displacement, it is the
geometric interleaving distance of the graph-PL Reeb quotients. -/
theorem geometricInterleavingDistance_graphPLReebGraph_eq_edist_of_sup'
    (hsup : edist h g = ENNReal.ofReal |Finset.univ.sup' Finset.univ_nonempty h -
      Finset.univ.sup' Finset.univ_nonempty g|) :
    geometricInterleavingDistance (graphPLReebGraph G h) (graphPLReebGraph G g) = edist h g :=
  le_antisymm (geometricInterleavingDistance_graphPLReebGraph_le_edist G h g)
    (hsup ▸ ofReal_abs_sup'_sub_le_geometricInterleavingDistance_graphPLReebGraph G h g)

/-- If the displacement of the minimal vertex heights is the vertex sup displacement, it is the
geometric interleaving distance of the graph-PL Reeb quotients. -/
theorem geometricInterleavingDistance_graphPLReebGraph_eq_edist_of_inf'
    (hinf : edist h g = ENNReal.ofReal |Finset.univ.inf' Finset.univ_nonempty h -
      Finset.univ.inf' Finset.univ_nonempty g|) :
    geometricInterleavingDistance (graphPLReebGraph G h) (graphPLReebGraph G g) = edist h g :=
  le_antisymm (geometricInterleavingDistance_graphPLReebGraph_le_edist G h g)
    (hinf ▸ ofReal_abs_inf'_sub_le_geometricInterleavingDistance_graphPLReebGraph G h g)

private theorem edist_add_const (c : ℝ) : edist h (fun v => h v + c) = ENNReal.ofReal |c| := by
  have hv (v : V) : edist (h v) (h v + c) = ENNReal.ofReal |c| := by
    rw [edist_dist, Real.dist_eq, show h v - (h v + c) = -c by ring, abs_neg]
  exact le_antisymm (edist_pi_le_iff.2 fun v => (hv v).le)
    ((hv (Classical.arbitrary V)).ge.trans (edist_le_pi_edist _ _ _))

/-- The geometric interleaving distance of the graph-PL Reeb quotients of a vertex-height
function and its vertical translate by `c` is `|c|`, on any graph. -/
theorem geometricInterleavingDistance_graphPLReebGraph_add_const (c : ℝ) :
    geometricInterleavingDistance (graphPLReebGraph G h) (graphPLReebGraph G fun v => h v + c) =
      ENNReal.ofReal |c| := by
  rw [← edist_add_const (h := h) c]
  apply geometricInterleavingDistance_graphPLReebGraph_eq_edist_of_sup'
  have hsup : Finset.univ.sup' Finset.univ_nonempty (fun v => h v + c) =
      Finset.univ.sup' Finset.univ_nonempty h + c :=
    (Finset.sup'_add _ _ _ _).symm
  rw [edist_add_const, hsup, show Finset.univ.sup' Finset.univ_nonempty h -
    (Finset.univ.sup' Finset.univ_nonempty h + c) = -c by ring, abs_neg]

end Extremal

/-- On an empty vertex type, the graph-PL Reeb quotients of any two heights are at geometric
distance `0`. -/
theorem geometricInterleavingDistance_graphPLReebGraph_of_isEmpty [IsEmpty V] (h g : V → ℝ) :
    geometricInterleavingDistance (graphPLReebGraph G h) (graphPLReebGraph G g) = 0 := by
  have : Fintype V := Fintype.ofIsEmpty
  have hz : edist h g = 0 := by
    rw [edist_pi_def, Finset.univ_eq_empty, Finset.sup_empty]
    rfl
  exact le_antisymm ((geometricInterleavingDistance_graphPLReebGraph_le_edist G h g).trans
    hz.le) bot_le

end TDA.Mapper.GraphPL
