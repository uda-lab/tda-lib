import TDA.Mapper.GraphPLReebStability
import TDA.Mapper.UniformCover
import TDA.Reeb.GraphPLVertexPerturbationExamples

/-!
# Stability of graph-PL Reeb quotients: fixtures

Q1. On an empty vertex type, the Reeb quotients of any two heights are at distance `0`. On the
single edge, equal heights give zero uniform displacement and Reeb distance `0`.

Q2. One vertex at heights `a` and `b`: the Reeb quotients are at distance exactly `|a - b|`; the
lower bound is the height-range bound.

Q3. The single edge from heights `(0, 0)` to `(0, 1)`: one vertex level becomes two, a horizontal
edge becomes nonhorizontal, and the Reeb quotients are at distance exactly `1`; the lower bound
compares the suprema of the height ranges.

Q4. On the single edge, reversing the heights `(0, 1)` to `(1, 0)` gives distance `0`, strictly
below `edist h g = 1`: the vertex swap is a height-preserving homeomorphism of the realizations.
Collapsing the heights to the common value `1/2` gives distance at most `1/2`. No order
preservation is assumed.

Q5. On two disjoint edges, a graph that is not connected, raising one edge by `1` gives distance at
most `1`.
-/

namespace TDA.Mapper.GraphPLReebStabilityExamples

open Set SimpleGraph
open TDA.Reeb TDA.Reeb.GraphPL TDA.Reeb.GraphRealization TDA.Reeb.RGraph
open TDA.Mapper.GraphPL
open TDA.Reeb.Examples.GraphRealization (edgeGraph d₀ pointGraph twoEdges fst_eq_of_reachable)
open TDA.Reeb.Examples.GraphPLVertexPerturbation (flat tilted edist_flat_tilted)
open scoped NNReal ENNReal

noncomputable section

/-! ## Q1. The empty vertex type -/

/-- On an empty vertex type, the graph-PL Reeb quotients of any two heights are at geometric
distance `0`. -/
theorem empty_geometricInterleavingDistance (G : SimpleGraph Empty) (h g : Empty → ℝ) :
    geometricInterleavingDistance (graphPLReebGraph G h) (graphPLReebGraph G g) = 0 := by
  have hz : edist h g = 0 := by
    rw [edist_pi_def, Finset.univ_eq_empty, Finset.sup_empty]
    rfl
  exact le_antisymm ((geometricInterleavingDistance_graphPLReebGraph_le_edist G h g).trans
    hz.le) bot_le

/-- Equal heights on the single edge: zero uniform displacement of the piecewise-linear heights
and Reeb distance `0`, from the vertex-height bound. -/
theorem tilted_self_geometricInterleavingDistance :
    edist (UniformFun.ofFun (plHeight edgeGraph tilted))
        (UniformFun.ofFun (plHeight edgeGraph tilted)) = 0 ∧
      geometricInterleavingDistance (graphPLReebGraph edgeGraph tilted)
        (graphPLReebGraph edgeGraph tilted) = 0 := by
  refine ⟨edist_self _, le_antisymm ?_ bot_le⟩
  exact (geometricInterleavingDistance_graphPLReebGraph_le_edist edgeGraph tilted tilted).trans
    (edist_self _).le

/-! ## Q2. One vertex -/

private theorem heightRange_point (a : ℝ) :
    heightRange (graphPLReebGraph pointGraph fun _ => a) = {a} := by
  rw [heightRange_graphPLReebGraph]
  ext t
  constructor
  · rintro ⟨x, rfl⟩
    rw [Subsingleton.elim x (vertex pointGraph ()), plHeight_vertex]
    rfl
  · rintro rfl
    exact ⟨vertex pointGraph (), rfl⟩

/-- One vertex at heights `a` and `b`: the Reeb quotients are at distance exactly `|a - b|`. -/
theorem point_geometricInterleavingDistance (a b : ℝ) :
    geometricInterleavingDistance (graphPLReebGraph pointGraph fun _ => a)
      (graphPLReebGraph pointGraph fun _ => b) = ENNReal.ofReal |a - b| := by
  have hab : ENNReal.ofReal |a - b| = edist a b := by rw [edist_dist, Real.dist_eq]
  apply le_antisymm
  · rw [hab, ← edist_pi_const (β := Unit) a b]
    exact geometricInterleavingDistance_graphPLReebGraph_le_edist pointGraph _ _
  · have hdist := hausdorffEDist_heightRange_le_geometricInterleavingDistance
      (graphPLReebGraph pointGraph fun _ => a) (graphPLReebGraph pointGraph fun _ => b)
    rw [heightRange_point, heightRange_point, Metric.hausdorffEDist_singleton] at hdist
    rwa [hab]

/-! ## Q3. The single edge from `(0, 0)` to `(0, 1)` -/

private theorem sSup_heightRange_flat :
    sSup (heightRange (graphPLReebGraph edgeGraph flat)) = 0 := by
  rw [heightRange_graphPLReebGraph]
  apply IsGreatest.csSup_eq
  refine ⟨⟨vertex edgeGraph false, rfl⟩, ?_⟩
  rintro _ ⟨x, rfl⟩
  exact (plHeight_mem_Icc_of_forall (m := 0) (M := 0)
    (fun v => by simp [flat]) x).2

private theorem sSup_heightRange_tilted :
    sSup (heightRange (graphPLReebGraph edgeGraph tilted)) = 1 := by
  rw [heightRange_graphPLReebGraph]
  apply IsGreatest.csSup_eq
  refine ⟨⟨vertex edgeGraph true, by simp [tilted]⟩, ?_⟩
  rintro _ ⟨x, rfl⟩
  exact (plHeight_mem_Icc_of_forall (m := 0) (M := 1)
    (fun v => by cases v <;> simp [tilted]) x).2

/-- The single edge with heights `(0, 0)` and `(0, 1)`: one vertex level becomes two, the edge
stops being horizontal, and the Reeb quotients are at distance exactly `1`. -/
theorem flat_tilted_geometricInterleavingDistance :
    range flat = {0} ∧ range tilted = {0, 1} ∧
      flat d₀.fst = flat d₀.snd ∧ tilted d₀.fst ≠ tilted d₀.snd ∧
      geometricInterleavingDistance (graphPLReebGraph edgeGraph flat)
        (graphPLReebGraph edgeGraph tilted) = 1 := by
  refine ⟨?_, ?_, rfl, by norm_num [tilted, d₀], ?_⟩
  · exact range_const
  · ext t
    constructor
    · rintro ⟨b, rfl⟩
      cases b <;> simp [tilted]
    · rintro (rfl | rfl)
      · exact ⟨false, by simp [tilted]⟩
      · exact ⟨true, by simp [tilted]⟩
  · apply le_antisymm
    · rw [← edist_flat_tilted]
      exact geometricInterleavingDistance_graphPLReebGraph_le_edist edgeGraph flat tilted
    · have hne : ∀ h : Bool → ℝ, (heightRange (graphPLReebGraph edgeGraph h)).Nonempty :=
        fun h => by
          rw [heightRange_graphPLReebGraph]
          exact range_nonempty_iff_nonempty.2 ⟨vertex edgeGraph false⟩
      have hsup := ofReal_abs_sSup_sub_le_hausdorffEDist (hne flat) (hne tilted)
        (bddAbove_heightRange _) (bddAbove_heightRange _)
      rw [sSup_heightRange_flat, sSup_heightRange_tilted] at hsup
      norm_num at hsup
      exact hsup.trans (hausdorffEDist_heightRange_le_geometricInterleavingDistance _ _)

/-! ## Q4. Order reversal and collision -/

/-- Height `1` at `false` and `0` at `true`, the reversal of `tilted`. -/
def reversed : Bool → ℝ := fun b => if b then 0 else 1

/-- The common height `1/2` at both endpoints. -/
def collided : Bool → ℝ := fun _ => 1 / 2

/-- The vertex swap of the single edge. -/
def swapEdge : edgeGraph →g edgeGraph where
  toFun := not
  map_rel' h := by simpa using h

private theorem swapEdge_comp : swapEdge.comp swapEdge = Hom.id :=
  RelHom.ext Bool.not_not

/-- The vertex swap as a homeomorphism of the realization of the single edge. -/
def swapHomeomorph : Realization edgeGraph ≃ₜ Realization edgeGraph where
  toFun := realizationMap swapEdge
  invFun := realizationMap swapEdge
  left_inv x := by
    rw [← ContinuousMap.comp_apply, ← realizationMap_comp, swapEdge_comp, realizationMap_id]
    rfl
  right_inv x := by
    rw [← ContinuousMap.comp_apply, ← realizationMap_comp, swapEdge_comp, realizationMap_id]
    rfl
  continuous_toFun := (realizationMap swapEdge).continuous
  continuous_invFun := (realizationMap swapEdge).continuous

private theorem reversed_swap (b : Bool) : reversed (swapEdge b) = tilted b := by
  cases b <;> rfl

private theorem plHeight_reversed_swap (x : Realization edgeGraph) :
    plHeight edgeGraph reversed (swapHomeomorph x) = plHeight edgeGraph tilted x := by
  induction x using GraphRealization.ind with
  | vertex v => exact reversed_swap v
  | edgePoint d t =>
    change (1 - (t : ℝ)) * reversed (swapEdge d.fst) + (t : ℝ) * reversed (swapEdge d.snd) =
      (1 - (t : ℝ)) * tilted d.fst + (t : ℝ) * tilted d.snd
    rw [reversed_swap, reversed_swap]

/-- Reversing the order of the two endpoint heights gives isomorphic Reeb quotients, at distance
`0`, while the vertex heights are at distance `1`. -/
theorem reversal_geometricInterleavingDistance :
    tilted false < tilted true ∧ reversed true < reversed false ∧ edist tilted reversed = 1 ∧
      geometricInterleavingDistance (graphPLReebGraph edgeGraph tilted)
        (graphPLReebGraph edgeGraph reversed) = 0 := by
  refine ⟨by norm_num [tilted], by norm_num [reversed], ?_, ?_⟩
  · apply le_antisymm
    · refine edist_pi_le_iff.2 fun b => ?_
      cases b <;> norm_num [tilted, reversed, edist_dist, Real.dist_eq]
    · calc (1 : ℝ≥0∞) = edist (tilted true) (reversed true) := by
            norm_num [tilted, reversed, edist_dist, Real.dist_eq]
        _ ≤ edist tilted reversed := edist_le_pi_edist tilted reversed true
  · let e : graphPLOver edgeGraph tilted ≅ graphPLOver edgeGraph reversed :=
      CategoryTheory.Over.isoMk (TopCat.isoOfHomeo swapHomeomorph) (by
        ext x
        exact plHeight_reversed_swap x)
    exact geometricInterleavingDistance_eq_zero_of_iso
      (CategoryTheory.ObjectProperty.isoMk _ ((ReebQuotient.quotientFunctor ℝ).mapIso e))

/-- Collapsing the two endpoint heights to `1/2` makes the edge horizontal and moves the Reeb
quotient by at most `1/2`. -/
theorem collision_geometricInterleavingDistance_le :
    collided false = collided true ∧
      geometricInterleavingDistance (graphPLReebGraph edgeGraph tilted)
        (graphPLReebGraph edgeGraph collided) ≤ ((1 / 2 : ℝ≥0) : ℝ≥0∞) := by
  refine ⟨rfl, ?_⟩
  exact geometricInterleavingDistance_graphPLReebGraph_le edgeGraph
    fun b => by cases b <;> norm_num [tilted, collided]

/-! ## Q5. A disconnected graph -/

/-- Height `0` at the bottom and `1` at the top of each of the two edges. -/
def twoEdgesHeight : Bool × Bool → ℝ := fun p => if p.2 then 1 else 0

/-- `twoEdgesHeight` with the edge `p.1 = true` raised by `1`. -/
def twoEdgesRaised : Bool × Bool → ℝ := fun p => twoEdgesHeight p + if p.1 then 1 else 0

/-- On two disjoint edges, raising one edge by `1` moves the Reeb quotient by at most `1`. -/
theorem twoEdges_geometricInterleavingDistance_le :
    ¬ twoEdges.Connected ∧
      geometricInterleavingDistance (graphPLReebGraph twoEdges twoEdgesHeight)
        (graphPLReebGraph twoEdges twoEdgesRaised) ≤ 1 := by
  refine ⟨fun hc => ?_, ?_⟩
  · exact Bool.false_ne_true (fst_eq_of_reachable (hc.preconnected (false, false) (true, false)))
  · exact_mod_cast geometricInterleavingDistance_graphPLReebGraph_le twoEdges (ε := 1)
      fun p => by rcases p with ⟨_ | _, _ | _⟩ <;> norm_num [twoEdgesRaised, twoEdgesHeight]

end

end TDA.Mapper.GraphPLReebStabilityExamples
