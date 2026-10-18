import TDA.Mapper.GraphPLReebQuotient
import TDA.Mapper.GraphPLCosheafExamples
import TDA.Mapper.GraphPLRefinementExamples

/-!
# Reeb quotients of graph-PL heights: fixtures

R1. The 4-cycle quotient is isomorphic to the cycle finite data and not to path data.

R2. The single-edge quotient is identified at both the coarse list `S02` and the refinement
`S012`, whose middle level carries no vertex.

R3. The subdivided Y-tree quotient is identified with its finite graph-PL data and is an
R-graph.

R4. A horizontal edge collapses to one Reeb-quotient point, although its two realization
vertices remain distinct.

R5. The interval-component comparison is an isomorphism for the 4-cycle graph-PL height.

R6. The quotient identification fails for the uncovered middle level of the path with heights
`0, 1, 2` and the list `S02`.
-/

namespace TDA.Mapper.GraphPLReebQuotientExamples

open Set SimpleGraph CategoryTheory
open TDA.Reeb TDA.Reeb.GraphPL TDA.Reeb.GraphRealization TDA.Reeb.OpenInterval TDA.Reeb.RGraph
open TDA.Reeb.Examples.GraphPL
open TDA.Reeb.Examples.GraphRealization (edgeGraph d₀ edgeGraph_dart pointGraph path3)
open TDA.Mapper.GraphPL
open TDA.Mapper.UniformCoverExamples (d12 d03 c4_edge_cases)
open TDA.Mapper.UniformCoverCellsExamples (Y hY y02 y12 y23 Y_edge_cases Y_vertexCells_one
  Y_vertexCells_other Y_edgeCells)
open TDA.Reeb.Examples.Cylinder (S01 S01_value_zero S01_value_one)
open TDA.Reeb.Examples.ConstructibleCylinder (S0 S012)
open TDA.Reeb.Examples.ConstructibleRepresentation (S02)
open TDA.Reeb.RGraph.Examples (cycleData pathData cycle_not_iso_path)
open TDA.Mapper.GraphPLReebDataExamples
open TDA.Mapper.GraphPLRefinementExamples (h012 path_S02_E0_empty)

noncomputable section

/-! ## R1. The 4-cycle -/

/-- The Reeb quotient of the graph-PL 4-cycle is the finite cycle realization. -/
noncomputable def c4_reebQuotientIso :
    (ReebQuotient.quotientFunctor ℝ).obj (graphPLOver C4 h4) ≅ toOver S012 cycleData :=
  graphPLReebQuotientIsoOfIso C4 h4 c4_covers cycleIso

/-- The Reeb quotient of the graph-PL 4-cycle is not the finite path realization. -/
theorem c4_reebQuotient_not_iso_path :
    IsEmpty ((ReebQuotient.quotientFunctor ℝ).obj (graphPLOver C4 h4) ≅
      toOver S012 pathData) := by
  constructor
  intro i
  exact cycle_not_iso_path.false (c4_reebQuotientIso.symm ≪≫ i)

/-! ## R2. The single edge -/

/-- The single-edge Reeb quotient is the finite realization at `S02`. -/
noncomputable def edge_reebQuotientIso_S02 :
    (ReebQuotient.quotientFunctor ℝ).obj (graphPLOver edgeGraph h02) ≅
      toOver S02 (graphPLReebData edgeGraph h02 S02) :=
  graphPLReebQuotientIso edgeGraph h02 edge_covers_S02

/-- The single-edge Reeb quotient is the finite realization at `S012`. -/
noncomputable def edge_reebQuotientIso_S012 :
    (ReebQuotient.quotientFunctor ℝ).obj (graphPLOver edgeGraph h02) ≅
      toOver S012 (graphPLReebData edgeGraph h02 S012) :=
  graphPLReebQuotientIso edgeGraph h02 edge_covers_S012

/-! ## R3. The subdivided Y-tree -/

/-- The subdivided Y-tree Reeb quotient is the finite realization at `S0123`. -/
noncomputable def Y_reebQuotientIso :
    (ReebQuotient.quotientFunctor ℝ).obj (graphPLOver Y hY) ≅
      toOver S0123 (graphPLReebData Y hY S0123) :=
  graphPLReebQuotientIso Y hY Y_covers

/-- The subdivided Y-tree Reeb quotient is an R-graph. -/
theorem Y_isRGraph :
    RGraph.IsRGraph ((ReebQuotient.quotientFunctor ℝ).obj (graphPLOver Y hY)) :=
  isRGraph_graphPLReebQuotient Y hY

/-! ## R4. The horizontal edge -/

/-- The constant-height horizontal edge has a subsingleton Reeb quotient. -/
theorem flatEdge_reebQuotient_subsingleton :
    Subsingleton (ReebQuotient (plHeight edgeGraph (fun _ => (0 : ℝ)))) := by
  have hsub :
      Subsingleton
        ((CylinderPresentation.ofFiniteData
          (graphPLReebData edgeGraph (fun _ => (0 : ℝ)) S0)).V 0) :=
    (Nat.card_eq_one_iff_unique.1 flatEdge_count).1
  have hrealization : Subsingleton
      ((CylinderPresentation.ofFiniteData
        (graphPLReebData edgeGraph (fun _ => (0 : ℝ)) S0)).Realization S0) := by
    constructor
    intro x y
    rcases (CylinderPresentation.ofFiniteData
      (graphPLReebData edgeGraph (fun _ => (0 : ℝ)) S0)).exists_rep S0 x with
      ⟨i, v, hx⟩ | ⟨e, p, hx⟩
    · rcases (CylinderPresentation.ofFiniteData
        (graphPLReebData edgeGraph (fun _ => (0 : ℝ)) S0)).exists_rep S0 y with
        ⟨j, w, hy⟩ | ⟨e, p, hy⟩
      · have hi : i = 0 := Fin.eq_zero i
        have hj : j = 0 := Fin.eq_zero j
        subst i
        subst j
        rw [hx, hy, @Subsingleton.elim _ hsub v w]
      · exact e.elim0
    · exact e.elim0
  haveI : Subsingleton
      ((CylinderPresentation.ofFiniteData
        (graphPLReebData edgeGraph (fun _ => (0 : ℝ)) S0)).Realization S0) := hrealization
  exact Equiv.subsingleton
    (graphPLReebQuotientHomeomorph edgeGraph (fun _ => (0 : ℝ)) const_covers).toEquiv

/-- The two endpoint vertices of the horizontal edge remain distinct in the realization. -/
theorem flatEdge_vertex_ne :
    vertex edgeGraph false ≠ vertex edgeGraph true :=
  (vertex_injective edgeGraph).ne (by decide)

/-! ## R5. The comparison -/

/-- The interval-component comparison is an isomorphism for the graph-PL 4-cycle height. -/
theorem c4_isIso_intervalComponentComparison :
    IsIso (ReebQuotient.intervalComponentComparison (plHeight C4 h4)) :=
  inferInstance

/-! ## R6. The uncovered-level negative control -/

/-- The `S02` quotient identification fails for the path whose middle vertex has height `1`. -/
theorem path3_reebQuotient_not_iso_S02 :
    IsEmpty ((ReebQuotient.quotientFunctor ℝ).obj (graphPLOver path3 h012) ≅
      toOver S02 (graphPLReebData path3 h012 S02)) := by
  constructor
  intro i
  let q : ReebQuotient (plHeight path3 h012) :=
    ReebQuotient.mk _ (vertex path3 1)
  have hq :
      (CylinderPresentation.ofFiniteData (graphPLReebData path3 h012 S02)).height S02
          (i.hom.left.hom q) = 1 := by
    have hcomm := overBaseMap_comm i.hom q
    change (CylinderPresentation.ofFiniteData (graphPLReebData path3 h012 S02)).height S02
        (i.hom.left.hom q) = ReebQuotient.height (plHeight path3 h012) q at hcomm
    rw [hcomm]
    rw [ReebQuotient.height_mk, plHeight_vertex]
    rfl
  have hlevel : ∀ j, S02.value j ≠ (1 : ℝ) := by
    intro j
    fin_cases j <;> norm_num [S02]
  obtain ⟨e, _, z, hz⟩ :=
    RGraph.exists_strip_rep
      (CylinderPresentation.ofFiniteData (graphPLReebData path3 h012 S02))
      (i.hom.left.hom q) hq hlevel
  have he : e = 0 := Fin.eq_zero e
  subst e
  exact path_S02_E0_empty.false z

end

end TDA.Mapper.GraphPLReebQuotientExamples
