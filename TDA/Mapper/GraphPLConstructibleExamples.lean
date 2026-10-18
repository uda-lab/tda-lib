import TDA.Mapper.GraphPLConstructible
import TDA.Mapper.GraphPLReebQuotientExamples

/-!
# Graph-PL constructible spaces: mandatory fixtures

K1 records constructibility of the 4-cycle, its component-data identification with the finite
cycle, and the corresponding quotient-isomorphism identification. K2 records the presentation
homeomorphism and thickening R-graph property for the subdivided Y-tree. K3 and K4 distinguish
the non-discrete horizontal-edge vertex piece from its collapsed Reeb quotient. K5 records the
failure of surjectivity for the uncovered `S02` presentation of the path with heights `0, 1, 2`.
K6 gives the midpoint/vertex separation and the Hausdorff instance for the 4-cycle. K7 records
the quotient-functor object equation and the resulting geometric interleaving-distance formula.
-/

namespace TDA.Mapper.GraphPLConstructibleExamples

open Set SimpleGraph CategoryTheory
open scoped NNReal
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

/-! ## K1. The 4-cycle -/

/-- The graph-PL 4-cycle is a constructible space over the real line. -/
theorem c4_isConstructibleSpace : IsConstructibleSpace (graphPLOver C4 h4) :=
  isConstructibleSpace_graphPLOver C4 h4

/-- The 4-cycle presentation component data are the finite cycle data. -/
noncomputable def c4_componentDataIso :
    (graphPLPresentation C4 h4 S012).componentData ≅ cycleData :=
  graphPLComponentDataIso C4 h4 S012 ≪≫ cycleIso.symm

/-- The two quotient-isomorphism constructions agree for the covering list `S012`. -/
theorem c4_quotientIsoOfIso_eq :
    graphPLReebQuotientIsoOfIso C4 h4 c4_covers
        (graphPLComponentDataIso C4 h4 S012) =
      (graphPLPresentation C4 h4 S012).quotientIsoOfIso S012
        (graphPLPresentationIso C4 h4 c4_covers) := by
  exact graphPLReebQuotientIsoOfIso_graphPLComponentDataIso C4 h4 c4_covers

/-! ## K2. The subdivided Y-tree -/

/-- The `S0123` graph-PL presentation is homeomorphic to the Y-tree realization. -/
noncomputable def Y_presentationHomeomorph :
    (graphPLPresentation Y hY S0123).Realization S0123 ≃ₜ Realization Y :=
  graphPLPresentationHomeomorph Y hY Y_covers

/-- Every geometric thickening of the Y-tree graph-PL object has an R-graph quotient. -/
theorem Y_isRGraph_thickening (ε : ℝ≥0) :
    RGraph.IsRGraph ((ReebQuotient.quotientFunctor ℝ).obj
      ((GeometricThickening.functor ε).obj (graphPLOver Y hY))) :=
  isRGraph_quotient_thickening_graphPLOver Y hY ε

/-! ## K3. The horizontal edge, positive control -/

/-- The constant-height horizontal edge is a constructible space. -/
theorem flatEdge_isConstructibleSpace :
    IsConstructibleSpace (graphPLOver edgeGraph (fun _ => (0 : ℝ))) :=
  isConstructibleSpace_graphPLOver edgeGraph (fun _ => (0 : ℝ))

/-- The vertex piece at height zero of the horizontal edge is not discrete. -/
theorem flatEdge_vertexPiece_not_discrete :
    ¬ DiscreteTopology
      ((graphPLPresentation edgeGraph (fun _ => (0 : ℝ)) S0).V 0) := by
  change ¬ DiscreteTopology (ClosedLevel edgeGraph (fun _ => (0 : ℝ)) 0)
  intro hdiscrete
  letI : DiscreteTopology (ClosedLevel edgeGraph (fun _ => (0 : ℝ)) 0) := hdiscrete
  have hfalse :
      plHeight edgeGraph (fun _ => (0 : ℝ)) (vertex edgeGraph false) ∈ ({0} : Set ℝ) := by
    simp
  have hone :
      plHeight edgeGraph (fun _ => (0 : ℝ)) (edgePoint edgeGraph d₀ (1 : unitInterval)) ∈
        ({0} : Set ℝ) := by
    simp [plHeight_edgePoint, dartHeight_one]
  have hjoined :=
    joinedIn_level_of_eq edgeGraph (fun _ => (0 : ℝ)) (c := 0) (d := d₀)
      rfl rfl (1 : unitInterval)
  have hjoined' :
      JoinedIn (plHeight edgeGraph (fun _ => (0 : ℝ)) ⁻¹' ({0} : Set ℝ))
        (vertex edgeGraph false) (edgePoint edgeGraph d₀ (1 : unitInterval)) := by
    simpa [d₀] using hjoined
  have hxy :
      (⟨vertex edgeGraph false, hfalse⟩ :
          ClosedLevel edgeGraph (fun _ => (0 : ℝ)) 0) =
        (⟨edgePoint edgeGraph d₀ (1 : unitInterval), hone⟩ :
          ClosedLevel edgeGraph (fun _ => (0 : ℝ)) 0) :=
    joined_eq_of_discrete
      ((joinedIn_iff_joined (F := plHeight edgeGraph (fun _ => (0 : ℝ)) ⁻¹' ({0} : Set ℝ))
        (x := vertex edgeGraph false) (y := edgePoint edgeGraph d₀ (1 : unitInterval))
        hfalse hone).mp hjoined')
  apply TDA.Mapper.GraphPLReebQuotientExamples.flatEdge_vertex_ne
  calc
    vertex edgeGraph false = edgePoint edgeGraph d₀ (1 : unitInterval) :=
      congrArg Subtype.val hxy
    _ = vertex edgeGraph true := edgePoint_one edgeGraph d₀

/-! ## K4. The horizontal edge, negative control -/

/-- The horizontal edge realization is not isomorphic to its discrete finite-data realization. -/
theorem flatEdge_not_iso_finiteData :
    IsEmpty (graphPLOver edgeGraph (fun _ => (0 : ℝ)) ≅
      RGraph.toOver S0 (graphPLReebData edgeGraph (fun _ => (0 : ℝ)) S0)) := by
  constructor
  intro i
  have hq : Subsingleton (ReebQuotient (plHeight edgeGraph (fun _ => (0 : ℝ)))) :=
    TDA.Mapper.GraphPLReebQuotientExamples.flatEdge_reebQuotient_subsingleton
  letI : Subsingleton (ReebQuotient (plHeight edgeGraph (fun _ => (0 : ℝ)))) := hq
  have hsub :
      Subsingleton (↑((RGraph.toOver S0
        (graphPLReebData edgeGraph (fun _ => (0 : ℝ)) S0)).left)) := by
    change Subsingleton
      ((CylinderPresentation.ofFiniteData
        (graphPLReebData edgeGraph (fun _ => (0 : ℝ)) S0)).Realization S0)
    exact (graphPLReebQuotientHomeomorph edgeGraph (fun _ => (0 : ℝ)) const_covers).symm.toEquiv.subsingleton
  letI : Subsingleton (↑((RGraph.toOver S0
      (graphPLReebData edgeGraph (fun _ => (0 : ℝ)) S0)).left)) := hsub
  have hinj : Function.Injective i.hom.left.hom := fun x y hxy => by
    have hx : i.inv.left.hom (i.hom.left.hom x) = x :=
      congrArg (fun φ : graphPLOver edgeGraph (fun _ => (0 : ℝ)) ⟶
          graphPLOver edgeGraph (fun _ => (0 : ℝ)) => φ.left.hom x) i.hom_inv_id
    have hy : i.inv.left.hom (i.hom.left.hom y) = y :=
      congrArg (fun φ : graphPLOver edgeGraph (fun _ => (0 : ℝ)) ⟶
          graphPLOver edgeGraph (fun _ => (0 : ℝ)) => φ.left.hom y) i.hom_inv_id
    rw [← hx, ← hy, hxy]
  exact TDA.Mapper.GraphPLReebQuotientExamples.flatEdge_vertex_ne
    (hinj (Subsingleton.elim _ _))

/-! ## K5. The uncovered list -/

/-- The `S02` graph-PL presentation of the path is not surjective. -/
theorem path3_presentationMap_not_surjective :
    ¬ Function.Surjective (graphPLPresentationMap path3 h012 S02) := by
  intro hsurjective
  obtain ⟨x, hx⟩ := hsurjective (vertex path3 1)
  have hheight := congrArg (plHeight path3 h012) hx
  rw [plHeight_graphPLPresentationMap, plHeight_vertex] at hheight
  rcases (graphPLPresentation path3 h012 S02).exists_rep S02 x with
    ⟨i, p, rfl⟩ | ⟨e, p, rfl⟩
  · rw [CylinderPresentation.height_ofVertex] at hheight
    fin_cases i <;> norm_num [S02, h012] at hheight
  · have he : e = 0 := Fin.eq_zero e
    subst e
    exact path_S02_E0_empty.false p.1

/-! ## K6. Identification lemmas -/

/-- The midpoint of the horizontal edge is different from either endpoint vertex. -/
theorem edge_mid_ne_vertex (v : Bool) :
    edgePoint edgeGraph d₀ ⟨1 / 2, by norm_num, by norm_num⟩ ≠ vertex edgeGraph v := by
  intro h
  have h' := (edgePoint_eq_vertex_iff edgeGraph).mp h
  rcases h' with ⟨ht, _⟩ | ⟨ht, _⟩
  · have ht' := congrArg (fun s : unitInterval => (s : ℝ)) ht
    norm_num at ht'
  · have ht' := congrArg (fun s : unitInterval => (s : ℝ)) ht
    norm_num at ht'

/-- The 4-cycle realization has Hausdorff topology. -/
theorem c4_t2Space : T2Space (Realization C4) := t2Space_realization C4

/-! ## K7. Consequences -/

/-- The quotient functor sends the 4-cycle graph-PL space to its graph-PL Reeb graph. -/
theorem c4_quotientRGraphFunctor_obj :
    quotientRGraphFunctor.obj (graphPLSpace C4 h4) = graphPLReebGraph C4 h4 :=
  quotientRGraphFunctor_obj_graphPLSpace C4 h4

/-- The 4-cycle/Y-tree geometric distance is the distance of their interval-component cosheaves. -/
theorem c4_Y_geometricInterleavingDistance :
    geometricInterleavingDistance (quotientRGraphFunctor.obj (graphPLSpace C4 h4))
        (quotientRGraphFunctor.obj (graphPLSpace Y hY)) =
      interleavingDistance (intervalComponents (plHeight C4 h4))
        (intervalComponents (plHeight Y hY)) := by
  rw [quotientRGraphFunctor_obj_graphPLSpace,
    quotientRGraphFunctor_obj_graphPLSpace]
  exact geometricInterleavingDistance_graphPLReebGraph C4 h4 Y hY

end

end TDA.Mapper.GraphPLConstructibleExamples
