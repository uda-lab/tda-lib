import TDA.Mapper.OneSkeletonReebData
import TDA.Mapper.UniformMapperReebDataExamples
import TDA.Reeb.FiniteDataGraphExamples

/-!
# Fixtures for the Mapper one-skeleton and finite Reeb data comparison

These fixtures record the ordinary Mapper one-skeleton counts and graph comparisons for the
four-cycle, a single edge, a Y-tree, a horizontal edge, and the boundary case `2 * g > r`.
They are finite Reeb data and Mapper fixtures; no realization claim is made here.

* **M1.** The four-cycle one-skeleton is isomorphic to the four-edge cycle data.
* **M2.** A single edge subdivided by a regular member has three vertices and two edges.
* **M3.** The Y-tree has five vertices and at most four one-skeleton edges.
* **M4.** A horizontal edge has one Mapper vertex and no one-skeleton adjacency.
* **M5.** At `2 * g > r`, the Mapper one-skeleton is complete while the incidence graph has
  non-adjacent vertices at levels zero and two.
-/

namespace TDA.Mapper.OneSkeletonReebDataExamples

open Finset Set SimpleGraph CategoryTheory
open TDA.Topology TDA.Topology.MultiNerveCell
open TDA.Reeb TDA.Reeb.OpenInterval TDA.Reeb.GraphPL TDA.Reeb.GraphRealization
open TDA.Reeb.Examples.GraphPL
open TDA.Reeb.Examples.GraphRealization (edgeGraph d₀ pointGraph edgeGraph_dart)
open TDA.Mapper.GraphPL
open TDA.Mapper.GraphPLReebDataExamples
open TDA.Mapper.UniformCoverCellsExamples
open TDA.Mapper.UniformCoverExamples (d12 d03 c4_edge_cases)
open TDA.Reeb.Examples.ConstructibleCylinder (S0 S012)
open TDA.Reeb.Examples.ConstructibleRepresentation (S02)
open TDA.Reeb.RGraph.Examples (cycleData)
open TDA.Mapper.UniformMapperReebDataExamples
open TDA.Reeb.Examples.FiniteDataGraph
open scoped Classical

noncomputable section

local notation "U_C4" => fun i =>
  (uniformCover (-1 / 8 : ℝ) 1 (3 / 8) 3 i : Set ℝ)
local notation "D_C4" =>
  uniformMapperData C4 h4 (-1 / 8) 1 (3 / 8) 2
local notation "D_edge" =>
  uniformMapperData edgeGraph h02 (-1 / 8) 1 (3 / 8) 2
local notation "U_edge" => fun i =>
  (uniformCover (-1 / 8 : ℝ) 1 (3 / 8) 3 i : Set ℝ)
local notation "D_Y" =>
  uniformMapperData Y hY (-1 / 2) (5 / 4) (1 / 4) 3
local notation "U_Y" => fun i =>
  (uniformCover (-1 / 2 : ℝ) (5 / 4) (1 / 4) 4 i : Set ℝ)
local notation "D_flat" =>
  uniformMapperData edgeGraph (fun _ => (0 : ℝ)) (-1 / 2) 3 1 0
local notation "U_flat" => fun i =>
  (uniformCover (-1 / 2 : ℝ) 3 1 1 i : Set ℝ)
local notation "D_point" =>
  uniformMapperData pointGraph (fun _ => (0 : ℝ)) (-3 / 2) 2 (3 / 2) 2
local notation "U_point" => fun i =>
  (uniformCover (-3 / 2 : ℝ) 2 (3 / 2) 3 i : Set ℝ)

/-! ## M1. The four-cycle -/

/-- The ordinary Mapper one-skeleton of the covered four-cycle is isomorphic to `cycleData`. -/
theorem c4_oneSkeletonIso :
    Nonempty (mapperOneSkeleton (plHeight C4 h4) U_C4 ≃g cycleData.incidenceGraph) := by
  refine ⟨(incidenceGraphUniformMapperIso (a := -1 / 8) (r := 1) (g := 3 / 8)
    (n := 2) C4 h4 (by norm_num)).symm.trans ?_⟩
  exact TDA.Reeb.FiniteReebData.incidenceGraphIso
    (c4_mapperIso ≪≫ cycleIso.symm)

/-- The four-cycle ordinary Mapper one-skeleton has four simple-graph edges. -/
theorem c4_oneSkeleton_edgeCard :
    Nat.card (mapperOneSkeleton (plHeight C4 h4) U_C4).edgeSet = 4 := by
  calc
    Nat.card (mapperOneSkeleton (plHeight C4 h4) U_C4).edgeSet =
        Nat.card (D_C4).incidenceGraph.edgeSet :=
      (Nat.card_congr ((incidenceGraphUniformMapperIso (a := -1 / 8) (r := 1) (g := 3 / 8)
        (n := 2) C4 h4 (by norm_num)).mapEdgeSet)).symm
    _ = Nat.card cycleData.incidenceGraph.edgeSet :=
      Nat.card_congr ((TDA.Reeb.FiniteReebData.incidenceGraphIso
        (c4_mapperIso ≪≫ cycleIso.symm)).mapEdgeSet)
    _ = 4 := cycle_edgeCard

/-! ## M2. The single edge -/

/-- The subdivided single-edge Mapper one-skeleton has three vertices. -/
theorem edge_oneSkeleton_vertexCard :
    Nat.card (MapperVertex (plHeight edgeGraph h02) U_edge) = 3 := by
  calc
    Nat.card (MapperVertex (plHeight edgeGraph h02) U_edge) =
        Nat.card (D_edge).IncidenceVertex :=
      (Nat.card_congr ((incidenceGraphUniformMapperIso (a := -1 / 8) (r := 1) (g := 3 / 8)
        (n := 2) edgeGraph h02 (by norm_num)).toEquiv)).symm
    _ = ∑ k, Nat.card ((D_edge).V k) := by
      change Nat.card (Σ k : Fin 3, (D_edge).V k) = _
      exact Nat.card_sigma
    _ = 3 := by
      rw [Fin.sum_univ_three]
      rw [edge_mapper_counts.1, edge_mapper_counts.2.1, edge_mapper_counts.2.2.1]

/-- Every edge type of the subdivided single-edge data is a singleton. -/
private theorem edge_data_subsingleton (e : Fin 2) :
    Subsingleton ((D_edge).E e) := by
  fin_cases e
  · exact (Nat.card_eq_one_iff_unique.1 edge_mapper_counts.2.2.2.1).1
  · exact (Nat.card_eq_one_iff_unique.1 edge_mapper_counts.2.2.2.2).1

/-- The subdivided single-edge Mapper one-skeleton has two simple-graph edges. -/
theorem edge_oneSkeleton_edgeCard :
    Nat.card (mapperOneSkeleton (plHeight edgeGraph h02) U_edge).edgeSet = 2 := by
  have hinj : Function.Injective (D_edge).incidenceEdgeSet := by
    rw [(D_edge).incidenceEdgeSet_injective_iff]
    intro e x y _ _
    exact (edge_data_subsingleton e).elim x y
  calc
    Nat.card (mapperOneSkeleton (plHeight edgeGraph h02) U_edge).edgeSet =
        Nat.card (D_edge).incidenceGraph.edgeSet :=
      (Nat.card_congr ((incidenceGraphUniformMapperIso (a := -1 / 8) (r := 1) (g := 3 / 8)
        (n := 2) edgeGraph h02 (by norm_num)).mapEdgeSet)).symm
    _ = ∑ e, Nat.card ((D_edge).E e) := (D_edge).card_incidenceGraph_edgeSet_eq hinj
    _ = 2 := by
      rw [Fin.sum_univ_two]
      rw [edge_mapper_counts.2.2.2.1, edge_mapper_counts.2.2.2.2]

/-! ## M3. The Y-tree -/

/-- The subdivided Y-tree ordinary Mapper one-skeleton has five vertices. -/
theorem Y_oneSkeleton_vertexCard :
    Nat.card (MapperVertex (plHeight Y hY) U_Y) = 5 := by
  calc
    Nat.card (MapperVertex (plHeight Y hY) U_Y) = Nat.card (D_Y).IncidenceVertex :=
      (Nat.card_congr ((incidenceGraphUniformMapperIso (a := -1 / 2) (r := 5 / 4) (g := 1 / 4)
        (n := 3) Y hY (by norm_num)).toEquiv)).symm
    _ = ∑ k, Nat.card ((D_Y).V k) := by
      change Nat.card (Σ k : Fin 4, (D_Y).V k) = _
      exact Nat.card_sigma
    _ = 5 := by
      rw [Fin.sum_univ_four]
      rw [Y_mapper_vertexCounts.1, Y_mapper_vertexCounts.2.1,
        Y_mapper_vertexCounts.2.2.1, Y_mapper_vertexCounts.2.2.2]

/-- The subdivided Y-tree ordinary Mapper one-skeleton has at most four edges. -/
theorem Y_oneSkeleton_edgeCard_le :
    Nat.card (mapperOneSkeleton (plHeight Y hY) U_Y).edgeSet ≤ 4 := by
  calc
    Nat.card (mapperOneSkeleton (plHeight Y hY) U_Y).edgeSet ≤
        ∑ e, Nat.card ((D_Y).E e) :=
      card_mapperOneSkeleton_edgeSet_le Y hY (by norm_num)
    _ = 4 := by
      rw [Fin.sum_univ_three]
      rw [Y_mapper_edgeCounts.1, Y_mapper_edgeCounts.2.1, Y_mapper_edgeCounts.2.2]

/-! ## M4. A horizontal edge -/

/-- The horizontal-edge ordinary Mapper one-skeleton has one vertex. -/
theorem flat_oneSkeleton_vertexCard :
    Nat.card (MapperVertex (plHeight edgeGraph (fun _ => (0 : ℝ))) U_flat) = 1 := by
  calc
    Nat.card (MapperVertex (plHeight edgeGraph (fun _ => (0 : ℝ))) U_flat) =
        Nat.card (D_flat).IncidenceVertex :=
      (Nat.card_congr ((incidenceGraphUniformMapperIso (a := -1 / 2) (r := 3) (g := 1)
        (n := 0) edgeGraph (fun _ => (0 : ℝ)) (by norm_num)).toEquiv)).symm
    _ = ∑ k, Nat.card ((D_flat).V k) := by
      change Nat.card (Σ k : Fin 1, (D_flat).V k) = _
      exact Nat.card_sigma
    _ = 1 := by
      simp only [Fin.sum_univ_succ, flat_mapper_count]
      norm_num

/-- No two vertices of the horizontal-edge ordinary Mapper one-skeleton are adjacent. -/
theorem flat_oneSkeleton_not_adj :
    ∀ a b : MapperVertex (plHeight edgeGraph (fun _ => (0 : ℝ))) U_flat,
      ¬(mapperOneSkeleton (plHeight edgeGraph (fun _ => (0 : ℝ))) U_flat).Adj a b := by
  intro a b hab
  let φ := incidenceGraphUniformMapperIso (a := -1 / 2) (r := 3) (g := 1) (n := 0)
    edgeGraph (fun _ => (0 : ℝ)) (by norm_num)
  have hD : (D_flat).incidenceGraph.Adj (φ.symm a) (φ.symm b) :=
    (φ.symm.map_adj_iff).mpr hab
  rcases (D_flat).incidenceGraph_adj_level hD with h | h
  · have h' := h
    have ha : (φ.symm a).1 = (0 : Fin 1) := Fin.eq_zero _
    have hb : (φ.symm b).1 = (0 : Fin 1) := Fin.eq_zero _
    rw [ha, hb] at h'
    norm_num at h'
  · have h' := h
    have ha : (φ.symm a).1 = (0 : Fin 1) := Fin.eq_zero _
    have hb : (φ.symm b).1 = (0 : Fin 1) := Fin.eq_zero _
    rw [ha, hb] at h'
    norm_num at h'

/-! ## M5. The boundary `2 * g > r` -/

/-- The boundary parameters satisfy `2 * g > r`. -/
theorem point_boundary : 2 * (3 / 2 : ℝ) > (2 : ℝ) := by
  norm_num

/-- The boundary Mapper one-skeleton has three vertices, one per cover member. -/
theorem point_oneSkeleton_vertexCard :
    Nat.card (MapperVertex (plHeight pointGraph (fun _ => (0 : ℝ))) U_point) = 3 := by
  have point_mem (k : Fin 3) :
      plHeight pointGraph (fun _ => (0 : ℝ)) (vertex pointGraph ()) ∈ U_point k := by
    rw [plHeight_vertex]
    fin_cases k <;> norm_num [uniformCover_apply, mem_uniformInterval]
  have hsub (k : Fin 3) :
      Subsingleton (ZerothHomotopy
        (PullbackSpace (plHeight pointGraph (fun _ => (0 : ℝ))) U_point k)) := by
    constructor
    intro c d
    obtain ⟨x, rfl⟩ := ZerothHomotopy.mk_surjective c
    obtain ⟨y, rfl⟩ := ZerothHomotopy.mk_surjective d
    have hxy : x = y := Subtype.ext (Subsingleton.elim _ _)
    subst y
    rfl
  have hnonempty (k : Fin 3) :
      Nonempty (ZerothHomotopy
        (PullbackSpace (plHeight pointGraph (fun _ => (0 : ℝ))) U_point k)) :=
    ⟨ZerothHomotopy.mk
      (⟨vertex pointGraph (), point_mem k⟩ :
        PullbackSpace (plHeight pointGraph (fun _ => (0 : ℝ))) U_point k)⟩
  have hcard (k : Fin 3) :
      Nat.card (ZerothHomotopy
        (PullbackSpace (plHeight pointGraph (fun _ => (0 : ℝ))) U_point k)) = 1 :=
    Nat.card_eq_one_iff_unique.2 ⟨hsub k, hnonempty k⟩
  let e : ComponentIndex (plHeight pointGraph (fun _ => (0 : ℝ))) U_point ≃
      MapperVertex (plHeight pointGraph (fun _ => (0 : ℝ))) U_point :=
    { toFun := toMapperVertex (plHeight pointGraph (fun _ => (0 : ℝ))) U_point
      invFun := fun z => z.1
      left_inv := fun z => rfl
      right_inv := fun z => Subtype.ext rfl }
  calc
    Nat.card (MapperVertex (plHeight pointGraph (fun _ => (0 : ℝ))) U_point) =
        Nat.card (ComponentIndex (plHeight pointGraph (fun _ => (0 : ℝ))) U_point) :=
      (Nat.card_congr e).symm
    _ = ∑ k : Fin 3, Nat.card (ZerothHomotopy
        (PullbackSpace (plHeight pointGraph (fun _ => (0 : ℝ))) U_point k)) := by
      change Nat.card (Σ k : Fin 3, ZerothHomotopy
        (PullbackSpace (plHeight pointGraph (fun _ => (0 : ℝ))) U_point k)) = _
      let : ∀ k : Fin 3, Finite (ZerothHomotopy
          (PullbackSpace (plHeight pointGraph (fun _ => (0 : ℝ))) U_point k)) :=
        fun k => @Finite.of_subsingleton _ (hsub k)
      exact Nat.card_sigma
    _ = 3 := by
      rw [Fin.sum_univ_three, hcard 0, hcard 1, hcard 2]

/-- The Mapper one-skeleton of the boundary point cover is complete. -/
theorem point_oneSkeleton_complete
    {a b : MapperVertex (plHeight pointGraph (fun _ => (0 : ℝ))) U_point}
    (hab : a ≠ b) :
    (mapperOneSkeleton (plHeight pointGraph (fun _ => (0 : ℝ))) U_point).Adj a b := by
  apply (mapperOneSkeleton_adj_iff (plHeight pointGraph (fun _ => (0 : ℝ))) U_point a b).2
  refine ⟨hab, ?_⟩
  apply (mem_mapper_iff (plHeight pointGraph (fun _ => (0 : ℝ))) U_point
    {a.1, b.1}).2
  refine ⟨Finset.insert_nonempty _ _, ?_⟩
  obtain ⟨x, hx⟩ := componentCover_nonempty
    (plHeight pointGraph (fun _ => (0 : ℝ))) U_point a.1
  refine ⟨x, ?_⟩
  intro z hz
  rcases Finset.mem_insert.1 hz with rfl | hz
  · exact hx
  · obtain rfl := Finset.mem_singleton.1 hz
    obtain ⟨y, hy⟩ := componentCover_nonempty
      (plHeight pointGraph (fun _ => (0 : ℝ))) U_point b.1
    exact (Subsingleton.elim x y).symm ▸ hy

private theorem point_cover_mem (k : Fin 3) :
    plHeight pointGraph (fun _ => (0 : ℝ)) (vertex pointGraph ()) ∈ U_point k := by
  rw [plHeight_vertex]
  fin_cases k <;> norm_num [uniformCover_apply, mem_uniformInterval]

private def point_vertex (k : Fin 3) : (D_point).V k :=
  (vertexCellsEquiv (plHeight pointGraph (fun _ => (0 : ℝ))) U_point k).symm
    (ZerothHomotopy.mk
      (⟨vertex pointGraph (), point_cover_mem k⟩ :
        plHeight pointGraph (fun _ => (0 : ℝ)) ⁻¹' U_point k))

/-- The boundary incidence graph has non-adjacent vertices at levels zero and two. -/
theorem point_incidence_not_adj :
    ¬(D_point).incidenceGraph.Adj
      (⟨0, point_vertex 0⟩ : (D_point).IncidenceVertex) ⟨2, point_vertex 2⟩ := by
  intro h
  rcases (D_point).incidenceGraph_adj_level h with h | h
  · change ((0 : Fin 3) : ℕ) + 1 = ((2 : Fin 3) : ℕ) at h
    norm_num at h
  · change ((2 : Fin 3) : ℕ) + 1 = ((0 : Fin 3) : ℕ) at h
    norm_num at h

/-- No graph isomorphism identifies the boundary incidence graph with its Mapper one-skeleton. -/
theorem point_no_oneSkeletonIso :
    IsEmpty ((D_point).incidenceGraph ≃g
      mapperOneSkeleton (plHeight pointGraph (fun _ => (0 : ℝ))) U_point) := by
  constructor
  intro φ
  let x : (D_point).IncidenceVertex := ⟨0, point_vertex 0⟩
  let y : (D_point).IncidenceVertex := ⟨2, point_vertex 2⟩
  have hxy : x ≠ y := by
    intro h
    have h' := congrArg (fun z : (D_point).IncidenceVertex => z.1) h
    change (0 : Fin 3) = 2 at h'
    exact absurd h' (by decide)
  have hφxy : φ x ≠ φ y := by
    intro h
    exact hxy (φ.injective h)
  have hm :
      (mapperOneSkeleton (plHeight pointGraph (fun _ => (0 : ℝ))) U_point).Adj
        (φ x) (φ y) :=
    point_oneSkeleton_complete hφxy
  have hd : (D_point).incidenceGraph.Adj x y := (φ.map_adj_iff).mp hm
  exact point_incidence_not_adj hd

end

end TDA.Mapper.OneSkeletonReebDataExamples
