import TDA.Mapper.UniformMapperReebData
import TDA.Mapper.GraphPLReebDataExamples
import TDA.Mapper.UniformCoverCellsExamples

/-!
# MultiNerve Mapper as finite Reeb data: fixtures

Acceptance fixtures for the member-adapted comparison in
`TDA.Mapper.UniformMapperReebData`.

* **F1.** The 4-cycle at levels `0 < 1 < 2` gives the composite cycle data; its lower
  endpoint maps retain the injective/non-injective distinction of the graph-PL data.
* **F2.** A single edge is subdivided by the regular member at level `1`; the middle
  vertex cell is the crossing edge and the two gaps each carry one edge cell.
* **F3.** The subdivided Y-tree has vertex counts `1, 2, 1, 1` and edge counts `1, 2, 1`,
  with the crossing edge `0 -- 2` at level `1`.
* **F4.** A horizontal edge in one member produces one vertex cell and no gap cells.
* **F5.** A vertex height in an overlap prevents adapted levels from covering the heights.
* **F6.** Adapted levels without vertex-height coverage need not give isomorphic finite data.
* **F7.** At the boundary `2g > r`, a cell can have three labels, so the two-summand
  exhaustion requires `2g ≤ r`.

These are finite Reeb data fixtures; no realization or 1-skeleton claim is made.
-/

namespace TDA.Mapper.UniformMapperReebDataExamples

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

noncomputable section

local notation "U₃" => uniformCover (-1 / 8 : ℝ) 1 (3 / 8) 3
local notation "U₄" => uniformCover (-1 / 2 : ℝ) (5 / 4) (1 / 4) 4

private theorem card_zero_of {α : Type*} {P : α → Prop} (hP : ∀ x, ¬ P x) :
    Nat.card {x // P x} = 0 := by
  have : IsEmpty {x // P x} := ⟨fun x => hP x.1 x.2⟩
  exact Nat.card_of_isEmpty

private theorem card_one_of {α : Type*} {P : α → Prop} {a : α} (ha : P a)
    (hP : ∀ x, P x → x = a) : Nat.card {x // P x} = 1 := by
  exact Nat.card_eq_one_iff_unique.2
    ⟨⟨fun x y => Subtype.ext ((hP x.1 x.2).trans (hP y.1 y.2).symm)⟩, ⟨⟨a, ha⟩⟩⟩

/-! ## F1. The 4-cycle -/

@[simp] private theorem S012_zero : S012.value 0 = 0 := by
  show ((0 : ℕ) : ℝ) = 0
  norm_num

@[simp] private theorem S012_one : S012.value 1 = 1 := by
  show ((1 : ℕ) : ℝ) = 1
  norm_num

@[simp] private theorem S012_two : S012.value 2 = 2 := by
  show ((2 : ℕ) : ℝ) = 2
  norm_num

/-- The list `S012` is adapted to the three-member cycle cover. -/
theorem c4_adapted : LevelsAdapted S012 (-1 / 8) 1 (3 / 8) := by
  intro k j
  fin_cases k <;> fin_cases j <;>
    norm_num [S012, uniformCover_apply, mem_uniformInterval]

/-- The Mapper data of the covered 4-cycle are isomorphic to its graph-PL finite data. -/
def c4_mapperIso :
    uniformMapperData C4 h4 (-1 / 8) 1 (3 / 8) 2 ≅ graphPLReebData C4 h4 S012 :=
  uniformMapperIso C4 h4 S012 c4_adapted c4_covers (by norm_num) (by norm_num)

/-- The cycle-data fixture is obtained by composing the Mapper comparison with `cycleIso.symm`. -/
theorem c4_mapper_cycleData :
    Nonempty (uniformMapperData C4 h4 (-1 / 8) 1 (3 / 8) 2 ≅ cycleData) :=
  ⟨c4_mapperIso.trans cycleIso.symm⟩

/-- The lower right endpoint map of the Mapper data is injective. -/
theorem c4_mapper_right_zero_injective :
    Function.Injective ((uniformMapperData C4 h4 (-1 / 8) 1 (3 / 8) 2).right 0) := by
  have hg : (0 : ℝ) < 3 / 8 := by norm_num
  have hgr : (3 / 8 : ℝ) ≤ 1 := by norm_num
  intro x y hxy
  apply (uniformMapperEdgeEquiv C4 h4 S012 c4_adapted c4_covers hg hgr 0).injective
  apply c4_right_zero_injective
  rw [← uniformMapperVertexEquiv_right C4 h4 S012 c4_adapted c4_covers hg hgr 0 x,
    ← uniformMapperVertexEquiv_right C4 h4 S012 c4_adapted c4_covers hg hgr 0 y, hxy]

/-- The Mapper has two edge cells over the lower consecutive pair, agreeing with `c4_edgeCells01`. -/
theorem c4_mapper_E0_card :
    Nat.card ((uniformMapperData C4 h4 (-1 / 8) 1 (3 / 8) 2).E 0) = 2 := by
  simpa [uniformMapperData_E] using c4_edgeCells01

/-- The lower left endpoint map of the Mapper data is not injective. -/
theorem c4_mapper_left_zero_not_injective :
    ¬ Function.Injective ((uniformMapperData C4 h4 (-1 / 8) 1 (3 / 8) 2).left 0) := by
  have hg : (0 : ℝ) < 3 / 8 := by norm_num
  have hgr : (3 / 8 : ℝ) ≤ 1 := by norm_num
  intro hinj
  apply c4_left_zero_not_injective
  intro y y' hyy
  let E := uniformMapperEdgeEquiv C4 h4 S012 c4_adapted c4_covers hg hgr 0
  let x := E.symm y
  let x' := E.symm y'
  have hxe : E x = y := by
    dsimp [x]
    exact E.apply_symm_apply y
  have hxe' : E x' = y' := by
    dsimp [x']
    exact E.apply_symm_apply y'
  have hxx :
      (uniformMapperData C4 h4 (-1 / 8) 1 (3 / 8) 2).left 0 x =
        (uniformMapperData C4 h4 (-1 / 8) 1 (3 / 8) 2).left 0 x' := by
    apply (uniformMapperVertexEquiv C4 h4 S012 c4_adapted c4_covers (Fin.castSucc 0)).injective
    have h1 := uniformMapperVertexEquiv_left C4 h4 S012 c4_adapted c4_covers hg hgr 0 x
    have h2 := uniformMapperVertexEquiv_left C4 h4 S012 c4_adapted c4_covers hg hgr 0 x'
    rw [h1, h2, hxe, hxe', hyy]
  exact hxe.symm.trans ((congrArg E (hinj hxx)).trans hxe')

/-! ## F2. The single edge and its subdivision -/

private theorem edgeGraph_edge' (e : edgeGraph.edgeSet) : e = dartEdge d₀ := by
  obtain ⟨d, rfl⟩ := exists_dartEdge_eq e
  rcases edgeGraph_dart d with rfl | rfl
  · rfl
  · exact dartEdge_symm d₀

private theorem edge_spans_S012_zero :
    EdgeSpans edgeGraph h02 (S012.value (Fin.castSucc 0)) (S012.value (Fin.succ 0))
      (dartEdge d₀) := by
  rw [edgeSpans_dartEdge_iff]
  norm_num [d₀, h02, S012]

private theorem edge_spans_S012_one :
    EdgeSpans edgeGraph h02 (S012.value (Fin.castSucc 1)) (S012.value (Fin.succ 1))
      (dartEdge d₀) := by
  rw [edgeSpans_dartEdge_iff]
  norm_num [d₀, h02, S012]

private theorem edge_S012_edgeCounts :
    Nat.card ((graphPLReebData edgeGraph h02 S012).E 0) = 1 ∧
      Nat.card ((graphPLReebData edgeGraph h02 S012).E 1) = 1 := by
  constructor
  · rw [graphPLReebData_E]
    exact card_one_of edge_spans_S012_zero fun e _ => edgeGraph_edge' e
  · rw [graphPLReebData_E]
    exact card_one_of edge_spans_S012_one fun e _ => edgeGraph_edge' e

/-- The single-edge Mapper is isomorphic to the graph-PL finite data at `S012`. -/
def edge_mapperIso :
    uniformMapperData edgeGraph h02 (-1 / 8) 1 (3 / 8) 2 ≅
      graphPLReebData edgeGraph h02 S012 :=
  uniformMapperIso edgeGraph h02 S012 c4_adapted edge_covers_S012 (by norm_num) (by norm_num)

/-- The regular middle member contributes the unique crossing vertex at level `1`. -/
theorem edge_mapper_middle
    (c : (uniformMapperData edgeGraph h02 (-1 / 8) 1 (3 / 8) 2).V 1) :
    uniformMapperVertexEquiv edgeGraph h02 S012 c4_adapted edge_covers_S012 1 c =
      Sum.inr ⟨dartEdge d₀, edge_crosses_one⟩ := by
  have hs : Subsingleton (LevelVertex edgeGraph h02 (S012.value 1)) := by
    simpa only [graphPLReebData_V] using
      (Nat.card_eq_one_iff_unique.1 edge_S012_V1.2).1
  exact hs.elim _ _

/-- The single-edge Mapper has vertex counts `1, 1, 1` and edge counts `1, 1`.

At the canonical list `S02` there is one gap; the member-adapted list `S012` inserts a
regular level and therefore subdivides it into two gaps. -/
theorem edge_mapper_counts :
    Nat.card ((uniformMapperData edgeGraph h02 (-1 / 8) 1 (3 / 8) 2).V 0) = 1 ∧
      Nat.card ((uniformMapperData edgeGraph h02 (-1 / 8) 1 (3 / 8) 2).V 1) = 1 ∧
      Nat.card ((uniformMapperData edgeGraph h02 (-1 / 8) 1 (3 / 8) 2).V 2) = 1 ∧
      Nat.card ((uniformMapperData edgeGraph h02 (-1 / 8) 1 (3 / 8) 2).E 0) = 1 ∧
      Nat.card ((uniformMapperData edgeGraph h02 (-1 / 8) 1 (3 / 8) 2).E 1) = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact (Nat.card_congr
      (uniformMapperVertexEquiv edgeGraph h02 S012 c4_adapted edge_covers_S012 0)).trans
      (by simpa [graphPLReebData_V, S02, S012] using edge_S02_counts.1)
  · exact (Nat.card_congr
      (uniformMapperVertexEquiv edgeGraph h02 S012 c4_adapted edge_covers_S012 1)).trans
      (by simpa only [graphPLReebData_V] using edge_S012_V1.2)
  · exact (Nat.card_congr
      (uniformMapperVertexEquiv edgeGraph h02 S012 c4_adapted edge_covers_S012 2)).trans
      (by simpa [graphPLReebData_V, S02, S012] using edge_S02_counts.2.1)
  · exact (Nat.card_congr
      (uniformMapperEdgeEquiv edgeGraph h02 S012 c4_adapted edge_covers_S012
        (by norm_num) (by norm_num) 0)).trans
      (by simpa only [graphPLReebData_E] using edge_S012_edgeCounts.1)
  · exact (Nat.card_congr
      (uniformMapperEdgeEquiv edgeGraph h02 S012 c4_adapted edge_covers_S012
        (by norm_num) (by norm_num) 1)).trans
      (by simpa only [graphPLReebData_E] using edge_S012_edgeCounts.2)

/-! ## F3. The subdivided Y-tree -/

/-- The list `S0123` is adapted to the four-member Y-tree cover. -/
theorem Y_adapted : LevelsAdapted S0123 (-1 / 2) (5 / 4) (1 / 4) := by
  intro k j
  fin_cases k <;> fin_cases j <;>
    norm_num [S0123, uniformCover_apply, mem_uniformInterval]

/-- The Y-tree Mapper data are isomorphic to the graph-PL finite data at `S0123`. -/
def Y_mapperIso :
    uniformMapperData Y hY (-1 / 2) (5 / 4) (1 / 4) 3 ≅
      graphPLReebData Y hY S0123 :=
  uniformMapperIso Y hY S0123 Y_adapted Y_covers (by norm_num) (by norm_num)

/-- The Y-tree Mapper vertex counts agree with `Y_vertexCounts`. -/
theorem Y_mapper_vertexCounts :
    Nat.card ((uniformMapperData Y hY (-1 / 2) (5 / 4) (1 / 4) 3).V 0) = 1 ∧
      Nat.card ((uniformMapperData Y hY (-1 / 2) (5 / 4) (1 / 4) 3).V 1) = 2 ∧
      Nat.card ((uniformMapperData Y hY (-1 / 2) (5 / 4) (1 / 4) 3).V 2) = 1 ∧
      Nat.card ((uniformMapperData Y hY (-1 / 2) (5 / 4) (1 / 4) 3).V 3) = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (Nat.card_congr (uniformMapperVertexEquiv Y hY S0123 Y_adapted Y_covers 0)).trans
      (by simpa only [graphPLReebData_V] using Y_vertexCounts.1)
  · exact (Nat.card_congr (uniformMapperVertexEquiv Y hY S0123 Y_adapted Y_covers 1)).trans
      (by simpa only [graphPLReebData_V] using Y_vertexCounts.2.1)
  · exact (Nat.card_congr (uniformMapperVertexEquiv Y hY S0123 Y_adapted Y_covers 2)).trans
      (by simpa only [graphPLReebData_V] using Y_vertexCounts.2.2.1)
  · exact (Nat.card_congr (uniformMapperVertexEquiv Y hY S0123 Y_adapted Y_covers 3)).trans
      (by simpa only [graphPLReebData_V] using Y_vertexCounts.2.2.2)

/-- The Y-tree Mapper edge counts agree with `Y_edgeCounts`. -/
theorem Y_mapper_edgeCounts :
    Nat.card ((uniformMapperData Y hY (-1 / 2) (5 / 4) (1 / 4) 3).E 0) = 1 ∧
      Nat.card ((uniformMapperData Y hY (-1 / 2) (5 / 4) (1 / 4) 3).E 1) = 2 ∧
      Nat.card ((uniformMapperData Y hY (-1 / 2) (5 / 4) (1 / 4) 3).E 2) = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · exact (Nat.card_congr
      (uniformMapperEdgeEquiv Y hY S0123 Y_adapted Y_covers (by norm_num) (by norm_num) 0)).trans
      (by simpa only [graphPLReebData_E] using Y_edgeCounts.1)
  · exact (Nat.card_congr
      (uniformMapperEdgeEquiv Y hY S0123 Y_adapted Y_covers (by norm_num) (by norm_num) 1)).trans
      (by simpa only [graphPLReebData_E] using Y_edgeCounts.2.1)
  · exact (Nat.card_congr
      (uniformMapperEdgeEquiv Y hY S0123 Y_adapted Y_covers (by norm_num) (by norm_num) 2)).trans
      (by simpa only [graphPLReebData_E] using Y_edgeCounts.2.2)

private theorem Y_y02_active :
    EdgeActive Y hY
      (uniformCover (-1 / 2) (5 / 4) (1 / 4) (3 + 1) 1) (dartEdge y02) := by
  apply edgeActive_dartEdge_of_mem
    (t := ⟨1 / 2, by norm_num, by norm_num⟩)
  rw [uniformCover_apply, mem_uniformInterval]
  norm_num [dartHeight, y02, hY, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.cons_val_succ]

/-- The vertex cell over label `1` generated by the edge `y02` is the crossing vertex. -/
theorem Y_mapper_crossing :
    uniformMapperVertexEquiv Y hY S0123 Y_adapted Y_covers 1
        ((vertexCellsCellGraphEquiv Y hY
            (uniformCover (-1 / 2) (5 / 4) (1 / 4) (3 + 1)) 1).symm
          ((cellGraph Y hY
              (uniformCover (-1 / 2) (5 / 4) (1 / 4) (3 + 1) 1)).connectedComponentMk
            (Sum.inr ⟨dartEdge y02, Y_y02_active⟩))) =
      Sum.inr ⟨dartEdge y02, Y_crosses_one⟩ := by
  have hne : ∀ v ∈ (dartEdge y02 : Sym2 (Fin 4)), hY v ≠ S0123.value 1 := by
    intro v hv
    rcases mem_dartEdge.1 hv with rfl | rfl <;> norm_num [y02]
  rw [uniformMapperVertexEquiv_cell_inr Y hY S0123 Y_adapted Y_covers 1
    ⟨dartEdge y02, Y_y02_active⟩ (fun _ => Y_crosses_one)]
  exact levelEnd_of_forall_ne Y hY _ hne

/-! ## F4. A horizontal edge in one member -/

/-- The single level `S0` is adapted to the one-member horizontal-edge cover. -/
theorem flat_adapted : LevelsAdapted S0 (-1 / 2) 3 1 := by
  intro k j
  (fin_cases k; fin_cases j)
  norm_num [S0, uniformCover_apply, mem_uniformInterval]

/-- The one-member horizontal-edge Mapper data are isomorphic to its graph-PL finite data. -/
def flat_mapperIso :
    uniformMapperData edgeGraph (fun _ => (0 : ℝ)) (-1 / 2) 3 1 0 ≅
      graphPLReebData edgeGraph (fun _ => (0 : ℝ)) S0 :=
  uniformMapperIso edgeGraph (fun _ => (0 : ℝ)) S0 flat_adapted const_covers (by norm_num)
    (by norm_num)

/-- The horizontal-edge Mapper has one vertex cell in its sole member. -/
theorem flat_mapper_count :
    Nat.card ((uniformMapperData edgeGraph (fun _ => (0 : ℝ)) (-1 / 2) 3 1 0).V 0) = 1 := by
  exact (Nat.card_congr
      (uniformMapperVertexEquiv edgeGraph (fun _ => (0 : ℝ)) S0 flat_adapted const_covers 0)).trans
    (by simpa only [graphPLReebData_V] using flatEdge_count)

/-! ## F5. A vertex height in an overlap -/

/-- No adapted list can cover the cycle heights for the cover with height `1` in an overlap. -/
theorem overlap_no_adapted :
    ¬ ∃ T : CriticalValues 2,
      LevelsAdapted T (-1 / 4) (3 / 2) (1 / 2) ∧ CoversVertexHeights T h4 := by
  rintro ⟨T, hT, hcov⟩
  exact overlap_control.2.2.1 (hT.heightSeparating hcov)

/-! ## F6. Adapted levels without coverage -/

/-- The strictly increasing list `0 < 21/20 < 2`, whose middle value is not a vertex height. -/
def T1 : CriticalValues 2 :=
  ⟨![0, 21 / 20, 2], Fin.strictMono_iff_lt_succ.2 fun i => by
    fin_cases i <;>
      norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.cons_val_succ]⟩

/-- `T1` is adapted to the three-member cycle cover. -/
theorem T1_adapted : LevelsAdapted T1 (-1 / 8) 1 (3 / 8) := by
  intro k j
  fin_cases k <;> fin_cases j <;>
    norm_num [T1, uniformCover_apply, mem_uniformInterval, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
      Matrix.cons_val_succ]

/-- `T1` does not cover the height `1` of the 4-cycle. -/
theorem T1_not_covers : ¬ CoversVertexHeights T1 h4 := by
  intro hcov
  obtain ⟨k, hk⟩ := hcov 1
  fin_cases k <;>
    norm_num [T1, h4, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.cons_val_succ] at hk

/-- The first graph-PL gap for `T1` has no spanning edge. -/
theorem T1_E0_card : Nat.card ((graphPLReebData C4 h4 T1).E 0) = 0 := by
  rw [graphPLReebData_E]
  exact card_zero_of fun e he => by
    rcases c4_edge_cases e with rfl | rfl | rfl | rfl <;>
      rw [edgeSpans_dartEdge_iff] at he <;>
      norm_num [d01, d12, d23, d03, T1, h4, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
        Matrix.cons_val_succ] at he

/-- The adapted but non-covering list `T1` cannot give data isomorphic to the Mapper data. -/
theorem T1_no_iso :
    IsEmpty (uniformMapperData C4 h4 (-1 / 8) 1 (3 / 8) 2 ≅ graphPLReebData C4 h4 T1) := by
  constructor
  intro i
  let _ : Finite ((graphPLReebData C4 h4 T1).E 0) :=
    (graphPLReebData C4 h4 T1).finiteE 0
  have hempty : IsEmpty ((graphPLReebData C4 h4 T1).E 0) :=
    (Finite.card_eq_zero_iff).1 T1_E0_card
  have hsource : Nonempty ((uniformMapperData C4 h4 (-1 / 8) 1 (3 / 8) 2).E 0) :=
    (Nat.card_pos_iff.1 (by rw [c4_mapper_E0_card]; norm_num)).1
  obtain ⟨x⟩ := hsource
  exact hempty.false (i.hom.e 0 x)

/-! ## F7. The boundary `2g > r` -/

/-- The boundary cover has a MultiNerve cell with all three labels. -/
theorem triple_cell :
    ∃ c : multiNerveMapper (plHeight pointGraph (fun _ => (0 : ℝ)))
        (fun i => (uniformCover (-3 / 2) 2 (3 / 2) 3 i : Set ℝ)),
      c.support.image Sigma.fst = {0, 1, 2} := by
  let τ : Finset (Fin 3) := {0, 1, 2}
  have hτ : τ.Nonempty := by simp [τ]
  have hv : vertex pointGraph () ∈
      (plHeight pointGraph (fun _ => (0 : ℝ))) ⁻¹'
        (⋂ i ∈ τ, (uniformCover (-3 / 2) 2 (3 / 2) 3 i : Set ℝ)) := by
    simp only [Set.mem_preimage, Set.mem_iInter, plHeight_vertex]
    intro i hi
    fin_cases i <;> norm_num [τ, uniformCover_apply, mem_uniformInterval]
  let z := ZerothHomotopy.mk
    (⟨vertex pointGraph (), hv⟩ :
      (plHeight pointGraph (fun _ => (0 : ℝ))) ⁻¹'
        (⋂ i ∈ τ, (uniformCover (-3 / 2) 2 (3 / 2) 3 i : Set ℝ)))
  let c := (cellsOverLabelsEquiv
      (plHeight pointGraph (fun _ => (0 : ℝ)))
      (fun i => (uniformCover (-3 / 2) 2 (3 / 2) 3 i : Set ℝ)) τ hτ).symm z
  exact ⟨c.1, c.2⟩

/-- A three-label boundary cell belongs to neither the vertex nor consecutive-edge summands. -/
theorem triple_cell_not_mem_summands
    {c : multiNerveMapper (plHeight pointGraph (fun _ => (0 : ℝ)))
        (fun i => (uniformCover (-3 / 2) 2 (3 / 2) 3 i : Set ℝ))}
    (hc : c.support.image Sigma.fst = {0, 1, 2}) :
    (∀ k : Fin 3, c.support.image Sigma.fst ≠ {k}) ∧
      (∀ e : Fin 2, c.support.image Sigma.fst ≠ {e.castSucc, e.succ}) := by
  constructor
  · intro k hk
    have hcard := congrArg Finset.card (hc.symm.trans hk)
    rw [show ({0, 1, 2} : Finset (Fin 3)).card = 3 by decide,
      Finset.card_singleton] at hcard
    omega
  · intro e he
    have hcard := congrArg Finset.card (hc.symm.trans he)
    rw [show ({0, 1, 2} : Finset (Fin 3)).card = 3 by decide,
      Finset.card_pair (Fin.castSucc_lt_succ (i := e)).ne] at hcard
    omega

end

end TDA.Mapper.UniformMapperReebDataExamples
