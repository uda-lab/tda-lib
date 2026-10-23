import TDA.Mapper.GraphPLRefinement
import TDA.Mapper.UniformMapperReebDataExamples
import TDA.Mapper.UniformCoverCellsExamples

/-!
# Refinement of graph-PL finite Reeb data: fixtures

Acceptance fixtures for `TDA.Mapper.GraphPLRefinement`:

* **R1.** A single edge with an inserted midpoint has one crossing finite Reeb vertex and two
  copies of its spanning edge.
* **R2.** Inserting `1/2` into the lower gap of the 4-cycle duplicates the lower edge data.
* **R3.** Inserting `3/2` into the middle gap of the Y-tree duplicates its two spanning edges.
* **R4.** Refinement by the same critical list is the empty-insertion comparison.
* **R5.** Levels and gaps exterior to the old extreme segment are empty.
* **R6.** A list containing an uncovered vertex height is not this refinement.
* **R7.** Refinement is transitive, and the adapted Mapper comparison composes with it.

These are finite Reeb data fixtures; R7 also records the stated realization comparison, and no
1-skeleton claim is made.
-/

namespace TDA.Mapper.GraphPLRefinementExamples

open Finset Set SimpleGraph CategoryTheory
open TDA.Topology TDA.Topology.MultiNerveCell
open TDA.Reeb TDA.Reeb.OpenInterval TDA.Reeb.GraphPL TDA.Reeb.GraphRealization
open TDA.Reeb.Examples.GraphPL
open TDA.Reeb.Examples.GraphRealization (edgeGraph d₀ pointGraph path3)
open TDA.Mapper.GraphPL
open TDA.Mapper.GraphPLReebDataExamples
open TDA.Mapper.UniformCoverCellsExamples (Y hY)
open TDA.Mapper.UniformMapperReebDataExamples (edge_mapperIso)
open TDA.Reeb.Examples.ConstructibleCylinder (S0 S012)
open TDA.Reeb.Examples.ConstructibleRepresentation (S02 S02_refines)

noncomputable section

/-- The critical list with values `0, 1/2, 1, 2`. -/
def S0h12 : CriticalValues 3 where
  value := ![0, 1 / 2, 1, 2]
  strictMono := Fin.strictMono_iff_lt_succ.2 fun i => by
    fin_cases i <;> norm_num [Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.cons_val_succ]

@[simp] private theorem S0h12_zero : S0h12.value 0 = 0 := by
  rfl

@[simp] private theorem S0h12_one : S0h12.value 1 = 1 / 2 := by
  rfl

@[simp] private theorem S0h12_two : S0h12.value 2 = 1 := by
  rfl

@[simp] private theorem S0h12_three : S0h12.value 3 = 2 := by
  rfl

@[simp] private theorem S0h12_castSucc_zero : S0h12.value (Fin.castSucc 0) = 0 := by
  rfl

@[simp] private theorem S0h12_succ_zero : S0h12.value (Fin.succ 0) = 1 / 2 := by
  rfl

@[simp] private theorem S0h12_castSucc_one : S0h12.value (Fin.castSucc 1) = 1 / 2 := by
  rfl

@[simp] private theorem S0h12_succ_one : S0h12.value (Fin.succ 1) = 1 := by
  rfl

@[simp] private theorem S0h12_castSucc_two : S0h12.value (Fin.castSucc 2) = 1 := by
  rfl

@[simp] private theorem S0h12_succ_two : S0h12.value (Fin.succ 2) = 2 := by
  rfl

/-- The critical list with values `0, 1, 3/2, 2, 3`. -/
def S01h23 : CriticalValues 4 where
  value := ![0, 1, 3 / 2, 2, 3]
  strictMono := Fin.strictMono_iff_lt_succ.2 fun i => by
    fin_cases i <;> norm_num [Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.cons_val_succ]

@[simp] private theorem S01h23_zero : S01h23.value 0 = 0 := by
  rfl

@[simp] private theorem S01h23_one : S01h23.value 1 = 1 := by
  rfl

@[simp] private theorem S01h23_two : S01h23.value 2 = 3 / 2 := by
  rfl

@[simp] private theorem S01h23_three : S01h23.value 3 = 2 := by
  rfl

@[simp] private theorem S01h23_four : S01h23.value 4 = 3 := by
  rfl

@[simp] private theorem S01h23_castSucc_one : S01h23.value (Fin.castSucc 1) = 1 := by
  rfl

@[simp] private theorem S01h23_succ_one : S01h23.value (Fin.succ 1) = 3 / 2 := by
  rfl

@[simp] private theorem S01h23_castSucc_two : S01h23.value (Fin.castSucc 2) = 3 / 2 := by
  rfl

@[simp] private theorem S01h23_succ_two : S01h23.value (Fin.succ 2) = 2 := by
  rfl

@[simp] private theorem S02_zero_local : S02.value 0 = 0 := by
  show 2 * ((0 : ℕ) : ℝ) = 0
  norm_num

@[simp] private theorem S02_one_local : S02.value 1 = 2 := by
  show 2 * ((1 : ℕ) : ℝ) = 2
  norm_num

@[simp] private theorem S02_last_local : S02.value (Fin.last 1) = 2 := by
  show 2 * ((1 : ℕ) : ℝ) = 2
  norm_num

@[simp] private theorem S02_castSucc_zero_local :
    S02.value (Fin.castSucc 0) = 0 := by
  show 2 * ((0 : ℕ) : ℝ) = 0
  norm_num

@[simp] private theorem S02_succ_zero_local : S02.value (Fin.succ 0) = 2 := by
  show 2 * ((1 : ℕ) : ℝ) = 2
  norm_num

@[simp] private theorem S012_zero_local : S012.value 0 = 0 := by
  show ((0 : ℕ) : ℝ) = 0
  norm_num

@[simp] private theorem S012_one_local : S012.value 1 = 1 := by
  show ((1 : ℕ) : ℝ) = 1
  norm_num

@[simp] private theorem S012_two_local : S012.value 2 = 2 := by
  show ((2 : ℕ) : ℝ) = 2
  norm_num

@[simp] private theorem S012_castSucc_zero_local :
    S012.value (Fin.castSucc 0) = 0 := by
  show ((0 : ℕ) : ℝ) = 0
  norm_num

@[simp] private theorem S012_succ_zero_local : S012.value (Fin.succ 0) = 1 := by
  show ((1 : ℕ) : ℝ) = 1
  norm_num

@[simp] private theorem S012_castSucc_one_local :
    S012.value (Fin.castSucc 1) = 1 := by
  show ((1 : ℕ) : ℝ) = 1
  norm_num

@[simp] private theorem S012_succ_one_local : S012.value (Fin.succ 1) = 2 := by
  show ((2 : ℕ) : ℝ) = 2
  norm_num

@[simp] private theorem S0123_zero_local : S0123.value 0 = 0 := by
  show ((0 : ℕ) : ℝ) = 0
  norm_num

@[simp] private theorem S0123_one_local : S0123.value 1 = 1 := by
  show ((1 : ℕ) : ℝ) = 1
  norm_num

@[simp] private theorem S0123_two_local : S0123.value 2 = 2 := by
  show ((2 : ℕ) : ℝ) = 2
  norm_num

@[simp] private theorem S0123_three_local : S0123.value 3 = 3 := by
  show ((3 : ℕ) : ℝ) = 3
  norm_num

@[simp] private theorem S0123_castSucc_one_local :
    S0123.value (Fin.castSucc 1) = 1 := by
  show ((1 : ℕ) : ℝ) = 1
  norm_num

@[simp] private theorem S0123_succ_one_local : S0123.value (Fin.succ 1) = 2 := by
  show ((2 : ℕ) : ℝ) = 2
  norm_num

@[simp] private theorem S0123_castSucc_two_local :
    S0123.value (Fin.castSucc 2) = 2 := by
  show ((2 : ℕ) : ℝ) = 2
  norm_num

@[simp] private theorem S0123_succ_two_local :
    S0123.value (Fin.succ 2) = 3 := by
  show ((3 : ℕ) : ℝ) = 3
  norm_num

private theorem refine_old_v_card {V : Type*} [Finite V] (G : SimpleGraph V) (h : V → ℝ)
    {n m : ℕ} {S : CriticalValues n} {T : CriticalValues m}
    (hST : Set.range S.value ⊆ Set.range T.value)
    (j : Fin (m + 1)) (i : Fin (n + 1)) (hi : T.value j = S.value i) :
    Nat.card ((RGraph.refineData hST (graphPLReebData G h S)).V j) =
      Nat.card ((graphPLReebData G h S).V i) :=
  Nat.card_congr (RGraph.refineVEquivOld hST (graphPLReebData G h S) j i hi)

private theorem refine_gap_v_card {V : Type*} [Finite V] (G : SimpleGraph V) (h : V → ℝ)
    {n m : ℕ} {S : CriticalValues n} {T : CriticalValues m}
    (hST : Set.range S.value ⊆ Set.range T.value)
    (j : Fin (m + 1)) (e : Fin n) (he : T.value j ∈ (S.K e : Set ℝ)) :
    Nat.card ((RGraph.refineData hST (graphPLReebData G h S)).V j) =
      Nat.card ((graphPLReebData G h S).E e) :=
  Nat.card_congr (RGraph.refineVEquiv hST (graphPLReebData G h S) j e he)

private theorem refine_gap_e_card {V : Type*} [Finite V] (G : SimpleGraph V) (h : V → ℝ)
    {n m : ℕ} {S : CriticalValues n} {T : CriticalValues m}
    (hST : Set.range S.value ⊆ Set.range T.value)
    (k : Fin m) (e : Fin n) (he : (RGraph.basePt T k : ℝ) ∈ (S.K e : Set ℝ)) :
    Nat.card ((RGraph.refineData hST (graphPLReebData G h S)).E k) =
      Nat.card ((graphPLReebData G h S).E e) :=
  Nat.card_congr (RGraph.refineEEquiv hST (graphPLReebData G h S) k e he)

private theorem basePt_S012_zero_mem_S02 :
    (RGraph.basePt S012 0 : ℝ) ∈ (S02.K 0 : Set ℝ) := by
  have hb := (RGraph.basePt S012 0).property
  change S012.value (Fin.castSucc 0) < (RGraph.basePt S012 0 : ℝ) ∧
    (RGraph.basePt S012 0 : ℝ) < S012.value (Fin.succ 0) at hb
  change S02.value (Fin.castSucc 0) < (RGraph.basePt S012 0 : ℝ) ∧
    (RGraph.basePt S012 0 : ℝ) < S02.value (Fin.succ 0)
  simp only [S012_castSucc_zero_local, S012_succ_zero_local,
    S02_castSucc_zero_local, S02_succ_zero_local] at hb ⊢
  exact ⟨hb.1, by linarith [hb.2]⟩

private theorem basePt_S012_one_mem_S02 :
    (RGraph.basePt S012 1 : ℝ) ∈ (S02.K 0 : Set ℝ) := by
  have hb := (RGraph.basePt S012 1).property
  change S012.value (Fin.castSucc 1) < (RGraph.basePt S012 1 : ℝ) ∧
    (RGraph.basePt S012 1 : ℝ) < S012.value (Fin.succ 1) at hb
  change S02.value (Fin.castSucc 0) < (RGraph.basePt S012 1 : ℝ) ∧
    (RGraph.basePt S012 1 : ℝ) < S02.value (Fin.succ 0)
  simp only [S012_castSucc_one_local, S012_succ_one_local,
    S02_castSucc_zero_local, S02_succ_zero_local] at hb ⊢
  exact ⟨by linarith [hb.1], by linarith [hb.2]⟩

private theorem S012_one_mem_S02_K0 : S012.value 1 ∈ (S02.K 0 : Set ℝ) := by
  change S02.value (Fin.castSucc 0) < S012.value 1 ∧
    S012.value 1 < S02.value (Fin.succ 0)
  simp only [S02_castSucc_zero_local, S012_one_local, S02_succ_zero_local]
  norm_num

private theorem basePt_S0h12_zero_mem_S012 :
    (RGraph.basePt S0h12 0 : ℝ) ∈ (S012.K 0 : Set ℝ) := by
  have hb := (RGraph.basePt S0h12 0).property
  change S0h12.value (Fin.castSucc 0) < (RGraph.basePt S0h12 0 : ℝ) ∧
    (RGraph.basePt S0h12 0 : ℝ) < S0h12.value (Fin.succ 0) at hb
  change S012.value (Fin.castSucc 0) < (RGraph.basePt S0h12 0 : ℝ) ∧
    (RGraph.basePt S0h12 0 : ℝ) < S012.value (Fin.succ 0)
  simp only [S0h12_castSucc_zero, S0h12_succ_zero, S012_castSucc_zero_local,
    S012_succ_zero_local] at hb ⊢
  exact ⟨hb.1, by linarith [hb.2]⟩

private theorem basePt_S0h12_one_mem_S012 :
    (RGraph.basePt S0h12 1 : ℝ) ∈ (S012.K 0 : Set ℝ) := by
  have hb := (RGraph.basePt S0h12 1).property
  change S0h12.value (Fin.castSucc 1) < (RGraph.basePt S0h12 1 : ℝ) ∧
    (RGraph.basePt S0h12 1 : ℝ) < S0h12.value (Fin.succ 1) at hb
  change S012.value (Fin.castSucc 0) < (RGraph.basePt S0h12 1 : ℝ) ∧
    (RGraph.basePt S0h12 1 : ℝ) < S012.value (Fin.succ 0)
  simp only [S0h12_castSucc_one, S0h12_succ_one, S012_castSucc_zero_local,
    S012_succ_zero_local] at hb ⊢
  exact ⟨by linarith [hb.1], hb.2⟩

private theorem basePt_S0h12_two_mem_S012 :
    (RGraph.basePt S0h12 2 : ℝ) ∈ (S012.K 1 : Set ℝ) := by
  have hb := (RGraph.basePt S0h12 2).property
  change S0h12.value (Fin.castSucc 2) < (RGraph.basePt S0h12 2 : ℝ) ∧
    (RGraph.basePt S0h12 2 : ℝ) < S0h12.value (Fin.succ 2) at hb
  change S012.value (Fin.castSucc 1) < (RGraph.basePt S0h12 2 : ℝ) ∧
    (RGraph.basePt S0h12 2 : ℝ) < S012.value (Fin.succ 1)
  simp only [S0h12_castSucc_two, S0h12_succ_two, S012_castSucc_one_local,
    S012_succ_one_local] at hb ⊢
  exact hb

private theorem basePt_S01h23_one_mem_S0123 :
    (RGraph.basePt S01h23 1 : ℝ) ∈ (S0123.K 1 : Set ℝ) := by
  have hb := (RGraph.basePt S01h23 1).property
  change S01h23.value (Fin.castSucc 1) < (RGraph.basePt S01h23 1 : ℝ) ∧
    (RGraph.basePt S01h23 1 : ℝ) < S01h23.value (Fin.succ 1) at hb
  change S0123.value (Fin.castSucc 1) < (RGraph.basePt S01h23 1 : ℝ) ∧
    (RGraph.basePt S01h23 1 : ℝ) < S0123.value (Fin.succ 1)
  simp only [S01h23_castSucc_one, S01h23_succ_one, S0123_castSucc_one_local,
    S0123_succ_one_local] at hb ⊢
  exact ⟨hb.1, by linarith [hb.2]⟩

private theorem basePt_S01h23_two_mem_S0123 :
    (RGraph.basePt S01h23 2 : ℝ) ∈ (S0123.K 1 : Set ℝ) := by
  have hb := (RGraph.basePt S01h23 2).property
  change S01h23.value (Fin.castSucc 2) < (RGraph.basePt S01h23 2 : ℝ) ∧
    (RGraph.basePt S01h23 2 : ℝ) < S01h23.value (Fin.succ 2) at hb
  change S0123.value (Fin.castSucc 1) < (RGraph.basePt S01h23 2 : ℝ) ∧
    (RGraph.basePt S01h23 2 : ℝ) < S0123.value (Fin.succ 1)
  simp only [S01h23_castSucc_two, S01h23_succ_two, S0123_castSucc_one_local,
    S0123_succ_one_local] at hb ⊢
  exact ⟨by linarith [hb.1], by linarith [hb.2]⟩

private theorem S0h12_one_mem_S012_K0 :
    S0h12.value 1 ∈ (S012.K 0 : Set ℝ) := by
  change S012.value (Fin.castSucc 0) < S0h12.value 1 ∧
    S0h12.value 1 < S012.value (Fin.succ 0)
  simp only [S012_castSucc_zero_local, S0h12_one, S012_succ_zero_local]
  norm_num

private theorem S01h23_two_mem_S0123_K1 :
    S01h23.value 2 ∈ (S0123.K 1 : Set ℝ) := by
  change S0123.value (Fin.castSucc 1) < S01h23.value 2 ∧
    S01h23.value 2 < S0123.value (Fin.succ 1)
  simp only [S0123_castSucc_one_local, S01h23_two, S0123_succ_one_local]
  norm_num

/-! ## R1. Single edge, inserted midpoint -/

/-- The levels `S02` occur in `S012`. -/
theorem S02_sub_S012 : Set.range S02.value ⊆ Set.range S012.value := S02_refines

private theorem edge_spans_S02 :
    EdgeSpans edgeGraph h02 (S02.value (Fin.castSucc 0))
      (S02.value (Fin.succ 0)) (dartEdge d₀) := by
  rw [edgeSpans_dartEdge_iff]
  norm_num [d₀, h02, S02_castSucc_zero_local, S02_succ_zero_local]

/-- The single-edge graph-PL refinement isomorphism. -/
def edge_refineIso :
    graphPLReebData edgeGraph h02 S012 ≅
      RGraph.refineData S02_sub_S012 (graphPLReebData edgeGraph h02 S02) :=
  graphPLRefineIso edgeGraph h02 edge_covers_S02 S02_sub_S012

/-- The inserted midpoint is the crossing-edge vertex. -/
theorem edge_refine_middle :
    edge_refineIso.hom.v 1 (Sum.inr ⟨dartEdge d₀, edge_crosses_one⟩) =
      (RGraph.refineVEquiv S02_sub_S012 _ 1 0 S012_one_mem_S02_K0).symm
        (⟨dartEdge d₀, edge_spans_S02⟩ :
          SpanEdge edgeGraph h02 (S02.value (Fin.castSucc 0))
            (S02.value (Fin.succ 0))) := by
  change (graphPLRefineHom edgeGraph h02 edge_covers_S02 S02_sub_S012).v 1 _ = _
  refine (graphPLRefineHom_v_inserted edgeGraph h02 edge_covers_S02 S02_sub_S012
    1 0 S012_one_mem_S02_K0 _).trans ?_
  rw [levelVertexEquivSpanOfMemK_inr]

/-- The refined single-edge data have vertex counts `1, 1, 1` and edge counts `1, 1`. -/
theorem edge_refine_counts :
    Nat.card ((RGraph.refineData S02_sub_S012
        (graphPLReebData edgeGraph h02 S02)).V 0) = 1 ∧
      Nat.card ((RGraph.refineData S02_sub_S012
        (graphPLReebData edgeGraph h02 S02)).V 1) = 1 ∧
      Nat.card ((RGraph.refineData S02_sub_S012
        (graphPLReebData edgeGraph h02 S02)).V 2) = 1 ∧
      Nat.card ((RGraph.refineData S02_sub_S012
        (graphPLReebData edgeGraph h02 S02)).E 0) = 1 ∧
      Nat.card ((RGraph.refineData S02_sub_S012
        (graphPLReebData edgeGraph h02 S02)).E 1) = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact (refine_old_v_card edgeGraph h02 S02_sub_S012 0 0
      (by simp only [S02_zero_local, S012_zero_local])).trans edge_S02_counts.1
  · exact (refine_gap_v_card edgeGraph h02 S02_sub_S012 1 0 S012_one_mem_S02_K0).trans
      edge_S02_counts.2.2
  · exact (refine_old_v_card edgeGraph h02 S02_sub_S012 2 1
      (by simp only [S02_one_local, S012_two_local])).trans edge_S02_counts.2.1
  · exact (refine_gap_e_card edgeGraph h02 S02_sub_S012 0 0 basePt_S012_zero_mem_S02).trans
      edge_S02_counts.2.2
  · exact (refine_gap_e_card edgeGraph h02 S02_sub_S012 1 0 basePt_S012_one_mem_S02).trans
      edge_S02_counts.2.2

/-! ## R2. C4 with a lower-gap insertion -/

/-- `S012` is refined by `S0h12`. -/
theorem S012_sub_S0h12 : Set.range S012.value ⊆ Set.range S0h12.value := by
  rintro _ ⟨i, rfl⟩
  fin_cases i
  · exact ⟨0, S0h12_zero.trans S012_zero_local.symm⟩
  · exact ⟨2, S0h12_two.trans S012_one_local.symm⟩
  · exact ⟨3, S0h12_three.trans S012_two_local.symm⟩

private theorem S02_sub_S0h12 : Set.range S02.value ⊆ Set.range S0h12.value :=
  S02_sub_S012.trans S012_sub_S0h12

/-- The 4-cycle refinement isomorphism after inserting `1/2`. -/
def c4_refineIso :
    graphPLReebData C4 h4 S0h12 ≅
      RGraph.refineData S012_sub_S0h12 (graphPLReebData C4 h4 S012) :=
  graphPLRefineIso C4 h4 c4_covers S012_sub_S0h12

/-- The inserted 4-cycle level carries the two lower-gap crossing edges; its level graph is empty,
and the corresponding inserted-list fiber has cardinality `2`; the vertex counts are
`1, 2, 2, 1`, and the two refined lower gaps have cardinality `2`. -/
theorem c4_refine_counts :
    Nat.card ((RGraph.refineData S012_sub_S0h12
        (graphPLReebData C4 h4 S012)).V 1) = 2 ∧
      Nat.card ((RGraph.refineData S012_sub_S0h12
        (graphPLReebData C4 h4 S012)).E 0) = 2 ∧
      Nat.card ((RGraph.refineData S012_sub_S0h12
        (graphPLReebData C4 h4 S012)).E 1) = 2 ∧
      Nat.card ((RGraph.refineData S012_sub_S0h12
        (graphPLReebData C4 h4 S012)).V 0) = 1 ∧
      Nat.card ((RGraph.refineData S012_sub_S0h12
        (graphPLReebData C4 h4 S012)).V 2) = 2 ∧
      Nat.card ((RGraph.refineData S012_sub_S0h12
        (graphPLReebData C4 h4 S012)).V 3) = 1 ∧
      IsEmpty (C4.induce {v | h4 v = S0h12.value 1}).ConnectedComponent ∧
      Nat.card ((graphPLReebData C4 h4 S0h12).V 1) = 2 := by
  have hV : Nat.card ((RGraph.refineData S012_sub_S0h12
      (graphPLReebData C4 h4 S012)).V 1) = 2 :=
    (refine_gap_v_card C4 h4 S012_sub_S0h12 1 0 S0h12_one_mem_S012_K0).trans
      c4_edgeCounts.1
  refine ⟨hV, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (refine_gap_e_card C4 h4 S012_sub_S0h12 0 0 basePt_S0h12_zero_mem_S012).trans
      c4_edgeCounts.1
  · exact (refine_gap_e_card C4 h4 S012_sub_S0h12 1 0 basePt_S0h12_one_mem_S012).trans
      c4_edgeCounts.1
  · exact (refine_old_v_card C4 h4 S012_sub_S0h12 0 0
      (by simp only [S0h12_zero, S012_zero_local])).trans c4_vertexCounts.1
  · exact (refine_old_v_card C4 h4 S012_sub_S0h12 2 1
      (by simp only [S0h12_two, S012_one_local])).trans c4_vertexCounts.2.1
  · exact (refine_old_v_card C4 h4 S012_sub_S0h12 3 2
      (by simp only [S0h12_three, S012_two_local])).trans c4_vertexCounts.2.2
  · have hv : IsEmpty {v : Fin 4 // h4 v = S0h12.value 1} :=
      ⟨fun ⟨v, hv⟩ => by
        fin_cases v <;> norm_num [h4, S0h12_one] at hv⟩
    exact ⟨fun c => c.ind fun v => hv.false ⟨v.1, v.2⟩⟩
  · exact (Nat.card_congr (Equiv.ofBijective _
      (graphPLRefineHom_bijective_v C4 h4 c4_covers S012_sub_S0h12 1))).trans hV

/-! ## R3. Y-tree with a middle-gap insertion -/

/-- `S0123` is refined by `S01h23`. -/
theorem S0123_sub_S01h23 : Set.range S0123.value ⊆ Set.range S01h23.value := by
  rintro _ ⟨i, rfl⟩
  fin_cases i
  · exact ⟨0, S01h23_zero.trans S0123_zero_local.symm⟩
  · exact ⟨1, S01h23_one.trans S0123_one_local.symm⟩
  · exact ⟨3, S01h23_three.trans S0123_two_local.symm⟩
  · exact ⟨4, S01h23_four.trans S0123_three_local.symm⟩

/-- The Y-tree refinement isomorphism after inserting `3/2`. -/
def Y_refineIso :
    graphPLReebData Y hY S01h23 ≅
      RGraph.refineData S0123_sub_S01h23 (graphPLReebData Y hY S0123) :=
  graphPLRefineIso Y hY Y_covers S0123_sub_S01h23

/-- The inserted Y-tree level has two crossing vertices, its original level has cardinality two,
and the two refined middle gaps have cardinality two. -/
theorem Y_refine_counts :
    Nat.card ((RGraph.refineData S0123_sub_S01h23
        (graphPLReebData Y hY S0123)).V 2) = 2 ∧
      Nat.card ((RGraph.refineData S0123_sub_S01h23
        (graphPLReebData Y hY S0123)).E 1) = 2 ∧
      Nat.card ((RGraph.refineData S0123_sub_S01h23
        (graphPLReebData Y hY S0123)).E 2) = 2 ∧
      Nat.card ((graphPLReebData Y hY S01h23).V 2) = 2 := by
  have hV : Nat.card ((RGraph.refineData S0123_sub_S01h23
      (graphPLReebData Y hY S0123)).V 2) = 2 :=
    (refine_gap_v_card Y hY S0123_sub_S01h23 2 1 S01h23_two_mem_S0123_K1).trans
      Y_edgeCounts.2.1
  refine ⟨hV, ?_, ?_, ?_⟩
  · exact (refine_gap_e_card Y hY S0123_sub_S01h23 1 1 basePt_S01h23_one_mem_S0123).trans
      Y_edgeCounts.2.1
  · exact (refine_gap_e_card Y hY S0123_sub_S01h23 2 1 basePt_S01h23_two_mem_S0123).trans
      Y_edgeCounts.2.1
  · exact (Nat.card_congr (Equiv.ofBijective _
      (graphPLRefineHom_bijective_v Y hY Y_covers S0123_sub_S01h23 2))).trans hV

/-! ## R4. Empty insertion -/

/-- The self-refinement comparison for the 4-cycle. -/
def c4_refineSelfIso :
    graphPLReebData C4 h4 S012 ≅
      RGraph.refineData (Set.Subset.refl (Set.range S012.value))
        (graphPLReebData C4 h4 S012) :=
  graphPLRefineIso C4 h4 c4_covers (Set.Subset.refl (Set.range S012.value))

/-- At an unchanged level, the self-refinement vertex map is the old-fiber equivalence. -/
theorem c4_refineSelf_v : ∀ j,
    (graphPLRefineHom C4 h4 c4_covers
      (Set.Subset.refl (Set.range S012.value))).v j =
      (RGraph.refineVEquivOld (Set.Subset.refl (Set.range S012.value)) _ j j rfl).symm := by
  intro j
  funext x
  exact (graphPLRefineHom_v_old C4 h4 c4_covers
    (Set.Subset.refl (Set.range S012.value)) j j rfl x).trans (by
      rw [levelVertexEquivOfEq_rfl]
      rfl)

/-! ## R5. Exterior levels -/

/-- The old levels `0, 2` occur in `S0123`. -/
theorem S02_sub_S0123 : Set.range S02.value ⊆ Set.range S0123.value := by
  rintro _ ⟨i, rfl⟩
  fin_cases i
  · exact ⟨0, S0123_zero_local.trans S02_zero_local.symm⟩
  · exact ⟨2, S0123_two_local.trans S02_one_local.symm⟩

/-- The single-edge refinement to the four-level list. -/
def edge_refineIso_ext :
    graphPLReebData edgeGraph h02 S0123 ≅
      RGraph.refineData S02_sub_S0123 (graphPLReebData edgeGraph h02 S02) :=
  graphPLRefineIso edgeGraph h02 edge_covers_S02 S02_sub_S0123

/-- The exterior level `3` and gap `[2, 3]` are empty. -/
theorem edge_ext_empty :
    IsEmpty ((graphPLReebData edgeGraph h02 S0123).V 3) ∧
      IsEmpty ((graphPLReebData edgeGraph h02 S0123).E 2) := by
  constructor
  · change IsEmpty (LevelVertex edgeGraph h02 (S0123.value 3))
    exact isEmpty_levelVertex_of_notMem_Icc edgeGraph h02 edge_covers_S02 (by
      norm_num [S02_zero_local, S02_last_local, S0123_three_local])
  · change IsEmpty (SpanEdge edgeGraph h02 (S0123.value (Fin.castSucc 2))
      (S0123.value (Fin.succ 2)))
    exact isEmpty_spanEdge_of_exterior edgeGraph h02 edge_covers_S02 (by
      norm_num [S0123_castSucc_two_local, S0123_succ_two_local])
      (Or.inr (by rw [S02_last_local, S0123_castSucc_two_local]))

/-! ## R6. Negative control -/

/-- The path height with the middle vertex at the inserted value `1`. -/
def h012 : Fin 3 → ℝ := ![0, 1, 2]

/-- The list `S02` does not cover the middle path vertex. -/
theorem path_not_covers_S02 : ¬ CoversVertexHeights S02 h012 := by
  intro hcov
  obtain ⟨i, hi⟩ := hcov 1
  fin_cases i <;> norm_num [h012, S02_zero_local, S02_one_local] at hi

private def path_d01 : path3.Dart :=
  ⟨(0, 1), pathGraph_adj.2 (.inl (by decide))⟩

private def path_d12 : path3.Dart :=
  ⟨(1, 2), pathGraph_adj.2 (.inl (by decide))⟩

private theorem path_edge_cases (e : path3.edgeSet) :
    e = dartEdge path_d01 ∨ e = dartEdge path_d12 := by
  obtain ⟨⟨⟨a, b⟩, hab⟩, rfl⟩ := exists_dartEdge_eq e
  have hab' := pathGraph_adj.1 hab
  fin_cases a <;> fin_cases b <;> first
    | exact absurd hab' (by decide)
    | exact Or.inl rfl
    | exact Or.inl (Subtype.ext Sym2.eq_swap)
    | exact Or.inr rfl
    | exact Or.inr (Subtype.ext Sym2.eq_swap)

/-- Neither path edge spans the interval `[0, 2]`. -/
theorem path_S02_E0_empty : IsEmpty ((graphPLReebData path3 h012 S02).E 0) := by
  rw [graphPLReebData_E]
  refine ⟨fun z => ?_⟩
  rcases path_edge_cases z.1 with hz | hz
  · have hz' := z.2
    rw [hz, edgeSpans_dartEdge_iff] at hz'
    rcases hz' with ⟨_, hz'⟩
    norm_num [path_d01, h012, S02_succ_zero_local] at hz'
  · have hz' := z.2
    rw [hz, edgeSpans_dartEdge_iff] at hz'
    rcases hz' with ⟨hz', _⟩
    norm_num [path_d12, h012, S02_castSucc_zero_local] at hz'
    have htwo : (![0, 1, 2] : Fin 3 → ℝ) 2 = 2 := rfl
    rw [htwo] at hz'
    norm_num at hz'

/-- There is no isomorphism for the uncovered-vertex path data. -/
theorem path_no_refineIso :
    IsEmpty (graphPLReebData path3 h012 S012 ≅
      RGraph.refineData S02_sub_S012 (graphPLReebData path3 h012 S02)) := by
  have hx : Nonempty ((graphPLReebData path3 h012 S012).V 1) := by
    change Nonempty (LevelVertex path3 h012 (S012.value 1))
    exact ⟨Sum.inl ((path3.induce {v | h012 v = S012.value 1}).connectedComponentMk
      ⟨1, by norm_num [h012, S012_one_local]⟩)⟩
  obtain ⟨x⟩ := hx
  refine ⟨fun e => ?_⟩
  exact path_S02_E0_empty.false
    (RGraph.refineVEquiv S02_sub_S012 (graphPLReebData path3 h012 S02) 1 0
      S012_one_mem_S02_K0
      (e.hom.v 1 x))

/-! ## R7. Transitivity and Mapper comparison -/

private theorem edge_half_crosses :
    EdgeCrosses edgeGraph h02 (S0h12.value 1) (dartEdge d₀) := by
  rw [edgeCrosses_dartEdge_iff]
  norm_num [d₀, S0h12_one, h02]

/-- The pointwise transitivity square at the inserted level `1/2`. -/
theorem edge_refine_trans :
    ((graphPLRefineHom edgeGraph h02 edge_covers_S02 S02_sub_S0h12).v 1
      (Sum.inr ⟨dartEdge d₀, edge_half_crosses⟩)).1 =
      RGraph.refineMap S02_sub_S012 (graphPLReebData edgeGraph h02 S02)
        (TDA.Reeb.CylinderPresentation.realizeHom S012
          (graphPLRefineHom edgeGraph h02 edge_covers_S02 S02_sub_S012)
          ((graphPLRefineHom edgeGraph h02 edge_covers_S012 S012_sub_S0h12).v 1
            (Sum.inr ⟨dartEdge d₀, edge_half_crosses⟩)).1) := by
  exact graphPLRefineHom_trans_v edgeGraph h02 edge_covers_S02 S02_sub_S012
    S012_sub_S0h12 S02_sub_S0h12 1 (Sum.inr ⟨dartEdge d₀, edge_half_crosses⟩)

/-- The single-edge Mapper comparison followed by refinement. -/
def edge_mapperRefineIso :
    uniformMapperData edgeGraph h02 (-1 / 8) 1 (3 / 8) 2 ≅
      RGraph.refineData S02_sub_S012 (graphPLReebData edgeGraph h02 S02) :=
  edge_mapperIso ≪≫ edge_refineIso

/-- The single-edge Mapper realization comparison after refinement. -/
def edge_mapper_toOver :
    RGraph.toOver S012 (uniformMapperData edgeGraph h02 (-1 / 8) 1 (3 / 8) 2) ≅
      RGraph.toOver S02 (graphPLReebData edgeGraph h02 S02) :=
  (RGraph.realizationFunctor S012).mapIso edge_mapperIso ≪≫
    graphPLRefineToOverIso edgeGraph h02 edge_covers_S02 S02_sub_S012

end
end TDA.Mapper.GraphPLRefinementExamples
