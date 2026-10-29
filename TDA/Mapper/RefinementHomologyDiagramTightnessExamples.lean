import TDA.Mapper.RefinementHomologyDiagramTightness
import TDA.Mapper.RefinementHomologyDiagramExamples

/-!
# Tightness fixtures for step-tower diagrams

* **Merge, exact `1/2`.** The degree-zero step diagrams of the two-stage merge at the radii
  `0, 1` and `1/2, 3/2` are at bottleneck distance exactly `1/2`: the second grid translated by
  `1/2` is the first, and the first nonempty stage has two vertices.
* **One-member tower, exact `1`.** Over the one-point space, the step towers with stages the
  empty family and the full space on the grids `{1}` and `shiftGrid 1 {1} = {0}` have
  degree-zero diagrams at bottleneck distance exactly `1`. The members are right-continuous
  steps, in contrast to the left-open members of the late and early towers.
* **Zero shift.** Translating the grid by `0` is the identity, and the merge diagram is at
  distance `0` from itself, in agreement with the exact distance at the shift `0`.
* **Negative control: the survival hypothesis.** On the 4-cycle with heights `0, 1, 2, 1`, the
  stages empty, three-member cover and one-member cover on the grid `0, 1` have the degree-one
  diagram `{(0, 1)}`, and its translate by `1` is `{(-1, 0)}`. Every double-shift structure map
  of the two modules at the parameter `1/2` vanishes, so the zero maps form a `1/2`-interleaving,
  the bottleneck distance is at most `1/2 < 1`, and the homology map from the three-member stage
  to the last stage is zero.
* **Negative control: infinite distance.** The empty-grid diagram has no essential bar and the
  merge diagram has one, so their bottleneck distance is infinite.
-/

namespace TDA.Mapper.RefinementHomologyDiagramTightnessExamples

open CategoryTheory CategoryTheory.Limits Set SimpleGraph
open TDA.Topology TDA.Simplicial TDA.Persistence TDA.Persistence.FiniteConstructible
open TDA.Reeb TDA.Reeb.OpenInterval TDA.Reeb.GraphPL TDA.Reeb.GraphRealization
open TDA.Reeb.Examples.GraphPL
open TDA.Reeb.Examples.GraphRealization (edgeGraph)
open TDA.Mapper.TowerExamples
open TDA.Mapper.RefinementHomologyExamples
open TDA.Mapper.RefinementHomologyBarcodeExamples
open TDA.Mapper.RefinementHomologyDiagramExamples
open TDA.Persistence.RealShift
open scoped NNReal ENNReal

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

noncomputable section

/-! ## Zero interleavings -/

section Zero

universe u w

variable {R : Type u} [Ring R] {M N : PModule.{u,0,w} R ℝ}

/-- If every double-shift structure map of two real modules at the parameter `ε` is zero, the
zero maps form an `ε`-interleaving. -/
theorem nonempty_realInterleaving_of_structureMap_eq_zero (ε : ℝ≥0)
    (hM : ∀ (t : ℝ) (h : t ≤ t + ((ε + ε : ℝ≥0) : ℝ)), structureMap M h = 0)
    (hN : ∀ (t : ℝ) (h : t ≤ t + ((ε + ε : ℝ≥0) : ℝ)), structureMap N h = 0) :
    Nonempty (RealInterleaving ε M N) :=
  ⟨RealInterleaving.ofApp 0 0
    (fun t => by
      rw [NatTrans.app_zero, zero_comp, transition_app]
      exact (hM t _).symm)
    (fun t => by
      rw [NatTrans.app_zero, zero_comp, transition_app]
      exact (hN t _).symm)⟩

end Zero

/-! ## The merge -/

section Merge

local instance (q : Fin 2) :
    LinearOrder (ComponentIndex (plHeight edgeGraph h01) (mergeCover q)) := by
  classical
  exact linearOrderOfSTO WellOrderingRel

private instance (q : Fin 2) : Finite (mergeIndex q) := by
  fin_cases q <;> dsimp [mergeIndex] <;> infer_instance

/-- A vertex of the first padded merge stage. -/
private def mergeVertex :
    ComponentIndex (plHeight edgeGraph h01) (padCover mergeCover (0 : Fin 2).succ) :=
  ⟨(0 : Fin 2), ZerothHomotopy.mk ⟨vertex edgeGraph false,
    show h01 false ∈ (mergeIntervals 0 (0 : Fin 2) : Set ℝ) by
      norm_num [h01, mergeIntervals, mergeFine, mem_ioo]⟩⟩

/-- The degree-zero step diagrams of the merge on the grids `0, 1` and `1/2, 3/2` are at
bottleneck distance exactly `1/2`. -/
theorem merge_bottleneck_eq :
    bottleneck (mergeDiagram grid01) (mergeDiagram gridHalf) = ((1 / 2 : ℝ≥0) : ℝ≥0∞) := by
  rw [bottleneck_comm, grid01_eq_shiftGrid]
  exact bottleneck_stepMapperDiagram_shiftGrid_eq_zero_degree ℚ _ gridHalf _ (1 / 2) mergeVertex

/-- The zero translate of a grid is the grid, and the merge diagram on a grid is at bottleneck
distance exactly `0` from the diagram on its zero translate. -/
theorem merge_shiftGrid_zero :
    shiftGrid 0 gridHalf = gridHalf ∧
      bottleneck (mergeDiagram gridHalf) (mergeDiagram (shiftGrid 0 gridHalf)) = 0 := by
  refine ⟨shiftGrid_zero gridHalf, ?_⟩
  simpa using bottleneck_stepMapperDiagram_shiftGrid_eq_zero_degree ℚ _ gridHalf _ 0 mergeVertex

end Merge

/-! ## A one-member tower over a point -/

section Point

local instance {ι : Type} [LinearOrder ι] (U : ι → Set Unit) :
    LinearOrder (ComponentIndex threeStageMap U) :=
  componentIndexLinearOrder threeStageMap U

private instance {ι : Type} [Finite ι] (U : ι → Set Unit) :
    Finite (ComponentIndex threeStageMap U) :=
  have : ∀ i, Finite (ZerothHomotopy (PullbackSpace threeStageMap U i)) := fun i =>
    have := subsingleton_zerothHomotopy (Z := PullbackSpace threeStageMap U i)
    inferInstance
  inferInstanceAs (Finite (Σ i, ZerothHomotopy (PullbackSpace threeStageMap U i)))

/-- The single stage: the full space as the only member. -/
def fullStage (_ : Fin 1) : Unit → Set Unit := fun _ => Set.univ

/-- The refinements of the single full stage. -/
def fullStageRefinement {i j : Fin 1} (_ : i ≤ j) : Refinement (fullStage i) (fullStage j) :=
  Refinement.id _

/-- The grid with the single radius `1`. -/
def oneGrid : Fin 1 ↪o ℝ :=
  OrderEmbedding.ofStrictMono (fun _ => 1) (fun i j h => absurd h (by
    rw [Subsingleton.elim i j]
    exact lt_irrefl _))

/-- The degree-zero step diagram of the empty stage followed by the full stage on the grid `c`. -/
abbrev fullDiagram (c : Fin 1 ↪o ℝ) : Diagram ℝ :=
  stepMapperDiagram ℚ threeStageMap c (padCover fullStage)
    (padRefinement fullStage fullStageRefinement) 0

/-- The step diagrams on the grid `{1}` and on its translate by `1`, the grid `{0}`, are at
bottleneck distance exactly `1`. -/
theorem full_bottleneck_eq :
    shiftGrid 1 oneGrid 0 = 0 ∧
      bottleneck (fullDiagram oneGrid) (fullDiagram (shiftGrid 1 oneGrid)) = ((1 : ℝ≥0) : ℝ≥0∞) := by
  refine ⟨by simp [oneGrid], ?_⟩
  exact bottleneck_stepMapperDiagram_shiftGrid_eq_zero_degree ℚ _ oneGrid _ 1
    ⟨(), ZerothHomotopy.mk ⟨(), Set.mem_univ _⟩⟩

end Point

/-! ## The loop -/

section Loop

local instance (q : Fin 2) :
    LinearOrder (ComponentIndex (plHeight C4 h4) (loopCover q)) := by
  classical
  exact linearOrderOfSTO WellOrderingRel

private instance (q : Fin 2) : Finite (loopIndex q) := by
  fin_cases q <;> dsimp [loopIndex] <;> infer_instance

/-- The one-member stage has no edge: its single member has pairwise disjoint components. -/
private instance : IsEmpty (Face (mapper (plHeight C4 h4) (loopCover 1)) 1) :=
  ⟨fun σ => by
    classical
    obtain ⟨a, b, hab, hσ⟩ := Finset.card_eq_two.1 σ.2.2
    have ha : a ∈ σ.1 := by simp [hσ]
    have hb : b ∈ σ.1 := by simp [hσ]
    exact hab (eq_of_mem_mapper_face_of_fst_eq _ _ σ.2.1 ha hb
      (Subsingleton.elim (α := Unit) a.1 b.1))⟩

/-- The degree-one step diagram of the empty, three-member and one-member stages of the
4-cycle on the grid `c`. -/
abbrev loopDiagram (c : Fin 2 ↪o ℝ) : Diagram ℝ :=
  stepMapperDiagram ℚ (plHeight C4 h4) c (padCover loopCover)
    (padRefinement loopCover loopRefinement) 1

/-- The degree-one Mapper homology module of the loop step tower on the grid `c`. -/
abbrev loopModule (c : Fin 2 ↪o ℝ) : PModule.{0,0,0} ℚ ℝ :=
  mapperHomologyPModule ℚ (plHeight C4 h4) (stepTower c (padCover loopCover))
    (stepRefinement c _ (padRefinement loopCover loopRefinement)) 1

/-- The degree-one diagram of the loop on the grid `c` is the single bar from `c 0` to `c 1`. -/
theorem loopDiagram_points (c : Fin 2 ↪o ℝ) :
    (loopDiagram c).points = {(c 0, ((c 1 : ℝ) : WithTop ℝ))} := by
  rw [loopDiagram, stepMapperDiagram_pad, loop_mapperBarcode]
  rfl

/-- The degree-one homology of the loop vanishes outside the three-member stage. -/
private theorem isZero_loopModule {c : Fin 2 ↪o ℝ} {t : ℝ} (ht : cellIndex c t ≠ 1) :
    IsZero ((loopModule c).obj t) := by
  change IsZero (simplicialHomology
    (mapper (plHeight C4 h4) (padCover loopCover (cellIndex c t))) ℚ 1)
  generalize cellIndex c t = i at ht ⊢
  match i, ht with
  | 0, _ => exact isZero_simplicialHomology_mapper_of_isEmpty ℚ _ _ 1
  | 1, ht => exact absurd rfl ht
  | 2, _ =>
    exact isZero_simplicialHomology_of_isEmpty_face (K := mapper (plHeight C4 h4) (loopCover 1)) ℚ 1

/-- If the bars of the loop diagram on `c` have length at most `1`, every double-shift
structure map at the parameter `1/2` is zero. -/
private theorem loopModule_structureMap_eq_zero {c : Fin 2 ↪o ℝ} (hc : c 1 ≤ c 0 + 1) {t : ℝ}
    (h : t ≤ t + (((1 / 2 : ℝ≥0) + 1 / 2 : ℝ≥0) : ℝ)) : structureMap (loopModule c) h = 0 := by
  by_cases ht : cellIndex c t = 1
  · refine (isZero_loopModule (t := t + (((1 / 2 : ℝ≥0) + 1 / 2 : ℝ≥0) : ℝ)) ?_).eq_of_tgt _ _
    have h0 := ((cellIndex_eq_succ_iff c 0 t).1 ht).1
    have : cellIndex c (t + (((1 / 2 : ℝ≥0) + 1 / 2 : ℝ≥0) : ℝ)) = Fin.last 2 :=
      cellIndex_of_last_le c _ (by push_cast; linarith [c.monotone (Fin.zero_le (Fin.last 1))])
    rw [this]
    decide
  · exact (isZero_loopModule ht).eq_of_src _ _

/-- The loop modules on the grid `0, 1` and on its translate by `1` are `1/2`-interleaved by the
zero maps. -/
theorem loop_shift_interleaving :
    Nonempty (RealInterleaving (1 / 2) (loopModule grid01) (loopModule (shiftGrid 1 grid01))) :=
  nonempty_realInterleaving_of_structureMap_eq_zero _
    (fun _ h => loopModule_structureMap_eq_zero (by simp [grid01]) h)
    (fun _ h => loopModule_structureMap_eq_zero (by simp [grid01]) h)

/-- The homology map from the three-member stage to the last stage vanishes in degree one. -/
theorem loop_not_survivesToLast :
    ¬ SurvivesToLast ℚ (plHeight C4 h4) 1 (padRefinement loopCover loopRefinement) := fun h =>
  h ((isZero_simplicialHomology_of_isEmpty_face
    (K := mapper (plHeight C4 h4) (loopCover 1)) ℚ 1).eq_of_tgt _ _)

/-- The loop diagrams on the grid `0, 1` and on its translate by `1` are the single bars `(0, 1)`
and `(-1, 0)`; they are at bottleneck distance at most `1/2`, hence less than the shift `1`; and
the survival hypothesis fails. -/
theorem loop_shift_control :
    (loopDiagram grid01).points = {((0 : ℝ), ((1 : ℝ) : WithTop ℝ))} ∧
      (loopDiagram (shiftGrid 1 grid01)).points = {((-1 : ℝ), ((0 : ℝ) : WithTop ℝ))} ∧
      bottleneck (loopDiagram grid01) (loopDiagram (shiftGrid 1 grid01)) ≤
        ((1 / 2 : ℝ≥0) : ℝ≥0∞) ∧
      bottleneck (loopDiagram grid01) (loopDiagram (shiftGrid 1 grid01)) < ((1 : ℝ≥0) : ℝ≥0∞) ∧
      ¬ SurvivesToLast ℚ (plHeight C4 h4) 1 (padRefinement loopCover loopRefinement) := by
  have hle : bottleneck (loopDiagram grid01) (loopDiagram (shiftGrid 1 grid01)) ≤
      ((1 / 2 : ℝ≥0) : ℝ≥0∞) := by
    obtain ⟨i⟩ := loop_shift_interleaving
    rw [bottleneck_stepMapperDiagram_eq]
    exact i.distance_le
  refine ⟨?_, ?_, hle, hle.trans_lt ?_, loop_not_survivesToLast⟩
  · rw [loopDiagram_points]
    simp [grid01]
  · rw [loopDiagram_points]
    simp [grid01]
  · rw [ENNReal.coe_lt_coe]
    norm_num

end Loop

/-! ## Infinite distance -/

section Infinite

local instance (i : Fin 1) :
    LinearOrder (ComponentIndex (plHeight edgeGraph h01) (emptyStage i)) :=
  @LinearOrder.lift' _ (Fin 0) _ (fun a => a.1) (fun a => Fin.elim0 a.1)

private instance (i : Fin 1) (n : ℕ) :
    Finite (Face (mapper (plHeight edgeGraph h01) (emptyStage i)) n) := by
  rw [mapper_eq_bot_of_isEmpty]
  infer_instance

local instance (q : Fin 2) :
    LinearOrder (ComponentIndex (plHeight edgeGraph h01) (mergeCover q)) := by
  classical
  exact linearOrderOfSTO WellOrderingRel

private instance (q : Fin 2) : Finite (mergeIndex q) := by
  fin_cases q <;> dsimp [mergeIndex] <;> infer_instance

/-- The empty-grid diagram has no essential bar, the merge diagram has one, and the bottleneck
distance between them is infinite. -/
theorem emptyGrid_merge_bottleneck_eq_top :
    (essentialPart (stepMapperDiagram ℚ (plHeight edgeGraph h01) emptyGrid emptyStage
        emptyStageRefinement 0).points).card = 0 ∧
      (essentialPart (mergeDiagram grid01).points).card = 1 ∧
      bottleneck (stepMapperDiagram ℚ (plHeight edgeGraph h01) emptyGrid emptyStage
        emptyStageRefinement 0) (mergeDiagram grid01) = ⊤ := by
  have h0 : (stepMapperDiagram ℚ (plHeight edgeGraph h01) emptyGrid emptyStage
      emptyStageRefinement 0).points = 0 := (emptyGrid_stepMapperDiagram ℚ _ 0).2.1
  have h1 : essentialPart (mergeDiagram grid01).points = {(0 : ℝ)} := merge_stepMapperDiagram.2.2
  have c0 : (essentialPart (stepMapperDiagram ℚ (plHeight edgeGraph h01) emptyGrid emptyStage
      emptyStageRefinement 0).points).card = 0 := by
    rw [h0]
    rfl
  have c1 : (essentialPart (mergeDiagram grid01).points).card = 1 := by
    rw [h1]
    rfl
  exact ⟨c0, c1, (bottleneck_stepMapperDiagram_eq_top_iff ℚ _ 0 _ _).2 (by rw [c0, c1]; simp)⟩

end Infinite

end

end TDA.Mapper.RefinementHomologyDiagramTightnessExamples
