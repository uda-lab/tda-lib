import TDA.Mapper.RefinementHomologyDiagram
import TDA.Mapper.RefinementHomologyBarcodeExamples
import TDA.Mapper.RefinementHomologyInterleavingExamples
import TDA.Persistence.DiagramBottleneckLaws

/-!
# Step-tower diagram fixtures

A finite family of cover families on `Fin N` becomes step data on `Fin (N + 1)` by prepending
an empty stage (`padIndex`, `padCover`, `padRefinement`); its step diagram on a grid
`c : Fin N ↪o ℝ` is `ofIndexBars c` of the finite Mapper barcode of the original stages.

* **Empty grid.** With no critical values and one empty stage, the module vanishes at every
  radius, the diagram is empty and its bottleneck distance to itself is `0`.
* **Two-stage merge.** On the single edge with heights `0, 1`, the stages `(-1, 1/3)`,
  `(2/3, 2)` and then `(-1, 2)` placed at the radii `0` and `1` give the degree-zero diagram
  over `ℚ` with finite part `{(0, 1)}` and essential part `{0}`.
* **Shifted copy.** The same stages at the radii `1/2` and `3/2` are related to the first copy
  by selected stage refinements shifting the radius by `1/2` in both directions: the identity
  from radius `t` to `t + 1/2`, which lie in the same stage, and the merge refinement, whose
  selector to the coarse stage is constant, in the other direction. The bottleneck
  distance is at most `1/2` and equals the interleaving distance, while the two diagrams differ
  in their essential births `0` and `1/2`.
* **Refinement independence.** The skew three-stage family over a point, padded by an empty
  stage, has the same step diagram `{(c 0, ∞)}` for its skew and its coherent selections.
* **Graph-PL loop.** On the 4-cycle with heights `0, 1, 2, 1`, the three-member cover and then
  the one-member cover at the radii `0` and `1` give the degree-one diagram `{(0, 1)}` with no
  essential bar; the face-finiteness instances are synthesized.
* **Negative control: nonempty left tail.** Over a point, the constant tower of the one full
  member has nonzero `H₀` at every radius, so it is not finite-constructible on any grid.
* **Negative control: centred tower.** For the constant map `0` on the unit interval, the
  Mapper homology module along the centred tower of spacing `1` is zero at radius `0` and
  nonzero at every positive radius. Since `0` and small positive radii lie in one cell of every
  grid, the module is not finite-constructible on any grid, and no diagram is defined for it.
-/

namespace TDA.Mapper.RefinementHomologyDiagramExamples

open CategoryTheory CategoryTheory.Limits
open TDA.Topology TDA.Simplicial TDA.Persistence TDA.Persistence.FiniteConstructible
open TDA.Reeb TDA.Reeb.OpenInterval TDA.Reeb.GraphPL
open TDA.Reeb.Examples.GraphPL
open TDA.Reeb.Examples.GraphRealization (edgeGraph)
open TDA.Mapper.TowerExamples
open TDA.Mapper.RefinementHomologyExamples
open TDA.Mapper.RefinementHomologyBarcodeExamples
open TDA.Mapper.RefinementHomologyInterleavingExamples
open scoped NNReal ENNReal unitInterval

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

noncomputable section

/-! ## Prepending an empty stage -/

section Pad

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] {N : ℕ}

/-- The index types with an empty stage `0` prepended. -/
def padIndex (Index : Fin N → Type) : Fin (N + 1) → Type :=
  Fin.cases (Fin 0) Index

/-- The prepended stage has no labels. -/
instance padIndex_isEmpty (Index : Fin N → Type) : IsEmpty (padIndex Index 0) :=
  inferInstanceAs (IsEmpty (Fin 0))

/-- Finitely many labels at every original stage give finitely many at every padded stage. -/
instance padIndex_finite (Index : Fin N → Type) [∀ q, Finite (Index q)] (i : Fin (N + 1)) :
    Finite (padIndex Index i) :=
  Fin.cases (motive := fun i => Finite (padIndex Index i)) (inferInstanceAs (Finite (Fin 0)))
    (fun q => inferInstanceAs (Finite (Index q))) i

variable {Index : Fin N → Type}

/-- The cover families with an empty stage `0` prepended. -/
def padCover (cover : (q : Fin N) → Index q → Set Y) :
    (i : Fin (N + 1)) → padIndex Index i → Set Y :=
  Fin.cases (motive := fun i => padIndex Index i → Set Y) (fun e => Fin.elim0 e) cover

/-- The refinements of the padded families: the empty stage refines every stage, and the other
comparisons are the given refinements. -/
def padRefinement (cover : (q : Fin N) → Index q → Set Y)
    (r : ∀ {q t : Fin N}, q ≤ t → Refinement (cover q) (cover t)) :
    ∀ {i j : Fin (N + 1)}, i ≤ j → Refinement (padCover cover i) (padCover cover j) := by
  intro i j h
  cases i using Fin.cases with
  | zero => exact ⟨fun e => Fin.elim0 e, fun e => Fin.elim0 e⟩
  | succ a =>
    cases j using Fin.cases with
    | zero => exact absurd h (by simp)
    | succ b => exact r (Fin.succ_le_succ_iff.mp h)

/-- Component orders of the padded families; the empty stage has no component index. -/
instance padOrder (f : C(X, Y)) (cover : (q : Fin N) → Index q → Set Y)
    [∀ q, LinearOrder (ComponentIndex f (cover q))] (i : Fin (N + 1)) :
    LinearOrder (ComponentIndex f (padCover cover i)) :=
  Fin.cases (motive := fun i => LinearOrder (ComponentIndex f (padCover cover i)))
    (@LinearOrder.lift' _ (Fin 0) _ (fun a => a.1) (fun a => Fin.elim0 a.1))
    (fun q => inferInstanceAs (LinearOrder (ComponentIndex f (cover q)))) i

/-- Face finiteness of the padded families; the empty stage has no faces. -/
instance padFace_finite (f : C(X, Y)) (cover : (q : Fin N) → Index q → Set Y)
    [∀ q, LinearOrder (ComponentIndex f (cover q))] (n : ℕ)
    [∀ q, Finite (Face (mapper f (cover q)) n)] (i : Fin (N + 1)) :
    Finite (Face (mapper f (padCover cover i)) n) :=
  Fin.cases (motive := fun i => Finite (Face (mapper f (padCover cover i)) n))
    (by
      rw [mapper_eq_bot_of_isEmpty]
      infer_instance)
    (fun q => inferInstanceAs (Finite (Face (mapper f (cover q)) n))) i

/-- The step diagram of padded families is `ofIndexBars` of the Mapper barcode of the
original families. -/
theorem stepMapperDiagram_pad (k : Type) [Field k] (f : C(X, Y)) (c : Fin N ↪o ℝ)
    (cover : (q : Fin N) → Index q → Set Y) [∀ q, LinearOrder (ComponentIndex f (cover q))]
    (r : ∀ {q t : Fin N}, q ≤ t → Refinement (cover q) (cover t))
    (n : ℕ) [∀ q, Finite (Face (mapper f (cover q)) n)] :
    stepMapperDiagram k f c (padCover cover) (padRefinement cover r) n =
      ofIndexBars c c.strictMono (mapperBarcode k f cover r n) :=
  (stepMapperDiagram_eq_ofIndexBars_succ k f c _ _ n).trans
    (congrArg _ (mapperBarcode_eq k f cover _ n r))

end Pad

/-! ## Grids -/

/-- The grid of radii `0, 1`. -/
def grid01 : Fin 2 ↪o ℝ :=
  OrderEmbedding.ofStrictMono ![0, 1] (by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all)

/-- The grid of radii `1/2, 3/2`. -/
def gridHalf : Fin 2 ↪o ℝ :=
  OrderEmbedding.ofStrictMono ![1 / 2, 3 / 2] (by
    intro i j hij
    fin_cases i <;> fin_cases j <;> (simp_all; try norm_num))

/-- The grid `0, 1` is the grid `1/2, 3/2` shifted by `1/2`. -/
theorem grid01_eq_shiftGrid : grid01 = shiftGrid (1 / 2) gridHalf := by
  ext i
  fin_cases i <;> (simp [grid01, gridHalf, shiftGrid]; try norm_num)

/-! ## The empty grid -/

section EmptyGrid

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (k : Type) [Field k]
  (f : C(X, Y)) (n : ℕ)

/-- The empty grid. -/
def emptyGrid : Fin 0 ↪o ℝ := OrderEmbedding.ofIsEmpty

/-- One stage with no members. -/
def emptyStage (_ : Fin 1) : Fin 0 → Set Y := fun e => Fin.elim0 e

/-- The refinements of the single empty stage. -/
def emptyStageRefinement {i j : Fin 1} (_ : i ≤ j) :
    Refinement (emptyStage (Y := Y) i) (emptyStage j) :=
  ⟨fun e => Fin.elim0 e, fun e => Fin.elim0 e⟩

local instance (i : Fin 1) : LinearOrder (ComponentIndex f (emptyStage i)) :=
  @LinearOrder.lift' _ (Fin 0) _ (fun a => a.1) (fun a => Fin.elim0 a.1)

private instance (i : Fin 1) : Finite (Face (mapper f (emptyStage i)) n) := by
  rw [mapper_eq_bot_of_isEmpty]
  infer_instance

/-- With no critical values and one empty stage, the module is zero at every radius, the
diagram is empty and its bottleneck distance to itself is `0`. -/
theorem emptyGrid_stepMapperDiagram :
    (∀ t, IsZero ((mapperHomologyPModule k f (stepTower emptyGrid emptyStage)
        (stepRefinement emptyGrid emptyStage emptyStageRefinement) n).obj t)) ∧
      (stepMapperDiagram k f emptyGrid emptyStage emptyStageRefinement n).points = 0 ∧
      bottleneck (stepMapperDiagram k f emptyGrid emptyStage emptyStageRefinement n)
        (stepMapperDiagram k f emptyGrid emptyStage emptyStageRefinement n) = 0 :=
  ⟨(isConstructible_empty_iff emptyGrid _).mp (isConstructible_stepTower _ _ k f _ n),
    moduleDiagram_empty_grid emptyGrid _, bottleneck_self _⟩

end EmptyGrid

/-! ## The two-stage merge and its shifted copy -/

section Merge

local instance (q : Fin 2) :
    LinearOrder (ComponentIndex (plHeight edgeGraph h01) (mergeCover q)) := by
  classical
  exact linearOrderOfSTO WellOrderingRel

/-- The degree-zero step diagram of the merge on the grid `c`. -/
abbrev mergeDiagram (c : Fin 2 ↪o ℝ) : Diagram ℝ :=
  stepMapperDiagram ℚ (plHeight edgeGraph h01) c (padCover mergeCover)
    (padRefinement mergeCover mergeRefinement) 0

/-- The degree-zero Mapper homology module of the merge step tower on the grid `c`. -/
abbrev mergeModule (c : Fin 2 ↪o ℝ) : PModule.{0,0,0} ℚ ℝ :=
  mapperHomologyPModule ℚ (plHeight edgeGraph h01) (stepTower c (padCover mergeCover))
    (stepRefinement c _ (padRefinement mergeCover mergeRefinement)) 0

private theorem mergeDiagram_points (c : Fin 2 ↪o ℝ) :
    (mergeDiagram c).points = {(c 0, ⊤), (c 0, ((c 1 : ℝ) : WithTop ℝ))} := by
  rw [mergeDiagram, stepMapperDiagram_pad, merge_mapperBarcode.1]
  rfl

/-- At the radii `0` and `1`, the degree-zero diagram of the merge over `ℚ` has the finite bar
`(0, 1)` and the essential bar born at `0`. -/
theorem merge_stepMapperDiagram :
    (mergeDiagram grid01).points = {((0 : ℝ), ⊤), (0, ((1 : ℝ) : WithTop ℝ))} ∧
      finitePart (mergeDiagram grid01).points = {((0 : ℝ), (1 : ℝ))} ∧
      essentialPart (mergeDiagram grid01).points = {(0 : ℝ)} := by
  rw [mergeDiagram_points]
  exact ⟨rfl, rfl, rfl⟩

private theorem cellIndex_grid01 (t : ℝ) :
    cellIndex grid01 t = cellIndex gridHalf (t + ((1 / 2 : ℝ≥0) : ℝ)) := by
  rw [grid01_eq_shiftGrid, cellIndex_shiftGrid]

/-- Cover maps from the merge at the radii `0, 1` into the copy at `1/2, 3/2`, shifted by `1/2`.
Both radii lie in the same stage, so each map is the identity refinement of that stage. -/
def mergeShiftForward (t : ℝ) :
    Refinement (stepTower grid01 (padCover mergeCover) t)
      (stepTower gridHalf (padCover mergeCover) (t + ((1 / 2 : ℝ≥0) : ℝ))) :=
  padRefinement mergeCover mergeRefinement (cellIndex_grid01 t).le

/-- Cover maps from the copy at `1/2, 3/2` into the merge at `0, 1`, shifted by `1/2`: the
selected stage refinement from the stage at `t` to the stage at `t + 1/2`, which is the constant
merge selector when these stages differ. -/
def mergeShiftBackward (t : ℝ) :
    Refinement (stepTower gridHalf (padCover mergeCover) t)
      (stepTower grid01 (padCover mergeCover) (t + ((1 / 2 : ℝ≥0) : ℝ))) :=
  padRefinement mergeCover mergeRefinement (by
    rw [cellIndex_grid01]
    exact (cellIndex gridHalf).monotone (by linarith [NNReal.coe_nonneg (1 / 2 : ℝ≥0)]))

/-- The merge at the radii `0, 1` and its copy at `1/2, 3/2` have diagrams at bottleneck
distance at most `1/2`, equal to the interleaving distance of their modules, while the
diagrams differ: their essential bars are born at `0` and at `1/2`. -/
theorem merge_shift_stepMapperDiagram :
    bottleneck (mergeDiagram grid01) (mergeDiagram gridHalf) ≤ ((1 / 2 : ℝ≥0) : ℝ≥0∞) ∧
      essentialPart (mergeDiagram grid01).points = {(0 : ℝ)} ∧
      essentialPart (mergeDiagram gridHalf).points = {(1 / 2 : ℝ)} ∧
      mergeDiagram grid01 ≠ mergeDiagram gridHalf ∧
      bottleneck (mergeDiagram grid01) (mergeDiagram gridHalf) =
        realInterleavingDistance (mergeModule grid01) (mergeModule gridHalf) := by
  have h01 : essentialPart (mergeDiagram grid01).points = {(0 : ℝ)} :=
    merge_stepMapperDiagram.2.2
  have hHalf : essentialPart (mergeDiagram gridHalf).points = {(1 / 2 : ℝ)} := by
    rw [mergeDiagram_points]
    rfl
  refine ⟨bottleneck_stepMapperDiagram_le ℚ _ 0 _ _ mergeShiftForward mergeShiftBackward, h01,
    hHalf, fun h => ?_, bottleneck_stepMapperDiagram_eq ℚ _ 0 _ _⟩
  rw [h, hHalf, Multiset.singleton_inj] at h01
  norm_num at h01

end Merge

/-! ## Refinement independence -/

section Skew

local instance (q : Fin 3) : LinearOrder (ComponentIndex threeStageMap (skewCover q)) :=
  componentIndexLinearOrder threeStageMap _

/-- On every grid, the skew three-stage family padded by an empty stage has the same
degree-zero step diagram over `ℚ` for its skew and its coherent selections: the single
essential bar born at the first radius. -/
theorem skew_stepMapperDiagram (c : Fin 3 ↪o ℝ) :
    stepMapperDiagram ℚ threeStageMap c (padCover skewCover) (padRefinement skewCover skewFin) 0 =
        stepMapperDiagram ℚ threeStageMap c (padCover skewCover)
          (padRefinement skewCover coherentFin) 0 ∧
      (stepMapperDiagram ℚ threeStageMap c (padCover skewCover)
        (padRefinement skewCover skewFin) 0).points = {(c 0, ⊤)} := by
  refine ⟨stepMapperDiagram_eq ℚ threeStageMap c _ _ 0 _, ?_⟩
  rw [stepMapperDiagram_pad, skew_mapperBarcode.2.1]
  rfl

end Skew

/-! ## The graph-PL loop -/

section Loop

local instance (q : Fin 2) :
    LinearOrder (ComponentIndex (plHeight C4 h4) (loopCover q)) := by
  classical
  exact linearOrderOfSTO WellOrderingRel

/-- At the radii `0` and `1`, the three-member cover and then the one-member cover of the
4-cycle give the degree-one diagram over `ℚ` with the single finite bar `(0, 1)` and no
essential bar. -/
theorem loop_stepMapperDiagram :
    (stepMapperDiagram ℚ (plHeight C4 h4) grid01 (padCover loopCover)
        (padRefinement loopCover loopRefinement) 1).points = {((0 : ℝ), ((1 : ℝ) : WithTop ℝ))} ∧
      essentialPart (stepMapperDiagram ℚ (plHeight C4 h4) grid01 (padCover loopCover)
        (padRefinement loopCover loopRefinement) 1).points = 0 := by
  rw [stepMapperDiagram_pad, loop_mapperBarcode]
  exact ⟨rfl, rfl⟩

end Loop

/-! ## Negative controls -/

section Controls

/-- A Mapper vertex makes `H₀` nonzero over a field. -/
private theorem not_isZero_H0 (k : Type) [Field k] {X Y ι : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) (U : ι → Set Y) [LinearOrder (ComponentIndex f U)]
    (a : ComponentIndex f U) : ¬ IsZero (simplicialHomology (mapper f U) k 0) := by
  intro hz
  have := ModuleCat.subsingleton_of_isZero hz
  exact simplicialHomologyClass_zeroVertexCycle_ne_zero (mapper f U) k
    ⟨{a}, componentIndex_supported f U a, Finset.card_singleton a⟩ (Subsingleton.elim _ _)

/-- Over a point, the constant tower of the one full member is not finite-constructible on any
grid, for every field and component order: its `H₀` is nonzero below the first critical
value. -/
theorem oneSource_not_isConstructible (k : Type) [Field k]
    [LinearOrder (ComponentIndex threeStageMap oneSource)] {m : ℕ} (c : Fin m ↪o ℝ) :
    ¬ IsConstructible c (mapperHomologyPModule k threeStageMap
      (stepTower c (fun _ : Fin (m + 1) => oneSource))
      (stepRefinement c _ fun _ => Refinement.id oneSource) 0) := by
  intro h
  have ht : ∀ i, -1 - ∑ j, |c j| < c i := by
    intro i
    have h1 := Finset.single_le_sum (f := fun j => |c j|) (fun j _ => abs_nonneg (c j))
      (Finset.mem_univ i)
    have h2 := neg_abs_le (c i)
    linarith
  exact not_isZero_H0 k threeStageMap oneSource ⟨(), ZerothHomotopy.mk ⟨(), Set.mem_univ _⟩⟩
    (h.zero_left _ ht)

/-- Every grid has a positive radius in the cell of `0`. -/
private theorem exists_pos_cellIndex_eq {m : ℕ} (c : Fin m ↪o ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ cellIndex c δ = cellIndex c 0 := by
  classical
  let S : Finset ℝ := (Finset.univ.filter fun i => 0 < c i).image c
  have hS : ∀ x ∈ S, 0 < x := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    exact (Finset.mem_filter.mp hi).2
  obtain ⟨δ, hδ, hlt⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ S, δ < x := by
    by_cases hne : S.Nonempty
    · exact ⟨S.min' hne / 2, by linarith [hS _ (S.min'_mem hne)],
        fun x hx => by linarith [S.min'_le x hx, hS _ (S.min'_mem hne)]⟩
    · exact ⟨1, one_pos, fun x hx => absurd ⟨x, hx⟩ hne⟩
  refine ⟨δ, hδ, Fin.ext ?_⟩
  change (Finset.univ.filter fun i => c i ≤ δ).card = (Finset.univ.filter fun i => c i ≤ 0).card
  congr 1
  apply Finset.filter_congr
  intro i _
  constructor
  · intro hi
    by_contra h0
    have hmem : c i ∈ S := Finset.mem_image.mpr
      ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, lt_of_not_ge h0⟩, rfl⟩
    linarith [hlt _ hmem]
  · intro hi
    linarith

/-- The Mapper homology module of the constant map `0` on the unit interval along the centred
tower of spacing `1`. -/
abbrev centredModule (k : Type) [Field k]
    [∀ t, LinearOrder (ComponentIndex flatMap (centredCover 1 t))] : PModule.{0,0,0} k ℝ :=
  mapperHomologyPModule k flatMap (centredCover 1) (centredCoverRefinement 1) 0

/-- Along the centred tower of spacing `1`, the Mapper homology of the constant map `0` on the
unit interval is zero at radius `0` and nonzero at every positive radius, so the module is not
finite-constructible on any grid, for every field and component orders. -/
theorem centred_not_isConstructible (k : Type) [Field k]
    [∀ t, LinearOrder (ComponentIndex flatMap (centredCover 1 t))] :
    IsZero ((centredModule k).obj 0) ∧ (∀ t, 0 < t → ¬ IsZero ((centredModule k).obj t)) ∧
      ∀ (m : ℕ) (c : Fin m ↪o ℝ), ¬ IsConstructible c (centredModule k) := by
  have hzero : IsZero ((centredModule k).obj 0) := by
    have : IsEmpty (ComponentIndex flatMap (centredCover 1 0)) := ⟨fun ⟨i, a⟩ => by
      induction a using ZerothHomotopy.rec with
      | mk x =>
        exact Set.eq_empty_iff_forall_notMem.mp
          (centredCover_eq_empty (s := 1) (t := 0) le_rfl i) _ x.2⟩
    change IsZero (simplicialHomology (mapper flatMap (centredCover 1 0)) k 0)
    rw [mapper_eq_bot_of_isEmpty_componentIndex]
    exact TDA.Persistence.isZero_simplicialHomology_bot k 0
  have hpos : ∀ t, 0 < t → ¬ IsZero ((centredModule k).obj t) := by
    intro t ht
    have hmem : flatMap 0 ∈ centredCover 1 t 0 := by
      rw [mem_centredCover_iff]
      simpa [scaleMap] using ht
    exact not_isZero_H0 k flatMap (centredCover 1 t) ⟨0, ZerothHomotopy.mk ⟨0, hmem⟩⟩
  refine ⟨hzero, hpos, fun m c h => ?_⟩
  obtain ⟨δ, hδ, hcell⟩ := exists_pos_cellIndex_eq c
  have := h.isIso_map 0 δ hδ.le hcell.symm
  exact hpos δ hδ (hzero.of_iso (asIso (structureMap (centredModule k) hδ.le)).symm)

end Controls


end

end TDA.Mapper.RefinementHomologyDiagramExamples
