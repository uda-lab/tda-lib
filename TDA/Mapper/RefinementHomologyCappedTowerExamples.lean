import TDA.Mapper.RefinementHomologyCappedTower
import TDA.Mapper.RefinementHomologyLowerBound
import TDA.Mapper.RefinementHomologyBarcodeExamples
import TDA.Simplicial.H0Augmentation

/-!
# Capped centred step tower fixtures

The maps are the constants `0` and `1/2` on the one-point space, with one label of integer label
`0`, base `0` and spacing `1`; the stage of radius `r` is then `(-r, r)`, which contains `0` for
`r > 0` and never contains `1/2` for `r ≤ 1/2`. Diagrams are in degree `0` over any field.

* **Exact value `1/2`.** On the uniform grid `0, 1/4, 1/2, 3/4, 1`, the two capped centred
  diagrams are at bottleneck distance exactly `1/2`. The uniform-grid bound gives `≤ 1/2`; for
  `ε < 1/2`, the map of `0` from radius `1/4` to `1/4 + 2ε` is nonzero on `H₀`, while the stage
  of `1/2` at radius `1/4 + ε < 3/4` has radius at most `1/2` and no component. The perturbation
  bound `δ + μ = 3/4` of the general grid is not attained.
* **Zero perturbation.** For one map on the same grid, the uniform-grid bound with `p = 0` gives
  bottleneck distance `0`.
* **Mesh comparison.** For the constant `0`, the capped centred diagrams on the grids
  `0, 1/2, 1` and `0, 1/4, 1/2, 3/4, 1` are at bottleneck distance at most `1/2`.
* **Graph-PL heights.** On the single edge with heights `(0, 1)` and `(0, 3/2)`, three labels
  `0, 1, 2`, base `0`, spacing `1` and the uniform grid of spacing `1/4` from `0` to `2`, the
  capped centred diagrams in every degree are at bottleneck distance at most `1/2`; every
  finiteness instance is synthesized.
* **Negative control: the full last stage.** On the grid `0, 1/4` with stages `∅`, radius `0` and
  radius `1/4`, without a full stage, the step module of `1/2` is zero at every radius while the
  module of `0` has a nonzero map from radius `1/4` to every larger radius. The bottleneck distance
  is `⊤`, and the numbers of essential bars differ, although the maps differ by `1/2`. Truncating
  the centred tower at a finite radius without the full stage admits no perturbation bound.
* **Negative control: the mesh term.** On the grid `0, 1/4, 1` of mesh `3/4`, the capped centred
  diagrams of `0` and `1/2` are at bottleneck distance at least `3/4 > 1/2`, so the bound `δ`
  without a mesh term fails; the perturbation bound gives at most `5/4`.
-/

namespace TDA.Mapper.RefinementHomologyCappedTowerExamples

open CategoryTheory
open TDA.Topology TDA.Simplicial TDA.Persistence TDA.Persistence.FiniteConstructible
open TDA.Reeb TDA.Reeb.GraphPL
open TDA.Reeb.Examples.GraphRealization (edgeGraph)
open TDA.Mapper.RefinementHomologyExamples (subsingleton_zerothHomotopy)
open TDA.Mapper.RefinementHomologyBarcodeExamples (h01)
open scoped NNReal ENNReal

noncomputable section

/-! ## Constant maps on the one-point space -/

/-- The constant map with value `y` on the one-point space. -/
abbrev constMap (y : ℝ) : C(Unit, ℝ) :=
  ContinuousMap.const Unit y

/-- The label `0` for the single label. -/
abbrev zeroLabel : Unit → ℤ :=
  fun _ => 0

local instance {X Y ι : Type} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y))
    (U : ι → Set Y) : LinearOrder (ComponentIndex f U) := by
  classical
  exact linearOrderOfSTO WellOrderingRel

private instance {Y ι : Type} [TopologicalSpace Y] [Finite ι] (f : C(Unit, Y)) (U : ι → Set Y)
    (n : ℕ) : Finite (Face (mapper f U) n) :=
  have : ∀ i, Finite (ZerothHomotopy (PullbackSpace f U i)) := fun i =>
    have := subsingleton_zerothHomotopy (Z := PullbackSpace f U i)
    inferInstance
  have : Finite (ComponentIndex f U) :=
    inferInstanceAs (Finite (Σ i, ZerothHomotopy (PullbackSpace f U i)))
  faceFiniteOfTotalFinite _ n

/-- A Mapper vertex makes every refinement map nonzero on `H₀` over a field. -/
private theorem mapperHomologyMap_ne_zero (k : Type) [Field k] {X Y ι κ : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) {U : ι → Set Y} {V : κ → Set Y}
    [LinearOrder (ComponentIndex f U)] [LinearOrder (ComponentIndex f V)] (r : Refinement U V)
    (a : ComponentIndex f U) : mapperHomologyMap k f r 0 ≠ 0 := by
  intro h0
  let σ : Face (mapper f U) 0 := ⟨{a}, componentIndex_supported f U a, Finset.card_singleton a⟩
  have hclass := simplicialHomologyMap_class k (mapperMap f r) 0 (zeroVertexCycle _ k σ)
    (zeroVertexCycle _ k (vertexImageFace (mapperMap f r) σ (fun i j _ => Fin.ext (by omega))))
    (vertexChainMap_vertex k _ _ 1)
  rw [← mapperHomologyMap_def, h0] at hclass
  exact simplicialHomologyClass_zeroVertexCycle_ne_zero _ k _ hclass.symm

/-- A stage of positive radius has a component of the constant `0`. -/
private theorem nonempty_zeroComponent {m : ℕ} (c : Fin m ↪o ℝ) (i : Fin (m + 1))
    (hi : 0 < stageRadius c i) :
    Nonempty (ComponentIndex (constMap 0) fun w =>
      (cappedCentredCover 0 1 zeroLabel c i w : Set ℝ)) := by
  obtain rfl | ⟨j, rfl⟩ := i.eq_zero_or_eq_succ
  · exact absurd hi (by simp)
  exact ⟨⟨(), ZerothHomotopy.mk ⟨(), (mem_cappedCentredCover_succ_iff 0 1 zeroLabel c j () 0).mpr
    (by simpa using hi)⟩⟩⟩

/-- A stage of radius at most `1/2` has no component of the constant `1/2`. -/
private theorem isEmpty_halfComponent {m : ℕ} (c : Fin m ↪o ℝ) (i : Fin (m + 1))
    (hi : stageRadius c i ≤ ((1 / 2 : ℝ) : EReal)) :
    IsEmpty (ComponentIndex (constMap (1 / 2)) fun w =>
      (cappedCentredCover 0 1 zeroLabel c i w : Set ℝ)) := by
  refine ⟨fun ⟨w, z⟩ => ?_⟩
  obtain rfl | ⟨j, rfl⟩ := i.eq_zero_or_eq_succ
  · exact isEmptyElim w
  induction z using ZerothHomotopy.rec with
  | mk x =>
    have hx := (mem_cappedCentredCover_succ_iff 0 1 zeroLabel c j w (1 / 2)).mp x.2
    have : ((1 / 2 : ℝ) : EReal) < (1 / 2 : ℝ) := by
      refine lt_of_le_of_lt ?_ (hx.trans_le hi)
      norm_num
    exact lt_irrefl _ this

/-- Below the grid value `c (q + 1)`, the stage radius is at most `c q`. -/
private theorem stageRadius_cellIndex_le {m : ℕ} (c : Fin m ↪o ℝ) (q : Fin m)
    (hq : q.val + 1 < m) {u : ℝ} (hu : u < c ⟨q.val + 1, hq⟩) :
    stageRadius c (cellIndex c u) ≤ (c q : EReal) := by
  obtain h | ⟨j, h⟩ := (cellIndex c u).eq_zero_or_eq_succ
  · rw [h, stageRadius_zero]
    exact bot_le
  have hju := ((cellIndex_eq_succ_iff c j u).mp h).1
  have hjq : j.val < q.val + 1 := by
    by_contra hge
    exact (hu.trans_le (hju.trans' (c.monotone (Fin.le_def.mpr (by simp; omega))))).false
  rw [h, stageRadius_succ_of_lt c j (by omega)]
  exact EReal.coe_le_coe_iff.mpr (c.monotone (Fin.le_def.mpr (by omega)))

/-- The degree-zero Mapper homology module of a constant along the capped centred stages. -/
abbrev constModule (k : Type) [Field k] (y : ℝ) {m : ℕ} (c : Fin m ↪o ℝ) :
    PModule.{0,0,0} k ℝ :=
  mapperHomologyPModule k (constMap y)
    (stepTower c fun i w => (cappedCentredCover 0 1 zeroLabel c i w : Set ℝ))
    (stepRefinement c _ fun h => cappedCentredRefinement 0 1 zeroLabel c h) 0

/-- For every `ε < r`, if the radius `c j` plus `ε` stays below `c (q + 1)` with `c q ≤ 1/2`,
the capped centred modules of `0` and `1/2` are at interleaving distance at least `r`. -/
private theorem le_realInterleavingDistance_const (k : Type) [Field k] {m : ℕ}
    (c : Fin m ↪o ℝ) (j : Fin m) (hj : j.val + 1 < m) (hcj : 0 < c j) (q : Fin m)
    (hq : q.val + 1 < m) (hcq : c q ≤ 1 / 2) {r : ℝ≥0∞}
    (hr : ∀ ε : ℝ≥0, (ε : ℝ≥0∞) < r → c j + ε < c ⟨q.val + 1, hq⟩) :
    r ≤ realInterleavingDistance (constModule k 0 c) (constModule k (1 / 2) c) := by
  refine le_realInterleavingDistance_mapperHomologyPModule_of_isEmpty_face k _ _ 0
    fun ε hε => ⟨c j, by simp, ?_, ?_⟩
  · have := isEmpty_halfComponent c _ ((stageRadius_cellIndex_le c q hq (hr ε hε)).trans
      (EReal.coe_le_coe_iff.mpr hcq))
    exact isEmpty_face_mapper _ _ 0
  · obtain ⟨a⟩ := nonempty_zeroComponent c (cellIndex c (c j)) (by
      rw [cellIndex_critical, stageRadius_succ_of_lt c j hj]
      exact EReal.coe_pos.mpr hcj)
    exact mapperHomologyMap_ne_zero k _ _ a

/-! ## Exact value `1/2` -/

/-- The uniform grid `0, 1/4, 1/2, 3/4, 1`. -/
abbrev quarterGrid : Fin 5 ↪o ℝ :=
  uniformGrid 0 (1 / 4) (by norm_num) 5

/-- The degree-zero capped centred diagram of the constant `y` on the grid `c`. -/
abbrev constDiagram (k : Type) [Field k] (y : ℝ) {m : ℕ} (c : Fin m ↪o ℝ) : Diagram ℝ :=
  cappedCentredDiagram k (constMap y) 0 1 zeroLabel c 0

private theorem abs_const_sub :
    ∀ x : Unit, |constMap 0 x - constMap (1 / 2) x| ≤ ((1 / 2 : ℝ≥0) : ℝ) :=
  fun _ => by norm_num [abs_of_neg]

/-- On the grid `0, 1/4, 1/2, 3/4, 1`, the capped centred diagrams of the constants `0` and `1/2`
are at bottleneck distance exactly `1/2`, over every field. -/
theorem const_bottleneck_eq (k : Type) [Field k] :
    bottleneck (constDiagram k 0 quarterGrid) (constDiagram k (1 / 2) quarterGrid) =
      ((1 / 2 : ℝ≥0) : ℝ≥0∞) := by
  apply le_antisymm
  · exact bottleneck_cappedCentredDiagram_uniformGrid_le k 0 1 zeroLabel 0 0 (1 / 4) _ 5
      abs_const_sub 2 (by norm_num)
  · rw [bottleneck_cappedCentredDiagram_eq]
    refine le_realInterleavingDistance_const k quarterGrid 1 (by norm_num) (by norm_num) 2
      (by norm_num) (by norm_num) fun ε hε => ?_
    have : (ε : ℝ) < 1 / 2 := by exact_mod_cast hε
    simp only [quarterGrid, uniformGrid_apply]
    norm_num
    linarith

/-- For one map, the uniform-grid bound with `p = 0` gives bottleneck distance `0`. -/
theorem const_bottleneck_self (k : Type) [Field k] :
    bottleneck (constDiagram k 0 quarterGrid) (constDiagram k 0 quarterGrid) = 0 :=
  le_antisymm ((bottleneck_cappedCentredDiagram_uniformGrid_le k 0 1 zeroLabel 0 0 (1 / 4) _ 5
    (f := constMap 0) (g := constMap 0) (δ := 0) (fun _ => by simp) 0 (by simp)).trans_eq
      ENNReal.coe_zero) bot_le

/-! ## Mesh comparison -/

/-- The uniform grid `0, 1/2, 1`. -/
abbrev halfGrid : Fin 3 ↪o ℝ :=
  uniformGrid 0 (1 / 2) (by norm_num) 3

/-- For the constant `0`, the capped centred diagrams on the grids `0, 1/2, 1` and
`0, 1/4, 1/2, 3/4, 1` are at bottleneck distance at most `1/2`. -/
theorem const_bottleneck_grid_le (k : Type) [Field k] :
    bottleneck (constDiagram k 0 halfGrid) (constDiagram k 0 quarterGrid) ≤
      ((1 / 2 : ℝ≥0) : ℝ≥0∞) :=
  bottleneck_cappedCentredDiagram_grid_le k 0 1 zeroLabel 0
    (fun _ _ hij => by rw [uniformGrid_of_val_eq_succ _ _ _ hij]; norm_num)
    (fun _ _ hij => by rw [uniformGrid_of_val_eq_succ _ _ _ hij]; norm_num)
    (by norm_num) (by norm_num)

/-! ## Graph-PL heights -/

/-- Heights `0` and `3/2` on the two vertices of the single edge. -/
def h032 : Bool → ℝ
  | false => 0
  | true => 3 / 2

/-- The uniform grid of spacing `1/4` from `0` to `2`. -/
abbrev edgeGrid : Fin 9 ↪o ℝ :=
  uniformGrid 0 (1 / 4) (by norm_num) 9

/-- On the single edge with heights `(0, 1)` and `(0, 3/2)`, the labels `0, 1, 2`, base `0`,
spacing `1` and the uniform grid of spacing `1/4` from `0` to `2`, the capped centred diagrams
in every degree are at bottleneck distance at most `1/2`; all finiteness instances are
synthesized. -/
theorem edge_bottleneck_le (k : Type) [Field k] (n : ℕ) :
    bottleneck (cappedCentredDiagram k (plHeight edgeGraph h01) 0 1 (fun w : Fin 3 => (w : ℤ))
        edgeGrid n)
      (cappedCentredDiagram k (plHeight edgeGraph h032) 0 1 (fun w : Fin 3 => (w : ℤ))
        edgeGrid n) ≤ ((1 / 2 : ℝ≥0) : ℝ≥0∞) :=
  bottleneck_cappedCentredDiagram_plHeight_uniformGrid_le k edgeGraph 0 1 _ n
    (fun v => by cases v <;> norm_num [h01, h032, abs_of_neg]) 0 (1 / 4) _ 9 2 (by norm_num)

/-! ## Negative control: the full last stage -/

/-- Labels of the uncapped stages: none at stage `0`, one later. -/
def openIndex (i : Fin 3) : Type :=
  {_u : Unit // i ≠ 0}

/-- Stage `0` has no labels. -/
instance openIndex_isEmpty : IsEmpty (openIndex 0) :=
  ⟨fun w => w.2 rfl⟩

/-- Every stage has finitely many labels. -/
instance openIndex_finite (i : Fin 3) : Finite (openIndex i) :=
  inferInstanceAs (Finite {_u : Unit // i ≠ 0})

/-- The uncapped stages on the grid `0, 1/4`: stage `i ≥ 1` is `(-(i - 1)/4, (i - 1)/4)`. -/
def openCover (i : Fin 3) (_ : openIndex i) : Set ℝ :=
  Set.Ioo (-(((i : ℕ) - 1 : ℕ) / 4 : ℝ)) (((i : ℕ) - 1 : ℕ) / 4 : ℝ)

/-- The refinements of the uncapped stages select the single label. -/
def openRefinement {i j : Fin 3} (h : i ≤ j) : Refinement (openCover i) (openCover j) where
  selector w := ⟨(), fun hj => w.2 (le_antisymm (hj ▸ h) (Fin.zero_le _))⟩
  subset _ := by
    have : (((i : ℕ) - 1 : ℕ) : ℝ) ≤ ((j : ℕ) - 1 : ℕ) :=
      Nat.cast_le.mpr (Nat.sub_le_sub_right (Fin.le_def.mp h) 1)
    exact Set.Ioo_subset_Ioo (by linarith) (by linarith)

/-- The uniform grid `0, 1/4`. -/
abbrev shortGrid : Fin 2 ↪o ℝ :=
  uniformGrid 0 (1 / 4) (by norm_num) 2

/-- The degree-zero Mapper homology module of a constant along the uncapped step tower. -/
abbrev openModule (k : Type) [Field k] (y : ℝ) : PModule.{0,0,0} k ℝ :=
  mapperHomologyPModule k (constMap y) (stepTower shortGrid openCover)
    (stepRefinement shortGrid openCover openRefinement) 0

/-- Without a full last stage, the step diagrams of the constants `0` and `1/2` on the grid
`0, 1/4` are at bottleneck distance `⊤` and have different numbers of essential bars, although
the maps differ by `1/2`. -/
theorem open_bottleneck_eq_top (k : Type) [Field k] :
    (∀ x, |constMap 0 x - constMap (1 / 2) x| ≤ 1 / 2) ∧
      bottleneck (stepMapperDiagram k (constMap 0) shortGrid openCover openRefinement 0)
        (stepMapperDiagram k (constMap (1 / 2)) shortGrid openCover openRefinement 0) = ⊤ ∧
      (essentialPart (stepMapperDiagram k (constMap 0) shortGrid openCover openRefinement
        0).points).card ≠
      (essentialPart (stepMapperDiagram k (constMap (1 / 2)) shortGrid openCover openRefinement
        0).points).card := by
  have hhalf : ∀ i, IsEmpty (ComponentIndex (constMap (1 / 2)) (openCover i)) := fun i =>
    ⟨fun ⟨w, z⟩ => by
      induction z using ZerothHomotopy.rec with
      | mk x =>
        have hx : (1 / 2 : ℝ) < (((i : ℕ) - 1 : ℕ) / 4 : ℝ) := x.2.2
        have : (((i : ℕ) - 1 : ℕ) : ℝ) ≤ 1 := by
          exact_mod_cast (by omega : (i : ℕ) - 1 ≤ 1)
        linarith⟩
  have htop : realInterleavingDistance (openModule k 0) (openModule k (1 / 2)) = ⊤ := by
    refine top_le_iff.mp (le_realInterleavingDistance_mapperHomologyPModule_of_isEmpty_face k _ _
      0 fun ε _ => ⟨1 / 4, by simp, isEmpty_face_mapper _ _ 0, ?_⟩)
    have hcell : ∀ t : ℝ, 1 / 4 ≤ t → cellIndex shortGrid t = 2 := fun t ht =>
      cellIndex_of_last_le shortGrid t (by simpa using ht)
    obtain ⟨a⟩ :
        Nonempty (ComponentIndex (constMap 0) (openCover (cellIndex shortGrid (1 / 4)))) := by
      rw [hcell _ le_rfl]
      exact ⟨⟨⟨(), by decide⟩, ZerothHomotopy.mk ⟨(), by norm_num [openCover]⟩⟩⟩
    exact mapperHomologyMap_ne_zero k _ _ a
  have hM := isConstructible_stepTower shortGrid openCover k (constMap 0) openRefinement 0
  have hN := isConstructible_stepTower shortGrid openCover k (constMap (1 / 2)) openRefinement 0
  refine ⟨fun _ => by norm_num [abs_of_neg], ?_, ?_⟩
  · exact (bottleneck_eq_distance hM hN _ _).trans htop
  · exact (distance_eq_top_iff_essential_card_ne hM hN _ _).mp htop

/-! ## Negative control: the mesh term -/

/-- The grid `0, 1/4, 1` of mesh `3/4`. -/
def coarseGrid : Fin 3 ↪o ℝ :=
  OrderEmbedding.ofStrictMono ![0, 1 / 4, 1] (by
    intro i j hij
    fin_cases i <;> fin_cases j <;> (simp_all; try norm_num))

/-- On the grid `0, 1/4, 1`, the capped centred diagrams of the constants `0` and `1/2` are at
bottleneck distance at least `3/4` and at most `5/4`; in particular the bound `1/2` given by the
pointwise distance alone fails. -/
theorem coarse_bottleneck_bounds (k : Type) [Field k] :
    ((3 / 4 : ℝ≥0) : ℝ≥0∞) ≤ bottleneck (constDiagram k 0 coarseGrid)
        (constDiagram k (1 / 2) coarseGrid) ∧
      bottleneck (constDiagram k 0 coarseGrid) (constDiagram k (1 / 2) coarseGrid) ≤
        ((1 / 2 : ℝ≥0) : ℝ≥0∞) + ((3 / 4 : ℝ≥0) : ℝ≥0∞) ∧
      ¬ bottleneck (constDiagram k 0 coarseGrid) (constDiagram k (1 / 2) coarseGrid) ≤
        ((1 / 2 : ℝ≥0) : ℝ≥0∞) := by
  have hlow : ((3 / 4 : ℝ≥0) : ℝ≥0∞) ≤
      bottleneck (constDiagram k 0 coarseGrid) (constDiagram k (1 / 2) coarseGrid) := by
    rw [bottleneck_cappedCentredDiagram_eq]
    refine le_realInterleavingDistance_const k coarseGrid 1 (by norm_num)
      (by norm_num [coarseGrid]) 1 (by norm_num) (by norm_num [coarseGrid]) fun ε hε => ?_
    have : (ε : ℝ) < 3 / 4 := by exact_mod_cast hε
    simp only [coarseGrid]
    norm_num
    linarith
  refine ⟨hlow, ?_, fun h => ?_⟩
  · refine bottleneck_cappedCentredDiagram_le k 0 1 zeroLabel 0 abs_const_sub fun i j hij => ?_
    fin_cases i <;> fin_cases j <;> simp_all [coarseGrid] <;> norm_num
  · have := hlow.trans h
    rw [ENNReal.coe_le_coe] at this
    have : ((3 / 4 : ℝ≥0) : ℝ) ≤ ((1 / 2 : ℝ≥0) : ℝ) := by exact_mod_cast this
    norm_num at this

end

end TDA.Mapper.RefinementHomologyCappedTowerExamples
