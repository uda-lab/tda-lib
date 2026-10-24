import TDA.Mapper.RefinementHomologyCappedMapPair
import TDA.Mapper.RefinementHomologyCappedTowerExamples
import TDA.Mapper.RefinementHomologyEssential
import TDA.Mapper.RefinementHomologyLowerBound
import TDA.Mapper.RefinementHomologyBarcode
import TDA.Persistence.LogScaleDiagram
import TDA.Reeb.GraphRealizationExamples
import TDA.Reeb.GraphPLVertexPerturbationExamples

/-!
# Fixtures for capped centred diagrams from height-map pairs

These fixtures exercise recovery from a uniform bound, a different-domain edge-to-point pair
whose bottleneck distance lies in `[1/4, 1/2]`, and a Bool-to-Unit negative control where
height-preserving maps exist but the required composite path condition does not.
-/

namespace TDA.Mapper.RefinementHomologyCappedMapPairExamples

open TDA.Topology TDA.Simplicial TDA.Persistence TDA.Reeb TDA.Reeb.GraphPL
open TDA.Reeb.GraphRealization
open TDA.Reeb.Examples.GraphRealization (edgeGraph d₀ half pointGraph edgeHomeomorph)
open TDA.Reeb.Examples.GraphPLVertexPerturbation (tilted)
open TDA.Mapper.RefinementHomologyCappedTowerExamples (quarterGrid edgeGrid constMap zeroLabel)
open TDA.Persistence.FiniteConstructible
open scoped NNReal ENNReal

noncomputable section

local instance anyComponentOrder {X Y I : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (U : I → Set Y) : LinearOrder (ComponentIndex f U) := by
  classical
  exact linearOrderOfSTO WellOrderingRel

private instance unitIntervalPathConnectedSpace : PathConnectedSpace unitInterval := by
  apply isPathConnected_iff_pathConnectedSpace.mp
  exact (convex_Icc (𝕜 := ℝ) (0 : ℝ) 1).isPathConnected ⟨0, by norm_num⟩

private instance finiteZerothHomotopyOfFiniteDomain {X : Type} [TopologicalSpace X] [Finite X] :
    Finite (ZerothHomotopy X) :=
  Finite.of_surjective ZerothHomotopy.mk ZerothHomotopy.mk_surjective

private instance finiteMapperFaceOfFiniteDomain {X Y I : Type} [TopologicalSpace X]
    [TopologicalSpace Y] [Finite X] [Finite I] (f : C(X, Y)) (U : I → Set Y) (n : ℕ) :
    Finite (Face (mapper f U) n) := by
  have hcomponents : Finite (ComponentIndex f U) := by
    have hpullbacks : ∀ i, Finite (ZerothHomotopy (PullbackSpace f U i)) := by
      intro i
      infer_instance
    exact inferInstanceAs (Finite (Σ i, ZerothHomotopy (PullbackSpace f U i)))
  letI : Finite (ComponentIndex f U) := hcomponents
  letI : Fintype (ComponentIndex f U) := Fintype.ofFinite _
  exact faceFiniteOfTotalFinite _ n

/-! ## Fixed-space recovery -/

private theorem constantHalfBound (x : Unit) :
    |constMap 0 x - constMap (1 / 2) x| ≤ ((1 / 2 : ℝ≥0) : ℝ) := by
  norm_num [constMap]

private theorem quarterGridHalfRadius (t : ℝ) :
    stageRadius quarterGrid (cellIndex quarterGrid t) + (1 / 2 : ℝ) ≤
      stageRadius quarterGrid (cellIndex quarterGrid (t + (1 / 2 : ℝ≥0))) := by
  convert stageRadius_add_le_uniformGrid 0 (1 / 4) (by norm_num) 5 2 t using 1 <;>
    norm_num [quarterGrid, uniformGrid_apply]

/-- The `ofUniformBound` recovery theorem gives the known `1/2` bound on the quarter grid. -/
theorem constant_pair_recovery_le_half :
    bottleneck
      (cappedCentredDiagram ℚ (constMap 0) 0 1 zeroLabel quarterGrid 0)
      (cappedCentredDiagram ℚ (constMap (1 / 2)) 0 1 zeroLabel quarterGrid 0) ≤ 1 / 2 := by
  simpa using bottleneck_cappedCentredDiagram_pair_le_ofUniformBound ℚ 0 1 zeroLabel 0
    constantHalfBound quarterGridHalfRadius quarterGridHalfRadius

/-! ## Different domains: edge to point -/

private instance edgePathConnected : PathConnectedSpace (Realization edgeGraph) :=
  edgeHomeomorph.symm.surjective.pathConnectedSpace edgeHomeomorph.symm.continuous

private theorem pointRealization_eq (x : Realization pointGraph) :
    x = vertex pointGraph () := Subsingleton.elim _ _

private def edgeHeight : C(Realization edgeGraph, ℝ) := plHeight edgeGraph tilted

private def pointHeight : C(Realization pointGraph, ℝ) :=
  plHeight pointGraph (fun _ => (1 / 2 : ℝ))

private def edgeLabels (w : Fin 3) : ℤ := (w : ℤ)

private theorem edgeLabels_dist_from_half (w : Fin 3) :
    (1 / 2 : ℝ) ≤ |(1 / 2 : ℝ) - edgeLabels w| := by
  fin_cases w <;> norm_num [edgeLabels]

private instance edgeCappedFacesFinite (n : ℕ) : ∀ i : Fin 10, Finite (Face
    (mapper edgeHeight (fun w : cappedIndex (Fin 3) i =>
      (cappedCentredCover 0 1 edgeLabels edgeGrid i w : Set ℝ))) n) := by
  intro i
  change Finite (Face (mapper (plHeight edgeGraph tilted) (fun w : cappedIndex (Fin 3) i =>
    (cappedCentredCover 0 1 edgeLabels edgeGrid i w : Set ℝ))) n)
  exact TDA.Mapper.GraphPL.finite_mapperFace edgeGraph tilted
    (cappedCentredCover 0 1 edgeLabels edgeGrid i) n

private instance pointCappedFacesFinite (n : ℕ) : ∀ i : Fin 10, Finite (Face
    (mapper pointHeight (fun w : cappedIndex (Fin 3) i =>
      (cappedCentredCover 0 1 edgeLabels edgeGrid i w : Set ℝ))) n) := by
  intro i
  change Finite (Face (mapper (plHeight pointGraph (fun _ => (1 / 2 : ℝ)))
    (fun w : cappedIndex (Fin 3) i =>
      (cappedCentredCover 0 1 edgeLabels edgeGrid i w : Set ℝ))) n)
  exact TDA.Mapper.GraphPL.finite_mapperFace pointGraph (fun _ => (1 / 2 : ℝ))
    (cappedCentredCover 0 1 edgeLabels edgeGrid i) n

private def edgeToPoint : C(Realization edgeGraph, Realization pointGraph) :=
  ContinuousMap.const _ (vertex pointGraph ())

private def pointToEdge : C(Realization pointGraph, Realization edgeGraph) :=
  ContinuousMap.const _ (edgePoint edgeGraph d₀ half)

private theorem edgeHeight_mem_Icc (x : Realization edgeGraph) :
    edgeHeight x ∈ Set.Icc (0 : ℝ) 1 :=
  plHeight_mem_Icc_of_forall (m := 0) (M := 1)
    (fun b => by cases b <;> norm_num [tilted]) x

private theorem edgeMidpoint_height : edgeHeight (edgePoint edgeGraph d₀ half) = 1 / 2 := by
  simp [edgeHeight, GraphPL.plHeight_edgePoint, GraphPL.dartHeight, tilted, d₀, half]

private theorem pointHeight_apply (x : Realization pointGraph) : pointHeight x = 1 / 2 := by
  rw [pointRealization_eq x]
  simp [pointHeight]

private def edgePointPair : HeightMapPair edgeHeight pointHeight (1 / 2 : ℝ≥0) where
  φ := edgeToPoint
  ψ := pointToEdge
  hφ x := by
    rw [pointHeight_apply]
    change |(1 / 2 : ℝ) - edgeHeight x| ≤ 1 / 2
    rw [abs_le]
    have hx := edgeHeight_mem_Icc x
    constructor <;> linarith [hx.1, hx.2]
  hψ x := by
    change |edgeHeight (edgePoint edgeGraph d₀ half) - pointHeight x| ≤ 1 / 2
    rw [edgeMidpoint_height, pointHeight_apply]
    norm_num
  hψφ x := by
    let γ : Path x (pointToEdge (edgeToPoint x)) := by
      simpa [pointToEdge, edgeToPoint] using
        (PathConnectedSpace.somePath x (edgePoint edgeGraph d₀ half))
    refine ⟨γ, ?_⟩
    intro t
    have h₁ := edgeHeight_mem_Icc (γ t)
    have h₂ := edgeHeight_mem_Icc x
    change |edgeHeight (γ t) - edgeHeight x| ≤ _
    rw [abs_le]
    have hsum : ((1 / 2 : ℝ≥0) : ℝ) + ((1 / 2 : ℝ≥0) : ℝ) = 1 := by norm_num
    rw [hsum]
    constructor <;> linarith [h₁.1, h₁.2, h₂.1, h₂.2]
  hφψ x := by
    rw [pointRealization_eq x]
    refine ⟨Path.refl _, ?_⟩
    intro t
    change |pointHeight (vertex pointGraph ()) - pointHeight (vertex pointGraph ())| ≤
      ((1 / 2 : ℝ≥0) + (1 / 2 : ℝ≥0) : ℝ≥0)
    rw [sub_self, abs_zero]
    norm_num

private theorem pointIndexEmpty (i : Fin 10)
    (hi : stageRadius edgeGrid i ≤ ((1 / 2 : ℝ) : EReal)) :
    IsEmpty (ComponentIndex pointHeight fun (w : cappedIndex (Fin 3) i) =>
      (cappedCentredCover 0 1 edgeLabels edgeGrid i w : Set ℝ)) := by
  refine ⟨fun ⟨w, z⟩ => ?_⟩
  obtain rfl | ⟨j, rfl⟩ := i.eq_zero_or_eq_succ
  · exact isEmptyElim w
  induction z using ZerothHomotopy.rec with
  | mk x =>
    have hxmem : (1 / 2 : ℝ) ∈
        (cappedCentredCover 0 1 edgeLabels edgeGrid j.succ w : Set ℝ) := by
      simpa [pointHeight_apply] using x.2
    have hx := (mem_cappedCentredCover_succ_iff 0 1 edgeLabels
      edgeGrid j w (1 / 2)).mp hxmem
    have hdist : ((1 / 2 : ℝ) : EReal) ≤
        ((|1 / 2 - (0 + edgeLabels w * 1)| : ℝ) : EReal) := by
      rw [EReal.coe_le_coe_iff]
      simpa [edgeLabels] using edgeLabels_dist_from_half (show Fin 3 from w)
    have hx' : ((1 / 2 : ℝ) : EReal) < stageRadius edgeGrid j.succ := by
      exact lt_of_le_of_lt hdist hx
    exact (not_lt_of_ge hi) hx'

private theorem edgeQuarterComponent :
    Nonempty (ComponentIndex edgeHeight fun (w : cappedIndex (Fin 3) (cellIndex edgeGrid (1 / 4))) =>
      (cappedCentredCover 0 1 edgeLabels edgeGrid
        (cellIndex edgeGrid (1 / 4)) w : Set ℝ)) := by
  have hidx : cellIndex edgeGrid (1 / 4) = (1 : Fin 9).succ := by
    simpa [edgeGrid, uniformGrid_apply] using (cellIndex_critical edgeGrid (1 : Fin 9))
  rw [hidx]
  change Nonempty (ComponentIndex edgeHeight (fun w : Fin 3 =>
    (cappedCentredCover 0 1 edgeLabels edgeGrid (1 : Fin 9).succ w : Set ℝ)))
  refine ⟨⟨0, ZerothHomotopy.mk ⟨vertex edgeGraph false, ?_⟩⟩⟩
  norm_num [cappedCentredCover, cappedIndex, centredInterval, edgeHeight, plHeight,
    tilted, edgeLabels, edgeGrid, uniformGrid_apply]

private theorem edgePoint_bottleneck_eq_distance :
    bottleneck
      (cappedCentredDiagram ℚ edgeHeight 0 1 edgeLabels edgeGrid 0)
      (cappedCentredDiagram ℚ pointHeight 0 1 edgeLabels edgeGrid 0) =
      realInterleavingDistance
        (mapperHomologyPModule ℚ edgeHeight
          (stepTower edgeGrid fun i w =>
            (cappedCentredCover 0 1 edgeLabels edgeGrid i w : Set ℝ))
          (stepRefinement edgeGrid _ fun h =>
            cappedCentredRefinement 0 1 edgeLabels edgeGrid h) 0)
        (mapperHomologyPModule ℚ pointHeight
          (stepTower edgeGrid fun i w =>
            (cappedCentredCover 0 1 edgeLabels edgeGrid i w : Set ℝ))
          (stepRefinement edgeGrid _ fun h =>
            cappedCentredRefinement 0 1 edgeLabels edgeGrid h) 0) := by
  change bottleneck
      (moduleDiagram edgeGrid
        (mapperHomologyPModule ℚ edgeHeight
          (stepTower edgeGrid fun i w =>
            (cappedCentredCover 0 1 edgeLabels edgeGrid i w : Set ℝ))
          (stepRefinement edgeGrid _ fun h =>
            cappedCentredRefinement 0 1 edgeLabels edgeGrid h) 0) _)
      (moduleDiagram edgeGrid
        (mapperHomologyPModule ℚ pointHeight
          (stepTower edgeGrid fun i w =>
            (cappedCentredCover 0 1 edgeLabels edgeGrid i w : Set ℝ))
          (stepRefinement edgeGrid _ fun h =>
            cappedCentredRefinement 0 1 edgeLabels edgeGrid h) 0) _) = _
  exact bottleneck_eq_distance
    (isConstructible_stepTower edgeGrid _ ℚ edgeHeight _ 0)
    (isConstructible_stepTower edgeGrid _ ℚ pointHeight _ 0) _ _

private theorem edge_point_pair_lower_bound :
    (1 / 4 : ℝ≥0∞) ≤ bottleneck
      (cappedCentredDiagram ℚ edgeHeight 0 1 edgeLabels edgeGrid 0)
      (cappedCentredDiagram ℚ pointHeight 0 1 edgeLabels edgeGrid 0) := by
  rw [edgePoint_bottleneck_eq_distance]
  refine le_realInterleavingDistance_of_structureMap_ne_zero (r := (1 / 4 : ℝ≥0∞)) ?_
  intro ε hε
  have hεnn : ε < (1 / 4 : ℝ≥0) := by
    have hεcoe : (ε : ℝ≥0∞) < ((1 / 4 : ℝ≥0) : ℝ≥0∞) := by simpa using hε
    exact ENNReal.coe_lt_coe.1 hεcoe
  have hε' : (ε : ℝ) < 1 / 4 := NNReal.coe_lt_coe.mpr hεnn
  let t : ℝ := 1 / 4
  have h : t ≤ t + ((ε + ε : ℝ≥0) : ℝ) := by
    dsimp [t]
    linarith [ε.coe_nonneg]
  refine ⟨t, h, ?_, ?_⟩
  · change Subsingleton (simplicialHomology
      (mapper pointHeight (fun w : cappedIndex (Fin 3) (cellIndex edgeGrid (t + ε)) =>
        (cappedCentredCover 0 1 edgeLabels edgeGrid
          (cellIndex edgeGrid (t + ε)) w : Set ℝ))) ℚ 0)
    have hparam : t + (ε : ℝ) < 1 / 2 := by dsimp [t]; linarith
    have hindex := (cellIndex edgeGrid).monotone (le_of_lt hparam)
    have hquarter : edgeGrid (2 : Fin 9) = (1 / 2 : ℝ) := by
      norm_num [edgeGrid, uniformGrid_apply]
    have hhalf : cellIndex edgeGrid (1 / 2) = (2 : Fin 9).succ := by
      rw [← hquarter, cellIndex_critical]
    have hradius : stageRadius edgeGrid (cellIndex edgeGrid (t + ε)) ≤
        ((1 / 2 : ℝ) : EReal) := by
      calc
        stageRadius edgeGrid (cellIndex edgeGrid (t + ε)) ≤
            stageRadius edgeGrid (cellIndex edgeGrid (1 / 2)) := stageRadius_mono edgeGrid hindex
        _ = ((1 / 2 : ℝ) : EReal) := by
          rw [hhalf, stageRadius_succ_of_lt edgeGrid 2 (by norm_num)]
          norm_num [edgeGrid, uniformGrid_apply]
    letI : IsEmpty (ComponentIndex pointHeight
        fun (w : cappedIndex (Fin 3) (cellIndex edgeGrid (t + ε))) =>
        (cappedCentredCover 0 1 edgeLabels edgeGrid
          (cellIndex edgeGrid (t + ε)) w : Set ℝ)) := pointIndexEmpty _ hradius
    letI : IsEmpty (Face (mapper pointHeight fun w : cappedIndex (Fin 3)
        (cellIndex edgeGrid (t + ε)) =>
        (cappedCentredCover 0 1 edgeLabels edgeGrid
          (cellIndex edgeGrid (t + ε)) w : Set ℝ)) 0) :=
      isEmpty_face_mapper pointHeight _ 0
    exact ModuleCat.subsingleton_of_isZero
      (isZero_simplicialHomology_of_isEmpty_face ℚ 0)
  · rw [structureMap_mapperHomologyPModule]
    change mapperHomologyMap ℚ edgeHeight
      (cappedCentredRefinement 0 1 edgeLabels edgeGrid
        ((cellIndex edgeGrid).monotone h)) 0 ≠ 0
    obtain ⟨a⟩ := by simpa [t] using edgeQuarterComponent
    exact mapperHomologyMap_zero_ne_zero ℚ _ a

/-- The edge-to-point upper bound holds in every degree on the specified edge grid. -/
theorem edge_to_point_bottleneck_le_half (n : ℕ) :
    bottleneck
      (cappedCentredDiagram ℚ edgeHeight 0 1 edgeLabels edgeGrid n)
      (cappedCentredDiagram ℚ pointHeight 0 1 edgeLabels edgeGrid n) ≤ 1 / 2 := by
  simpa [edgeHeight, pointHeight] using
    bottleneck_cappedCentredDiagram_pair_plHeight_uniformGrid_le ℚ 0 1
      edgeLabels n edgePointPair 0 (1 / 4) (by norm_num) 9 2 (by norm_num)

/-- The different-domain edge-to-point bottleneck lies in `[1/4, 1/2]`; this fixture does not
claim that either endpoint is exact. -/
theorem edge_to_point_bottleneck_bracket :
    (1 / 4 : ℝ≥0∞) ≤ bottleneck
      (cappedCentredDiagram ℚ edgeHeight 0 1 edgeLabels edgeGrid 0)
      (cappedCentredDiagram ℚ pointHeight 0 1 edgeLabels edgeGrid 0) ∧
    bottleneck
      (cappedCentredDiagram ℚ edgeHeight 0 1 edgeLabels edgeGrid 0)
      (cappedCentredDiagram ℚ pointHeight 0 1 edgeLabels edgeGrid 0) ≤ 1 / 2 := by
  exact ⟨edge_point_pair_lower_bound, edge_to_point_bottleneck_le_half 0⟩

/-! ## Negative control: Bool to Unit -/

private def boolZeroHeight : C(Bool, ℝ) := ContinuousMap.const Bool 0

private def unitZeroHeight : C(Unit, ℝ) := ContinuousMap.const Unit 0

private def boolToUnit : C(Bool, Unit) := ContinuousMap.const Bool ()

private def unitToBool : C(Unit, Bool) := ContinuousMap.const Unit false

private theorem boolPath_eq {b₀ b₁ : Bool} (γ : Path b₀ b₁) : b₀ = b₁ := by
  have hc := PreconnectedSpace.constant inferInstance γ.continuous (x := 0) (y := 1)
  simpa using hc

private def boolComponentsEquiv : ZerothHomotopy Bool ≃ Bool where
  toFun := ZerothHomotopy.lift id (fun _ _ γ => boolPath_eq γ)
  invFun := ZerothHomotopy.mk
  left_inv c := by induction c using ZerothHomotopy.rec with | mk b => rfl
  right_inv _ := rfl

private noncomputable instance boolZerothFinite : Finite (ZerothHomotopy Bool) :=
  Finite.of_equiv Bool boolComponentsEquiv.symm

private theorem boolToUnit_noHeightMapPair :
    ∀ δ : ℝ≥0, ¬ Nonempty (HeightMapPair boolZeroHeight unitZeroHeight δ) := by
  intro δ ⟨P⟩
  have htrue : P.ψ (P.φ true) = true := by
    obtain ⟨γ, _⟩ := P.hψφ true
    have hc := PreconnectedSpace.constant inferInstance γ.continuous (x := 0) (y := 1)
    simpa using hc
  have hfalse : P.ψ (P.φ false) = false := by
    obtain ⟨γ, _⟩ := P.hψφ false
    have hc := PreconnectedSpace.constant inferInstance γ.continuous (x := 0) (y := 1)
    simpa using hc
  have hcomp : P.ψ (P.φ true) = P.ψ (P.φ false) :=
    congrArg P.ψ (Subsingleton.elim (P.φ true) (P.φ false))
  exact Bool.false_ne_true (htrue.symm.trans (hcomp.trans hfalse)).symm

private theorem boolEssentialCount :
    (essentialPart (cappedCentredDiagram ℚ boolZeroHeight 0 1
      (fun _ : Unit => 0) quarterGrid 0).points).card = 2 := by
  rw [card_essentialPart_cappedCentredDiagram_zero_of_unique]
  rw [Nat.card_congr boolComponentsEquiv]
  norm_num

private theorem unitEssentialCount :
    (essentialPart (cappedCentredDiagram ℚ unitZeroHeight 0 1
      (fun _ : Unit => 0) quarterGrid 0).points).card = 1 := by
  rw [card_essentialPart_cappedCentredDiagram_zero_of_unique]
  norm_num

/-- The two constant maps preserve heights, but the missing composite path condition would
produce unequal essential multiplicities and hence infinite bottleneck distance. -/
theorem bool_to_unit_path_condition_needed :
    (∀ b, unitZeroHeight (boolToUnit b) = boolZeroHeight b) ∧
      (∀ u, boolZeroHeight (unitToBool u) = unitZeroHeight u) ∧
      (∀ δ : ℝ≥0, ¬ Nonempty (HeightMapPair boolZeroHeight unitZeroHeight δ)) ∧
      bottleneck
        (cappedCentredDiagram ℚ boolZeroHeight 0 1 (fun _ : Unit => 0) quarterGrid 0)
        (cappedCentredDiagram ℚ unitZeroHeight 0 1 (fun _ : Unit => 0) quarterGrid 0) = ⊤ := by
  refine ⟨fun _ => rfl, fun _ => rfl, boolToUnit_noHeightMapPair, ?_⟩
  apply le_antisymm le_top
  by_contra htop
  have hne : bottleneck
      (cappedCentredDiagram ℚ boolZeroHeight 0 1 (fun _ : Unit => 0) quarterGrid 0)
      (cappedCentredDiagram ℚ unitZeroHeight 0 1 (fun _ : Unit => 0) quarterGrid 0) ≠ ⊤ := by
    intro heq
    exact htop (heq ▸ le_rfl)
  have hfinite := lt_top_iff_ne_top.mpr hne
  have hcount := (bottleneck_lt_top_iff _ _).mp hfinite
  rw [boolEssentialCount, unitEssentialCount] at hcount
  norm_num at hcount

end

end TDA.Mapper.RefinementHomologyCappedMapPairExamples
