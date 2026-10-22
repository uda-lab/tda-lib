import TDA.Mapper.MultiNerveRefinement
import TDA.Mapper.MultiNerveExamples
import TDA.Mapper.TowerExamples

/-!
# MultiNerve Mapper refinement fixtures

Acceptance fixtures for `TDA.Mapper.MultiNerveRefinement`, on the merged objects.

* **Coherent three-stage tower.** On the merged three-stage tower, the first-to-middle map
  sends the first-stage cell over two component indices to the middle-stage vertex cell, so the
  support drops from two elements to one. The square with ordinary Mapper holds there, and the
  first-to-last map is the composite of the two adjacent maps.
* **4-cycle, merging of edge cells.** On `cycleGraph 4` with heights `0, 1, 2, 1`, refine the
  overlapping intervals `(-1, 3/2)` and `(1/2, 3)` to two copies of `(-1, 3)` by the identity
  selector. The Mapper vertex map is injective, but the two distinct edge cells represented by
  the vertices `1` and `3` have the same image, whose support has two elements.
* **Two disjoint edges, separation of the isomorphism hypotheses.** For two disjoint edges with
  endpoint heights `0` and `2`, every nonempty finite intersection of component members has at
  most one path component, while the preimage of `(-1, 3/2)` has two path components. Hence
  `IntersectionsPathSubsingleton (componentCover f U)` holds and
  `PreimageIntersectionsPathConnected f U` fails, and the MultiNerve Mapper is order-isomorphic
  to ordinary Mapper.
-/

namespace TDA.Mapper.MultiNerveRefinementExamples

open Finset Set SimpleGraph
open TDA.Topology TDA.Topology.MultiNerveCell
open TDA.Reeb TDA.Reeb.GraphPL TDA.Reeb.GraphRealization TDA.Reeb.OpenInterval
open TDA.Reeb.Examples.GraphPL
open TDA.Reeb.Examples.GraphRealization (edgeGraph half)
open TDA.Mapper.GraphPL.Examples (overlappingIntervals twoEdgeGraph twoEdgeHeight twoEdgeDart
  twoEdgeOverlapPoint twoEdgeOverlapIndex twoEdgeIndexEquiv twoEdge_edge_eq
  twoEdge_midpoint_height twoEdge_cross_componentCover_disjoint
  twoEdge_mapper_two_disjoint_edges)
open TDA.Mapper.MultiNerveExamples (cycleIndex cycleEdge cycleEdgeCellOne cycleEdgeCellThree
  cycleEdgeCellOne_ne_three cycle_preimage_subsingleton)
open TDA.Mapper.TowerExamples (ThreeStage ThreeStageLE threeStageIndex threeStageCover
  threeStageTower threeStageMap threeStageComponentIndex)

noncomputable section

local instance multiNerveRefinementExamplesDecidableEq (α : Type*) : DecidableEq α :=
  Classical.decEq α

/-- The two overlapping intervals as a family of real sets. -/
local notation "overlapCover" => fun i : Bool => ((overlappingIntervals i : OpenInterval) : Set ℝ)

/-! ## The coherent three-stage tower -/

section Tower

/-- The two first-stage component indices. -/
def threeStagePair : Finset (ComponentIndex threeStageMap (threeStageCover .first)) :=
  {threeStageComponentIndex .first false, threeStageComponentIndex .first true}

private theorem threeStagePair_nonempty : threeStagePair.Nonempty := by
  simp [threeStagePair]

private theorem unit_mem_threeStagePair :
    () ∈ interMember (componentCover threeStageMap (threeStageCover .first)) threeStagePair := by
  rw [mem_interMember_iff]
  intro a ha
  simp only [threeStagePair, Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha with rfl | rfl <;> exact ⟨Set.mem_univ (), rfl⟩

/-- The first-stage MultiNerve Mapper cell over the two first-stage component indices. -/
def threeStagePairCell : multiNerveMapper threeStageMap (threeStageCover .first) :=
  MultiNerveCell.mk threeStagePair threeStagePair_nonempty
    (ZerothHomotopy.mk ⟨(), unit_mem_threeStagePair⟩)

private theorem threeStagePair_card : threeStagePair.card = 2 :=
  Finset.card_pair fun h => Bool.false_ne_true (congrArg Sigma.fst h)

/-- On the three-stage tower, the first-to-middle map sends the first-stage cell over two
component indices to the middle-stage vertex cell, the square with ordinary Mapper holds there,
and the first-to-last map is the composite of the adjacent maps. -/
theorem three_stage_multiNerve_tower :
    threeStagePairCell.support.card = 2 ∧
    threeStageTower.multiNerveMapperMap threeStageMap
        (ThreeStageLE.first_middle : ThreeStage.first ≤ ThreeStage.middle) threeStagePairCell =
      vertexCell threeStageMap (threeStageCover .middle) (threeStageComponentIndex .middle ()) ∧
    (threeStageTower.multiNerveMapperMap threeStageMap
        (ThreeStageLE.first_middle : ThreeStage.first ≤ ThreeStage.middle)
        threeStagePairCell).support.card = 1 ∧
    (multiNerveMapper_projection threeStageMap (threeStageCover .middle)
        (threeStageTower.multiNerveMapperMap threeStageMap
          (ThreeStageLE.first_middle : ThreeStage.first ≤ ThreeStage.middle)
          threeStagePairCell)).1 =
      (multiNerveMapper_projection threeStageMap (threeStageCover .first)
          threeStagePairCell).1.image
        (threeStageTower.mapperMap threeStageMap
          (ThreeStageLE.first_middle : ThreeStage.first ≤ ThreeStage.middle)) ∧
    threeStageTower.multiNerveMapperMap threeStageMap
        (ThreeStageLE.first_last : ThreeStage.first ≤ ThreeStage.last) =
      threeStageTower.multiNerveMapperMap threeStageMap
          (ThreeStageLE.middle_last : ThreeStage.middle ≤ ThreeStage.last) ∘
        threeStageTower.multiNerveMapperMap threeStageMap
          (ThreeStageLE.first_middle : ThreeStage.first ≤ ThreeStage.middle) := by
  have hvertex : threeStageTower.multiNerveMapperMap threeStageMap
      (ThreeStageLE.first_middle : ThreeStage.first ≤ ThreeStage.middle) threeStagePairCell =
      vertexCell threeStageMap (threeStageCover .middle)
        (threeStageComponentIndex .middle ()) := by
    apply eq_vertexCell_of_support_eq
    refine Finset.eq_singleton_iff_nonempty_unique_mem.2 ⟨support_nonempty _, ?_⟩
    intro b hb
    obtain ⟨⟨i, c⟩, -, rfl⟩ := Finset.mem_image.1 hb
    induction c using ZerothHomotopy.rec with
    | mk x => rfl
  refine ⟨threeStagePair_card, hvertex, ?_,
    multiNerveMapper_projection_multiNerveMapperMap _ _ _,
    (threeStageTower.multiNerveMapperMap_trans threeStageMap _ _).symm⟩
  rw [hvertex]
  exact (congrArg Finset.card (support_vertexCell threeStageMap (threeStageCover .middle)
    (threeStageComponentIndex .middle ()))).trans (Finset.card_singleton _)

end Tower

/-! ## The 4-cycle: merging of edge cells -/

section Cycle

/-- The PL height of the 4-cycle with vertex heights `0, 1, 2, 1`. -/
local notation "cycleMap" => plHeight C4 h4

/-- Two copies of the interval `(-1, 3)`. -/
def doubleWideIntervals : Bool → OpenInterval := fun _ => ioo (-1) 3

/-- The identity-selector refinement of the overlapping intervals to two copies of `(-1, 3)`. -/
def overlapToDoubleWide : Refinement (fun i => (overlappingIntervals i : Set ℝ))
    (fun i => (doubleWideIntervals i : Set ℝ)) where
  selector := id
  subset i x hx := by
    cases i <;> rcases hx with ⟨hx₁, hx₂⟩ <;> constructor <;> linarith

/-- The Mapper vertex map of the refinement is injective: labels are preserved, and each label
carries one path component. -/
theorem cycle_doubleWide_mapperMap_injective :
    Function.Injective (mapperMap cycleMap overlapToDoubleWide) := by
  rintro ⟨i, c⟩ ⟨j, d⟩ h
  have hij : i = j := congrArg Sigma.fst h
  subst hij
  exact Sigma.ext rfl (heq_of_eq (@Subsingleton.elim _ (cycle_preimage_subsingleton i) _ _))

private theorem J4_subset_doubleWide (T : Finset Bool) :
    (plHeight C4 h4 ⁻¹' (J4 : Set ℝ)) ⊆
      plHeight C4 h4 ⁻¹' ⋂ i ∈ T, (doubleWideIntervals i : Set ℝ) := by
  intro p hp
  have hp' : (-1 / 2 : ℝ) < plHeight C4 h4 p ∧ plHeight C4 h4 p < 5 / 2 := hp
  refine Set.mem_iInter₂.2 fun i _ => ?_
  show (-1 : ℝ) < plHeight C4 h4 p ∧ plHeight C4 h4 p < 3
  constructor <;> linarith [hp'.1, hp'.2]

private theorem mk_eq_mk_of_subset {X : Type*} [TopologicalSpace X] {S T : Set X} (hST : S ⊆ T)
    {x y : X} {hx : x ∈ S} {hy : y ∈ S}
    (h : (ZerothHomotopy.mk ⟨x, hx⟩ : ZerothHomotopy S) = ZerothHomotopy.mk ⟨y, hy⟩) :
    (ZerothHomotopy.mk ⟨x, hST hx⟩ : ZerothHomotopy T) = ZerothHomotopy.mk ⟨y, hST hy⟩ :=
  congrArg (componentMap (preimageSetInclusion (ContinuousMap.id X) hST)) h

/-- The refinement merges the two distinct edge cells over the single Mapper edge. -/
theorem cycle_doubleWide_edgeCells_merge :
    multiNerveMapperMap cycleMap overlapToDoubleWide cycleEdgeCellOne =
      multiNerveMapperMap cycleMap overlapToDoubleWide cycleEdgeCellThree := by
  have hJ : (ZerothHomotopy.mk ⟨vertex C4 1, h4_mem_J4 1⟩ :
        ZerothHomotopy (plHeight C4 h4 ⁻¹' (J4 : Set ℝ))) =
      ZerothHomotopy.mk ⟨vertex C4 3, h4_mem_J4 3⟩ :=
    c4_J_preimage_merge
  have h : refinementFaceMap (componentRefinement cycleMap overlapToDoubleWide) cycleEdge
        cycleEdgeCellOne.component =
      refinementFaceMap (componentRefinement cycleMap overlapToDoubleWide) cycleEdge
        cycleEdgeCellThree.component := by
    apply interMemberPreimageMap_injective
    exact mk_eq_mk_of_subset (J4_subset_doubleWide _) hJ
  exact congrArg (MultiNerveCell.mk _ _) h

private theorem cycleEdge_card : cycleEdge.card = 2 :=
  Finset.card_pair (componentIndex_ne_of_index_ne cycleMap overlapCover Bool.false_ne_true _ _)

/-- On the 4-cycle, the Mapper vertex map of the identity-selector refinement to `(-1, 3)` is
injective, while the MultiNerve Mapper map identifies the two distinct edge cells. Their common
image lies over the image of the Mapper edge, which has two elements. -/
theorem cycle_doubleWide_multiNerve_merge :
    Function.Injective (mapperMap cycleMap overlapToDoubleWide) ∧
    cycleEdgeCellOne ≠ cycleEdgeCellThree ∧
    multiNerveMapperMap cycleMap overlapToDoubleWide cycleEdgeCellOne =
      multiNerveMapperMap cycleMap overlapToDoubleWide cycleEdgeCellThree ∧
    ¬ Function.Injective (multiNerveMapperMap cycleMap overlapToDoubleWide) ∧
    (multiNerveMapperMap cycleMap overlapToDoubleWide cycleEdgeCellOne).support =
      cycleEdge.image (mapperMap cycleMap overlapToDoubleWide) ∧
    (multiNerveMapperMap cycleMap overlapToDoubleWide cycleEdgeCellOne).support.card = 2 := by
  have hsupp : (multiNerveMapperMap cycleMap overlapToDoubleWide cycleEdgeCellOne).support =
      cycleEdge.image (mapperMap cycleMap overlapToDoubleWide) :=
    multiNerveMapper_projection_multiNerveMapperMap _ _ _
  refine ⟨cycle_doubleWide_mapperMap_injective, cycleEdgeCellOne_ne_three,
    cycle_doubleWide_edgeCells_merge,
    fun hinj => cycleEdgeCellOne_ne_three (hinj cycle_doubleWide_edgeCells_merge), hsupp, ?_⟩
  rw [hsupp, Finset.card_image_of_injective _ cycle_doubleWide_mapperMap_injective, cycleEdge_card]

end Cycle

/-! ## Two disjoint edges: separation of the isomorphism hypotheses -/

section TwoEdge

/-- The PL height of two disjoint edges with endpoint heights `0` and `2`. -/
local notation "twoEdgeMap" => plHeight twoEdgeGraph twoEdgeHeight

private theorem twoEdge_index_cases (a : ComponentIndex twoEdgeMap overlapCover) :
    ∃ σ i, a = twoEdgeOverlapIndex σ i :=
  ⟨(twoEdgeIndexEquiv.symm a).1, (twoEdgeIndexEquiv.symm a).2,
    (twoEdgeIndexEquiv.apply_symm_apply a).symm⟩

/-- A point lying in component members of two graph copies forces the copies to agree. -/
private theorem twoEdge_side_eq {p : Realization twoEdgeGraph} {σ τ i j : Bool}
    (hσ : p ∈ componentCover twoEdgeMap overlapCover (twoEdgeOverlapIndex σ i))
    (hτ : p ∈ componentCover twoEdgeMap overlapCover (twoEdgeOverlapIndex τ j)) : σ = τ := by
  cases σ <;> cases τ
  · rfl
  · exact ((Set.disjoint_left.1 (twoEdge_cross_componentCover_disjoint i j)) hσ hτ).elim
  · exact ((Set.disjoint_left.1 (twoEdge_cross_componentCover_disjoint j i)) hτ hσ).elim
  · rfl

/-- The preimage of `(-1, 3/2)` has two distinct path components, so
`PreimageIntersectionsPathConnected` fails. -/
theorem twoEdge_not_preimageIntersectionsPathConnected :
    ¬ PreimageIntersectionsPathConnected twoEdgeMap overlapCover := by
  intro h
  have hne : (twoEdgeMap ⁻¹' ⋂ i ∈ ({false} : Finset Bool), overlapCover i).Nonempty := by
    rw [Finset.set_biInter_singleton]
    exact ⟨_, (twoEdgeOverlapPoint false false).2⟩
  have hpc := h {false} (Finset.singleton_nonempty _) hne
  rw [Finset.set_biInter_singleton] at hpc
  have hsub := subsingleton_zerothHomotopy_of_isPathConnected hpc
  have hne' : twoEdgeOverlapIndex false false ≠ twoEdgeOverlapIndex true false := fun h =>
    Bool.false_ne_true (congrArg Prod.fst
      (twoEdgeIndexEquiv.injective (a₁ := (false, false)) (a₂ := (true, false)) h))
  exact hne' (Sigma.ext rfl (heq_of_eq (@Subsingleton.elim _ hsub _ _)))

private theorem twoEdge_midpoint_mem_half (σ : Bool) :
    dartHeight twoEdgeHeight (twoEdgeDart σ) half ∈ ioo (1 / 2) (3 / 2) := by
  rw [twoEdge_midpoint_height, mem_ioo]
  norm_num

/-- Every path component of the preimage of `(1/2, 3/2)` is the class of one of the two
midpoints. -/
private theorem twoEdge_half_classification
    (z : {p : Realization twoEdgeGraph // twoEdgeMap p ∈ ioo (1 / 2) (3 / 2)}) :
    ∃ σ, ZerothHomotopy.mk z = ZerothHomotopy.mk
      (⟨edgePoint twoEdgeGraph (twoEdgeDart σ) half, twoEdge_midpoint_mem_half σ⟩ :
        {p : Realization twoEdgeGraph // twoEdgeMap p ∈ ioo (1 / 2) (3 / 2)}) := by
  have key : ∀ c : (cellGraph twoEdgeGraph twoEdgeHeight (ioo (1 / 2) (3 / 2))).ConnectedComponent,
      ∃ σ, c = preimageComponentsEquiv twoEdgeGraph twoEdgeHeight (ioo (1 / 2) (3 / 2))
        (ZerothHomotopy.mk ⟨edgePoint twoEdgeGraph (twoEdgeDart σ) half,
          twoEdge_midpoint_mem_half σ⟩) := by
    intro c
    induction c using ConnectedComponent.ind with
    | h x =>
      rcases x with ⟨v, hv⟩ | ⟨e, hact⟩
      · exfalso
        rcases v with b | b <;> cases b <;> norm_num [twoEdgeHeight, h02, mem_ioo] at hv
      · rcases twoEdge_edge_eq e with he | he
        · refine ⟨false, ?_⟩
          rw [preimageComponentsEquiv_mk_edgePoint]
          exact congrArg _ (congrArg Sum.inr (Subtype.ext he))
        · refine ⟨true, ?_⟩
          rw [preimageComponentsEquiv_mk_edgePoint]
          exact congrArg _ (congrArg Sum.inr (Subtype.ext he))
  obtain ⟨σ, hσ⟩ := key (preimageComponentsEquiv twoEdgeGraph twoEdgeHeight _
    (ZerothHomotopy.mk z))
  exact ⟨σ, (preimageComponentsEquiv twoEdgeGraph twoEdgeHeight _).injective hσ⟩

private theorem half_subset_overlap (T : Finset Bool) :
    twoEdgeMap ⁻¹' ((ioo (1 / 2) (3 / 2) : OpenInterval) : Set ℝ) ⊆
      twoEdgeMap ⁻¹' ⋂ i ∈ T, overlapCover i := by
  intro p hp
  have hp' : (1 / 2 : ℝ) < twoEdgeMap p ∧ twoEdgeMap p < 3 / 2 := hp
  refine Set.mem_iInter₂.2 fun i _ => ?_
  cases i
  · show (-1 : ℝ) < twoEdgeMap p ∧ twoEdgeMap p < 3 / 2
    constructor <;> linarith [hp'.1, hp'.2]
  · show (1 / 2 : ℝ) < twoEdgeMap p ∧ twoEdgeMap p < 3
    constructor <;> linarith [hp'.1, hp'.2]

/-- Every point of the intersection of the two component members of one graph copy is joined to
the midpoint of that copy inside the preimage of `(1/2, 3/2)`. -/
private theorem twoEdge_pair_joined {σ : Bool} {p : Realization twoEdgeGraph}
    (hp : p ∈ interMember (componentCover twoEdgeMap overlapCover)
      {twoEdgeOverlapIndex σ false, twoEdgeOverlapIndex σ true}) :
    JoinedIn (twoEdgeMap ⁻¹' ((ioo (1 / 2) (3 / 2) : OpenInterval) : Set ℝ)) p
      (edgePoint twoEdgeGraph (twoEdgeDart σ) half) := by
  have hf : p ∈ componentCover twoEdgeMap overlapCover (twoEdgeOverlapIndex σ false) :=
    (mem_interMember_iff _).1 hp _ (by simp)
  have ht : p ∈ componentCover twoEdgeMap overlapCover (twoEdgeOverlapIndex σ true) :=
    (mem_interMember_iff _).1 hp _ (by simp)
  have h₁ : (-1 : ℝ) < twoEdgeMap p ∧ twoEdgeMap p < 3 / 2 := hf.1
  have h₂ : (1 / 2 : ℝ) < twoEdgeMap p ∧ twoEdgeMap p < 3 := ht.1
  have hpK : twoEdgeMap p ∈ ioo (1 / 2) (3 / 2) := ⟨h₂.1, h₁.2⟩
  obtain ⟨τ, hτ⟩ := twoEdge_half_classification ⟨p, hpK⟩
  have hJ : JoinedIn (twoEdgeMap ⁻¹' ((ioo (1 / 2) (3 / 2) : OpenInterval) : Set ℝ)) p
      (edgePoint twoEdgeGraph (twoEdgeDart τ) half) :=
    (joinedIn_iff_joined (F := twoEdgeMap ⁻¹' ((ioo (1 / 2) (3 / 2) : OpenInterval) : Set ℝ))
      hpK (twoEdge_midpoint_mem_half τ)).2 (Quotient.exact hτ)
  have hsub : twoEdgeMap ⁻¹' ((ioo (1 / 2) (3 / 2) : OpenInterval) : Set ℝ) ⊆
      twoEdgeMap ⁻¹' overlapCover false := by
    intro w hw
    have hw' : (1 / 2 : ℝ) < twoEdgeMap w ∧ twoEdgeMap w < 3 / 2 := hw
    show (-1 : ℝ) < twoEdgeMap w ∧ twoEdgeMap w < 3 / 2
    constructor <;> linarith [hw'.1, hw'.2]
  have hτmem : p ∈ componentCover twoEdgeMap overlapCover (twoEdgeOverlapIndex τ false) :=
    ⟨hf.1, mk_eq_of_joinedIn twoEdgeMap (overlapCover false) (hJ.mono hsub) hf.1
      (twoEdgeOverlapPoint τ false).2⟩
  obtain rfl := twoEdge_side_eq hf hτmem
  exact hJ

private theorem twoEdge_pair_subsingleton (σ : Bool) :
    Subsingleton (ZerothHomotopy (interMember (componentCover twoEdgeMap overlapCover)
      {twoEdgeOverlapIndex σ false, twoEdgeOverlapIndex σ true})) := by
  refine ⟨fun c d => ?_⟩
  obtain ⟨x, rfl⟩ := ZerothHomotopy.mk_surjective c
  obtain ⟨y, rfl⟩ := ZerothHomotopy.mk_surjective d
  apply interMemberPreimageMap_injective
  refine ZerothHomotopy.sound (JoinedIn.joined_subtype ?_).somePath
  exact ((twoEdge_pair_joined x.2).trans (twoEdge_pair_joined y.2).symm).mono
    (half_subset_overlap _)

private theorem singleton_subsingleton (a : ComponentIndex twoEdgeMap overlapCover) :
    Subsingleton (ZerothHomotopy (interMember (componentCover twoEdgeMap overlapCover) {a})) := by
  have hpc : IsPathConnected (interMember (componentCover twoEdgeMap overlapCover) {a}) := by
    rw [interMember_singleton]
    exact componentCover_isPathConnected _ _ a
  exact subsingleton_zerothHomotopy_of_isPathConnected hpc

/-- Every nonempty finite intersection of component members has at most one path component. -/
theorem twoEdge_intersectionsPathSubsingleton :
    IntersectionsPathSubsingleton (componentCover twoEdgeMap overlapCover) := by
  intro s hs
  by_cases hempty : interMember (componentCover twoEdgeMap overlapCover) s = ∅
  · have := (isEmpty_cellsOver_iff _ s).2 hempty
    infer_instance
  obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.2 hempty
  obtain ⟨a₀, ha₀⟩ := hs
  obtain ⟨σ, i₀, rfl⟩ := twoEdge_index_cases a₀
  have hside : ∀ a ∈ s, ∃ i, a = twoEdgeOverlapIndex σ i := by
    intro a ha
    obtain ⟨τ, j, rfl⟩ := twoEdge_index_cases a
    obtain rfl := twoEdge_side_eq ((mem_interMember_iff _).1 hx _ ha₀)
      ((mem_interMember_iff _).1 hx _ ha)
    exact ⟨j, rfl⟩
  by_cases hf : twoEdgeOverlapIndex σ false ∈ s <;> by_cases ht : twoEdgeOverlapIndex σ true ∈ s
  · have hs_eq : s = {twoEdgeOverlapIndex σ false, twoEdgeOverlapIndex σ true} := by
      ext a
      constructor
      · intro ha
        obtain ⟨i, rfl⟩ := hside a ha
        cases i <;> simp
      · intro ha
        simp only [Finset.mem_insert, Finset.mem_singleton] at ha
        rcases ha with rfl | rfl <;> assumption
    rw [hs_eq]
    exact twoEdge_pair_subsingleton σ
  · have hs_eq : s = {twoEdgeOverlapIndex σ false} := by
      ext a
      constructor
      · intro ha
        obtain ⟨i, rfl⟩ := hside a ha
        cases i
        · simp
        · exact absurd ha ht
      · intro ha
        rw [Finset.mem_singleton.1 ha]
        exact hf
    rw [hs_eq]
    exact singleton_subsingleton _
  · have hs_eq : s = {twoEdgeOverlapIndex σ true} := by
      ext a
      constructor
      · intro ha
        obtain ⟨i, rfl⟩ := hside a ha
        cases i
        · exact absurd ha hf
        · simp
      · intro ha
        rw [Finset.mem_singleton.1 ha]
        exact ht
    rw [hs_eq]
    exact singleton_subsingleton _
  · exfalso
    cases i₀
    · exact hf ha₀
    · exact ht ha₀

/-- The MultiNerve Mapper of the two disjoint edges is order-isomorphic to ordinary Mapper. -/
def twoEdgeMultiNerveOrderIso :
    multiNerveMapper twoEdgeMap overlapCover ≃o {s // s ∈ mapper twoEdgeMap overlapCover} :=
  multiNerveMapperOrderIso _ _ twoEdge_intersectionsPathSubsingleton

/-- On two disjoint edges, `IntersectionsPathSubsingleton` holds while
`PreimageIntersectionsPathConnected` fails, so the first hypothesis is strictly weaker. The
projection onto ordinary Mapper is bijective and an order isomorphism; each graph copy carries
exactly one edge cell, and no cell joins the two copies. -/
theorem twoEdge_multiNerveMapper_separation :
    ¬ PreimageIntersectionsPathConnected twoEdgeMap overlapCover ∧
    IntersectionsPathSubsingleton (componentCover twoEdgeMap overlapCover) ∧
    Function.Bijective (multiNerveMapper_projection twoEdgeMap overlapCover) ∧
    ⇑twoEdgeMultiNerveOrderIso = multiNerveMapper_projection twoEdgeMap overlapCover ∧
    (∀ σ, ∃! c : multiNerveMapper twoEdgeMap overlapCover,
      c.support = {twoEdgeOverlapIndex σ false, twoEdgeOverlapIndex σ true}) ∧
    ∀ (i j : Bool) (c : multiNerveMapper twoEdgeMap overlapCover),
      c.support ≠ {twoEdgeOverlapIndex false i, twoEdgeOverlapIndex true j} := by
  have hinj : Function.Injective (multiNerveMapper_projection twoEdgeMap overlapCover) :=
    (projection_injective_iff _).2 twoEdge_intersectionsPathSubsingleton
  refine ⟨twoEdge_not_preimageIntersectionsPathConnected, twoEdge_intersectionsPathSubsingleton,
    ⟨hinj, multiNerveMapper_projection_surjective _ _⟩, rfl, fun σ => ?_, fun i j c hc => ?_⟩
  · obtain ⟨c, hc⟩ := multiNerveMapper_projection_surjective twoEdgeMap overlapCover
      ⟨_, twoEdge_mapper_two_disjoint_edges.2.1 σ⟩
    refine ⟨c, congrArg Subtype.val hc, fun d hd => hinj ?_⟩
    rw [hc]
    exact Subtype.ext hd
  · apply twoEdge_mapper_two_disjoint_edges.2.2.1 i j
    rw [← hc]
    exact c.support_mem_nerve

end TwoEdge

end

end TDA.Mapper.MultiNerveRefinementExamples
