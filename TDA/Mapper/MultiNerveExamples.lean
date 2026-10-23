import TDA.Mapper.MultiNerve
import TDA.Mapper.GraphPLExamples

/-!
# MultiNerve Mapper fixtures

Acceptance fixtures for `TDA.Mapper.MultiNerve`, on the merged graph-PL and Mapper
objects. Every graph-PL fixture uses the two overlapping intervals `(-1, 3/2)` and `(1/2, 3)`.

* **4-cycle, MultiNerve Mapper differs from Mapper.** On `cycleGraph 4` with heights `0, 1, 2, 1`
  each interval preimage has exactly one path component, so ordinary Mapper has exactly two
  vertices and exactly one edge. The intersection of the two component members is the preimage of
  `(1/2, 3/2)`, which has the two path components `x1` and `x3`. The MultiNerve Mapper therefore
  has exactly two vertex cells and exactly two edge cells over the single Mapper edge; the
  projection is surjective but not injective and `IntersectionsPathSubsingleton` fails.
* **Single edge, agreement.** For one edge of heights `0` and `2`, every nonempty finite
  intersection of target members has a path-connected preimage, so the MultiNerve Mapper is
  order-isomorphic to the merged two-vertex, one-edge Mapper.
* **One-point triangle.** Three labels for the full member over a one-point domain satisfy
  `IntersectionsPathSubsingleton`, and the MultiNerve Mapper has a cell with three-element support
  over the merged triangle; the target multiplicity is not at most two.
* **Empty domain.** The MultiNerve Mapper of the empty domain has no cells, and ordinary Mapper is
  the bottom complex.
-/

namespace TDA.Mapper.MultiNerveExamples

open Finset Set SimpleGraph
open TDA.Topology TDA.Topology.MultiNerveCell
open TDA.Reeb TDA.Reeb.GraphPL TDA.Reeb.GraphRealization TDA.Reeb.OpenInterval
open TDA.Reeb.Examples.GraphPL
open TDA.Reeb.Examples.GraphRealization (edgeGraph)
open TDA.Mapper.GraphPL.Examples (overlappingIntervals overlap_components_subsingleton
  overlappingIntervals_multiplicity_two edgeOverlapIndex singleEdge_overlap_exact)
open TDA.Mapper.Examples (triangleMap tripleUnitCover triangleComponentIndex
  triple_duplicate_cover_has_triangle emptyDomainMap unitCover emptyDomain_mapper_eq_bot)

noncomputable section

local instance (α : Type*) : DecidableEq α := Classical.decEq α

/-- The two overlapping intervals as a family of real sets. -/
local notation "overlapCover" => fun i : Bool => ((overlappingIntervals i : OpenInterval) : Set ℝ)

/-! ## The 4-cycle: two edge cells over one Mapper edge -/

section Cycle

/-- The PL height of the 4-cycle with vertex heights `0, 1, 2, 1`. -/
local notation "cycleMap" => plHeight C4 h4

private theorem h4_mem_overlap_false {v : Fin 4} :
    h4 v ∈ overlappingIntervals false ↔ v ≠ 2 := by
  fin_cases v <;> norm_num [h4, overlappingIntervals, mem_ioo] <;> decide

private theorem h4_mem_overlap_true {v : Fin 4} :
    h4 v ∈ overlappingIntervals true ↔ v ≠ 0 := by
  fin_cases v <;> norm_num [h4, overlappingIntervals, mem_ioo]

private theorem one_mem_overlap (i : Bool) : h4 1 ∈ overlappingIntervals i := by
  cases i <;> norm_num [overlappingIntervals, mem_ioo]

private theorem C4_adj_ne_two : ∀ a b : Fin 4, C4.Adj a b → a ≠ 2 ∨ b ≠ 2 := by decide

private theorem C4_adj_ne_zero : ∀ a b : Fin 4, C4.Adj a b → a ≠ 0 ∨ b ≠ 0 := by decide

/-- If every surviving vertex lies in the class of `v₀` and every edge has a surviving endpoint,
the incidence graph has one class. -/
private theorem cycle_cell_class {K : OpenInterval} (v₀ : Fin 4) (hv₀ : h4 v₀ ∈ K)
    (hv : ∀ (v : Fin 4) (hv : h4 v ∈ K),
      (cellGraph C4 h4 K).connectedComponentMk (Sum.inl ⟨v, hv⟩) =
        (cellGraph C4 h4 K).connectedComponentMk (Sum.inl ⟨v₀, hv₀⟩))
    (he : ∀ d : C4.Dart, ∃ w ∈ (dartEdge d : Sym2 (Fin 4)), h4 w ∈ K)
    (x : Cell C4 h4 K) :
    (cellGraph C4 h4 K).connectedComponentMk x =
      (cellGraph C4 h4 K).connectedComponentMk (Sum.inl ⟨v₀, hv₀⟩) := by
  rcases x with ⟨v, hvK⟩ | ⟨e, hact⟩
  · exact hv v hvK
  · obtain ⟨d, rfl⟩ := exists_dartEdge_eq e
    obtain ⟨w, hw, hwK⟩ := he d
    exact (connectedComponentMk_inl_eq_inr C4 h4 K (v := ⟨w, hwK⟩)
      (e := ⟨dartEdge d, hact⟩) hw).symm.trans (hv w hwK)

private theorem cycle_preimage_subsingleton_of {K : OpenInterval} (v₀ : Fin 4)
    (hv₀ : h4 v₀ ∈ K)
    (hv : ∀ (v : Fin 4) (hv : h4 v ∈ K),
      (cellGraph C4 h4 K).connectedComponentMk (Sum.inl ⟨v, hv⟩) =
        (cellGraph C4 h4 K).connectedComponentMk (Sum.inl ⟨v₀, hv₀⟩))
    (he : ∀ d : C4.Dart, ∃ w ∈ (dartEdge d : Sym2 (Fin 4)), h4 w ∈ K) :
    Subsingleton (ZerothHomotopy {p : Realization C4 // plHeight C4 h4 p ∈ K}) := by
  have hcell : Subsingleton (cellGraph C4 h4 K).ConnectedComponent :=
    ⟨ConnectedComponent.ind₂ fun x y => by
      rw [cycle_cell_class v₀ hv₀ hv he x, cycle_cell_class v₀ hv₀ hv he y]⟩
  exact ⟨fun c d => (preimageComponentsEquiv C4 h4 K).injective
    (@Subsingleton.elim _ hcell _ _)⟩

/-- Each overlapping-interval preimage under the 4-cycle height has at most one path component. -/
theorem cycle_preimage_subsingleton (i : Bool) :
    Subsingleton (ZerothHomotopy
      {p : Realization C4 // plHeight C4 h4 p ∈ overlappingIntervals i}) := by
  cases i
  · refine cycle_preimage_subsingleton_of 0 (h4_mem_overlap_false.2 (by decide)) ?_ ?_
    · intro v hv
      have hv2 : v ≠ 2 := h4_mem_overlap_false.1 hv
      fin_cases v
      · rfl
      · exact connectedComponentMk_inl_eq_of_adj C4 h4 _ (show C4.Adj 1 0 by decide)
      · exact absurd rfl hv2
      · exact connectedComponentMk_inl_eq_of_adj C4 h4 _ (show C4.Adj 3 0 by decide)
    · intro d
      rcases C4_adj_ne_two d.fst d.snd d.adj with h | h
      · exact ⟨d.fst, fst_mem_dartEdge d, h4_mem_overlap_false.2 h⟩
      · exact ⟨d.snd, snd_mem_dartEdge d, h4_mem_overlap_false.2 h⟩
  · refine cycle_preimage_subsingleton_of 2 (h4_mem_overlap_true.2 (by decide)) ?_ ?_
    · intro v hv
      have hv0 : v ≠ 0 := h4_mem_overlap_true.1 hv
      fin_cases v
      · exact absurd rfl hv0
      · exact connectedComponentMk_inl_eq_of_adj C4 h4 _ (show C4.Adj 1 2 by decide)
      · rfl
      · exact connectedComponentMk_inl_eq_of_adj C4 h4 _ (show C4.Adj 3 2 by decide)
    · intro d
      rcases C4_adj_ne_zero d.fst d.snd d.adj with h | h
      · exact ⟨d.fst, fst_mem_dartEdge d, h4_mem_overlap_true.2 h⟩
      · exact ⟨d.snd, snd_mem_dartEdge d, h4_mem_overlap_true.2 h⟩

/-- Each overlapping-interval preimage under the 4-cycle height has exactly one path
component. -/
theorem cycle_preimage_card (i : Bool) :
    Nat.card (ZerothHomotopy
      {p : Realization C4 // plHeight C4 h4 p ∈ overlappingIntervals i}) = 1 :=
  Nat.card_eq_one_iff_unique.2 ⟨cycle_preimage_subsingleton i,
    ⟨ZerothHomotopy.mk ⟨vertex C4 1, one_mem_overlap i⟩⟩⟩

/-- The component index at interval label `i`, represented by the vertex `1`. -/
def cycleIndex (i : Bool) : ComponentIndex cycleMap overlapCover :=
  ⟨i, ZerothHomotopy.mk ⟨vertex C4 1, one_mem_overlap i⟩⟩

private theorem cycleIndex_eq (a : ComponentIndex cycleMap overlapCover) :
    a = cycleIndex a.1 := by
  rcases a with ⟨i, c⟩
  exact Sigma.ext rfl (heq_of_eq (@Subsingleton.elim _ (cycle_preimage_subsingleton i) _ _))

private theorem cycleIndex_ne : cycleIndex false ≠ cycleIndex true :=
  componentIndex_ne_of_index_ne cycleMap overlapCover Bool.false_ne_true _ _

private theorem cycleIndex_exhaustive (a : ComponentIndex cycleMap overlapCover) :
    a = cycleIndex false ∨ a = cycleIndex true := by
  rcases a with ⟨i, c⟩
  cases i
  · exact Or.inl (cycleIndex_eq _)
  · exact Or.inr (cycleIndex_eq _)

/-- Each component member is the whole interval preimage. -/
theorem componentCover_cycleIndex (i : Bool) :
    componentCover cycleMap overlapCover (cycleIndex i) =
      plHeight C4 h4 ⁻¹' (overlappingIntervals i : Set ℝ) := by
  ext p
  constructor
  · rintro ⟨hp, -⟩
    exact hp
  · intro hp
    exact ⟨hp, @Subsingleton.elim _ (cycle_preimage_subsingleton i) _ _⟩

/-- The two vertices of the single Mapper edge. -/
def cycleEdge : Finset (ComponentIndex cycleMap overlapCover) :=
  {cycleIndex false, cycleIndex true}

private theorem cycleEdge_nonempty : cycleEdge.Nonempty := by
  simp [cycleEdge]

private theorem cycleEdge_card : cycleEdge.card = 2 :=
  Finset.card_pair cycleIndex_ne

private theorem cycleEdge_mem_mapper : cycleEdge ∈ mapper cycleMap overlapCover := by
  refine (mem_mapper_iff _ _ _).2 ⟨cycleEdge_nonempty, vertex C4 1, ?_⟩
  intro a ha
  simp only [cycleEdge, Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha with rfl | rfl <;> exact ⟨one_mem_overlap _, rfl⟩

private theorem cycle_mapper_edge_unique (s : Finset (ComponentIndex cycleMap overlapCover))
    (_hs : s ∈ mapper cycleMap overlapCover) (hcard : s.card = 2) : s = cycleEdge := by
  refine Finset.eq_of_subset_of_card_le ?_ (by rw [hcard, cycleEdge_card])
  intro a _
  rcases cycleIndex_exhaustive a with rfl | rfl <;> simp [cycleEdge]

/-- The intersection of the two component members is the preimage of `(1/2, 3/2)`. -/
theorem cycle_interMember_eq :
    interMember (componentCover cycleMap overlapCover) cycleEdge =
      plHeight C4 h4 ⁻¹' (I4 : Set ℝ) := by
  unfold cycleEdge
  rw [interMember_insert, interMember_singleton, componentCover_cycleIndex,
    componentCover_cycleIndex, ← Set.preimage_inter]
  congr 1
  ext y
  simp only [overlappingIntervals, I4, coe_ioo, mem_inter_iff, Set.mem_Ioo]
  constructor
  · rintro ⟨⟨_, h₂⟩, h₃, _⟩
    exact ⟨h₃, h₂⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨⟨by linarith, h₂⟩, h₁, by linarith⟩

/-- The path components of the intersection of the two component members are those of the
preimage of `(1/2, 3/2)`. -/
def cycleInterComponentsEquiv :
    ZerothHomotopy (interMember (componentCover cycleMap overlapCover) cycleEdge) ≃
      ZerothHomotopy {p : Realization C4 // plHeight C4 h4 p ∈ I4} where
  toFun := TDA.Topology.componentMap
    (preimageSetInclusion (ContinuousMap.id _) cycle_interMember_eq.subset)
  invFun := TDA.Topology.componentMap
    (preimageSetInclusion (ContinuousMap.id _) cycle_interMember_eq.symm.subset)
  left_inv c := by
    induction c using ZerothHomotopy.rec with
    | mk x => rfl
  right_inv c := by
    induction c using ZerothHomotopy.rec with
    | mk x => rfl

/-- The edge cell over the single Mapper edge represented by a vertex of height in
`(1/2, 3/2)`. -/
def cycleEdgeCell (v : Fin 4) (hv : h4 v ∈ I4) : multiNerveMapper cycleMap overlapCover :=
  MultiNerveCell.mk cycleEdge cycleEdge_nonempty
    (ZerothHomotopy.mk ⟨vertex C4 v, cycle_interMember_eq.symm.subset hv⟩)

/-- The edge cell represented by the vertex `1`. -/
def cycleEdgeCellOne : multiNerveMapper cycleMap overlapCover := cycleEdgeCell 1 one_mem_I4

/-- The edge cell represented by the vertex `3`. -/
def cycleEdgeCellThree : multiNerveMapper cycleMap overlapCover :=
  cycleEdgeCell 3 three_mem_I4

/-- The edge cell at `1` corresponds to the preimage class `x1`. -/
theorem cycleInterComponentsEquiv_one :
    cycleInterComponentsEquiv cycleEdgeCellOne.component = x1 := rfl

/-- The edge cell at `3` corresponds to the preimage class `x3`. -/
theorem cycleInterComponentsEquiv_three :
    cycleInterComponentsEquiv cycleEdgeCellThree.component = x3 := rfl

/-- The two edge cells are distinct. -/
theorem cycleEdgeCellOne_ne_three : cycleEdgeCellOne ≠ cycleEdgeCellThree := by
  intro h
  unfold cycleEdgeCellOne cycleEdgeCellThree cycleEdgeCell MultiNerveCell.mk at h
  have hc := eq_of_heq (Sigma.mk.inj_iff.1 h).2
  exact c4_x1_ne_x3 (congrArg cycleInterComponentsEquiv hc)

/-- Every cell over the Mapper edge is one of the two edge cells. -/
theorem cycle_cells_over_edge (c : multiNerveMapper cycleMap overlapCover)
    (hc : c.support = cycleEdge) : c = cycleEdgeCellOne ∨ c = cycleEdgeCellThree := by
  rcases c with ⟨⟨s, hs⟩, d⟩
  change s = cycleEdge at hc
  subst hc
  rcases c4_preimage_classification (cycleInterComponentsEquiv d) with h | h
  · obtain rfl : d = cycleEdgeCellOne.component :=
      cycleInterComponentsEquiv.injective (h.trans cycleInterComponentsEquiv_one.symm)
    exact Or.inl rfl
  · obtain rfl : d = cycleEdgeCellThree.component :=
      cycleInterComponentsEquiv.injective (h.trans cycleInterComponentsEquiv_three.symm)
    exact Or.inr rfl

private theorem cycle_componentIndex_card :
    Nat.card (ComponentIndex cycleMap overlapCover) = 2 :=
  Nat.card_eq_two_iff.2 ⟨cycleIndex false, cycleIndex true, cycleIndex_ne,
    Set.eq_univ_of_forall fun a => cycleIndex_exhaustive a⟩

/-- On the 4-cycle, ordinary Mapper has exactly two vertices and exactly one edge, while the
MultiNerve Mapper has exactly two vertex cells and exactly two edge cells, both over that edge
and represented by the vertices `1` and `3`. The projection is surjective but not injective,
`IntersectionsPathSubsingleton` fails, and every cell has support of size at most two. -/
theorem cycle_multiNerveMapper_ne_mapper :
    (∀ i, Nat.card (ZerothHomotopy
      {p : Realization C4 // plHeight C4 h4 p ∈ overlappingIntervals i}) = 1) ∧
    Nat.card (ComponentIndex cycleMap overlapCover) = 2 ∧
    cycleEdge ∈ mapper cycleMap overlapCover ∧
    (∀ s ∈ mapper cycleMap overlapCover, s.card = 2 → s = cycleEdge) ∧
    interMember (componentCover cycleMap overlapCover) cycleEdge =
      plHeight C4 h4 ⁻¹' (I4 : Set ℝ) ∧
    Nat.card {c : multiNerveMapper cycleMap overlapCover // c.support.card = 1} = 2 ∧
    Nat.card {c : multiNerveMapper cycleMap overlapCover // c.support = cycleEdge} = 2 ∧
    Nat.card {c : multiNerveMapper cycleMap overlapCover // c.support.card = 2} = 2 ∧
    cycleEdgeCellOne ≠ cycleEdgeCellThree ∧
    cycleEdgeCellOne.support = cycleEdge ∧ cycleEdgeCellThree.support = cycleEdge ∧
    cycleInterComponentsEquiv cycleEdgeCellOne.component = x1 ∧
    cycleInterComponentsEquiv cycleEdgeCellThree.component = x3 ∧
    Function.Surjective (multiNerveMapper_projection cycleMap overlapCover) ∧
    ¬ Function.Injective (multiNerveMapper_projection cycleMap overlapCover) ∧
    ¬ IntersectionsPathSubsingleton (componentCover cycleMap overlapCover) ∧
    ∀ c : multiNerveMapper cycleMap overlapCover, c.support.card ≤ 2 := by
  have hnotinj : ¬ Function.Injective (multiNerveMapper_projection cycleMap overlapCover) :=
    fun h => cycleEdgeCellOne_ne_three (h rfl)
  refine ⟨cycle_preimage_card, cycle_componentIndex_card, cycleEdge_mem_mapper,
    cycle_mapper_edge_unique, cycle_interMember_eq,
    (Nat.card_congr (vertexCellEquiv _ _)).trans cycle_componentIndex_card,
    (Nat.card_congr ((cellsOverEquiv _ cycleEdge cycleEdge_nonempty).trans
      cycleInterComponentsEquiv)).trans c4_card_preimage, ?_, cycleEdgeCellOne_ne_three,
    rfl, rfl, cycleInterComponentsEquiv_one, cycleInterComponentsEquiv_three,
    multiNerveMapper_projection_surjective _ _, hnotinj,
    fun h => hnotinj ((projection_injective_iff _).2 h),
    multiNerveMapper_card_le_of_multiplicity _ _ (overlappingIntervals_multiplicity_two C4 h4)⟩
  refine Nat.card_eq_two_iff.2 ⟨⟨cycleEdgeCellOne, cycleEdge_card⟩,
    ⟨cycleEdgeCellThree, cycleEdge_card⟩, fun h => cycleEdgeCellOne_ne_three
      (congrArg Subtype.val h), Set.eq_univ_of_forall fun c => ?_⟩
  rcases cycle_cells_over_edge c.1
      (cycle_mapper_edge_unique _ c.1.support_mem_nerve c.2) with h | h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Subtype.ext h)

end Cycle

/-! ## The single edge: agreement with ordinary Mapper -/

section SingleEdge

/-- The PL height of the single edge with endpoint heights `0` and `2`. -/
local notation "edgeMap" => plHeight edgeGraph h02

private theorem preimage_isPathConnected_of_subsingleton {K : OpenInterval}
    (hs : Subsingleton (ZerothHomotopy
      {p : Realization edgeGraph // plHeight edgeGraph h02 p ∈ K}))
    (hne : (plHeight edgeGraph h02 ⁻¹' (K : Set ℝ)).Nonempty) :
    IsPathConnected (plHeight edgeGraph h02 ⁻¹' (K : Set ℝ)) := by
  rw [isPathConnected_iff_pathConnectedSpace, pathConnectedSpace_iff_zerothHomotopy]
  obtain ⟨p, hp⟩ := hne
  exact ⟨⟨ZerothHomotopy.mk ⟨p, hp⟩⟩, hs⟩

private theorem overlap_inter_eq :
    (overlappingIntervals false : Set ℝ) ∩ (overlappingIntervals true : Set ℝ) =
      (ioo (1 / 2) (3 / 2) : Set ℝ) := by
  ext y
  simp only [overlappingIntervals, coe_ioo, mem_inter_iff, Set.mem_Ioo]
  constructor
  · rintro ⟨⟨_, h₂⟩, h₃, _⟩
    exact ⟨h₃, h₂⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨⟨by linarith, h₂⟩, h₁, by linarith⟩

private theorem bool_finset_cases (τ : Finset Bool) (hτ : τ.Nonempty) :
    τ = {false} ∨ τ = {true} ∨ τ = {false, true} := by
  obtain ⟨b, hb⟩ := hτ
  by_cases hf : false ∈ τ <;> by_cases ht : true ∈ τ
  · right; right
    ext x
    cases x <;> simp [hf, ht]
  · left
    ext x
    cases x <;> simp [hf, ht]
  · right; left
    ext x
    cases x <;> simp [hf, ht]
  · exfalso
    cases b <;> contradiction

/-- Every nonempty finite intersection of the overlapping intervals has a path-connected
preimage under the single-edge height. -/
theorem singleEdge_preimageIntersectionsPathConnected :
    PreimageIntersectionsPathConnected edgeMap overlapCover := by
  intro τ hτ hne
  rcases bool_finset_cases τ hτ with rfl | rfl | rfl
  · simp only [Finset.set_biInter_singleton] at hne ⊢
    exact preimage_isPathConnected_of_subsingleton (overlap_components_subsingleton false) hne
  · simp only [Finset.set_biInter_singleton] at hne ⊢
    exact preimage_isPathConnected_of_subsingleton (overlap_components_subsingleton true) hne
  · simp only [Finset.set_biInter_insert, Finset.set_biInter_singleton] at hne ⊢
    rw [overlap_inter_eq] at hne ⊢
    exact preimage_isPathConnected_of_subsingleton
      ⟨fun _ _ => (preimageComponentsEquiv edgeGraph h02 _).injective
        (@Subsingleton.elim _
          (single_cellComponents_subsingleton ioo_half_zero ioo_half_two ioo_half_one) _ _)⟩
      hne

/-- The MultiNerve Mapper of the single edge is order-isomorphic to ordinary Mapper. -/
def singleEdgeMultiNerveOrderIso :
    multiNerveMapper edgeMap overlapCover ≃o {s // s ∈ mapper edgeMap overlapCover} :=
  multiNerveMapperOrderIso _ _
    (intersectionsPathSubsingleton_of_preimage _ _ singleEdge_preimageIntersectionsPathConnected)

/-- For the single edge, the projection onto the merged two-vertex, one-edge Mapper is
bijective: there are exactly two vertex cells and exactly one cell over the Mapper edge. -/
theorem singleEdge_multiNerveMapper_agrees :
    IntersectionsPathSubsingleton (componentCover edgeMap overlapCover) ∧
    Function.Bijective (multiNerveMapper_projection edgeMap overlapCover) ∧
    ⇑singleEdgeMultiNerveOrderIso = multiNerveMapper_projection edgeMap overlapCover ∧
    Nat.card {c : multiNerveMapper edgeMap overlapCover // c.support.card = 1} = 2 ∧
    ∃! c : multiNerveMapper edgeMap overlapCover,
      c.support = {edgeOverlapIndex false, edgeOverlapIndex true} := by
  have hsub := intersectionsPathSubsingleton_of_preimage _ _
    singleEdge_preimageIntersectionsPathConnected
  have hinj : Function.Injective (multiNerveMapper_projection edgeMap overlapCover) :=
    (projection_injective_iff _).2 hsub
  refine ⟨hsub, ⟨hinj, multiNerveMapper_projection_surjective _ _⟩, rfl,
    (Nat.card_congr (vertexCellEquiv _ _)).trans singleEdge_overlap_exact.1, ?_⟩
  obtain ⟨c, hc⟩ := multiNerveMapper_projection_surjective edgeMap overlapCover
    ⟨_, singleEdge_overlap_exact.2.1⟩
  refine ⟨c, congrArg Subtype.val hc, fun d hd => hinj ?_⟩
  rw [hc]
  exact Subtype.ext hd

end SingleEdge

/-! ## The one-point triangle -/

/-- Over the one-point domain every intersection has at most one path component. -/
theorem triangle_intersectionsPathSubsingleton :
    IntersectionsPathSubsingleton (componentCover triangleMap tripleUnitCover) := by
  intro s _
  refine ⟨fun c d => ?_⟩
  obtain ⟨x, rfl⟩ := ZerothHomotopy.mk_surjective c
  obtain ⟨y, rfl⟩ := ZerothHomotopy.mk_surjective d
  exact congrArg ZerothHomotopy.mk (Subtype.ext rfl)

/-- The one-point triangle satisfies `IntersectionsPathSubsingleton` and has a MultiNerve
Mapper cell with three-element support over the merged triangle; its target multiplicity is
not at most two. -/
theorem triangle_multiNerveMapper_cell :
    IntersectionsPathSubsingleton (componentCover triangleMap tripleUnitCover) ∧
    (∃ c : multiNerveMapper triangleMap tripleUnitCover, c.support.card = 3 ∧
      (multiNerveMapper_projection triangleMap tripleUnitCover c).1 =
        {triangleComponentIndex 0, triangleComponentIndex 1, triangleComponentIndex 2}) ∧
    ¬ CoverMultiplicityAtMost triangleMap tripleUnitCover 2 := by
  obtain ⟨c, hc⟩ := exists_cell_of_mem_nerve (V := componentCover triangleMap tripleUnitCover)
    triple_duplicate_cover_has_triangle.1
  have hcard : c.support.card = 3 := by
    rw [hc]
    exact triple_duplicate_cover_has_triangle.2
  refine ⟨triangle_intersectionsPathSubsingleton, ⟨c, hcard, hc⟩, fun hmult => ?_⟩
  have h := multiNerveMapper_card_le_of_multiplicity _ _ hmult c
  omega

/-! ## The empty domain -/

/-- The MultiNerve Mapper of the empty domain has no cells, matching the bottom ordinary
Mapper. -/
theorem emptyDomain_multiNerveMapper_isEmpty :
    IsEmpty (multiNerveMapper emptyDomainMap unitCover) ∧
      mapper emptyDomainMap unitCover =
        (⊥ : PreAbstractSimplicialComplex (ComponentIndex emptyDomainMap unitCover)) := by
  refine ⟨⟨fun c => ?_⟩, emptyDomain_mapper_eq_bot⟩
  obtain ⟨x, -⟩ := ZerothHomotopy.mk_surjective c.component
  exact isEmptyElim x.1

end

end TDA.Mapper.MultiNerveExamples
