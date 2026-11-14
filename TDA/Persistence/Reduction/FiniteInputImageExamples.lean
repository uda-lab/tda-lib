import TDA.Persistence.Reduction.FiniteInputImage
import TDA.Persistence.Reduction.FiniteInputExamples
import TDA.Persistence.Reduction.FiniteInputHomologyMapExamples
import TDA.Persistence.Reduction.FiniteInputHomologyDimensionsCorrectness

/-!
# Consumers of finite-input image persistence

The validator rejects a delayed image edge even when an earlier query passes.
A circle maps into a triangle that is filled at grade three: its H₁ image
survives from grade one to two and vanishes from grade one to three. The
numerical witnesses reuse the existing homology-map dimension correctness API;
the semantic adapter itself is independent of that evaluator.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option maxRecDepth 10000

namespace TDA.Persistence.Reduction.FiniteInput.ImageExamples

open TDA.Simplicial TDA.Filtration CategoryTheory

/-- Identity, inclusion, collapsed faces, coincident images and empty inputs validate globally. -/
theorem validator_accepts :
    validateGlobalVertexMap MapExamples.sourceEdge MapExamples.sourceEdge id = true ∧
    validateGlobalVertexMap Examples.hollow Examples.filled id = true ∧
    validateGlobalVertexMap MapExamples.square MapExamples.circle MapExamples.collapseEdge = true ∧
    validateGlobalVertexMap MapExamples.path MapExamples.edge MapExamples.fold = true ∧
    validateGlobalVertexMap [] MapExamples.point id = true ∧
    validateGlobalVertexMap [] [] id = true := by
  decide +kernel

/-- An early query cannot certify global grade preservation; invalid geometry is always rejected. -/
theorem validator_rejects :
    VertexMapInput MapExamples.sourceEdge MapExamples.lateEdge (-4) (-4) MapExamples.relabel ∧
    validateGlobalVertexMap MapExamples.sourceEdge MapExamples.lateEdge MapExamples.relabel = false ∧
    validateGlobalVertexMap [({0, 1}, 0)] [] id = false ∧
    validateGlobalVertexMap [({0, 1}, 0)] MapExamples.point (fun _ => 42) = false ∧
    validateGlobalVertexMap [] [({0, 1}, 0)] id = false ∧
    validateGlobalVertexMap MapExamples.components [] id = false := by
  decide +kernel

/-- The existing triangle, with its filling delayed until grade three. -/
def filling : Input :=
  [({0}, 0), ({1}, 0), ({2}, 0), ({0, 1}, 1), ({1, 2}, 1),
    ({0, 2}, 1), ({0, 1, 2}, 3)]

theorem filling_valid : Valid filling := by decide +kernel

theorem filling_global : GlobalVertexMapCondition Examples.hollow filling id := by decide +kernel

/-- Sample at grades one, two and three; both cross-stage comparisons are strict. -/
def fillingStages : Fin 3 →o ℤ where
  toFun i := (i.val : ℤ) + 1
  monotone' := by
    intro i j hij
    change (i.val : ℤ) + 1 ≤ (j.val : ℤ) + 1
    have hv : i.val ≤ j.val := hij
    omega

noncomputable def fillingMap :=
  sampledHomologyMap Examples.hollow filling Examples.hollow_valid filling_valid id filling_global
    1 fillingStages

private theorem filling_boundary : boundary filling = Examples.triangleMatrix := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [boundary, filling, Examples.triangleMatrix, Finset.orderEmbOfFin_apply,
      Finset.sort_insert, Finset.sort_singleton] <;> decide +kernel

private local instance : NeZero Examples.hollow.length := ⟨by decide⟩
private local instance : NeZero filling.length := ⟨by decide⟩

private def sourceRecord : Representative Examples.hollow.length :=
  ⟨⟨1, 1, .essential⟩, 5, none, [3, 4, 5], none⟩

private def targetRecord : Representative filling.length :=
  ⟨⟨1, 1, .finite 3⟩, 5, some 6, [3, 4, 5], some [6]⟩

private theorem source_records : activeRepresentatives Examples.hollow 1 1 = [sourceRecord] := by
  unfold activeRepresentatives representedOccurrences pairedRepresentative essentialRepresentative
    pairedVector essentialVector change essentialIndices pivotPairs reduced trace
  rw [Examples.hollow_boundary]
  decide +kernel

private theorem target_records : activeRepresentatives filling 1 2 = [targetRecord] ∧
    activeRepresentatives filling 1 3 = [] := by
  constructor <;>
    unfold activeRepresentatives representedOccurrences pairedRepresentative essentialRepresentative
      pairedVector essentialVector change essentialIndices pivotPairs reduced trace <;>
    rw [filling_boundary] <;> decide +kernel

private theorem source_length : (activeRepresentatives Examples.hollow 1 1).length = 1 := by
  rw [source_records]
  rfl

private theorem target_length : (activeRepresentatives filling 1 2).length = 1 := by
  rw [target_records.1]
  rfl

private theorem target_dead : (activeRepresentatives filling 1 3).length = 0 := by
  rw [target_records.2]
  rfl

private def sourceIndex : BasisIndex Examples.hollow 1 1 := ⟨0, by rw [source_records]; decide⟩
private def targetIndex : BasisIndex filling 1 2 := ⟨0, by rw [target_records.1]; decide⟩

private theorem source_record (j : BasisIndex Examples.hollow 1 1) :
    basisRecord Examples.hollow 1 1 j = sourceRecord := by
  have he := congrArg (fun rs => rs[j.val]?) source_records
  rw [List.getElem?_eq_getElem j.isLt] at he
  have hj : j.val = 0 := by have hi := j.isLt; have hn := source_length; omega
  have hr : ([sourceRecord][j.val]?) = some sourceRecord := by rw [hj]; rfl
  rw [hr] at he
  exact Option.some.inj he

private theorem target_record (i : BasisIndex filling 1 2) :
    basisRecord filling 1 2 i = targetRecord := by
  have he := congrArg (fun rs => rs[i.val]?) target_records.1
  rw [List.getElem?_eq_getElem i.isLt] at he
  have hi : i.val = 0 := by have hi := i.isLt; have hn := target_length; omega
  have hr : ([targetRecord][i.val]?) = some targetRecord := by rw [hi]; rfl
  rw [hr] at he
  exact Option.some.inj he

private theorem filling_entry (i : BasisIndex filling 1 2) (j : BasisIndex Examples.hollow 1 1) :
    homologyMapMatrix Examples.hollow filling 1 1 2 id i j = 1 := by
  rw [homologyMapMatrix_apply]
  have hv : vertexVector Examples.hollow filling 1 id
      (chainVector (basisRecord Examples.hollow 1 1 j).cycle) =
      chainVector (basisRecord filling 1 2 i).cycle := by
    rw [source_record, target_record]
    decide +kernel
  rw [hv]
  simpa only [Pi.single_apply, ite_true] using
    congrFun (rawCycleCoordinates_basisRecord filling 1 2 i) i

private theorem filling_surjective :
    Function.Surjective (homologyMapMatrix Examples.hollow filling 1 1 2 id).mulVecLin := by
  intro v
  refine ⟨Pi.single sourceIndex (v targetIndex), ?_⟩
  funext i
  change (homologyMapMatrix Examples.hollow filling 1 1 2 id).mulVec _ i = _
  rw [Matrix.mulVec_single]
  change homologyMapMatrix Examples.hollow filling 1 1 2 id i sourceIndex * v targetIndex = v i
  rw [filling_entry, one_mul]
  have hi : i = targetIndex := by
    apply Fin.ext
    have hi := i.isLt
    have hn := target_length
    change i.val = 0
    omega
  rw [hi]

private theorem filling_dimensions :
    (homologyMapDimensions Examples.hollow filling 1 1 2 id).rank = 1 ∧
    (homologyMapDimensions Examples.hollow filling 1 1 3 id).rank = 0 := by
  constructor
  · rw [homologyMapDimensions_rank, LinearMap.range_eq_top.mpr filling_surjective,
      finrank_top, Module.finrank_fintype_fun_eq_card, Fintype.card_fin, target_records.1]
    rfl
  · let : IsEmpty (BasisIndex filling 1 3) := ⟨fun i => by
      have hi := i.isLt
      have hn := target_dead
      omega⟩
    have hz : (homologyMapMatrix Examples.hollow filling 1 1 3 id).mulVecLin = 0 :=
      Subsingleton.elim _ _
    rw [homologyMapDimensions_rank, hz]
    simp

/-- The geometric cross-stage map really is the inclusion into the target sublevel. -/
theorem filling_inclusion (a b : ℤ) (hab : a ≤ b) :
    ∃ hle : (gradeFilter Examples.hollow Examples.hollow_valid).sublevel a ≤
        (gradeFilter filling filling_valid).sublevel b,
      simplicialHomologyMap (ZMod 2)
        (validatedVertexMap Examples.hollow filling Examples.hollow_valid filling_valid a b id
          (filling_global.cross _ _ _ a b hab)) 1 = simplicialHomologyIncl (ZMod 2) hle 1 := by
  have hle : (gradeFilter Examples.hollow Examples.hollow_valid).sublevel a ≤
      (gradeFilter filling filling_valid).sublevel b := by
    intro face hf
    change face ∈ (gradeFilter filling filling_valid).sublevel b
    simpa only [Finset.image_id] using
      (vertexMapCondition_iff Examples.hollow filling Examples.hollow_valid filling_valid
      a b id).mp (filling_global.cross _ _ _ a b hab) face hf
  refine ⟨hle, ?_⟩
  rw [← simplicialHomologyMap_inclusion]
  exact congrArg (fun q => simplicialHomologyMap (ZMod 2) q 1) (VertexMap.ext (fun _ => rfl))

/-- The actual cross-threshold inclusion has range dimension one before filling and zero after. -/
theorem filling_actual_ranges :
    Module.finrank (ZMod 2) (LinearMap.range
      (simplicialHomologyMap (ZMod 2)
        (validatedVertexMap Examples.hollow filling Examples.hollow_valid filling_valid 1 2 id
          (filling_global.cross _ _ _ 1 2 (by decide))) 1).hom) = 1 ∧
    Module.finrank (ZMod 2) (LinearMap.range
      (simplicialHomologyMap (ZMod 2)
        (validatedVertexMap Examples.hollow filling Examples.hollow_valid filling_valid 1 3 id
          (filling_global.cross _ _ _ 1 3 (by decide))) 1).hom) = 0 := by
  constructor <;> rw [← homologyMapDimensions_rank_actual]
  · exact filling_dimensions.1
  · exact filling_dimensions.2

/-- The H₁ image survives a strict stage increase, then dies on the target filling. -/
theorem filling_image_ranks :
    structureMapRank (finiteImage fillingMap) 0 1 (by decide) = 1 ∧
    structureMapRank (finiteImage fillingMap) 0 2 (by decide) = 0 := by
  constructor <;> rw [fillingMap, sampledHomologyMap_image_rank]
  · exact filling_actual_ranges.1
  · exact filling_actual_ranges.2

/-- A genuinely nonidentity vertex map, including an edge collapse, has a nonzero actual H₁ image. -/
theorem collapsed_component_nonzero :
    let h : GlobalVertexMapCondition MapExamples.square MapExamples.circle MapExamples.collapseEdge :=
      by decide +kernel
    ∃ x, ((sampledHomologyMap MapExamples.square MapExamples.circle MapExamples.square_valid
      MapExamples.circle_valid MapExamples.collapseEdge h 1 fillingStages).app 0).hom x ≠ 0 := by
  exact MapExamples.square_actual_map_nonzero

/-- The collapsed-square transformation has a one-dimensional actual image fiber. -/
theorem collapsed_image_rank :
    let h : GlobalVertexMapCondition MapExamples.square MapExamples.circle MapExamples.collapseEdge :=
      by decide +kernel
    structureMapRank (finiteImage (sampledHomologyMap MapExamples.square MapExamples.circle
      MapExamples.square_valid MapExamples.circle_valid MapExamples.collapseEdge h 1 fillingStages))
        0 0 le_rfl = 1 := by
  dsimp only
  rw [sampledHomologyMap_image_rank]
  let F := (simplicialHomologyMap (ZMod 2)
    (validatedVertexMap MapExamples.square MapExamples.circle MapExamples.square_valid
      MapExamples.circle_valid 1 1 MapExamples.collapseEdge MapExamples.square_map) 1).hom
  change Module.finrank (ZMod 2) (LinearMap.range F) = 1
  have hd : Module.finrank (ZMod 2) (simplicialHomology
      ((gradeFilter MapExamples.circle MapExamples.circle_valid).sublevel 1) (ZMod 2) 1) = 1 := by
    rw [sublevelHomology_finrank]
    exact (runHomologyMap_row_count _ _ _ _ _ _ _ MapExamples.square_execution).symm
  have hn : F ≠ 0 := by
    intro he
    obtain ⟨x, hx⟩ := MapExamples.square_actual_map_nonzero
    apply hx
    change F x = 0
    rw [he]
    rfl
  have hs : Function.Surjective F := surjective_of_nonzero_of_finrank_eq_one hd hn
  rw [LinearMap.range_eq_top.mpr hs, finrank_top]
  exact hd

/-- Repeated negative thresholds use the same actual maps and inclusions. -/
def negativeStages : Fin 3 →o ℤ where
  toFun i := if i.val < 2 then -4 else -1
  monotone' := by
    intro i j hij
    change (if i.val < 2 then (-4 : ℤ) else -1) ≤ (if j.val < 2 then (-4 : ℤ) else -1)
    split_ifs <;> omega

theorem negative_repeated_identity :
    structureMapRank (finiteImage (sampledHomologyMap MapExamples.sourceEdge MapExamples.sourceEdge
      (by decide +kernel) (by decide +kernel) id (globalVertexMapCondition_id _) 0 negativeStages))
        0 1 (by decide) =
      structureMapRank (sampledHomology MapExamples.sourceEdge (by decide +kernel) 0 negativeStages)
        0 1 (by decide) ∧
    (sampledHomologyMap MapExamples.sourceEdge MapExamples.sourceEdge (by decide +kernel)
      (by decide +kernel) id (globalVertexMapCondition_id _) 0 negativeStages).app 0 =
      𝟙 ((sampledHomology MapExamples.sourceEdge (by decide +kernel) 0 negativeStages).obj 0) := by
  constructor
  · exact sampledHomologyMap_id_image_rank _ _ _ _ _ _ _
  · rw [sampledHomologyMap_id]
    rfl

private local instance : NeZero MapExamples.sourceEdge.length := ⟨by decide⟩

private def edgePair : Representative MapExamples.sourceEdge.length :=
  ⟨⟨0, -4, .finite (-1)⟩, 1, some 2, [0, 1], some [2]⟩
private def edgeEssential : Representative MapExamples.sourceEdge.length :=
  ⟨⟨0, -4, .essential⟩, 0, none, [0], none⟩

private theorem edge_records : activeRepresentatives MapExamples.sourceEdge 0 (-4) = [edgePair, edgeEssential] ∧
    activeRepresentatives MapExamples.sourceEdge 0 (-1) = [edgeEssential] := by
  constructor <;>
    unfold activeRepresentatives representedOccurrences pairedRepresentative essentialRepresentative
      pairedVector essentialVector change essentialIndices pivotPairs reduced trace <;>
    rw [show boundary MapExamples.sourceEdge = Examples.edgeMatrix from Examples.negative_boundary] <;>
    decide +kernel

private theorem edge_early_length : (activeRepresentatives MapExamples.sourceEdge 0 (-4)).length = 2 := by
  rw [edge_records.1]
  rfl
private theorem edge_late_length : (activeRepresentatives MapExamples.sourceEdge 0 (-1)).length = 1 := by
  rw [edge_records.2]
  rfl
private def edgeSource : BasisIndex MapExamples.sourceEdge 0 (-4) := ⟨1, by rw [edge_early_length]; decide⟩
private def edgeTarget : BasisIndex MapExamples.sourceEdge 0 (-1) := ⟨0, by rw [edge_late_length]; decide⟩

private theorem edge_source_record : basisRecord MapExamples.sourceEdge 0 (-4) edgeSource = edgeEssential := by
  have he := congrArg (fun rs => rs[edgeSource.val]?) edge_records.1
  rw [List.getElem?_eq_getElem edgeSource.isLt] at he
  exact Option.some.inj he
private theorem edge_target_record : basisRecord MapExamples.sourceEdge 0 (-1) edgeTarget = edgeEssential := by
  have he := congrArg (fun rs => rs[edgeTarget.val]?) edge_records.2
  rw [List.getElem?_eq_getElem edgeTarget.isLt] at he
  exact Option.some.inj he

private theorem edge_surjective : Function.Surjective (basisTransition MapExamples.sourceEdge 0 (-4) (-1)).mulVecLin := by
  intro v
  refine ⟨Pi.single edgeSource (v edgeTarget), ?_⟩
  funext i
  rw [Matrix.mulVecLin_apply, Matrix.mulVec_single]
  change basisTransition MapExamples.sourceEdge 0 (-4) (-1) i edgeSource * v edgeTarget = v i
  have hi : i = edgeTarget := by
    apply Fin.ext
    have hi := i.isLt
    have hn := edge_late_length
    change i.val = 0
    omega
  subst i
  rw [basisTransition_apply, edge_source_record, edge_target_record]
  simp

private theorem negative_dimensions :
    (homologyMapDimensions MapExamples.sourceEdge MapExamples.sourceEdge 0 (-4) (-4) id).rank = 2 ∧
    (homologyMapDimensions MapExamples.sourceEdge MapExamples.sourceEdge 0 (-4) (-1) id).rank = 1 := by
  have hv : Valid MapExamples.sourceEdge := by decide +kernel
  constructor
  · rw [homologyMapDimensions_rank, homologyMapMatrix_id _ hv,
      Matrix.mulVecLin_one, LinearMap.range_id, finrank_top,
      Module.finrank_fintype_fun_eq_card, Fintype.card_fin, edge_early_length]
  · rw [homologyMapDimensions_rank,
      homologyMapMatrix_inclusion _ hv 0 (-4) (-1) (by decide),
      LinearMap.range_eq_top.mpr edge_surjective, finrank_top,
      Module.finrank_fintype_fun_eq_card, Fintype.card_fin, edge_late_length]

/-- Two components persist across the repeated negative grade, then merge at the edge grade. -/
theorem negative_image_ranks :
    structureMapRank (finiteImage (sampledHomologyMap MapExamples.sourceEdge MapExamples.sourceEdge
      (by decide +kernel) (by decide +kernel) id (globalVertexMapCondition_id _) 0
      negativeStages)) 0 1 (by decide) = 2 ∧
    structureMapRank (finiteImage (sampledHomologyMap MapExamples.sourceEdge MapExamples.sourceEdge
      (by decide +kernel) (by decide +kernel) id (globalVertexMapCondition_id _) 0
      negativeStages)) 0 2 (by decide) = 1 := by
  constructor <;> rw [sampledHomologyMap_image_rank, ← homologyMapDimensions_rank_actual]
  · exact negative_dimensions.1
  · exact negative_dimensions.2


private theorem empty_source_map (ys : Input) (hy : Valid ys) (p : ℕ)
    {s : ℕ} (t : Fin s →o ℤ) (f : ℕ → ℕ) :
    sampledHomologyMap [] ys (by decide +kernel) hy f (by intro i; exact Fin.elim0 i) p t = 0 := by
  apply NatTrans.ext
  funext i
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  have hx : x = 0 := by
    apply (sublevelCoordinates [] (by decide +kernel) p (t i)).injective
    funext q
    exact Fin.elim0 q
  rw [hx, map_zero]
  rfl

/-- Empty source spaces have zero actual image rank in every degree and at arbitrary thresholds. -/
theorem empty_image_ranks (ys : Input) (hy : Valid ys) (p : ℕ)
    {s : ℕ} (t : Fin s →o ℤ) (f : ℕ → ℕ) (i j : Fin s) (hij : i ≤ j) :
    structureMapRank (finiteImage (sampledHomologyMap [] ys (by decide +kernel) hy f
      (by intro q; exact Fin.elim0 q) p t)) i j hij = 0 := by
  rw [empty_source_map, finiteImage_zero_structureMapRank]

/-- Sampling an empty chain constructs the actual empty natural transformation. -/
theorem empty_chain_components (xs ys : Input) (hx : Valid xs) (hy : Valid ys)
    (f : ℕ → ℕ) (h : GlobalVertexMapCondition xs ys f) (p : ℕ) (t : Fin 0 →o ℤ) :
    ∀ i : Fin 0, (sampledHomologyMap xs ys hx hy f h p t).app i = 0 := by
  intro i
  exact Fin.elim0 i

end TDA.Persistence.Reduction.FiniteInput.ImageExamples
