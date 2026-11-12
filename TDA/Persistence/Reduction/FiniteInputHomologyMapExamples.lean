import TDA.Persistence.Reduction.FiniteInputHomologyMapCorrectness

/-! Finite induced maps with relabelling, collapsed faces and coincident chain images. -/

set_option maxRecDepth 10000
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 512
set_option backward.defeqAttrib.useBackward true

namespace TDA.Persistence.Reduction.FiniteInput.MapExamples

open TDA.Simplicial TDA.Filtration

def square : Input :=
  [({0}, 0), ({1}, 0), ({2}, 0), ({3}, 0),
    ({0, 1}, 1), ({1, 2}, 1), ({2, 3}, 1), ({0, 3}, 1)]

def circle : Input :=
  [({10}, 0), ({11}, 0), ({12}, 0), ({10, 11}, 1), ({11, 12}, 1), ({10, 12}, 1)]

def collapseEdge (v : ℕ) : ℕ := if v = 0 ∨ v = 3 then 10 else if v = 1 then 11 else 12

def point : Input := [({42}, -1)]
def components : Input := [({0}, 0), ({1}, 0)]
def path : Input := [({0}, 0), ({1}, 0), ({2}, 0), ({0, 1}, 1), ({1, 2}, 1)]
def edge : Input := [({5}, -4), ({9}, -4), ({5, 9}, -1)]
def lateEdge : Input := [({5}, -4), ({9}, -4), ({5, 9}, 2)]
def sourceEdge : Input := [({0}, -4), ({1}, -4), ({0, 1}, -1)]
def fold (v : ℕ) : ℕ := if v = 1 then 9 else 5
def relabel (v : ℕ) : ℕ := if v = 0 then 5 else 9
def swap (v : ℕ) : ℕ := if v = 0 then 1 else 0

private local instance : NeZero square.length := ⟨by decide⟩
private local instance : NeZero circle.length := ⟨by decide⟩
private local instance : NeZero path.length := ⟨by decide⟩
private local instance : NeZero edge.length := ⟨by decide⟩

theorem square_valid : Valid square := by decide +kernel
theorem circle_valid : Valid circle := by decide +kernel
theorem point_valid : Valid point := by decide +kernel
theorem components_valid : Valid components := by decide +kernel

private def squareMatrix : Matrix (Fin 8) (Fin 8) (ZMod 2) := fun r c =>
  if c.val = 4 then (if r.val = 0 ∨ r.val = 1 then 1 else 0)
  else if c.val = 5 then (if r.val = 1 ∨ r.val = 2 then 1 else 0)
  else if c.val = 6 then (if r.val = 2 ∨ r.val = 3 then 1 else 0)
  else if c.val = 7 then (if r.val = 0 ∨ r.val = 3 then 1 else 0)
  else 0

private def circleMatrix : Matrix (Fin 6) (Fin 6) (ZMod 2) := fun r c =>
  if c.val = 3 then (if r.val = 0 ∨ r.val = 1 then 1 else 0)
  else if c.val = 4 then (if r.val = 1 ∨ r.val = 2 then 1 else 0)
  else if c.val = 5 then (if r.val = 0 ∨ r.val = 2 then 1 else 0)
  else 0

private theorem square_boundary : boundary square = squareMatrix := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [boundary, square, squareMatrix, Finset.orderEmbOfFin_apply,
      Finset.sort_insert, Finset.sort_singleton] <;> decide +kernel

private theorem circle_boundary : boundary circle = circleMatrix := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [boundary, circle, circleMatrix, Finset.orderEmbOfFin_apply,
      Finset.sort_insert, Finset.sort_singleton] <;> decide +kernel

/-- The fourth square edge collapses, while the loop maps to the three target edges. -/
theorem square_chain_image :
    vertexVector square circle 1 collapseEdge (chainVector [4, 5, 6, 7]) = chainVector [3, 4, 5] ∧
    vertexVector square circle 1 collapseEdge (Pi.single 7 1) = 0 := by
  decide +kernel

/-- Two coincident image edges cancel; image supports must not be deduplicated. -/
theorem folded_path_chain_image :
    vertexVector path edge 1 fold (chainVector [3, 4]) = 0 := by
  decide +kernel

private def squareRecord : Representative square.length :=
  ⟨⟨1, 1, .essential⟩, 7, none, [4, 5, 6, 7], none⟩

private def circleRecord : Representative circle.length :=
  ⟨⟨1, 1, .essential⟩, 5, none, [3, 4, 5], none⟩

private theorem square_records : activeRepresentatives square 1 1 = [squareRecord] := by
  unfold activeRepresentatives representedOccurrences pairedRepresentative essentialRepresentative
    pairedVector essentialVector change essentialIndices pivotPairs reduced trace
  rw [square_boundary]
  decide +kernel

private theorem circle_records : activeRepresentatives circle 1 1 = [circleRecord] := by
  unfold activeRepresentatives representedOccurrences pairedRepresentative essentialRepresentative
    pairedVector essentialVector change essentialIndices pivotPairs reduced trace
  rw [circle_boundary]
  decide +kernel

private theorem square_length : (activeRepresentatives square 1 1).length = 1 := by
  rw [square_records]
  rfl

private theorem circle_length : (activeRepresentatives circle 1 1).length = 1 := by
  rw [circle_records]
  rfl

private theorem square_record (j : BasisIndex square 1 1) : basisRecord square 1 1 j = squareRecord := by
  have hj : j.val = 0 := by have hj := j.isLt; have hn := square_length; omega
  have he := congrArg (fun rs => rs[j.val]?) square_records
  rw [List.getElem?_eq_getElem j.isLt] at he
  have hr : ([squareRecord][j.val]?) = some squareRecord := by rw [hj]; rfl
  rw [hr] at he
  exact Option.some.inj he

private theorem circle_record (i : BasisIndex circle 1 1) : basisRecord circle 1 1 i = circleRecord := by
  have hi : i.val = 0 := by have hi := i.isLt; have hn := circle_length; omega
  have he := congrArg (fun rs => rs[i.val]?) circle_records
  rw [List.getElem?_eq_getElem i.isLt] at he
  have hr : ([circleRecord][i.val]?) = some circleRecord := by rw [hi]; rfl
  rw [hr] at he
  exact Option.some.inj he

private theorem singleton_rows {m n : ℕ} (hm : m = 1) (hn : n = 1)
    (M : Matrix (Fin m) (Fin n) (ZMod 2)) :
    (List.ofFn fun i => List.ofFn fun j => M i j) =
      [[M ⟨0, by omega⟩ ⟨0, by omega⟩]] := by
  subst m
  subst n
  rfl

private theorem square_entry (i : BasisIndex circle 1 1) (j : BasisIndex square 1 1) :
    homologyMapMatrix square circle 1 1 1 collapseEdge i j = 1 := by
  rw [homologyMapMatrix_apply]
  have hv : vertexVector square circle 1 collapseEdge (chainVector (basisRecord square 1 1 j).cycle) =
      chainVector (basisRecord circle 1 1 i).cycle := by
    rw [square_record, circle_record]
    exact square_chain_image.1
  rw [hv]
  have he := congrFun (rawCycleCoordinates_basisRecord circle 1 1 i) i
  simpa [Pi.single_apply] using he

/-- A noninjective map of differently labelled circles induces a nonzero H₁ map. -/
theorem square_execution : runHomologyMap square circle 1 1 1 collapseEdge = some [[1]] := by
  unfold runHomologyMap
  rw [if_pos (show VertexMapInput square circle 1 1 collapseEdge from by decide +kernel)]
  unfold homologyMapRows
  rw [singleton_rows circle_length square_length, square_entry]

/-- Constant maps have zero target H₁, represented by no rows and one source column. -/
theorem constant_execution : runHomologyMap square point 1 1 (-1) (fun _ => 42) = some [] := by
  unfold runHomologyMap
  rw [if_pos (show VertexMapInput square point 1 (-1) (fun _ => 42) from by decide +kernel)]
  apply congrArg some
  apply List.eq_nil_iff_length_eq_zero.mpr
  change (List.ofFn _).length = 0
  rw [List.length_ofFn]
  decide +kernel

/-- Distinct essential components can merge, and their order can be permuted. -/
theorem component_executions :
    runHomologyMap components point 0 0 (-1) (fun _ => 42) = some [[1, 1]] ∧
    runHomologyMap components components 0 0 0 swap = some [[0, 1], [1, 0]] ∧
    runHomologyMap components components 0 0 0 id = some [[1, 0], [0, 1]] := by
  decide +kernel

private def edgeMatrix : Matrix (Fin 3) (Fin 3) (ZMod 2) := fun r c =>
  if c.val = 2 ∧ r.val < 2 then 1 else 0

private theorem sourceEdge_boundary : boundary sourceEdge = edgeMatrix := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [boundary, sourceEdge, edgeMatrix, Finset.orderEmbOfFin_apply,
      Finset.sort_insert, Finset.sort_singleton] <;> decide +kernel

private theorem lateEdge_boundary : boundary lateEdge = edgeMatrix := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [boundary, lateEdge, edgeMatrix, Finset.orderEmbOfFin_apply,
      Finset.sort_insert, Finset.sort_singleton] <;> decide +kernel

/-- Admission checks all face degrees; unselected edges impose no condition. -/
theorem grade_executions :
    runHomologyMap sourceEdge lateEdge 0 (-4) (-4) relabel = some [[1, 0], [0, 1]] ∧
    runHomologyMap sourceEdge lateEdge 0 (-1) (-1) relabel = none ∧
    runHomologyMap sourceEdge components 0 (-1) 0 id = none ∧
    runHomologyMap sourceEdge lateEdge 0 (-1) 2 relabel = some [[1]] := by
  unfold runHomologyMap
  simp only [homologyMapRows_eq_map]
  unfold normalCoordinateVector
    activeRepresentatives representedOccurrences pairedRepresentative essentialRepresentative
    pairedVector essentialVector change essentialIndices pivotPairs reduced trace
  rw [sourceEdge_boundary, lateEdge_boundary]
  decide +kernel

private theorem empty_invalid_executions :
    runHomologyMap [] components 0 0 0 id = some [[], []] ∧
    runHomologyMap components [] 0 (-1) 0 id = some [] ∧
    runHomologyMap components [] 0 0 0 id = none ∧
    runHomologyMap [] [] 99 (-100) 42 id = some [] ∧
    runHomologyMap [({0, 1}, 0)] [] 0 (-1) 0 id = none ∧
    runHomologyMap [] [({42, 43}, 0)] 0 (-100) 0 id = none ∧
    runHomologyMap components point 0 0 (-1) id = none ∧
    runHomologyMap point point 0 (-1) (-2) id = none := by
  decide +kernel

theorem square_map : VertexMapCondition square circle 1 1 collapseEdge := by decide +kernel

private def squareIndex : BasisIndex square 1 1 := ⟨0, by have h := square_length; omega⟩
private def circleIndex : BasisIndex circle 1 1 := ⟨0, by have h := circle_length; omega⟩

/-- The nonzero coefficient represents a genuinely nonzero actual H₁ image. -/
theorem square_actual_map_nonzero :
    ∃ x : simplicialHomology ((gradeFilter square square_valid).sublevel 1) (ZMod 2) 1,
      (simplicialHomologyMap (ZMod 2)
        (validatedVertexMap square circle square_valid circle_valid 1 1 collapseEdge square_map) 1).hom x ≠ 0 := by
  refine ⟨basisClass square square_valid 1 1 squareIndex, ?_⟩
  intro hz
  have he := homologyMapMatrix_correct square circle square_valid circle_valid 1 1 1 collapseEdge
    square_map (basisClass square square_valid 1 1 squareIndex)
  rw [hz, map_zero, sublevelCoordinates_basisClass, Matrix.mulVec_single_one] at he
  have hv := congrFun he circleIndex
  have hc : (0 : ZMod 2) = 1 := by
    simpa only [Pi.zero_apply, Matrix.col_apply, square_entry] using hv
  exact zero_ne_one hc

private def component0 : BasisIndex components 0 0 := ⟨0, by decide +kernel⟩
private def component1 : BasisIndex components 0 0 := ⟨1, by decide +kernel⟩

/-- Merging two components gives an actual noninjective homology map. -/
theorem component_actual_map_not_injective :
    ¬ Function.Injective (simplicialHomologyMap (ZMod 2)
      (validatedVertexMap components point components_valid point_valid 0 (-1) (fun _ => 42)
        (by decide +kernel)) 0).hom := by
  intro hinj
  have hcols : (homologyMapMatrix components point 0 0 (-1) (fun _ => 42)).col component0 =
      (homologyMapMatrix components point 0 0 (-1) (fun _ => 42)).col component1 := by
    decide +kernel
  have he : (simplicialHomologyMap (ZMod 2)
      (validatedVertexMap components point components_valid point_valid 0 (-1) (fun _ => 42)
        (by decide +kernel)) 0).hom (basisClass components components_valid 0 0 component0) =
      (simplicialHomologyMap (ZMod 2)
      (validatedVertexMap components point components_valid point_valid 0 (-1) (fun _ => 42)
        (by decide +kernel)) 0).hom (basisClass components components_valid 0 0 component1) := by
    apply (sublevelCoordinates point point_valid 0 (-1)).injective
    rw [homologyMapMatrix_correct, homologyMapMatrix_correct, sublevelCoordinates_basisClass,
      sublevelCoordinates_basisClass, Matrix.mulVec_single_one, Matrix.mulVec_single_one]
    exact hcols
  have hb := hinj he
  have hi : component0 = component1 := (sublevelBasis components components_valid 0 0).injective (by
    rw [sublevelBasis_apply, sublevelBasis_apply]
    exact hb)
  have hc : (0 : ℕ) = 1 := congrArg Fin.val hi
  exact Nat.zero_ne_one hc

/-- The executed nonidentity permutation composes to the executed identity. -/
theorem swap_composition :
    runHomologyMap components components 0 0 0 (swap ∘ swap) = some [[1, 0], [0, 1]] ∧
    homologyMapMatrix components components 0 0 0 (swap ∘ swap) =
      homologyMapMatrix components components 0 0 0 swap *
        homologyMapMatrix components components 0 0 0 swap := by
  exact ⟨by decide +kernel,
    homologyMapMatrix_comp components components components components_valid components_valid
      components_valid 0 0 0 0 swap swap (by decide +kernel) (by decide +kernel)⟩

private theorem inclusion_execution :
    runHomologyMap sourceEdge sourceEdge 0 (-4) (-1) id = some [[0, 1]] := by
  unfold runHomologyMap
  simp only [homologyMapRows_eq_map]
  unfold normalCoordinateVector
    activeRepresentatives representedOccurrences pairedRepresentative essentialRepresentative
    pairedVector essentialVector change essentialIndices pivotPairs reduced trace
  rw [sourceEdge_boundary]
  decide +kernel

end TDA.Persistence.Reduction.FiniteInput.MapExamples
