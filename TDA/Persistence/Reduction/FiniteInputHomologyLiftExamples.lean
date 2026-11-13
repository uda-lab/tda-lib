import TDA.Persistence.Reduction.FiniteInputHomologyLiftCorrectness
import TDA.Persistence.Reduction.FiniteInputHomologyMapExamples

/-! A theta graph: a target class enters the image when a different loop is filled. -/

set_option maxRecDepth 10000
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 512
set_option backward.defeqAttrib.useBackward true

namespace TDA.Persistence.Reduction.FiniteInput.LiftExamples

open TDA.Simplicial TDA.Filtration

def theta : Input :=
  [({0}, 0), ({1}, 0), ({2}, 0), ({3}, 0),
    ({0, 3}, 1), ({0, 1}, 1), ({0, 2}, 1), ({1, 3}, 1), ({2, 3}, 1), ({0, 1, 3}, 2)]

def intoTheta (v : ℕ) : ℕ := if v = 10 then 0 else if v = 11 then 2 else 3

private local instance : NeZero theta.length := ⟨by decide⟩
private local instance : NeZero MapExamples.circle.length := ⟨by decide⟩
private local instance : NeZero MapExamples.components.length := ⟨by decide⟩
private local instance : NeZero MapExamples.point.length := ⟨by decide⟩

theorem theta_valid : Valid theta := by decide +kernel

theorem theta_map (b : ℤ) (hb : 1 ≤ b) :
    VertexMapInput MapExamples.circle theta 1 b intoTheta := by
  refine ⟨MapExamples.circle_valid, theta_valid, ?_⟩
  have hm : VertexMapCondition MapExamples.circle theta 1 1 intoTheta := by decide +kernel
  intro i hi
  obtain ⟨j, hj, hg⟩ := hm i hi
  exact ⟨j, hj, hg.trans hb⟩

private def thetaMatrix : Matrix (Fin 10) (Fin 10) (ZMod 2) := fun r c =>
  if c.val = 4 then (if r.val = 0 ∨ r.val = 3 then 1 else 0)
  else if c.val = 5 then (if r.val = 0 ∨ r.val = 1 then 1 else 0)
  else if c.val = 6 then (if r.val = 0 ∨ r.val = 2 then 1 else 0)
  else if c.val = 7 then (if r.val = 1 ∨ r.val = 3 then 1 else 0)
  else if c.val = 8 then (if r.val = 2 ∨ r.val = 3 then 1 else 0)
  else if c.val = 9 then (if r.val = 4 ∨ r.val = 5 ∨ r.val = 7 then 1 else 0)
  else 0

private theorem theta_boundary : boundary theta = thetaMatrix := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [boundary, theta, thetaMatrix, Finset.orderEmbOfFin_apply,
      Finset.sort_insert, Finset.sort_singleton] <;> decide +kernel

/-- Both independent graph cycles exist before the face is admitted. -/
theorem theta_cycles (b : ℤ) (hb : 1 ≤ b) :
    CycleInput theta 1 b (chainVector [5, 6, 7, 8]) ∧
    CycleInput theta 1 b (chainVector [4, 5, 7]) ∧
    CycleInput theta 1 b (chainVector [4, 6, 8]) := by
  have he : CycleInput theta 1 1 (chainVector [5, 6, 7, 8]) ∧
      CycleInput theta 1 1 (chainVector [4, 5, 7]) ∧
      CycleInput theta 1 1 (chainVector [4, 6, 8]) := by
    simp only [CycleInput, theta_boundary]
    decide +kernel
  exact ⟨cycleInput_mono _ _ _ _ hb _ he.1, cycleInput_mono _ _ _ _ hb _ he.2.1,
    cycleInput_mono _ _ _ _ hb _ he.2.2⟩

private def circleMatrix : Matrix (Fin 6) (Fin 6) (ZMod 2) := fun r c =>
  if c.val = 3 then (if r.val = 0 ∨ r.val = 1 then 1 else 0)
  else if c.val = 4 then (if r.val = 1 ∨ r.val = 2 then 1 else 0)
  else if c.val = 5 then (if r.val = 0 ∨ r.val = 2 then 1 else 0)
  else 0

private theorem circle_boundary : boundary MapExamples.circle = circleMatrix := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [boundary, MapExamples.circle, circleMatrix, Finset.orderEmbOfFin_apply,
      Finset.sort_insert, Finset.sort_singleton] <;> decide +kernel

private def circleRecord : Representative MapExamples.circle.length :=
  ⟨⟨1, 1, .essential⟩, 5, none, [3, 4, 5], none⟩

private def leftRecord : Representative theta.length :=
  ⟨⟨1, 1, .finite 2⟩, 7, some 9, [4, 5, 7], some [9]⟩

private def rightRecord : Representative theta.length :=
  ⟨⟨1, 1, .essential⟩, 8, none, [4, 6, 8], none⟩

private theorem circle_records : activeRepresentatives MapExamples.circle 1 1 = [circleRecord] := by
  unfold activeRepresentatives representedOccurrences pairedRepresentative essentialRepresentative
    pairedVector essentialVector change essentialIndices pivotPairs reduced trace
  rw [circle_boundary]
  decide +kernel

private theorem theta_records :
    activeRepresentatives theta 1 1 = [leftRecord, rightRecord] ∧
    activeRepresentatives theta 1 2 = [rightRecord] := by
  constructor <;>
    unfold activeRepresentatives representedOccurrences pairedRepresentative essentialRepresentative
      pairedVector essentialVector change essentialIndices pivotPairs reduced trace <;>
    rw [theta_boundary] <;> decide +kernel

private theorem left_normal : normalCoordinateVector theta (chainVector [4, 5, 7]) =
    Vector.ofFn (Pi.single (7 : Fin theta.length) 1) := by
  unfold normalCoordinateVector change pivotPairs reduced trace
  rw [theta_boundary]
  decide +kernel

private theorem outer_normal : normalCoordinateVector theta (chainVector [5, 6, 7, 8]) =
    Vector.ofFn (fun i : Fin theta.length => if i.val = 7 ∨ i.val = 8 then 1 else 0) := by
  unfold normalCoordinateVector change pivotPairs reduced trace
  rw [theta_boundary]
  decide +kernel

private theorem right_normal : normalCoordinateVector theta (chainVector [4, 6, 8]) =
    Vector.ofFn (Pi.single (8 : Fin theta.length) 1) := by
  unfold normalCoordinateVector change pivotPairs reduced trace
  rw [theta_boundary]
  decide +kernel

private theorem left_filling : fillingSupport theta 1 2 (chainVector [4, 5, 7]) = [9] := by
  unfold fillingSupport fillingVector normalCoordinateVector change pivotPairs reduced trace
  rw [theta_boundary]
  decide +kernel

/-- The image test has nonzero groups on both sides, with two target graph coordinates. -/
theorem theta_dimensions :
    (activeRepresentatives MapExamples.circle 1 1).length = 1 ∧
    (activeRepresentatives theta 1 1).length = 2 ∧
    (activeRepresentatives theta 1 2).length = 1 := by
  rw [circle_records, theta_records.1, theta_records.2]
  decide +kernel

/-- These query dimensions are the dimensions of the actual simplicial homology groups. -/
theorem theta_actual_dimensions :
    Module.finrank (ZMod 2)
      (simplicialHomology ((gradeFilter MapExamples.circle MapExamples.circle_valid).sublevel 1) (ZMod 2) 1) = 1 ∧
    Module.finrank (ZMod 2)
      (simplicialHomology ((gradeFilter theta theta_valid).sublevel 1) (ZMod 2) 1) = 2 ∧
    Module.finrank (ZMod 2)
      (simplicialHomology ((gradeFilter theta theta_valid).sublevel 2) (ZMod 2) 1) = 1 := by
  simpa only [sublevelHomology_finrank] using theta_dimensions

private theorem circle_record (j : BasisIndex MapExamples.circle 1 1) :
    basisRecord MapExamples.circle 1 1 j = circleRecord := by
  have hj : j.val = 0 := by have hj := j.isLt; have hn := theta_dimensions.1; omega
  have he := congrArg (fun rs => rs[j.val]?) circle_records
  rw [List.getElem?_eq_getElem j.isLt] at he
  have hr : ([circleRecord][j.val]?) = some circleRecord := by rw [hj]; rfl
  rw [hr] at he
  exact Option.some.inj he

private theorem theta_record_early (i : BasisIndex theta 1 1) :
    basisRecord theta 1 1 i = if i.val = 0 then leftRecord else rightRecord := by
  have he := congrArg (fun rs => rs[i.val]?) theta_records.1
  rw [List.getElem?_eq_getElem i.isLt] at he
  have hr : ([leftRecord, rightRecord][i.val]?) = some (if i.val = 0 then leftRecord else rightRecord) := by
    by_cases hi : i.val = 0
    · simp [hi]
    · have hi1 : i.val = 1 := by have hlt := i.isLt; have hn := theta_dimensions.2.1; omega
      simp [hi1]
  rw [hr] at he
  exact Option.some.inj he

private theorem theta_record_late (i : BasisIndex theta 1 2) :
    basisRecord theta 1 2 i = rightRecord := by
  have hi : i.val = 0 := by have hi := i.isLt; have hn := theta_dimensions.2.2; omega
  have he := congrArg (fun rs => rs[i.val]?) theta_records.2
  rw [List.getElem?_eq_getElem i.isLt] at he
  have hr : ([rightRecord][i.val]?) = some rightRecord := by rw [hi]; rfl
  rw [hr] at he
  exact Option.some.inj he

private theorem theta_coordinates_early (i : BasisIndex theta 1 1) :
    rawCycleCoordinates theta 1 1 (chainVector [5, 6, 7, 8]) i = 1 ∧
    rawCycleCoordinates theta 1 1 (chainVector [4, 5, 7]) i = (if i.val = 0 then 1 else 0) ∧
    rawCycleCoordinates theta 1 1 (chainVector [4, 6, 8]) i = (if i.val = 0 then 0 else 1) := by
  change (normalCoordinateVector theta (chainVector [5, 6, 7, 8]))[(basisRecord theta 1 1 i).birthIndex] = _ ∧
    (normalCoordinateVector theta (chainVector [4, 5, 7]))[(basisRecord theta 1 1 i).birthIndex] = _ ∧
    (normalCoordinateVector theta (chainVector [4, 6, 8]))[(basisRecord theta 1 1 i).birthIndex] = _
  rw [outer_normal, left_normal, right_normal]
  simp only [Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta]
  simp only [theta_record_early]
  by_cases hi : i.val = 0
  · simp only [if_pos hi]
    decide +kernel
  · simp only [if_neg hi]
    decide +kernel

private theorem theta_coordinates_late (i : BasisIndex theta 1 2) :
    rawCycleCoordinates theta 1 2 (chainVector [5, 6, 7, 8]) i = 1 ∧
    rawCycleCoordinates theta 1 2 (chainVector [4, 5, 7]) i = 0 ∧
    rawCycleCoordinates theta 1 2 (chainVector [4, 6, 8]) i = 1 := by
  change (normalCoordinateVector theta (chainVector [5, 6, 7, 8]))[(basisRecord theta 1 2 i).birthIndex] = _ ∧
    (normalCoordinateVector theta (chainVector [4, 5, 7]))[(basisRecord theta 1 2 i).birthIndex] = _ ∧
    (normalCoordinateVector theta (chainVector [4, 6, 8]))[(basisRecord theta 1 2 i).birthIndex] = _
  rw [outer_normal, left_normal, right_normal]
  simp only [Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta]
  simp only [theta_record_late]
  decide +kernel

private theorem circle_image : vertexVector MapExamples.circle theta 1 intoTheta
    (chainVector [3, 4, 5]) = chainVector [4, 6, 8] := by decide +kernel

private theorem early_entry (i : BasisIndex theta 1 1) (j : BasisIndex MapExamples.circle 1 1) :
    homologyMapMatrix MapExamples.circle theta 1 1 1 intoTheta i j = (if i.val = 0 then 0 else 1) := by
  rw [homologyMapMatrix_apply, circle_record]
  change rawCycleCoordinates theta 1 1 (vertexVector MapExamples.circle theta 1 intoTheta (chainVector [3, 4, 5])) i = (if i.val = 0 then 0 else 1)
  rw [circle_image]
  exact (theta_coordinates_early i).2.2

private theorem late_entry (i : BasisIndex theta 1 2) (j : BasisIndex MapExamples.circle 1 1) :
    homologyMapMatrix MapExamples.circle theta 1 1 2 intoTheta i j = 1 := by
  rw [homologyMapMatrix_apply, circle_record]
  change rawCycleCoordinates theta 1 2 (vertexVector MapExamples.circle theta 1 intoTheta (chainVector [3, 4, 5])) i = 1
  rw [circle_image]
  exact (theta_coordinates_late i).2.2

private theorem sum_one {n : ℕ} (hn : n = 1) (v : Fin n → ZMod 2) :
    ∑ j, v j = v ⟨0, by omega⟩ := by subst n; simp

private theorem early_mulVec (v : BasisIndex MapExamples.circle 1 1 → ZMod 2) (i : BasisIndex theta 1 1) :
    (homologyMapMatrix MapExamples.circle theta 1 1 1 intoTheta).mulVec v i =
      if i.val = 0 then 0 else v ⟨0, by have hn := theta_dimensions.1; omega⟩ := by
  by_cases hi : i.val = 0
  · simp [Matrix.mulVec, dotProduct, early_entry, hi]
  · simp only [Matrix.mulVec, dotProduct, early_entry, if_neg hi, one_mul]
    exact sum_one theta_dimensions.1 v

private theorem late_mulVec (v : BasisIndex MapExamples.circle 1 1 → ZMod 2) (i : BasisIndex theta 1 2) :
    (homologyMapMatrix MapExamples.circle theta 1 1 2 intoTheta).mulVec v i =
      v ⟨0, by have hn := theta_dimensions.1; omega⟩ := by
  simp only [Matrix.mulVec, dotProduct, late_entry, one_mul]
  exact sum_one theta_dimensions.1 v

private theorem circle_synthesis : cycleSynthesis MapExamples.circle 1 1 (fun _ => 1) = chainVector [3, 4, 5] := by
  change (∑ j : BasisIndex MapExamples.circle 1 1, (1 : ZMod 2) • chainVector (basisRecord MapExamples.circle 1 1 j).cycle) = _
  simp only [circle_record, one_smul, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    theta_dimensions.1]
  rfl

/-- The outer target class enters the source image exactly when the face is added. -/
theorem theta_executions :
    runHomologyLift MapExamples.circle theta 1 1 1 intoTheta (chainVector [5, 6, 7, 8]) = none ∧
    runHomologyLift MapExamples.circle theta 1 1 1 intoTheta (chainVector [4, 5, 7]) = none ∧
    runHomologyLift MapExamples.circle theta 1 1 2 intoTheta (chainVector [5, 6, 7, 8]) =
      some ⟨Vector.replicate _ 1, [3, 4, 5], [9]⟩ := by
  have h0 : 0 < (activeRepresentatives theta 1 1).length := by have hn := theta_dimensions.2.1; omega
  refine ⟨?_, ?_, ?_⟩
  · apply (runHomologyLift_eq_none_iff _ _ _ _ _ _ _).mpr
    rintro ⟨_, _, v, hv⟩
    have ha := congrFun hv ⟨0, h0⟩
    rw [early_mulVec, (theta_coordinates_early _).1] at ha
    simp at ha
  · apply (runHomologyLift_eq_none_iff _ _ _ _ _ _ _).mpr
    rintro ⟨_, _, v, hv⟩
    have ha := congrFun hv ⟨0, h0⟩
    rw [early_mulVec, (theta_coordinates_early _).2.1] at ha
    simp at ha
  · have hc : homologyLiftCoefficients MapExamples.circle theta 1 1 2 intoTheta
        (chainVector [5, 6, 7, 8]) = some (Vector.replicate _ 1) := by
      apply homologyLiftCoefficients_of_unique
      · ext i
        rw [late_mulVec, (theta_coordinates_late i).1]
        simp
      · intro v hv
        have hi : 0 < (activeRepresentatives theta 1 2).length := by have hn := theta_dimensions.2.2; omega
        have he := congrFun hv ⟨0, hi⟩
        rw [late_mulVec, (theta_coordinates_late _).1] at he
        funext j
        have hj : j = ⟨0, by have hn := theta_dimensions.1; omega⟩ := by
          apply Fin.ext
          have hj := j.isLt; have hn := theta_dimensions.1; omega
        simpa [hj] using he
    apply (runHomologyLift_eq_some_iff _ _ _ _ _ _ _ _).mpr
    refine ⟨theta_map 2 (by omega), (theta_cycles 2 (by omega)).1, _, hc, ?_⟩
    simp only [homologyLiftResult_eq]
    simp only [Fin.getElem_fin, Vector.getElem_replicate]
    rw [circle_synthesis, circle_image]
    have hs : supportChain (chainVector ([3, 4, 5] : List (Fin MapExamples.circle.length))) = [3, 4, 5] := by decide +kernel
    have hr : chainVector ([5, 6, 7, 8] : List (Fin theta.length)) - chainVector [4, 6, 8] = chainVector [4, 5, 7] := by decide +kernel
    rw [hs, hr, left_filling]

/-- Empty source homology still fills a nonzero null target, but cannot lift an essential class. -/
theorem empty_source_executions :
    runHomologyLift [] theta 1 0 2 id (chainVector [4, 5, 7]) =
      some ⟨Vector.replicate _ 0, [], [9]⟩ ∧
    runHomologyLift [] theta 1 0 2 id (chainVector [4, 6, 8]) = none := by
  constructor
  · have hz : rawCycleCoordinates theta 1 2 (chainVector [4, 5, 7]) = 0 := by
      ext i
      exact (theta_coordinates_late i).2.1
    rw [runHomologyLift_null [] theta 1 0 2 id (by decide +kernel) _
      (theta_cycles 2 (by omega)).2.1 hz, left_filling]
  · apply (runHomologyLift_eq_none_iff _ _ _ _ _ _ _).mpr
    rintro ⟨_, _, v, hv⟩
    have hi : 0 < (activeRepresentatives theta 1 2).length := by have hn := theta_dimensions.2.2; omega
    have he := congrFun hv ⟨0, hi⟩
    have hm : (homologyMapMatrix [] theta 1 0 2 id).mulVec v = 0 := by
      ext i
      change (∑ j : BasisIndex [] 1 0, homologyMapMatrix [] theta 1 0 2 id i j * v j) = 0
      apply Finset.sum_eq_zero
      intro j _
      have hj := j.isLt
      have hn : (activeRepresentatives [] 1 0).length = 0 := by decide +kernel
      omega
    rw [hm, (theta_coordinates_late _).2.2] at he
    exact zero_ne_one he

/-- Multiple source preimages use a deterministic solution; negative grades remain ordinary sublevels. -/
theorem component_executions :
    runHomologyLift MapExamples.components MapExamples.point 0 0 (-1) (fun _ => 42) (chainVector [0]) =
      some ⟨Vector.ofFn (fun i => if i.val = 1 then 1 else 0), [1], []⟩ ∧
    runHomologyLift MapExamples.point MapExamples.point 0 (-1) (-1) id (chainVector [0]) =
      some ⟨Vector.replicate _ 1, [0], []⟩ := by
  decide +kernel

/-- Zero targets select zero even with a kernel, empty complexes or an empty selected sublevel. -/
theorem zero_executions :
    runHomologyLift MapExamples.components MapExamples.point 0 0 (-1) (fun _ => 42) 0 =
      some ⟨Vector.replicate _ 0, [], []⟩ ∧
    runHomologyLift [] [] 7 (-100) 20 id 0 = some ⟨Vector.replicate _ 0, [], []⟩ ∧
    runHomologyLift MapExamples.point MapExamples.point 0 (-2) (-2) id 0 =
      some ⟨Vector.replicate _ 0, [], []⟩ :=
  ⟨runHomologyLift_zero _ _ _ _ _ _ (by decide +kernel),
    runHomologyLift_zero _ _ _ _ _ _ (by decide +kernel),
    runHomologyLift_zero _ _ _ _ _ _ (by decide +kernel)⟩

/-- Geometry and target support/degree/cycle conditions are checked before searching. -/
theorem invalid_executions :
    runHomologyLift [({0, 1}, 0)] [] 0 0 0 id 0 = none ∧
    runHomologyLift [] [({0, 1}, 0)] 0 0 0 id 0 = none ∧
    runHomologyLift MapExamples.components MapExamples.point 4 0 (-1) id 0 = none ∧
    runHomologyLift MapExamples.point MapExamples.point 0 (-1) (-2) id 0 = none ∧
    runHomologyLift [] MapExamples.point 1 0 (-1) id (chainVector [0]) = none ∧
    runHomologyLift [] MapExamples.point 0 0 (-2) id (chainVector [0]) = none ∧
    runHomologyLift [] theta 1 0 2 id (chainVector [4]) = none := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, ?_⟩
  apply (runHomologyLift_eq_none_iff _ _ _ _ _ _ _).mpr
  rintro ⟨_, hw, _⟩
  have he := hw.2
  rw [theta_boundary] at he
  have hn : thetaMatrix.mulVec (chainVector [4]) ≠ 0 := by decide +kernel
  exact hn he

/-- Rejection before the face is genuine nonmembership in the actual induced H₁ image. -/
theorem theta_actual_nonmembership :
    vectorSublevelClass theta theta_valid 1 1 (chainVector [5, 6, 7, 8])
        (theta_cycles 1 le_rfl).1 ∉ LinearMap.range
      (simplicialHomologyMap (ZMod 2)
        (validatedVertexMap MapExamples.circle theta MapExamples.circle_valid theta_valid 1 1
          intoTheta (theta_map 1 le_rfl).2.2) 1).hom ∧
    vectorSublevelClass theta theta_valid 1 1 (chainVector [4, 5, 7])
        (theta_cycles 1 le_rfl).2.1 ∉ LinearMap.range
      (simplicialHomologyMap (ZMod 2)
        (validatedVertexMap MapExamples.circle theta MapExamples.circle_valid theta_valid 1 1
          intoTheta (theta_map 1 le_rfl).2.2) 1).hom :=
  ⟨(runHomologyLift_eq_none_iff_not_mem_range _ _ _ _ _ _ _ _ (theta_map 1 le_rfl).2.2 _
      (theta_cycles 1 le_rfl).1).mp theta_executions.1,
    (runHomologyLift_eq_none_iff_not_mem_range _ _ _ _ _ _ _ _ (theta_map 1 le_rfl).2.2 _
      (theta_cycles 1 le_rfl).2.1).mp theta_executions.2.1⟩

/-- The nonzero filling really compares the input cycle with the actual source-chain image. -/
theorem theta_actual_certificate :
    ∃ (z : simplicialCycles ((gradeFilter MapExamples.circle MapExamples.circle_valid).sublevel 1) (ZMod 2) 1)
      (B : Chain ((gradeFilter theta theta_valid).sublevel 2) (ZMod 2) 2),
      sublevelChainVector MapExamples.circle MapExamples.circle_valid 1 1 z.1 = chainVector [3, 4, 5] ∧
      sublevelChainVector theta theta_valid 2 2 B = chainVector [9] ∧
      TDA.Simplicial.boundary _ (ZMod 2) 1 B =
        (vectorSublevelCycle theta theta_valid 1 2 (chainVector [5, 6, 7, 8])
          (theta_cycles 2 (by omega)).1).1 -
        vertexChainMap (ZMod 2)
          (validatedVertexMap MapExamples.circle theta MapExamples.circle_valid theta_valid 1 2
            intoTheta (theta_map 2 (by omega)).2.2) 1 z.1 ∧
      (simplicialHomologyMap (ZMod 2)
        (validatedVertexMap MapExamples.circle theta MapExamples.circle_valid theta_valid 1 2
          intoTheta (theta_map 2 (by omega)).2.2) 1).hom
        (simplicialHomologyClass (ZMod 2) _ 1 z) =
        vectorSublevelClass theta theta_valid 1 2 (chainVector [5, 6, 7, 8])
          (theta_cycles 2 (by omega)).1 := by
  obtain ⟨_, _, _, _, z, B, hs, _, hb, hd, he⟩ := runHomologyLift_correct
    MapExamples.circle theta 1 1 2 intoTheta (chainVector [5, 6, 7, 8]) _ theta_executions.2.2
  exact ⟨z, B, hs, hb, hd, he⟩

/-- Original edges outside the source image survive in the supplied target chain. -/
theorem theta_not_chain_preimage :
    vertexVector MapExamples.circle theta 1 intoTheta (chainVector [3, 4, 5]) = chainVector [4, 6, 8] ∧
    chainVector ([4, 6, 8] : List (Fin theta.length)) ≠ chainVector [5, 6, 7, 8] ∧
    chainVector ([9] : List (Fin theta.length)) ≠ 0 := by
  decide +kernel

end TDA.Persistence.Reduction.FiniteInput.LiftExamples
