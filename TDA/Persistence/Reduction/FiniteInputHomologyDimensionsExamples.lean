import TDA.Persistence.Reduction.FiniteInputHomologyDimensionsCorrectness
import TDA.Persistence.Reduction.FiniteInputHomologyLiftExamples

/-! Rectangular maps, a disappearing H₁ image and validation at zero-dimensional queries. -/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

namespace TDA.Persistence.Reduction.FiniteInput.DimensionExamples

open TDA.Simplicial TDA.Filtration

/-- Three components at a negative tied grade. -/
def source : Input := [({0}, -2), ({1}, -2), ({2}, -2)]

/-- Four target components; two are outside the map's image. -/
def target : Input := [({10}, -2), ({11}, -2), ({12}, -2), ({13}, -2)]

def merge (v : ℕ) : ℕ := if v = 0 then 10 else 11

theorem rectangular_input : VertexMapInput source target (-2) (-2) merge := by decide +kernel

/-- A `3 → 4` map has rank two and nullity one, rather than the smaller ambient dimension. -/
theorem rectangular_run : runHomologyDimensions source target 0 (-2) (-2) merge = some ⟨2, 1⟩ := by
  decide +kernel

/-- The returned numbers measure the actual signed simplicial homology map. -/
theorem rectangular_actual :
    let F := (simplicialHomologyMap (ZMod 2)
      (validatedVertexMap source target rectangular_input.1 rectangular_input.2.1 (-2) (-2) merge
        rectangular_input.2.2) 0).hom
    Module.finrank (ZMod 2) (LinearMap.range F) = 2 ∧
      Module.finrank (ZMod 2) (LinearMap.ker F) = 1 ∧
      Module.finrank (ZMod 2)
        (simplicialHomology ((gradeFilter target rectangular_input.2.1).sublevel (-2)) (ZMod 2) 0) = 4 ∧
      ¬ Function.Injective F ∧ ¬ Function.Surjective F := by
  have he := (runHomologyDimensions_eq_some_iff _ _ _ _ _ _ _).mp rectangular_run |>.2
  have hr := homologyMapDimensions_rank_actual source target rectangular_input.1 rectangular_input.2.1
    0 (-2) (-2) merge rectangular_input.2.2
  have hk := homologyMapDimensions_nullity_actual source target rectangular_input.1 rectangular_input.2.1
    0 (-2) (-2) merge rectangular_input.2.2
  have hi := homologyMapDimensions_injective_iff source target rectangular_input.1 rectangular_input.2.1
    0 (-2) (-2) merge rectangular_input.2.2
  have hs := homologyMapDimensions_surjective_iff source target rectangular_input.1 rectangular_input.2.1
    0 (-2) (-2) merge rectangular_input.2.2
  rw [← he] at hr hk hi hs
  have hd : (activeRepresentatives target 0 (-2)).length = 4 := by decide +kernel
  rw [hd] at hs
  exact ⟨hr.symm, hk.symm, by rw [sublevelHomology_finrank, hd], by simpa using hi, by simpa using hs⟩

private def thetaBoundary : Matrix (Fin 10) (Fin 10) (ZMod 2) := fun r c =>
  if c.val = 4 then (if r.val = 0 ∨ r.val = 3 then 1 else 0)
  else if c.val = 5 then (if r.val = 0 ∨ r.val = 1 then 1 else 0)
  else if c.val = 6 then (if r.val = 0 ∨ r.val = 2 then 1 else 0)
  else if c.val = 7 then (if r.val = 1 ∨ r.val = 3 then 1 else 0)
  else if c.val = 8 then (if r.val = 2 ∨ r.val = 3 then 1 else 0)
  else if c.val = 9 then (if r.val = 4 ∨ r.val = 5 ∨ r.val = 7 then 1 else 0)
  else 0

private theorem theta_boundary : boundary LiftExamples.theta = thetaBoundary := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [boundary, LiftExamples.theta, thetaBoundary, Finset.orderEmbOfFin_apply,
      Finset.sort_insert, Finset.sort_singleton] <;> decide +kernel

private instance : NeZero LiftExamples.theta.length := ⟨by decide⟩

private def leftRecord : Representative LiftExamples.theta.length :=
  ⟨⟨1, 1, .finite 2⟩, 7, some 9, [4, 5, 7], some [9]⟩

private def rightRecord : Representative LiftExamples.theta.length :=
  ⟨⟨1, 1, .essential⟩, 8, none, [4, 6, 8], none⟩

private theorem theta_records :
    activeRepresentatives LiftExamples.theta 1 1 = [leftRecord, rightRecord] ∧
    activeRepresentatives LiftExamples.theta 1 2 = [rightRecord] := by
  constructor <;>
    unfold activeRepresentatives representedOccurrences pairedRepresentative essentialRepresentative
      pairedVector essentialVector change essentialIndices pivotPairs reduced trace <;>
    rw [theta_boundary] <;> decide +kernel

private def sourceRight : BasisIndex LiftExamples.theta 1 1 :=
  ⟨1, by rw [LiftExamples.theta_dimensions.2.1]; decide⟩

private def targetRight : BasisIndex LiftExamples.theta 1 2 :=
  ⟨0, by rw [LiftExamples.theta_dimensions.2.2]; decide⟩

private theorem source_right_record : basisRecord LiftExamples.theta 1 1 sourceRight = rightRecord := by
  have he := congrArg (fun rs => rs[sourceRight.val]?) theta_records.1
  rw [List.getElem?_eq_getElem sourceRight.isLt] at he
  exact Option.some.inj he

private theorem target_right_record (i : BasisIndex LiftExamples.theta 1 2) :
    basisRecord LiftExamples.theta 1 2 i = rightRecord := by
  have hi : i.val = 0 := by have hi := i.isLt; have hn := LiftExamples.theta_dimensions.2.2; omega
  have he := congrArg (fun rs => rs[i.val]?) theta_records.2
  rw [List.getElem?_eq_getElem i.isLt] at he
  have hr : ([rightRecord][i.val]?) = some rightRecord := by rw [hi]; rfl
  rw [hr] at he
  exact Option.some.inj he

private theorem theta_late_surjective : Function.Surjective
    (basisTransition LiftExamples.theta 1 1 2).mulVecLin := by
  intro v
  refine ⟨Pi.single sourceRight (v targetRight), ?_⟩
  funext i
  change (basisTransition LiftExamples.theta 1 1 2).mulVec _ i = _
  rw [Matrix.mulVec_single]
  change basisTransition LiftExamples.theta 1 1 2 i sourceRight * v targetRight = v i
  rw [basisTransition_apply, source_right_record, target_right_record]
  simp only [↓reduceIte, one_mul]
  have hi : i = targetRight := by
    apply Fin.ext
    have hi := i.isLt
    have hn := LiftExamples.theta_dimensions.2.2
    change i.val = 0
    omega
  rw [hi]

private theorem theta_dimensions :
    homologyMapDimensions LiftExamples.theta LiftExamples.theta 1 1 1 id = ⟨2, 0⟩ ∧
    homologyMapDimensions LiftExamples.theta LiftExamples.theta 1 1 2 id = ⟨1, 1⟩ := by
  have h1 : (homologyMapDimensions LiftExamples.theta LiftExamples.theta 1 1 1 id).rank = 2 := by
    rw [homologyMapDimensions_rank, homologyMapMatrix_id _ LiftExamples.theta_valid,
      Matrix.mulVecLin_one, LinearMap.range_id, finrank_top,
      Module.finrank_fintype_fun_eq_card, Fintype.card_fin, LiftExamples.theta_dimensions.2.1]
  have h2 : (homologyMapDimensions LiftExamples.theta LiftExamples.theta 1 1 2 id).rank = 1 := by
    rw [homologyMapDimensions_rank,
      homologyMapMatrix_inclusion _ LiftExamples.theta_valid 1 1 2 (by decide),
      LinearMap.range_eq_top.mpr theta_late_surjective, finrank_top,
      Module.finrank_fintype_fun_eq_card, Fintype.card_fin, LiftExamples.theta_dimensions.2.2]
  have hn1 := homologyMapDimensions_rank_nullity LiftExamples.theta LiftExamples.theta 1 1 1 id
  have hn2 := homologyMapDimensions_rank_nullity LiftExamples.theta LiftExamples.theta 1 1 2 id
  rw [LiftExamples.theta_dimensions.2.1, h1] at hn1
  rw [LiftExamples.theta_dimensions.2.1, h2] at hn2
  constructor
  · cases he : homologyMapDimensions LiftExamples.theta LiftExamples.theta 1 1 1 id
    simp_all
  · cases he : homologyMapDimensions LiftExamples.theta LiftExamples.theta 1 1 2 id
    simp_all
    omega

/-- The H₁ image loses one dimension exactly when the triangle face is admitted. -/
theorem theta_run :
    runHomologyDimensions LiftExamples.theta LiftExamples.theta 1 1 1 id = some ⟨2, 0⟩ ∧
    runHomologyDimensions LiftExamples.theta LiftExamples.theta 1 1 2 id = some ⟨1, 1⟩ := by
  constructor
  · apply (runHomologyDimensions_eq_some_iff _ _ _ _ _ _ _).mpr
    exact ⟨⟨LiftExamples.theta_valid, LiftExamples.theta_valid, vertexMapCondition_id _ _ _ le_rfl⟩,
      theta_dimensions.1.symm⟩
  · apply (runHomologyDimensions_eq_some_iff _ _ _ _ _ _ _).mpr
    exact ⟨⟨LiftExamples.theta_valid, LiftExamples.theta_valid, vertexMapCondition_id _ _ _ (by decide)⟩,
      theta_dimensions.2.symm⟩

/-- The rank change is a statement about the actual homology inclusion, with a one-dimensional kernel. -/
theorem theta_actual :
    let F (b : ℤ) (hb : 1 ≤ b) := (simplicialHomologyMap (ZMod 2)
      (validatedVertexMap LiftExamples.theta LiftExamples.theta LiftExamples.theta_valid LiftExamples.theta_valid
        1 b id (vertexMapCondition_id _ _ _ hb)) 1).hom
    Module.finrank (ZMod 2) (LinearMap.range (F 1 le_rfl)) = 2 ∧
      Module.finrank (ZMod 2) (LinearMap.ker (F 1 le_rfl)) = 0 ∧
      Module.finrank (ZMod 2) (LinearMap.range (F 2 (by decide))) = 1 ∧
      Module.finrank (ZMod 2) (LinearMap.ker (F 2 (by decide))) = 1 := by
  dsimp only
  rw [← homologyMapDimensions_rank_actual, ← homologyMapDimensions_nullity_actual,
    ← homologyMapDimensions_rank_actual, ← homologyMapDimensions_nullity_actual,
    theta_dimensions.1, theta_dimensions.2]
  decide +kernel

/-- Empty source and target need no exceptional rank convention; identity retains all three classes. -/
theorem empty_and_identity_runs :
    runHomologyDimensions [] target 0 0 (-2) id = some ⟨0, 0⟩ ∧
    runHomologyDimensions source [] 0 (-3) 0 id = some ⟨0, 0⟩ ∧
    runHomologyDimensions source source 0 (-2) (-2) id = some ⟨3, 0⟩ := by
  decide +kernel

/-- Validation remains mandatory when every queried homology group is zero. -/
theorem zero_and_invalid_runs :
    runHomologyDimensions [] [] 0 0 0 id = some ⟨0, 0⟩ ∧
    runHomologyDimensions source target 0 (-3) (-3) merge = some ⟨0, 0⟩ ∧
    runHomologyDimensions source target 7 (-2) (-2) merge = some ⟨0, 0⟩ ∧
    runHomologyDimensions [({0, 1}, 0)] [] 7 0 0 id = none ∧
    runHomologyDimensions MapExamples.sourceEdge MapExamples.components 7 0 0 id = none := by
  decide +kernel

end TDA.Persistence.Reduction.FiniteInput.DimensionExamples
