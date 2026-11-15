import TDA.Persistence.Reduction.FiniteInputImageBarcodeCorrectness
import TDA.Persistence.Reduction.FiniteInputImageExamples

/-!
# Sampled image-barcode consumers

These examples retain finite observation endpoints. In particular an interval
ending at `N` asserts no behavior after the final sample.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option maxRecDepth 20000
set_option maxHeartbeats 1600000

namespace TDA.Persistence.Reduction.FiniteInput.ImageBarcodeExamples

open CategoryTheory
open scoped BigOperators

/-- Two triangle loops sharing an edge. One is born at zero, the other at one.
At grade two, fill either the later loop or the earlier loop. -/
def twoLoops (fillLater : Bool) : Input :=
  [({0}, 0), ({1}, 0), ({2}, 0), ({3}, 0),
    ({0, 3}, 0), ({0, 1}, 0), ({1, 3}, 0), ({0, 2}, 1), ({2, 3}, 1),
    (if fillLater then {0, 2, 3} else {0, 1, 3}, 2)]

def stages : Fin 3 → ℤ := fun i => i.val

theorem stages_monotone : Monotone stages := by
  intro i j hij
  change (i.val : ℤ) ≤ (j.val : ℤ)
  exact_mod_cast (show i.val ≤ j.val from hij)

theorem twoLoops_valid (later : Bool) : Valid (twoLoops later) := by
  cases later <;> decide +kernel

theorem twoLoops_input (later : Bool) :
    ImageBarcodeInput (twoLoops later) (twoLoops later) id stages :=
  ⟨⟨twoLoops_valid later, twoLoops_valid later, globalVertexMapCondition_id _⟩, stages_monotone⟩

/-- The two intended ordered barcodes differ only in which class dies at index two. -/
def expectedLoops (later : Bool) : List (FiniteInterval 3) :=
  if later then [⟨0, 3, by decide, by decide⟩, ⟨1, 2, by decide, by decide⟩]
  else [⟨0, 2, by decide, by decide⟩, ⟨1, 3, by decide, by decide⟩]

private def loopBoundary (later : Bool) : Matrix (Fin 10) (Fin 10) (ZMod 2) := fun r c =>
  if c.val = 4 then (if r.val = 0 ∨ r.val = 3 then 1 else 0)
  else if c.val = 5 then (if r.val = 0 ∨ r.val = 1 then 1 else 0)
  else if c.val = 6 then (if r.val = 1 ∨ r.val = 3 then 1 else 0)
  else if c.val = 7 then (if r.val = 0 ∨ r.val = 2 then 1 else 0)
  else if c.val = 8 then (if r.val = 2 ∨ r.val = 3 then 1 else 0)
  else if c.val = 9 then
    (if r.val = 4 ∨ r.val = (if later then 7 else 5) ∨
      r.val = (if later then 8 else 6) then 1 else 0)
  else 0

private theorem loop_boundary (later : Bool) : boundary (twoLoops later) = loopBoundary later := by
  cases later <;> funext i j
  all_goals fin_cases i <;> fin_cases j <;>
    norm_num [boundary, twoLoops, loopBoundary, Finset.orderEmbOfFin_apply,
      Finset.sort_insert, Finset.sort_singleton] <;> decide +kernel

private instance (later : Bool) : NeZero (twoLoops later).length := ⟨by cases later <;> decide⟩

private def earlyLoop (later : Bool) : Representative (twoLoops later).length :=
  ⟨⟨1, 0, if later then .essential else .finite 2⟩, 6,
    if later then none else some 9, [4, 5, 6], if later then none else some [9]⟩

private def lateLoop (later : Bool) : Representative (twoLoops later).length :=
  ⟨⟨1, 1, if later then .finite 2 else .essential⟩, 8,
    if later then some 9 else none, [4, 7, 8], if later then some [9] else none⟩

private def loopRecords (later : Bool) (i : Fin 3) : List (Representative (twoLoops later).length) :=
  if i.val = 0 then [earlyLoop later]
  else if i.val = 1 then
    (if later then [lateLoop later, earlyLoop later] else [earlyLoop later, lateLoop later])
  else if later then [earlyLoop later] else [lateLoop later]

private theorem loop_records (later : Bool) (i : Fin 3) :
    activeRepresentatives (twoLoops later) 1 (stages i) = loopRecords later i := by
  cases later <;> fin_cases i
  all_goals
    unfold activeRepresentatives representedOccurrences pairedRepresentative essentialRepresentative
      pairedVector essentialVector change essentialIndices pivotPairs reduced trace
    rw [loop_boundary]
    decide +kernel

/-- Same diagonal and adjacent entries, with a different long-range entry. -/
def expectedRanks (later : Bool) : ImageRankTable 3 :=
  #v[#v[1, 1, if later then 1 else 0], #v[0, 2, 1], #v[0, 0, 1]]

private def recordRank {m : ℕ} (source target : List (Representative m)) : ℕ :=
  Nat.log 2 (Finset.univ.image
    (fun v : Fin source.length → ZMod 2 => fun j : Fin target.length =>
      ∑ i : Fin source.length,
        (if (target.get j).birthIndex = (source.get i).birthIndex then 1 else 0) * v i)).card

private theorem id_record_rank (xs : Input) (hx : Valid xs) (p : ℕ) (a b : ℤ) (hab : a ≤ b) :
    (homologyMapDimensions xs xs p a b id).rank =
      recordRank (activeRepresentatives xs p a) (activeRepresentatives xs p b) := by
  have he := congrArg HomologyMapDimensions.rank (homologyMapDimensions_eq xs xs p a b id)
  change (homologyMapDimensions xs xs p a b id).rank =
    Nat.log 2 (Finset.univ.image (homologyMapMatrix xs xs p a b id).mulVec).card at he
  rw [homologyMapMatrix_inclusion xs hx p a b hab] at he
  exact he

private theorem loop_pair_rank (later : Bool) (i j : Fin 3) (hij : i ≤ j) :
    (homologyMapDimensions (twoLoops later) (twoLoops later) 1 (stages i) (stages j) id).rank =
      imageRank (expectedRanks later) i j := by
  rw [id_record_rank _ (twoLoops_valid later) 1 _ _ (stages_monotone hij)]
  simp only [loop_records]
  have hv : i.val ≤ j.val := hij
  cases later <;> fin_cases i <;> fin_cases j <;> norm_num at hv
  all_goals exact of_decide_eq_true rfl

/-- All nine stored entries are identified, including every forward rank. -/
theorem loop_table (later : Bool) :
    imageRankTable (twoLoops later) (twoLoops later) 1 id stages = expectedRanks later := by
  apply Vector.ext
  intro i hi
  apply Vector.ext
  intro j hj
  change imageRank (imageRankTable (twoLoops later) (twoLoops later) 1 id stages)
    ⟨i, hi⟩ ⟨j, hj⟩ = imageRank (expectedRanks later) ⟨i, hi⟩ ⟨j, hj⟩
  by_cases hij : i ≤ j
  · rw [imageRank_table _ _ _ _ _ _ _ hij]
    exact loop_pair_rank later ⟨i, hi⟩ ⟨j, hj⟩ hij
  · simp only [imageRank, imageRankTable, Vector.getElem_ofFn]
    rw [if_neg (show ¬ (⟨i, hi⟩ : Fin 3) ≤ ⟨j, hj⟩ from hij)]
    interval_cases i <;> interval_cases j <;> cases later <;> rfl

/-- Exact ordered output distinguishes modules that adjacent ranks cannot distinguish. -/
theorem loop_runs (later : Bool) :
    runImageBarcode (twoLoops later) (twoLoops later) 1 id stages = some (expectedLoops later) := by
  apply (runImageBarcode_eq_some_iff _ _ _ _ _ _).mpr
  refine ⟨twoLoops_input later, ?_⟩
  unfold imageBarcode
  rw [loop_table]
  cases later <;> decide +kernel

/-- The all-pairs guard compares actual image modules, rather than abstract proxy tables. -/
theorem all_pairs_actual :
    let A := sampledImage (twoLoops true) (twoLoops true) 1 id stages (twoLoops_input true)
    let B := sampledImage (twoLoops false) (twoLoops false) 1 id stages (twoLoops_input false)
    structureMapRank A 0 1 (by decide) = structureMapRank B 0 1 (by decide) ∧
    structureMapRank A 1 2 (by decide) = structureMapRank B 1 2 (by decide) ∧
    (∀ i, structureMapRank A i i le_rfl = structureMapRank B i i le_rfl) ∧
    structureMapRank A 0 2 (by decide) = 1 ∧
    structureMapRank B 0 2 (by decide) = 0 ∧ rankBarcode A ≠ rankBarcode B := by
  dsimp only
  have hr (later : Bool) (i j : Fin 3) (hij : i ≤ j) :
      structureMapRank (sampledImage (twoLoops later) (twoLoops later) 1 id stages
        (twoLoops_input later)) i j hij = imageRank (expectedRanks later) i j := by
    rw [← imageRank_correct, loop_table]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hr, hr]; decide +kernel
  · rw [hr, hr]; decide +kernel
  · intro i; rw [hr, hr]; fin_cases i <;> decide +kernel
  · rw [hr]; decide +kernel
  · rw [hr]; decide +kernel
  · intro he
    have heq := (rankBarcode_eq_iff _ _).mp he 0 2 (by decide)
    rw [hr, hr] at heq
    have : (1 : ℕ) = 0 := heq
    omega

/-- The certified lists realize the actual H₁ image modules by natural isomorphisms. -/
theorem loop_actual (later : Bool) :
    Nonempty (sampledImage (twoLoops later) (twoLoops later) 1 id stages (twoLoops_input later) ≅
      barcodeModule (k := ZMod 2) (expectedLoops later : Multiset (FiniteInterval 3))) := by
  obtain ⟨h, _, _, he⟩ := runImageBarcode_correct _ _ _ _ _ _ (loop_runs later)
  exact he

/-- Empty observations still validate; an empty complex has no interval at one sample. -/
theorem empty_runs :
    runImageBarcode [] [] 0 id (fun i : Fin 0 => Fin.elim0 i) = some [] ∧
    runImageBarcode [] [] 1 id (fun _ : Fin 1 => -3) = some [] := by
  decide +kernel

private theorem one_table (xs ys : Input) (p : ℕ) (f : ℕ → ℕ) (a : ℤ) (r : ℕ)
    (hr : (homologyMapDimensions xs ys p a a f).rank = r) :
    imageRankTable xs ys p f (fun _ : Fin 1 => a) = #v[#v[r]] := by
  apply Vector.ext
  intro i hi
  apply Vector.ext
  intro j hj
  have hi0 : i = 0 := by omega
  have hj0 : j = 0 := by omega
  subst i; subst j
  change imageRank (imageRankTable _ _ _ _ _) 0 0 = r
  rw [imageRank_table _ _ _ _ _ _ _ le_rfl]
  exact hr

/-- A collapsed source edge coexists with a nonzero H₁ image and a final surviving bar. -/
theorem collapsed_run :
    runImageBarcode MapExamples.square MapExamples.circle 1 MapExamples.collapseEdge
      (fun _ : Fin 1 => 1) = some [⟨0, 1, by decide, by decide⟩] := by
  apply (runImageBarcode_eq_some_iff _ _ _ _ _ _).mpr
  refine ⟨by decide +kernel, ?_⟩
  have hr : (homologyMapDimensions MapExamples.square MapExamples.circle 1 1 1
      MapExamples.collapseEdge).rank = 1 := by
    have he := ImageExamples.collapsed_image_rank
    dsimp only at he
    rw [sampledHomologyMap_image_rank, ← homologyMapDimensions_rank_actual] at he
    exact he
  unfold imageBarcode
  rw [one_table _ _ _ _ _ _ hr]
  decide +kernel

/-- Collapsing the entire square to a point gives the empty H₁ barcode. -/
theorem zero_map_run :
    runImageBarcode MapExamples.square MapExamples.point 1 (fun _ => 42)
      (fun _ : Fin 1 => 1) = some [] := by
  apply (runImageBarcode_eq_some_iff _ _ _ _ _ _).mpr
  refine ⟨by decide +kernel, ?_⟩
  have ht : (activeRepresentatives MapExamples.point 1 1).length = 0 := by decide +kernel
  let : IsEmpty (BasisIndex MapExamples.point 1 1) := ⟨fun i => by have hi := i.isLt; omega⟩
  have hz : (homologyMapMatrix MapExamples.square MapExamples.point 1 1 1 (fun _ => 42)).mulVecLin = 0 :=
    Subsingleton.elim _ _
  have hr : (homologyMapDimensions MapExamples.square MapExamples.point 1 1 1 (fun _ => 42)).rank = 0 := by
    rw [homologyMapDimensions_rank, hz]; simp
  unfold imageBarcode
  rw [one_table _ _ _ _ _ _ hr]
  decide +kernel

private instance : NeZero Examples.hollow.length := ⟨by decide⟩

private def hollowLoop : Representative Examples.hollow.length :=
  ⟨⟨1, 1, .essential⟩, 5, none, [3, 4, 5], none⟩

private theorem hollow_records (i : Fin 2) :
    activeRepresentatives Examples.hollow 1 (i.val : ℤ) =
      (if i.val = 0 then [] else [hollowLoop]) := by
  fin_cases i <;>
    unfold activeRepresentatives representedOccurrences pairedRepresentative essentialRepresentative
      pairedVector essentialVector change essentialIndices pivotPairs reduced trace <;>
    rw [Examples.hollow_boundary] <;> decide +kernel

private theorem later_table :
    imageRankTable Examples.hollow Examples.hollow 1 id (fun i : Fin 2 => i.val) =
      #v[#v[0, 0], #v[0, 1]] := by
  apply Vector.ext
  intro i hi
  apply Vector.ext
  intro j hj
  simp only [imageRankTable, Vector.getElem_ofFn]
  split_ifs with hij
  · have hij' : i ≤ j := hij
    rw [id_record_rank _ Examples.hollow_valid 1 _ _ (by exact_mod_cast hij')]
    have hri := hollow_records ⟨i, hi⟩
    have hrj := hollow_records ⟨j, hj⟩
    dsimp only [Fin.val_mk] at hri hrj
    rw [hri, hrj]
    clear hri hrj
    interval_cases i <;> interval_cases j <;> try omega
    all_goals exact of_decide_eq_true rfl
  · have hij' : ¬ i ≤ j := hij
    interval_cases i <;> interval_cases j <;> try omega
    all_goals rfl

theorem later_input :
    ImageBarcodeInput Examples.hollow Examples.hollow id (fun i : Fin 2 => (i.val : ℤ)) :=
  ⟨⟨Examples.hollow_valid, Examples.hollow_valid, globalVertexMapCondition_id _⟩,
    fun i j hij => by
      change (i.val : ℤ) ≤ (j.val : ℤ)
      exact_mod_cast (show i.val ≤ j.val from hij)⟩

/-- The later component has rank one, but the earlier-to-later map has rank zero. -/
theorem later_born_run :
    runImageBarcode Examples.hollow Examples.hollow 1 id (fun i : Fin 2 => i.val) =
      some [⟨1, 2, by decide, by decide⟩] := by
  apply (runImageBarcode_eq_some_iff _ _ _ _ _ _).mpr
  refine ⟨later_input, ?_⟩
  unfold imageBarcode
  rw [later_table]
  decide +kernel

theorem later_born_actual :
    structureMapRank (sampledImage Examples.hollow Examples.hollow 1 id _ later_input) 0 1 (by decide) = 0 ∧
    structureMapRank (sampledImage Examples.hollow Examples.hollow 1 id _ later_input) 1 1 le_rfl = 1 := by
  constructor
  · rw [← imageRank_correct Examples.hollow Examples.hollow 1 id
      (fun i : Fin 2 => (i.val : ℤ)) later_input 0 1 (by decide), later_table]
    decide +kernel
  · rw [← imageRank_correct Examples.hollow Examples.hollow 1 id
      (fun i : Fin 2 => (i.val : ℤ)) later_input 1 1 le_rfl, later_table]
    decide +kernel

/-- Negative repeated observations preserve both equal interval occurrences. -/
theorem repeated_runs :
    runImageBarcode MapExamples.components MapExamples.components 0 id (fun _ : Fin 2 => 0) =
      some [⟨0, 2, by decide, by decide⟩, ⟨0, 2, by decide, by decide⟩] ∧
    runImageBarcode MapExamples.sourceEdge MapExamples.sourceEdge 0 id (fun _ : Fin 1 => -4) =
      some [⟨0, 1, by decide, by decide⟩, ⟨0, 1, by decide, by decide⟩] := by
  constructor
  · decide +kernel
  · apply (runImageBarcode_eq_some_iff _ _ _ _ _ _).mpr
    refine ⟨by decide +kernel, ?_⟩
    have hd : (homologyMapDimensions MapExamples.sourceEdge MapExamples.sourceEdge
        0 (-4) (-4) id).rank = 2 := by
      have he := ImageExamples.negative_image_ranks.1
      rw [sampledHomologyMap_image_rank, ← homologyMapDimensions_rank_actual] at he
      exact he
    have ht : imageRankTable MapExamples.sourceEdge MapExamples.sourceEdge 0 id
        (fun _ : Fin 1 => -4) = #v[#v[2]] := by
      apply Vector.ext
      intro i hi
      apply Vector.ext
      intro j hj
      have hi0 : i = 0 := by omega
      have hj0 : j = 0 := by omega
      subst i; subst j
      change imageRank (imageRankTable _ _ _ _ _) 0 0 = 2
      rw [imageRank_table _ _ _ _ _ _ _ le_rfl]
      exact hd
    unfold imageBarcode
    rw [ht]
    decide +kernel

/-- Rejection is independent of the requested degree and of whether any sample is present. -/
theorem rejected_runs :
    runImageBarcode [] [] 0 id (fun i : Fin 2 => -(i.val : ℤ)) = none ∧
    runImageBarcode [({0, 1}, 0)] MapExamples.point 7 (fun _ => 42)
      (fun i : Fin 0 => Fin.elim0 i) = none ∧
    runImageBarcode [] [({0, 1}, 0)] 7 id (fun _ : Fin 1 => 0) = none ∧
    runImageBarcode MapExamples.sourceEdge MapExamples.lateEdge 7 MapExamples.relabel
      (fun _ : Fin 1 => -4) = none ∧
    runImageBarcode MapExamples.sourceEdge MapExamples.lateEdge 0 MapExamples.relabel
      (fun i : Fin 0 => Fin.elim0 i) = none := by
  decide +kernel

/-- Successful concrete extraction gives a genuine image-module decomposition. -/
theorem repeated_actual :
    let h : ImageBarcodeInput MapExamples.components MapExamples.components id
        (fun _ : Fin 2 => 0) := by decide +kernel
    Nonempty (sampledImage MapExamples.components MapExamples.components 0 id
        (fun _ : Fin 2 => 0) h ≅ barcodeModule (k := ZMod 2)
        (([⟨0, 2, by decide, by decide⟩, ⟨0, 2, by decide, by decide⟩] :
          List (FiniteInterval 2)) : Multiset (FiniteInterval 2))) := by
  obtain ⟨h, _, _, he⟩ := runImageBarcode_correct _ _ _ _ _ _ repeated_runs.1
  exact he

end TDA.Persistence.Reduction.FiniteInput.ImageBarcodeExamples
