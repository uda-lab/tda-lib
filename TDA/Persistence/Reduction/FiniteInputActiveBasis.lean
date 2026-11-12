import TDA.Persistence.Reduction.FiniteInputSublevelHomology

/-!
# Complete enumeration of active computed representatives

Labels are positions in the degree-filtered active output. Original birth indices,
rather than interval values or positions at another grade, identify the same bar.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

namespace TDA.Persistence.Reduction.FiniteInput

open TDA.Simplicial TDA.Filtration

/-- The existing representative list, filtered at a grade and then by degree. -/
def activeRepresentatives (xs : Input) (p : ℕ) (a : ℤ) :
    List (Representative xs.length) :=
  ((representedOccurrences xs).filter (fun r => decide (r.occurrence.AliveAt a))).filter
    (fun r => r.occurrence.degree == p)

/-- A degree-specific query in the unchanged occurrence order; invalid input is rejected. -/
def runDegreeAtGrade (xs : Input) (p : ℕ) (a : ℤ) :
    Option (List (Representative xs.length)) :=
  (runAtGrade xs a).map (List.filter (fun r => r.occurrence.degree == p))

theorem runDegreeAtGrade_eq_some_iff (xs : Input) (p : ℕ) (a : ℤ)
    (out : List (Representative xs.length)) :
    runDegreeAtGrade xs p a = some out ↔ Valid xs ∧ out = activeRepresentatives xs p a := by
  unfold runDegreeAtGrade
  rw [Option.map_eq_some_iff]
  constructor
  · rintro ⟨rs, hrs, rfl⟩
    obtain ⟨hv, rfl⟩ := (runAtGrade_eq_some_iff xs a rs).mp hrs
    exact ⟨hv, rfl⟩
  · rintro ⟨hv, rfl⟩
    exact ⟨_, (runAtGrade_eq_some_iff xs a _).mpr ⟨hv, rfl⟩, rfl⟩

theorem runDegreeAtGrade_eq_none_iff (xs : Input) (p : ℕ) (a : ℤ) :
    runDegreeAtGrade xs p a = none ↔ ¬ Valid xs := by
  simp [runDegreeAtGrade, runAtGrade_eq_none_iff]

theorem mem_activeRepresentatives (xs : Input) (p : ℕ) (a : ℤ)
    (r : Representative xs.length) :
    r ∈ activeRepresentatives xs p a ↔
      r ∈ representedOccurrences xs ∧ r.occurrence.AliveAt a ∧ r.occurrence.degree = p := by
  simp [activeRepresentatives, and_comm, and_left_comm]

/-- Finite basis labels follow the actual query's list positions. -/
abbrev BasisIndex (xs : Input) (p : ℕ) (a : ℤ) :=
  Fin (activeRepresentatives xs p a).length

def basisRecord (xs : Input) (p : ℕ) (a : ℤ) (i : BasisIndex xs p a) :
    Representative xs.length := (activeRepresentatives xs p a).get i

theorem basisRecord_spec (xs : Input) (p : ℕ) (a : ℤ) (i : BasisIndex xs p a) :
    basisRecord xs p a i ∈ representedOccurrences xs ∧
      (basisRecord xs p a i).occurrence.AliveAt a ∧
      (basisRecord xs p a i).occurrence.degree = p :=
  (mem_activeRepresentatives xs p a _).mp (List.get_mem _ i)

private theorem paired_births (xs : Input) (l : List (Fin xs.length × Fin xs.length)) :
    (l.filterMap (pairedRepresentative xs)).map Representative.birthIndex =
      (l.filter (fun q => (xs.get q.1).2 ≠ (xs.get q.2).2)).map Prod.fst := by
  induction l with
  | nil => rfl
  | cons q l ih =>
    by_cases he : (xs.get q.1).2 = (xs.get q.2).2
    · have hr : pairedRepresentative xs q = none := by
        simp only [pairedRepresentative, pairOccurrence, if_pos he, Option.map_none]
      rw [List.filterMap_cons, hr, List.filter_cons]
      simp only [ne_eq, he, not_true_eq_false, decide_false, Bool.false_eq_true,
        ↓reduceIte, ih]
    · have hr : pairedRepresentative xs q = some
          ⟨⟨degree xs q.1, (xs.get q.1).2, .finite (xs.get q.2).2⟩,
            q.1, some q.2, supportChain (pairedVector xs q),
            some (supportChain ((change xs).col q.2))⟩ := by
        simp only [pairedRepresentative, pairOccurrence, if_neg he, Option.map_some]
      rw [List.filterMap_cons, hr, List.filter_cons]
      simp only [ne_eq, he, not_false_eq_true, decide_true, ↓reduceIte, List.map_cons, ih]

/-- Even coincident value intervals have different original birth indices. -/
theorem representedOccurrences_birth_nodup (xs : Input) :
    ((representedOccurrences xs).map Representative.birthIndex).Nodup := by
  have hp : ((pivotPairs xs).map Prod.fst).Nodup := by
    have hd : DistinctPivots (reduced xs) := by
      simpa only [DistinctPivots, reduced, trace] using
        matrixReductionTrace_pivots_distinct (boundary xs)
    apply (pivotPairs_nodup xs).map_on
    intro q hq q' hq' he
    apply Prod.ext he
    apply hd q.2 q'.2 q.1
    · exact (pivotPairs_mem xs q.1 q.2).mp hq
    · simpa only [he] using (pivotPairs_mem xs q'.1 q'.2).mp hq'
  have he : (essentialIndices xs).Nodup := (List.nodup_finRange _).filter _
  rw [representedOccurrences, List.map_append, paired_births, List.map_map]
  have hmap : Representative.birthIndex ∘ essentialRepresentative xs = id := by
    funext i
    rfl
  rw [hmap, List.map_id]
  change (((pivotPairs xs).filter _).map Prod.fst ++ essentialIndices xs).Nodup
  apply List.Nodup.append
  · exact ((List.filter_sublist (l := pivotPairs xs)).map Prod.fst).nodup hp
  · exact he
  · rw [List.disjoint_left]
    intro i hi hie
    obtain ⟨q, hq, hqi⟩ := List.mem_map.mp hi
    have hpq := (pivotPairs_mem xs q.1 q.2).mp (List.mem_filter.mp hq).1
    exact ((essentialIndices_mem xs i).mp hie).2 ⟨q.2, hqi ▸ hpq⟩

theorem representedOccurrences_birth_injective (xs : Input)
    (r s : Representative xs.length) (hr : r ∈ representedOccurrences xs)
    (hs : s ∈ representedOccurrences xs) (he : r.birthIndex = s.birthIndex) : r = s :=
  List.inj_on_of_nodup_map (representedOccurrences_birth_nodup xs) hr hs he

theorem activeRepresentatives_birth_nodup (xs : Input) (p : ℕ) (a : ℤ) :
    ((activeRepresentatives xs p a).map Representative.birthIndex).Nodup := by
  exact ((List.filter_sublist.trans List.filter_sublist).map Representative.birthIndex).nodup
    (representedOccurrences_birth_nodup xs)

theorem basisRecord_birth_injective (xs : Input) (p : ℕ) (a : ℤ) :
    Function.Injective (fun i : BasisIndex xs p a => (basisRecord xs p a i).birthIndex) := by
  intro i j he
  have hi := List.nodup_iff_injective_get.mp (activeRepresentatives_birth_nodup xs p a)
  apply Fin.ext
  have hij := hi (a₁ := ⟨i.val, by simp⟩)
    (a₂ := ⟨j.val, by simp⟩) (by simpa [basisRecord] using he)
  exact congrArg (fun k : Fin ((activeRepresentatives xs p a).map
    Representative.birthIndex).length => k.val) hij

/-- Every alive normal-form coordinate is actually retained by value extraction. -/
theorem activeRepresentatives_complete (xs : Input) (h : Valid xs) (p : ℕ) (a : ℤ)
    (i : Fin xs.length)
    (hi : AliveCoordinate (degree xs) (reduced xs) p (sublevelStage xs a) i) :
    ∃ r ∈ activeRepresentatives xs p a, r.birthIndex = i := by
  rcases hi with ⟨hdeg, hp | he⟩
  · obtain ⟨hp, hbirth, hdeath⟩ := hp
    let j := deathOfPivot (reduced xs) i hp
    have hpiv := deathOfPivot_spec (reduced xs) i hp
    have hb : (xs.get i).2 ≤ a := (grade_le_iff_index_lt_stage xs h a i).mpr hbirth
    have hd : a < (xs.get j).2 := by
      by_contra hn
      have hj := (grade_le_iff_index_lt_stage xs h a j).mp (le_of_not_gt hn)
      change sublevelStage xs a ≤ j.val at hdeath
      omega
    have hne : (xs.get i).2 ≠ (xs.get j).2 := ne_of_lt (hb.trans_lt hd)
    let r : Representative xs.length :=
      ⟨⟨degree xs i, (xs.get i).2, .finite (xs.get j).2⟩, i, some j,
        supportChain (pairedVector xs (i, j)), some (supportChain ((change xs).col j))⟩
    have hr : pairedRepresentative xs (i, j) = some r := by
      simp only [pairedRepresentative, pairOccurrence, if_neg hne, Option.map_some, r]
    refine ⟨r, (mem_activeRepresentatives xs p a r).mpr ⟨?_, ⟨hb, hd⟩, hdeg⟩, rfl⟩
    exact pairedRepresentative_mem xs (i, j) ((pivotPairs_mem xs i j).mpr hpiv) r hr
  · refine ⟨essentialRepresentative xs i,
      (mem_activeRepresentatives xs p a _).mpr ⟨?_, ⟨?_, trivial⟩, hdeg⟩, rfl⟩
    · exact essentialRepresentative_mem xs i ((essentialIndices_mem xs i).mpr he.1)
    · exact (grade_le_iff_index_lt_stage xs h a i).mpr he.2

theorem basisRecord_alive (xs : Input) (h : Valid xs) (p : ℕ) (a : ℤ)
    (i : BasisIndex xs p a) :
    AliveCoordinate (degree xs) (reduced xs) p (sublevelStage xs a)
      (basisRecord xs p a i).birthIndex := by
  obtain ⟨hr, ha, hdeg⟩ := basisRecord_spec xs p a i
  have hb := aliveAt_prefix_bounds xs h _ hr a ha
  simpa only [hdeg] using returned_alive xs h _ hr _ hb.1 hb.2

/-- Complete and unique list-position labeling of the live birth coordinates. -/
theorem basisRecord_birth_bijective (xs : Input) (h : Valid xs) (p : ℕ) (a : ℤ) :
    Function.Bijective (fun i : BasisIndex xs p a =>
      (⟨(basisRecord xs p a i).birthIndex, basisRecord_alive xs h p a i⟩ :
        {j : Fin xs.length // AliveCoordinate (degree xs) (reduced xs) p
          (sublevelStage xs a) j})) := by
  constructor
  · intro i j he
    exact basisRecord_birth_injective xs p a (congrArg Subtype.val he)
  · intro j
    obtain ⟨r, hr, he⟩ := activeRepresentatives_complete xs h p a j.1 j.2
    obtain ⟨i, hi⟩ := List.get_of_mem hr
    exact ⟨i, Subtype.ext (by simpa only [basisRecord, hi] using he)⟩

end TDA.Persistence.Reduction.FiniteInput
