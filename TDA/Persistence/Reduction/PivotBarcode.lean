import TDA.Persistence.Reduction.FilteredNormalForm

set_option maxHeartbeats 800000

/-! Occurrence-level finite intervals supplied by a reduced filtered boundary. -/

namespace TDA.Persistence.Reduction

open TDA.Persistence

variable {m : ℕ} {k : Type*} [Field k] [DecidableEq k]

private theorem filterMap_some_map {A B : Type*} (f : A → B) (s : Multiset A) :
    s.filterMap (fun x => some (f x)) = s.map f := by
  simpa only [Function.comp_def] using congrFun (Multiset.filterMap_eq_map f) s

private theorem filterMap_none_zero {A B : Type*} (s : Multiset A) :
    s.filterMap (fun _ => (none : Option B)) = 0 := by
  induction s using Multiset.induction_on with
  | empty => rfl
  | @cons a s ih => simp [Multiset.filterMap_cons, ih]

/-- One finite interval for every pivot row in the requested degree. -/
noncomputable def pivotPairIntervals (degree : Fin m → ℕ)
    (R : Matrix (Fin m) (Fin m) k) (hstrict : StrictBoundary R) (p : ℕ) :
    Multiset (FiniteInterval (m + 1)) := by
  classical
  exact (Finset.univ : Finset {i : Fin m // IsPivot R i ∧ degree i = p}).val.map
    (fun x => pairedInterval R hstrict (deathOfPivot R x.1 x.2.1) x.1
      (deathOfPivot_spec R x.1 x.2.1))

/-- One terminal-sentinel interval for each unpaired zero column. -/
noncomputable def pivotEssentialIntervals (degree : Fin m → ℕ)
    (R : Matrix (Fin m) (Fin m) k) (p : ℕ) :
    Multiset (FiniteInterval (m + 1)) := by
  classical
  exact (Finset.univ : Finset {i : Fin m // IsEssential R i ∧ degree i = p}).val.map
    (fun x => essentialInterval x.1)

/-- Multiplicities are preserved even when several intervals have equal endpoints. -/
noncomputable def pivotBarcode (degree : Fin m → ℕ)
    (R : Matrix (Fin m) (Fin m) k) (hstrict : StrictBoundary R) (p : ℕ) :
    Multiset (FiniteInterval (m + 1)) :=
  pivotPairIntervals degree R hstrict p + pivotEssentialIntervals degree R p

/-- Finite pivot pairs, recorded at zero-based face indices. -/
noncomputable def pivotIndexPairs (degree : Fin m → ℕ)
    (R : Matrix (Fin m) (Fin m) k) (p : ℕ) :
    Multiset (Fin m × Fin m) := by
  classical
  exact (Finset.univ : Finset {i : Fin m // IsPivot R i ∧ degree i = p}).val.map
    (fun x => (x.1, deathOfPivot R x.1 x.2.1))

/-- Essential births, recorded at zero-based face indices. -/
noncomputable def pivotEssentialIndices (degree : Fin m → ℕ)
    (R : Matrix (Fin m) (Fin m) k) (p : ℕ) :
    Multiset (Fin m) := by
  classical
  exact (Finset.univ : Finset {i : Fin m // IsEssential R i ∧ degree i = p}).val.map
    (fun x => x.1)

/-- Shift a finite stage interval back to its face-index pair. -/
def finiteIndexPair (I : FiniteInterval (m + 1)) : Option (Fin m × Fin m) :=
  if hb : 0 < I.birth then
    if hd : I.death ≤ m then
      some (⟨I.birth - 1, by have := I.birth_lt_death; have := I.death_le_size; omega⟩,
        ⟨I.death - 1, by have := I.birth_lt_death; omega⟩)
    else none
  else none

/-- Shift a terminal-sentinel interval back to its essential birth index. -/
def essentialIndex (I : FiniteInterval (m + 1)) : Option (Fin m) :=
  if hb : 0 < I.birth then
    if I.death ≤ m then none
    else some ⟨I.birth - 1,
      by have := I.birth_lt_death; have := I.death_le_size; omega⟩
  else none

theorem finiteIndexPair_paired (R : Matrix (Fin m) (Fin m) k)
    (hstrict : StrictBoundary R) (j i : Fin m)
    (hji : columnPivot (R.col j) = some i) :
    finiteIndexPair (pairedInterval R hstrict j i hji) = some (i, j) := by
  have hb : 0 < i.val + 1 := by omega
  have hd : j.val + 1 ≤ m := by omega
  simp [finiteIndexPair, pairedInterval, hb, hd]

theorem finiteIndexPair_essential (i : Fin m) :
    finiteIndexPair (essentialInterval i) = none := by
  have hb : 0 < i.val + 1 := by omega
  have hd : ¬m + 1 ≤ m := by omega
  simp [finiteIndexPair, essentialInterval, hb, hd]

theorem essentialIndex_paired (R : Matrix (Fin m) (Fin m) k)
    (hstrict : StrictBoundary R) (j i : Fin m)
    (hji : columnPivot (R.col j) = some i) :
    essentialIndex (pairedInterval R hstrict j i hji) = none := by
  have hb : 0 < i.val + 1 := by omega
  have hd : j.val + 1 ≤ m := by omega
  simp [essentialIndex, pairedInterval, hb, hd]

theorem essentialIndex_essential (i : Fin m) :
    essentialIndex (essentialInterval i) = some i := by
  have hb : 0 < i.val + 1 := by omega
  have hd : ¬m + 1 ≤ m := by omega
  simp [essentialIndex, essentialInterval, hb, hd]

/-- Stage-to-face conversion of reducer occurrences recovers exactly its
zero-based finite pivot pairs, including a pivot in row zero. -/
theorem pivotBarcode_pairs (degree : Fin m → ℕ)
    (R : Matrix (Fin m) (Fin m) k) (hstrict : StrictBoundary R) (p : ℕ) :
    (pivotBarcode degree R hstrict p).filterMap finiteIndexPair =
      pivotIndexPairs degree R p := by
  classical
  unfold pivotBarcode pivotPairIntervals pivotEssentialIntervals pivotIndexPairs
  rw [Multiset.filterMap_add, Multiset.filterMap_map, Multiset.filterMap_map]
  simp only [Function.comp_def, finiteIndexPair_paired, finiteIndexPair_essential,
    filterMap_some_map, filterMap_none_zero, add_zero]

/-- Stage-to-face conversion recovers exactly the unpaired zero indices. -/
theorem pivotBarcode_essential (degree : Fin m → ℕ)
    (R : Matrix (Fin m) (Fin m) k) (hstrict : StrictBoundary R) (p : ℕ) :
    (pivotBarcode degree R hstrict p).filterMap essentialIndex =
      pivotEssentialIndices degree R p := by
  classical
  unfold pivotBarcode pivotPairIntervals pivotEssentialIntervals pivotEssentialIndices
  rw [Multiset.filterMap_add, Multiset.filterMap_map, Multiset.filterMap_map]
  simp only [Function.comp_def, essentialIndex_paired, essentialIndex_essential,
    filterMap_some_map, filterMap_none_zero, zero_add]

/-- A pivot occurrence survives a structure map precisely when its row was
born before the source stage and its death column enters after the target. -/
theorem pivotPairIntervals_count (degree : Fin m → ℕ)
    (R : Matrix (Fin m) (Fin m) k) (hstrict : StrictBoundary R)
    (p s t : ℕ) :
    (pivotPairIntervals degree R hstrict p).countP
      (fun I => I.birth ≤ s ∧ t < I.death) =
      (pairSurvivorFinset degree R p s t).card := by
  classical
  unfold pivotPairIntervals
  rw [Multiset.countP_map]
  rw [← Finset.filter_val]
  apply Finset.card_bij (fun x _ => x.1)
  · intro x hx
    obtain ⟨hi, hdegree⟩ := x.2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, hi, hdegree, ?_, ?_⟩
    · simp only [pairedInterval] at hx
      omega
    · simp only [pairedInterval] at hx
      omega
  · intro x hx y hy hxy
    exact Subtype.ext hxy
  · intro i hi
    obtain ⟨hpiv, hdegree, hbirth, hdeath⟩ :=
      (Finset.mem_filter.mp hi).2
    let x : {i : Fin m // IsPivot R i ∧ degree i = p} := ⟨i, hpiv, hdegree⟩
    refine ⟨x, ?_, rfl⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    change i.val + 1 ≤ s ∧ t < (deathOfPivot R i hpiv).val + 1
    omega

/-- An essential occurrence survives exactly when born before the source. -/
theorem pivotEssentialIntervals_count (degree : Fin m → ℕ)
    (R : Matrix (Fin m) (Fin m) k) (p s t : ℕ) (_hst : s ≤ t)
    (ht : t ≤ m) :
    (pivotEssentialIntervals degree R p).countP
      (fun I => I.birth ≤ s ∧ t < I.death) =
      (essentialSurvivorFinset degree R p s).card := by
  classical
  unfold pivotEssentialIntervals
  rw [Multiset.countP_map]
  rw [← Finset.filter_val]
  apply Finset.card_bij (fun x _ => x.1)
  · intro x hx
    obtain ⟨he, hdegree⟩ := x.2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, he, hdegree, ?_⟩
    simp only [essentialInterval] at hx
    omega
  · intro x hx y hy hxy
    exact Subtype.ext hxy
  · intro i hi
    obtain ⟨he, hdegree, hbirth⟩ :=
      (Finset.mem_filter.mp hi).2
    let x : {i : Fin m // IsEssential R i ∧ degree i = p} := ⟨i, he, hdegree⟩
    refine ⟨x, ?_, rfl⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    dsimp only [essentialInterval, x]
    omega

/-- Rank count of the occurrence multiset, in the reducer's death-column form. -/
theorem pivotBarcode_rank (degree : Fin m → ℕ)
    (R : Matrix (Fin m) (Fin m) k) (hstrict : StrictBoundary R)
    (hpiv : DistinctPivots R) (p s t : ℕ) (hst : s ≤ t)
    (ht : t ≤ m) :
    (pivotBarcode degree R hstrict p).countP
      (fun I => I.birth ≤ s ∧ t < I.death) =
      (deathSurvivorFinset degree R p s t).card +
        (essentialSurvivorFinset degree R p s).card := by
  rw [pivotBarcode, Multiset.countP_add,
    pivotPairIntervals_count, pivotEssentialIntervals_count degree R p s t hst ht,
    pair_survivor_card_eq_death_card degree R hpiv p s t]

/-- Distinct pivot-row indices give distinct finite pair occurrences, even without reducedness. -/
theorem pivotIndexPairs_nodup (degree : Fin m → ℕ)
    (R : Matrix (Fin m) (Fin m) k) (p : ℕ) :
    (pivotIndexPairs degree R p).Nodup := by
  classical
  unfold pivotIndexPairs
  apply Multiset.Nodup.map _ (Finset.univ.nodup)
  intro x y h
  exact Subtype.ext (congrArg Prod.fst h)

/-- For distinct pivots, membership records the exact degree and row/death-column pairing. -/
theorem mem_pivotIndexPairs_iff (degree : Fin m → ℕ)
    (R : Matrix (Fin m) (Fin m) k) (hpiv : DistinctPivots R)
    (p : ℕ) (i j : Fin m) :
    (i,j) ∈ pivotIndexPairs degree R p ↔
      degree i = p ∧ columnPivot (R.col j) = some i := by
  classical
  unfold pivotIndexPairs
  simp only [Multiset.mem_map, Finset.mem_val, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨x, h⟩
    have hi : x.val = i := congrArg Prod.fst h
    have hj : deathOfPivot R x.val x.property.1 = j := congrArg Prod.snd h
    exact ⟨hi ▸ x.property.2, by rw [← hi, ← hj]; exact deathOfPivot_spec R _ _⟩
  · rintro ⟨hd,hj⟩
    let x : {i : Fin m // IsPivot R i ∧ degree i = p} := ⟨i, ⟨j,hj⟩,hd⟩
    exact ⟨x, Prod.ext rfl (deathOfPivot_unique R hpiv i j x.property.1 hj)⟩

/-- Unpaired zero columns contribute distinct essential index occurrences. -/
theorem pivotEssentialIndices_nodup (degree : Fin m → ℕ)
    (R : Matrix (Fin m) (Fin m) k) (p : ℕ) :
    (pivotEssentialIndices degree R p).Nodup := by
  classical
  unfold pivotEssentialIndices
  exact Multiset.Nodup.map Subtype.val_injective (Finset.univ.nodup)

/-- Essential-index membership records an unpaired zero column of the requested degree. -/
theorem mem_pivotEssentialIndices_iff (degree : Fin m → ℕ)
    (R : Matrix (Fin m) (Fin m) k) (p : ℕ) (i : Fin m) :
    i ∈ pivotEssentialIndices degree R p ↔ IsEssential R i ∧ degree i = p := by
  classical
  simp [pivotEssentialIndices]

/-- Convert stage endpoints to zero-based face occurrences. Death `m + 1` is the
finite observation sentinel, not an infinite grade. -/
theorem pivotBarcode_endpoints (degree : Fin m → ℕ)
    (R : Matrix (Fin m) (Fin m) k) (hs : StrictBoundary R) (p : ℕ) :
    (pivotBarcode degree R hs p).map (fun I => (I.birth, I.death)) =
      (pivotIndexPairs degree R p).map (fun q => (q.1.val+1,q.2.val+1)) +
      (pivotEssentialIndices degree R p).map (fun i => (i.val+1,m+1)) := by
  simp only [pivotBarcode, Multiset.map_add, pivotPairIntervals, pivotEssentialIntervals,
    pivotIndexPairs, pivotEssentialIndices, Multiset.map_map]
  rfl

end TDA.Persistence.Reduction
