import TDA.Persistence.Reduction.FilteredNormalForm

set_option maxHeartbeats 800000

/-! Occurrence-level finite intervals supplied by a reduced filtered boundary. -/

namespace TDA.Persistence.Reduction

open TDA.Persistence

variable {m : ℕ} {k : Type*} [Field k] [DecidableEq k]

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
    (R : Matrix (Fin m) (Fin m) k) (p s t : ℕ) (hst : s ≤ t)
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

end TDA.Persistence.Reduction
