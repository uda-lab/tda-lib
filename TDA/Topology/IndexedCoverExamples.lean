import TDA.Topology.IndexedCover

/-!
# Indexed set-cover fixtures

These concrete theorems exercise empty supports, duplicate labels, range-only coverage,
retained empty pullbacks and distinct selectors.
-/

universe u v

namespace TDA.Topology

namespace ProbeFixtures

/-! The empty-index family on `Bool` has no members. -/
def emptyFamily : CoverFamily Bool Empty := Empty.elim

/-! An empty-index family covers exactly the empty support. -/
theorem emptyFamily_covers_iff (A : Set Bool) : Covers emptyFamily A ↔ A = ∅ := by
  constructor
  · intro h
    ext x
    constructor
    · intro hx
      obtain ⟨i, _⟩ := h x hx
      exact Empty.elim i
    · intro hx
      exact False.elim (by simpa using hx)
  · intro hA x hx
    exact False.elim (by simpa [hA] using hx)

/-! The empty-index family is not a full cover of a nonempty concrete type. -/
theorem emptyFamily_not_full : ¬ Covers emptyFamily (Set.univ : Set Bool) := by
  intro h
  obtain ⟨i, _⟩ := h false (Set.mem_univ false)
  exact Empty.elim i

/-! The same singleton member may be labelled by two distinct indices. -/
def duplicatedFamily : CoverFamily Bool Bool := fun _ => ({true} : Set Bool)

/-! A one-index family gives the target member for the merge refinement fixture. -/
def singletonFamily : CoverFamily Bool Unit := fun _ => ({true} : Set Bool)

/-! The selected refinement sends both duplicated indices to the one target index. -/
def mergeDuplicated : Refinement duplicatedFamily singletonFamily :=
  { selector := fun _ => ()
    subset := fun _ => subset_rfl }

/-! The duplicated singleton member has a selected refinement that merges its labels. -/
theorem duplicated_singleton_fixture :
    duplicatedFamily false = duplicatedFamily true ∧ false ≠ true ∧
      mergeDuplicated.selector false = () ∧ mergeDuplicated.selector true = () ∧
      Covers duplicatedFamily ({true} : Set Bool) := by
  refine ⟨rfl, Bool.noConfusion, rfl, rfl, ?_⟩
  intro x hx
  exact ⟨false, by simpa [duplicatedFamily] using hx⟩

/-! A concrete map from `Bool` attains only two natural-number values. -/
def boolCode : Bool → Nat := fun b => if b then 1 else 0

/-! A one-index target family whose member is exactly the attained range. -/
def rangeFamily : CoverFamily Nat Unit := fun _ => Set.range boolCode

/-! The range family covers its specified range. -/
theorem rangeFamily_covers_range : Covers rangeFamily (Set.range boolCode) := by
  intro y hy
  exact ⟨(), hy⟩

/-! The range family does not cover a natural number outside the attained range. -/
theorem rangeFamily_not_full : ¬ Covers rangeFamily (Set.univ : Set Nat) := by
  intro h
  obtain ⟨_, hy⟩ := h 2 (Set.mem_univ 2)
  obtain ⟨b, hb⟩ := hy
  cases b <;> simp [boolCode] at hb

/-! A range-only cover pulls back to a full cover of its concrete domain. -/
theorem range_pullback_full :
    Covers (pullback boolCode rangeFamily) (Set.univ : Set Bool) :=
  covers_range_pullback boolCode rangeFamily_covers_range

/-! A member disjoint from a map range pulls back to the empty set while its index remains. -/
def missingRangeFamily : CoverFamily Nat Unit := fun _ => ({2} : Set Nat)

/-! The retained unit index labels an empty pullback member. -/
theorem missingRange_pullback_empty :
    ∃ i : Unit, pullback boolCode missingRangeFamily i = (∅ : Set Bool) := by
  refine ⟨(), ?_⟩
  ext x
  constructor
  · intro hx
    have hx' : boolCode x = 2 := by
      simpa [pullback, missingRangeFamily] using hx
    cases x <;> simp [boolCode] at hx'
  · intro hx
    exact False.elim (by simpa using hx)

/-! The constant family permits two distinct valid selector functions. -/
def allFamily {X : Type u} {I : Type v} : CoverFamily X I := fun _ => Set.univ

/-! The identity selector is a valid refinement between two constant families. -/
def identitySelector : Refinement (allFamily (X := Unit) (I := Bool))
    (allFamily (X := Unit) (I := Bool)) :=
  Refinement.id _

/-! Boolean negation is a second valid selector between the same constant families. -/
def swappedSelector : Refinement (allFamily (X := Unit) (I := Bool))
    (allFamily (X := Unit) (I := Bool)) :=
  { selector := fun b => !b
    subset := fun _ _ _ => trivial }

/-! The two valid selectors remain distinguishable as index functions. -/
theorem selectors_are_distinct :
    identitySelector.selector ≠ swappedSelector.selector := by
  intro h
  have hfalse := congrFun h false
  simp [identitySelector, swappedSelector, Refinement.id] at hfalse

end ProbeFixtures

end TDA.Topology
