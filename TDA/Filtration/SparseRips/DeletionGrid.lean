import TDA.Filtration.SparseRips.UnionDeletion

/-!
# A finite deletion grid for the sparse filtration

Every sparse face visible at a scale `r` is already present at `r` or at a
finite deletion time of a vertex. The grid is built from the actual finite
metric space; no constructibility assumption is required.
-/

namespace TDA.Filtration.SparseRips

open TDA.Simplicial

noncomputable section

variable {V : Type*} [MetricSpace V] [Fintype V]

local instance deletionGridDecidableEq : DecidableEq V := Classical.decEq V

/-- Finite deletion times of the vertices. The seed's infinite time is omitted. -/
def deletionTimes (seed : V) (η : ℝ) : Finset ℝ :=
  Finset.univ.biUnion fun x =>
    match deletionTime seed η x with
    | none => ∅
    | some t => {t}

@[simp] theorem mem_deletionTimes (seed : V) (η t : ℝ) :
    t ∈ deletionTimes seed η ↔ ∃ x, deletionTime seed η x = some t := by
  simp only [deletionTimes, Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨x, hx⟩
    cases ht : deletionTime seed η x with
    | none => simp [ht] at hx
    | some u =>
      have htu : t = u := by simpa [ht] using hx
      subst t
      exact ⟨x, ht⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, by simp [hx]⟩

/-- The deletion times visible by `r`, together with the terminal scale `r`. -/
def deletionGrid (seed : V) (η r : ℝ) : Finset ℝ :=
  insert r ((deletionTimes seed η).filter (· ≤ r))

@[simp] theorem mem_deletionGrid (seed : V) (η r a : ℝ) :
    a ∈ deletionGrid seed η r ↔ a = r ∨ (a ≤ r ∧ ∃ x, deletionTime seed η x = some a) := by
  simp [deletionGrid, and_comm]

/-- The finite union of closed active complexes over a grid. -/
def activeUnion (seed : V) (η : ℝ) (G : Finset ℝ) :
    PreAbstractSimplicialComplex V where
  faces := {σ | ∃ a ∈ G, σ ∈ closedActiveComplex seed η a}
  isRelLowerSet_faces := by
    intro σ hσ
    obtain ⟨a, ha, hσ⟩ := hσ
    exact ⟨hσ.1.1, fun τ hτσ hτ =>
      ⟨a, ha, (closedActiveComplex seed η a).isRelLowerSet_faces hσ |>.2 hτσ hτ⟩⟩

@[simp] theorem mem_activeUnion (seed : V) (η : ℝ) (G : Finset ℝ) (σ : Finset V) :
    σ ∈ activeUnion seed η G ↔ ∃ a ∈ G, σ ∈ closedActiveComplex seed η a := Iff.rfl

/-- The sparse union needs only the terminal scale and actual finite deletion times. -/
theorem sparseComplex_eq_activeUnion_deletionGrid (seed : V) {η : ℝ}
    (hη : 0 < η) (hη' : η ≤ 1 / 3) (r : ℝ) :
    sparseComplex seed η r = activeUnion seed η (deletionGrid seed η r) := by
  ext σ
  constructor
  · rintro ⟨a, ha, har, hσ⟩
    let F := (deletionGrid seed η r).filter (a ≤ ·)
    have hrF : r ∈ F := Finset.mem_filter.mpr ⟨by simp, har⟩
    let b := F.min' ⟨r, hrF⟩
    have hbF : b ∈ F := Finset.min'_mem F ⟨r, hrF⟩
    have hab : a ≤ b := (Finset.mem_filter.mp hbF).2
    have hbr : b ≤ r := Finset.min'_le F r hrF
    have hbGrid : b ∈ deletionGrid seed η r := (Finset.mem_filter.mp hbF).1
    refine ⟨b, hbGrid, ?_, ?_⟩
    · exact relaxedComplex_mono hη.le (by linarith) (deletionTime seed η)
        (deletionTime_nonneg seed hη hη') hab hσ.1
    · intro x hx
      cases ht : deletionTime seed η x with
      | none => trivial
      | some t =>
        have hat : a ≤ t := by simpa [ClosedActive, ht] using hσ.2 x hx
        have hbt : b ≤ t := by
          by_cases htr : t ≤ r
          · apply Finset.min'_le F t
            exact Finset.mem_filter.mpr
              ⟨(mem_deletionGrid seed η r t).mpr (Or.inr ⟨htr, x, ht⟩), hat⟩
          · exact hbr.trans (le_of_lt (lt_of_not_ge htr))
        simpa [ClosedActive, ht] using hbt
  · rintro ⟨a, ha, hσ⟩
    have har : a ≤ r := (mem_deletionGrid seed η r a).mp ha |>.elim
      (fun h => h ▸ le_rfl) (fun h => h.1)
    exact ⟨a, hσ.1.2.1, har, hσ⟩

end

end TDA.Filtration.SparseRips
