import TDA.Persistence.Reduction.FiniteInput

/-!
# Executable representatives of finite F₂ barcode occurrences

Chains are duplicate-free lists of original face indices. The reducer's finite
pivot pairs select normalized reduced columns; essential indices select columns
of the chronological change matrix. The existing value-output order is retained.
-/

set_option autoImplicit false

namespace TDA.Persistence.Reduction.FiniteInput

/-- The chronological, executable change of the original list-face basis. -/
def change (xs : Input) : Matrix (Fin xs.length) (Fin xs.length) (ZMod 2) :=
  traceChange (trace xs)

/-- F₂ chains are encoded by their increasing, nonzero face indices. -/
def supportChain {n : ℕ} (v : Fin n → ZMod 2) : List (Fin n) :=
  (List.finRange n).filter (fun i => v i ≠ 0)

/-- Interpret a support list as an F₂ coefficient vector in the original basis. -/
def chainVector {n : ℕ} (c : List (Fin n)) : Fin n → ZMod 2 :=
  fun i => if i ∈ c then 1 else 0

theorem supportChain_nodup {n : ℕ} (v : Fin n → ZMod 2) :
    (supportChain v).Nodup := (List.nodup_finRange n).filter _

private theorem f2_eq_one_of_ne_zero {a : ZMod 2} (ha : a ≠ 0) : a = 1 := by
  have h : ∀ b : ZMod 2, b = 0 ∨ b = 1 := by decide +kernel
  exact (h a).resolve_left ha

theorem chainVector_supportChain {n : ℕ} (v : Fin n → ZMod 2) :
    chainVector (supportChain v) = v := by
  funext i
  by_cases h : v i = 0
  · simp [chainVector, supportChain, h]
  · simp [chainVector, supportChain, f2_eq_one_of_ne_zero h]

/-- Normalizing at the pivot fixes the existing normal-form choice. -/
def pairedVector (xs : Input) (q : Fin xs.length × Fin xs.length) :
    Fin xs.length → ZMod 2 :=
  ((reduced xs) q.1 q.2)⁻¹ • (reduced xs).col q.2

def essentialVector (xs : Input) (i : Fin xs.length) : Fin xs.length → ZMod 2 :=
  (change xs).col i

/-- Additional data for one unchanged occurrence, with original list identities. -/
structure Representative (n : ℕ) where
  occurrence : Occurrence
  birthIndex : Fin n
  deathIndex : Option (Fin n)
  cycle : List (Fin n)
  bounding : Option (List (Fin n))
  deriving DecidableEq, Repr

/-- Equal-grade finite pairs are omitted by the existing value-output rule. -/
def pairedRepresentative (xs : Input) (q : Fin xs.length × Fin xs.length) :
    Option (Representative xs.length) :=
  (pairOccurrence xs q).map fun o =>
    ⟨o, q.1, some q.2, supportChain (pairedVector xs q),
      some (supportChain ((change xs).col q.2))⟩

def essentialRepresentative (xs : Input) (i : Fin xs.length) :
    Representative xs.length :=
  ⟨⟨degree xs i, (xs.get i).2, .essential⟩, i, none,
    supportChain (essentialVector xs i), none⟩

def representedOccurrences (xs : Input) : List (Representative xs.length) :=
  (pivotPairs xs).filterMap (pairedRepresentative xs) ++
    (essentialIndices xs).map (essentialRepresentative xs)

/-- Run the same validation and reducer with additive representative data. -/
def runWithRepresentatives (xs : Input) : Option (List (Representative xs.length)) :=
  if validBool xs then some (representedOccurrences xs) else none

theorem pairedRepresentative_forget (xs : Input) (q : Fin xs.length × Fin xs.length) :
    (pairedRepresentative xs q).map Representative.occurrence = pairOccurrence xs q := by
  simp [pairedRepresentative, Option.map_map, Function.comp_def]

theorem representedOccurrences_forget (xs : Input) :
    (representedOccurrences xs).map Representative.occurrence = occurrences xs := by
  unfold representedOccurrences occurrences finiteOccurrences essentialOccurrences
  rw [List.map_append, List.map_filterMap, List.map_map]
  congr 1
  · apply List.filterMap_congr
    intro q _
    exact pairedRepresentative_forget xs q

theorem pairedRepresentative_mem (xs : Input) (q : Fin xs.length × Fin xs.length)
    (hq : q ∈ pivotPairs xs) (r : Representative xs.length)
    (hr : pairedRepresentative xs q = some r) : r ∈ representedOccurrences xs :=
  List.mem_append_left _ (List.mem_filterMap.mpr ⟨q, hq, hr⟩)

theorem essentialRepresentative_mem (xs : Input) (i : Fin xs.length)
    (hi : i ∈ essentialIndices xs) : essentialRepresentative xs i ∈ representedOccurrences xs :=
  List.mem_append_right _ (List.mem_map.mpr ⟨i, hi, rfl⟩)

/-- Forgetting representatives preserves the exact ordered output, even on rejection. -/
theorem runWithRepresentatives_forget (xs : Input) :
    (runWithRepresentatives xs).map (List.map Representative.occurrence) = run xs := by
  by_cases h : validBool xs = true
  · simp [runWithRepresentatives, run, h, representedOccurrences_forget]
  · have hf : validBool xs = false := Bool.eq_false_iff.mpr h
    simp [runWithRepresentatives, run, hf]

theorem runWithRepresentatives_eq_none_iff (xs : Input) :
    runWithRepresentatives xs = none ↔ ¬ Valid xs := by
  simp [runWithRepresentatives, validBool_iff]

theorem runWithRepresentatives_eq_some_iff (xs : Input)
    (out : List (Representative xs.length)) :
    runWithRepresentatives xs = some out ↔ Valid xs ∧ out = representedOccurrences xs := by
  simp only [runWithRepresentatives]
  split_ifs with h
  · simp only [Option.some.injEq]
    exact ⟨fun he => ⟨(validBool_iff xs).mp h, he.symm⟩, fun he => he.2.symm⟩
  · simp only [false_iff, not_and]
    exact fun hv => (h ((validBool_iff xs).mpr hv)).elim

theorem pairedVector_eq_reduced_column (xs : Input)
    (q : Fin xs.length × Fin xs.length) (hq : q ∈ pivotPairs xs) :
    pairedVector xs q = (reduced xs).col q.2 := by
  have hp := (pivotPairs_mem xs q.1 q.2).mp hq
  have hne := ((columnPivot_some_iff ((reduced xs).col q.2) q.1).mp hp).1
  have hone : (reduced xs) q.1 q.2 = 1 := f2_eq_one_of_ne_zero hne
  simp [pairedVector, hone]

/-- The explicit paired construction agrees with the theoretical chosen normal column. -/
theorem pairedVector_eq_normalColumn (xs : Input)
    (q : Fin xs.length × Fin xs.length) (hq : q ∈ pivotPairs xs) :
    pairedVector xs q = normalColumn (reduced xs) (change xs) q.1 := by
  classical
  have hp := (pivotPairs_mem xs q.1 q.2).mp hq
  have hi : IsPivot (reduced xs) q.1 := ⟨q.2, hp⟩
  have hd := deathOfPivot_unique (reduced xs)
    (fun i j p hi hj => matrixReductionTrace_pivots_distinct (boundary xs) i j p hi hj)
    q.1 q.2 hi hp
  rw [normalColumn_pivot (reduced xs) (change xs) q.1 hi, hd]
  rfl

theorem essentialVector_eq_normalColumn (xs : Input) (i : Fin xs.length)
    (hi : i ∈ essentialIndices xs) :
    essentialVector xs i = normalColumn (reduced xs) (change xs) i := by
  rw [normalColumn_nonpivot (reduced xs) (change xs) i
    ((essentialIndices_mem xs i).mp hi).2]
  rfl

end TDA.Persistence.Reduction.FiniteInput
