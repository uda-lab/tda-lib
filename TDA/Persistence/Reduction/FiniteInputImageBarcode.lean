import TDA.Persistence.Reduction.FiniteInputImageRanks

/-!
# Executable sampled image barcodes

Endpoint pairs are traversed by increasing birth, then increasing death. Each
signed multiplicity is replicated only after its nonnegativity has been proved
for validated input in `FiniteInputImageRanks`. Equal intervals remain separate
occurrences. Death at the observation count means observed survival only.
-/

set_option autoImplicit false

namespace TDA.Persistence.Reduction.FiniteInput

variable {N : ℕ}

/-- Enumerate endpoint pairs from a stored table. On validated tables the integer
differences are nonnegative; this lower-level operation itself performs no validation. -/
def imageBarcodeOfTable (R : ImageRankTable N) : List (FiniteInterval N) :=
  (List.ofFn fun b : Fin N =>
    (List.ofFn fun d : Fin (N + 1) =>
      if h : b.val < d.val then
        List.replicate (imageMultiplicityInteger R b.val d.val).toNat
          ⟨b.val, d.val, h, by omega⟩
      else []).flatten).flatten

/-- Compute the table once and reuse it for every endpoint multiplicity. -/
def imageBarcode (xs ys : Input) (p : ℕ) (f : ℕ → ℕ) (t : Fin N → ℤ) :
    List (FiniteInterval N) :=
  let R := imageRankTable xs ys p f t
  imageBarcodeOfTable R

/-- Validate the complete geometry and global map even when there are no observations. -/
def runImageBarcode (xs ys : Input) (p : ℕ) (f : ℕ → ℕ) (t : Fin N → ℤ) :
    Option (List (FiniteInterval N)) :=
  if ImageBarcodeInput xs ys f t then some (imageBarcode xs ys p f t) else none

theorem runImageBarcode_eq_some_iff (xs ys : Input) (p : ℕ) (f : ℕ → ℕ)
    (t : Fin N → ℤ) (out : List (FiniteInterval N)) :
    runImageBarcode xs ys p f t = some out ↔
      ImageBarcodeInput xs ys f t ∧ out = imageBarcode xs ys p f t := by
  simp only [runImageBarcode]
  split_ifs with h <;> simp [h, eq_comm]

theorem runImageBarcode_eq_none_iff (xs ys : Input) (p : ℕ) (f : ℕ → ℕ)
    (t : Fin N → ℤ) :
    runImageBarcode xs ys p f t = none ↔ ¬ ImageBarcodeInput xs ys f t := by
  simp [runImageBarcode]

/-- Weak lexicographic order permits distinct occurrences of equal intervals. -/
def ImageIntervalOrdered (I J : FiniteInterval N) : Prop :=
  I.birth < J.birth ∨ I.birth = J.birth ∧ I.death ≤ J.death

private theorem pairwise_flatten_ofFn {α : Type*} {n : ℕ} (R : α → α → Prop)
    (f : Fin n → List α) (hs : ∀ i, (f i).Pairwise R)
    (hc : ∀ i j, i < j → ∀ x ∈ f i, ∀ y ∈ f j, R x y) :
    (List.ofFn f).flatten.Pairwise R := by
  rw [List.pairwise_flatten]
  constructor
  · intro l hl
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hl
    exact hs i
  · rw [List.pairwise_ofFn]
    exact fun {i j} hij => hc i j hij

private theorem block_endpoints (R : ImageRankTable N) (b : Fin N) (d : Fin (N + 1))
    (I : FiniteInterval N)
    (hI : I ∈ (if h : b.val < d.val then
      List.replicate (imageMultiplicityInteger R b.val d.val).toNat
        (⟨b.val, d.val, h, by omega⟩ : FiniteInterval N) else [])) :
    I.birth = b.val ∧ I.death = d.val := by
  split_ifs at hI with h
  · obtain ⟨_, rfl⟩ := List.mem_replicate.mp hI
    exact ⟨rfl, rfl⟩
  · simp at hI

/-- Deterministic endpoint order holds even for an arbitrary lower-level table. -/
theorem imageBarcodeOfTable_ordered (R : ImageRankTable N) :
    (imageBarcodeOfTable R).Pairwise ImageIntervalOrdered := by
  unfold imageBarcodeOfTable
  apply pairwise_flatten_ofFn
  · intro b
    apply pairwise_flatten_ofFn
    · intro d
      split_ifs with h
      · simp [ImageIntervalOrdered]
      · simp
    · intro d e hde I hI J hJ
      obtain ⟨hIb, hId⟩ := block_endpoints R b d I hI
      obtain ⟨hJb, hJd⟩ := block_endpoints R b e J hJ
      exact Or.inr ⟨hIb.trans hJb.symm, by rw [hId, hJd]; exact Nat.le_of_lt hde⟩
  · intro b c hbc I hI J hJ
    obtain ⟨l, hl, hI⟩ := List.mem_flatten.mp hI
    obtain ⟨d, rfl⟩ := List.mem_ofFn.mp hl
    obtain ⟨l, hl, hJ⟩ := List.mem_flatten.mp hJ
    obtain ⟨e, rfl⟩ := List.mem_ofFn.mp hl
    have hi := (block_endpoints R b d I hI).1
    have hj := (block_endpoints R c e J hJ).1
    exact Or.inl (by rw [hi, hj]; exact hbc)

theorem imageBarcode_ordered (xs ys : Input) (p : ℕ) (f : ℕ → ℕ)
    (t : Fin N → ℤ) : (imageBarcode xs ys p f t).Pairwise ImageIntervalOrdered :=
  imageBarcodeOfTable_ordered _

end TDA.Persistence.Reduction.FiniteInput
