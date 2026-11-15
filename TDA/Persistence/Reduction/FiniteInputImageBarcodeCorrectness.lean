import TDA.Persistence.Reduction.FiniteInputImageBarcode
import TDA.Persistence.FiniteDecomposition

/-!
# Complete semantics of sampled image-barcode extraction

The output multiset is the existing rank barcode of the actual image module.
Consequently it recovers every forward rank and admits a genuine natural
isomorphism to that module. The decomposition and its classical choices are
proof-side results; extraction does not execute them.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

namespace TDA.Persistence.Reduction.FiniteInput

open CategoryTheory
open scoped BigOperators

variable {N : ℕ}

private theorem coe_flatten_ofFn {α : Type*} {n : ℕ} (f : Fin n → List α) :
    ((List.ofFn f).flatten : Multiset α) = ∑ i, (f i : Multiset α) := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [List.ofFn_succ, List.flatten_cons, ← Multiset.coe_add,
      ih, Fin.sum_univ_succ]

/-- Exact multiset equality retains endpoint multiplicities and repeated occurrences. -/
theorem imageBarcode_multiset (xs ys : Input) (p : ℕ) (f : ℕ → ℕ)
    (t : Fin N → ℤ) (h : ImageBarcodeInput xs ys f t) :
    (imageBarcode xs ys p f t : Multiset (FiniteInterval N)) =
      rankBarcode (sampledImage xs ys p f t h) := by
  classical
  unfold imageBarcode imageBarcodeOfTable rankBarcode
  rw [coe_flatten_ofFn]
  apply Finset.sum_congr rfl
  intro b _
  rw [coe_flatten_ofFn]
  apply Finset.sum_congr rfl
  intro d _
  split_ifs with hbd
  · rw [Multiset.coe_replicate, imageMultiplicityInteger_correct xs ys p f t h]
  · rfl

/-- Endpoint occurrence counts are the computed nonnegative multiplicities. -/
theorem imageBarcode_multiplicity (xs ys : Input) (p : ℕ) (f : ℕ → ℕ)
    (t : Fin N → ℤ) (h : ImageBarcodeInput xs ys f t)
    (b d : ℕ) (hbd : b < d) (hd : d ≤ N) :
    barcodeMultiplicity (imageBarcode xs ys p f t : Multiset (FiniteInterval N)) b d =
      (imageMultiplicityInteger (imageRankTable xs ys p f t) b d).toNat := by
  rw [imageBarcode_multiset xs ys p f t h, imageMultiplicityInteger_correct xs ys p f t h]
  exact_mod_cast congrArg Int.toNat
    (barcodeMultiplicity_rankBarcode (sampledImage xs ys p f t h) b d hbd hd)

/-- Realizing the entire output recovers every computed forward-pair rank. -/
theorem imageBarcode_rank (xs ys : Input) (p : ℕ) (f : ℕ → ℕ)
    (t : Fin N → ℤ) (h : ImageBarcodeInput xs ys f t)
    (i j : Fin N) (hij : i ≤ j) :
    structureMapRank (barcodeModule (k := ZMod 2)
      (imageBarcode xs ys p f t : Multiset (FiniteInterval N))) i j hij =
      imageRank (imageRankTable xs ys p f t) i j := by
  rw [imageBarcode_multiset xs ys p f t h, structureMapRank_rankBarcode,
    imageRank_correct xs ys p f t h]

/-- This is a natural isomorphism of persistence modules, with no supplied decomposition. -/
theorem imageBarcode_nonempty_iso (xs ys : Input) (p : ℕ) (f : ℕ → ℕ)
    (t : Fin N → ℤ) (h : ImageBarcodeInput xs ys f t) :
    Nonempty (sampledImage xs ys p f t h ≅ barcodeModule (k := ZMod 2)
      (imageBarcode xs ys p f t : Multiset (FiniteInterval N))) := by
  rw [imageBarcode_multiset xs ys p f t h]
  exact nonempty_rankBarcodeIso _

/-- A successful call supplies geometry and monotonicity as well as full module semantics.
The stored table, output and wrapper have no proof arguments, so proof choices cannot
affect the returned list. -/
theorem runImageBarcode_correct (xs ys : Input) (p : ℕ) (f : ℕ → ℕ)
    (t : Fin N → ℤ) (out : List (FiniteInterval N))
    (hout : runImageBarcode xs ys p f t = some out) :
    ∃ h : ImageBarcodeInput xs ys f t,
      out.Pairwise ImageIntervalOrdered ∧
      (out : Multiset (FiniteInterval N)) = rankBarcode (sampledImage xs ys p f t h) ∧
      Nonempty (sampledImage xs ys p f t h ≅
        barcodeModule (k := ZMod 2) (out : Multiset (FiniteInterval N))) := by
  obtain ⟨h, rfl⟩ := (runImageBarcode_eq_some_iff xs ys p f t out).mp hout
  exact ⟨h, imageBarcode_ordered xs ys p f t, imageBarcode_multiset xs ys p f t h,
    imageBarcode_nonempty_iso xs ys p f t h⟩

/-- Identity input gives the ordinary barcode of sampled source homology.
No conclusion about grades omitted from the supplied observations is made. -/
theorem imageBarcode_id_multiset (xs : Input) (hx : Valid xs) (p : ℕ)
    (t : Fin N → ℤ) (ht : Monotone t) :
    (imageBarcode xs xs p id t : Multiset (FiniteInterval N)) =
      rankBarcode (sampledHomology xs hx p ⟨t, ht⟩) := by
  let h : ImageBarcodeInput xs xs id t :=
    ⟨⟨hx, hx, globalVertexMapCondition_id xs⟩, ht⟩
  rw [imageBarcode_multiset xs xs p id t h]
  apply (rankBarcode_eq_iff _ _).mpr
  intro i j hij
  exact sampledHomologyMap_id_image_rank xs hx p ⟨t, ht⟩ i j hij

end TDA.Persistence.Reduction.FiniteInput
