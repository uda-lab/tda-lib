import TDA.Persistence.RealBarcodeRankUniqueness

/-!
# Barcode cancellation for finite rank-exact resolutions

Rank additivity in the actual rows of a finite resolution telescopes to an
additive equality between the resolved rank and the even and odd term ranks.
When the resolved module is realized by a positive finite real barcode and
the terms have interval rank counts, endpoint uniqueness upgrades this rank
equality to equality of endpoint multisets. This is the algebraic cancellation
step used for affine restrictions of signed hook barcodes.
-/

set_option autoImplicit false

universe u v

namespace TDA.Persistence.FiniteRankExactResolution

open CategoryTheory
open scoped BigOperators Classical

private theorem parityTelescope {A : Type*} [AddCommMonoid A] :
    ∀ (m : ℕ) (r : Fin (m + 1) → A) (q : Fin m → A),
      (∀ i, q i = r i.succ + r i.castSucc) → r (Fin.last m) = 0 →
      r 0 + (∑ i : Fin m, if Odd i.val then q i else 0) =
        ∑ i : Fin m, if Even i.val then q i else 0 := by
  intro m
  induction m with
  | zero => intro r q _ hz; simpa using hz
  | succ m ih =>
      intro r q hrow hz
      let r' : Fin (m + 1) → A := fun i => r i.succ
      let q' : Fin m → A := fun i => q i.succ
      have hrow' : ∀ i, q' i = r' i.succ + r' i.castSucc := by
        intro i
        simpa [r', q'] using hrow i.succ
      have hz' : r' (Fin.last m) = 0 := by
        simpa [r', Fin.succ_last] using hz
      have ht := ih r' q' hrow' hz'
      have hEven : Even (0 : ℕ) := ⟨0, rfl⟩
      simp only [Fin.sum_univ_succ, Fin.val_zero, Nat.not_odd_zero,
        hEven, ↓reduceIte, zero_add, Fin.val_succ,
        Nat.odd_add_one, Nat.even_add_one, Nat.not_odd_iff_even, Nat.not_even_iff_odd]
      change r 0 + (∑ i : Fin m, if Even i.val then q' i else 0) =
        q 0 + ∑ i : Fin m, if Odd i.val then q' i else 0
      rw [← ht, hrow 0]
      simp only [r', Fin.castSucc_zero]
      ac_rfl


variable {k : Type u} [Field k] {P : Type v} [Preorder P]
    {M : PModule.{u, v, u} k P}

/-- The structure-map rank of the resolved module plus the odd-degree ranks
equals the even-degree ranks. The actual rank-exact rows telescope over the
natural numbers, including a resolution of length zero. -/
theorem rank_add_odd_eq_even (R : FiniteRankExactResolution M)
    {a b : P} (hab : a ≤ b) :
    rankOfStructureMap M hab +
      (∑ i : Fin R.length, if Odd i.val then rankOfStructureMap (R.term i) hab else 0) =
      ∑ i : Fin R.length, if Even i.val then rankOfStructureMap (R.term i) hab else 0 := by
  have hz : rankOfStructureMap (R.kernel (Fin.last R.length)) hab = 0 := by
    rw [rankOfStructureMap_iso hab R.terminal_iso, rankOfStructureMap_zero]
  have ht := parityTelescope R.length
    (fun i => rankOfStructureMap (R.kernel i) hab)
    (fun i => rankOfStructureMap (R.term i) hab)
    (fun i => (R.row_rank_exact i).rank_add hab) hz
  rw [rankOfStructureMap_iso hab R.initial_iso] at ht
  exact ht

private theorem positive_sum_ite {J : Type} [Fintype J]
    (D : J → Multiset (ℝ × WithTop ℝ)) (p : J → Prop) [DecidablePred p]
    (hD : ∀ i, ∀ x ∈ D i, (x.1 : WithTop ℝ) < x.2) :
    ∀ x ∈ (∑ i, if p i then D i else 0), (x.1 : WithTop ℝ) < x.2 := by
  intro x hx
  obtain ⟨i, _, hi⟩ := Multiset.mem_sum.mp hx
  by_cases hp : p i
  · simp only [hp, ↓reduceIte] at hi
    exact hD i x hi
  · simp [hp] at hi

private theorem countP_sum_ite {J α : Type} [Fintype J]
    (D : J → Multiset α) (parity : J → Prop) (p : α → Prop)
    [DecidablePred parity] [DecidablePred p] :
    (∑ i, if parity i then D i else 0).countP p =
      ∑ i, if parity i then (D i).countP p else 0 := by
  change (Multiset.countPAddMonoidHom p) _ = _
  rw [map_sum]
  simp only [apply_ite, Multiset.coe_countPAddMonoidHom, Multiset.countP_zero]

/-- An actual finite rank-exact resolution gives endpoint-multiset cancellation
along any monotone real parameterization. The resolved module is identified
with its actual barcode realization, and each term is described by positive
endpoint occurrences whose counts compute its structure-map ranks.

Applications derive these descriptions from the term modules; no minimality
or projectivity of the restricted resolution is needed. The equality retains
all multiplicities and uses addition rather than truncated subtraction. -/
theorem barcode_points_add_odd_eq_even (R : FiniteRankExactResolution M) (f : ℝ →o P)
    (B : Diagram ℝ) (hB : B.IsPositive)
    (eB : reindex f M ≅ RealBarcode.realize (k := k) B)
    (D : Fin R.length → Multiset (ℝ × WithTop ℝ))
    (hD : ∀ i, ∀ p ∈ D i, (p.1 : WithTop ℝ) < p.2)
    (hrank : ∀ i (s t : ℝ) (hst : s ≤ t),
      rankOfStructureMap (R.term i) (f.monotone hst) =
        (D i).countP (fun p => p.1 ≤ s ∧ (t : WithTop ℝ) < p.2)) :
    B.points + (∑ i : Fin R.length, if Odd i.val then D i else 0) =
      ∑ i : Fin R.length, if Even i.val then D i else 0 := by
  apply RealBarcode.multiset_eq_of_rankCounts_eq
  · intro x hx
    rcases Multiset.mem_add.mp hx with hx | hx
    · exact hB x hx
    · exact positive_sum_ite D (fun i => Odd i.val) hD x hx
  · exact positive_sum_ite D (fun i => Even i.val) hD
  · intro s t hst
    rw [Multiset.countP_add, countP_sum_ite, countP_sum_ite]
    have ht := rank_add_odd_eq_even R (f.monotone hst)
    have hm : rankOfStructureMap M (f.monotone hst) =
        B.points.countP (fun p => p.1 ≤ s ∧ (t : WithTop ℝ) < p.2) := by
      change rankOfStructureMap (reindex f M) hst = _
      rw [rankOfStructureMap_iso hst eB, RealBarcode.rank_realize]
    have hi (i : Fin R.length) := hrank i s t hst
    simp only [hm, hi] at ht
    exact ht

end TDA.Persistence.FiniteRankExactResolution
