import TDA.Persistence.IndexDiagram
import TDA.Persistence.RankBarcode
import TDA.Persistence.DiagramLaws
import Mathlib.Data.Finset.Sort

/-!
# Diagrams over a linear order are determined by their slice counts

For a diagram over a linear order `α`, the slice count at `a ≤ b` is the number of points
`(b', d)`, with multiplicity, such that `b' ≤ a` and `b < d`: inclusive birth and strict death,
the convention of `rank_sublevelHomologyMap`. `multiset_eq_of_sliceCounts_eq` says that two
finite multisets of positive points (`b' < d`, essential deaths `⊤` allowed) with equal slice
counts at all `a ≤ b` are equal, and `Diagram.eq_of_sliceCounts_eq` says the same for positive
diagrams.

`RealBarcode.multiset_eq_of_rankCounts_eq` is derived from this theorem as its real case. The
births and finite deaths of both multisets lie on one finite grid
`Finset.orderEmbOfFin`; on it each multiset is `ofIndexBars` of a finite index barcode, the slice
counts become the interval counts of those barcodes (`ofIndexBars_countP_grades`), and
finite-barcode uniqueness (`rankBarcode_barcodeModule`, `rank_barcodeMap`) recovers them. Only
the order of `α` is used.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence

variable {α : Type u} [LinearOrder α]

/-- The point of an index interval on a strictly monotone grid; it is the point of
`ofIndexBars` (`ofIndexBars_points_eq_map`). -/
private def gridPoint {N : ℕ} (v : Fin N → α) (I : FiniteInterval N) : α × WithTop α :=
  (v ⟨I.birth, lt_of_lt_of_le I.birth_lt_death I.death_le_size⟩,
    if hd : I.death < N then (v ⟨I.death, hd⟩ : WithTop α) else ⊤)

private theorem ofIndexBars_points_eq_map {N : ℕ} (v : Fin N → α) (hv : StrictMono v)
    (B : Multiset (FiniteInterval N)) :
    (ofIndexBars v hv B).points = B.map (gridPoint v) :=
  rfl

private theorem exists_gridInterval {N : ℕ} (c : Fin N ↪o α)
    (p : α × WithTop α) (hpos : (p.1 : WithTop α) < p.2)
    (hb : p.1 ∈ Set.range c)
    (hd : ∀ d : α, p.2 = (d : WithTop α) → d ∈ Set.range c) :
    ∃ I : FiniteInterval N, gridPoint c I = p := by
  rcases p with ⟨b, d⟩
  rcases hb with ⟨i, hi⟩
  cases d using WithTop.recTopCoe with
  | top =>
      exact ⟨⟨i.val, N, i.isLt, le_rfl⟩, by simp [gridPoint, hi]⟩
  | coe d =>
      rcases hd d rfl with ⟨j, hj⟩
      have hij : i < j := c.lt_iff_lt.mp (by
        simpa only [hi, hj] using WithTop.coe_lt_coe.mp hpos)
      exact ⟨⟨i.val, j.val, hij, j.isLt.le⟩, by simp [gridPoint, hi, hj, j.isLt]⟩

private theorem exists_gridBars {N : ℕ} (c : Fin N ↪o α)
    (B : Multiset (α × WithTop α)) :
    (∀ p ∈ B, (p.1 : WithTop α) < p.2) →
    (∀ p ∈ B, p.1 ∈ Set.range c) →
    (∀ p ∈ B, ∀ d : α, p.2 = (d : WithTop α) → d ∈ Set.range c) →
    ∃ A : Multiset (FiniteInterval N), (ofIndexBars c c.strictMono A).points = B := by
  classical
  induction B using Multiset.induction_on with
  | empty =>
      intro _ _ _
      exact ⟨0, rfl⟩
  | @cons p B ih =>
      intro hpos hb hd
      obtain ⟨I, hI⟩ := exists_gridInterval c p
        (hpos p (Multiset.mem_cons_self _ _)) (hb p (Multiset.mem_cons_self _ _))
        (hd p (Multiset.mem_cons_self _ _))
      obtain ⟨A, hA⟩ := ih (fun p hp => hpos p (Multiset.mem_cons_of_mem hp))
        (fun p hp => hb p (Multiset.mem_cons_of_mem hp))
        (fun p hp => hd p (Multiset.mem_cons_of_mem hp))
      refine ⟨I ::ₘ A, ?_⟩
      rw [ofIndexBars_points_eq_map] at hA ⊢
      rw [Multiset.map_cons, hI, hA]

private theorem barcode_eq_of_countP_eq {N : ℕ} (A B : Multiset (FiniteInterval N))
    (h : ∀ i j : Fin N, i ≤ j →
      A.countP (fun I => I.birth ≤ i.val ∧ j.val < I.death) =
      B.countP (fun I => I.birth ≤ i.val ∧ j.val < I.death)) : A = B := by
  have he : rankBarcode (barcodeModule (k := ℚ) A) =
      rankBarcode (barcodeModule (k := ℚ) B) := by
    apply (rankBarcode_eq_iff _ _).mpr
    intro i j hij
    rw [rank_barcodeMap, rank_barcodeMap]
    exact h i j hij
  simpa only [rankBarcode_barcodeModule] using he

/-- **Slice counts determine positive multisets.** Two finite multisets of points over a linear
order, each with birth strictly below death (`⊤` allowed as death), that have the same number
of points `(b', d)` with `b' ≤ a` and `b < d` for all `a ≤ b`, are equal. -/
theorem multiset_eq_of_sliceCounts_eq (B C : Multiset (α × WithTop α))
    (hB : ∀ p ∈ B, (p.1 : WithTop α) < p.2)
    (hC : ∀ p ∈ C, (p.1 : WithTop α) < p.2)
    (h : ∀ a b : α, a ≤ b →
      B.countP (fun p => p.1 ≤ a ∧ (b : WithTop α) < p.2) =
      C.countP (fun p => p.1 ≤ a ∧ (b : WithTop α) < p.2)) : B = C := by
  classical
  let S : Finset α := ((B + C).map Prod.fst).toFinset ∪
    ((finitePart (B + C)).map Prod.snd).toFinset
  let c : Fin S.card ↪o α := S.orderEmbOfFin rfl
  have hc : Set.range c = (S : Set α) := Finset.range_orderEmbOfFin S rfl
  have hb : ∀ p ∈ B + C, p.1 ∈ Set.range c := by
    intro p hp
    rw [hc]
    exact Finset.mem_union_left _ (Multiset.mem_toFinset.mpr
      (Multiset.mem_map.mpr ⟨p, hp, rfl⟩))
  have hd : ∀ p ∈ B + C, ∀ d : α, p.2 = (d : WithTop α) → d ∈ Set.range c := by
    intro p hp d he
    rw [hc]
    apply Finset.mem_union_right
    apply Multiset.mem_toFinset.mpr
    apply Multiset.mem_map.mpr
    refine ⟨(p.1, d), ?_, rfl⟩
    apply (Multiset.mem_filterMap _ _).mpr
    exact ⟨p, hp, by simp [he]⟩
  obtain ⟨A, hA⟩ := exists_gridBars c B hB
    (fun p hp => hb p (Multiset.mem_add.mpr (Or.inl hp)))
    (fun p hp => hd p (Multiset.mem_add.mpr (Or.inl hp)))
  obtain ⟨A', hA'⟩ := exists_gridBars c C hC
    (fun p hp => hb p (Multiset.mem_add.mpr (Or.inr hp)))
    (fun p hp => hd p (Multiset.mem_add.mpr (Or.inr hp)))
  have he : A = A' := by
    apply barcode_eq_of_countP_eq
    intro i j hij
    have ht := h (c i) (c j) (c.monotone hij)
    rw [← hA, ← hA', ofIndexBars_countP_grades, ofIndexBars_countP_grades] at ht
    exact ht
  rw [← hA, ← hA', he]

/-- **Slice counts determine positive diagrams.** Two positive diagrams over a linear order
with the same slice counts at all `a ≤ b` are equal. -/
theorem Diagram.eq_of_sliceCounts_eq {D E : Diagram α} (hD : D.IsPositive) (hE : E.IsPositive)
    (h : ∀ a b : α, a ≤ b →
      D.points.countP (fun p => p.1 ≤ a ∧ (b : WithTop α) < p.2) =
      E.points.countP (fun p => p.1 ≤ a ∧ (b : WithTop α) < p.2)) : D = E :=
  Diagram.ext (multiset_eq_of_sliceCounts_eq D.points E.points hD hE h)

end TDA.Persistence
