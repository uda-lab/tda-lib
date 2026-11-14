import TDA.Persistence.RealBarcodeRank
import TDA.Persistence.DiagramLaws
import TDA.Persistence.FiniteRankProjectiveResolution
import Mathlib.Data.Finset.Sort

/-!
# Real barcode ranks and endpoint uniqueness

Actual finite interval families and barcode realizations have structure-map
ranks given by their endpoint occurrence counts. The existing interval-image
and realization-rank formulas supply the rank calculation; no new interval
decomposition is chosen.

Conversely, the counts determine every finite positive endpoint multiset.
A common grid contains every birth and finite death, and the existing
finite-barcode uniqueness theorem recovers the occurrences on that grid.
The construction includes empty multisets, repeated intervals and essential
right endpoints.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence.RealBarcode

open CategoryTheory
open scoped BigOperators Classical

private theorem exists_indexInterval {N : ℕ} (c : Fin N ↪o ℝ)
    (p : ℝ × WithTop ℝ) (hpos : (p.1 : WithTop ℝ) < p.2)
    (hb : p.1 ∈ Set.range c)
    (hd : ∀ d : ℝ, p.2 = (d : WithTop ℝ) → d ∈ Set.range c) :
    ∃ I : FiniteInterval N, RealBarcode.endpoints c I = p := by
  rcases p with ⟨b, d⟩
  rcases hb with ⟨i, hi⟩
  cases d using WithTop.recTopCoe with
  | top =>
      let I : FiniteInterval N := ⟨i.val, N, i.isLt, le_rfl⟩
      exact ⟨I, by simp [RealBarcode.endpoints, I, hi]⟩
  | coe d =>
      rcases hd d rfl with ⟨j, hj⟩
      have hij : i < j := c.lt_iff_lt.mp (by
        simpa only [hi, hj] using WithTop.coe_lt_coe.mp hpos)
      let I : FiniteInterval N := ⟨i.val, j.val, hij, j.isLt.le⟩
      exact ⟨I, by simp [RealBarcode.endpoints, I, hi, hj, j.isLt]⟩

private theorem exists_indexBars {N : ℕ} (c : Fin N ↪o ℝ)
    (B : Multiset (ℝ × WithTop ℝ)) :
    (∀ p ∈ B, (p.1 : WithTop ℝ) < p.2) →
    (∀ p ∈ B, p.1 ∈ Set.range c) →
    (∀ p ∈ B, ∀ d : ℝ, p.2 = (d : WithTop ℝ) → d ∈ Set.range c) →
    ∃ A : Multiset (FiniteInterval N), (ofIndexBars c c.strictMono A).points = B := by
  classical
  induction B using Multiset.induction_on with
  | empty =>
      intro _ _ _
      exact ⟨0, rfl⟩
  | @cons p B ih =>
      intro hpos hb hd
      obtain ⟨I, hI⟩ := exists_indexInterval c p
        (hpos p (Multiset.mem_cons_self _ _)) (hb p (Multiset.mem_cons_self _ _))
        (hd p (Multiset.mem_cons_self _ _))
      obtain ⟨A, hA⟩ := ih (fun p hp => hpos p (Multiset.mem_cons_of_mem hp))
        (fun p hp => hb p (Multiset.mem_cons_of_mem hp))
        (fun p hp => hd p (Multiset.mem_cons_of_mem hp))
      refine ⟨I ::ₘ A, ?_⟩
      simpa only [RealBarcode.ofIndexBars_points, Multiset.map_cons, hI] using
        congrArg (fun x => p ::ₘ x) hA

private theorem finiteRankCounts_injective {N : ℕ} (A B : Multiset (FiniteInterval N))
    (h : ∀ (i j : Fin N), i ≤ j →
      A.countP (fun I => I.birth ≤ i.val ∧ j.val < I.death) =
      B.countP (fun I => I.birth ≤ i.val ∧ j.val < I.death)) : A = B := by
  have he : rankBarcode (barcodeModule (k := ℚ) A) =
      rankBarcode (barcodeModule (k := ℚ) B) := by
    apply (rankBarcode_eq_iff _ _).mpr
    intro i j hij
    rw [rank_barcodeMap, rank_barcodeMap]
    exact h i j hij
  simpa only [rankBarcode_barcodeModule] using he

private theorem rankCounts_injective_on_grid {N : ℕ} (c : Fin N ↪o ℝ)
    (B C : Multiset (ℝ × WithTop ℝ))
    (hB : ∀ p ∈ B, (p.1 : WithTop ℝ) < p.2)
    (hC : ∀ p ∈ C, (p.1 : WithTop ℝ) < p.2)
    (hbB : ∀ p ∈ B, p.1 ∈ Set.range c)
    (hbC : ∀ p ∈ C, p.1 ∈ Set.range c)
    (hdB : ∀ p ∈ B, ∀ d : ℝ, p.2 = (d : WithTop ℝ) → d ∈ Set.range c)
    (hdC : ∀ p ∈ C, ∀ d : ℝ, p.2 = (d : WithTop ℝ) → d ∈ Set.range c)
    (h : ∀ s t : ℝ, s ≤ t →
      B.countP (fun p => p.1 ≤ s ∧ (t : WithTop ℝ) < p.2) =
      C.countP (fun p => p.1 ≤ s ∧ (t : WithTop ℝ) < p.2)) : B = C := by
  obtain ⟨A, hA⟩ := exists_indexBars c B hB hbB hdB
  obtain ⟨D, hD⟩ := exists_indexBars c C hC hbC hdC
  have he : A = D := by
    apply finiteRankCounts_injective
    intro i j hij
    have ht := h (c i) (c j) (c.monotone hij)
    rw [← hA, ← hD, ofIndexBars_countP_grades, ofIndexBars_countP_grades] at ht
    exact ht
  rw [← hA, ← hD, he]

/-- Positive finite endpoint multisets are determined by their interval counts
across all ordered real parameter pairs. The proof encodes births and finite
deaths on one finite grid and reuses finite-barcode uniqueness; essential
deaths remain essential and repeated endpoints retain their multiplicities. -/
theorem multiset_eq_of_rankCounts_eq (B C : Multiset (ℝ × WithTop ℝ))
    (hB : ∀ p ∈ B, (p.1 : WithTop ℝ) < p.2)
    (hC : ∀ p ∈ C, (p.1 : WithTop ℝ) < p.2)
    (h : ∀ s t : ℝ, s ≤ t →
      B.countP (fun p => p.1 ≤ s ∧ (t : WithTop ℝ) < p.2) =
      C.countP (fun p => p.1 ≤ s ∧ (t : WithTop ℝ) < p.2)) : B = C := by
  classical
  let S : Finset ℝ := ((B + C).map Prod.fst).toFinset ∪
    ((finitePart (B + C)).map Prod.snd).toFinset
  let c : Fin S.card ↪o ℝ := S.orderEmbOfFin rfl
  have hc : Set.range c = (S : Set ℝ) := Finset.range_orderEmbOfFin S rfl
  have hb : ∀ p ∈ B + C, p.1 ∈ Set.range c := by
    intro p hp
    rw [hc]
    exact Finset.mem_union_left _ (Multiset.mem_toFinset.mpr
      (Multiset.mem_map.mpr ⟨p, hp, rfl⟩))
  have hd : ∀ p ∈ B + C, ∀ d : ℝ, p.2 = (d : WithTop ℝ) → d ∈ Set.range c := by
    intro p hp d he
    rw [hc]
    apply Finset.mem_union_right
    apply Multiset.mem_toFinset.mpr
    apply Multiset.mem_map.mpr
    refine ⟨(p.1, d), ?_, rfl⟩
    apply (Multiset.mem_filterMap _ _).mpr
    exact ⟨p, hp, by simp [he]⟩
  exact rankCounts_injective_on_grid c B C hB hC
    (fun p hp => hb p (Multiset.mem_add.mpr (Or.inl hp)))
    (fun p hp => hb p (Multiset.mem_add.mpr (Or.inr hp)))
    (fun p hp => hd p (Multiset.mem_add.mpr (Or.inl hp)))
    (fun p hp => hd p (Multiset.mem_add.mpr (Or.inr hp))) h

variable {k : Type u} [Field k]

/-- The rank of an actual barcode realization counts the interval occurrences
covering both parameters. This also permits empty interval supports. -/
theorem rank_realize (D : Diagram ℝ) (s t : ℝ) (hst : s ≤ t) :
    rankOfStructureMap (RealBarcode.realize (k := k) D) hst =
      D.points.countP (fun p => p.1 ≤ s ∧ (t : WithTop ℝ) < p.2) := by
  exact realize_image_rank D hst

/-- The actual finite product of real interval modules has rank equal to the
number of occurrences covering both parameters. Repeated and empty supports
are allowed, and essential right endpoints are retained. -/
theorem rank_intervalFamily {J : Type} [Fintype J]
    (F : J → ℝ × WithTop ℝ) (s t : ℝ) (hst : s ≤ t) :
    rankOfStructureMap (RealBarcode.familyModule
      (fun a => RealBarcode.intervalModule (k := k) (F a))) hst =
      ∑ a : J, if (F a).1 ≤ s ∧ (t : WithTop ℝ) < (F a).2 then 1 else 0 := by
  classical
  let f := fun i : J => structureMapLinear (intervalModule (k := k) (F i)) hst
  change Module.finrank k (LinearMap.range (LinearMap.piMap f)) = _
  let : ∀ i : J, FiniteDimensional k ((intervalModule (k := k) (F i)).obj s) :=
    fun i => by
      change FiniteDimensional k (fiber (k := k) (F i) s)
      infer_instance
  rw [finrank_range_piMap f]
  apply Finset.sum_congr rfl
  intro i _
  have he : alive (F i) s ∧ alive (F i) t ↔
      (F i).1 ≤ s ∧ (t : WithTop ℝ) < (F i).2 := by
    constructor
    · exact fun h => ⟨h.1.1, h.2.2⟩
    · exact fun h => ⟨⟨h.1, lt_of_le_of_lt (WithTop.coe_le_coe.mpr hst) h.2⟩,
        ⟨h.1.trans hst, h.2⟩⟩
  change Module.finrank k (persistenceImage (intervalModule (k := k) (F i)) hst) = _
  rw [intervalImage_rank]
  simp only [he]

/-- Positive real barcode diagrams agree whenever their actual realizations
have equal ranks at every ordered pair of parameters. -/
theorem diagram_eq_of_rank_eq (D E : Diagram ℝ) (hD : D.IsPositive) (hE : E.IsPositive)
    (h : ∀ (s t : ℝ) (hst : s ≤ t),
      rankOfStructureMap (realize (k := k) D) hst =
        rankOfStructureMap (realize (k := k) E) hst) : D = E := by
  apply Diagram.ext
  apply multiset_eq_of_rankCounts_eq D.points E.points hD hE
  intro s t hst
  simpa only [rank_realize] using h s t hst

end TDA.Persistence.RealBarcode
