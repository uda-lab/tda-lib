import TDA.Persistence.RankBarcode
import Mathlib.Data.Fintype.Fin

/-!
# Finite monotone sampling of ranks and barcodes

Endpoint cuts count sample occurrences, including repeated source indices. Restriction
uses these cuts to retain precisely the sampled part of each half-open interval and
drops empty restrictions. For an arbitrary module with finite-dimensional fibers,
reindexing transports actual structure-map ranks, sums integer multiplicities over
endpoint rectangles, and restricts the canonical rank barcode by `Multiset.filterMap`.

Death at the size of the sample denotes survival through its last observed stage.
The construction uses finite ranks and does not require a module decomposition.
-/

universe u
namespace TDA.Persistence
open scoped BigOperators

variable {L N : ℕ}

/-- Count sample *occurrences* strictly before a source endpoint. -/
def sampledEndpoint (s : Fin N →o Fin L) (e : ℕ) : ℕ :=
  (Finset.univ.filter (fun j : Fin N => (s j).val < e)).card

private theorem sampledEndpoint_le (s : Fin N →o Fin L) (e : ℕ) :
    sampledEndpoint s e ≤ N := by
  unfold sampledEndpoint
  calc
    (Finset.univ.filter (fun j : Fin N => (s j).val < e)).card ≤
        (Finset.univ : Finset (Fin N)).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    _ = N := by simp

private theorem sampledEndpoint_mono (s : Fin N →o Fin L) {a b : ℕ}
    (hab : a ≤ b) : sampledEndpoint s a ≤ sampledEndpoint s b := by
  unfold sampledEndpoint
  apply Finset.card_le_card
  intro j hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
  exact hj.trans_le hab

private theorem sampledEndpoint_zero (s : Fin N →o Fin L) :
    sampledEndpoint s 0 = 0 := by simp [sampledEndpoint]

private theorem sampledEndpoint_size (s : Fin N →o Fin L) :
    sampledEndpoint s L = N := by
  simp [sampledEndpoint]

/-- A monotone sample's endpoint cut is exactly the initial segment below that endpoint. -/
theorem lt_sampledEndpoint_iff (s : Fin N →o Fin L) (e : ℕ) (j : Fin N) :
    j.val < sampledEndpoint s e ↔ (s j).val < e := by
  simpa only [sampledEndpoint] using
    (Fin.lt_card_filter_univ_iff_apply_of_imp
      (j := j) (fun i : Fin N => (s i).val < e)
      (by
        intro i j hji hi
        exact (Fin.le_iff_val_le_val.mp (s.monotone' hji)).trans_lt hi))

private theorem sampledEndpoint_le_val_iff (s : Fin N →o Fin L) (e : ℕ) (j : Fin N) :
    sampledEndpoint s e ≤ j.val ↔ e ≤ (s j).val := by
  have h := lt_sampledEndpoint_iff s e j
  omega

namespace FiniteInterval

/-- The sampled half-open interval, dropped exactly when it has no sampled occurrence. -/
def restrictAlong (s : Fin N →o Fin L) (I : FiniteInterval L) :
    Option (FiniteInterval N) :=
  if h : sampledEndpoint s I.birth < sampledEndpoint s I.death then
    some ⟨sampledEndpoint s I.birth, sampledEndpoint s I.death, h,
      sampledEndpoint_le s I.death⟩
  else none

/-- An interval restriction is empty exactly when no sample occurrence lies in the interval. -/
theorem restrictAlong_eq_none_iff (s : Fin N →o Fin L) (I : FiniteInterval L) :
    I.restrictAlong s = none ↔ ∀ j : Fin N, ¬ I.alive (s j) := by
  constructor
  · intro hn j hj
    have hmono := sampledEndpoint_mono s (Nat.le_of_lt I.birth_lt_death)
    have hnot : ¬ sampledEndpoint s I.birth < sampledEndpoint s I.death := by
      intro hlt
      simp [restrictAlong, hlt] at hn
    have heq : sampledEndpoint s I.birth = sampledEndpoint s I.death := by omega
    have hb := (sampledEndpoint_le_val_iff s I.birth j).2 hj.1
    have hd := (lt_sampledEndpoint_iff s I.death j).2 hj.2
    omega
  · intro h
    by_cases hlt : sampledEndpoint s I.birth < sampledEndpoint s I.death
    · have hbound : sampledEndpoint s I.birth < N :=
        hlt.trans_le (sampledEndpoint_le s I.death)
      let j : Fin N := ⟨sampledEndpoint s I.birth, hbound⟩
      have hj : I.alive (s j) := by
        constructor
        · apply (sampledEndpoint_le_val_iff s I.birth j).1
          rfl
        · apply (lt_sampledEndpoint_iff s I.death j).1
          exact hlt
      exact False.elim (h j hj)
    · simp [restrictAlong, hlt]

/-- A retained interval is alive precisely at the occurrences sampled from the source interval. -/
theorem alive_restrictAlong (s : Fin N →o Fin L) (I : FiniteInterval L)
    (J : FiniteInterval N) (h : I.restrictAlong s = some J) (j : Fin N) :
    J.alive j ↔ I.alive (s j) := by
  have hlt : sampledEndpoint s I.birth < sampledEndpoint s I.death := by
    by_contra hn
    simp [restrictAlong, hn] at h
  have hJ : J = ⟨sampledEndpoint s I.birth, sampledEndpoint s I.death,
      hlt, sampledEndpoint_le s I.death⟩ := by
    simpa [restrictAlong, hlt] using h.symm
  subst J
  simp only [alive]
  exact Iff.and (sampledEndpoint_le_val_iff s I.birth j)
    (lt_sampledEndpoint_iff s I.death j)

end FiniteInterval

/-- Apply interval restriction to every occurrence, retaining multiplicity. -/
def reindexBarcode (s : Fin N →o Fin L)
    (B : Multiset (FiniteInterval L)) : Multiset (FiniteInterval N) :=
  Multiset.filterMap (FiniteInterval.restrictAlong s) B

variable {k : Type u} [Field k]
variable (M : PModule.{u,0,u} k (Fin L))
variable [∀ i : Fin L, FiniteDimensional k (M.obj i)]

private instance reindex_finiteDimensional (s : Fin N →o Fin L) (i : Fin N) :
    FiniteDimensional k ((reindex s M).obj i) := by
  change FiniteDimensional k (M.obj (s i))
  infer_instance

/-- The sampled structure map has the rank of the actual source map at its sampled endpoints. -/
theorem structureMapRank_reindex (s : Fin N →o Fin L)
    (i j : Fin N) (hij : i ≤ j) :
    structureMapRank (reindex s M) i j hij =
      structureMapRank M (s i) (s j) (s.monotone' hij) := by
  unfold structureMapRank
  rw [structureMapLinear_reindex]
  rfl

private theorem rankInteger_reindex_nat (s : Fin N →o Fin L)
    (i j : ℕ) (hij : i ≤ j) (hj : j < N) :
    moduleRankInteger (reindex s M) (i : ℤ) (j : ℤ) =
      moduleRankInteger M ((s ⟨i, by omega⟩).val : ℤ)
        ((s ⟨j, hj⟩).val : ℤ) := by
  let fi : Fin N := ⟨i, by omega⟩
  let fj : Fin N := ⟨j, hj⟩
  have hfin : fi ≤ fj := Fin.le_iff_val_le_val.mpr hij
  have hs : s fi ≤ s fj := s.monotone' hfin
  have hleft := moduleRankInteger_fin (reindex s M) fi fj hfin
  have hright := moduleRankInteger_fin M (s fi) (s fj) hs
  rw [hleft, hright]
  exact_mod_cast structureMapRank_reindex M s fi fj hfin

private theorem multiplicity_reindex_four_ranks (s : Fin N →o Fin L)
    (b d : ℕ) (hbd : b < d) (hd : d ≤ N) :
    moduleMultiplicityInteger (reindex s M) b d =
      let A := if b = 0 then 0 else (s ⟨b - 1, by omega⟩).val + 1
      let B := (s ⟨b, by omega⟩).val
      let C := (s ⟨d - 1, by omega⟩).val
      let D := if hdN : d < N then (s ⟨d, hdN⟩).val else L
      moduleRankInteger M (B : ℤ) (C : ℤ) -
        moduleRankInteger M ((A : ℤ) - 1) (C : ℤ) -
        moduleRankInteger M (B : ℤ) (D : ℤ) +
        moduleRankInteger M ((A : ℤ) - 1) (D : ℤ) := by
  let A : ℕ := if b = 0 then 0 else (s ⟨b - 1, by omega⟩).val + 1
  let B : ℕ := (s ⟨b, by omega⟩).val
  let C : ℕ := (s ⟨d - 1, by omega⟩).val
  let D : ℕ := if hdN : d < N then (s ⟨d, hdN⟩).val else L
  have hc : ((d - 1 : ℕ) : ℤ) = (d : ℤ) - 1 := by omega
  have hBC : moduleRankInteger (reindex s M) (b : ℤ) ((d : ℤ) - 1) =
      moduleRankInteger M (B : ℤ) (C : ℤ) := by
    rw [← hc]
    simpa [B, C] using rankInteger_reindex_nat M s b (d - 1) (by omega) (by omega)
  have hAC : moduleRankInteger (reindex s M) ((b : ℤ) - 1) ((d : ℤ) - 1) =
      moduleRankInteger M ((A : ℤ) - 1) (C : ℤ) := by
    by_cases hb : b = 0
    · subst b
      simp only [Nat.cast_zero, zero_sub, A, if_pos rfl]
      rw [moduleRankInteger_neg_one, moduleRankInteger_neg_one]
    · have ha : ((b - 1 : ℕ) : ℤ) = (b : ℤ) - 1 := by omega
      have ha' : ((A : ℤ) - 1) = ((s ⟨b - 1, by omega⟩).val : ℤ) := by
        simp [A, hb]
      rw [← ha, ← hc, ha']
      simpa [C] using rankInteger_reindex_nat M s (b - 1) (d - 1)
        (by omega) (by omega)
  have hBD : moduleRankInteger (reindex s M) (b : ℤ) (d : ℤ) =
      moduleRankInteger M (B : ℤ) (D : ℤ) := by
    by_cases hdN : d < N
    · simpa [B, D, hdN] using rankInteger_reindex_nat M s b d (by omega) hdN
    · have hdeq : d = N := by omega
      have ht := moduleRankInteger_at_size (reindex s M) (b : ℤ)
      have hs := moduleRankInteger_at_size M (B : ℤ)
      simpa [D, hdN, hdeq] using ht.trans hs.symm
  have hAD : moduleRankInteger (reindex s M) ((b : ℤ) - 1) (d : ℤ) =
      moduleRankInteger M ((A : ℤ) - 1) (D : ℤ) := by
    by_cases hb : b = 0
    · subst b
      simp only [Nat.cast_zero, zero_sub, A, if_pos rfl]
      rw [moduleRankInteger_neg_one, moduleRankInteger_neg_one]
    · have ha : ((b - 1 : ℕ) : ℤ) = (b : ℤ) - 1 := by omega
      have ha' : ((A : ℤ) - 1) = ((s ⟨b - 1, by omega⟩).val : ℤ) := by
        simp [A, hb]
      by_cases hdN : d < N
      · rw [← ha, ha']
        simpa [D, hdN] using rankInteger_reindex_nat M s (b - 1) d
          (by omega) hdN
      · have hdeq : d = N := by omega
        have ht := moduleRankInteger_at_size (reindex s M) ((b : ℤ) - 1)
        have hs := moduleRankInteger_at_size M ((A : ℤ) - 1)
        simpa [D, hdN, hdeq] using ht.trans hs.symm
  change moduleMultiplicityInteger (reindex s M) b d =
    moduleRankInteger M (B : ℤ) (C : ℤ) -
      moduleRankInteger M ((A : ℤ) - 1) (C : ℤ) -
      moduleRankInteger M (B : ℤ) (D : ℤ) +
      moduleRankInteger M ((A : ℤ) - 1) (D : ℤ)
  unfold moduleMultiplicityInteger
  rw [hBC, hAC, hBD, hAD]

/-- A sampled integer multiplicity is the source multiplicity sum over its endpoint rectangle.
Repeated adjacent samples can make a birth or death range empty. The outer boundaries
use birth zero and source death `L`, with the existing integer rank sentinels. -/
theorem moduleMultiplicityInteger_reindex (s : Fin N →o Fin L)
    (b d : ℕ) (hbd : b < d) (hd : d ≤ N) :
    moduleMultiplicityInteger (reindex s M) b d =
      let A := if b = 0 then 0 else (s ⟨b - 1, by omega⟩).val + 1
      let B := (s ⟨b, by omega⟩).val
      let C := (s ⟨d - 1, by omega⟩).val
      let D := if hdN : d < N then (s ⟨d, hdN⟩).val else L
      ∑ x ∈ Finset.Icc A B, ∑ y ∈ Finset.Ioc C D,
        moduleMultiplicityInteger M x y := by
  let A : ℕ := if b = 0 then 0 else (s ⟨b - 1, by omega⟩).val + 1
  let B : ℕ := (s ⟨b, by omega⟩).val
  let C : ℕ := (s ⟨d - 1, by omega⟩).val
  let D : ℕ := if hdN : d < N then (s ⟨d, hdN⟩).val else L
  have hfour := multiplicity_reindex_four_ranks M s b d hbd hd
  change moduleMultiplicityInteger (reindex s M) b d =
    ∑ x ∈ Finset.Icc A B, ∑ y ∈ Finset.Ioc C D,
      moduleMultiplicityInteger M x y
  change moduleMultiplicityInteger (reindex s M) b d =
    moduleRankInteger M (B : ℤ) (C : ℤ) -
      moduleRankInteger M ((A : ℤ) - 1) (C : ℤ) -
      moduleRankInteger M (B : ℤ) (D : ℤ) +
      moduleRankInteger M ((A : ℤ) - 1) (D : ℤ) at hfour
  by_cases hAB : A ≤ B
  · have hBC : B ≤ C := by
      change (s ⟨b, by omega⟩).val ≤ (s ⟨d - 1, by omega⟩).val
      exact Fin.le_iff_val_le_val.mp
        (s.monotone' (Fin.le_iff_val_le_val.mpr (by change b ≤ d - 1; omega)))
    have hCD : C ≤ D := by
      by_cases hdN : d < N
      · have hle : (⟨d - 1, by omega⟩ : Fin N) ≤ ⟨d, hdN⟩ :=
          Fin.le_iff_val_le_val.mpr (by change d - 1 ≤ d; omega)
        simpa [C, D, hdN] using Fin.le_iff_val_le_val.mp (s.monotone' hle)
      · simp [C, D, hdN]
    have hDL : D ≤ L := by
      by_cases hdN : d < N
      · simp [D, hdN]
      · simp [D, hdN]
    exact hfour.trans
      (moduleMultiplicityInteger_sum_rectangle M A B C D hAB hBC hCD hDL).symm
  · have hb : b ≠ 0 := by
      intro hzero
      subst b
      have hAzero : A = 0 := rfl
      omega
    have hprev : (s ⟨b - 1, by omega⟩).val ≤ B := by
      change (s ⟨b - 1, by omega⟩).val ≤ (s ⟨b, by omega⟩).val
      exact Fin.le_iff_val_le_val.mp
        (s.monotone' (Fin.le_iff_val_le_val.mpr (by change b - 1 ≤ b; omega)))
    have heq : ((A : ℤ) - 1) = (B : ℤ) := by
      have hA : A = (s ⟨b - 1, by omega⟩).val + 1 := by simp [A, hb]
      omega
    have hempty : Finset.Icc A B = ∅ := Finset.Icc_eq_empty_of_lt (by omega)
    rw [hfour, heq, hempty]
    simp

private theorem countP_filterMap {α β : Type*} (f : α → Option β)
    (B : Multiset α) (p : β → Prop) [DecidablePred p]
    [DecidablePred (fun a : α => ∃ b, f a = some b ∧ p b)] :
    (Multiset.filterMap f B).countP p =
      B.countP (fun a => ∃ b, f a = some b ∧ p b) := by
  classical
  induction B using Multiset.induction_on with
  | empty => simp
  | @cons a B ih =>
    cases h : f a with
    | none => simpa [Multiset.filterMap_cons_none a B h, h] using ih
    | some b =>
      rw [Multiset.filterMap_cons_some f a B h,
        Multiset.countP_cons, Multiset.countP_cons, ih]
      have hp : (∃ c, f a = some c ∧ p c) ↔ p b := by simp [h]
      simp only [hp]

private theorem countP_reindexBarcode (s : Fin N →o Fin L)
    (B : Multiset (FiniteInterval L)) (i j : Fin N) (hij : i ≤ j) :
    (reindexBarcode s B).countP
        (fun J => J.birth ≤ i.val ∧ j.val < J.death) =
      B.countP (fun I => I.birth ≤ (s i).val ∧ (s j).val < I.death) := by
  classical
  rw [reindexBarcode, countP_filterMap]
  apply Multiset.countP_congr (s := B) (s' := B) rfl
  intro I _
  apply propext
  constructor
  · rintro ⟨J, hJ, hp⟩
    have hAliveJ := (interval_alive_endpoints_iff J hij).2 hp
    have hAliveI : I.alive (s i) ∧ I.alive (s j) :=
      ⟨(FiniteInterval.alive_restrictAlong s I J hJ i).1 hAliveJ.1,
        (FiniteInterval.alive_restrictAlong s I J hJ j).1 hAliveJ.2⟩
    exact (interval_alive_endpoints_iff I (s.monotone' hij)).1 hAliveI
  · intro hp
    have hAliveI : I.alive (s i) ∧ I.alive (s j) :=
      (interval_alive_endpoints_iff I (s.monotone' hij)).2 hp
    cases hres : I.restrictAlong s with
    | none =>
      exact False.elim ((FiniteInterval.restrictAlong_eq_none_iff s I).1 hres i hAliveI.1)
    | some J =>
      refine ⟨J, rfl, ?_⟩
      apply (interval_alive_endpoints_iff J hij).1
      exact ⟨(FiniteInterval.alive_restrictAlong s I J hres i).2 hAliveI.1,
        (FiniteInterval.alive_restrictAlong s I J hres j).2 hAliveI.2⟩

/-- The canonical rank barcode of a sampled module restricts every source barcode occurrence
and discards exactly the empty restrictions. This equality requires no interval decomposition. -/
theorem rankBarcode_reindex (s : Fin N →o Fin L) :
    rankBarcode (reindex s M) = reindexBarcode s (rankBarcode M) := by
  have hr : ∀ (i j : Fin N) (hij : i ≤ j),
      structureMapRank (reindex s M) i j hij =
        structureMapRank
          (barcodeModule (k := k) (reindexBarcode s (rankBarcode M))) i j hij := by
    intro i j hij
    calc
      structureMapRank (reindex s M) i j hij =
          structureMapRank M (s i) (s j) (s.monotone' hij) :=
        structureMapRank_reindex M s i j hij
      _ = structureMapRank (barcodeModule (k := k) (rankBarcode M))
          (s i) (s j) (s.monotone' hij) :=
        (structureMapRank_rankBarcode M (s i) (s j) (s.monotone' hij)).symm
      _ = (rankBarcode M).countP
          (fun I => I.birth ≤ (s i).val ∧ (s j).val < I.death) :=
        rank_barcodeMap (k := k) (rankBarcode M) (s i) (s j) (s.monotone' hij)
      _ = (reindexBarcode s (rankBarcode M)).countP
          (fun J => J.birth ≤ i.val ∧ j.val < J.death) :=
        (countP_reindexBarcode s (rankBarcode M) i j hij).symm
      _ = structureMapRank
          (barcodeModule (k := k) (reindexBarcode s (rankBarcode M))) i j hij :=
        (rank_barcodeMap (k := k) (reindexBarcode s (rankBarcode M)) i j hij).symm
  have heq := (rankBarcode_eq_iff (reindex s M)
    (barcodeModule (k := k) (reindexBarcode s (rankBarcode M)))).2 hr
  exact heq.trans (rankBarcode_barcodeModule (k := k) (reindexBarcode s (rankBarcode M)))

/-- Sampled canonical barcode multiplicities are natural source multiplicity block sums.
The counts retain their natural values in every coefficient characteristic. -/
theorem barcodeMultiplicity_rankBarcode_reindex (s : Fin N →o Fin L)
    (b d : ℕ) (hbd : b < d) (hd : d ≤ N) :
    barcodeMultiplicity (rankBarcode (reindex s M)) b d =
      let A := if b = 0 then 0 else (s ⟨b - 1, by omega⟩).val + 1
      let B := (s ⟨b, by omega⟩).val
      let C := (s ⟨d - 1, by omega⟩).val
      let D := if hdN : d < N then (s ⟨d, hdN⟩).val else L
      ∑ x ∈ Finset.Icc A B, ∑ y ∈ Finset.Ioc C D,
        barcodeMultiplicity (rankBarcode M) x y := by
  let A : ℕ := if b = 0 then 0 else (s ⟨b - 1, by omega⟩).val + 1
  let B : ℕ := (s ⟨b, by omega⟩).val
  let C : ℕ := (s ⟨d - 1, by omega⟩).val
  let D : ℕ := if hdN : d < N then (s ⟨d, hdN⟩).val else L
  have hBC : B ≤ C := by
    change (s ⟨b, by omega⟩).val ≤ (s ⟨d - 1, by omega⟩).val
    exact Fin.le_iff_val_le_val.mp
      (s.monotone' (Fin.le_iff_val_le_val.mpr (by change b ≤ d - 1; omega)))
  have hD : D ≤ L := by
    by_cases hdN : d < N
    · simp [D, hdN]
    · simp [D, hdN]
  have hInt : (barcodeMultiplicity (rankBarcode (reindex s M)) b d : ℤ) =
      ∑ x ∈ Finset.Icc A B, ∑ y ∈ Finset.Ioc C D,
        (barcodeMultiplicity (rankBarcode M) x y : ℤ) := by
    rw [barcodeMultiplicity_rankBarcode (reindex s M) b d hbd hd,
      moduleMultiplicityInteger_reindex M s b d hbd hd]
    apply Finset.sum_congr rfl
    intro x hx
    apply Finset.sum_congr rfl
    intro y hy
    have hxy : x < y := by
      have hx' := Finset.mem_Icc.mp hx
      have hy' := Finset.mem_Ioc.mp hy
      omega
    have hyL : y ≤ L := (Finset.mem_Ioc.mp hy).2.trans hD
    exact (barcodeMultiplicity_rankBarcode M x y hxy hyL).symm
  change barcodeMultiplicity (rankBarcode (reindex s M)) b d =
    ∑ x ∈ Finset.Icc A B, ∑ y ∈ Finset.Ioc C D,
      barcodeMultiplicity (rankBarcode M) x y
  exact_mod_cast hInt

end TDA.Persistence
