import TDA.Mapper.Basic
import TDA.Reeb.CriticalValues
import TDA.Reeb.GraphPLHeight

/-!
# Uniform interval covers of the attained range

For a base point `a`, an interval length `r` and an overlap length `g`, the uniform family has
the open members `U_k = (a + k(r - g), a + k(r - g) + r)` for `k : ℕ` (`uniformInterval`), and
`uniformCover a r g n : Fin n → OpenInterval` keeps the first `n` of them. The count `n` is an
explicit argument; no floor or ceiling occurs.

* Every member has length `r`. For `g ≤ r` consecutive members meet in the interval
  `(a + (k + 1)(r - g), a + (k + 1)(r - g) + g)` of length `g` (`uniformInterval_inf_succ`).
* For `2g ≤ r`, members whose indices differ by at least two are disjoint
  (`uniformInterval_disjoint`); no sign condition on `r` is needed, since for `r ≤ 0` every
  member is empty. Hence every real number lies in at most two members
  (`uniformCover_card_le_two`), which gives `CoverMultiplicityAtMost f _ 2` for every continuous
  `f` (`coverMultiplicityAtMost_uniformCover`). For `3 ≤ n` and `g < r` this bound holds
  exactly when `2g ≤ r` (`uniformCover_card_le_two_iff`). At `2g = r` the middle members are
  not generic in the sense of Carrière–Oudot (CO16-v3 §2.4); the bound is proved directly and is
  not attributed to CO16-v3 Lemma 2.10.
* For `0 < g` and `0 < n`, the window `(a, a + n(r - g) + g)` lies in the union of the `n`
  members (`Ioo_subset_iUnion_uniformCover`), and for `0 < g ≤ r` it is that union
  (`iUnion_uniformCover`). The equality needs `g ≤ r`: for `r < g` and `n ≥ 2` later members lie
  to the left of `a`.
* Vertex height bounds `h v ∈ [m, M]` bound the graph-PL height `plHeight G h`
  (`range_plHeight_subset_Icc`), with no connectedness and no nonemptiness. Hence the uniform
  family covers the attained range when `a < m` and `M < a + n(r - g) + g`
  (`uniformCover_covers_range`), and for `0 < g < r` such an `n` exists
  (`exists_uniformCover_window`).

The family, its arithmetic and the coverage statements are elementary library results, not
attributed to a source. See `docs/math/mapper.md`.
-/

namespace TDA.Mapper

open Set
open TDA.Topology TDA.Reeb TDA.Reeb.OpenInterval
open TDA.Reeb.GraphPL TDA.Reeb.GraphRealization

noncomputable section

/-! ## Members -/

/-- The `k`-th member `(a + k(r - g), a + k(r - g) + r)` of the uniform family with base point
`a`, interval length `r` and overlap length `g`. -/
def uniformInterval (a r g : ℝ) (k : ℕ) : OpenInterval :=
  ioo (a + k * (r - g)) (a + k * (r - g) + r)

/-- The first `n` members of the uniform family, indexed by `Fin n`. -/
def uniformCover (a r g : ℝ) (n : ℕ) : Fin n → OpenInterval :=
  fun k => uniformInterval a r g k

@[simp] theorem coe_uniformInterval (a r g : ℝ) (k : ℕ) :
    (uniformInterval a r g k : Set ℝ) = Ioo (a + k * (r - g)) (a + k * (r - g) + r) := rfl

theorem mem_uniformInterval {a r g y : ℝ} {k : ℕ} :
    y ∈ uniformInterval a r g k ↔ a + k * (r - g) < y ∧ y < a + k * (r - g) + r := Iff.rfl

@[simp] theorem uniformCover_apply (a r g : ℝ) (n : ℕ) (k : Fin n) :
    uniformCover a r g n k = uniformInterval a r g k := rfl

/-! ## Overlaps -/

/-- For `g ≤ r`, consecutive members meet in an interval of length `g`. -/
theorem uniformInterval_inf_succ {a r g : ℝ} (hgr : g ≤ r) (k : ℕ) :
    uniformInterval a r g k ⊓ uniformInterval a r g (k + 1) =
      ioo (a + (k + 1) * (r - g)) (a + (k + 1) * (r - g) + g) := by
  apply SetLike.coe_injective
  ext y
  simp only [coe_inf, coe_uniformInterval, coe_ioo, mem_inter_iff, mem_Ioo, Nat.cast_add,
    Nat.cast_one]
  constructor
  · rintro ⟨⟨-, h₂⟩, h₃, -⟩
    constructor <;> linarith
  · rintro ⟨h₁, h₂⟩
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith

/-- For `2g ≤ r`, members whose indices differ by at least two are disjoint. No sign condition
on `r` is needed: for `r ≤ 0` every member is empty. -/
theorem uniformInterval_disjoint {a r g : ℝ} (hg : 2 * g ≤ r) {k l : ℕ}
    (hkl : k + 2 ≤ l) :
    Disjoint (uniformInterval a r g k : Set ℝ) (uniformInterval a r g l) := by
  refine Set.disjoint_left.2 fun y h₁ h₂ => ?_
  rw [coe_uniformInterval, mem_Ioo] at h₁ h₂
  have hkl' : (k : ℝ) + 2 ≤ l := by exact_mod_cast hkl
  have hd : 0 ≤ r - g := by linarith [h₁.1, h₁.2]
  have := mul_le_mul_of_nonneg_right hkl' hd
  linarith [h₁.2, h₂.1]

/-- The disjointness of far members as a meet of open intervals. -/
theorem uniformInterval_inf_eq_bot {a r g : ℝ} (hg : 2 * g ≤ r) {k l : ℕ}
    (hkl : k + 2 ≤ l) : uniformInterval a r g k ⊓ uniformInterval a r g l = ⊥ := by
  apply SetLike.coe_injective
  rw [coe_inf, coe_bot]
  exact (uniformInterval_disjoint hg hkl).inter_eq

/-! ## The window -/

/-- A point of `(a, a + (n + 1)(r - g) + g)` lies in one of the members with index at most `n`;
induction on `n`, without floor. -/
private theorem exists_uniformInterval_of_mem {a r g : ℝ} (hg : 0 < g) :
    ∀ (n : ℕ) (y : ℝ), a < y → y < a + ((n : ℝ) + 1) * (r - g) + g →
      ∃ k ≤ n, y ∈ uniformInterval a r g k
  | 0, y, h₁, h₂ => ⟨0, le_rfl, by
      rw [mem_uniformInterval]
      simp only [Nat.cast_zero, zero_add, zero_mul, add_zero, one_mul] at h₂ ⊢
      constructor <;> linarith⟩
  | n + 1, y, h₁, h₂ => by
      by_cases hy : y < a + ((n : ℝ) + 1) * (r - g) + g
      · obtain ⟨k, hk, hmem⟩ := exists_uniformInterval_of_mem hg n y h₁ hy
        exact ⟨k, Nat.le_succ_of_le hk, hmem⟩
      · refine ⟨n + 1, le_rfl, ?_⟩
        rw [mem_uniformInterval]
        push_cast at h₂ ⊢
        have hy' := not_lt.1 hy
        constructor <;> linarith

/-- For `0 < g` and `0 < n`, the window `(a, a + n(r - g) + g)` lies in the union of the
members. No relation between `g` and `r` is needed. -/
theorem Ioo_subset_iUnion_uniformCover {a r g : ℝ} {n : ℕ} (hg : 0 < g) (hn : 0 < n) :
    Set.Ioo a (a + n * (r - g) + g) ⊆ ⋃ k : Fin n, (uniformCover a r g n k : Set ℝ) := by
  intro y hy
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  obtain ⟨k, hk, hmem⟩ := exists_uniformInterval_of_mem hg m y hy.1 (by
    have := hy.2
    push_cast at this
    exact this)
  exact Set.mem_iUnion.2 ⟨⟨k, Nat.lt_succ_of_le hk⟩, hmem⟩

/-- For `0 < g ≤ r` and `0 < n`, the union of the `n` members is the window
`(a, a + n(r - g) + g)`. -/
theorem iUnion_uniformCover {a r g : ℝ} {n : ℕ} (hg : 0 < g) (hgr : g ≤ r) (hn : 0 < n) :
    ⋃ k : Fin n, (uniformCover a r g n k : Set ℝ) = Set.Ioo a (a + n * (r - g) + g) := by
  refine Subset.antisymm ?_ (Ioo_subset_iUnion_uniformCover hg hn)
  intro y hy
  obtain ⟨k, hk⟩ := Set.mem_iUnion.1 hy
  rw [uniformCover_apply, coe_uniformInterval, mem_Ioo] at hk
  have hk0 : (0 : ℝ) ≤ (k : ℕ) := Nat.cast_nonneg _
  have hkn : ((k : ℕ) : ℝ) + 1 ≤ n := by exact_mod_cast Nat.succ_le_of_lt k.2
  have hd : 0 ≤ r - g := sub_nonneg.2 hgr
  have h₁ := mul_nonneg hk0 hd
  have h₂ := mul_le_mul_of_nonneg_right hkn hd
  constructor <;> linarith [hk.1, hk.2]

/-! ## The attained range of a graph-PL height -/

/-- Vertex height bounds bound the graph-PL height at every point of the realization. -/
theorem plHeight_mem_Icc_of_forall {V : Type*} {G : SimpleGraph V} {h : V → ℝ} {m M : ℝ}
    (hh : ∀ v, h v ∈ Set.Icc m M) (p : Realization G) : plHeight G h p ∈ Set.Icc m M := by
  induction p using ind G with
  | vertex v => exact hh v
  | edgePoint d t =>
      have hf := hh d.fst
      have hs := hh d.snd
      have ht0 : (0 : ℝ) ≤ t := t.2.1
      have ht1 : (t : ℝ) ≤ 1 := t.2.2
      change m ≤ (1 - (t : ℝ)) * h d.fst + (t : ℝ) * h d.snd ∧
        (1 - (t : ℝ)) * h d.fst + (t : ℝ) * h d.snd ≤ M
      constructor
      · nlinarith [mul_nonneg (sub_nonneg.2 ht1) (sub_nonneg.2 hf.1),
          mul_nonneg ht0 (sub_nonneg.2 hs.1)]
      · nlinarith [mul_nonneg (sub_nonneg.2 ht1) (sub_nonneg.2 hf.2),
          mul_nonneg ht0 (sub_nonneg.2 hs.2)]

/-- Vertex height bounds bound the attained range of the graph-PL height. No connectedness of
`G` and no nonemptiness of `V` is assumed. -/
theorem range_plHeight_subset_Icc {V : Type*} {G : SimpleGraph V} {h : V → ℝ} {m M : ℝ}
    (hh : ∀ v, h v ∈ Set.Icc m M) : Set.range (plHeight G h) ⊆ Set.Icc m M := by
  rintro _ ⟨p, rfl⟩
  exact plHeight_mem_Icc_of_forall hh p

/-- The uniform family covers the attained range of a graph-PL height whose vertex heights lie
in `[m, M]`, as soon as the window `(a, a + n(r - g) + g)` contains `[m, M]`. -/
theorem uniformCover_covers_range {V : Type*} {G : SimpleGraph V} {h : V → ℝ}
    {a r g m M : ℝ} {n : ℕ} (hh : ∀ v, h v ∈ Set.Icc m M) (ha : a < m)
    (hM : M < a + n * (r - g) + g) (hg : 0 < g) (hn : 0 < n) :
    Covers (fun k => (uniformCover a r g n k : Set ℝ)) (Set.range (plHeight G h)) := by
  intro y hy
  have hIcc := range_plHeight_subset_Icc hh hy
  exact Set.mem_iUnion.1 (Ioo_subset_iUnion_uniformCover hg hn
    ⟨by linarith [hIcc.1], by linarith [hIcc.2]⟩)

/-- For `0 < g < r`, some positive count `n` makes the window reach beyond any given `M`. -/
theorem exists_uniformCover_window {r g : ℝ} (hg : 0 < g) (hgr : g < r) (a M : ℝ) :
    ∃ n : ℕ, 0 < n ∧ M < a + n * (r - g) + g := by
  have hd : 0 < r - g := sub_pos.2 hgr
  obtain ⟨n, hn⟩ := exists_nat_gt ((M - a) / (r - g))
  rw [div_lt_iff₀ hd] at hn
  refine ⟨n + 1, Nat.succ_pos n, ?_⟩
  push_cast
  linarith

/-! ## Multiplicity -/

/-- For `2g ≤ r`, every real number lies in at most two members. -/
theorem uniformCover_card_le_two {a r g : ℝ} {n : ℕ} (hg : 2 * g ≤ r) :
    ∀ y (t : Finset (Fin n)), (∀ k ∈ t, y ∈ uniformCover a r g n k) → t.card ≤ 2 := by
  intro y t ht
  by_contra hcard
  obtain ⟨i, hi, j, hj, k, hk, hij, hik, hjk⟩ := Finset.two_lt_card.1 (not_le.1 hcard)
  have far : ∀ p q : Fin n, p ∈ t → q ∈ t → (p : ℕ) + 2 ≤ q → False := fun p q hp hq hpq =>
    Set.disjoint_left.1 (uniformInterval_disjoint (a := a) hg hpq) (ht p hp) (ht q hq)
  have hij' : (i : ℕ) ≠ j := fun h => hij (Fin.ext h)
  have hik' : (i : ℕ) ≠ k := fun h => hik (Fin.ext h)
  have hjk' : (j : ℕ) ≠ k := fun h => hjk (Fin.ext h)
  have : (i : ℕ) + 2 ≤ j ∨ (j : ℕ) + 2 ≤ i ∨ (i : ℕ) + 2 ≤ k ∨ (k : ℕ) + 2 ≤ i ∨
      (j : ℕ) + 2 ≤ k ∨ (k : ℕ) + 2 ≤ j := by omega
  rcases this with h | h | h | h | h | h
  · exact far i j hi hj h
  · exact far j i hj hi h
  · exact far i k hi hk h
  · exact far k i hk hi h
  · exact far j k hj hk h
  · exact far k j hk hj h

/-- For `2g ≤ r`, the uniform family has multiplicity at most two for every continuous map. -/
theorem coverMultiplicityAtMost_uniformCover {X : Type*} [TopologicalSpace X] {a r g : ℝ}
    {n : ℕ} (hg : 2 * g ≤ r) (f : C(X, ℝ)) :
    CoverMultiplicityAtMost f (fun k => (uniformCover a r g n k : Set ℝ)) 2 :=
  fun y _ t ht => uniformCover_card_le_two hg y t ht

/-- For `3 ≤ n` and `g < r`, every real number lies in at most two members exactly when
`2g ≤ r`. If `r < 2g`, the midpoint of `(a + 2(r - g), a + r)` lies in the first three members.
The case `0 < g < r` of the specification is included; `0 < g` follows from `g < r < 2g`. -/
theorem uniformCover_card_le_two_iff {a r g : ℝ} {n : ℕ} (hn : 3 ≤ n) (hgr : g < r) :
    (∀ y (t : Finset (Fin n)), (∀ k ∈ t, y ∈ uniformCover a r g n k) → t.card ≤ 2) ↔
      2 * g ≤ r := by
  refine ⟨fun h => ?_, fun h => uniformCover_card_le_two h⟩
  by_contra hlt'
  have hlt := not_le.1 hlt'
  let k₀ : Fin n := ⟨0, by omega⟩
  let k₁ : Fin n := ⟨1, by omega⟩
  let k₂ : Fin n := ⟨2, by omega⟩
  have hmem : ∀ k ∈ ({k₀, k₁, k₂} : Finset (Fin n)),
      (a + 2 * (r - g) + (a + r)) / 2 ∈ uniformCover a r g n k := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl <;>
      simp only [uniformCover_apply, mem_uniformInterval, k₀, k₁, k₂, Nat.cast_zero,
        Nat.cast_one, Nat.cast_ofNat] <;>
      constructor <;> linarith
  have hcard : ({k₀, k₁, k₂} : Finset (Fin n)).card = 3 :=
    Finset.card_eq_three.2 ⟨k₀, k₁, k₂, Fin.ne_of_val_ne (by norm_num),
      Fin.ne_of_val_ne (by norm_num), Fin.ne_of_val_ne (by norm_num), rfl⟩
  have := h _ _ hmem
  omega

end

end TDA.Mapper
