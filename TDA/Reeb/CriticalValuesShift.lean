import TDA.Reeb.CriticalValues
import Mathlib.Data.Finset.Sort

/-!
# Shifted critical levels

For `S : CriticalValues n` with levels `a 0 < ⋯ < a n` and `ε : ℝ≥0`, the shifted levels
`a i - ε` and `a i + ε` form a finite critical set for the `ε`-smoothing of a precosheaf that is
constructible at `S` (de Silva–Munch–Patel, Proposition 4.19).

* Shifted set. `S.shiftedSet ε : Finset ℝ` is the union of the images of `a i ↦ a i - ε` and
  `a i ↦ a i + ε`, so coinciding shifts are merged (`mem_shiftedSet`). It is nonempty
  (`shiftedSet_nonempty`), with least element `a 0 - ε` (`min'_shiftedSet`) and greatest element
  `a n + ε` (`max'_shiftedSet`).
* Shifted witness. `S.shiftedCount ε` is the cardinality of the shifted set minus one
  (`card_shiftedSet`), and `S.shifted ε : CriticalValues (S.shiftedCount ε)` lists the shifted set
  in increasing order through `Finset.orderEmbOfFin`. Its levels are exactly the shifted set
  (`range_shifted`, `mem_range_shifted_iff`); the first level is `a 0 - ε`
  (`shifted_value_zero`) and the last is `a n + ε` (`shifted_value_last`). The witness is not
  claimed minimal, and its length is only bounded: there are at most `2 (n + 1)` levels
  (`shiftedCount_le`). Shifts of different levels may coincide, so the length is not determined
  by `n`.
* `ε = 0`. The shifted set is the set of levels (`shiftedSet_zero`), the count is `n`
  (`shiftedCount_zero`) and the ranges agree (`range_shifted_zero`). These equalities are
  propositional; `S.shifted 0` is not identified with `S`.
* Key interval lemma. For open intervals `I ≤ J` with `I` nonempty, if each of `a - ε` and
  `a + ε` lies in `I` exactly when it lies in `J`, then `a` lies in `thicken ε I` exactly when it
  lies in `thicken ε J` (`OpenInterval.mem_thicken_iff_of_sub_add`). Hence intervals meeting the
  same shifted levels have thickenings meeting the same levels of `S`
  (`value_mem_thicken_iff_of_shifted`). The nonemptiness of `I` is necessary: `⊥` and `(-1, 1)`
  meet no shifted level of `{0}` at `ε = 1`, while `thicken 1 (-1, 1) = (-2, 2)` contains `0`.

See `docs/math/reeb-constructible-smoothing.md`.
-/

open Set
open scoped NNReal

namespace TDA.Reeb

noncomputable section

open OpenInterval

namespace OpenInterval

/-- Key interval step (DMP Proposition 4.19 with a nonempty source). Let `I ≤ J` with `I`
nonempty, and let each of `a - ε` and `a + ε` lie in `I` exactly when it lies in `J`. Then `a`
lies in the `ε`-thickening of `I` exactly when it lies in that of `J`. -/
theorem mem_thicken_iff_of_sub_add {I J : OpenInterval} (hIJ : I ≤ J)
    (hI : (I : Set ℝ).Nonempty) {ε : ℝ≥0} {a : ℝ} (hsub : a - ε ∈ I ↔ a - ε ∈ J)
    (hadd : a + ε ∈ I ↔ a + ε ∈ J) : a ∈ thicken ε I ↔ a ∈ thicken ε J := by
  refine ⟨fun h => thicken_mono hIJ h, fun hJ => ?_⟩
  by_contra hnot
  have hfar : ∀ y ∈ I, ¬ (-(ε : ℝ) ≤ a - y ∧ a - y ≤ ε) := fun y hy h =>
    hnot (mem_thicken.2 ⟨y, hy, abs_le.2 h⟩)
  obtain ⟨x, hx⟩ := hI
  obtain ⟨y, hyJ, hy⟩ := mem_thicken.1 hJ
  rw [abs_le] at hy
  rcases lt_or_ge x (a - ε) with hxa | hxa
  · -- `x < a - ε ≤ y`, so `a - ε ∈ J`; but `a - ε` is within `ε` of `a`, so not in `I`
    have hJ' : a - ε ∈ J := mem_of_le_of_le (hIJ hx) hyJ hxa.le (by linarith [hy.2])
    exact hfar _ (hsub.2 hJ') ⟨by linarith [ε.coe_nonneg], by linarith⟩
  rcases lt_or_ge (a + ε) x with hxb | hxb
  · -- `y ≤ a + ε < x`, so `a + ε ∈ J`; but `a + ε` is within `ε` of `a`, so not in `I`
    have hJ' : a + ε ∈ J := mem_of_le_of_le hyJ (hIJ hx) (by linarith [hy.1]) hxb.le
    exact hfar _ (hadd.2 hJ') ⟨by linarith, by linarith [ε.coe_nonneg]⟩
  · exact hfar x hx ⟨by linarith, by linarith⟩

end OpenInterval

namespace CriticalValues

variable {n : ℕ} (S : CriticalValues n) (ε : ℝ≥0)

/-- The shifted finite set `(S - ε) ∪ (S + ε)` of DMP Proposition 4.19, collisions merged. -/
def shiftedSet : Finset ℝ :=
  Finset.univ.image (fun i => S.value i - ε) ∪ Finset.univ.image (fun i => S.value i + ε)

theorem mem_shiftedSet {x : ℝ} :
    x ∈ S.shiftedSet ε ↔ ∃ i, x = S.value i - ε ∨ x = S.value i + ε := by
  simp only [shiftedSet, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro (⟨i, rfl⟩ | ⟨i, rfl⟩)
    exacts [⟨i, Or.inl rfl⟩, ⟨i, Or.inr rfl⟩]
  · rintro ⟨i, rfl | rfl⟩
    exacts [Or.inl ⟨i, rfl⟩, Or.inr ⟨i, rfl⟩]

theorem sub_mem_shiftedSet (i : Fin (n + 1)) : S.value i - ε ∈ S.shiftedSet ε :=
  (S.mem_shiftedSet ε).2 ⟨i, Or.inl rfl⟩

theorem add_mem_shiftedSet (i : Fin (n + 1)) : S.value i + ε ∈ S.shiftedSet ε :=
  (S.mem_shiftedSet ε).2 ⟨i, Or.inr rfl⟩

/-- The shifted set is nonempty: it contains `S.value 0 - ε`. -/
theorem shiftedSet_nonempty : (S.shiftedSet ε).Nonempty := ⟨_, S.sub_mem_shiftedSet ε 0⟩

/-- The number of internal gaps of the shifted witness: one less than the number of distinct
shifted levels. -/
def shiftedCount : ℕ := (S.shiftedSet ε).card - 1

theorem card_shiftedSet : (S.shiftedSet ε).card = S.shiftedCount ε + 1 := by
  have := (S.shiftedSet_nonempty ε).card_pos
  unfold shiftedCount
  omega

/-- The shifted witness: the shifted set sorted increasingly by `Finset.orderEmbOfFin`, with
collisions merged. It is a witness, not a minimal critical set. -/
def shifted : CriticalValues (S.shiftedCount ε) where
  value := (S.shiftedSet ε).orderEmbOfFin (S.card_shiftedSet ε)
  strictMono := ((S.shiftedSet ε).orderEmbOfFin (S.card_shiftedSet ε)).strictMono

theorem shifted_value :
    (S.shifted ε).value = (S.shiftedSet ε).orderEmbOfFin (S.card_shiftedSet ε) := rfl

/-- Exact range: the levels of the shifted witness are exactly the shifted set. -/
theorem range_shifted : Set.range (S.shifted ε).value = ↑(S.shiftedSet ε) :=
  Finset.range_orderEmbOfFin _ _

theorem mem_range_shifted_iff {x : ℝ} :
    x ∈ Set.range (S.shifted ε).value ↔ ∃ i, x = S.value i - ε ∨ x = S.value i + ε := by
  rw [range_shifted, Finset.mem_coe, mem_shiftedSet]

theorem exists_shifted_value_eq_sub (i : Fin (n + 1)) :
    ∃ j, (S.shifted ε).value j = S.value i - ε :=
  (S.mem_range_shifted_iff ε).2 ⟨i, Or.inl rfl⟩

theorem exists_shifted_value_eq_add (i : Fin (n + 1)) :
    ∃ j, (S.shifted ε).value j = S.value i + ε :=
  (S.mem_range_shifted_iff ε).2 ⟨i, Or.inr rfl⟩

theorem min'_shiftedSet : (S.shiftedSet ε).min' (S.shiftedSet_nonempty ε) = S.value 0 - ε := by
  refine le_antisymm (Finset.min'_le _ _ (S.sub_mem_shiftedSet ε 0))
    (Finset.le_min' _ _ _ fun y hy => ?_)
  obtain ⟨i, rfl | rfl⟩ := (S.mem_shiftedSet ε).1 hy
  · linarith [S.strictMono.monotone (Fin.zero_le i)]
  · linarith [S.strictMono.monotone (Fin.zero_le i), ε.coe_nonneg]

theorem max'_shiftedSet :
    (S.shiftedSet ε).max' (S.shiftedSet_nonempty ε) = S.value (Fin.last n) + ε := by
  refine le_antisymm (Finset.max'_le _ _ _ fun y hy => ?_)
    (Finset.le_max' _ _ (S.add_mem_shiftedSet ε _))
  obtain ⟨i, rfl | rfl⟩ := (S.mem_shiftedSet ε).1 hy
  · linarith [S.strictMono.monotone (Fin.le_last i), ε.coe_nonneg]
  · linarith [S.strictMono.monotone (Fin.le_last i)]

/-- The first shifted level is `S.value 0 - ε`. -/
theorem shifted_value_zero : (S.shifted ε).value 0 = S.value 0 - ε :=
  (Finset.orderEmbOfFin_zero (S.card_shiftedSet ε) (Nat.succ_pos _)).trans (S.min'_shiftedSet ε)

/-- The last shifted level is `S.value (Fin.last n) + ε`. -/
theorem shifted_value_last : (S.shifted ε).value (Fin.last _) = S.value (Fin.last n) + ε := by
  have h := Finset.orderEmbOfFin_last (S.card_shiftedSet ε) (Nat.succ_pos _)
  rw [S.max'_shiftedSet ε] at h
  rw [← h, shifted_value]
  congr 1

/-- Length bound: at most `2 (n + 1)` levels. No exact length or minimality is claimed. -/
theorem shiftedCount_le : S.shiftedCount ε ≤ 2 * n + 1 := by
  have h₁ := Finset.card_union_le (Finset.univ.image fun i => S.value i - ε)
    (Finset.univ.image fun i => S.value i + ε)
  have h₂ := Finset.card_image_le (s := (Finset.univ : Finset (Fin (n + 1))))
    (f := fun i => S.value i - ε)
  have h₃ := Finset.card_image_le (s := (Finset.univ : Finset (Fin (n + 1))))
    (f := fun i => S.value i + ε)
  have h₄ := S.card_shiftedSet ε
  simp only [Finset.card_univ, Fintype.card_fin] at h₂ h₃
  unfold shiftedSet at h₄
  omega

/-- At `ε = 0` the two shifts of each level coincide and the shifted set is the set of levels. -/
theorem shiftedSet_zero : S.shiftedSet 0 = Finset.univ.image S.value := by
  ext x
  rw [mem_shiftedSet]
  simp only [NNReal.coe_zero, sub_zero, add_zero, or_self, Finset.mem_image, Finset.mem_univ,
    true_and]
  exact ⟨fun ⟨i, h⟩ => ⟨i, h.symm⟩, fun ⟨i, h⟩ => ⟨i, h.symm⟩⟩

theorem shiftedCount_zero : S.shiftedCount 0 = n := by
  unfold shiftedCount
  rw [shiftedSet_zero, Finset.card_image_of_injective _ S.strictMono.injective, Finset.card_univ,
    Fintype.card_fin]
  simp

theorem range_shifted_zero : Set.range (S.shifted 0).value = Set.range S.value := by
  rw [range_shifted, shiftedSet_zero, Finset.coe_image, Finset.coe_univ, Set.image_univ]

/-- Key interval lemma (DMP Proposition 4.19 with the nonempty-source correction). For `I ≤ J`
with `I` nonempty, meeting the same shifted levels, the thickenings `I^ε ≤ J^ε` meet the same
levels of `S`. -/
theorem value_mem_thicken_iff_of_shifted {I J : OpenInterval} (hIJ : I ≤ J)
    (hI : (I : Set ℝ).Nonempty)
    (hhit : ∀ j, (S.shifted ε).value j ∈ I ↔ (S.shifted ε).value j ∈ J) (i : Fin (n + 1)) :
    S.value i ∈ thicken ε I ↔ S.value i ∈ thicken ε J := by
  obtain ⟨j, hj⟩ := S.exists_shifted_value_eq_sub ε i
  obtain ⟨k, hk⟩ := S.exists_shifted_value_eq_add ε i
  refine mem_thicken_iff_of_sub_add hIJ hI ?_ ?_
  · rw [← hj]; exact hhit j
  · rw [← hk]; exact hhit k

end CriticalValues

end

end TDA.Reeb
