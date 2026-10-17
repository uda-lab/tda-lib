import TDA.Persistence.FinitePMatchingCost
import TDA.Persistence.FiniteMatchingCostLaws
import Mathlib.Analysis.MeanInequalities

/-!
# Distance laws of finite real-exponent matching costs

Rooted candidate costs satisfy a sharp composition inequality. Each matching's
charges are placed on a common finite index, without duplicating a middle
occurrence, before applying finite-sum Minkowski. Attained minima then satisfy
the triangle inequality. Positive lifetimes identify zero cost with a
value-preserving equivalence of occurrence labels, including multiplicities.
-/

noncomputable section
namespace TDA.Persistence
open scoped Classical

namespace OccurrenceMatching
variable {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]

private def finiteSourceCharge (M : OccurrenceMatching I J PEmpty.{1} PEmpty.{1})
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) (i : I) : ℝ :=
  match M.finite i with
  | some j => (finitePairCost (x i) (y j)).toReal
  | none => (diagonalCost (x i)).toReal

private def finiteTargetCharge (M : OccurrenceMatching I J PEmpty.{1} PEmpty.{1})
    (y : J → ℝ × ℝ) (j : J) : ℝ :=
  if ∃ i, M.finite i = some j then 0 else (diagonalCost (y j)).toReal

omit [Fintype I] [Fintype J] in
private theorem finiteSourceCharge_nonneg
    (M : OccurrenceMatching I J PEmpty.{1} PEmpty.{1})
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) (i : I) : 0 ≤ finiteSourceCharge M x y i := by
  unfold finiteSourceCharge
  cases M.finite i <;> exact ENNReal.toReal_nonneg

omit [Fintype J] in
private theorem finiteTargetCharge_nonneg
    (M : OccurrenceMatching I J PEmpty.{1} PEmpty.{1})
    (y : J → ℝ × ℝ) (j : J) : 0 ≤ finiteTargetCharge M y j := by
  unfold finiteTargetCharge
  split_ifs <;> first | exact le_rfl | exact ENNReal.toReal_nonneg

private theorem totalFinitePowerCost_eq_chargeSums
    (M : OccurrenceMatching I J PEmpty.{1} PEmpty.{1}) {p : ℝ} (hp : p ≠ 0)
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    M.totalFinitePowerCost p x y =
      (∑ i, finiteSourceCharge M x y i ^ p) + ∑ j, finiteTargetCharge M y j ^ p := by
  unfold totalFinitePowerCost totalBoundaryCost
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    cases h : M.finite i <;> simp only [finiteSourceCharge, h]
  · apply Finset.sum_congr rfl
    intro j _
    unfold finiteTargetCharge
    split_ifs <;> simp only [Real.zero_rpow hp]

private theorem totalFinitePowerCost_eq_symmetricSums
    (M : OccurrenceMatching I J PEmpty.{1} PEmpty.{1}) (p : ℝ)
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    M.totalFinitePowerCost p x y =
      (∑ i, ∑ j, if M.finite i = some j then (finitePairCost (x i) (y j)).toReal ^ p else 0) +
      (∑ i, if ∃ j, M.finite i = some j then 0 else (diagonalCost (x i)).toReal ^ p) +
      ∑ j, if ∃ i, M.finite i = some j then 0 else (diagonalCost (y j)).toReal ^ p := by
  have hs (i : I) :
      (match M.finite i with
        | some j => (finitePairCost (x i) (y j)).toReal ^ p
        | none => (diagonalCost (x i)).toReal ^ p) =
      (∑ j, if M.finite i = some j then (finitePairCost (x i) (y j)).toReal ^ p else 0) +
        (if ∃ j, M.finite i = some j then 0 else (diagonalCost (x i)).toReal ^ p) := by
    cases M.finite i <;> simp
  unfold totalFinitePowerCost totalBoundaryCost
  change (∑ i, match M.finite i with
    | some j => (finitePairCost (x i) (y j)).toReal ^ p
    | none => (diagonalCost (x i)).toReal ^ p) +
    (∑ j, if ∃ i, M.finite i = some j then 0 else (diagonalCost (y j)).toReal ^ p) = _
  simp_rw [hs]
  rw [Finset.sum_add_distrib]

/-- Reversal exchanges the two unmatched parts and preserves every powered pair charge. -/
theorem totalFinitePowerCost_reverse
    (M : OccurrenceMatching I J PEmpty.{1} PEmpty.{1}) (p : ℝ)
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    M.reverse.totalFinitePowerCost p y x = M.totalFinitePowerCost p x y := by
  rw [totalFinitePowerCost_eq_symmetricSums, totalFinitePowerCost_eq_symmetricSums]
  simp_rw [reverse_finite_some_iff, finitePairCost_comm (y _) (x _)]
  rw [Finset.sum_comm]
  abel

private theorem diagonal_toReal_le_pair_add (a b : ℝ × ℝ) :
    (diagonalCost a).toReal ≤ (finitePairCost a b).toReal + (diagonalCost b).toReal := by
  have h := ENNReal.toReal_mono
    (by simp [finitePairCost, diagonalCost]) (diagonalCost_le_pair_add a b)
  rw [ENNReal.toReal_add (show finitePairCost a b ≠ ⊤ by simp [finitePairCost])
    (show diagonalCost b ≠ ⊤ by simp [diagonalCost])] at h
  exact h

omit [Fintype I] [Fintype J] [Fintype K] in
private theorem sourcePathCharge_le
    (M : OccurrenceMatching I J PEmpty.{1} PEmpty.{1})
    (N : OccurrenceMatching J K PEmpty.{1} PEmpty.{1})
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) (z : K → ℝ × ℝ) (i : I) :
    finiteSourceCharge (M.compose N) x z i ≤ finiteSourceCharge M x y i +
      (match M.finite i with | some j => finiteSourceCharge N y z j | none => 0) := by
  cases hm : M.finite i with
  | none => simp [finiteSourceCharge, compose, hm]
  | some j =>
    cases hn : N.finite j with
    | none =>
      simpa [finiteSourceCharge, compose, hm, hn] using
        diagonal_toReal_le_pair_add (x i) (y j)
    | some k =>
      simpa [finiteSourceCharge, compose, hm, hn, finitePairCost_toReal, dist_eq_norm] using
        dist_triangle (x i) (y j) (z k)

private def targetPathCharge
    (M : OccurrenceMatching I J PEmpty.{1} PEmpty.{1})
    (N : OccurrenceMatching J K PEmpty.{1} PEmpty.{1}) (z : K → ℝ × ℝ) (j : J) : ℝ :=
  match N.finite j with
  | some k => finiteTargetCharge (M.compose N) z k
  | none => 0

omit [Fintype J] [Fintype K] in
private theorem targetPathCharge_nonneg
    (M : OccurrenceMatching I J PEmpty.{1} PEmpty.{1})
    (N : OccurrenceMatching J K PEmpty.{1} PEmpty.{1}) (z : K → ℝ × ℝ) (j : J) :
    0 ≤ targetPathCharge M N z j := by
  unfold targetPathCharge
  cases N.finite j
  · exact le_rfl
  · exact finiteTargetCharge_nonneg _ _ _

omit [Fintype J] [Fintype K] in
private theorem targetPathCharge_le
    (M : OccurrenceMatching I J PEmpty.{1} PEmpty.{1})
    (N : OccurrenceMatching J K PEmpty.{1} PEmpty.{1})
    (y : J → ℝ × ℝ) (z : K → ℝ × ℝ) (j : J) :
    targetPathCharge M N z j ≤ finiteTargetCharge M y j +
      (if ∃ i, M.finite i = some j then 0 else finiteSourceCharge N y z j) := by
  cases hn : N.finite j with
  | none =>
    simp only [targetPathCharge, hn]
    exact add_nonneg (finiteTargetCharge_nonneg M y j)
      (by split_ifs <;> first | exact le_rfl | exact finiteSourceCharge_nonneg N y z j)
  | some k =>
    by_cases hm : ∃ i, M.finite i = some j
    · obtain ⟨i, hi⟩ := hm
      have hc : ∃ i, (M.compose N).finite i = some k := ⟨i, by simp [compose, hi, hn]⟩
      simp [targetPathCharge, finiteTargetCharge, hn, hc,
        show ∃ i, M.finite i = some j from ⟨i, hi⟩]
    · have hdiag : (diagonalCost (z k)).toReal ≤
          (diagonalCost (y j)).toReal + (finitePairCost (y j) (z k)).toReal := by
        simpa only [finitePairCost_comm, add_comm] using
          diagonal_toReal_le_pair_add (z k) (y j)
      calc
        _ ≤ (diagonalCost (z k)).toReal := by
          simp only [targetPathCharge, hn]
          unfold finiteTargetCharge
          split_ifs <;> first | exact ENNReal.toReal_nonneg | exact le_rfl
        _ ≤ _ := by simpa [finiteTargetCharge, finiteSourceCharge, hm, hn] using hdiag

/-- Split the composed unmatched-target sum into paths through N and targets not selected by N. -/
private theorem sum_targetPath_powers
    (M : OccurrenceMatching I J PEmpty.{1} PEmpty.{1})
    (N : OccurrenceMatching J K PEmpty.{1} PEmpty.{1}) {p : ℝ} (hp : p ≠ 0)
    (z : K → ℝ × ℝ) :
    (∑ j, targetPathCharge M N z j ^ p) + ∑ k, finiteTargetCharge N z k ^ p =
      ∑ k, finiteTargetCharge (M.compose N) z k ^ p := by
  have hncomp (k : K) (hn : ¬ ∃ j, N.finite j = some k) :
      ¬ ∃ i, (M.compose N).finite i = some k := by
    rintro ⟨i, hi⟩
    cases hm : M.finite i with
    | none => simp [compose, hm] at hi
    | some j => exact hn ⟨j, by simpa [compose, hm] using hi⟩
  have hmap : (∑ j, targetPathCharge M N z j ^ p) =
      ∑ k, if ∃ j, N.finite j = some k then finiteTargetCharge (M.compose N) z k ^ p else 0 := by
    calc
      _ = ∑ j, match N.finite j with
          | some k => finiteTargetCharge (M.compose N) z k ^ p | none => 0 := by
        apply Finset.sum_congr rfl
        intro j _
        cases hn : N.finite j <;> simp [targetPathCharge, hn, Real.zero_rpow hp]
      _ = _ := N.sum_matched _
  rw [hmap, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hn : ∃ j, N.finite j = some k
  · simp [finiteTargetCharge, hn, Real.zero_rpow hp]
  · simp [finiteTargetCharge, hn, hncomp k hn]

/-- The selected and complementary middle charges partition N's source p-power sum. -/
private theorem sum_middle_powers
    (M : OccurrenceMatching I J PEmpty.{1} PEmpty.{1}) {p : ℝ} (hp : p ≠ 0)
    (f : J → ℝ) :
    (∑ i, (match M.finite i with | some j => f j | none => 0) ^ p) +
        (∑ j, (if ∃ i, M.finite i = some j then 0 else f j) ^ p) = ∑ j, f j ^ p := by
  have hmap : (∑ i, (match M.finite i with | some j => f j | none => 0) ^ p) =
      ∑ j, if ∃ i, M.finite i = some j then f j ^ p else 0 := by
    calc
      _ = ∑ i, match M.finite i with | some j => f j ^ p | none => 0 := by
        apply Finset.sum_congr rfl
        intro i _
        cases M.finite i <;> simp [Real.zero_rpow hp]
      _ = _ := M.sum_matched _
  rw [hmap, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp [Real.zero_rpow hp]

/-- Finite gluing followed by Minkowski bounds rooted candidate costs sharply.
The three common index blocks are source paths, remaining middle paths, and
targets unmatched by N. Their p-power sums recover each original cost exactly. -/
theorem totalFinitePowerCost_compose_root_le
    (M : OccurrenceMatching I J PEmpty.{1} PEmpty.{1})
    (N : OccurrenceMatching J K PEmpty.{1} PEmpty.{1}) {p : ℝ} (hp : 1 ≤ p)
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) (z : K → ℝ × ℝ) :
    (M.compose N).totalFinitePowerCost p x z ^ p⁻¹ ≤
      M.totalFinitePowerCost p x y ^ p⁻¹ + N.totalFinitePowerCost p y z ^ p⁻¹ := by
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hp)
  let A : I ⊕ J ⊕ K → ℝ := Sum.elim (finiteSourceCharge M x y)
    (Sum.elim (finiteTargetCharge M y) (fun _ => 0))
  let B : I ⊕ J ⊕ K → ℝ := Sum.elim
    (fun i => match M.finite i with | some j => finiteSourceCharge N y z j | none => 0)
    (Sum.elim (fun j => if ∃ i, M.finite i = some j then 0 else finiteSourceCharge N y z j)
      (finiteTargetCharge N z))
  let C : I ⊕ J ⊕ K → ℝ := Sum.elim (finiteSourceCharge (M.compose N) x z)
    (Sum.elim (targetPathCharge M N z) (finiteTargetCharge N z))
  have hA : ∀ t, 0 ≤ A t := by
    intro t
    rcases t with i | j | k
    · exact finiteSourceCharge_nonneg _ _ _ _
    · exact finiteTargetCharge_nonneg _ _ _
    · exact le_rfl
  have hB : ∀ t, 0 ≤ B t := by
    intro t
    rcases t with i | j | k
    · dsimp only [B, Sum.elim_inl]
      cases M.finite i <;> first | exact le_rfl | exact finiteSourceCharge_nonneg N y z _
    · dsimp [B]
      split_ifs <;> first | exact le_rfl | exact finiteSourceCharge_nonneg _ _ _ _
    · exact finiteTargetCharge_nonneg _ _ _
  have hC : ∀ t, 0 ≤ C t := by
    intro t
    rcases t with i | j | k
    · exact finiteSourceCharge_nonneg _ _ _ _
    · exact targetPathCharge_nonneg _ _ _ _
    · exact finiteTargetCharge_nonneg _ _ _
  have hpath : ∀ t, C t ≤ A t + B t := by
    intro t
    rcases t with i | j | k
    · exact sourcePathCharge_le M N x y z i
    · exact targetPathCharge_le M N y z j
    · simp [A, B, C]
  have hsumA : (∑ t, A t ^ p) = M.totalFinitePowerCost p x y := by
    simp only [A, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
      Real.zero_rpow hp0, Finset.sum_const_zero, add_zero]
    exact (totalFinitePowerCost_eq_chargeSums M hp0 x y).symm
  have hsumB : (∑ t, B t ^ p) = N.totalFinitePowerCost p y z := by
    simp only [B, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
    rw [← add_assoc, sum_middle_powers M hp0]
    exact (totalFinitePowerCost_eq_chargeSums N hp0 y z).symm
  have hsumC : (∑ t, C t ^ p) = (M.compose N).totalFinitePowerCost p x z := by
    simp only [C, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
    rw [sum_targetPath_powers M N hp0]
    exact (totalFinitePowerCost_eq_chargeSums (M.compose N) hp0 x z).symm
  have hpowers : (∑ t, C t ^ p) ≤ ∑ t, (A t + B t) ^ p :=
    Finset.sum_le_sum fun t _ => Real.rpow_le_rpow (hC t) (hpath t) (zero_le_one.trans hp)
  have hroot := Real.rpow_le_rpow
    (Finset.sum_nonneg (fun t _ => Real.rpow_nonneg (hC t) p)) hpowers
    (inv_nonneg.mpr (zero_le_one.trans hp))
  have hminkowski : (∑ t, (A t + B t) ^ p) ^ p⁻¹ ≤
      (∑ t, A t ^ p) ^ p⁻¹ + (∑ t, B t ^ p) ^ p⁻¹ := by
    simpa only [abs_of_nonneg (hA _), abs_of_nonneg (hB _),
      abs_of_nonneg (add_nonneg (hA _) (hB _)), one_div] using
      Real.Lp_add_le Finset.univ A B hp
  rw [← hsumC, ← hsumA, ← hsumB]
  exact hroot.trans hminkowski

private theorem totalFinitePowerCost_eq_zero_iff_totalFiniteCost_eq_zero
    (M : OccurrenceMatching I J PEmpty.{1} PEmpty.{1}) {p : ℝ} (hp : p ≠ 0)
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    M.totalFinitePowerCost p x y = 0 ↔ M.totalFiniteCost x y = 0 := by
  rw [totalFinitePowerCost_eq_chargeSums M hp x y]
  change (∑ i, finiteSourceCharge M x y i ^ p) + (∑ j, finiteTargetCharge M y j ^ p) = 0 ↔
    (∑ i, finiteSourceCharge M x y i) + (∑ j, finiteTargetCharge M y j) = 0
  rw [add_eq_zero_iff_of_nonneg
    (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (finiteSourceCharge_nonneg M x y i) p)
    (Finset.sum_nonneg fun j _ => Real.rpow_nonneg (finiteTargetCharge_nonneg M y j) p),
    add_eq_zero_iff_of_nonneg
      (Finset.sum_nonneg fun i _ => finiteSourceCharge_nonneg M x y i)
      (Finset.sum_nonneg fun j _ => finiteTargetCharge_nonneg M y j)]
  rw [Finset.sum_eq_zero_iff_of_nonneg
    (fun i _ => Real.rpow_nonneg (finiteSourceCharge_nonneg M x y i) p),
    Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => Real.rpow_nonneg (finiteTargetCharge_nonneg M y j) p),
    Finset.sum_eq_zero_iff_of_nonneg (fun i _ => finiteSourceCharge_nonneg M x y i),
    Finset.sum_eq_zero_iff_of_nonneg (fun j _ => finiteTargetCharge_nonneg M y j)]
  simp only [Real.rpow_eq_zero (finiteSourceCharge_nonneg M x y _) hp,
    Real.rpow_eq_zero (finiteTargetCharge_nonneg M y _) hp]

end OccurrenceMatching

variable {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]

private theorem finitePowerMatchingCost_eq_zero_iff_firstOrder_eq_zero
    {p : ℝ} (hp : p ≠ 0) (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    finitePowerMatchingCost p x y = 0 ↔ finiteFirstOrderMatchingCost x y = 0 := by
  constructor
  · intro hz
    obtain ⟨M, hM⟩ := exists_minimizing_powerMatching p x y
    have hzero := (M.totalFinitePowerCost_eq_zero_iff_totalFiniteCost_eq_zero hp x y).mp
      (hM.trans hz)
    exact le_antisymm ((finiteFirstOrderMatchingCost_le_totalFiniteCost x y M).trans_eq hzero)
      (finiteFirstOrderMatchingCost_nonneg x y)
  · intro hz
    obtain ⟨M, hM⟩ := exists_minimizing_occurrenceMatching x y
    have hzero := (M.totalFinitePowerCost_eq_zero_iff_totalFiniteCost_eq_zero hp x y).mpr
      (hM.trans hz)
    exact le_antisymm ((finitePowerMatchingCost_le_matching p x y M).trans_eq hzero)
      (finitePowerMatchingCost_nonneg p x y)

/-- Pairing each occurrence with itself gives zero rooted cost for every real p≥1. -/
@[simp] theorem finitePMatchingCost_self {p : ℝ} (hp : 1 ≤ p) (x : I → ℝ × ℝ) :
    finitePMatchingCost p x x = 0 := by
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hp)
  have hz := (finitePowerMatchingCost_eq_zero_iff_firstOrder_eq_zero hp0 x x).mpr
    (finiteFirstOrderMatchingCost_self x)
  simp only [finitePMatchingCost, hz, Real.zero_rpow (inv_ne_zero hp0)]

/-- Powered minima are symmetric because reversal preserves each candidate cost. -/
theorem finitePowerMatchingCost_comm (p : ℝ) (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    finitePowerMatchingCost p x y = finitePowerMatchingCost p y x := by
  obtain ⟨M, hM⟩ := exists_minimizing_powerMatching p x y
  obtain ⟨N, hN⟩ := exists_minimizing_powerMatching p y x
  apply le_antisymm
  · calc
      _ ≤ N.reverse.totalFinitePowerCost p x y := finitePowerMatchingCost_le_matching _ _ _ _
      _ = N.totalFinitePowerCost p y x := N.totalFinitePowerCost_reverse p y x
      _ = _ := hN
  · calc
      _ ≤ M.reverse.totalFinitePowerCost p y x := finitePowerMatchingCost_le_matching _ _ _ _
      _ = M.totalFinitePowerCost p x y := M.totalFinitePowerCost_reverse p x y
      _ = _ := hM

/-- Symmetry also holds for the supporting rooted algebra outside the PD exponent domain. -/
theorem finitePMatchingCost_comm (p : ℝ) (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    finitePMatchingCost p x y = finitePMatchingCost p y x := by
  simp only [finitePMatchingCost, finitePowerMatchingCost_comm p x y]

/-- Compose two actual minimizing matchings, then apply the rooted candidate inequality. -/
theorem finitePMatchingCost_triangle {p : ℝ} (hp : 1 ≤ p)
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) (z : K → ℝ × ℝ) :
    finitePMatchingCost p x z ≤ finitePMatchingCost p x y + finitePMatchingCost p y z := by
  obtain ⟨M, hM⟩ := exists_minimizing_pMatching p x y
  obtain ⟨N, hN⟩ := exists_minimizing_pMatching p y z
  calc
    _ ≤ (M.compose N).totalFinitePowerCost p x z ^ p⁻¹ :=
      finitePMatchingCost_le_matching hp x z (M.compose N)
    _ ≤ M.totalFinitePowerCost p x y ^ p⁻¹ + N.totalFinitePowerCost p y z ^ p⁻¹ :=
      M.totalFinitePowerCost_compose_root_le N hp x y z
    _ = _ := by rw [hM, hN]

/-- A value-preserving equivalence has zero rooted cost, independently of the occurrence labels. -/
theorem finitePMatchingCost_eq_zero_of_equiv {p : ℝ} (hp : 1 ≤ p)
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) (e : I ≃ J) (he : ∀ i, x i = y (e i)) :
    finitePMatchingCost p x y = 0 := by
  have hx : y ∘ e = x := funext (fun i => (he i).symm)
  have h := finitePMatchingCost_reindex e (Equiv.refl J) p y y
  rw [hx] at h
  exact h.trans (finitePMatchingCost_self hp y)

/-- Positive lifetimes make zero cost equivalent to equal values with multiplicity. -/
theorem finitePMatchingCost_eq_zero_iff {p : ℝ} (hp : 1 ≤ p)
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ)
    (hx : ∀ i, (x i).1 < (x i).2) (hy : ∀ j, (y j).1 < (y j).2) :
    finitePMatchingCost p x y = 0 ↔ ∃ e : I ≃ J, ∀ i, x i = y (e i) := by
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hp)
  rw [finitePMatchingCost, Real.rpow_eq_zero (finitePowerMatchingCost_nonneg p x y)
    (inv_ne_zero hp0), finitePowerMatchingCost_eq_zero_iff_firstOrder_eq_zero hp0 x y]
  exact finiteFirstOrderMatchingCost_eq_zero_iff x y hx hy

end TDA.Persistence
