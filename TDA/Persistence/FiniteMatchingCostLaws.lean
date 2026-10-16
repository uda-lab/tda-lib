import TDA.Persistence.FiniteMatchingCost
import TDA.Persistence.DiagramBottleneckLaws

/-!
# Laws of the finite first-order matching cost

Reversal and composition of the existing partial injections give symmetry and
the triangle inequality for the real sum cost. Composition allocates each middle
occurrence's second-matching charge to exactly one side of the estimate.
Positive lifetimes are needed only for separation by value-preserving occurrence
bijections. Raw occurrence presentations may differ by a permutation at zero cost.
-/

namespace TDA.Persistence

open scoped Classical

namespace OccurrenceMatching

variable {I J K : Type*}

private noncomputable def sourceCharge
    (M : OccurrenceMatching I J PEmpty.{1} PEmpty.{1})
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) (i : I) : ℝ :=
  match M.finite i with
  | some j => (finitePairCost (x i) (y j)).toReal
  | none => (diagonalCost (x i)).toReal

private theorem sourceCharge_nonneg
    (M : OccurrenceMatching I J PEmpty.{1} PEmpty.{1})
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) (i : I) : 0 ≤ sourceCharge M x y i := by
  unfold sourceCharge
  cases M.finite i <;> exact ENNReal.toReal_nonneg

variable [Fintype I]

private noncomputable def targetCharge
    (M : OccurrenceMatching I J PEmpty.{1} PEmpty.{1})
    (y : J → ℝ × ℝ) (j : J) : ℝ := by
  classical
  exact if ∃ i, M.finite i = some j then 0 else (diagonalCost (y j)).toReal

private theorem targetCharge_nonneg
    (M : OccurrenceMatching I J PEmpty.{1} PEmpty.{1})
    (y : J → ℝ × ℝ) (j : J) : 0 ≤ targetCharge M y j := by
  classical
  unfold targetCharge
  split_ifs <;> positivity

variable [Fintype J] [Fintype K]

/-- Separate paired cells from the two unmatched sums to make reversal explicit. -/
private theorem totalFiniteCost_eq_symmetricSums
    (M : OccurrenceMatching I J PEmpty.{1} PEmpty.{1})
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    M.totalFiniteCost x y =
      (∑ i, ∑ j, if M.finite i = some j then (finitePairCost (x i) (y j)).toReal else 0) +
      (∑ i, if ∃ j, M.finite i = some j then 0 else (diagonalCost (x i)).toReal) +
      ∑ j, targetCharge M y j := by
  classical
  have hs (i : I) : sourceCharge M x y i =
      (∑ j, if M.finite i = some j then (finitePairCost (x i) (y j)).toReal else 0) +
      (if ∃ j, M.finite i = some j then 0 else (diagonalCost (x i)).toReal) := by
    cases h : M.finite i <;> simp [sourceCharge, h]
  change (∑ i, sourceCharge M x y i) + ∑ j, targetCharge M y j = _
  simp_rw [hs]
  rw [Finset.sum_add_distrib]

/-- Reversal preserves the real total, including both unmatched occurrence sums. -/
theorem totalFiniteCost_reverse
    (M : OccurrenceMatching I J PEmpty.{1} PEmpty.{1})
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    M.reverse.totalFiniteCost y x = M.totalFiniteCost x y := by
  classical
  rw [totalFiniteCost_eq_symmetricSums, totalFiniteCost_eq_symmetricSums]
  unfold targetCharge
  simp_rw [reverse_finite_some_iff, finitePairCost_comm (y _) (x _)]
  rw [Finset.sum_comm]
  abel

private theorem diagonal_toReal_le_pair_add (p q : ℝ × ℝ) :
    (diagonalCost p).toReal ≤ (finitePairCost p q).toReal + (diagonalCost q).toReal := by
  have h := ENNReal.toReal_mono
    (by simp [finitePairCost, diagonalCost]) (diagonalCost_le_pair_add p q)
  rw [ENNReal.toReal_add (show finitePairCost p q ≠ ⊤ by simp [finitePairCost])
    (show diagonalCost q ≠ ⊤ by simp [diagonalCost])] at h
  exact h

private theorem pair_toReal_triangle (p q r : ℝ × ℝ) :
    (finitePairCost p r).toReal ≤
      (finitePairCost p q).toReal + (finitePairCost q r).toReal := by
  simpa only [finitePairCost_toReal, dist_eq_norm] using dist_triangle p q r

/-- Compose partial injections and allocate each middle charge once.
Selected middle labels pay for source paths; the complementary labels pay for
remaining target paths. A middle occurrence unmatched on both sides has no endpoint. -/
theorem totalFiniteCost_compose_le
    (M : OccurrenceMatching I J PEmpty.{1} PEmpty.{1})
    (N : OccurrenceMatching J K PEmpty.{1} PEmpty.{1})
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) (z : K → ℝ × ℝ) :
    (M.compose N).totalFiniteCost x z ≤ M.totalFiniteCost x y + N.totalFiniteCost y z := by
  classical
  -- A source path uses N's source charge only at a middle label selected by M.
  have hs (i : I) : sourceCharge (M.compose N) x z i ≤ sourceCharge M x y i +
      (match M.finite i with | some j => sourceCharge N y z j | none => 0) := by
    cases hm : M.finite i with
    | none => simp [sourceCharge, compose, hm]
    | some j =>
      cases hn : N.finite j with
      | none =>
        simpa [sourceCharge, compose, hm, hn] using diagonal_toReal_le_pair_add (x i) (y j)
      | some k =>
        simpa [sourceCharge, compose, hm, hn] using pair_toReal_triangle (x i) (y j) (z k)
  have hsource : (∑ i, sourceCharge (M.compose N) x z i) ≤
      (∑ i, sourceCharge M x y i) +
        ∑ j, if ∃ i, M.finite i = some j then sourceCharge N y z j else 0 := by
    calc
      _ ≤ ∑ i, (sourceCharge M x y i +
          (match M.finite i with | some j => sourceCharge N y z j | none => 0)) :=
        Finset.sum_le_sum (fun i _ => hs i)
      _ = _ := by
        rw [Finset.sum_add_distrib]
        exact congrArg (fun r => (∑ i, sourceCharge M x y i) + r)
          (M.sum_matched (sourceCharge N y z))
  -- A target not selected by N cannot be selected by the composed matching.
  have hncomp (k : K) (hn : ¬ ∃ j, N.finite j = some k) :
      ¬ ∃ i, (M.compose N).finite i = some k := by
    rintro ⟨i, hi⟩
    cases hm : M.finite i with
    | none => simp [compose, hm] at hi
    | some j => exact hn ⟨j, by simpa [compose, hm] using hi⟩
  -- Split targets into those selected by N and its unmatched targets.
  have hsplit : (∑ k, targetCharge (M.compose N) z k) =
      (∑ j, match N.finite j with
        | some k => targetCharge (M.compose N) z k | none => 0) +
      ∑ k, targetCharge N z k := by
    calc
      _ = (∑ k, if ∃ j, N.finite j = some k then targetCharge (M.compose N) z k else 0) +
          ∑ k, targetCharge N z k := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro k _
        by_cases hn : ∃ j, N.finite j = some k
        · simp [targetCharge, hn]
        · simp [targetCharge, hn, hncomp k hn]
      _ = _ := congrArg (fun r => r + ∑ k, targetCharge N z k)
        (N.sum_matched (targetCharge (M.compose N) z)).symm
  -- The remaining target paths use precisely the complementary middle labels.
  have ht (j : J) :
      (match N.finite j with
        | some k => targetCharge (M.compose N) z k | none => 0) ≤
      targetCharge M y j +
        (if ∃ i, M.finite i = some j then 0 else sourceCharge N y z j) := by
    cases hn : N.finite j with
    | none =>
      exact add_nonneg (targetCharge_nonneg M y j)
        (by split_ifs <;> first | exact le_rfl | exact sourceCharge_nonneg N y z j)
    | some k =>
      by_cases hm : ∃ i, M.finite i = some j
      · obtain ⟨i, hi⟩ := hm
        have hc : ∃ i, (M.compose N).finite i = some k :=
          ⟨i, by simp [compose, hi, hn]⟩
        simp [targetCharge, hc, show ∃ i, M.finite i = some j from ⟨i, hi⟩]
      · have hdiag : (diagonalCost (z k)).toReal ≤
            (diagonalCost (y j)).toReal + (finitePairCost (y j) (z k)).toReal := by
          simpa only [finitePairCost_comm, add_comm] using
            diagonal_toReal_le_pair_add (z k) (y j)
        calc
          _ ≤ (diagonalCost (z k)).toReal := by
            change targetCharge (M.compose N) z k ≤ _
            unfold targetCharge
            split_ifs <;> first | exact ENNReal.toReal_nonneg | exact le_rfl
          _ ≤ _ := by simpa [targetCharge, sourceCharge, hm, hn] using hdiag
  have htarget : (∑ k, targetCharge (M.compose N) z k) ≤
      (∑ j, targetCharge M y j) +
        (∑ j, if ∃ i, M.finite i = some j then 0 else sourceCharge N y z j) +
        ∑ k, targetCharge N z k := by
    rw [hsplit]
    refine add_le_add ?_ le_rfl
    calc
      _ ≤ ∑ j, (targetCharge M y j +
          (if ∃ i, M.finite i = some j then 0 else sourceCharge N y z j)) :=
        Finset.sum_le_sum (fun j _ => ht j)
      _ = _ := Finset.sum_add_distrib
  have hpartition :
      (∑ j, if ∃ i, M.finite i = some j then sourceCharge N y z j else 0) +
        (∑ j, if ∃ i, M.finite i = some j then 0 else sourceCharge N y z j) =
      ∑ j, sourceCharge N y z j := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> simp
  change (∑ i, sourceCharge (M.compose N) x z i) +
      (∑ k, targetCharge (M.compose N) z k) ≤
    ((∑ i, sourceCharge M x y i) + ∑ j, targetCharge M y j) +
      ((∑ j, sourceCharge N y z j) + ∑ k, targetCharge N z k)
  have h := add_le_add hsource htarget
  linarith

private theorem sourceCharge_le_total
    (M : OccurrenceMatching I J PEmpty.{1} PEmpty.{1})
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) (i : I) :
    sourceCharge M x y i ≤ M.totalFiniteCost x y := by
  calc
    _ ≤ ∑ i, sourceCharge M x y i :=
      Finset.single_le_sum (fun i _ => sourceCharge_nonneg M x y i) (Finset.mem_univ i)
    _ ≤ (∑ i, sourceCharge M x y i) + ∑ j, targetCharge M y j :=
      le_add_of_nonneg_right (Finset.sum_nonneg (fun j _ => targetCharge_nonneg M y j))

private theorem targetCharge_le_total
    (M : OccurrenceMatching I J PEmpty.{1} PEmpty.{1})
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) (j : J) :
    targetCharge M y j ≤ M.totalFiniteCost x y := by
  calc
    _ ≤ ∑ j, targetCharge M y j :=
      Finset.single_le_sum (fun j _ => targetCharge_nonneg M y j) (Finset.mem_univ j)
    _ ≤ (∑ i, sourceCharge M x y i) + ∑ j, targetCharge M y j :=
      le_add_of_nonneg_left (Finset.sum_nonneg (fun i _ => sourceCharge_nonneg M x y i))

private theorem diagonal_toReal_pos {p : ℝ × ℝ} (hp : p.1 < p.2) :
    0 < (diagonalCost p).toReal := by
  rw [diagonalCost_toReal, abs_of_pos (sub_pos.mpr hp)]
  exact div_pos (sub_pos.mpr hp) (by norm_num)

/-- Positive lifetimes force a zero-cost partial injection to be total on both sides. -/
private theorem exists_valueEquiv_of_totalFiniteCost_eq_zero
    (M : OccurrenceMatching I J PEmpty.{1} PEmpty.{1})
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ)
    (hx : ∀ i, (x i).1 < (x i).2) (hy : ∀ j, (y j).1 < (y j).2)
    (hzero : M.totalFiniteCost x y = 0) :
    ∃ e : I ≃ J, ∀ i, x i = y (e i) := by
  classical
  have hs (i : I) : ∃ j, M.finite i = some j := by
    cases hi : M.finite i with
    | some j => exact ⟨j, rfl⟩
    | none =>
      have hd : (diagonalCost (x i)).toReal ≤ 0 := by
        simpa only [sourceCharge, hi, hzero] using sourceCharge_le_total M x y i
      exact (not_le_of_gt (diagonal_toReal_pos (hx i)) hd).elim
  have ht (j : J) : ∃ i, M.finite i = some j := by
    by_contra hn
    have hd : (diagonalCost (y j)).toReal ≤ 0 := by
      simpa only [targetCharge, if_neg hn, hzero] using targetCharge_le_total M x y j
    exact not_le_of_gt (diagonal_toReal_pos (hy j)) hd
  let f : I → J := fun i => (hs i).choose
  have hf (i : I) : M.finite i = some (f i) := (hs i).choose_spec
  have hinj : Function.Injective f := by
    intro i i' he
    exact M.finite_injective i i' (f i) (hf i) (he ▸ hf i')
  have hsurj : Function.Surjective f := by
    intro j
    obtain ⟨i, hi⟩ := ht j
    exact ⟨i, Option.some.inj ((hf i).symm.trans hi)⟩
  let e : I ≃ J := Equiv.ofBijective f ⟨hinj, hsurj⟩
  refine ⟨e, fun i => ?_⟩
  have hc : ‖x i - y (f i)‖ ≤ 0 := by
    simpa only [sourceCharge, hf i, finitePairCost_toReal, hzero] using
      sourceCharge_le_total M x y i
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hc (norm_nonneg _)))

end OccurrenceMatching

variable {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]

/-- Pairing each occurrence with itself has zero total cost. -/
@[simp] theorem finiteFirstOrderMatchingCost_self (x : I → ℝ × ℝ) :
    finiteFirstOrderMatchingCost x x = 0 := by
  classical
  let M : OccurrenceMatching I I PEmpty.{1} PEmpty.{1} :=
    ⟨some, by intro i i' j hi hi'; exact Option.some.inj (hi.trans hi'.symm), Equiv.refl _⟩
  have hcost : M.totalFiniteCost x x = 0 := by
    simp [OccurrenceMatching.totalFiniteCost, M]
  exact le_antisymm ((finiteFirstOrderMatchingCost_le_totalFiniteCost x x M).trans_eq hcost)
    (finiteFirstOrderMatchingCost_nonneg x x)

/-- Reversing attaining matchings proves symmetry of the minimum. -/
theorem finiteFirstOrderMatchingCost_comm (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    finiteFirstOrderMatchingCost x y = finiteFirstOrderMatchingCost y x := by
  obtain ⟨M, hM⟩ := exists_minimizing_occurrenceMatching x y
  obtain ⟨N, hN⟩ := exists_minimizing_occurrenceMatching y x
  apply le_antisymm
  · calc
      _ ≤ N.reverse.totalFiniteCost x y := finiteFirstOrderMatchingCost_le_totalFiniteCost _ _ _
      _ = N.totalFiniteCost y x := N.totalFiniteCost_reverse y x
      _ = _ := hN
  · calc
      _ ≤ M.reverse.totalFiniteCost y x := finiteFirstOrderMatchingCost_le_totalFiniteCost _ _ _
      _ = M.totalFiniteCost x y := M.totalFiniteCost_reverse x y
      _ = _ := hM

/-- Composing attained minimizers gives the first-order triangle inequality. -/
theorem finiteFirstOrderMatchingCost_triangle
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) (z : K → ℝ × ℝ) :
    finiteFirstOrderMatchingCost x z ≤
      finiteFirstOrderMatchingCost x y + finiteFirstOrderMatchingCost y z := by
  obtain ⟨M, hM⟩ := exists_minimizing_occurrenceMatching x y
  obtain ⟨N, hN⟩ := exists_minimizing_occurrenceMatching y z
  calc
    _ ≤ (M.compose N).totalFiniteCost x z := finiteFirstOrderMatchingCost_le_totalFiniteCost _ _ _
    _ ≤ M.totalFiniteCost x y + N.totalFiniteCost y z := M.totalFiniteCost_compose_le N x y z
    _ = _ := by rw [hM, hN]

/-- Value-preserving occurrence equivalences have zero cost, by reindexing self cost. -/
theorem finiteFirstOrderMatchingCost_eq_zero_of_equiv
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) (e : I ≃ J) (he : ∀ i, x i = y (e i)) :
    finiteFirstOrderMatchingCost x y = 0 := by
  have hx : y ∘ e = x := funext (fun i => (he i).symm)
  have hy : y ∘ Equiv.refl J = y := rfl
  have h := finiteFirstOrderMatchingCost_reindex e (Equiv.refl J) y y
  rw [hx, hy] at h
  exact h.trans (finiteFirstOrderMatchingCost_self y)

/-- On positive finite diagrams, zero cost means equal values with multiplicity.
Diagonal occurrences are excluded: they could otherwise disappear at zero cost. -/
theorem finiteFirstOrderMatchingCost_eq_zero_iff
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ)
    (hx : ∀ i, (x i).1 < (x i).2) (hy : ∀ j, (y j).1 < (y j).2) :
    finiteFirstOrderMatchingCost x y = 0 ↔ ∃ e : I ≃ J, ∀ i, x i = y (e i) := by
  constructor
  · intro hz
    obtain ⟨M, hM⟩ := exists_minimizing_occurrenceMatching x y
    exact M.exists_valueEquiv_of_totalFiniteCost_eq_zero x y hx hy (hM.trans hz)
  · rintro ⟨e, he⟩
    exact finiteFirstOrderMatchingCost_eq_zero_of_equiv x y e he

end TDA.Persistence
