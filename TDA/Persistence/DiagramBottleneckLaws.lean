import TDA.Persistence.DiagramBottleneck

/-! Extended-distance laws for occurrence-based bottleneck distance. -/

namespace TDA.Persistence

open scoped ENNReal

private theorem ofReal_le_add_of_le {a b c : ℝ} (h : a ≤ b + c) :
    ENNReal.ofReal a ≤ ENNReal.ofReal b + ENNReal.ofReal c :=
  (ENNReal.ofReal_le_ofReal h).trans ENNReal.ofReal_add_le

theorem finitePairCost_self (p : ℝ × ℝ) : finitePairCost p p = 0 := by
  simp [finitePairCost]

theorem finitePairCost_comm (p q : ℝ × ℝ) :
    finitePairCost p q = finitePairCost q p := by
  simp [finitePairCost, abs_sub_comm]

theorem finitePairCost_triangle (p q r : ℝ × ℝ) :
    finitePairCost p r ≤ finitePairCost p q + finitePairCost q r := by
  apply ofReal_le_add_of_le
  have h₁ := abs_sub_le p.1 q.1 r.1
  have h₂ := abs_sub_le p.2 q.2 r.2
  have h₃ : |p.1 - q.1| ≤ max |p.1 - q.1| |p.2 - q.2| := le_max_left _ _
  have h₄ : |p.2 - q.2| ≤ max |p.1 - q.1| |p.2 - q.2| := le_max_right _ _
  have h₅ : |q.1 - r.1| ≤ max |q.1 - r.1| |q.2 - r.2| := le_max_left _ _
  have h₆ : |q.2 - r.2| ≤ max |q.1 - r.1| |q.2 - r.2| := le_max_right _ _
  exact max_le (by linarith) (by linarith)

theorem essentialPairCost_self (b : ℝ) : essentialPairCost b b = 0 := by
  simp [essentialPairCost]

theorem essentialPairCost_comm (b c : ℝ) :
    essentialPairCost b c = essentialPairCost c b := by
  simp [essentialPairCost, abs_sub_comm]

theorem essentialPairCost_triangle (b c d : ℝ) :
    essentialPairCost b d ≤ essentialPairCost b c + essentialPairCost c d :=
  ofReal_le_add_of_le (abs_sub_le b c d)

/-- Moving a finite pair changes its diagonal cost by at most its maximum-coordinate cost.
The absolute persistence also covers pairs whose death precedes birth. -/
theorem diagonalCost_le_pair_add (p q : ℝ × ℝ) :
    diagonalCost p ≤ finitePairCost p q + diagonalCost q := by
  unfold diagonalCost finitePairCost
  apply ofReal_le_add_of_le
  have h₁ := abs_sub_le p.2 q.2 p.1
  have h₂ := abs_sub_le q.2 q.1 p.1
  have h₃ : |q.1 - p.1| = |p.1 - q.1| := abs_sub_comm _ _
  have h₄ : |p.1 - q.1| ≤ max |p.1 - q.1| |p.2 - q.2| := le_max_left _ _
  have h₅ : |p.2 - q.2| ≤ max |p.1 - q.1| |p.2 - q.2| := le_max_right _ _
  linarith

theorem diagonalCost_le_pair_add_rev (p q : ℝ × ℝ) :
    diagonalCost q ≤ diagonalCost p + finitePairCost p q := by
  rw [add_comm, finitePairCost_comm]
  exact diagonalCost_le_pair_add q p

namespace OccurrenceMatching

variable {F₁ F₂ F₃ E₁ E₂ E₃ : Type*}
variable [Fintype F₁] [Fintype F₂] [Fintype F₃]
variable [Fintype E₁] [Fintype E₂] [Fintype E₃]
noncomputable local instance : DecidableEq F₁ := Classical.decEq F₁
noncomputable local instance : DecidableEq F₂ := Classical.decEq F₂
noncomputable local instance : DecidableEq F₃ := Classical.decEq F₃

theorem source_le_cost (M : OccurrenceMatching F₁ F₂ E₁ E₂)
    (x : F₁ → ℝ × ℝ) (y : F₂ → ℝ × ℝ)
    (b : E₁ → ℝ) (c : E₂ → ℝ) (i : F₁) :
    (match M.finite i with
      | some j => finitePairCost (x i) (y j)
      | none => diagonalCost (x i)) ≤ M.cost x y b c := by
  classical
  exact (Finset.le_sup (s := (Finset.univ : Finset F₁))
    (f := fun i => match M.finite i with
      | some j => finitePairCost (x i) (y j)
      | none => diagonalCost (x i)) (Finset.mem_univ i)).trans
      (le_max_left _ _)

theorem target_le_cost (M : OccurrenceMatching F₁ F₂ E₁ E₂)
    (x : F₁ → ℝ × ℝ) (y : F₂ → ℝ × ℝ)
    (b : E₁ → ℝ) (c : E₂ → ℝ) (j : F₂) :
    (if ∃ i, M.finite i = some j then 0 else diagonalCost (y j)) ≤
      M.cost x y b c := by
  classical
  exact (Finset.le_sup (s := (Finset.univ : Finset F₂))
    (f := fun j => if ∃ i, M.finite i = some j then 0 else diagonalCost (y j))
    (Finset.mem_univ j)).trans ((le_max_left _ _).trans (le_max_right _ _))

theorem essential_le_cost (M : OccurrenceMatching F₁ F₂ E₁ E₂)
    (x : F₁ → ℝ × ℝ) (y : F₂ → ℝ × ℝ)
    (b : E₁ → ℝ) (c : E₂ → ℝ) (k : E₁) :
    essentialPairCost (b k) (c (M.essential k)) ≤ M.cost x y b c := by
  classical
  exact (Finset.le_sup (s := (Finset.univ : Finset E₁))
    (f := fun k => essentialPairCost (b k) (c (M.essential k)))
    (Finset.mem_univ k)).trans ((le_max_right _ _).trans (le_max_right _ _))

theorem cost_le_of (M : OccurrenceMatching F₁ F₂ E₁ E₂)
    (x : F₁ → ℝ × ℝ) (y : F₂ → ℝ × ℝ)
    (b : E₁ → ℝ) (c : E₂ → ℝ) (r : ℝ≥0∞)
    (hs : ∀ i, (match M.finite i with
      | some j => finitePairCost (x i) (y j)
      | none => diagonalCost (x i)) ≤ r)
    (ht : ∀ j, (if ∃ i, M.finite i = some j then 0 else diagonalCost (y j)) ≤ r)
    (he : ∀ k, essentialPairCost (b k) (c (M.essential k)) ≤ r) :
    M.cost x y b c ≤ r := by
  classical
  unfold cost
  apply max_le_iff.mpr
  constructor
  · exact Finset.sup_le (fun i _ => hs i)
  · apply max_le_iff.mpr
    exact ⟨Finset.sup_le (fun j _ => ht j), Finset.sup_le (fun k _ => he k)⟩

/-- Reverse a partial injection by taking the unique predecessor of each selected target. -/
noncomputable def reverse (M : OccurrenceMatching F₁ F₂ E₁ E₂) :
    OccurrenceMatching F₂ F₁ E₂ E₁ where
  finite j := if h : ∃ i, M.finite i = some j then some h.choose else none
  finite_injective := by
    classical
    intro j j' i hj hj'
    change (if h : ∃ k, M.finite k = some j then some h.choose else none) = some i at hj
    change (if h : ∃ k, M.finite k = some j' then some h.choose else none) = some i at hj'
    split_ifs at hj hj' with h h'
    · have hi := h.choose_spec
      have hi' := h'.choose_spec
      have he : h.choose = h'.choose := Option.some.inj (hj.trans hj'.symm)
      exact Option.some.inj (hi.symm.trans (he ▸ hi'))
  essential := M.essential.symm

theorem reverse_finite_some_iff (M : OccurrenceMatching F₁ F₂ E₁ E₂)
    (j : F₂) (i : F₁) : M.reverse.finite j = some i ↔ M.finite i = some j := by
  classical
  constructor
  · intro h
    change (if he : ∃ k, M.finite k = some j then some he.choose else none) = some i at h
    split_ifs at h with he
    · have hi : he.choose = i := Option.some.inj h
      simpa [hi] using he.choose_spec
  · intro h
    have he : ∃ k, M.finite k = some j := ⟨i, h⟩
    have hi : he.choose = i := M.finite_injective _ _ _ he.choose_spec h
    change (if he : ∃ k, M.finite k = some j then some he.choose else none) = some i
    simp [he, hi]

/-- Reverse preserves the full occurrence cost, including both unmatched sets. -/
private theorem cost_reverse_le (M : OccurrenceMatching F₁ F₂ E₁ E₂)
    (x : F₁ → ℝ × ℝ) (y : F₂ → ℝ × ℝ)
    (b : E₁ → ℝ) (c : E₂ → ℝ) :
    M.reverse.cost y x c b ≤ M.cost x y b c := by
  classical
  apply cost_le_of
  · intro j
    cases hr : M.reverse.finite j with
    | none =>
      have hn : ¬ ∃ i, M.finite i = some j := by
        intro ⟨i, hi⟩
        have hc := hr.symm.trans ((reverse_finite_some_iff M j i).mpr hi)
        cases hc
      simpa [hr, hn] using target_le_cost M x y b c j
    | some i =>
      have hi := (reverse_finite_some_iff M j i).mp hr
      simpa [hr, hi, finitePairCost_comm] using source_le_cost M x y b c i
  · intro i
    by_cases hi : ∃ j, M.reverse.finite j = some i
    · simp [hi]
    · have hm : M.finite i = none := by
        cases h : M.finite i with
        | none => rfl
        | some j => exact (hi ⟨j, (reverse_finite_some_iff M j i).mpr h⟩).elim
      simpa [hi, hm] using source_le_cost M x y b c i
  · intro k
    simpa [reverse, essentialPairCost_comm] using
      essential_le_cost M x y b c (M.essential.symm k)

theorem reverse_reverse (M : OccurrenceMatching F₁ F₂ E₁ E₂) :
    M.reverse.reverse = M := by
  classical
  apply ext
  · funext i
    cases h : M.finite i with
    | none =>
      have hh : M.reverse.reverse.finite i = none := by
        cases h' : M.reverse.reverse.finite i with
        | none => rfl
        | some j =>
          have hj := (reverse_finite_some_iff M.reverse i j).mp h'
          have hi := (reverse_finite_some_iff M j i).mp hj
          simp [h] at hi
      exact hh
    | some j =>
      exact (reverse_finite_some_iff M.reverse i j).mpr
        ((reverse_finite_some_iff M j i).mpr h)
  · change M.essential.symm.symm = M.essential
    simp

theorem cost_reverse (M : OccurrenceMatching F₁ F₂ E₁ E₂)
    (x : F₁ → ℝ × ℝ) (y : F₂ → ℝ × ℝ)
    (b : E₁ → ℝ) (c : E₂ → ℝ) :
    M.reverse.cost y x c b = M.cost x y b c := by
  apply le_antisymm (cost_reverse_le M x y b c)
  simpa [reverse_reverse] using cost_reverse_le M.reverse y x c b

/-- Glue matching paths through their common middle occurrence labels. -/
def compose (M : OccurrenceMatching F₁ F₂ E₁ E₂)
    (N : OccurrenceMatching F₂ F₃ E₂ E₃) :
    OccurrenceMatching F₁ F₃ E₁ E₃ where
  finite i := (M.finite i).bind N.finite
  finite_injective := by
    intro i i' k hi hi'
    cases hm : M.finite i with
    | none => simp [hm] at hi
    | some j =>
      cases hm' : M.finite i' with
      | none => simp [hm'] at hi'
      | some j' =>
        have hn : N.finite j = some k := by simpa [hm] using hi
        have hn' : N.finite j' = some k := by simpa [hm'] using hi'
        have hj := N.finite_injective j j' k hn hn'
        exact M.finite_injective i i' j hm (hj ▸ hm')
  essential := M.essential.trans N.essential

/-- Every complete path or diagonal endpoint in a glued matching costs at most the
sum of the original costs. Middle occurrences unmatched on both sides create no endpoint. -/
theorem cost_compose_le (M : OccurrenceMatching F₁ F₂ E₁ E₂)
    (N : OccurrenceMatching F₂ F₃ E₂ E₃)
    (x : F₁ → ℝ × ℝ) (y : F₂ → ℝ × ℝ) (z : F₃ → ℝ × ℝ)
    (b : E₁ → ℝ) (c : E₂ → ℝ) (d : E₃ → ℝ) :
    (M.compose N).cost x z b d ≤ M.cost x y b c + N.cost y z c d := by
  classical
  apply cost_le_of
  · intro i
    cases hm : M.finite i with
    | none =>
      have h := source_le_cost M x y b c i
      simpa [compose, hm] using le_trans h (le_add_of_nonneg_right bot_le)
    | some j =>
      cases hn : N.finite j with
      | none =>
        have h₁ : finitePairCost (x i) (y j) ≤ M.cost x y b c := by
          simpa [hm] using source_le_cost M x y b c i
        have h₂ : diagonalCost (y j) ≤ N.cost y z c d := by
          simpa [hn] using source_le_cost N y z c d j
        have h := (diagonalCost_le_pair_add (x i) (y j)).trans (add_le_add h₁ h₂)
        simpa [compose, hm, hn] using h
      | some k =>
        have h₁ : finitePairCost (x i) (y j) ≤ M.cost x y b c := by
          simpa [hm] using source_le_cost M x y b c i
        have h₂ : finitePairCost (y j) (z k) ≤ N.cost y z c d := by
          simpa [hn] using source_le_cost N y z c d j
        have h := (finitePairCost_triangle (x i) (y j) (z k)).trans
          (add_le_add h₁ h₂)
        simpa [compose, hm, hn] using h
  · intro k
    by_cases hk : ∃ i, (M.compose N).finite i = some k
    · simp [hk]
    · by_cases hn : ∃ j, N.finite j = some k
      · obtain ⟨j, hj⟩ := hn
        have hm : ¬ ∃ i, M.finite i = some j := by
          rintro ⟨i, hi⟩
          apply hk
          exact ⟨i, by simp [compose, hi, hj]⟩
        have h₁ : diagonalCost (y j) ≤ M.cost x y b c := by
          simpa [hm] using target_le_cost M x y b c j
        have h₂ : finitePairCost (y j) (z k) ≤ N.cost y z c d := by
          simpa [hj] using source_le_cost N y z c d j
        have h := (diagonalCost_le_pair_add_rev (y j) (z k)).trans
          (add_le_add h₁ h₂)
        simpa [hk] using h
      · have h : diagonalCost (z k) ≤ N.cost y z c d := by
          simpa [hn] using target_le_cost N y z c d k
        simpa [hk] using le_trans h (le_add_of_nonneg_left bot_le)
  · intro k
    have h₁ := essential_le_cost M x y b c k
    have h₂ := essential_le_cost N y z c d (M.essential k)
    exact (essentialPairCost_triangle (b k) (c (M.essential k))
      (d (N.essential (M.essential k)))).trans (add_le_add h₁ h₂)

end OccurrenceMatching

theorem bottleneck_self (D : Diagram ℝ) : bottleneck D D = 0 := by
  classical
  let M : OccurrenceMatching D.finiteOccurrences D.finiteOccurrences
      D.essentialOccurrences D.essentialOccurrences :=
    ⟨some, by intro i i' j hi hi'; exact Option.some.inj (hi.trans hi'.symm), Equiv.refl _⟩
  have hc : M.cost (fun p => p.1) (fun p => p.1)
      (fun b => b.1) (fun b => b.1) = 0 := by
    simp [OccurrenceMatching.cost, M, finitePairCost_self, essentialPairCost_self]
  exact le_antisymm ((bottleneck_le_matching D D M).trans_eq hc) bot_le

theorem presentationBottleneck_comm {F₁ F₂ E₁ E₂ : Type*}
    [Fintype F₁] [Fintype F₂] [Fintype E₁] [Fintype E₂]
    (x : F₁ → ℝ × ℝ) (y : F₂ → ℝ × ℝ)
    (b : E₁ → ℝ) (c : E₂ → ℝ) :
    presentationBottleneck x y b c = presentationBottleneck y x c b := by
  apply le_antisymm
  · apply le_iInf
    intro M
    exact (presentationBottleneck_le_cost x y b c M.reverse).trans_eq
      (OccurrenceMatching.cost_reverse M y x c b)
  · apply le_iInf
    intro M
    exact (presentationBottleneck_le_cost y x c b M.reverse).trans_eq
      (OccurrenceMatching.cost_reverse M x y b c)

theorem bottleneck_comm (D E : Diagram ℝ) : bottleneck D E = bottleneck E D :=
  presentationBottleneck_comm _ _ _ _

theorem bottleneck_triangle (D E F : Diagram ℝ) :
    bottleneck D F ≤ bottleneck D E + bottleneck E F := by
  by_cases hDE : bottleneck D E = ⊤
  · simp [hDE]
  by_cases hEF : bottleneck E F = ⊤
  · simp [hEF]
  have hcardDE := (bottleneck_lt_top_iff D E).mp (lt_top_iff_ne_top.mpr hDE)
  have hcardEF := (bottleneck_lt_top_iff E F).mp (lt_top_iff_ne_top.mpr hEF)
  obtain ⟨M, hM⟩ := (bottleneck_optimal_iff D E).mpr hcardDE
  obtain ⟨N, hN⟩ := (bottleneck_optimal_iff E F).mpr hcardEF
  calc
    bottleneck D F ≤ (M.compose N).cost (fun p => p.1) (fun p => p.1)
        (fun b => b.1) (fun b => b.1) := bottleneck_le_matching D F _
    _ ≤ M.cost (fun p => p.1) (fun p => p.1) (fun b => b.1) (fun b => b.1) +
        N.cost (fun p => p.1) (fun p => p.1) (fun b => b.1) (fun b => b.1) :=
          OccurrenceMatching.cost_compose_le M N _ _ _ _ _ _
    _ = bottleneck D E + bottleneck E F := by rw [hM, hN]

private theorem finitePart_offDiagonal_point (D : Diagram ℝ)
    {p : ℝ × ℝ} (hp : p ∈ finitePart D.points) : p.1 ≠ p.2 := by
  obtain ⟨q, hq, hqp⟩ := (Multiset.mem_filterMap _ _).mp hp
  obtain ⟨b, d⟩ := q
  cases d with
  | top => simp [finitePart] at hqp
  | coe d =>
    have hd := D.offDiagonal (b, (d : WithTop ℝ)) hq
    simp [finitePart] at hqp
    subst p
    simpa using hd

private theorem diagonalCost_ne_zero {p : ℝ × ℝ} (h : p.1 ≠ p.2) :
    diagonalCost p ≠ 0 := by
  intro hz
  have hr : |p.2 - p.1| / 2 ≤ 0 := by
    exact ENNReal.ofReal_eq_zero.mp hz
  have hn : p.2 - p.1 ≠ 0 := sub_ne_zero.mpr h.symm
  have hp : 0 < |p.2 - p.1| := abs_pos.mpr hn
  linarith

private theorem finitePairCost_eq_zero_iff (p q : ℝ × ℝ) :
    finitePairCost p q = 0 ↔ p = q := by
  constructor
  · intro h
    have hm : max |p.1 - q.1| |p.2 - q.2| ≤ 0 :=
      ENNReal.ofReal_eq_zero.mp h
    have h₁ : |p.1 - q.1| = 0 :=
      le_antisymm ((le_max_left _ _).trans hm) (abs_nonneg _)
    have h₂ : |p.2 - q.2| = 0 :=
      le_antisymm ((le_max_right _ _).trans hm) (abs_nonneg _)
    exact Prod.ext (sub_eq_zero.mp (abs_eq_zero.mp h₁))
      (sub_eq_zero.mp (abs_eq_zero.mp h₂))
  · rintro rfl
    exact finitePairCost_self p

private theorem essentialPairCost_eq_zero_iff (b c : ℝ) :
    essentialPairCost b c = 0 ↔ b = c := by
  constructor
  · intro h
    have hr : |b - c| ≤ 0 := ENNReal.ofReal_eq_zero.mp h
    exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hr (abs_nonneg _)))
  · rintro rfl
    exact essentialPairCost_self b

/-- A value-preserving equivalence of occurrence labels preserves the multiset,
including multiplicities of equal values. -/
private theorem map_univ_eq_of_equiv {A B C : Type*}
    [Fintype A] [Fintype B] (x : A → C) (y : B → C)
    (e : A ≃ B) (h : ∀ i, y (e i) = x i) :
    (Finset.univ : Finset A).val.map x = (Finset.univ : Finset B).val.map y := by
  classical
  calc
    (Finset.univ : Finset A).val.map x =
        (Finset.univ : Finset A).val.map (y ∘ e) := by
          congr 1
          funext i
          exact (h i).symm
    _ = ((Finset.univ : Finset A).map e.toEmbedding).val.map y := by
          rw [Finset.map_val, Multiset.map_map]
          rfl
    _ = (Finset.univ : Finset B).val.map y := by rw [Finset.map_univ_equiv]

private theorem diagram_eq_of_parts (D E : Diagram ℝ)
    (hf : finitePart D.points = finitePart E.points)
    (he : essentialPart D.points = essentialPart E.points) : D = E := by
  obtain ⟨m, n, z, hD⟩ := orderedQ_surjective D
  obtain ⟨m', n', w, hE⟩ := orderedQ_surjective E
  rw [← hD, ← hE] at hf he ⊢
  exact (orderedQ_eq_iff m n m' n' z w).mpr
    ⟨(finitePart_orderedQ m n z).symm.trans (hf.trans (finitePart_orderedQ m' n' w)),
     (essentialPart_orderedQ m n z).symm.trans
       (he.trans (essentialPart_orderedQ m' n' w))⟩

theorem bottleneck_eq_zero_iff (D E : Diagram ℝ) :
    bottleneck D E = 0 ↔ D = E := by
  classical
  constructor
  · intro hzero
    have hfinite : bottleneck D E < ⊤ := by simp [hzero]
    obtain ⟨M, hM⟩ := (bottleneck_optimal_iff D E).mpr
      ((bottleneck_lt_top_iff D E).mp hfinite)
    have hcost : M.cost (fun p => p.1) (fun p => p.1)
        (fun b => b.1) (fun b => b.1) = 0 := hM.trans hzero
    have hs (i : D.finiteOccurrences) : ∃ j, M.finite i = some j := by
      cases hi : M.finite i with
      | some j => exact ⟨j, rfl⟩
      | none =>
        have hd : diagonalCost i.1 ≤ 0 := by
          simpa [hi, hcost] using OccurrenceMatching.source_le_cost M
            (fun p => p.1) (fun p => p.1) (fun b => b.1) (fun b => b.1) i
        exact (diagonalCost_ne_zero
          (finitePart_offDiagonal_point D (Multiset.coe_mem (x := i)))
          (le_antisymm hd bot_le)).elim
    have ht (j : E.finiteOccurrences) : ∃ i, M.finite i = some j := by
      by_contra hn
      have hd : diagonalCost j.1 ≤ 0 := by
        simpa [hn, hcost] using OccurrenceMatching.target_le_cost M
          (fun p => p.1) (fun p => p.1) (fun b => b.1) (fun b => b.1) j
      exact diagonalCost_ne_zero
        (finitePart_offDiagonal_point E (Multiset.coe_mem (x := j)))
        (le_antisymm hd bot_le)
    let f : D.finiteOccurrences → E.finiteOccurrences := fun i => (hs i).choose
    have hf (i : D.finiteOccurrences) : M.finite i = some (f i) := (hs i).choose_spec
    have hfi : Function.Injective f := by
      intro i i' he
      exact M.finite_injective i i' (f i) (hf i) (he ▸ hf i')
    have hfs : Function.Surjective f := by
      intro j
      obtain ⟨i, hi⟩ := ht j
      exact ⟨i, Option.some.inj ((hf i).symm.trans hi)⟩
    let e : D.finiteOccurrences ≃ E.finiteOccurrences := Equiv.ofBijective f ⟨hfi, hfs⟩
    have hvalue (i : D.finiteOccurrences) : (e i).1 = i.1 := by
      have hc : finitePairCost i.1 (f i).1 = 0 := by
        apply le_antisymm _ bot_le
        simpa [hf i, hcost] using OccurrenceMatching.source_le_cost M
          (fun p => p.1) (fun p => p.1) (fun b => b.1) (fun b => b.1) i
      exact (finitePairCost_eq_zero_iff _ _).mp hc |>.symm
    have hevalue (k : D.essentialOccurrences) :
        (M.essential k).1 = k.1 := by
      have hc : essentialPairCost k.1 (M.essential k).1 = 0 := by
        apply le_antisymm _ bot_le
        simpa [hcost] using OccurrenceMatching.essential_le_cost M
          (fun p => p.1) (fun p => p.1) (fun b => b.1) (fun b => b.1) k
      exact ((essentialPairCost_eq_zero_iff _ _).mp hc).symm
    apply diagram_eq_of_parts
    · calc
        finitePart D.points = (Finset.univ : Finset D.finiteOccurrences).val.map
            (fun p => p.1) := (Multiset.map_univ_coe _).symm
        _ = (Finset.univ : Finset E.finiteOccurrences).val.map (fun p => p.1) :=
          map_univ_eq_of_equiv _ _ e hvalue
        _ = finitePart E.points := Multiset.map_univ_coe _
    · calc
        essentialPart D.points = (Finset.univ : Finset D.essentialOccurrences).val.map
            (fun p => p.1) := (Multiset.map_univ_coe _).symm
        _ = (Finset.univ : Finset E.essentialOccurrences).val.map (fun p => p.1) :=
          map_univ_eq_of_equiv _ _ M.essential hevalue
        _ = essentialPart E.points := Multiset.map_univ_coe _
  · rintro rfl
    exact bottleneck_self D

end TDA.Persistence
