import TDA.Persistence.DiagramBottleneckScaling
import TDA.Persistence.DiagramBottleneckTranslation

set_option autoImplicit false

/-!
# Total persistence of finite bars

`Diagram.totalPersistence p D` sums `|d - b|^p` over the finite bars of `D`; essential
bars are excluded, as in the kernel embeddings.  This is the natural natural-exponent
form of KFH18 §2.2 `Pers_p`, together with its card-times-maximum remark.  The
bar-count bounds below make this estimate size-uniform for configurations of at most
`N` points.  They feed KFH18 equations (8)--(9), but do not prove KFH18 Lemma 4,
(W1), Proposition 8, or Theorem 9.  Vanishing of essential bars in positive degree
is not claimed here.
-/

universe u

namespace TDA.Persistence

/-- The degree-`p` total persistence, summing absolute finite bar lengths only. -/
noncomputable def Diagram.totalPersistence (p : ℕ) (D : Diagram ℝ) : ℝ :=
  ((finitePart D.points).map (fun x => |x.2 - x.1| ^ p)).sum

/-- Total persistence is nonnegative. -/
theorem totalPersistence_nonneg (D : Diagram ℝ) (p : ℕ) :
    0 ≤ D.totalPersistence p := by
  unfold Diagram.totalPersistence
  apply Multiset.sum_nonneg
  intro y hy
  obtain ⟨x, _, rfl⟩ := Multiset.mem_map.mp hy
  exact pow_nonneg (abs_nonneg _) _

/-- At exponent zero, total persistence is exactly the finite occurrence count. -/
theorem totalPersistence_zero (D : Diagram ℝ) :
    D.totalPersistence 0 = Fintype.card D.finiteOccurrences := by
  simp [Diagram.totalPersistence, Multiset.map_const', Multiset.card_coe]

/-- A diagram with no finite bars has zero total persistence. -/
theorem totalPersistence_empty (D : Diagram ℝ) (p : ℕ)
    (h : finitePart D.points = 0) : D.totalPersistence p = 0 := by
  simp [Diagram.totalPersistence, h]

/-- Positive scaling multiplies degree-`p` total persistence by `c^p`. -/
theorem totalPersistence_scale (D : Diagram ℝ) (p : ℕ) {c : ℝ} (hc : 0 < c) :
    (D.scale c hc).totalPersistence p = c ^ p * D.totalPersistence p := by
  unfold Diagram.totalPersistence
  rw [Diagram.scale, finitePart_map_points, Multiset.map_map]
  have hmap :
      (finitePart D.points).map
          ((fun x => |x.2 - x.1| ^ p) ∘
            fun x => ((OrderIso.mulLeft₀ c hc).toOrderEmbedding x.1,
              (OrderIso.mulLeft₀ c hc).toOrderEmbedding x.2)) =
        (finitePart D.points).map (fun x => c ^ p * |x.2 - x.1| ^ p) := by
    apply Multiset.map_congr rfl
    intro x hx
    show |c * x.2 - c * x.1| ^ p = c ^ p * |x.2 - x.1| ^ p
    have hx' : c * x.2 - c * x.1 = c * (x.2 - x.1) := by ring
    rw [hx', abs_mul, abs_of_pos hc, mul_pow]
  rw [hmap, Multiset.sum_map_mul_left]

/-- Translating both endpoints leaves degree-`p` total persistence unchanged. -/
theorem totalPersistence_translateDiagram (D : Diagram ℝ) (a : ℝ) (p : ℕ) :
    (translateDiagram D a).totalPersistence p = D.totalPersistence p := by
  unfold Diagram.totalPersistence
  rw [translateDiagram_eq_map, finitePart_map_points, Multiset.map_map]
  apply congrArg (fun s : Multiset ℝ => s.sum)
  apply Multiset.map_congr rfl
  intro x hx
  show |(x.2 + a) - (x.1 + a)| ^ p = |x.2 - x.1| ^ p
  have hx' : (x.2 + a) - (x.1 + a) = x.2 - x.1 := by ring
  rw [hx']

/-- The card-times-maximum total-persistence estimate for finite coordinates. -/
theorem totalPersistence_le_card_mul_pow (D : Diagram ℝ) (p : ℕ) (M : ℝ)
    (hM : ∀ x ∈ finitePart D.points, |x.2 - x.1| ≤ M) (_hM0 : 0 ≤ M) :
    D.totalPersistence p ≤ Fintype.card D.finiteOccurrences * M ^ p := by
  have hsum : ∀ s : Multiset (ℝ × ℝ),
        (∀ x ∈ s, |x.2 - x.1| ≤ M) →
        (s.map (fun x => |x.2 - x.1| ^ p)).sum ≤ (s.card : ℝ) * M ^ p := by
    intro s
    refine Multiset.induction_on s ?_ ?_
    · intro hs
      simp
    · intro x s ih hs
      have hx : |x.2 - x.1| ^ p ≤ M ^ p :=
        pow_le_pow_left₀ (abs_nonneg _) (hs x (by simp)) p
      have hs' : ∀ y ∈ s, |y.2 - y.1| ≤ M := by
        intro y hy
        exact hs y (by simp [hy])
      have htail := ih hs'
      rw [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons, Nat.cast_add,
        Nat.cast_one, add_one_mul]
      linarith
  unfold Diagram.totalPersistence
  have hcard : Fintype.card D.finiteOccurrences = (finitePart D.points).card :=
    Multiset.card_coe _
  rw [hcard]
  exact hsum (finitePart D.points) hM

/-- The card-times-maximum estimate when every finite coordinate lies in `[0,M]`. -/
theorem totalPersistence_le_of_coordinates_mem_Icc (D : Diagram ℝ) (p : ℕ) (M : ℝ)
    (h : ∀ x ∈ finitePart D.points,
      x.1 ∈ Set.Icc 0 M ∧ x.2 ∈ Set.Icc 0 M) :
    D.totalPersistence p ≤ Fintype.card D.finiteOccurrences * M ^ p := by
  by_cases hs : finitePart D.points = 0
  · have hcard : Fintype.card D.finiteOccurrences = 0 := by
      rw [Multiset.card_coe, hs]
      simp
    simp [Diagram.totalPersistence, hs, hcard]
  · obtain ⟨x, hx⟩ := Multiset.exists_mem_of_ne_zero hs
    have hM0 : 0 ≤ M := le_trans (h x hx).1.1 (h x hx).1.2
    apply totalPersistence_le_card_mul_pow D p M _ hM0
    intro y hy
    rw [abs_sub_le_iff]
    constructor <;> linarith [(h y hy).1.1, (h y hy).1.2, (h y hy).2.1, (h y hy).2.2]

end TDA.Persistence
