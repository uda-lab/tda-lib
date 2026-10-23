import TDA.Persistence.DiagramBottleneck

/-!
# Finite additive features and partial matchings

A feature is summed over occurrence labels, so equal point values contribute repeatedly.
The bound below uses the existing partial-injection matching API with empty essential
parts. It charges matched pairs and both unmatched parts in the birth–death maximum norm.

This elementary normed-group interface supplies the finite-sum step of a possible
persistence-image construction. It does not prove Gaussian integrability, a translation
estimate, or stability of pixel integrals. Those require separate analytic proofs.
Adams et al., *Persistence Images*, JMLR 18(8), 2017, §§4–5 motivates the sum argument;
Kusano–Fukumizu–Hiraoka, JMLR 18(189), 2018, §4.1.3 distinguishes pixel and RKHS norms.
-/

namespace TDA.Persistence

open scoped Classical

/-- Birth–persistence coordinates; the input coordinates are birth and death. -/
def birthPersistence (p : ℝ × ℝ) : ℝ × ℝ := (p.1, p.2 - p.1)

theorem birthPersistence_snd_pos {p : ℝ × ℝ} (hp : p.1 < p.2) :
    0 < (birthPersistence p).2 := sub_pos.mpr hp

/-- Products of real normed spaces use the maximum norm, not the Euclidean norm. -/
theorem norm_birthPersistence_sub_le (p q : ℝ × ℝ) :
    ‖birthPersistence p - birthPersistence q‖ ≤ 2 * ‖p - q‖ := by
  simp only [birthPersistence, Prod.norm_def, Prod.fst_sub, Prod.snd_sub,
    Real.norm_eq_abs]
  have h₁ := le_max_left |p.1 - q.1| |p.2 - q.2|
  have h₂ := le_max_right |p.1 - q.1| |p.2 - q.2|
  have hn := abs_nonneg (p.1 - q.1)
  have ht : |(p.2 - q.2) - (p.1 - q.1)| ≤ |p.2 - q.2| + |p.1 - q.1| := by
    simpa only [sub_zero, zero_sub, abs_neg] using
      abs_sub_le (p.2 - q.2) 0 (p.1 - q.1)
  apply max_le
  · linarith
  · rw [show p.2 - p.1 - (q.2 - q.1) = (p.2 - q.2) - (p.1 - q.1) by ring]
    linarith

@[simp] theorem finitePairCost_toReal (p q : ℝ × ℝ) :
    (finitePairCost p q).toReal = ‖p - q‖ := by
  rw [finitePairCost, ENNReal.toReal_ofReal
    (le_trans (abs_nonneg _) (le_max_left _ _))]
  simp only [Prod.norm_def, Prod.fst_sub, Prod.snd_sub, Real.norm_eq_abs]

@[simp] theorem diagonalCost_toReal (p : ℝ × ℝ) :
    (diagonalCost p).toReal = |p.2 - p.1| / 2 := by
  exact ENNReal.toReal_ofReal (div_nonneg (abs_nonneg _) (by norm_num))

/-- Sum over occurrences, with no deduplication of equal point values. -/
noncomputable def finiteFeatureSum {I E : Type*} [Fintype I] [AddCommMonoid E]
    (F : ℝ × ℝ → E) (x : I → ℝ × ℝ) : E := ∑ i, F (x i)

/-- Changing occurrence labels preserves the sum, without identifying equal values. -/
theorem finiteFeatureSum_reindex {I J E : Type*} [Fintype I] [Fintype J]
    [AddCommMonoid E] (e : I ≃ J) (F : ℝ × ℝ → E) (y : J → ℝ × ℝ) :
    finiteFeatureSum F (y ∘ e) = finiteFeatureSum F y :=
  e.sum_comp (fun j => F (y j))

@[simp] theorem finiteFeatureSum_empty {I E : Type*} [Fintype I] [IsEmpty I]
    [AddCommMonoid E] (F : ℝ × ℝ → E) (x : I → ℝ × ℝ) :
    finiteFeatureSum F x = 0 := Fintype.sum_empty _

namespace OccurrenceMatching

variable {I J : Type*} [Fintype I] [Fintype J]

/-- Total finite cost of one partial matching. Essential occurrences are absent.
This is a sum of real costs; it is not the existing bottleneck maximum or an infimum. -/
noncomputable def totalFiniteCost (M : OccurrenceMatching I J PEmpty.{1} PEmpty.{1})
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) : ℝ := by
  classical
  exact (∑ i, match M.finite i with
      | some j => (finitePairCost (x i) (y j)).toReal
      | none => (diagonalCost (x i)).toReal) +
    ∑ j, if ∃ i, M.finite i = some j then 0 else (diagonalCost (y j)).toReal

theorem totalFiniteCost_nonneg (M : OccurrenceMatching I J PEmpty.{1} PEmpty.{1})
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) : 0 ≤ M.totalFiniteCost x y := by
  classical
  apply add_nonneg
  · apply Finset.sum_nonneg
    intro i _
    cases M.finite i <;> exact ENNReal.toReal_nonneg
  · apply Finset.sum_nonneg
    intro j _
    split_ifs <;> positivity

/-- Partial injectivity counts each matched target contribution exactly once. -/
theorem sum_matched {E : Type*} [AddCommMonoid E]
    (M : OccurrenceMatching I J PEmpty.{1} PEmpty.{1}) (g : J → E) :
    (∑ i, match M.finite i with | some j => g j | none => 0) =
      ∑ j, if ∃ i, M.finite i = some j then g j else 0 := by
  classical
  calc
    _ = ∑ i, ∑ j, if M.finite i = some j then g j else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      cases M.finite i <;> simp
    _ = ∑ j, ∑ i, if M.finite i = some j then g j else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : ∃ i, M.finite i = some j
      · obtain ⟨i, hi⟩ := hj
        rw [if_pos ⟨i, hi⟩]
        rw [Finset.sum_eq_single i]
        · simp [hi]
        · intro k _ hki
          have hk : M.finite k ≠ some j := fun hk =>
            hki (M.finite_injective k i j hk hi)
          simp [hk]
        · simp
      · simp [show ∀ i, M.finite i ≠ some j from fun i hi => hj ⟨i, hi⟩]

/-- Split a sum difference into source residuals and the unmatched target sum.
A source residual is a matched difference or a single unmatched source feature. -/
theorem sum_sub_eq_residual_sub_unmatched {E : Type*} [AddCommGroup E]
    (M : OccurrenceMatching I J PEmpty.{1} PEmpty.{1}) (f : I → E) (g : J → E) :
    (∑ i, f i) - ∑ j, g j =
      (∑ i, (f i - (match M.finite i with | some j => g j | none => 0))) -
        ∑ j, if ∃ i, M.finite i = some j then 0 else g j := by
  classical
  have hsplit : (∑ j, if ∃ i, M.finite i = some j then g j else 0) +
      (∑ j, if ∃ i, M.finite i = some j then 0 else g j) = ∑ j, g j := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> simp
  rw [Finset.sum_sub_distrib, M.sum_matched g]
  rw [← hsplit]
  abel

/-- Every finite partial matching bounds the difference of additive features.
Only positive finite birth–death pairs are required to satisfy the pointwise estimates.
No optimal matching, Gaussian estimate or transport-distance theorem is assumed. -/
theorem norm_featureSum_sub_le {E : Type*} [NormedAddCommGroup E]
    (M : OccurrenceMatching I J PEmpty.{1} PEmpty.{1})
    (F : ℝ × ℝ → E) (L : ℝ) (_hL : 0 ≤ L)
    (hpair : ∀ p q : ℝ × ℝ, p.1 < p.2 → q.1 < q.2 →
      ‖F p - F q‖ ≤ L * ‖p - q‖)
    (hdiag : ∀ p : ℝ × ℝ, p.1 < p.2 → ‖F p‖ ≤ L * (diagonalCost p).toReal)
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ)
    (hx : ∀ i, (x i).1 < (x i).2) (hy : ∀ j, (y j).1 < (y j).2) :
    ‖finiteFeatureSum F x - finiteFeatureSum F y‖ ≤ L * M.totalFiniteCost x y := by
  classical
  unfold finiteFeatureSum
  rw [M.sum_sub_eq_residual_sub_unmatched]
  calc
    _ ≤ ‖∑ i, (F (x i) - (match M.finite i with | some j => F (y j) | none => 0))‖ +
        ‖∑ j, if ∃ i, M.finite i = some j then 0 else F (y j)‖ := norm_sub_le _ _
    _ ≤ (∑ i, ‖F (x i) -
          (match M.finite i with | some j => F (y j) | none => 0)‖) +
        ∑ j, ‖if ∃ i, M.finite i = some j then 0 else F (y j)‖ :=
      add_le_add (norm_sum_le _ _) (norm_sum_le _ _)
    _ ≤ (∑ i, L * (match M.finite i with
          | some j => (finitePairCost (x i) (y j)).toReal
          | none => (diagonalCost (x i)).toReal)) +
        ∑ j, L * (if ∃ i, M.finite i = some j then 0 else (diagonalCost (y j)).toReal) := by
      apply add_le_add
      · apply Finset.sum_le_sum
        intro i _
        cases h : M.finite i with
        | none => simpa [h] using hdiag (x i) (hx i)
        | some j => simpa [h] using hpair (x i) (y j) (hx i) (hy j)
      · apply Finset.sum_le_sum
        intro j _
        split_ifs
        · simp
        · exact hdiag (y j) (hy j)
    _ = L * M.totalFiniteCost x y := by
      simp only [totalFiniteCost, Finset.mul_sum, mul_add]

end OccurrenceMatching
end TDA.Persistence
