import TDA.Probability.FiniteSampling
import Mathlib.Data.Nat.Choose.Sum

/-!
# Pairwise moment estimates for iid tuples

Only unordered pairs of distinct draw indices contribute. The diagonal vanishes
and symmetry removes the second copy of each pair, giving the sharp factor
`Nat.choose n 2` even when several draws have the same value.
-/

noncomputable section

universe u
namespace TDA.Probability

open scoped ENNReal

variable {X : Type u}

theorem expectation_add (μ : PMF X) (f g : X → ℝ≥0∞) :
    expectation μ (fun x => f x + g x) = expectation μ f + expectation μ g := by
  simp only [expectation, mul_add, ENNReal.tsum_add]

theorem expectation_sum (μ : PMF X) {I : Type*} (s : Finset I) (f : I → X → ℝ≥0∞) :
    expectation μ (fun x => ∑ i ∈ s, f i x) = ∑ i ∈ s, expectation μ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [expectation]
  | @insert i s hi ih => simp [hi, expectation_add, ih]

/-- Every coordinate of the iid tuple has the original law. -/
theorem iid_eval (μ : PMF X) {n : ℕ} (i : Fin n) :
    (iid μ n).map (fun t => t i) = μ := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [iid_succ, PMF.map_bind, PMF.map_comp, Function.comp_def, Fin.cons_zero]
      change (μ.bind fun x => (iid μ n).map (Function.const _ x)) = μ
      simp [PMF.map_const, PMF.bind_pure]
    · simp only [iid_succ, PMF.map_bind, PMF.map_comp, Function.comp_def, Fin.cons_succ]
      simp only [ih, PMF.bind_const]

/-- Sum a pair cost over each unordered pair of distinct tuple positions once. -/
def pairEnergy (c : X → X → ℝ≥0∞) : {n : ℕ} → (Fin n → X) → ℝ≥0∞
  | 0, _ => 0
  | n + 1, t => pairEnergy c (fun i => t i.succ) + ∑ j : Fin n, c (t 0) (t j.succ)

@[simp] theorem pairEnergy_zero (c : X → X → ℝ≥0∞) (t : Fin 0 → X) :
    pairEnergy c t = 0 := rfl

@[simp] theorem pairEnergy_succ (c : X → X → ℝ≥0∞) {n : ℕ} (t : Fin (n+1) → X) :
    pairEnergy c t = pairEnergy c (fun i => t i.succ) + ∑ j : Fin n, c (t 0) (t j.succ) := rfl

/-- Each off-diagonal cost is one of the nonnegative summands of the pair energy. -/
theorem cost_le_pairEnergy (c : X → X → ℝ≥0∞)
    (hc : ∀ x, c x x = 0) (hs : ∀ x y, c x y = c y x)
    {n : ℕ} (t : Fin n → X) (i j : Fin n) : c (t i) (t j) ≤ pairEnergy c t := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun i' => ?_) i
    · refine Fin.cases ?_ (fun j' => ?_) j
      · simp [hc]
      · exact (Finset.single_le_sum (f := fun j : Fin n => c (t 0) (t j.succ))
          (fun _ _ => bot_le) (Finset.mem_univ j')).trans
          (le_add_left le_rfl)
    · refine Fin.cases ?_ (fun j' => ?_) j
      · rw [hs]
        exact (Finset.single_le_sum (f := fun j : Fin n => c (t 0) (t j.succ))
          (fun _ _ => bot_le) (Finset.mem_univ i')).trans
          (le_add_left le_rfl)
      · exact (ih (fun a => t a.succ) i' j').trans (le_add_right le_rfl)

/-- The expectation of the unordered-pair energy is exactly the two-draw moment
multiplied by the number of distinct pairs. No replacement restriction is imposed. -/
theorem expectation_pairEnergy (μ : PMF X) (c : X → X → ℝ≥0∞) (n : ℕ) :
    expectation (iid μ n) (pairEnergy c) =
      (n.choose 2 : ℝ≥0∞) * expectation μ (fun x => expectation μ (c x)) := by
  induction n with
  | zero => simp [expectation]
  | succ n ih =>
    rw [iid_succ, expectation_bind]
    simp only [expectation_map, pairEnergy_succ, Fin.cons_zero, Fin.cons_succ,
      expectation_add, expectation_sum]
    have heval (x : X) (j : Fin n) :
        expectation (iid μ n) (fun t => c x (t j)) = expectation μ (c x) := by
      rw [← expectation_map, iid_eval]
    simp only [heval, ih, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    rw [expectation_const]
    rw [← add_mul]
    congr 1
    norm_cast
    simp [Nat.choose_succ_succ, Nat.choose_one_right, Nat.add_comm]

/-- Maximum over all entries of a finite tuple's pair-cost matrix. -/
def pairMaximum (c : X → X → ℝ≥0∞) {n : ℕ} (t : Fin n → X) : ℝ≥0∞ :=
  Finset.univ.sup (fun ij : Fin n × Fin n => c (t ij.1) (t ij.2))

theorem cost_le_pairMaximum (c : X → X → ℝ≥0∞) {n : ℕ} (t : Fin n → X)
    (i j : Fin n) : c (t i) (t j) ≤ pairMaximum c t := by
  exact Finset.le_sup (f := fun ij : Fin n × Fin n => c (t ij.1) (t ij.2))
    (Finset.mem_univ (i, j))

/-- The p-th power of a maximum is bounded by the sum of p-th powers over
unordered pairs, for every positive real exponent. -/
theorem pairMaximum_rpow_le_pairEnergy (c : X → X → ℝ≥0∞)
    (hc : ∀ x, c x x = 0) (hs : ∀ x y, c x y = c y x)
    {p : ℝ} (hp : 0 < p) {n : ℕ} (t : Fin n → X) :
    pairMaximum c t ^ p ≤ pairEnergy (fun x y => c x y ^ p) t := by
  rw [← ENNReal.le_rpow_inv_iff hp]
  apply Finset.sup_le
  intro ij _
  rw [ENNReal.le_rpow_inv_iff hp]
  exact cost_le_pairEnergy _ (fun x => by simp [hc, hp])
    (fun x y => by rw [hs]) t ij.1 ij.2

/-- Sharp iid bound on the moment of the entire distance-matrix maximum. -/
theorem expectation_pairMaximum_rpow_le (μ : PMF X) (c : X → X → ℝ≥0∞)
    (hc : ∀ x, c x x = 0) (hs : ∀ x y, c x y = c y x)
    {p : ℝ} (hp : 0 < p) (n : ℕ) :
    expectation (iid μ n) (fun t => pairMaximum c t ^ p) ≤
      (n.choose 2 : ℝ≥0∞) * expectation μ (fun x => expectation μ (fun y => c x y ^ p)) := by
  exact (expectation_mono _ (fun t => pairMaximum_rpow_le_pairEnergy c hc hs hp t)).trans_eq
    (expectation_pairEnergy μ _ n)

/-- A tuple with positive probability uses only positive-probability values. -/
theorem mem_support_of_mem_support_iid (μ : PMF X) {n : ℕ} {t : Fin n → X}
    (ht : t ∈ (iid μ n).support) (i : Fin n) : t i ∈ μ.support := by
  rw [← iid_eval μ i]
  exact (PMF.mem_support_map_iff _ _ _).mpr ⟨t, ht, rfl⟩

/-- The maximum between draws in a supported tuple is bounded by the two-draw
essential supremum, independent of the number of draws. -/
theorem essentialSup_pairMaximum_le (μ : PMF X) (c : X → X → ℝ≥0∞) (n : ℕ) :
    essentialSup (iid μ n) (pairMaximum c) ≤
      essentialSup μ (fun x => essentialSup μ (c x)) := by
  apply iSup_le
  intro t
  apply iSup_le
  intro ht
  apply Finset.sup_le
  intro ij _
  apply le_iSup_of_le (t ij.1)
  apply le_iSup_of_le (mem_support_of_mem_support_iid μ ht ij.1)
  apply le_iSup_of_le (t ij.2)
  exact le_iSup_of_le (mem_support_of_mem_support_iid μ ht ij.2) le_rfl

end TDA.Probability
