import TDA.Persistence.PersistenceMeasureBox
import TDA.Persistence.DiagramBottleneck
import Mathlib.Combinatorics.Hall.Basic

/-!
# Local matching from persistence box inequalities

Finite occurrence families retain repeated point values. Small box comparisons,
when distinct source points are separated, give disjoint target clusters with the
correct multiplicities. Hall's theorem then constructs an occurrence matching.
This is the finite local step in CDSGO, arXiv:1207.3674v3, Theorem 4.25, Part 2(ii).
The separation assumption is essential to this local statement: Example 4.26
rules out a general bottleneck bound from a single pair of box inequalities.
-/

universe u v

namespace TDA.Persistence.PersistenceMeasureMatching

open scoped BigOperators

variable {I : Type u} {J : Type v} [Fintype I] [Fintype J]

/-- Number of occurrences in a closed maximum-norm square. -/
noncomputable def finiteBoxCount (x : I → ℝ × ℝ) (p : ℝ × ℝ) (r : ℝ) : ℕ := by
  classical
  exact (Finset.univ.filter (fun i => dist (x i) p ≤ r)).card

private theorem exists_small_radius (y : J → ℝ × ℝ) (p : ℝ × ℝ)
    (r ρ : ℝ) (hρ : 0 < ρ) :
    ∃ t, 0 < t ∧ t < ρ ∧ ∀ j, dist (y j) p ≤ r + t → dist (y j) p ≤ r := by
  classical
  have aux : ∀ s : Finset J, ∃ t, 0 < t ∧ t < ρ ∧
      ∀ j ∈ s, dist (y j) p ≤ r + t → dist (y j) p ≤ r := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨ρ / 2, by positivity, by linarith, by simp⟩
    | @insert j s hj ih =>
      obtain ⟨t, ht, htρ, hts⟩ := ih
      by_cases hd : dist (y j) p ≤ r
      · refine ⟨t, ht, htρ, ?_⟩
        intro l hl hlr
        rcases Finset.mem_insert.mp hl with rfl | hl
        · exact hd
        · exact hts l hl hlr
      · have hd' : r < dist (y j) p := lt_of_not_ge hd
        refine ⟨min t ((dist (y j) p - r) / 2), lt_min ht (by linarith),
          lt_of_le_of_lt (min_le_left _ _) htρ, ?_⟩
        intro l hl hlr
        rcases Finset.mem_insert.mp hl with rfl | hl
        · have := min_le_right t ((dist (y l) p - r) / 2)
          linarith
        · exact hts l hl (hlr.trans (add_le_add le_rfl (min_le_left _ _)))
  obtain ⟨t, ht, htρ, hts⟩ := aux Finset.univ
  exact ⟨t, ht, htρ, fun j => hts j (Finset.mem_univ _)⟩

/-- Finite support lets positive-radius box inequalities pass to closed limiting squares,
including radius zero. Only the expanded square must remain above the diagonal. -/
theorem finiteBoxCount_box_le (x : I → ℝ × ℝ) (y : J → ℝ × ℝ)
    {ε : ℝ} (hbox : ∀ (p : ℝ × ℝ) (r : ℝ), 0 < r →
      2 * (r + ε) < p.2 - p.1 → finiteBoxCount x p r ≤ finiteBoxCount y p (r + ε))
    (p : ℝ × ℝ) {r : ℝ} (hr : 0 ≤ r) (hgap : 2 * (r + ε) < p.2 - p.1) :
    finiteBoxCount x p r ≤ finiteBoxCount y p (r + ε) := by
  classical
  obtain ⟨t, ht, htρ, hty⟩ := exists_small_radius y p (r + ε)
    ((p.2 - p.1) / 2 - (r + ε)) (by linarith)
  have h := hbox p (r + t) (by linarith) (by linarith)
  refine (Finset.card_le_card ?_).trans (h.trans (Finset.card_le_card ?_))
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    linarith
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    apply hty j
    linarith

private theorem hall_injection_of_separated_counts
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) {ε : ℝ}
    (hsep : ∀ i i', x i ≠ x i' → 2 * ε < dist (x i) (x i'))
    (hcount : ∀ i, (Finset.univ.filter (fun i' => x i' = x i)).card ≤
      (Finset.univ.filter (fun j => dist (y j) (x i) ≤ ε)).card) :
    ∃ f : I → J, Function.Injective f ∧ ∀ i, dist (y (f i)) (x i) ≤ ε := by
  classical
  apply (Fintype.all_card_le_filter_rel_iff_exists_injective
    (fun i j => dist (y j) (x i) ≤ ε)).mp
  intro s
  let P := s.image x
  let N := fun p : ℝ × ℝ => Finset.univ.filter (fun j => dist (y j) p ≤ ε)
  have hdis : (P : Set (ℝ × ℝ)).PairwiseDisjoint N := by
    intro p hp q hq hpq
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨i', hi', rfl⟩ := Finset.mem_image.mp hq
    apply Finset.disjoint_left.mpr
    intro j hj hj'
    have hji := (Finset.mem_filter.mp hj).2
    have hji' := (Finset.mem_filter.mp hj').2
    have ht := dist_triangle (x i) (y j) (x i')
    rw [dist_comm (x i) (y j)] at ht
    have hs := hsep i i' hpq
    linarith
  calc
    s.card = ∑ p ∈ P, (s.filter (fun i => x i = p)).card :=
      Finset.card_eq_sum_card_image x s
    _ ≤ ∑ p ∈ P, (N p).card := by
      apply Finset.sum_le_sum
      intro p hp
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
      exact (Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ s))).trans
        (hcount i)
    _ = (P.biUnion N).card := (Finset.card_biUnion hdis).symm
    _ = (Finset.univ.filter (fun j => ∃ i ∈ s, dist (y j) (x i) ≤ ε)).card := by
      congr 1
      ext j
      simp only [P, N, Finset.mem_biUnion, Finset.mem_image, Finset.mem_filter,
        Finset.mem_univ, true_and]
      aesop

private theorem separated_cluster_counts
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (hgap : ∀ i, 4 * ε < (x i).2 - (x i).1)
    (hsep : ∀ i i', x i ≠ x i' → 2 * ε < dist (x i) (x i'))
    (hxy : ∀ p r, 0 < r → 2 * (r + ε) < p.2 - p.1 →
      finiteBoxCount x p r ≤ finiteBoxCount y p (r + ε))
    (hyx : ∀ p r, 0 < r → 2 * (r + ε) < p.2 - p.1 →
      finiteBoxCount y p r ≤ finiteBoxCount x p (r + ε))
    (i : I) :
    (Finset.univ.filter (fun j => dist (y j) (x i) ≤ ε)).card =
      (Finset.univ.filter (fun i' => x i' = x i)).card := by
  classical
  have hzero : finiteBoxCount x (x i) 0 =
      (Finset.univ.filter (fun i' => x i' = x i)).card := by
    simp [finiteBoxCount]
  have htwo : finiteBoxCount x (x i) (ε + ε) =
      (Finset.univ.filter (fun i' => x i' = x i)).card := by
    unfold finiteBoxCount
    congr 1
    ext i'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h
      by_contra hn
      have := hsep i' i hn
      linarith
    · rintro h
      simp only [h, dist_self]
      linarith
  apply le_antisymm
  · have h := finiteBoxCount_box_le y x hyx (x i) hε (by have := hgap i; linarith)
    rw [htwo] at h
    exact h
  · have h := finiteBoxCount_box_le x y hxy (x i) (le_refl 0)
      (by have := hgap i; linarith)
    rw [hzero, zero_add] at h
    exact h

/-- The finite local matching step: separated long source points and two-sided box
bounds give a matching of cost at most `ε`. Repeated occurrences are retained, all
source occurrences are matched, and every unmatched target is close to the diagonal.
The strict source bounds are the local small-parameter hypotheses of CDSGO,
Theorem 4.25, Part 2(ii); they cannot be dropped using box comparisons alone. -/
theorem exists_matching_of_separated_box_bounds
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (hy : ∀ j, (y j).1 ≤ (y j).2)
    (hgap : ∀ i, 4 * ε < (x i).2 - (x i).1)
    (hsep : ∀ i i', x i ≠ x i' → 2 * ε < dist (x i) (x i'))
    (hxy : ∀ p r, 0 < r → 2 * (r + ε) < p.2 - p.1 →
      finiteBoxCount x p r ≤ finiteBoxCount y p (r + ε))
    (hyx : ∀ p r, 0 < r → 2 * (r + ε) < p.2 - p.1 →
      finiteBoxCount y p r ≤ finiteBoxCount x p (r + ε)) :
    ∃ M : OccurrenceMatching I J PEmpty.{1} PEmpty.{1},
      (∀ i, ∃ j, M.finite i = some j) ∧
      M.cost x y PEmpty.elim PEmpty.elim ≤ ENNReal.ofReal ε := by
  classical
  have hcounts := separated_cluster_counts x y hε hgap hsep hxy hyx
  obtain ⟨f, hf, hclose⟩ := hall_injection_of_separated_counts x y hsep
    (fun i => (hcounts i).ge)
  have hcover : ∀ i j, dist (y j) (x i) ≤ ε → ∃ i', f i' = j := by
    intro i j hj
    let A := Finset.univ.filter (fun i' => x i' = x i)
    let B := Finset.univ.filter (fun j => dist (y j) (x i) ≤ ε)
    have hsub : A.image f ⊆ B := by
      intro j' hj'
      obtain ⟨i', hi', rfl⟩ := Finset.mem_image.mp hj'
      have hi := (Finset.mem_filter.mp hi').2
      simp only [B, Finset.mem_filter, Finset.mem_univ, true_and]
      simpa only [hi] using hclose i'
    have heq : A.image f = B := Finset.eq_of_subset_of_card_le hsub (by
      rw [Finset.card_image_of_injective _ hf]
      exact (hcounts i).le)
    have hj' : j ∈ A.image f := heq ▸ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩)
    obtain ⟨i', _, hi'⟩ := Finset.mem_image.mp hj'
    exact ⟨i', hi'⟩
  have hshort : ∀ j, (¬ ∃ i, f i = j) → (y j).2 - (y j).1 ≤ 2 * ε := by
    intro j hj
    by_contra hlong
    have hlong' : 2 * ε < (y j).2 - (y j).1 := lt_of_not_ge hlong
    have h := finiteBoxCount_box_le y x hyx (y j) (le_refl 0) (by simpa using hlong')
    have hpos : 0 < finiteBoxCount y (y j) 0 := by
      apply Finset.card_pos.mpr
      exact ⟨j, by simp⟩
    have hpos' : 0 < finiteBoxCount x (y j) ε := by simpa only [zero_add] using hpos.trans_le h
    obtain ⟨i, hi⟩ := Finset.card_pos.mp hpos'
    have hi' : dist (y j) (x i) ≤ ε := by
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and, dist_comm] using hi
    exact hj (hcover i j hi')
  let M : OccurrenceMatching I J PEmpty.{1} PEmpty.{1} := {
    finite := fun i => some (f i)
    finite_injective := by
      intro i i' j hi hi'
      exact hf ((Option.some.inj hi).trans (Option.some.inj hi').symm)
    essential := Equiv.refl PEmpty }
  refine ⟨M, fun i => ⟨f i, rfl⟩, ?_⟩
  apply max_le
  · apply Finset.sup_le
    intro i _
    change finitePairCost (x i) (y (f i)) ≤ ENNReal.ofReal ε
    apply ENNReal.ofReal_le_ofReal
    have h := hclose i
    simpa only [dist_comm (y (f i)) (x i), Prod.dist_eq, Real.dist_eq] using h
  · apply max_le
    · apply Finset.sup_le
      intro j _
      change (if ∃ i, some (f i) = some j then 0 else diagonalCost (y j)) ≤ _
      split_ifs with hj
      · exact zero_le
      · have hn : ¬ ∃ i, f i = j := by simpa using hj
        apply ENNReal.ofReal_le_ofReal
        rw [abs_of_nonneg (sub_nonneg.mpr (hy j))]
        have := hshort j hn
        linarith
    · apply Finset.sup_le
      intro k _
      exact PEmpty.elim k

end TDA.Persistence.PersistenceMeasureMatching
