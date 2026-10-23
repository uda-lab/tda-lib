import TDA.Persistence.PersistenceMeasureMatching

/-! A finite local matching fixture with two copies of a long point, translated
long target points, and an additional short target interval. -/

namespace TDA.Persistence.PersistenceMeasureMatchingExamples

open PersistenceMeasureMatching

private def source (_ : Fin 2) : ℝ × ℝ := (0, 10)

private def target (j : Fin 3) : ℝ × ℝ := if j = 2 then (0, 1) else (1, 11)

private theorem forward_boxes (p : ℝ × ℝ) (r : ℝ) :
    finiteBoxCount source p r ≤ finiteBoxCount target p (r + 1) := by
  classical
  apply Finset.card_le_card_of_injOn Fin.castSucc
  · intro i hi
    have hi' : dist (source i) p ≤ r := (Finset.mem_filter.mp hi).2
    have ht : dist (target i.castSucc) (source i) ≤ 1 := by
      fin_cases i <;> norm_num [target, source, Prod.dist_eq, Real.dist_eq, Fin.ext_iff]
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    have := dist_triangle (target i.castSucc) (source i) p
    linarith
  · intro i _ i' _ h
    exact Fin.castSucc_injective _ h

private theorem reverse_boxes (p : ℝ × ℝ) (r : ℝ)
    (hgap : 2 * (r + 1) < p.2 - p.1) :
    finiteBoxCount target p r ≤ finiteBoxCount source p (r + 1) := by
  classical
  let f : Fin 3 → Fin 2 := fun j => ⟨j.val % 2, Nat.mod_lt _ (by decide)⟩
  have hlong : ∀ j, dist (target j) p ≤ r → j ≠ 2 := by
    intro j hj heq
    subst j
    simp [target, Prod.dist_eq, Real.dist_eq, abs_le] at hj
    linarith
  apply Finset.card_le_card_of_injOn f
  · intro j hj
    have hj' := (Finset.mem_filter.mp hj).2
    have hne := hlong j hj'
    have ht : dist (source (f j)) (target j) ≤ 1 := by
      norm_num [source, target, hne, Prod.dist_eq, Real.dist_eq]
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    have := dist_triangle (source (f j)) (target j) p
    linarith
  · intro j hj j' hj' heq
    have hne := hlong j (Finset.mem_filter.mp hj).2
    have hne' := hlong j' (Finset.mem_filter.mp hj').2
    fin_cases j <;> fin_cases j' <;> norm_num [f, Fin.ext_iff] at *

/-- Repeated source occurrences can move by a nonzero amount while an extra short
interval is left for the diagonal. Both box bounds are verified directly. -/
theorem duplicated_shift_with_short_target :
    ∃ M : OccurrenceMatching (Fin 2) (Fin 3) PEmpty.{1} PEmpty.{1},
      (∀ i, ∃ j, M.finite i = some j) ∧
      M.cost (fun _ => (0, 10)) (fun j => if j = 2 then (0, 1) else (1, 11))
        PEmpty.elim PEmpty.elim ≤ 1 := by
  have h := exists_matching_of_separated_box_bounds source target (ε := 1)
    (by norm_num) (by intro j; unfold target; split_ifs <;> norm_num)
    (by intro i; norm_num [source]) (by intro i i' hn; exact (hn rfl).elim)
    (fun p r _ _ => forward_boxes p r) (fun p r _ hgap => reverse_boxes p r hgap)
  change ∃ M : OccurrenceMatching (Fin 2) (Fin 3) PEmpty.{1} PEmpty.{1},
    (∀ i, ∃ j, M.finite i = some j) ∧ M.cost source target PEmpty.elim PEmpty.elim ≤ 1
  simpa only [ENNReal.ofReal_one] using h

end TDA.Persistence.PersistenceMeasureMatchingExamples
