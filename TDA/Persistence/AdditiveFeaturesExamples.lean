import TDA.Persistence.AdditiveFeatures

/-! A nonzero scalar feature tests matched, unmatched, repeated and empty inputs. -/

namespace TDA.Persistence
namespace AdditiveFeaturesExamples

private noncomputable def halfPersistence (p : ℝ × ℝ) : ℝ := (p.2 - p.1) / 2

private theorem halfPersistence_sub_le (p q : ℝ × ℝ) :
    ‖halfPersistence p - halfPersistence q‖ ≤ ‖p - q‖ := by
  have he : halfPersistence p - halfPersistence q =
      ((p.2 - q.2) - (p.1 - q.1)) / 2 := by unfold halfPersistence; ring
  rw [he, Real.norm_eq_abs, abs_div]
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  simp only [Prod.norm_def, Prod.fst_sub, Prod.snd_sub, Real.norm_eq_abs]
  have ht : |(p.2 - q.2) - (p.1 - q.1)| ≤ |p.2 - q.2| + |p.1 - q.1| := by
    simpa only [sub_zero, zero_sub, abs_neg] using
      abs_sub_le (p.2 - q.2) 0 (p.1 - q.1)
  have h₁ := le_max_left |p.1 - q.1| |p.2 - q.2|
  have h₂ := le_max_right |p.1 - q.1| |p.2 - q.2|
  linarith

private theorem halfPersistence_norm (p : ℝ × ℝ) :
    ‖halfPersistence p‖ = (diagonalCost p).toReal := by
  simp [halfPersistence, Real.norm_eq_abs]

private def duplicate : Fin 2 → ℝ × ℝ := fun _ => (0, 2)
private def target : Fin 2 → ℝ × ℝ := ![(1, 3), (3, 7)]

/-- Only the first of two source occurrences is matched. -/
private def partialMatching : OccurrenceMatching (Fin 2) (Fin 2) PEmpty.{1} PEmpty.{1} where
  finite i := if i = 0 then some 0 else none
  finite_injective := by
    intro i i' j hi hi'
    have h : i = 0 := by by_contra h; simp [h] at hi
    have h' : i' = 0 := by by_contra h; simp [h] at hi'
    exact h.trans h'.symm
  essential := Equiv.refl _

private def unmatched (I J : Type*) : OccurrenceMatching I J PEmpty.{1} PEmpty.{1} where
  finite _ := none
  finite_injective := by simp
  essential := Equiv.refl _

-- Both equal occurrences contribute: this sum would be one after deduplication.
private theorem repeated_sum : finiteFeatureSum halfPersistence duplicate = 2 := by
  norm_num [finiteFeatureSum, duplicate, halfPersistence, Fin.sum_univ_two]

-- Cost 1 for the matched pair, 1 for the unmatched source, 2 for the unmatched target.
private theorem partialMatching_cost : partialMatching.totalFiniteCost duplicate target = 4 := by
  norm_num [OccurrenceMatching.totalFiniteCost, partialMatching, duplicate, target,
    Fin.sum_univ_two, Fin.exists_fin_succ]

private theorem partialMatching_bound :
    ‖finiteFeatureSum halfPersistence duplicate - finiteFeatureSum halfPersistence target‖ ≤
      partialMatching.totalFiniteCost duplicate target := by
  simpa only [one_mul] using partialMatching.norm_featureSum_sub_le halfPersistence 1 (by norm_num)
    (fun p q _ _ => by simpa using halfPersistence_sub_le p q)
    (fun p _ => by simpa only [one_mul] using le_of_eq (halfPersistence_norm p)) duplicate target
    (fun _ => by norm_num [duplicate]) (by intro j; fin_cases j <;> norm_num [target])

private theorem empty_target_sharp :
    ‖finiteFeatureSum halfPersistence duplicate -
        finiteFeatureSum halfPersistence (Fin.elim0 : Fin 0 → ℝ × ℝ)‖ =
      (unmatched (Fin 2) (Fin 0)).totalFiniteCost duplicate Fin.elim0 := by
  norm_num [OccurrenceMatching.totalFiniteCost, unmatched, duplicate,
    finiteFeatureSum, halfPersistence, Fin.sum_univ_two]

private theorem empty_source_sharp :
    ‖finiteFeatureSum halfPersistence (Fin.elim0 : Fin 0 → ℝ × ℝ) -
        finiteFeatureSum halfPersistence target‖ =
      (unmatched (Fin 0) (Fin 2)).totalFiniteCost Fin.elim0 target := by
  norm_num [OccurrenceMatching.totalFiniteCost, unmatched, target,
    finiteFeatureSum, halfPersistence, Fin.sum_univ_two]

private theorem empty_cost :
    (unmatched (Fin 0) (Fin 0)).totalFiniteCost Fin.elim0 Fin.elim0 = 0 := by
  simp [OccurrenceMatching.totalFiniteCost]

end AdditiveFeaturesExamples
end TDA.Persistence
