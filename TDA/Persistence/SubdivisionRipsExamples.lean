import TDA.Persistence.SubdivisionRips

/-!
# Normalized flag and restricted-index regression examples

A two-point metric separates the open radius boundary from the normalized
mass boundary. The final consumer checks the whole homology interleaving,
including both exact restrictions, for arbitrary finite labelled metrics.
-/

namespace TDA.Persistence.SubdivisionRips.Examples
open TDA.Filtration.SubdivisionRips TDA.Topology.MeasureBifiltration CategoryTheory
open scoped NNReal ENNReal

private abbrev twoPointMetric (c : ℝ) (hc : 0 < c) : MetricSpace (Fin 2) where
  dist i j := if i = j then 0 else c
  dist_self _ := if_pos rfl
  dist_comm i j := by simp only [eq_comm]
  dist_triangle i j k := by
    fin_cases i <;> fin_cases j <;> fin_cases k <;> norm_num <;> linarith
  eq_of_dist_eq_zero := by
    intro i j h
    by_contra hij
    simp only [if_neg hij] at h
    exact hc.ne' h

private abbrev d : MetricSpace (Fin 2) := twoPointMetric 2 (by norm_num)

private theorem d_dist (i j : Fin 2) : d.dist i j = if i = j then 0 else 2 := rfl

private theorem open_edge_boundary : ({0, 1} : Finset (Fin 2)) ∉ openRips d 1 := by
  intro h
  have := h.2 0 (by simp) 1 (by simp)
  rw [d_dist] at this
  norm_num at this

private theorem edge_above_boundary : ({0, 1} : Finset (Fin 2)) ∈ openRips d (3 / 2) := by
  refine ⟨by simp, ?_⟩
  intro v _ w _
  change (if v = w then 0 else 2 : ℝ) < 2 * (3 / 2)
  split_ifs <;> norm_num

private theorem singleton_flag_excluded_by_mass :
    ({{0}} : Finset (Finset (Fin 2))) ∉ subdivision (openRips d 2) (3 / 4) := by
  intro h
  have := (h.2.1 {0} (by simp)).2
  norm_num at this

private theorem two_step_flag_at_half_mass :
    ({{0}, {0, 1}} : Finset (Finset (Fin 2))) ∈ subdivision (openRips d 2) (1 / 2) := by
  refine ⟨by simp, ?_, ?_⟩
  · intro s hs
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl
    · refine ⟨⟨by simp, ?_⟩, by norm_num⟩
      intro v hv w hw
      simp only [Finset.mem_singleton] at hv hw
      subst v; subst w
      norm_num [d, twoPointMetric]
    · exact ⟨openRips_mono d (by norm_num) edge_above_boundary, by norm_num⟩
  · intro s hs t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs ht
    rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;> simp

private theorem nonzero_actual_homology_at_mass_one :
    ∃ z : (homology ℚ d 0).obj
      ⟨OrderDual.toDual ⟨1, by norm_num⟩, ⟨2, by norm_num⟩⟩, z ≠ 0 := by
  let := vertexOrder (Fin 2)
  change ∃ z : TDA.Simplicial.simplicialHomology
    (subdivision (openRips d 2) 1) ℚ 0, z ≠ 0
  have hfull : Finset.univ ∈ openRips d 2 := by
    refine ⟨Finset.univ_nonempty, ?_⟩
    intro v _ w _
    change (if v = w then 0 else 2 : ℝ) < 2 * 2
    split_ifs <;> norm_num
  rw [subdivision_one_eq_singleton _ hfull]
  exact ⟨(TDA.Simplicial.simplicialSingletonH0Equiv ℚ (Finset.univ : Finset (Fin 2))).symm 1,
    TDA.Simplicial.simplicialSingletonH0Equiv_symm_one_ne_zero ℚ _⟩

private theorem no_cross_arrow_below_shift (p q : Index)
    (hk : mass p ≤ (1 : ℝ)) :
    ¬ (⟨p, false⟩ : InterleavingIndex 1) ≤ ⟨q, true⟩ := by
  rw [cross_le_iff]
  intro h
  have hq : 0 < mass q := mass_pos q
  norm_num at h
  linarith [h.1]

private theorem actual_homology_metric_consumer (n : ℕ) :
    (copy 1 false).toFunctor ⋙ metricInterleaving ℚ d (twoPointMetric 4 (by norm_num)) 1
      (fun v w => by
        change |(if v = w then 0 else 2 : ℝ) - (if v = w then 0 else 4)| ≤ 2 * 1
        split_ifs <;> norm_num) n = homology ℚ d n :=
  metricInterleaving_left ℚ _ _ _ _ n

end TDA.Persistence.SubdivisionRips.Examples
