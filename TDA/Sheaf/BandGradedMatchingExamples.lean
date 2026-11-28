import TDA.Sheaf.BandMatchingNormalization
import TDA.Sheaf.RealIntervalSectionsExamples

/-!
# Graded matching over the rationals

The open interval `(0, 2)` in degree zero and the point `1` in degree one have
an edge of cost one. The point has a source partner in every finite-cost matching.
Common convolution places both occurrences in the same degree. The half-open pair
`[0, 2)`, `[4, 6)` is affordable by joint deletion at radius one.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits DerivedCategory TDA.Persistence TDA.Sheaf
open TDA.Sheaf.AlternatingDiagram TDA.Sheaf.BandConvolution TDA.Sheaf.RealConstructible
open TDA.Sheaf.RealStratification
open TDA.Sheaf.RealIntervalSectionsExamples (Joo)
open scoped ENNReal ZeroObject

attribute [local instance] HasDerivedCategory.standard

private def breaks : Fin 2 → ℝ := ![0, 2]

private theorem strictMono_breaks : StrictMono breaks := by
  refine Fin.strictMono_iff_lt_succ.2 fun i => ?_
  fin_cases i
  norm_num [breaks]

private theorem open_interval : intervalSet breaks Joo = Set.Ioo 0 2 := by
  rw [intervalSet_eq_Ioo strictMono_breaks (i := 0) (j := 1) rfl rfl]
  simp [breaks]

private def pointBreak : Fin 1 → ℝ := fun _ => 1

private theorem strictMono_pointBreak : StrictMono pointBreak := Subsingleton.strictMono _

private def pointInterval : FiniteInterval 3 := ⟨1, 2, by decide, by decide⟩

private theorem point_support : intervalSet pointBreak pointInterval = {1} :=
  intervalSet_eq_singleton strictMono_pointBreak (i := 0) rfl rfl

private def openObj :=
  (GradedInterval.mk Joo 0).obj ℚ strictMono_breaks

private def pointObj :=
  (GradedInterval.mk pointInterval 1).obj ℚ strictMono_pointBreak

private def pointObjIso : (Plus.singleFunctor _ 1).obj (skyscraperSheaf ℚ 1) ≅ pointObj :=
  (Plus.singleFunctor _ 1).mapIso
    (nonempty_iso_skyscraperSheaf_interval ℚ strictMono_pointBreak pointInterval point_support).some

private theorem pair_distance : distance openObj pointObj = 1 := by
  rw [← distance_congr (Iso.refl openObj) pointObjIso]
  have h := distance_interval_Ioo_shifted_skyscraper ℚ strictMono_breaks Joo
    zero_le_one (by norm_num : (0 : ℝ) < 2) (by norm_num) open_interval
  rw [show (0 + 2 : ℝ) / 2 = 1 by norm_num, ENNReal.ofReal_one] at h
  exact h

private def pair : GradedMatching Unit Unit := GradedMatching.ofEquiv (Equiv.refl _)

private theorem pair_cost : pair.cost (fun _ => openObj) (fun _ => pointObj) = 1 := by
  apply le_antisymm
  · apply pair.cost_le_iff.mpr
    refine ⟨fun _ _ _ => pair_distance.le, ?_, ?_⟩
    · intro i hi
      change some i = none at hi
      cases hi
    · rintro ⟨⟩ hn
      exact (hn ⟨(), rfl⟩).elim
  · have h := (pair.cost_le_iff (X := fun _ => openObj) (Y := fun _ => pointObj)).mp le_rfl
    simpa only [pair_distance] using h.1 () () rfl

example : ∃ M : GradedMatching Unit Unit, M.cost (fun _ => openObj) (fun _ => pointObj) < ⊤ :=
  ⟨pair, by rw [pair_cost]; exact ENNReal.one_lt_top⟩

example :
    distance (⨁ fun _ : Unit => openObj) (⨁ fun _ : Unit => pointObj) ≤ 1 :=
  pair_cost ▸ pair.distance_biproduct_le_cost

private theorem nonempty_midpoint_biproduct_witness :
    Nonempty (Witness ℚ (zero_le_one : (0 : ℝ) ≤ 1)
    (⨁ fun _ : Unit => openObj) (⨁ fun _ : Unit => pointObj)) := by
  apply pair.nonempty_witness_biproduct
  · intro _ _ _
    obtain ⟨w⟩ := (nonempty_witness_interval_Ioo_shifted_skyscraper_iff ℚ strictMono_breaks Joo
      zero_le_one zero_le_one (by norm_num : (0 : ℝ) < 2) (by norm_num) open_interval).mpr le_rfl
    refine ⟨w.congr (Iso.refl openObj) ?_⟩
    rw [show (0 + 2 : ℝ) / 2 = 1 by norm_num]
    exact pointObjIso
  · intro i hi
    change some i = none at hi
    cases hi
  · rintro ⟨⟩ hn
    exact (hn ⟨(), rfl⟩).elim

example : ¬ Nonempty (Witness ℚ (show (0 : ℝ) ≤ 1 / 2 by norm_num) openObj pointObj) := by
  rintro ⟨w⟩
  have h := w.distance_le
  rw [pair_distance] at h
  norm_num at h

example {I : Type} (F : I → DerivedCategory.Plus (realLine.Sheaf (ModuleCat ℚ)))
    (M : GradedMatching I Unit) (h : M.cost F (fun _ => pointObj) < ⊤) :
    ∃ i, M.finite i = some () := by
  apply M.exists_source_of_cost_lt_top () _ h
  rw [← distance_congr pointObjIso (Iso.refl _)]
  exact distance_singleFunctor_skyscraper_zero ℚ 1 1

private def openEndpoints : IntervalEndpoints := .ioo 0 2 (by norm_num)

private def pointEndpoints : IntervalEndpoints := .icc 1 1 le_rfl

private theorem normalization_radius_nonneg : (0 : ℝ) ≤ 2 := by norm_num

private theorem open_threshold : openEndpoints.normalizationThreshold < 2 * 2 := by
  norm_num [openEndpoints, IntervalEndpoints.normalizationThreshold]

private theorem point_threshold : pointEndpoints.normalizationThreshold < 2 * 2 := by
  norm_num [pointEndpoints, IntervalEndpoints.normalizationThreshold]

example : openEndpoints.totalPairCost pointEndpoints 0 1 ≤ 1 := by
  rw [← ENNReal.ofReal_one]
  apply (openEndpoints.totalPairCost_le_iff_normalizedEdge_or_deletable pointEndpoints 0 1
    normalization_radius_nonneg open_threshold point_threshold zero_le_one).2
  left
  change (0 + 1 : ℤ) = 1 ∧ true = true ∧
    max |(2 - 2 : ℝ) - (1 - 2)| |-(0 + 2 : ℝ) - -(1 + 2)| ≤ 1
  norm_num

example : ¬ openEndpoints.normalizedEdge pointEndpoints 0 0 normalization_radius_nonneg
    open_threshold point_threshold 1 := by
  intro h
  have hdegree : (0 + 1 : ℤ) = 0 := h.1
  omega

example :
    ∃ (X' : Unit → GradedInterval (bandBreakpoints breaks 2).card)
      (Y' : Unit → GradedInterval (bandBreakpoints pointBreak 2).card),
      (X' ()).degree = 1 ∧ (Y' ()).degree = 1 ∧
      Nonempty (Witness ℚ (zero_le_one : (0 : ℝ) ≤ 1)
        (⨁ fun i => (X' i).obj ℚ (strictMono_sortedBreakpoints (bandBreakpoints breaks 2)))
        (⨁ fun j => (Y' j).obj ℚ
          (strictMono_sortedBreakpoints (bandBreakpoints pointBreak 2)))) := by
  obtain ⟨w⟩ := nonempty_midpoint_biproduct_witness
  obtain ⟨X', Y', hx, hy, W⟩ := w.exists_normalized_biproduct
    (p := fun _ : Unit => breaks) (q := fun _ : Unit => pointBreak)
    (fun _ => strictMono_breaks) (fun _ => strictMono_pointBreak)
    (X := fun _ => ⟨Joo, 0⟩) (Y := fun _ => ⟨pointInterval, 1⟩)
    (fun _ => openEndpoints) (fun _ => pointEndpoints)
    (fun _ => open_interval) (fun _ => by
      simpa [pointEndpoints, IntervalEndpoints.support] using point_support)
    normalization_radius_nonneg (fun _ => open_threshold) (fun _ => point_threshold)
  exact ⟨X', Y', (hx ()).2.1, (hy ()).2.1, W⟩

private def halfOpenLeft : IntervalEndpoints := .ico 0 2 (by norm_num)

private def halfOpenRight : IntervalEndpoints := .ico 4 6 (by norm_num)

private theorem halfOpenLeft_threshold : halfOpenLeft.normalizationThreshold < 2 * 2 := by
  norm_num [halfOpenLeft, IntervalEndpoints.normalizationThreshold]

private theorem halfOpenRight_threshold : halfOpenRight.normalizationThreshold < 2 * 2 := by
  norm_num [halfOpenRight, IntervalEndpoints.normalizationThreshold]

example : halfOpenLeft.totalPairCost halfOpenRight 0 0 ≤ 1 ∧
    ¬ halfOpenLeft.normalizedEdge halfOpenRight 0 0 normalization_radius_nonneg
      halfOpenLeft_threshold halfOpenRight_threshold 1 := by
  constructor
  · rw [← ENNReal.ofReal_one]
    apply (halfOpenLeft.totalPairCost_le_iff_normalizedEdge_or_deletable halfOpenRight 0 0
      normalization_radius_nonneg halfOpenLeft_threshold halfOpenRight_threshold zero_le_one).2
    right
    norm_num [halfOpenLeft, halfOpenRight, IntervalEndpoints.deletionCost]
  · intro h
    have hclose := (le_max_left _ _).trans h.2.2
    change |(0 - 2 : ℝ) - (4 - 2)| ≤ 1 at hclose
    norm_num at hclose
