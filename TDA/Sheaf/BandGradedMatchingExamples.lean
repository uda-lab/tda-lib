import TDA.Sheaf.BandMatchingIntervalCosts
import TDA.Sheaf.RealIntervalSectionsExamples

/-!
# Graded matching over the rationals

The open interval `(0, 2)` in degree zero and the point `1` in degree one have
an edge of cost one. The point cannot be left unmatched in a finite-cost matching.
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

example : Nonempty (Witness ℚ (zero_le_one : (0 : ℝ) ≤ 1)
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
