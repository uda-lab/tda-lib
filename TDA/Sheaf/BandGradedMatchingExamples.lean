import TDA.Sheaf.BandMatchingLowerBound
import TDA.Sheaf.RealIntervalSectionsExamples

/-!
# Graded matching and projected witness equations

The open interval `(0, 2)` in degree zero and the point `1` in degree one have
an edge of cost one. The point has a source partner in every finite-cost matching.
Common convolution places both occurrences in the same degree. The half-open pair
`[0, 2)`, `[4, 6)` is affordable by joint deletion at radius one.
The finite isometry gives both distances in these examples. Two copies of
`[0, 2]` against one copy in the same degree admit no witness at a finite
radius. The projected equations retain the intermediates of the common
degree and endpoint type.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits DerivedCategory TDA.Persistence TDA.Sheaf
open TDA.Sheaf.AlternatingDiagram TDA.Sheaf.BandConvolution TDA.Sheaf.RealConstructible
open TDA.Sheaf.RealStratification
open TDA.Sheaf.RealIntervalSectionsExamples (Joo)
open scoped BigOperators ENNReal ZeroObject

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

section Projection

variable {k : Type} [Field k]
  [HasDerivedCategory (realLine.Sheaf (ModuleCat k))]
  [∀ a : ℝ, HasDerivedCategory ((D a).Sheaf (ModuleCat k))]
  [∀ a b : ℝ, HasDerivedCategory ((Z a b).Sheaf (ModuleCat k))]
  [HasDerivedCategory (pt.Sheaf (ModuleCat k))]
  [∀ u v : ℝ, HasDerivedCategory ((TopCat.of (Set.Icc u v)).Sheaf (ModuleCat k))]

private def closedInterval : FiniteInterval 5 := ⟨1, 4, by decide, by decide⟩

private def halfOpenInterval : FiniteInterval 5 := ⟨1, 3, by decide, by decide⟩

private theorem support_closedInterval : intervalSet breaks closedInterval = Set.Icc 0 2 := by
  rw [intervalSet_eq_Icc strictMono_breaks (i := 0) (j := 1) rfl rfl]
  simp [breaks]

private theorem support_halfOpenInterval : intervalSet breaks halfOpenInterval = Set.Ico 0 2 := by
  rw [intervalSet_eq_Ico strictMono_breaks (i := 0) (j := 1) rfl rfl]
  simp [breaks]

private def mixedGraded : Fin 4 → GradedInterval 2 :=
  ![⟨closedInterval, 0⟩, ⟨closedInterval, 0⟩, ⟨closedInterval, 1⟩, ⟨halfOpenInterval, 0⟩]

private def mixedEndpoints : Fin 4 → IntervalEndpoints :=
  let E := IntervalEndpoints.icc 0 2 (by norm_num)
  ![E, E, E, halfOpenLeft]

private theorem mixedSupport (i : Fin 4) :
    intervalSet breaks (mixedGraded i).interval = (mixedEndpoints i).support := by
  fin_cases i <;>
    first | exact support_closedInterval | exact support_halfOpenInterval

private theorem mixedStable (i : Fin 4) : (mixedEndpoints i).hasDegreeOneOutput = false := by
  fin_cases i <;> rfl

local notation "mixedObj" =>
  (fun i : Fin 4 => GradedInterval.obj k strictMono_breaks (mixedGraded i))

private def mixedBlock : Finset (Fin 4) := {0, 1}

private theorem mixedBlock_eq :
    Finset.univ.filter (fun j : Fin 4 =>
      (mixedGraded j).degree = (mixedGraded 0).degree ∧
        (mixedEndpoints 0).sameType (mixedEndpoints j) = true) =
      mixedBlock := by
  decide

local notation "H₀" =>
  Plus.homologyFunctor (realLine.Sheaf (ModuleCat k)) (GradedInterval.degree (mixedGraded 0))

/-- With identical interval supports on distinct outer labels, the projected
equation has zero off the occurrence diagonal. The mixed family admits a witness
at each nonnegative radius by enlarging the identity witness. -/
example {ε : ℝ} (hε : 0 ≤ ε) (w : Witness k hε (⨁ mixedObj) (⨁ mixedObj)) :
    (∑ j ∈ mixedBlock,
      (H₀).map ((T k ε).map (w.biproductHom mixedObj mixedObj 0 j) ≫
        w.symm.biproductHom mixedObj mixedObj j 1)) = 0 := by
  have h := w.sum_homology_biproductHom_in_block (k := k)
    (X := mixedGraded) (Y := mixedGraded) (pi := fun _ => breaks) (qj := fun _ => breaks)
    (fun _ => strictMono_breaks) (fun _ => strictMono_breaks) hε
    mixedEndpoints mixedEndpoints mixedSupport mixedSupport mixedStable mixedStable 0 1 rfl rfl
  simpa only [mixedBlock_eq, biproduct.ι_π_ne _ (by decide : (0 : Fin 4) ≠ 1),
    comp_zero, Functor.map_zero] using h

/-- The same projection has nonzero diagonal for the required closed occurrence. -/
example {ε : ℝ} (hε : 0 ≤ ε) (w : Witness k hε (⨁ mixedObj) (⨁ mixedObj)) :
    (∑ j ∈ mixedBlock,
      (H₀).map ((T k ε).map (w.biproductHom mixedObj mixedObj 0 j) ≫
        w.symm.biproductHom mixedObj mixedObj j 0)) ≠ 0 := by
  have h := w.sum_homology_biproductHom_in_block (k := k)
    (X := mixedGraded) (Y := mixedGraded) (pi := fun _ => breaks) (qj := fun _ => breaks)
    (fun _ => strictMono_breaks) (fun _ => strictMono_breaks) hε
    mixedEndpoints mixedEndpoints mixedSupport mixedSupport mixedStable mixedStable 0 0 rfl rfl
  rw [mixedBlock_eq, biproduct.ι_π_self] at h
  rw [h]
  let A := mixedObj 0
  let η : (T k (ε + ε)).obj A ⟶ A := (aug k (add_nonneg hε hε)).app A
  change (H₀).map ((TComp k hε hε).hom.app A ≫ η ≫ 𝟙 A) ≠ 0
  rw [Category.comp_id η]
  exact homology_band_augmentation_ne_zero_of_lt_deletionCost (k := k)
    strictMono_breaks (mixedGraded 0) (mixedEndpoints 0) (mixedSupport 0) (mixedStable 0) hε
    ENNReal.ofReal_lt_top

end Projection

example :
    distance (⨁ fun _ : Unit => openObj) (⨁ fun _ : Unit => pointObj) = 1 ∧
      matchingDistance (fun _ : Unit => openObj) (fun _ : Unit => pointObj) = 1 := by
  have h := distance_biproduct_eq_matchingDistance
    (k := ℚ) (pi := fun _ : Unit => breaks) (qj := fun _ : Unit => pointBreak)
    (X := fun _ => ⟨Joo, 0⟩) (Y := fun _ => ⟨pointInterval, 1⟩)
    (fun _ => strictMono_breaks) (fun _ => strictMono_pointBreak)
  have hd := (distance_congr (biproductUniqueIso (fun _ : Unit => openObj))
    (biproductUniqueIso (fun _ : Unit => pointObj))).trans pair_distance
  exact ⟨hd, h.symm.trans hd⟩

private def closedObj :=
  (GradedInterval.mk closedInterval 0).obj ℚ strictMono_breaks

private abbrev repeatedClosed := fun _ : Fin 2 => closedObj
private abbrev singleClosed := fun _ : Unit => closedObj

private theorem repeated_has_unmatched (M : GradedMatching (Fin 2) Unit) :
    ∃ i, M.finite i = none := by
  cases h₀ : M.finite (0 : Fin 2) with
  | none => exact ⟨0, h₀⟩
  | some j₀ =>
    cases h₁ : M.finite (1 : Fin 2) with
    | none => exact ⟨1, h₁⟩
    | some j₁ =>
      have hj : j₀ = j₁ := Subsingleton.elim _ _
      exact ((by decide : (0 : Fin 2) ≠ 1) (M.finite_injective 0 1 j₀ h₀ (hj.symm ▸ h₁))).elim

private theorem repeated_cost_eq_top (M : GradedMatching (Fin 2) Unit) :
    M.cost repeatedClosed singleClosed = ⊤ := by
  obtain ⟨i, hi⟩ := repeated_has_unmatched M
  have hdel : distance closedObj 0 = ⊤ :=
    distance_interval_Icc_zero ℚ strictMono_breaks ⟨closedInterval, 0⟩
      (show (0 : ℝ) ≤ 2 by norm_num) support_closedInterval
  have hc : distance closedObj 0 ≤ M.cost repeatedClosed singleClosed :=
    ((M.cost_le_iff (X := repeatedClosed) (Y := singleClosed)).mp le_rfl).2.1 i hi
  rw [hdel] at hc
  exact top_unique hc

private theorem repeated_distance_eq_top :
    distance (⨁ repeatedClosed) (⨁ singleClosed) = ⊤ := by
  have h := distance_biproduct_eq_matchingDistance
    (k := ℚ) (pi := fun _ : Fin 2 => breaks) (qj := fun _ : Unit => breaks)
    (X := fun _ => ⟨closedInterval, 0⟩) (Y := fun _ => ⟨closedInterval, 0⟩)
    (fun _ => strictMono_breaks) (fun _ => strictMono_breaks)
  have hm : matchingDistance repeatedClosed singleClosed = ⊤ :=
    top_unique (le_iInf fun M => (repeated_cost_eq_top M).ge)
  exact h.trans hm

example {r : ℝ} (hr : 0 ≤ r) :
    ¬ Nonempty (Witness ℚ hr (⨁ repeatedClosed) (⨁ singleClosed)) := by
  rintro ⟨w⟩
  have h := w.distance_le
  rw [repeated_distance_eq_top] at h
  exact ENNReal.ofReal_lt_top.not_ge h

private def rightBreaks : Fin 2 → ℝ := ![4, 6]

private theorem strictMono_rightBreaks : StrictMono rightBreaks := by
  refine Fin.strictMono_iff_lt_succ.2 fun i => ?_
  fin_cases i
  norm_num [rightBreaks]

private def halfOpenObj :=
  (GradedInterval.mk halfOpenInterval 0).obj ℚ strictMono_breaks

private def rightHalfOpenObj :=
  (GradedInterval.mk halfOpenInterval 0).obj ℚ strictMono_rightBreaks

example :
    distance (⨁ fun _ : Unit => halfOpenObj) (⨁ fun _ : Unit => rightHalfOpenObj) = 1 ∧
      matchingDistance (fun _ : Unit => halfOpenObj) (fun _ : Unit => rightHalfOpenObj) = 1 ∧
      (GradedMatching.empty : GradedMatching Unit Unit).cost
        (fun _ => halfOpenObj) (fun _ => rightHalfOpenObj) = 1 := by
  have h₀ := support_halfOpenInterval
  have h₁ : intervalSet rightBreaks halfOpenInterval = Set.Ico 4 6 := by
    rw [intervalSet_eq_Ico strictMono_rightBreaks (i := 0) (j := 1) rfl rfl]
    simp [rightBreaks]
  have hpair : distance halfOpenObj rightHalfOpenObj = 1 := by
    have h := distance_interval_Ico_Ico ℚ strictMono_breaks strictMono_rightBreaks
      halfOpenInterval halfOpenInterval 0 (by norm_num) (by norm_num) h₀ h₁
    norm_num [min_def] at h
    exact h
  have hdel₀ : distance halfOpenObj 0 = 1 := by
    have h := distance_interval_Ico_zero ℚ strictMono_breaks
      ⟨halfOpenInterval, 0⟩ (by norm_num) h₀
    norm_num at h
    exact h
  have hdel₁ : distance rightHalfOpenObj 0 = 1 := by
    have h := distance_interval_Ico_zero ℚ strictMono_rightBreaks
      ⟨halfOpenInterval, 0⟩ (by norm_num) h₁
    norm_num at h
    exact h
  have h := distance_biproduct_eq_matchingDistance
    (k := ℚ) (pi := fun _ : Unit => breaks) (qj := fun _ : Unit => rightBreaks)
    (X := fun _ => ⟨halfOpenInterval, 0⟩) (Y := fun _ => ⟨halfOpenInterval, 0⟩)
    (fun _ => strictMono_breaks) (fun _ => strictMono_rightBreaks)
  have hd := (distance_congr (biproductUniqueIso (fun _ : Unit => halfOpenObj))
    (biproductUniqueIso (fun _ : Unit => rightHalfOpenObj))).trans hpair
  let M : GradedMatching Unit Unit := GradedMatching.empty
  let A (_ : Unit) := halfOpenObj
  let B (_ : Unit) := rightHalfOpenObj
  refine ⟨hd, h.symm.trans hd, le_antisymm ?_ ?_⟩
  · apply (M.cost_le_iff (X := A) (Y := B)).mpr
    refine ⟨?_, fun _ _ => hdel₀.le, fun _ _ => hdel₁.le⟩
    intro i j hij
    cases hij
  · rw [← hdel₀]
    exact ((M.cost_le_iff (X := A) (Y := B)).mp le_rfl).2.1 () rfl
