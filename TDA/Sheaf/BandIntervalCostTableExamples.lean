import TDA.Sheaf.BandIntervalCostTable

/-!
# Numeric interval costs over the rationals

The examples cover half-open direct and deletion costs and their tie, bounded
open and closed pairs in common and adjacent degrees, and pairs involving rays
and the whole line.
-/

noncomputable section

open CategoryTheory DerivedCategory TDA.Persistence TDA.Sheaf
open TDA.Sheaf.BandConvolution TDA.Sheaf.RealStratification
open scoped ENNReal ZeroObject

attribute [local instance] HasDerivedCategory.standard

private def breaks : Fin 2 → ℝ := ![0, 2]

private theorem mono_breaks : StrictMono breaks := by
  refine Fin.strictMono_iff_lt_succ.2 fun i => ?_
  fin_cases i
  norm_num [breaks]

private def Icc : FiniteInterval 5 := ⟨1, 4, by decide, by decide⟩
private def Ico : FiniteInterval 5 := ⟨1, 3, by decide, by decide⟩
private def Ioo : FiniteInterval 5 := ⟨2, 3, by decide, by decide⟩
private theorem ends_lt : (0 : ℝ) < 2 := by norm_num

private theorem support_Icc : intervalSet breaks Icc = Set.Icc 0 2 := by
  rw [intervalSet_eq_Icc mono_breaks (i := 0) (j := 1) rfl rfl]
  simp [breaks]

private theorem support_Ico : intervalSet breaks Ico = Set.Ico 0 2 := by
  rw [intervalSet_eq_Ico mono_breaks (i := 0) (j := 1) rfl rfl]
  simp [breaks]

private theorem support_Ioo : intervalSet breaks Ioo = Set.Ioo 0 2 := by
  rw [intervalSet_eq_Ioo mono_breaks (i := 0) (j := 1) rfl rfl]
  simp [breaks]

example : distance ((GradedInterval.mk Ico (-2)).obj ℚ mono_breaks) 0 = 1 := by
  rw [distance_interval_Ico_zero ℚ mono_breaks _ ends_lt support_Ico]
  norm_num

example : Nonempty (Witness ℚ (zero_le_one : (0 : ℝ) ≤ 1)
    ((GradedInterval.mk Ico (-2)).obj ℚ mono_breaks) 0) := by
  exact nonempty_witness_interval_Ico_zero_iff ℚ mono_breaks ⟨Ico, -2⟩
    ends_lt support_Ico zero_le_one |>.mpr (by norm_num)

example : distance ((GradedInterval.mk Ioo (-2)).obj ℚ mono_breaks) 0 = ⊤ :=
  distance_interval_Ioo_zero ℚ mono_breaks _ ends_lt support_Ioo

example : distance ((GradedInterval.mk Ioo 2).obj ℚ mono_breaks)
    ((GradedInterval.mk Icc 3).obj ℚ mono_breaks) = 2 := by
  have h := distance_interval_Ioo_Icc_succ ℚ mono_breaks mono_breaks Ioo Icc 2
    ends_lt ends_lt.le support_Ioo support_Icc
  norm_num at h ⊢
  exact h

example : distance ((GradedInterval.mk Ico 2).obj ℚ mono_breaks)
    ((GradedInterval.mk Ico 3).obj ℚ mono_breaks) = 1 := by
  let E := IntervalEndpoints.ico 0 2 ends_lt
  rw [distance_interval_of_degree_lt ℚ mono_breaks mono_breaks ⟨Ico, 2⟩ ⟨Ico, 3⟩ E E
    support_Ico support_Ico (by decide) (Or.inr rfl), sup_idem]
  norm_num [E, IntervalEndpoints.deletionCost]

private def point : FiniteInterval 5 := ⟨1, 2, by decide, by decide⟩

private theorem support_point : intervalSet breaks point = Set.Icc 0 0 := by
  rw [intervalSet_eq_singleton mono_breaks (i := 0) rfl rfl, Set.Icc_self]
  simp [breaks]

example : distance ((GradedInterval.mk Icc (-3)).obj ℚ mono_breaks)
    ((GradedInterval.mk point (-3)).obj ℚ mono_breaks) = 2 := by
  have h := distance_interval_Icc_Icc ℚ mono_breaks mono_breaks Icc point (-3)
    ends_lt.le le_rfl support_Icc support_point
  norm_num at h ⊢
  exact h

private def matching : GradedMatching Unit Unit := GradedMatching.ofEquiv (Equiv.refl _)

example : matching.cost
    (fun _ => (GradedInterval.mk Ioo 2).obj ℚ mono_breaks)
    (fun _ => (GradedInterval.mk Icc 3).obj ℚ mono_breaks) ≤ 2 := by
  refine (GradedMatching.cost_le_iff_of_pairCost ℚ matching mono_breaks mono_breaks
    (fun _ => ⟨Ioo, 2⟩) (fun _ => ⟨Icc, 3⟩)
    (fun _ => .ioo 0 2 ends_lt) (fun _ => .icc 0 2 ends_lt.le)
    (fun _ => support_Ioo) (fun _ => support_Icc)
    (fun _ _ => ENNReal.ofReal (max (2 - 0) (2 - 0))) (fun _ _ _ => rfl)).2 ?_
  refine ⟨fun _ _ _ => ?_, ?_, ?_⟩
  · norm_num
  · rintro ⟨⟩ h
    change some () = none at h
    cases h
  · rintro ⟨⟩ h
    exact (h ⟨(), rfl⟩).elim

private def Ioc : FiniteInterval 5 := ⟨2, 4, by decide, by decide⟩

private theorem support_Ioc : intervalSet breaks Ioc = Set.Ioc 0 2 := by
  rw [intervalSet_eq_Ioc mono_breaks (i := 0) (j := 1) rfl rfl]
  simp [breaks]

example : distance ((GradedInterval.mk Ico 0).obj ℚ mono_breaks)
    ((GradedInterval.mk Ioc 0).obj ℚ mono_breaks) = 1 := by
  have h := distance_interval_Ico_Ioc ℚ mono_breaks mono_breaks Ico Ioc 0
    ends_lt ends_lt support_Ico support_Ioc
  norm_num at h
  simpa only [sup_idem] using h

private def movedBreaks (a b : ℝ) : Fin 2 → ℝ := ![a, b]

private theorem mono_movedBreaks {a b : ℝ} (h : a < b) : StrictMono (movedBreaks a b) := by
  refine Fin.strictMono_iff_lt_succ.2 fun i => ?_
  fin_cases i
  simpa [movedBreaks] using h

private theorem moved_Ico {a b : ℝ} (h : a < b) :
    intervalSet (movedBreaks a b) Ico = Set.Ico a b := by
  rw [intervalSet_eq_Ico (mono_movedBreaks h) (i := 0) (j := 1) rfl rfl]
  simp [movedBreaks]

private theorem moved_Ioc {a b : ℝ} (h : a < b) :
    intervalSet (movedBreaks a b) Ioc = Set.Ioc a b := by
  rw [intervalSet_eq_Ioc (mono_movedBreaks h) (i := 0) (j := 1) rfl rfl]
  simp [movedBreaks]

private theorem moved_Ioo {a b : ℝ} (h : a < b) :
    intervalSet (movedBreaks a b) Ioo = Set.Ioo a b := by
  rw [intervalSet_eq_Ioo (mono_movedBreaks h) (i := 0) (j := 1) rfl rfl]
  simp [movedBreaks]

example : distance ((GradedInterval.mk Ico 0).obj ℚ mono_breaks)
    ((GradedInterval.mk Ico 0).obj ℚ (mono_movedBreaks (show (0 : ℝ) < 3 by norm_num))) =
      1 := by
  have h : (0 : ℝ) < 3 := by norm_num
  rw [distance_interval_Ico_Ico ℚ mono_breaks (mono_movedBreaks h) Ico Ico 0
    ends_lt h support_Ico (moved_Ico h)]
  norm_num [min_def]

example : distance ((GradedInterval.mk Ioc 0).obj ℚ mono_breaks)
    ((GradedInterval.mk Ioc 0).obj ℚ (mono_movedBreaks (show (4 : ℝ) < 6 by norm_num))) =
      1 := by
  have h : (4 : ℝ) < 6 := by norm_num
  rw [distance_interval_Ioc_Ioc ℚ mono_breaks (mono_movedBreaks h) Ioc Ioc 0
    ends_lt h support_Ioc (moved_Ioc h)]
  norm_num [min_def]

example : distance ((GradedInterval.mk Ico 0).obj ℚ mono_breaks)
    ((GradedInterval.mk Ico 0).obj ℚ (mono_movedBreaks (show (1 : ℝ) < 3 by norm_num))) =
      1 := by
  have h : (1 : ℝ) < 3 := by norm_num
  rw [distance_interval_Ico_Ico ℚ mono_breaks (mono_movedBreaks h) Ico Ico 0
    ends_lt h support_Ico (moved_Ico h)]
  norm_num

example : distance ((GradedInterval.mk Ioo 1).obj ℚ mono_breaks)
    ((GradedInterval.mk Ioo 1).obj ℚ (mono_movedBreaks (show (4 : ℝ) < 6 by norm_num))) =
      4 := by
  have h : (4 : ℝ) < 6 := by norm_num
  rw [distance_interval_Ioo_Ioo ℚ mono_breaks (mono_movedBreaks h) Ioo Ioo 1
    ends_lt h support_Ioo (moved_Ioo h)]
  norm_num

example : distance ((GradedInterval.mk Ioo 2).obj ℚ mono_breaks)
    ((GradedInterval.mk Icc 2).obj ℚ mono_breaks) = ⊤ :=
  distance_interval_of_different_endpoint_types ℚ mono_breaks mono_breaks Ioo Icc 2
    (.ioo 0 2 ends_lt) (.icc 0 2 ends_lt.le) support_Ioo support_Icc rfl

private def Ici : FiniteInterval 5 := ⟨1, 5, by decide, by decide⟩
private def Ioi : FiniteInterval 5 := ⟨2, 5, by decide, by decide⟩

private theorem support_Ici : intervalSet breaks Ici = Set.Ici 0 := by
  rw [intervalSet_eq_Ici mono_breaks (i := 0) rfl rfl]
  simp [breaks]

private theorem support_Ioi : intervalSet breaks Ioi = Set.Ioi 0 := by
  rw [intervalSet_eq_Ioi mono_breaks (i := 0) rfl rfl]
  simp [breaks]

example : distance ((GradedInterval.mk Ici 2).obj ℚ mono_breaks)
    ((GradedInterval.mk Ioi 2).obj ℚ mono_breaks) = ⊤ :=
  distance_interval_of_different_endpoint_types ℚ mono_breaks mono_breaks Ici Ioi 2
    (.ici 0) (.ioi 0) support_Ici support_Ioi rfl

example :
    distance ((GradedInterval.mk Ici 2).obj ℚ mono_breaks)
      ((GradedInterval.mk Ico 2).obj ℚ mono_breaks) = ⊤ :=
  distance_interval_of_different_endpoint_types ℚ mono_breaks mono_breaks Ici Ico 2
    (.ici 0) (.ico 0 2 ends_lt) support_Ici support_Ico rfl

example : (IntervalEndpoints.iio 0).totalPairCost (.iio 3) 2 2 = 3 := by
  change ENNReal.ofReal |(0 : ℝ) - 3| = 3
  norm_num

private def IciTwo : FiniteInterval 5 := ⟨3, 5, by decide, by decide⟩

private theorem support_IciTwo : intervalSet breaks IciTwo = Set.Ici 2 := by
  rw [intervalSet_eq_Ici mono_breaks (i := 1) rfl rfl]
  simp [breaks]

example : distance ((GradedInterval.mk Ici 3).obj ℚ mono_breaks)
    ((GradedInterval.mk IciTwo 3).obj ℚ mono_breaks) = 2 := by
  rw [distance_interval_Ici_Ici ℚ mono_breaks mono_breaks Ici IciTwo 3 support_Ici support_IciTwo]
  norm_num

private def whole : FiniteInterval 5 := ⟨0, 5, by decide, by decide⟩
private theorem support_whole : intervalSet breaks whole = Set.univ :=
  intervalSet_eq_univ mono_breaks rfl rfl

example : distance ((GradedInterval.mk whole 3).obj ℚ mono_breaks)
    ((GradedInterval.mk IciTwo 3).obj ℚ mono_breaks) = ⊤ :=
  distance_interval_of_different_endpoint_types ℚ mono_breaks mono_breaks whole IciTwo 3
    .univ (.ici 2) support_whole support_IciTwo rfl

example : distance ((GradedInterval.mk whole 3).obj ℚ mono_breaks)
    ((GradedInterval.mk whole 3).obj ℚ (mono_movedBreaks (show (1 : ℝ) < 3 by norm_num))) = 0 := by
  let hq : StrictMono (movedBreaks 1 3) := mono_movedBreaks (by norm_num)
  have hs : intervalSet (movedBreaks 1 3) whole = Set.univ := intervalSet_eq_univ hq rfl rfl
  exact distance_interval_univ_univ ℚ mono_breaks hq whole whole 3 support_whole hs

example : distance ((GradedInterval.mk Icc 0).obj ℚ mono_breaks)
    ((GradedInterval.mk Ioc 0).obj ℚ mono_breaks) = ⊤ :=
  distance_interval_of_different_endpoint_types ℚ mono_breaks mono_breaks Icc Ioc 0
    (.icc 0 2 ends_lt.le) (.ioc 0 2 ends_lt) support_Icc support_Ioc rfl

example : distance ((GradedInterval.mk Ioo 0).obj ℚ mono_breaks)
    ((GradedInterval.mk Ico 0).obj ℚ mono_breaks) = ⊤ :=
  distance_interval_of_different_endpoint_types ℚ mono_breaks mono_breaks Ioo Ico 0
    (.ioo 0 2 ends_lt) (.ico 0 2 ends_lt) support_Ioo support_Ico rfl

example :
    distance ((GradedInterval.mk Ioo 2).obj ℚ mono_breaks)
      ((GradedInterval.mk Icc 3).obj ℚ mono_breaks) =
    (IntervalEndpoints.ofInterval mono_breaks Ioo).totalPairCost
      (IntervalEndpoints.ofInterval mono_breaks Icc) 2 3 :=
  IntervalEndpoints.distance_eq_totalPairCost ℚ mono_breaks mono_breaks
    ⟨Ioo, 2⟩ ⟨Icc, 3⟩ _ _ (IntervalEndpoints.support_ofInterval _ _)
    (IntervalEndpoints.support_ofInterval _ _)

private def rightOpenTwo : FiniteInterval 5 := ⟨4, 5, by decide, by decide⟩

private theorem support_rightOpenTwo : intervalSet breaks rightOpenTwo = Set.Ioi 2 := by
  rw [intervalSet_eq_Ioi mono_breaks (i := 1) rfl rfl]
  simp [breaks]

example : distance ((GradedInterval.mk Ioi (-1)).obj ℚ mono_breaks)
    ((GradedInterval.mk rightOpenTwo (-1)).obj ℚ mono_breaks) = 2 := by
  rw [distance_interval_Ioi_Ioi ℚ mono_breaks mono_breaks Ioi rightOpenTwo (-1)
    support_Ioi support_rightOpenTwo]
  norm_num

private def leftClosed (i : Fin 2) : FiniteInterval 5 :=
  ⟨0, 2 * i.val + 2, by omega, by have := i.isLt; omega⟩

private theorem support_leftClosed (i : Fin 2) :
    intervalSet breaks (leftClosed i) = Set.Iic (breaks i) :=
  intervalSet_eq_Iic mono_breaks (j := i) rfl rfl

example : distance ((GradedInterval.mk (leftClosed 0) 1).obj ℚ mono_breaks)
    ((GradedInterval.mk (leftClosed 1) 1).obj ℚ mono_breaks) = 2 := by
  rw [distance_interval_Iic_Iic ℚ mono_breaks mono_breaks _ _ 1
    (support_leftClosed 0) (support_leftClosed 1)]
  norm_num [breaks]

private def leftOpen (i : Fin 2) : FiniteInterval 5 :=
  ⟨0, 2 * i.val + 1, by omega, by have := i.isLt; omega⟩

private theorem support_leftOpen (i : Fin 2) :
    intervalSet breaks (leftOpen i) = Set.Iio (breaks i) :=
  intervalSet_eq_Iio mono_breaks (j := i) rfl rfl

example : distance ((GradedInterval.mk (leftOpen 0) 1).obj ℚ mono_breaks)
    ((GradedInterval.mk (leftOpen 1) 1).obj ℚ mono_breaks) = 2 := by
  rw [distance_interval_Iio_Iio ℚ mono_breaks mono_breaks _ _ 1
    (support_leftOpen 0) (support_leftOpen 1)]
  norm_num [breaks]
