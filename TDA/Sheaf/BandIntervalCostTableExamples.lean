import TDA.Sheaf.BandIntervalCostTable

/-!
# Numeric interval costs over the rationals

The half-open interval from zero to two is deletable at radius one. The open
interval with these endpoints has infinite deletion cost and matches the closed
interval from zero to two in the next degree at radius two.
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
