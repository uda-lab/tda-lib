import TDA.Persistence.IndexDiagram
import TDA.Persistence.GradeHomologyBarcode

namespace TDA.Persistence

universe u w
variable {α : Type u} [LinearOrder α]

private theorem noGrades_noBars {α : Type u} [LinearOrder α]
    (v : Fin 0 → α) (hv : StrictMono v)
    (B : Multiset (FiniteInterval 0)) :
    B = 0 ∧ (ofIndexBars v hv B).points = 0 := by
  have h : ∀ I : FiniteInterval 0, False := by
    intro I
    have := I.birth_lt_death
    have := I.death_le_size
    omega
  have hB : B = 0 := by
    apply Multiset.eq_zero_iff_forall_notMem.mpr
    intro I _
    exact h I
  constructor
  · exact hB
  · simp [hB, ofIndexBars]

private theorem noGrades_emptyValue (v : Fin 0 → Empty) (hv : StrictMono v)
    (B : Multiset (FiniteInterval 0)) :
    B = 0 ∧ (ofIndexBars v hv B).points = 0 :=
  noGrades_noBars v hv B

private def oneBar : FiniteInterval 1 := ⟨0, 1, by omega, by omega⟩
private def oneValue (a : α) : Fin 1 → α := fun _ => a
private theorem oneValue_strict (a : α) : StrictMono (oneValue a) := by
  intro i j hij
  have heq : i = j := Subsingleton.elim _ _
  subst j
  exact (lt_irrefl i hij).elim

private theorem oneBar_points (a : α) :
    (ofIndexBars (oneValue a) (oneValue_strict a) ({oneBar} : Multiset (FiniteInterval 1))).points =
      {(a, (⊤ : WithTop α))} := by
  rfl

private theorem twoBars_points (a : α) :
    (ofIndexBars (oneValue a) (oneValue_strict a)
      ({oneBar, oneBar} : Multiset (FiniteInterval 1))).points =
      ({(a, (⊤ : WithTop α)), (a, (⊤ : WithTop α))} : Multiset (α × WithTop α)) := by
  rfl

private theorem oneBar_terminal_count (a : α) :
    (ofIndexBars (oneValue a) (oneValue_strict a)
      ({oneBar} : Multiset (FiniteInterval 1))).points.count (a, (⊤ : WithTop α)) = 1 := by
  calc
    _ = barcodeMultiplicity ({oneBar} : Multiset (FiniteInterval 1)) 0 1 := by
      simpa [oneValue] using
        (ofIndexBars_count_essential (oneValue a) (oneValue_strict a)
          ({oneBar} : Multiset (FiniteInterval 1)) (0 : Fin 1))
    _ = 1 := by decide

private theorem twoBars_terminal_count (a : α) :
    (ofIndexBars (oneValue a) (oneValue_strict a)
      ({oneBar, oneBar} : Multiset (FiniteInterval 1))).points.count (a, (⊤ : WithTop α)) = 2 := by
  calc
    _ = barcodeMultiplicity ({oneBar, oneBar} : Multiset (FiniteInterval 1)) 0 1 := by
      simpa [oneValue] using
        (ofIndexBars_count_essential (oneValue a) (oneValue_strict a)
          ({oneBar, oneBar} : Multiset (FiniteInterval 1)) (0 : Fin 1))
    _ = 2 := by decide

private theorem oneBar_diagonal_zero (a : α) :
    (ofIndexBars (oneValue a) (oneValue_strict a)
      ({oneBar} : Multiset (FiniteInterval 1))).points.count (a, (a : WithTop α)) = 0 := by
  calc
    _ = barcodeMultiplicity ({oneBar} : Multiset (FiniteInterval 1)) 0 0 := by
      simpa [oneValue] using
        (ofIndexBars_count_finite (oneValue a) (oneValue_strict a)
          ({oneBar} : Multiset (FiniteInterval 1)) (0 : Fin 1) (0 : Fin 1))
    _ = 0 := by decide

private theorem oneBar_slice (a : α) :
    (ofIndexBars (oneValue a) (oneValue_strict a)
      ({oneBar} : Multiset (FiniteInterval 1))).points.countP
      (fun p => p.1 ≤ a ∧ (a : WithTop α) < p.2) = 1 := by
  have hc : ({oneBar} : Multiset (FiniteInterval 1)).countP
      (fun I => I.birth ≤ (0 : Fin 1).val ∧ (0 : Fin 1).val < I.death) = 1 := by
    decide
  exact (ofIndexBars_countP_grades (oneValue a) (oneValue_strict a)
    ({oneBar} : Multiset (FiniteInterval 1)) (0 : Fin 1) (0 : Fin 1)).trans hc

private theorem twoBars_slice (a : α) :
    (ofIndexBars (oneValue a) (oneValue_strict a)
      ({oneBar, oneBar} : Multiset (FiniteInterval 1))).points.countP
      (fun p => p.1 ≤ a ∧ (a : WithTop α) < p.2) = 2 := by
  have hc : ({oneBar, oneBar} : Multiset (FiniteInterval 1)).countP
      (fun I => I.birth ≤ (0 : Fin 1).val ∧ (0 : Fin 1).val < I.death) = 2 := by
    decide
  exact (ofIndexBars_countP_grades (oneValue a) (oneValue_strict a)
    ({oneBar, oneBar} : Multiset (FiniteInterval 1)) (0 : Fin 1) (0 : Fin 1)).trans hc

private def mixedValue : Fin 3 → ℚ := ![2, 5, 9]
private theorem mixedValue_strict : StrictMono mixedValue := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> norm_num [mixedValue, Fin.lt_def] at *

private def mixedBar01 : FiniteInterval 3 := ⟨0, 1, by omega, by omega⟩
private def mixedBar02 : FiniteInterval 3 := ⟨0, 2, by omega, by omega⟩
private def mixedBar13 : FiniteInterval 3 := ⟨1, 3, by omega, by omega⟩
private def mixedBar23 : FiniteInterval 3 := ⟨2, 3, by omega, by omega⟩
private def mixedBars : Multiset (FiniteInterval 3) :=
  {mixedBar01, mixedBar02, mixedBar02, mixedBar13, mixedBar13, mixedBar23}

private theorem mixed_points :
    (ofIndexBars mixedValue mixedValue_strict mixedBars).points =
      ({((2:ℚ), (5:WithTop ℚ)), ((2:ℚ), (9:WithTop ℚ)),
       ((2:ℚ), (9:WithTop ℚ)), ((5:ℚ), (⊤:WithTop ℚ)),
       ((5:ℚ), (⊤:WithTop ℚ)), ((9:ℚ), (⊤:WithTop ℚ))} : Multiset (ℚ × WithTop ℚ)) := by
  decide

private theorem mixed_count_25 :
    (ofIndexBars mixedValue mixedValue_strict mixedBars).points.count
      ((2:ℚ), (5:WithTop ℚ)) = 1 := by
  convert ofIndexBars_count_finite mixedValue mixedValue_strict mixedBars (0 : Fin 3) (1 : Fin 3) using 1 <;>
    decide

private theorem mixed_count_29 :
    (ofIndexBars mixedValue mixedValue_strict mixedBars).points.count
      ((2:ℚ), (9:WithTop ℚ)) = 2 := by
  convert ofIndexBars_count_finite mixedValue mixedValue_strict mixedBars (0 : Fin 3) (2 : Fin 3) using 1 <;>
    decide

private theorem mixed_count_5top :
    (ofIndexBars mixedValue mixedValue_strict mixedBars).points.count
      ((5:ℚ), (⊤:WithTop ℚ)) = 2 := by
  convert ofIndexBars_count_essential mixedValue mixedValue_strict mixedBars (1 : Fin 3) using 1 <;>
    decide

private theorem mixed_count_9top :
    (ofIndexBars mixedValue mixedValue_strict mixedBars).points.count
      ((9:ℚ), (⊤:WithTop ℚ)) = 1 := by
  convert ofIndexBars_count_essential mixedValue mixedValue_strict mixedBars (2 : Fin 3) using 1 <;>
    decide

private theorem mixed_count_diagonal :
    (ofIndexBars mixedValue mixedValue_strict mixedBars).points.count
      ((5:ℚ), (5:WithTop ℚ)) = 0 := by
  convert ofIndexBars_count_finite mixedValue mixedValue_strict mixedBars (1 : Fin 3) (1 : Fin 3) using 1 <;>
    decide

private theorem mixed_count_reverse :
    (ofIndexBars mixedValue mixedValue_strict mixedBars).points.count
      ((9:ℚ), (2:WithTop ℚ)) = 0 := by
  convert ofIndexBars_count_finite mixedValue mixedValue_strict mixedBars (2 : Fin 3) (0 : Fin 3) using 1 <;>
    decide

private theorem mixed_count_unsupported :
    (ofIndexBars mixedValue mixedValue_strict mixedBars).points.count
      ((7:ℚ), (⊤:WithTop ℚ)) = 0 := by
  rw [mixed_points]
  decide

private theorem mixed_slice (i j : Fin 3) :
    (ofIndexBars mixedValue mixedValue_strict mixedBars).points.countP
      (fun p => p.1 ≤ mixedValue i ∧ (mixedValue j : WithTop ℚ) < p.2) =
    mixedBars.countP (fun I => I.birth ≤ i.val ∧ j.val < I.death) :=
  ofIndexBars_countP_grades mixedValue mixedValue_strict mixedBars i j

private theorem mixed_slice_00 :
    (ofIndexBars mixedValue mixedValue_strict mixedBars).points.countP
      (fun p => p.1 ≤ mixedValue (0 : Fin 3) ∧
        (mixedValue (0 : Fin 3) : WithTop ℚ) < p.2) = 3 := by
  rw [mixed_slice]
  decide
private theorem mixed_slice_01 :
    (ofIndexBars mixedValue mixedValue_strict mixedBars).points.countP
      (fun p => p.1 ≤ mixedValue (0 : Fin 3) ∧
        (mixedValue (1 : Fin 3) : WithTop ℚ) < p.2) = 2 := by
  rw [mixed_slice]
  decide
private theorem mixed_slice_02 :
    (ofIndexBars mixedValue mixedValue_strict mixedBars).points.countP
      (fun p => p.1 ≤ mixedValue (0 : Fin 3) ∧
        (mixedValue (2 : Fin 3) : WithTop ℚ) < p.2) = 0 := by
  rw [mixed_slice]
  decide
private theorem mixed_slice_11 :
    (ofIndexBars mixedValue mixedValue_strict mixedBars).points.countP
      (fun p => p.1 ≤ mixedValue (1 : Fin 3) ∧
        (mixedValue (1 : Fin 3) : WithTop ℚ) < p.2) = 4 := by
  rw [mixed_slice]
  decide
private theorem mixed_slice_12 :
    (ofIndexBars mixedValue mixedValue_strict mixedBars).points.countP
      (fun p => p.1 ≤ mixedValue (1 : Fin 3) ∧
        (mixedValue (2 : Fin 3) : WithTop ℚ) < p.2) = 2 := by
  rw [mixed_slice]
  decide
private theorem mixed_slice_22 :
    (ofIndexBars mixedValue mixedValue_strict mixedBars).points.countP
      (fun p => p.1 ≤ mixedValue (2 : Fin 3) ∧
        (mixedValue (2 : Fin 3) : WithTop ℚ) < p.2) = 3 := by
  rw [mixed_slice]
  decide
private theorem mixed_slice_20 :
    (ofIndexBars mixedValue mixedValue_strict mixedBars).points.countP
      (fun p => p.1 ≤ mixedValue (2 : Fin 3) ∧
        (mixedValue (0 : Fin 3) : WithTop ℚ) < p.2) = 6 := by
  rw [mixed_slice]
  decide

private theorem mixed_injective {B C : Multiset (FiniteInterval 3)}
    (h : ofIndexBars mixedValue mixedValue_strict B =
      ofIndexBars mixedValue mixedValue_strict C) : B = C :=
  ofIndexBars_injective mixedValue mixedValue_strict h

private theorem mixed_delete_duplicate_changes :
    ofIndexBars mixedValue mixedValue_strict mixedBars ≠
      ofIndexBars mixedValue mixedValue_strict
        ({mixedBar01, mixedBar02, mixedBar13, mixedBar13, mixedBar23} : Multiset (FiniteInterval 3)) := by
  intro h
  have hb := mixed_injective h
  have : mixedBars ≠
      ({mixedBar01, mixedBar02, mixedBar13, mixedBar13, mixedBar23} : Multiset (FiniteInterval 3)) := by
    decide
  exact this hb

private theorem mixed_change_death_changes :
    ofIndexBars mixedValue mixedValue_strict mixedBars ≠
      ofIndexBars mixedValue mixedValue_strict
        ({mixedBar02, mixedBar02, mixedBar02, mixedBar13, mixedBar13, mixedBar23} : Multiset (FiniteInterval 3)) := by
  intro h
  have hb := mixed_injective h
  have : mixedBars ≠
      ({mixedBar02, mixedBar02, mixedBar02, mixedBar13, mixedBar13, mixedBar23} : Multiset (FiniteInterval 3)) := by
    decide
  exact this hb

private theorem fullBar_points {α : Type u} [LinearOrder α] {N : ℕ}
    (hN : 0 < N) (v : Fin N → α) (hv : StrictMono v) :
    (ofIndexBars v hv
      ({(⟨0, N, hN, le_rfl⟩ : FiniteInterval N)} : Multiset (FiniteInterval N))).points =
      ({(v ⟨0, hN⟩, (⊤ : WithTop α))} : Multiset (α × WithTop α)) := by
  change ({(v ⟨0, hN⟩,
    if hd : N < N then (v ⟨N, hd⟩ : WithTop α) else (⊤ : WithTop α))} :
      Multiset (α × WithTop α)) = _
  simp

private theorem fullBar_recover {α : Type u} [LinearOrder α] {N : ℕ}
    (v : Fin N → α) (hv : StrictMono v)
    {B C : Multiset (FiniteInterval N)}
    (h : ofIndexBars v hv B = ofIndexBars v hv C) : B = C :=
  ofIndexBars_injective v hv h

private theorem criticalValue_rank_consumer
    {V : Type u} [LinearOrder V] (k : Type u) [Field k]
    {α : Type w} [LinearOrder α]
    {K : PreAbstractSimplicialComplex V}
    [Fintype (TDA.Simplicial.TotalFace K)]
    (f : TDA.Filtration.FilterFunction K α) (n : ℕ)
    (i j : Fin f.criticalValues.card) (hij : i ≤ j) :
    Module.finrank k (LinearMap.range
      (TDA.Simplicial.simplicialHomologyIncl k
        (f.gradeFiltration.monotone hij) n).hom) =
      (TDA.Persistence.ofIndexBars f.criticalValue f.criticalValue.strictMono
        (TDA.Persistence.gradeHomologyBarcode k f n)).points.countP
          (fun p => p.1 ≤ f.criticalValue i ∧
            (f.criticalValue j : WithTop α) < p.2) := by
  exact (rank_gradeHomologyMap k f n i j hij).trans
    (ofIndexBars_countP_grades f.criticalValue f.criticalValue.strictMono
      (gradeHomologyBarcode k f n) i j).symm

private theorem criticalValue_positive
    {V : Type u} [LinearOrder V] (k : Type u) [Field k]
    {α : Type w} [LinearOrder α]
    {K : PreAbstractSimplicialComplex V}
    [Fintype (TDA.Simplicial.TotalFace K)]
    (f : TDA.Filtration.FilterFunction K α) (n : ℕ) :
    (ofIndexBars f.criticalValue f.criticalValue.strictMono
      (gradeHomologyBarcode k f n)).IsPositive :=
  ofIndexBars_isPositive _ _ _

private theorem criticalValue_tail_sanity
    {V : Type u} [LinearOrder V]
    {α : Type w} [LinearOrder α]
    {K : PreAbstractSimplicialComplex V}
    [Fintype (TDA.Simplicial.TotalFace K)]
    (f : TDA.Filtration.FilterFunction K α)
    (hN : 0 < f.criticalValues.card) (r : α)
    (hr : f.criticalValue
      ⟨f.criticalValues.card - 1, Nat.sub_lt hN (by decide)⟩ ≤ r) :
    f.sublevel r = K ∧
      f.gradeFiltration ⟨f.criticalValues.card - 1, Nat.sub_lt hN (by decide)⟩ = K ∧
      f.sublevel r = f.gradeFiltration
        ⟨f.criticalValues.card - 1, Nat.sub_lt hN (by decide)⟩ := by
  have ht : f.sublevel r = K := f.sublevel_eq_self_of_last_le hN r hr
  have hg : f.gradeFiltration
      ⟨f.criticalValues.card - 1, Nat.sub_lt hN (by decide)⟩ = K := by
    rw [f.gradeFiltration_apply]
    exact f.sublevel_eq_self_of_last_le hN _ le_rfl
  exact ⟨ht, hg, ht.trans hg.symm⟩

private theorem criticalValue_bottom_sanity
    {V : Type u} [LinearOrder V]
    {α : Type w} [LinearOrder α]
    [Fintype (TDA.Simplicial.TotalFace (⊥ : PreAbstractSimplicialComplex V))]
    (f : TDA.Filtration.FilterFunction (⊥ : PreAbstractSimplicialComplex V) α)
    (r : α) : f.sublevel r = ⊥ :=
  f.sublevel_bot r

end TDA.Persistence
