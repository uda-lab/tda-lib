import TDA.Persistence.MatchingInterleaving

/-!
# Matching-to-interleaving boundary examples

These fixtures construct their matchings explicitly. They cover endpoint equality,
one zero comparison, exact deletion length, essential births, repeated bars, empty
realizations and zero parameters.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence.MatchingInterleavingExamples

open CategoryTheory RealBarcode RealShift
open scoped NNReal ENNReal Classical ZeroObject

variable {k : Type u} [Field k]

private theorem finite_points {m n : ℕ} (x : Fin m → ℝ × ℝ) (b : Fin n → ℝ)
    (hx : ∀ i, (x i).1 < (x i).2) :
    (Finset.univ : Finset (Fin m)).val.map x = finitePart (orderedQ m n (x, b)).points := by
  rw [finitePart_orderedQ]
  have hf : (Multiset.ofList (List.ofFn x)).filter (fun p => p.1 ≠ p.2) =
      Multiset.ofList (List.ofFn x) := by
    apply Multiset.filter_eq_self.mpr
    intro p hp
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
    exact ne_of_lt (hx i)
  rw [hf, Fin.univ_val_map]

-- Relabel a concrete fixture matching to the existing canonical occurrence types.
private noncomputable def presented {m n m' n' : ℕ}
    (x : Fin m → ℝ × ℝ) (y : Fin m' → ℝ × ℝ) (b : Fin n → ℝ) (c : Fin n' → ℝ)
    (hx : ∀ i, (x i).1 < (x i).2) (hy : ∀ j, (y j).1 < (y j).2)
    (ε : ℝ≥0) (M : OccurrenceMatching (Fin m) (Fin m') (Fin n) (Fin n'))
    (hc : M.cost x y b c ≤ (ε : ℝ≥0∞)) :
    RealInterleaving ε (realize (k := k) (orderedQ m n (x, b)))
      (realize (orderedQ m' n' (y, c))) := by
  let D := orderedQ m n (x, b)
  let E := orderedQ m' n' (y, c)
  let ef := presentationEquiv x (fun p : D.finiteOccurrences => p.1)
    ((finite_points x b hx).trans (Multiset.map_univ_coe _).symm)
  let eg := presentationEquiv y (fun p : E.finiteOccurrences => p.1)
    ((finite_points y c hy).trans (Multiset.map_univ_coe _).symm)
  let eb := presentationEquiv b (fun p : D.essentialOccurrences => p.1)
    ((orderedQ_essential_occurrences m n (x, b)).trans (Multiset.map_univ_coe _).symm)
  let ec := presentationEquiv c (fun p : E.essentialOccurrences => p.1)
    ((orderedQ_essential_occurrences m' n' (y, c)).trans (Multiset.map_univ_coe _).symm)
  have hf : x ∘ ef.1.symm = fun p : D.finiteOccurrences => p.1 := by
    funext p; simpa using (ef.2 (ef.1.symm p)).symm
  have hg : y ∘ eg.1.symm = fun p : E.finiteOccurrences => p.1 := by
    funext p; simpa using (eg.2 (eg.1.symm p)).symm
  have hb : b ∘ eb.1.symm = fun p : D.essentialOccurrences => p.1 := by
    funext p; simpa using (eb.2 (eb.1.symm p)).symm
  have hd : c ∘ ec.1.symm = fun p : E.essentialOccurrences => p.1 := by
    funext p; simpa using (ec.2 (ec.1.symm p)).symm
  apply matchingInterleaving D E
    ((orderedQ_isPositive_iff m n (x, b)).mpr (fun i => (hx i).le))
    ((orderedQ_isPositive_iff m' n' (y, c)).mpr (fun i => (hy i).le)) ε
    (M.relabel ef.1.symm eg.1.symm eb.1.symm ec.1.symm)
  simpa only [hf, hg, hb, hd] using
    (M.cost_relabel ef.1.symm eg.1.symm eb.1.symm ec.1.symm x y b c).le.trans hc

private def singletonMatching : OccurrenceMatching (Fin 1) (Fin 1) (Fin 0) (Fin 0) :=
  ⟨some, by intro i i' j hi hi'; exact Option.some.inj (hi.trans hi'.symm), Equiv.refl _⟩

/-- Both endpoints move by exactly ε; the constructed realization maps satisfy both laws. -/
noncomputable def exact_endpoint_displacement :
    RealInterleaving 1 (realize (k := k) (orderedQ 1 0 (fun _ => (0, 2), Fin.elim0)))
      (realize (orderedQ 1 0 (fun _ => (1, 3), Fin.elim0))) := by
  apply presented (fun _ => (0, 2)) (fun _ => (1, 3)) Fin.elim0 Fin.elim0
    (by intro i; norm_num) (by intro i; norm_num) 1 singletonMatching
  norm_num [OccurrenceMatching.cost, singletonMatching, finitePairCost]

/-- At contact, one comparison in that matched pair is identically zero. -/
theorem reverse_comparison_zero :
    (interleavingOfBounds (k := k) 1 (0, (2 : WithTop ℝ)) (1, (3 : WithTop ℝ))
      (by norm_num) (by norm_num)
      (by norm_num [← WithTop.coe_add, WithTop.coe_le_coe])
      (by exact WithTop.coe_le_coe.mpr (show (2 : ℝ) ≤ 3 + 1 by norm_num))).ψ = 0 :=
  comparison_eq_zero_of_death_le 1 (1, (3 : WithTop ℝ)) (0, (2 : WithTop ℝ))
    (by norm_num)
    (by exact WithTop.coe_le_coe.mpr (show (2 : ℝ) ≤ 3 + 1 by norm_num))
    (by norm_num)

/-- The opposite map in the same pair really is nonzero. -/
theorem forward_comparison_ne_zero :
    (comparison (k := k) 1 (0, (2 : WithTop ℝ)) (1, (3 : WithTop ℝ))
      (by norm_num) (by norm_num [← WithTop.coe_add, WithTop.coe_le_coe])) ≠ 0 := by
  apply (comparison_ne_zero_iff _ _ _ (by norm_num) _ _).mpr
  norm_num

private def deletionMatching : OccurrenceMatching (Fin 1) (Fin 0) (Fin 0) (Fin 0) :=
  ⟨fun _ => none, by simp, Equiv.refl _⟩

/-- A finite bar of length exactly `2ε` can be unmatched. -/
noncomputable def exact_deletion_length :
    RealInterleaving 1 (realize (k := k) (orderedQ 1 0 (fun _ => (0, 2), Fin.elim0)))
      (realize (orderedQ 0 0 (Fin.elim0, Fin.elim0))) := by
  apply presented (fun _ => (0, 2)) Fin.elim0 Fin.elim0 Fin.elim0
    (by intro i; norm_num) (by intro i; exact Fin.elim0 i) 1 deletionMatching
  norm_num [OccurrenceMatching.cost, deletionMatching, diagonalCost]

/-- A longer finite interval fails the actual zero-module criterion. -/
theorem longer_interval_fails :
    ¬ Nonempty (RealInterleaving 1 (RealBarcode.intervalModule (k := k) (0, (3 : WithTop ℝ))) 0) := by
  intro h
  have ht := (interleaved_zero_iff (k := k) 1 0 3).mp h
  norm_num at ht

private def essentialMatching : OccurrenceMatching (Fin 0) (Fin 0) (Fin 1) (Fin 1) :=
  ⟨Fin.elim0, by intro i; exact Fin.elim0 i, Equiv.refl _⟩

/-- Essential births may differ by exactly ε; no essential coordinate is deleted. -/
noncomputable def essential_birth_displacement :
    RealInterleaving 1 (realize (k := k) (orderedQ 0 1 (Fin.elim0, fun _ => 0)))
      (realize (orderedQ 0 1 (Fin.elim0, fun _ => 1))) := by
  apply presented Fin.elim0 Fin.elim0 (fun _ => 0) (fun _ => 1)
    (by intro i; exact Fin.elim0 i) (by intro i; exact Fin.elim0 i) 1 essentialMatching
  norm_num [OccurrenceMatching.cost, essentialMatching, essentialPairCost]

/-- Essential deletion fails for arbitrary births and finite parameters. -/
theorem essential_deletion_fails (ε : ℝ≥0) (b : ℝ) :
    ¬ Nonempty (RealInterleaving ε (RealBarcode.intervalModule (k := k) (b, ⊤)) 0) :=
  essential_not_interleaved_zero ε b

/-- A finite bar cannot replace an essential occurrence in this matching model. -/
theorem finite_essential_no_matching :
    ¬ Nonempty (OccurrenceMatching (Fin 1) (Fin 0) (Fin 0) (Fin 1)) := by
  rw [occurrenceMatching_nonempty_iff]
  norm_num

private def duplicateMatching : OccurrenceMatching (Fin 2) (Fin 1) (Fin 0) (Fin 0) where
  finite i := if i = 0 then some 0 else none
  finite_injective := by
    intro i i' j hi hi'
    fin_cases i <;> fin_cases i' <;> simp_all
  essential := Equiv.refl _

/-- Of two identical occurrences, one is paired and the other is deleted at length `2ε`. -/
noncomputable def multiplicity_two_to_one :
    RealInterleaving 1 (realize (k := k) (orderedQ 2 0 (fun _ => (0, 2), Fin.elim0)))
      (realize (orderedQ 1 0 (fun _ => (0, 2), Fin.elim0))) := by
  apply presented (fun _ => (0, 2)) (fun _ => (0, 2)) Fin.elim0 Fin.elim0
    (by intro i; norm_num) (by intro i; norm_num) 1 duplicateMatching
  norm_num [OccurrenceMatching.cost, duplicateMatching, finitePairCost, diagonalCost,
    Finset.univ_fin2]

/-- Empty diagrams give concrete witnesses at every finite nonnegative parameter. -/
noncomputable def empty_interleaving (ε : ℝ≥0) :
    RealInterleaving ε (realize (k := k) (orderedQ 0 0 (Fin.elim0, Fin.elim0)))
      (realize (orderedQ 0 0 (Fin.elim0, Fin.elim0))) := by
  apply presented Fin.elim0 Fin.elim0 Fin.elim0 Fin.elim0
    (by intro i; exact Fin.elim0 i) (by intro i; exact Fin.elim0 i) ε
    ⟨Fin.elim0, by intro i; exact Fin.elim0 i, Equiv.refl _⟩
  simp [OccurrenceMatching.cost]

/-- At ε=0 a concrete matching constructs a nonempty interval's zero witness. -/
noncomputable def zero_parameter :
    RealInterleaving 0 (realize (k := k) (orderedQ 1 0 (fun _ => (0, 2), Fin.elim0)))
      (realize (orderedQ 1 0 (fun _ => (0, 2), Fin.elim0))) := by
  apply presented (fun _ => (0, 2)) (fun _ => (0, 2)) Fin.elim0 Fin.elim0
    (by intro i; norm_num) (by intro i; norm_num) 0 singletonMatching
  simp [OccurrenceMatching.cost, singletonMatching, finitePairCost]

end TDA.Persistence.MatchingInterleavingExamples
