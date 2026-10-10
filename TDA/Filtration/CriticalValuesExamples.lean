import TDA.Filtration.CriticalValues

set_option autoImplicit false

universe u w

/-!
# Finite critical-value fixtures

Concrete filters on empty, singleton, and edge complexes check distinct-value enumeration,
simultaneous entry at ties, exact threshold recovery, and the generic ordered-grade interface.
Every private fixture declaration and helper instance is audited below.
-/

namespace TDA.Filtration.Issue92Fixtures

open FilterFunction

private def emptyFilter (V : Type u) (α : Type w) [LinearOrder α] :
    FilterFunction (⊥ : PreAbstractSimplicialComplex V) α where
  value := fun s => ((mem_bot_iff s.val).mp s.property).elim
  mono := by
    intro τ σ _
    exact ((mem_bot_iff τ.val).mp τ.property).elim

private instance emptyFaceIsEmpty (V : Type u) :
    IsEmpty (TDA.Simplicial.TotalFace (⊥ : PreAbstractSimplicialComplex V)) :=
  ⟨fun s => ((mem_bot_iff s.val).mp s.property).elim⟩

private instance emptyFaces (V : Type u) :
    Fintype (TDA.Simplicial.TotalFace (⊥ : PreAbstractSimplicialComplex V)) :=
  Fintype.ofIsEmpty

private theorem empty_case (V : Type u) (α : Type w) [LinearOrder α] (r : α) :
    (emptyFilter V α).criticalValues = ∅ ∧
    (emptyFilter V α).criticalValues.card = 0 ∧
    IsEmpty (Fin (emptyFilter V α).criticalValues.card) ∧
    (emptyFilter V α).sublevel r = ⊥ := by
  have h : (emptyFilter V α).criticalValues = ∅ :=
    ((emptyFilter V α).criticalValues_eq_empty_iff).2 rfl
  have hc : (emptyFilter V α).criticalValues.card = 0 := by simp [h]
  refine ⟨h, hc, ?_, (emptyFilter V α).sublevel_bot r⟩
  rw [hc]
  infer_instance

private theorem empty_ordered_grade :
    (emptyFilter Empty Empty).criticalValues.card = 0 ∧
    IsEmpty (Fin (emptyFilter Empty Empty).criticalValues.card) := by
  have h : (emptyFilter Empty Empty).criticalValues = ∅ :=
    ((emptyFilter Empty Empty).criticalValues_eq_empty_iff).2 rfl
  have hc : (emptyFilter Empty Empty).criticalValues.card = 0 := by simp [h]
  refine ⟨hc, ?_⟩
  rw [hc]
  infer_instance

private instance singletonMem (s : Finset (Fin 2)) :
    Decidable (s ∈ singletonFace (0 : Fin 2)) :=
  decidable_of_iff (s = {0}) (mem_singletonFace_iff 0 s).symm

private instance singletonFaces :
    Fintype (TDA.Simplicial.TotalFace (singletonFace (0 : Fin 2))) :=
  inferInstance

private def singletonFilter : FilterFunction (singletonFace (0 : Fin 2)) ℤ where
  value := fun _ => 3
  mono := by intros; exact le_refl 3

private theorem singleton_values :
    singletonFilter.criticalValues = {3} ∧
    singletonFilter.criticalValues.card = 1 := by
  decide

private def s0 : Fin singletonFilter.criticalValues.card :=
  ⟨0, by rw [singleton_values.2]; decide⟩

private theorem singleton_case :
    singletonFilter.criticalValue s0 = 3 ∧
    singletonFilter.gradeFiltration s0 = singletonFace (0 : Fin 2) ∧
    singletonFilter.sublevel 2 = ⊥ ∧
    singletonFilter.sublevel 3 = singletonFace (0 : Fin 2) ∧
    ({1} : Finset (Fin 2)) ∉ singletonFilter.gradeFiltration s0 ∧
    singletonFilter.gradeFiltration s0 ≠
      (⊤ : PreAbstractSimplicialComplex (Fin 2)) := by
  have hv : singletonFilter.criticalValue s0 = 3 := by
    have hm := singletonFilter.criticalValue_mem s0
    simpa [singleton_values.1] using hm
  have hg : singletonFilter.gradeFiltration s0 = singletonFace (0 : Fin 2) := by
    rw [singletonFilter.gradeFiltration_apply, hv]
    apply singletonFilter.sublevel_eq_self_of_forall_le
    intro s
    simp [singletonFilter]
  have hlow : singletonFilter.sublevel 2 = ⊥ := by
    apply singletonFilter.sublevel_eq_bot_of_forall_lt
    intro s
    norm_num [singletonFilter]
  have hnot : ({1} : Finset (Fin 2)) ∉ singletonFilter.gradeFiltration s0 := by
    rw [hg]
    exact (mem_singletonFace_iff 0 {1}).not.mpr (by decide)
  have hat : singletonFilter.sublevel 3 = singletonFace (0 : Fin 2) := by
    apply singletonFilter.sublevel_eq_self_of_forall_le
    intro s
    simp [singletonFilter]
  refine ⟨hv, hg, hlow, ?_, hnot, ?_⟩
  · exact hat
  · intro h
    have hx : ({1} : Finset (Fin 2)) ∈ singletonFilter.gradeFiltration s0 := by
      rw [h]
      change ({1} : Finset (Fin 2)).Nonempty
      simp
    exact hnot hx

private instance topMem (s : Finset (Fin 2)) :
    Decidable (s ∈ (⊤ : PreAbstractSimplicialComplex (Fin 2))) :=
  decidable_of_iff s.Nonempty Iff.rfl.symm

private instance edgeFaces :
    Fintype (TDA.Simplicial.TotalFace (⊤ : PreAbstractSimplicialComplex (Fin 2))) :=
  inferInstance

private def tiedFilter : FilterFunction (⊤ : PreAbstractSimplicialComplex (Fin 2)) ℤ where
  value := fun _ => 5
  mono := by intros; exact le_refl 5

private theorem tied_case :
    Fintype.card (TDA.Simplicial.TotalFace (⊤ : PreAbstractSimplicialComplex (Fin 2))) = 3 ∧
    tiedFilter.criticalValues = {5} ∧ tiedFilter.criticalValues.card = 1 := by
  decide

private def t0 : Fin tiedFilter.criticalValues.card :=
  ⟨0, by rw [tied_case.2.2]; decide⟩

private theorem tied_faces :
    tiedFilter.criticalValue t0 = 5 ∧
    tiedFilter.gradeFiltration t0 = (⊤ : PreAbstractSimplicialComplex (Fin 2)) ∧
    ({0} : Finset (Fin 2)) ∈ tiedFilter.gradeFiltration t0 ∧
    ({1} : Finset (Fin 2)) ∈ tiedFilter.gradeFiltration t0 ∧
    ({0,1} : Finset (Fin 2)) ∈ tiedFilter.gradeFiltration t0 := by
  have hv : tiedFilter.criticalValue t0 = 5 := by
    have hm := tiedFilter.criticalValue_mem t0
    simpa [tied_case.2.1] using hm
  have hg : tiedFilter.gradeFiltration t0 =
      (⊤ : PreAbstractSimplicialComplex (Fin 2)) := by
    rw [tiedFilter.gradeFiltration_apply, hv]
    apply tiedFilter.sublevel_eq_self_of_forall_le
    intro s
    simp [tiedFilter]
  rw [hg]
  refine ⟨hv, rfl, ?_, ?_, ?_⟩
  · change ({0} : Finset (Fin 2)).Nonempty
    simp
  · change ({1} : Finset (Fin 2)).Nonempty
    simp
  · change ({0,1} : Finset (Fin 2)).Nonempty
    simp

private def steppedFilter :
    FilterFunction (⊤ : PreAbstractSimplicialComplex (Fin 2)) ℤ where
  value := fun s => if s.val = {0,1} then 5 else if 1 ∈ s.val then 2 else 0
  mono := by decide

private theorem stepped_values :
    steppedFilter.criticalValues = {0,2,5} ∧
    steppedFilter.criticalValues.card = 3 := by
  decide

private def e0 : Fin steppedFilter.criticalValues.card :=
  ⟨0, by rw [stepped_values.2]; decide⟩
private def e1 : Fin steppedFilter.criticalValues.card :=
  ⟨1, by rw [stepped_values.2]; decide⟩
private def e2 : Fin steppedFilter.criticalValues.card :=
  ⟨2, by rw [stepped_values.2]; decide⟩

private theorem stepped_entries :
    steppedFilter.criticalValue e0 = 0 ∧
    steppedFilter.criticalValue e1 = 2 ∧
    steppedFilter.criticalValue e2 = 5 := by
  have hm0 := steppedFilter.criticalValue_mem e0
  have hm1 := steppedFilter.criticalValue_mem e1
  have hm2 := steppedFilter.criticalValue_mem e2
  simp only [stepped_values.1, Finset.mem_insert, Finset.mem_singleton] at hm0 hm1 hm2
  have h01 : steppedFilter.criticalValue e0 < steppedFilter.criticalValue e1 :=
    steppedFilter.criticalValue.strictMono (by decide)
  have h12 : steppedFilter.criticalValue e1 < steppedFilter.criticalValue e2 :=
    steppedFilter.criticalValue.strictMono (by decide)
  omega

private theorem stepped_thresholds :
    steppedFilter.sublevel (-1) = ⊥ ∧
    steppedFilter.sublevel 0 = steppedFilter.gradeFiltration e0 ∧
    steppedFilter.sublevel 1 = steppedFilter.gradeFiltration e0 ∧
    steppedFilter.sublevel 2 = steppedFilter.gradeFiltration e1 ∧
    steppedFilter.sublevel 4 = steppedFilter.gradeFiltration e1 ∧
    steppedFilter.sublevel 5 = steppedFilter.gradeFiltration e2 ∧
    steppedFilter.sublevel 6 = (⊤ : PreAbstractSimplicialComplex (Fin 2)) := by
  have ⟨h0, h1, h2⟩ := stepped_entries
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply steppedFilter.sublevel_eq_bot_of_lt_first (by rw [stepped_values.2]; decide)
    change -1 < steppedFilter.criticalValue e0
    rw [h0]
    omega
  · rw [steppedFilter.gradeFiltration_apply, h0]
  · apply steppedFilter.sublevel_eq_grade_of_adjacent e0 e1 (by decide) 1
    · rw [h0]; omega
    · rw [h1]; omega
  · rw [steppedFilter.gradeFiltration_apply, h1]
  · apply steppedFilter.sublevel_eq_grade_of_adjacent e1 e2 (by decide) 4
    · rw [h1]; omega
    · rw [h2]; omega
  · rw [steppedFilter.gradeFiltration_apply, h2]
  · apply steppedFilter.sublevel_eq_self_of_forall_le
    intro s
    change (if s.val = {0,1} then (5 : ℤ) else if 1 ∈ s.val then 2 else 0) ≤ 6
    split_ifs <;> omega

private theorem stepped_stage_faces :
    ({0} : Finset (Fin 2)) ∈ steppedFilter.gradeFiltration e0 ∧
    ({1} : Finset (Fin 2)) ∉ steppedFilter.gradeFiltration e0 ∧
    ({0} : Finset (Fin 2)) ∈ steppedFilter.gradeFiltration e1 ∧
    ({1} : Finset (Fin 2)) ∈ steppedFilter.gradeFiltration e1 ∧
    ({0,1} : Finset (Fin 2)) ∉ steppedFilter.gradeFiltration e1 ∧
    steppedFilter.gradeFiltration e2 =
      (⊤ : PreAbstractSimplicialComplex (Fin 2)) := by
  have ⟨h0, h1, h2⟩ := stepped_entries
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [steppedFilter.gradeFiltration_apply, h0]
    rw [FilterFunction.mem_sublevel_iff]
    refine ⟨?_, ?_⟩
    · change ({0} : Finset (Fin 2)).Nonempty
      simp
    · decide
  · rw [steppedFilter.gradeFiltration_apply, h0]
    rw [FilterFunction.mem_sublevel_iff]
    intro h
    have hv : steppedFilter.value ⟨{1}, h.1⟩ = 2 := by
      change (if ({1} : Finset (Fin 2)) = {0,1} then (5 : ℤ)
        else if 1 ∈ ({1} : Finset (Fin 2)) then 2 else 0) = 2
      decide
    omega
  · rw [steppedFilter.gradeFiltration_apply, h1]
    rw [FilterFunction.mem_sublevel_iff]
    refine ⟨?_, ?_⟩
    · change ({0} : Finset (Fin 2)).Nonempty
      simp
    · decide
  · rw [steppedFilter.gradeFiltration_apply, h1]
    rw [FilterFunction.mem_sublevel_iff]
    refine ⟨?_, ?_⟩
    · change ({1} : Finset (Fin 2)).Nonempty
      simp
    · decide
  · rw [steppedFilter.gradeFiltration_apply, h1]
    rw [FilterFunction.mem_sublevel_iff]
    intro h
    have hv : steppedFilter.value ⟨{0,1}, h.1⟩ = 5 := by
      change (if ({0,1} : Finset (Fin 2)) = {0,1} then (5 : ℤ)
        else if 1 ∈ ({0,1} : Finset (Fin 2)) then 2 else 0) = 5
      decide
    omega
  · rw [steppedFilter.gradeFiltration_apply, h2]
    apply steppedFilter.sublevel_eq_self_of_forall_le
    intro s
    change (if s.val = {0,1} then (5 : ℤ) else if 1 ∈ s.val then 2 else 0) ≤ 5
    split_ifs <;> omega

private def cofaceTieFilter :
    FilterFunction (⊤ : PreAbstractSimplicialComplex (Fin 2)) ℤ where
  value := fun s => if s.val = {0} then 0 else 5
  mono := by decide

private theorem coface_values :
    cofaceTieFilter.criticalValues = {0,5} ∧
    cofaceTieFilter.criticalValues.card = 2 := by
  decide

private def c1 : Fin cofaceTieFilter.criticalValues.card :=
  ⟨1, by rw [coface_values.2]; decide⟩
private def c0 : Fin cofaceTieFilter.criticalValues.card :=
  ⟨0, by rw [coface_values.2]; decide⟩

private theorem coface_tie :
    cofaceTieFilter.criticalValue c1 = 5 ∧
    ({1} : Finset (Fin 2)) ∈ cofaceTieFilter.gradeFiltration c1 ∧
    ({0,1} : Finset (Fin 2)) ∈ cofaceTieFilter.gradeFiltration c1 := by
  have hm0 := cofaceTieFilter.criticalValue_mem c0
  have hm1 := cofaceTieFilter.criticalValue_mem c1
  simp only [coface_values.1, Finset.mem_insert, Finset.mem_singleton] at hm0 hm1
  have h01 : cofaceTieFilter.criticalValue c0 < cofaceTieFilter.criticalValue c1 :=
    cofaceTieFilter.criticalValue.strictMono (by decide)
  have hv : cofaceTieFilter.criticalValue c1 = 5 := by omega
  refine ⟨hv, ?_, ?_⟩
  · rw [cofaceTieFilter.gradeFiltration_apply, hv]
    rw [FilterFunction.mem_sublevel_iff]
    refine ⟨?_, ?_⟩
    · change ({1} : Finset (Fin 2)).Nonempty
      simp
    · decide
  · rw [cofaceTieFilter.gradeFiltration_apply, hv]
    rw [FilterFunction.mem_sublevel_iff]
    refine ⟨?_, ?_⟩
    · change ({0,1} : Finset (Fin 2)).Nonempty
      simp
    · decide

private def rationalFilter :
    FilterFunction (⊤ : PreAbstractSimplicialComplex (Fin 2)) ℚ where
  value := fun s => (steppedFilter.value s : ℚ)
  mono := by
    intro τ σ h
    exact_mod_cast steppedFilter.mono h

private theorem rational_values :
    rationalFilter.criticalValues = {0,2,5} ∧
    rationalFilter.criticalValues.card = 3 := by
  decide

private def q0 : Fin rationalFilter.criticalValues.card :=
  ⟨0, by rw [rational_values.2]; decide⟩
private def q1 : Fin rationalFilter.criticalValues.card :=
  ⟨1, by rw [rational_values.2]; decide⟩
private def q2 : Fin rationalFilter.criticalValues.card :=
  ⟨2, by rw [rational_values.2]; decide⟩

private theorem rational_entries :
    rationalFilter.criticalValue q0 = 0 ∧
    rationalFilter.criticalValue q1 = 2 ∧
    rationalFilter.criticalValue q2 = 5 := by
  have hm0 := rationalFilter.criticalValue_mem q0
  have hm1 := rationalFilter.criticalValue_mem q1
  have hm2 := rationalFilter.criticalValue_mem q2
  simp only [rational_values.1, Finset.mem_insert, Finset.mem_singleton] at hm0 hm1 hm2
  have h01 : rationalFilter.criticalValue q0 < rationalFilter.criticalValue q1 :=
    rationalFilter.criticalValue.strictMono (by decide)
  have h12 : rationalFilter.criticalValue q1 < rationalFilter.criticalValue q2 :=
    rationalFilter.criticalValue.strictMono (by decide)
  rcases hm0 with h0 | h0 | h0 <;>
    rcases hm1 with h1 | h1 | h1 <;>
    rcases hm2 with h2 | h2 | h2 <;>
    simp_all <;> norm_num at *

private theorem rational_gap :
    rationalFilter.sublevel (3 / 2 : ℚ) = rationalFilter.gradeFiltration q0 := by
  apply rationalFilter.sublevel_eq_grade_of_adjacent q0 q1 (by decide) (3 / 2 : ℚ)
  · rw [rational_entries.1]
    norm_num
  · rw [rational_entries.2.1]
    norm_num

#print axioms emptyFilter
#print axioms emptyFaceIsEmpty
#print axioms emptyFaces
#print axioms empty_case
#print axioms empty_ordered_grade
#print axioms singletonMem
#print axioms singletonFaces
#print axioms singletonFilter
#print axioms singleton_values
#print axioms s0
#print axioms singleton_case
#print axioms topMem
#print axioms edgeFaces
#print axioms tiedFilter
#print axioms tied_case
#print axioms t0
#print axioms tied_faces
#print axioms steppedFilter
#print axioms stepped_values
#print axioms e0
#print axioms e1
#print axioms e2
#print axioms stepped_entries
#print axioms stepped_thresholds
#print axioms stepped_stage_faces
#print axioms cofaceTieFilter
#print axioms coface_values
#print axioms c1
#print axioms c0
#print axioms coface_tie
#print axioms rationalFilter
#print axioms rational_values
#print axioms q0
#print axioms q1
#print axioms q2
#print axioms rational_entries
#print axioms rational_gap

end TDA.Filtration.Issue92Fixtures
