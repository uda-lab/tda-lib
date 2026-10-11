import TDA.Filtration.CompatibleOrderExistence

set_option autoImplicit false

namespace TDA.Filtration.Examples.CompatibleOrderExistence

open TDA.Filtration TDA.Simplicial

private def bottomFilter (V : Type*) :
    FilterFunction (⊥ : PreAbstractSimplicialComplex V) Empty where
  value := fun s => False.elim ((TDA.Filtration.mem_bot_iff s.val).mp s.property)
  mono := by
    intro s t _
    exact False.elim ((TDA.Filtration.mem_bot_iff s.val).mp s.property)

private instance bottomIsEmpty (V : Type*) :
    IsEmpty (TotalFace (⊥ : PreAbstractSimplicialComplex V)) :=
  ⟨fun s => (TDA.Filtration.mem_bot_iff s.val).mp s.property⟩

private noncomputable instance bottomFintype (V : Type*) :
    Fintype (TotalFace (⊥ : PreAbstractSimplicialComplex V)) :=
  Fintype.ofFinite _

private theorem bottom_exists_fin0 :
    Nonempty (CompatibleOrder (bottomFilter (Fin 0))) := by
  exact exists_compatibleOrder (bottomFilter (Fin 0))

private theorem bottom_exists_nat :
    Nonempty (CompatibleOrder (bottomFilter ℕ)) := by
  exact exists_compatibleOrder (bottomFilter ℕ)

private theorem bottom_empty_index (V : Type*) :
    ∃ _h : CompatibleOrder (bottomFilter V),
      IsEmpty (Fin (Fintype.card (TotalFace (⊥ : PreAbstractSimplicialComplex V)))) := by
  let h := (exists_compatibleOrder (bottomFilter V)).some
  refine ⟨h, ?_⟩
  exact Equiv.isEmpty h.enum

private theorem bottom_fin0_empty_index :
    ∃ _h : CompatibleOrder (bottomFilter (Fin 0)),
      IsEmpty (Fin (Fintype.card (TotalFace (⊥ : PreAbstractSimplicialComplex (Fin 0))))) :=
  bottom_empty_index (Fin 0)

private theorem bottom_nat_empty_index :
    ∃ _h : CompatibleOrder (bottomFilter ℕ),
      IsEmpty (Fin (Fintype.card (TotalFace (⊥ : PreAbstractSimplicialComplex ℕ)))) :=
  bottom_empty_index ℕ

private def edgeNat : PreAbstractSimplicialComplex ℕ where
  faces := {s | s.Nonempty ∧ s ⊆ ({0, 1} : Finset ℕ)}
  isRelLowerSet_faces := by
    intro s hs
    exact ⟨hs.1, fun _ hts ht => ⟨ht, hts.trans hs.2⟩⟩

private def vertex0 : TotalFace edgeNat := ⟨{0}, by change ({0} : Finset ℕ).Nonempty ∧ _; decide⟩
private def vertex1 : TotalFace edgeNat := ⟨{1}, by change ({1} : Finset ℕ).Nonempty ∧ _; decide⟩
private def edge : TotalFace edgeNat := ⟨{0, 1}, by change ({0, 1} : Finset ℕ).Nonempty ∧ _; decide⟩

private theorem edgeNat_cases (s : TotalFace edgeNat) :
    s = vertex0 ∨ s = vertex1 ∨ s = edge := by
  have hs : s.val ⊆ ({0, 1} : Finset ℕ) := s.property.2
  have hn : s.val.Nonempty := s.property.1
  by_cases h0 : 0 ∈ s.val
  · by_cases h1 : 1 ∈ s.val
    · right; right
      apply Subtype.ext
      change s.val = ({0, 1} : Finset ℕ)
      apply Finset.Subset.antisymm hs
      simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
      exact ⟨h0, h1⟩
    · left
      apply Subtype.ext
      change s.val = ({0} : Finset ℕ)
      apply Finset.Subset.antisymm
      · intro x hx
        have hx' := hs hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx'
        rcases hx' with h | h
        · simpa using h
        · exact (h1 (h ▸ hx)).elim
      · simpa only [Finset.singleton_subset_iff] using h0
  · by_cases h1 : 1 ∈ s.val
    · right; left
      apply Subtype.ext
      change s.val = ({1} : Finset ℕ)
      apply Finset.Subset.antisymm
      · intro x hx
        have hx' := hs hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx'
        rcases hx' with h | h
        · exact (h0 (h ▸ hx)).elim
        · simpa using h
      · simpa only [Finset.singleton_subset_iff] using h1
    · obtain ⟨x, hx⟩ := hn
      have hx' := hs hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx'
      rcases hx' with h | h
      · exact (h0 (h ▸ hx)).elim
      · exact (h1 (h ▸ hx)).elim

private def edgeEnum : Fin 3 ≃ TotalFace edgeNat where
  toFun := fun i => if i = 0 then vertex1 else if i = 1 then vertex0 else edge
  invFun := fun s => if s = vertex1 then 0 else if s = vertex0 then 1 else 2
  left_inv := by intro i; fin_cases i <;> decide
  right_inv := by
    intro s
    rcases edgeNat_cases s with h | h | h <;> subst s <;> decide

private noncomputable instance edgeNatFintype : Fintype (TotalFace edgeNat) :=
  Fintype.ofEquiv (Fin 3) edgeEnum

private theorem edgeNat_card : Fintype.card (TotalFace edgeNat) = 3 := by
  simpa using (Fintype.card_congr edgeEnum).symm

private def edgeEnumCard : Fin (Fintype.card (TotalFace edgeNat)) ≃ TotalFace edgeNat :=
  edgeEnum

private def constantFilter : FilterFunction edgeNat ℕ where
  value := fun _ => 0
  mono := by intros; exact le_rfl

private def gradedFilter : FilterFunction edgeNat ℕ where
  value := fun s => s.val.card - 1
  mono := by
    intro s t h
    exact Nat.sub_le_sub_right (Finset.card_le_card h) 1

private def negativeFilter : FilterFunction edgeNat ℕ where
  value := fun s => if s = vertex1 then 1 else if s = vertex0 then 0 else 2
  mono := by
    intro s t h
    rcases edgeNat_cases s with hs | hs | hs <;>
      rcases edgeNat_cases t with ht | ht | ht <;>
      subst s <;> subst t <;>
      simp_all [vertex0, vertex1, edge]
    all_goals decide

private theorem edgeNat_card_definitional : Fintype.card (TotalFace edgeNat) = 3 := by
  rfl

private theorem graded_mono3 : Monotone (gradedFilter.value ∘ edgeEnum) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [gradedFilter, edgeEnum, vertex0, vertex1, edge]

private theorem graded_mono : Monotone (gradedFilter.value ∘ edgeEnumCard) := by
  exact graded_mono3

private theorem graded_reflection :
    ∀ i j, gradedFilter.value (edgeEnumCard i) < gradedFilter.value (edgeEnumCard j) →
      i < j :=
  (CompatibleOrder.monotone_enum_iff_reflects_lt gradedFilter edgeEnumCard).mp graded_mono

private theorem graded_mono_from_reflection :
    Monotone (gradedFilter.value ∘ edgeEnumCard) :=
  (CompatibleOrder.monotone_enum_iff_reflects_lt gradedFilter edgeEnumCard).mpr
    graded_reflection

private theorem constant_reflection :
    ∀ i j, constantFilter.value (edgeEnumCard i) < constantFilter.value (edgeEnumCard j) →
      i < j := by
  intro i j h
  exact (Nat.not_lt_zero _ h).elim

private theorem constant_mono_from_reflection :
    Monotone (constantFilter.value ∘ edgeEnumCard) :=
  (CompatibleOrder.monotone_enum_iff_reflects_lt constantFilter edgeEnumCard).mpr
    constant_reflection

private theorem constant_not_strictMono :
    ¬ StrictMono (constantFilter.value ∘ edgeEnumCard) := by
  intro h
  have h01 := h (show (0 : Fin 3) < 1 from by decide)
  exact (Nat.not_lt_zero _ h01).elim

private theorem graded_witness :
    ∃ h : CompatibleOrder gradedFilter,
      h.enum.symm vertex0 < h.enum.symm edge ∧
      h.enum.symm vertex1 < h.enum.symm edge ∧
      Monotone (gradedFilter.value ∘ h.enum) := by
  obtain ⟨h⟩ := exists_compatibleOrder gradedFilter
  refine ⟨h, ?_, ?_, h.monotone⟩
  · simpa using h.face_lt (h.enum.symm vertex0) (h.enum.symm edge)
      (by simpa using (show vertex0.val ⊂ edge.val by decide))
  · simpa using h.face_lt (h.enum.symm vertex1) (h.enum.symm edge)
      (by simpa using (show vertex1.val ⊂ edge.val by decide))

private theorem tied_witness :
    ∃ h : CompatibleOrder constantFilter,
      h.enum.symm vertex0 < h.enum.symm edge ∧
      h.enum.symm vertex1 < h.enum.symm edge ∧
      Monotone (constantFilter.value ∘ h.enum) := by
  obtain ⟨h⟩ := exists_compatibleOrder constantFilter
  refine ⟨h, ?_, ?_, h.monotone⟩
  · simpa using h.face_lt (h.enum.symm vertex0) (h.enum.symm edge)
      (by simpa using (show vertex0.val ⊂ edge.val by decide))
  · simpa using h.face_lt (h.enum.symm vertex1) (h.enum.symm edge)
      (by simpa using (show vertex1.val ⊂ edge.val by decide))

private theorem negative_value_vertex0 : negativeFilter.value vertex0 = 0 := by
  have h : vertex0 ≠ vertex1 := by decide
  simp [negativeFilter, h]

private theorem negative_value_vertex1 : negativeFilter.value vertex1 = 1 := by
  simp [negativeFilter]

private theorem enum_zero : edgeEnumCard (0 : Fin 3) = vertex1 := by decide
private theorem enum_one : edgeEnumCard (1 : Fin 3) = vertex0 := by decide

private theorem negative_not_mono :
    ¬ Monotone (negativeFilter.value ∘ edgeEnumCard) := by
  intro h
  have h01 := h (show (0 : Fin 3) ≤ 1 from by decide)
  change negativeFilter.value (edgeEnumCard (0 : Fin 3)) ≤
    negativeFilter.value (edgeEnumCard (1 : Fin 3)) at h01
  have hh : (1 : ℕ) ≤ 0 := by
    simpa only [enum_zero, enum_one,
      negative_value_vertex0, negative_value_vertex1] using h01
  omega

private theorem negative_not_reflection :
    ¬ (∀ i j, negativeFilter.value (edgeEnumCard i) <
        negativeFilter.value (edgeEnumCard j) → i < j) := by
  intro h
  have hr := h
    (1 : Fin 3)
    (0 : Fin 3)
    (by simpa only [enum_zero, enum_one,
      negative_value_vertex0, negative_value_vertex1] using
        (show (0 : ℕ) < 1 by decide))
  exact (by decide : ¬ ((1 : Fin 3) < 0)) hr

private def badEnum : Fin 3 ≃ TotalFace edgeNat where
  toFun := fun i => if i = 0 then edge else if i = 1 then vertex0 else vertex1
  invFun := fun s => if s = edge then 0 else if s = vertex0 then 1 else 2
  left_inv := by intro i; fin_cases i <;> decide
  right_inv := by
    intro s
    rcases edgeNat_cases s with h | h | h <;> subst s <;> decide

private def badEnumCard : Fin (Fintype.card (TotalFace edgeNat)) ≃ TotalFace edgeNat :=
  badEnum

private theorem badEnum_constant_mono :
    Monotone (constantFilter.value ∘ badEnumCard) := by
  intro i j _
  exact le_rfl

private theorem badEnum_constant_reflection :
    ∀ i j, constantFilter.value (badEnumCard i) < constantFilter.value (badEnumCard j) →
      i < j :=
  (CompatibleOrder.monotone_enum_iff_reflects_lt constantFilter badEnumCard).mp
    badEnum_constant_mono

private theorem badEnum_not_compatible :
    ¬ ∃ h : CompatibleOrder constantFilter, h.enum = badEnumCard := by
  rintro ⟨h, he⟩
  have hp : (h.enum (1 : Fin 3)).val ⊂ (h.enum (0 : Fin 3)).val := by
    rw [he]
    decide
  have hi := h.face_lt _ _ hp
  exact (by decide : ¬ ((1 : Fin 3) < 0)) hi

#print axioms bottomFilter
#print axioms bottomIsEmpty
#print axioms bottomFintype
#print axioms bottom_exists_fin0
#print axioms bottom_exists_nat
#print axioms bottom_empty_index
#print axioms bottom_fin0_empty_index
#print axioms bottom_nat_empty_index
#print axioms edgeNat
#print axioms vertex0
#print axioms vertex1
#print axioms edge
#print axioms edgeNat_cases
#print axioms edgeEnum
#print axioms edgeNatFintype
#print axioms edgeNat_card
#print axioms edgeEnumCard
#print axioms constantFilter
#print axioms gradedFilter
#print axioms negativeFilter
#print axioms edgeNat_card_definitional
#print axioms graded_mono3
#print axioms graded_mono
#print axioms graded_reflection
#print axioms graded_mono_from_reflection
#print axioms constant_reflection
#print axioms constant_mono_from_reflection
#print axioms constant_not_strictMono
#print axioms graded_witness
#print axioms tied_witness
#print axioms negative_value_vertex0
#print axioms negative_value_vertex1
#print axioms enum_zero
#print axioms enum_one
#print axioms negative_not_mono
#print axioms negative_not_reflection
#print axioms badEnum
#print axioms badEnumCard
#print axioms badEnum_constant_mono
#print axioms badEnum_constant_reflection
#print axioms badEnum_not_compatible

end TDA.Filtration.Examples.CompatibleOrderExistence
