import TDA.Filtration.OrderingEquivalent

set_option autoImplicit false

namespace TDA.Filtration.OrderingEquivalentExamples

universe u' v' w'

private def emptyFilter (V : Type u') (α : Type v') [LinearOrder α] :
    FilterFunction (⊥ : PreAbstractSimplicialComplex V) α where
  value := fun s => ((mem_bot_iff s.val).mp s.property).elim
  mono := by
    intro s t _
    exact ((mem_bot_iff s.val).mp s.property).elim

private theorem empty_equiv (V : Type u') :
    OrderingEquivalent (emptyFilter V Unit) (emptyFilter V Empty) := by
  intro s t
  exact ((mem_bot_iff s.val).mp s.property).elim

private theorem empty_iso (V : Type u') :
    ∃ e : Set.range (emptyFilter V Unit).value ≃o
        Set.range (emptyFilter V Empty).value,
      ∀ s, (e ⟨(emptyFilter V Unit).value s, ⟨s, rfl⟩⟩).val =
        (emptyFilter V Empty).value s :=
  (orderingEquivalent_iff_exists_rangeOrderIso _ _).mp (empty_equiv V)

private theorem empty_fin0 :
    OrderingEquivalent (emptyFilter (Fin 0) Unit) (emptyFilter (Fin 0) Empty) ∧
    (∃ e : Set.range (emptyFilter (Fin 0) Unit).value ≃o
        Set.range (emptyFilter (Fin 0) Empty).value,
      ∀ s, (e ⟨(emptyFilter (Fin 0) Unit).value s, ⟨s, rfl⟩⟩).val =
        (emptyFilter (Fin 0) Empty).value s) :=
  ⟨empty_equiv _, empty_iso _⟩

private theorem empty_fin2 :
    OrderingEquivalent (emptyFilter (Fin 2) Unit) (emptyFilter (Fin 2) Empty) ∧
    (∃ e : Set.range (emptyFilter (Fin 2) Unit).value ≃o
        Set.range (emptyFilter (Fin 2) Empty).value,
      ∀ s, (e ⟨(emptyFilter (Fin 2) Unit).value s, ⟨s, rfl⟩⟩).val =
        (emptyFilter (Fin 2) Empty).value s) :=
  ⟨empty_equiv _, empty_iso _⟩

private theorem no_unit_to_empty : ¬ Nonempty (Unit → Empty) := by
  rintro ⟨φ⟩
  exact (φ ()).elim

private def singletonNat :
    FilterFunction (singletonFace (0 : Fin 2)) ℕ where
  value := fun _ => 3
  mono := by intros; exact le_refl 3

private def singletonInt :
    FilterFunction (singletonFace (0 : Fin 2)) ℤ where
  value := fun _ => -2
  mono := by intros; exact le_refl (-2 : ℤ)

private def singletonFace0 : TDA.Simplicial.TotalFace (singletonFace (0 : Fin 2)) :=
  ⟨{0}, (mem_singletonFace_iff 0 {0}).mpr rfl⟩

private theorem singleton_equiv : OrderingEquivalent singletonNat singletonInt := by
  intro s t
  simp [singletonNat, singletonInt]

private theorem singleton_attained :
    singletonNat.sublevel (singletonNat.value singletonFace0) =
      singletonInt.sublevel (singletonInt.value singletonFace0) ∧
    singletonNat.sublevel 3 = singletonFace (0 : Fin 2) ∧
    singletonInt.sublevel (-2) = singletonFace (0 : Fin 2) ∧
    ({1} : Finset (Fin 2)) ∉ singletonNat.sublevel 3 := by
  have hn : singletonNat.sublevel 3 = singletonFace (0 : Fin 2) := by
    apply FilterFunction.sublevel_eq_self_of_forall_le
    intro s
    exact le_refl 3
  have hi : singletonInt.sublevel (-2) = singletonFace (0 : Fin 2) := by
    apply FilterFunction.sublevel_eq_self_of_forall_le
    intro s
    exact le_refl (-2 : ℤ)
  refine ⟨singleton_equiv.sublevel_eq singletonFace0, hn, hi, ?_⟩
  rw [hn]
  exact (mem_singletonFace_iff 0 {1}).not.mpr (by decide)

private def singletonUnit :
    FilterFunction (singletonFace (0 : Fin 2)) Unit where
  value := fun _ => ()
  mono := by intros; exact le_refl ()

private def singletonZeroInt :
    FilterFunction (singletonFace (0 : Fin 2)) ℤ where
  value := fun _ => 0
  mono := by intros; exact le_refl (0 : ℤ)

private theorem arbitrary_threshold_mismatch :
    OrderingEquivalent singletonUnit singletonZeroInt ∧
    singletonUnit.sublevel () = singletonFace (0 : Fin 2) ∧
    singletonZeroInt.sublevel (-1) = ⊥ ∧
    ∀ r : Unit, singletonUnit.sublevel r ≠ singletonZeroInt.sublevel (-1) := by
  have he : OrderingEquivalent singletonUnit singletonZeroInt := by
    intro s t
    simp [singletonUnit, singletonZeroInt]
  have hu : singletonUnit.sublevel () = singletonFace (0 : Fin 2) := by
    apply FilterFunction.sublevel_eq_self_of_forall_le
    intro s
    exact le_refl ()
  have hz : singletonZeroInt.sublevel (-1) = ⊥ := by
    apply FilterFunction.sublevel_eq_bot_of_forall_lt
    intro s
    norm_num [singletonZeroInt]
  refine ⟨he, hu, hz, ?_⟩
  intro r
  cases r
  rw [hu, hz]
  intro h
  have hs : ({0} : Finset (Fin 2)) ∈ (⊥ : PreAbstractSimplicialComplex (Fin 2)) := by
    rw [← h]
    exact singletonFace0.property
  exact (mem_bot_iff _).mp hs

private def edgeK : PreAbstractSimplicialComplex (Fin 2) := ⊤

private def vertex0 : TDA.Simplicial.TotalFace edgeK :=
  ⟨{0}, by change ({0} : Finset (Fin 2)).Nonempty; simp⟩

private def vertex1 : TDA.Simplicial.TotalFace edgeK :=
  ⟨{1}, by change ({1} : Finset (Fin 2)).Nonempty; simp⟩

private def edge : TDA.Simplicial.TotalFace edgeK :=
  ⟨{0, 1}, by change ({0, 1} : Finset (Fin 2)).Nonempty; simp⟩

private def edgeF : FilterFunction edgeK ℤ where
  value := fun s => if 0 ∈ s.val ∧ 1 ∈ s.val then 1 else 0
  mono := by
    intro s t hst
    split_ifs with hs ht
    · exact le_refl 1
    · exact (ht ⟨hst hs.1, hst hs.2⟩).elim
    · norm_num
    · exact le_refl 0

private def edgeG : FilterFunction edgeK ℤ where
  value := fun s => 2 * edgeF.value s + 1
  mono := by
    intro s t hst
    have h := edgeF.mono hst
    omega

private theorem edge_equiv : OrderingEquivalent edgeF edgeG := by
  intro s t
  change edgeF.value s ≤ edgeF.value t ↔
    2 * edgeF.value s + 1 ≤ 2 * edgeF.value t + 1
  omega

private theorem edge_values :
    edgeF.value vertex0 = 0 ∧ edgeF.value vertex1 = 0 ∧
    edgeF.value edge = 1 ∧ edgeG.value vertex0 = 1 ∧
    edgeG.value vertex1 = 1 ∧ edgeG.value edge = 3 := by
  decide

private theorem edge_iso_and_sublevels :
    (∃ e : Set.range edgeF.value ≃o Set.range edgeG.value,
      (e ⟨edgeF.value vertex0, ⟨vertex0, rfl⟩⟩).val = edgeG.value vertex0 ∧
      (e ⟨edgeF.value vertex1, ⟨vertex1, rfl⟩⟩).val = edgeG.value vertex1 ∧
      (e ⟨edgeF.value edge, ⟨edge, rfl⟩⟩).val = edgeG.value edge) ∧
    edgeF.sublevel (edgeF.value vertex0) = edgeG.sublevel (edgeG.value vertex0) ∧
    edgeF.sublevel (edgeF.value vertex1) = edgeG.sublevel (edgeG.value vertex1) ∧
    edgeF.sublevel (edgeF.value edge) = edgeG.sublevel (edgeG.value edge) := by
  obtain ⟨e, he⟩ := (orderingEquivalent_iff_exists_rangeOrderIso edgeF edgeG).mp edge_equiv
  exact ⟨⟨e, he vertex0, he vertex1, he edge⟩,
    edge_equiv.sublevel_eq vertex0,
    edge_equiv.sublevel_eq vertex1,
    edge_equiv.sublevel_eq edge⟩

private def edgeBreak : FilterFunction edgeK ℤ where
  value := fun s =>
    (if 1 ∈ s.val then 1 else 0) +
      (if 0 ∈ s.val ∧ 1 ∈ s.val then 1 else 0)
  mono := by
    intro s t hst
    have h₁ : (if 1 ∈ s.val then (1 : ℤ) else 0) ≤
        (if 1 ∈ t.val then 1 else 0) := by
      split_ifs with hs ht <;> try omega
      exact (ht (hst hs)).elim
    have h₂ : (if 0 ∈ s.val ∧ 1 ∈ s.val then (1 : ℤ) else 0) ≤
        (if 0 ∈ t.val ∧ 1 ∈ t.val then 1 else 0) := by
      split_ifs with hs ht <;> try omega
      exact (ht ⟨hst hs.1, hst hs.2⟩).elim
    omega

private theorem break_values :
    edgeBreak.value vertex0 = 0 ∧ edgeBreak.value vertex1 = 1 ∧
    edgeBreak.value edge = 2 := by
  decide

private theorem break_preserves_forward_strict :
    ∀ s t : TDA.Simplicial.TotalFace edgeK,
      edgeF.value s < edgeF.value t → edgeBreak.value s < edgeBreak.value t := by
  intro s t h
  have ht : 0 ∈ t.val ∧ 1 ∈ t.val := by
    by_contra hn
    have : edgeF.value t = 0 := by simp [edgeF, hn]
    have hs : 0 ≤ edgeF.value s := by
      dsimp [edgeF]
      split_ifs <;> omega
    omega
  have hs : ¬ (0 ∈ s.val ∧ 1 ∈ s.val) := by
    intro hs
    have : edgeF.value s = 1 := by simp [edgeF, hs]
    have htmax : edgeF.value t ≤ 1 := by
      dsimp [edgeF]
      split_ifs <;> omega
    omega
  simp [edgeBreak, ht, hs]
  split_ifs <;> omega

private theorem break_not_equiv : ¬ OrderingEquivalent edgeF edgeBreak := by
  intro h
  have hfalse : edgeBreak.value vertex1 ≤ edgeBreak.value vertex0 :=
    (h vertex1 vertex0).mp (by decide)
  norm_num [edgeBreak, vertex0, vertex1] at hfalse

private def edgeNat : FilterFunction edgeK ℕ where
  value := fun s => if 0 ∈ s.val ∧ 1 ∈ s.val then 1 else 0
  mono := by
    intro s t hst
    split_ifs with hs ht
    · exact le_refl 1
    · exact (ht ⟨hst hs.1, hst hs.2⟩).elim
    · omega
    · exact le_refl 0

private theorem cross_equiv : OrderingEquivalent edgeNat edgeF := by
  intro s t
  dsimp [edgeNat, edgeF]
  split_ifs <;> omega

private theorem cross_nat_int_mpr : OrderingEquivalent edgeNat edgeF :=
  (orderingEquivalent_iff_exists_rangeOrderIso edgeNat edgeF).mpr
    ((orderingEquivalent_iff_exists_rangeOrderIso edgeNat edgeF).mp cross_equiv)

private theorem cross_int_nat_mpr : OrderingEquivalent edgeF edgeNat :=
  (orderingEquivalent_iff_exists_rangeOrderIso edgeF edgeNat).mpr
    ((orderingEquivalent_iff_exists_rangeOrderIso edgeF edgeNat).mp cross_equiv.symm)

private theorem cross_both_directions :
    (∃ e : Set.range edgeNat.value ≃o Set.range edgeF.value,
      ∀ s, (e ⟨edgeNat.value s, ⟨s, rfl⟩⟩).val = edgeF.value s) ∧
    (∃ e : Set.range edgeF.value ≃o Set.range edgeNat.value,
      ∀ s, (e ⟨edgeF.value s, ⟨s, rfl⟩⟩).val = edgeNat.value s) ∧
    edgeNat.sublevel (edgeNat.value edge) = edgeF.sublevel (edgeF.value edge) ∧
    OrderingEquivalent edgeNat edgeF ∧ OrderingEquivalent edgeF edgeNat := by
  exact ⟨(orderingEquivalent_iff_exists_rangeOrderIso edgeNat edgeF).mp cross_equiv,
    (orderingEquivalent_iff_exists_rangeOrderIso edgeF edgeNat).mp cross_equiv.symm,
    cross_equiv.sublevel_eq edge,
    cross_nat_int_mpr,
    cross_int_nat_mpr⟩

private theorem range_iso_unique
    {V : Type u'} {α : Type v'} {β : Type w'}
    [LinearOrder α] [LinearOrder β]
    {K : PreAbstractSimplicialComplex V}
    (f : FilterFunction K α) (g : FilterFunction K β)
    (e d : Set.range f.value ≃o Set.range g.value)
    (he : ∀ s, (e ⟨f.value s, ⟨s, rfl⟩⟩).val = g.value s)
    (hd : ∀ s, (d ⟨f.value s, ⟨s, rfl⟩⟩).val = g.value s) : e = d := by
  apply OrderIso.ext
  funext a
  rcases a with ⟨a, ⟨s, rfl⟩⟩
  apply Subtype.ext
  exact (he s).trans (hd s).symm

#check empty_fin0
#check empty_fin2
#check no_unit_to_empty
#check singleton_attained
#check arbitrary_threshold_mismatch
#check edge_values
#check edge_iso_and_sublevels
#check break_values
#check break_preserves_forward_strict
#check break_not_equiv
#check cross_both_directions
#check cross_nat_int_mpr
#check cross_int_nat_mpr
#check range_iso_unique

#print axioms empty_fin0
#print axioms empty_fin2
#print axioms no_unit_to_empty
#print axioms singleton_attained
#print axioms arbitrary_threshold_mismatch
#print axioms edge_values
#print axioms edge_iso_and_sublevels
#print axioms break_values
#print axioms break_preserves_forward_strict
#print axioms break_not_equiv
#print axioms cross_both_directions
#print axioms cross_nat_int_mpr
#print axioms cross_int_nat_mpr
#print axioms range_iso_unique

#print axioms emptyFilter
#print axioms empty_equiv
#print axioms empty_iso
#print axioms singletonNat
#print axioms singletonInt
#print axioms singletonFace0
#print axioms singleton_equiv
#print axioms singletonUnit
#print axioms singletonZeroInt
#print axioms edgeK
#print axioms vertex0
#print axioms vertex1
#print axioms edge
#print axioms edgeF
#print axioms edgeG
#print axioms edge_equiv
#print axioms edgeBreak
#print axioms edgeNat
#print axioms cross_equiv


end TDA.Filtration.OrderingEquivalentExamples
