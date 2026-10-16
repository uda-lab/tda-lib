import TDA.Persistence.FiniteMonoCounts
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Prod.Lex

/-!
# Canonical barcode embeddings from finite-chain monomorphisms

At a fixed death, occurrences are ordered by ascending birth and then their existing
list index. A monomorphism supplies the prefix-count inequalities; the embedding pairs
equal ordinals. It is compatible with identities and composition of monomorphisms.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence.FiniteBarcode

open CategoryTheory
open scoped BigOperators

variable {s : ℕ}

/-- The interval at an existing list-occurrence label. -/
noncomputable def occurrence (B : Multiset (FiniteInterval s))
    (i : BarcodeOccurrence s B) : FiniteInterval s :=
  B.toList.get i

/-- An occurrence with one specified observed death, retaining its original label. -/
@[ext] structure DeathOccurrence (B : Multiset (FiniteInterval s)) (d : ℕ) where
  index : BarcodeOccurrence s B
  death_eq : (occurrence B index).death = d

private def deathEquiv (B : Multiset (FiniteInterval s)) (d : ℕ) :
    DeathOccurrence B d ≃ {i : BarcodeOccurrence s B // (occurrence B i).death = d} where
  toFun i := ⟨i.index, i.death_eq⟩
  invFun i := ⟨i.val, i.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance deathOccurrenceFintype (B : Multiset (FiniteInterval s)) (d : ℕ) :
    Fintype (DeathOccurrence B d) := Fintype.ofEquiv _ (deathEquiv B d).symm

noncomputable instance deathOccurrenceLinearOrder (B : Multiset (FiniteInterval s)) (d : ℕ) :
    LinearOrder (DeathOccurrence B d) :=
  LinearOrder.lift' (fun i => toLex ((occurrence B i.index).birth, i.index)) (by
    intro i j h
    exact DeathOccurrence.ext (congrArg (fun x => (ofLex x).2) h))

/-- Increasing enumeration by `(birth, original occurrence index)` at one death. -/
noncomputable def deathEnumeration (B : Multiset (FiniteInterval s)) (d : ℕ) :
    Fin (Fintype.card (DeathOccurrence B d)) ≃o DeathOccurrence B d :=
  Fintype.orderIsoFinOfCardEq _ rfl

/-- The zero-based ordinal of an occurrence among those with the same death. -/
noncomputable def deathOrdinal (B : Multiset (FiniteInterval s)) (i : BarcodeOccurrence s B) : ℕ :=
  ((deathEnumeration B (occurrence B i).death).symm ⟨i, rfl⟩).val

private theorem list_count (xs : List (FiniteInterval s)) (p : FiniteInterval s → Prop)
    [DecidablePred p] :
    (∑ i : Fin xs.length, if p (xs.get i) then 1 else 0) =
      (xs : Multiset (FiniteInterval s)).countP p := by
  induction xs with
  | nil => simp
  | cons I xs ih =>
    change (∑ i : Fin (xs.length + 1), if p ((I :: xs).get i) then 1 else 0) = _
    rw [Fin.sum_univ_succ]
    change (if p I then 1 else 0) + (∑ i : Fin xs.length, if p (xs.get i) then 1 else 0) = _
    rw [ih]
    by_cases h : p I <;> simp [Multiset.coe_countP, h, add_comm]

private theorem occurrence_count (B : Multiset (FiniteInterval s))
    (p : FiniteInterval s → Prop) [DecidablePred p] :
    Fintype.card {i : BarcodeOccurrence s B // p (occurrence B i)} = B.countP p := by
  rw [Fintype.card_subtype, Finset.card_filter]
  change (∑ i : Fin B.toList.length, if p (B.toList.get i) then 1 else 0) = _
  calc
    _ = (B.toList : Multiset (FiniteInterval s)).countP p := list_count B.toList p
    _ = B.countP p := congrArg (Multiset.countP p) (Multiset.coe_toList B)

private def prefixEquiv (B : Multiset (FiniteInterval s)) (b d : ℕ) :
    {i : DeathOccurrence B d // (occurrence B i.index).birth ≤ b} ≃
      {i : BarcodeOccurrence s B // (occurrence B i).birth ≤ b ∧ (occurrence B i).death = d} where
  toFun i := ⟨i.val.index, i.property, i.val.death_eq⟩
  invFun i := ⟨⟨i.val, i.property.2⟩, i.property.1⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem prefix_card (B : Multiset (FiniteInterval s)) (b d : ℕ) :
    Fintype.card {i : DeathOccurrence B d // (occurrence B i.index).birth ≤ b} =
      deathPrefixCount B b d := by
  classical
  rw [Fintype.card_congr (prefixEquiv B b d),
    occurrence_count B (fun I => I.birth ≤ b ∧ I.death = d)]
  rfl

private theorem death_card (B : Multiset (FiniteInterval s)) (d : ℕ) (hd : 0 < d) :
    Fintype.card (DeathOccurrence B d) = deathPrefixCount B (d - 1) d := by
  classical
  rw [Fintype.card_congr (deathEquiv B d), occurrence_count B (fun I => I.death = d)]
  unfold deathPrefixCount
  apply Multiset.countP_congr rfl
  intro I _
  apply propext
  have := I.birth_lt_death
  omega

private theorem birth_mono (B : Multiset (FiniteInterval s)) (d : ℕ)
    {i j : DeathOccurrence B d} (h : i ≤ j) :
    (occurrence B i.index).birth ≤ (occurrence B j.index).birth :=
  Prod.Lex.monotone_fst _ _ h

private theorem lt_of_birth_lt (B : Multiset (FiniteInterval s)) (d : ℕ)
    {i j : DeathOccurrence B d}
    (h : (occurrence B i.index).birth < (occurrence B j.index).birth) : i < j :=
  Prod.Lex.toLex_lt_toLex.mpr (Or.inl h)

private theorem ordinal_lt_prefix (B : Multiset (FiniteInterval s)) (d : ℕ)
    (x : DeathOccurrence B d) :
    ((deathEnumeration B d).symm x).val <
      deathPrefixCount B (occurrence B x.index).birth d := by
  classical
  let r := (deathEnumeration B d).symm x
  let f : Fin (r.val + 1) → {i : DeathOccurrence B d //
      (occurrence B i.index).birth ≤ (occurrence B x.index).birth} := fun a => by
    let q : Fin (Fintype.card (DeathOccurrence B d)) := ⟨a.val, by have := r.isLt; omega⟩
    have hqr : q ≤ r := by change a.val ≤ r.val; have := a.isLt; omega
    exact ⟨deathEnumeration B d q, by
      simpa [r] using birth_mono B d ((deathEnumeration B d).monotone hqr)⟩
  have hf : Function.Injective f := by
    intro a b h
    apply Fin.ext
    have he := congrArg Subtype.val h
    change deathEnumeration B d ⟨a.val, _⟩ = deathEnumeration B d ⟨b.val, _⟩ at he
    exact congrArg (fun q : Fin (Fintype.card (DeathOccurrence B d)) => q.val)
      ((deathEnumeration B d).injective he)
  have h := Fintype.card_le_of_injective f hf
  rw [Fintype.card_fin, prefix_card] at h
  omega

private theorem prefix_le_ordinal (B : Multiset (FiniteInterval s)) (b d : ℕ)
    (x : DeathOccurrence B d) (hb : b < (occurrence B x.index).birth) :
    deathPrefixCount B b d ≤ ((deathEnumeration B d).symm x).val := by
  classical
  let r := (deathEnumeration B d).symm x
  let f : {i : DeathOccurrence B d // (occurrence B i.index).birth ≤ b} → Fin r.val :=
    fun i => ⟨((deathEnumeration B d).symm i.val).val,
      (deathEnumeration B d).symm.strictMono
        (lt_of_birth_lt B d (i.property.trans_lt hb))⟩
  have hf : Function.Injective f := by
    intro a c h
    apply Subtype.ext
    apply (deathEnumeration B d).symm.injective
    exact Fin.ext (congrArg (fun a : Fin r.val => a.val) h)
  have h := Fintype.card_le_of_injective f hf
  rwa [Fintype.card_fin, prefix_card] at h

/-- An occurrence's ordinal is below the prefix count at its own birth. -/
theorem deathOrdinal_lt_deathPrefixCount (B : Multiset (FiniteInterval s))
    (i : BarcodeOccurrence s B) :
    deathOrdinal B i < deathPrefixCount B (occurrence B i).birth (occurrence B i).death :=
  ordinal_lt_prefix B _ ⟨i, rfl⟩

/-- A cutoff before an occurrence's birth counts at most its ordinal. -/
theorem deathPrefixCount_le_deathOrdinal (B : Multiset (FiniteInterval s))
    (i : BarcodeOccurrence s B) (b : ℕ) (hb : b < (occurrence B i).birth) :
    deathPrefixCount B b (occurrence B i).death ≤ deathOrdinal B i :=
  prefix_le_ordinal B b _ ⟨i, rfl⟩ hb

/-- Every birth prefix is bounded by the cardinality of its death group. -/
theorem deathPrefixCount_le_card (B : Multiset (FiniteInterval s)) (b d : ℕ) :
    deathPrefixCount B b d ≤ Fintype.card (DeathOccurrence B d) := by
  rw [← prefix_card]
  exact Fintype.card_subtype_le _

variable {k : Type u} [Field k]
variable {M N : PModule.{u,0,u} k (Fin s)}
variable [∀ i, FiniteDimensional k (M.obj i)] [∀ i, FiniteDimensional k (N.obj i)]

private theorem death_card_le (j : M ⟶ N) (hj : ∀ i, Function.Injective (j.app i).hom)
    (d : ℕ) : Fintype.card (DeathOccurrence (rankBarcode M) d) ≤
      Fintype.card (DeathOccurrence (rankBarcode N) d) := by
  classical
  by_cases h : Nonempty (DeathOccurrence (rankBarcode M) d)
  · obtain ⟨x⟩ := h
    have hdpos : 0 < d := by
      have := (occurrence (rankBarcode M) x.index).birth_lt_death
      rw [x.death_eq] at this
      omega
    have hds : d ≤ s := x.death_eq ▸ (occurrence (rankBarcode M) x.index).death_le_size
    rw [death_card _ _ hdpos, death_card _ _ hdpos]
    exact deathPrefixCount_le_of_injective j hj _ _ (by omega) hds
  · have := not_nonempty_iff.mp h
    simp

private noncomputable def groupEmbedding (j : M ⟶ N)
    (hj : ∀ i, Function.Injective (j.app i).hom) (d : ℕ) :
    DeathOccurrence (rankBarcode M) d ↪ DeathOccurrence (rankBarcode N) d :=
  ((deathEnumeration (rankBarcode M) d).symm.toEmbedding.trans
    (Fin.castLEEmb (death_card_le j hj d))).trans
      (deathEnumeration (rankBarcode N) d).toEmbedding

private theorem groupEmbedding_rank (j : M ⟶ N)
    (hj : ∀ i, Function.Injective (j.app i).hom) (d : ℕ)
    (x : DeathOccurrence (rankBarcode M) d) :
    ((deathEnumeration (rankBarcode N) d).symm (groupEmbedding j hj d x)).val =
      ((deathEnumeration (rankBarcode M) d).symm x).val := by
  simp [groupEmbedding]

private theorem ordinal_in_group (B : Multiset (FiniteInterval s)) (d : ℕ)
    (x : DeathOccurrence B d) :
    deathOrdinal B x.index = ((deathEnumeration B d).symm x).val := by
  cases x with
  | mk i hi => cases hi; rfl

private noncomputable def mapOccurrence (j : M ⟶ N)
    (hj : ∀ i, Function.Injective (j.app i).hom) (i : BarcodeOccurrence s (rankBarcode M)) :
    BarcodeOccurrence s (rankBarcode N) :=
  (groupEmbedding j hj (occurrence (rankBarcode M) i).death ⟨i, rfl⟩).index

private theorem mapOccurrence_death (j : M ⟶ N)
    (hj : ∀ i, Function.Injective (j.app i).hom) (i : BarcodeOccurrence s (rankBarcode M)) :
    (occurrence (rankBarcode N) (mapOccurrence j hj i)).death =
      (occurrence (rankBarcode M) i).death :=
  (groupEmbedding j hj _ ⟨i, rfl⟩).death_eq

private theorem mapOccurrence_in_group (j : M ⟶ N)
    (hj : ∀ i, Function.Injective (j.app i).hom) (d : ℕ)
    (x : DeathOccurrence (rankBarcode M) d) :
    mapOccurrence j hj x.index = (groupEmbedding j hj d x).index := by
  cases x with
  | mk i hi => cases hi; rfl

private theorem mapOccurrence_ordinal (j : M ⟶ N)
    (hj : ∀ i, Function.Injective (j.app i).hom) (i : BarcodeOccurrence s (rankBarcode M)) :
    deathOrdinal (rankBarcode N) (mapOccurrence j hj i) = deathOrdinal (rankBarcode M) i := by
  let d := (occurrence (rankBarcode M) i).death
  let x : DeathOccurrence (rankBarcode M) d := ⟨i, rfl⟩
  rw [mapOccurrence_in_group j hj d x, ordinal_in_group,
    groupEmbedding_rank, ← ordinal_in_group]

private theorem occurrence_eq_of_death_ordinal (B : Multiset (FiniteInterval s))
    (i j : BarcodeOccurrence s B) (hd : (occurrence B i).death = (occurrence B j).death)
    (ho : deathOrdinal B i = deathOrdinal B j) : i = j := by
  let d := (occurrence B i).death
  let x : DeathOccurrence B d := ⟨i, rfl⟩
  let y : DeathOccurrence B d := ⟨j, hd.symm⟩
  have hxy : (deathEnumeration B d).symm x = (deathEnumeration B d).symm y := by
    apply Fin.ext
    rw [← ordinal_in_group B d x, ← ordinal_in_group B d y]
    exact ho
  exact congrArg DeathOccurrence.index ((deathEnumeration B d).symm.injective hxy)

/-- The canonical death-preserving barcode embedding supplied by a componentwise injection.
It matches equal ordinals in birth/index order, with no essential-bijection requirement. -/
noncomputable def monoEmbedding (j : M ⟶ N) (hj : ∀ i, Function.Injective (j.app i).hom) :
    BarcodeOccurrence s (rankBarcode M) ↪ BarcodeOccurrence s (rankBarcode N) where
  toFun := mapOccurrence j hj
  inj' i i' h := by
    apply occurrence_eq_of_death_ordinal (rankBarcode M) i i'
    · exact (mapOccurrence_death j hj i).symm.trans
        ((congrArg (fun a => (occurrence (rankBarcode N) a).death) h).trans
          (mapOccurrence_death j hj i'))
    · exact (mapOccurrence_ordinal j hj i).symm.trans
        ((congrArg (deathOrdinal (rankBarcode N)) h).trans (mapOccurrence_ordinal j hj i'))

/-- The canonical embedding preserves each observed death exactly. -/
theorem monoEmbedding_death (j : M ⟶ N) (hj : ∀ i, Function.Injective (j.app i).hom)
    (i : BarcodeOccurrence s (rankBarcode M)) :
    (occurrence (rankBarcode N) (monoEmbedding j hj i)).death =
      (occurrence (rankBarcode M) i).death := mapOccurrence_death j hj i

/-- Source and target have the same ordinal in their birth/index ordered death group. -/
theorem monoEmbedding_ordinal (j : M ⟶ N) (hj : ∀ i, Function.Injective (j.app i).hom)
    (i : BarcodeOccurrence s (rankBarcode M)) :
    deathOrdinal (rankBarcode N) (monoEmbedding j hj i) = deathOrdinal (rankBarcode M) i :=
  mapOccurrence_ordinal j hj i

/-- The target of the canonical embedding is born no later than its source. -/
theorem monoEmbedding_birth_le (j : M ⟶ N) (hj : ∀ i, Function.Injective (j.app i).hom)
    (i : BarcodeOccurrence s (rankBarcode M)) :
    (occurrence (rankBarcode N) (monoEmbedding j hj i)).birth ≤
      (occurrence (rankBarcode M) i).birth := by
  let I := occurrence (rankBarcode M) i
  let x : DeathOccurrence (rankBarcode M) I.death := ⟨i, rfl⟩
  let y := groupEmbedding j hj I.death x
  change (occurrence (rankBarcode N) y.index).birth ≤ I.birth
  by_contra h
  have hlo := ordinal_lt_prefix (rankBarcode M) I.death x
  have hhi := prefix_le_ordinal (rankBarcode N) I.birth I.death y (lt_of_not_ge h)
  have hcounts := deathPrefixCount_le_of_injective j hj I.birth I.death
    I.birth_lt_death I.death_le_size
  have he := groupEmbedding_rank j hj I.death x
  change ((deathEnumeration (rankBarcode M) I.death).symm x).val <
    deathPrefixCount (rankBarcode M) I.birth I.death at hlo
  change ((deathEnumeration (rankBarcode N) I.death).symm y).val =
    ((deathEnumeration (rankBarcode M) I.death).symm x).val at he
  omega

/-- Death and ordinal uniquely characterize the canonical correspondence. -/
theorem monoEmbedding_eq_iff (j : M ⟶ N) (hj : ∀ i, Function.Injective (j.app i).hom)
    (i : BarcodeOccurrence s (rankBarcode M)) (a : BarcodeOccurrence s (rankBarcode N)) :
    monoEmbedding j hj i = a ↔
      (occurrence (rankBarcode N) a).death = (occurrence (rankBarcode M) i).death ∧
      deathOrdinal (rankBarcode N) a = deathOrdinal (rankBarcode M) i := by
  constructor
  · rintro rfl
    exact ⟨monoEmbedding_death j hj i, monoEmbedding_ordinal j hj i⟩
  · rintro ⟨hd, ho⟩
    exact occurrence_eq_of_death_ordinal (rankBarcode N) _ _
      ((monoEmbedding_death j hj i).trans hd.symm)
      ((monoEmbedding_ordinal j hj i).trans ho.symm)

/-- A target occurrence is selected precisely when its ordinal fits in the source death group. -/
theorem monoEmbedding_mem_range_iff (j : M ⟶ N)
    (hj : ∀ i, Function.Injective (j.app i).hom)
    (a : BarcodeOccurrence s (rankBarcode N)) :
    a ∈ Set.range (monoEmbedding j hj) ↔
      deathOrdinal (rankBarcode N) a <
        Fintype.card (DeathOccurrence (rankBarcode M) (occurrence (rankBarcode N) a).death) := by
  constructor
  · rintro ⟨i, rfl⟩
    rw [monoEmbedding_death, monoEmbedding_ordinal]
    exact ((deathEnumeration (rankBarcode M) _).symm ⟨i, rfl⟩).isLt
  · intro ha
    let q : Fin (Fintype.card (DeathOccurrence (rankBarcode M)
      (occurrence (rankBarcode N) a).death)) := ⟨deathOrdinal (rankBarcode N) a, ha⟩
    let x := deathEnumeration (rankBarcode M) (occurrence (rankBarcode N) a).death q
    refine ⟨x.index, (monoEmbedding_eq_iff j hj _ a).mpr ⟨x.death_eq.symm, ?_⟩⟩
    rw [ordinal_in_group (rankBarcode M) _ x]
    simp [x, q]

/-- Identity monomorphisms induce identity occurrence embeddings. -/
theorem monoEmbedding_id (M : PModule.{u,0,u} k (Fin s))
    [∀ i, FiniteDimensional k (M.obj i)] :
    monoEmbedding (𝟙 M) (fun _ => Function.injective_id) = Function.Embedding.refl _ := by
  apply Function.Embedding.ext
  intro i
  exact occurrence_eq_of_death_ordinal (rankBarcode M) _ i
    (monoEmbedding_death (𝟙 M) (fun _ => Function.injective_id) i)
    (monoEmbedding_ordinal (𝟙 M) (fun _ => Function.injective_id) i)

/-- Standard ordinal embeddings compose on monomorphisms. No law for arbitrary
persistence-module morphisms is asserted. -/
theorem monoEmbedding_comp {P : PModule.{u,0,u} k (Fin s)}
    [∀ i, FiniteDimensional k (P.obj i)] (j : M ⟶ N) (l : N ⟶ P)
    (hj : ∀ i, Function.Injective (j.app i).hom) (hl : ∀ i, Function.Injective (l.app i).hom) :
    monoEmbedding (j ≫ l) (fun i => (hl i).comp (hj i)) =
      (monoEmbedding j hj).trans (monoEmbedding l hl) := by
  apply Function.Embedding.ext
  intro i
  apply occurrence_eq_of_death_ordinal (rankBarcode P)
  · exact (monoEmbedding_death _ _ i).trans
      ((monoEmbedding_death l hl _).trans (monoEmbedding_death j hj i)).symm
  · exact (monoEmbedding_ordinal _ _ i).trans
      ((monoEmbedding_ordinal l hl _).trans (monoEmbedding_ordinal j hj i)).symm

end TDA.Persistence.FiniteBarcode
