import TDA.Persistence.FiniteEpiCounts
import TDA.Persistence.FiniteMonoMatching

/-!
# Canonical barcode embeddings from finite-chain epimorphisms

At a fixed birth, order occurrences by descending death, then by their original list
index. A componentwise surjection supplies survival-count bounds. The embedding goes
from target occurrences back to source occurrences and pairs equal ordinals.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence.FiniteBarcode

open CategoryTheory
open scoped BigOperators

variable {s : ℕ}

/-- An occurrence with one specified birth, retaining its original label. -/
@[ext] structure BirthOccurrence (B : Multiset (FiniteInterval s)) (b : ℕ) where
  index : BarcodeOccurrence s B
  birth_eq : (occurrence B index).birth = b

private def birthEquiv (B : Multiset (FiniteInterval s)) (b : ℕ) :
    BirthOccurrence B b ≃ {i : BarcodeOccurrence s B // (occurrence B i).birth = b} where
  toFun i := ⟨i.index, i.birth_eq⟩
  invFun i := ⟨i.val, i.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance birthOccurrenceFintype (B : Multiset (FiniteInterval s)) (b : ℕ) :
    Fintype (BirthOccurrence B b) := Fintype.ofEquiv _ (birthEquiv B b).symm

noncomputable instance birthOccurrenceLinearOrder (B : Multiset (FiniteInterval s)) (b : ℕ) :
    LinearOrder (BirthOccurrence B b) :=
  LinearOrder.lift' (fun i => toLex (OrderDual.toDual (occurrence B i.index).death, i.index)) (by
    intro i j h
    exact BirthOccurrence.ext (congrArg (fun x => (ofLex x).2) h))

/-- Enumeration by descending death, then ascending original occurrence index. -/
noncomputable def birthEnumeration (B : Multiset (FiniteInterval s)) (b : ℕ) :
    Fin (Fintype.card (BirthOccurrence B b)) ≃o BirthOccurrence B b :=
  Fintype.orderIsoFinOfCardEq _ rfl

/-- The zero-based ordinal among occurrences with the same birth. -/
noncomputable def birthOrdinal (B : Multiset (FiniteInterval s)) (i : BarcodeOccurrence s B) : ℕ :=
  ((birthEnumeration B (occurrence B i).birth).symm ⟨i, rfl⟩).val

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

private def suffixEquiv (B : Multiset (FiniteInterval s)) (b c : ℕ) :
    {i : BirthOccurrence B b // c < (occurrence B i.index).death} ≃
      {i : BarcodeOccurrence s B // (occurrence B i).birth = b ∧ c < (occurrence B i).death} where
  toFun i := ⟨i.val.index, i.val.birth_eq, i.property⟩
  invFun i := ⟨⟨i.val, i.property.1⟩, i.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem suffix_card (B : Multiset (FiniteInterval s)) (b c : ℕ) :
    Fintype.card {i : BirthOccurrence B b // c < (occurrence B i.index).death} =
      birthSuffixCount B b c := by
  classical
  rw [Fintype.card_congr (suffixEquiv B b c),
    occurrence_count B (fun I => I.birth = b ∧ c < I.death)]
  rfl

private theorem birth_card (B : Multiset (FiniteInterval s)) (b : ℕ) :
    Fintype.card (BirthOccurrence B b) = birthSuffixCount B b b := by
  classical
  rw [Fintype.card_congr (birthEquiv B b), occurrence_count B (fun I => I.birth = b)]
  unfold birthSuffixCount
  apply Multiset.countP_congr rfl
  intro I _
  apply propext
  have := I.birth_lt_death
  omega

private theorem death_antitone (B : Multiset (FiniteInterval s)) (b : ℕ)
    {i j : BirthOccurrence B b} (h : i ≤ j) :
    (occurrence B j.index).death ≤ (occurrence B i.index).death :=
  Prod.Lex.monotone_fst _ _ h

private theorem lt_of_death_gt (B : Multiset (FiniteInterval s)) (b : ℕ)
    {i j : BirthOccurrence B b}
    (h : (occurrence B j.index).death < (occurrence B i.index).death) : i < j :=
  Prod.Lex.toLex_lt_toLex.mpr (Or.inl h)

private theorem ordinal_lt_suffix (B : Multiset (FiniteInterval s)) (b c : ℕ)
    (x : BirthOccurrence B b) (hc : c < (occurrence B x.index).death) :
    ((birthEnumeration B b).symm x).val < birthSuffixCount B b c := by
  classical
  let r := (birthEnumeration B b).symm x
  let f : Fin (r.val + 1) → {i : BirthOccurrence B b // c < (occurrence B i.index).death} :=
    fun a => by
      let q : Fin (Fintype.card (BirthOccurrence B b)) := ⟨a.val, by have := r.isLt; omega⟩
      have hqr : q ≤ r := by change a.val ≤ r.val; have := a.isLt; omega
      refine ⟨birthEnumeration B b q, ?_⟩
      have h := death_antitone B b ((birthEnumeration B b).monotone hqr)
      have hr : birthEnumeration B b r = x := (birthEnumeration B b).apply_symm_apply x
      rw [hr] at h
      exact hc.trans_le h
  have hf : Function.Injective f := by
    intro a d h
    apply Fin.ext
    have he := congrArg Subtype.val h
    change birthEnumeration B b ⟨a.val, _⟩ = birthEnumeration B b ⟨d.val, _⟩ at he
    exact congrArg (fun q : Fin (Fintype.card (BirthOccurrence B b)) => q.val)
      ((birthEnumeration B b).injective he)
  have h := Fintype.card_le_of_injective f hf
  rw [Fintype.card_fin, suffix_card] at h
  omega

private theorem suffix_le_ordinal (B : Multiset (FiniteInterval s)) (b c : ℕ)
    (x : BirthOccurrence B b) (hc : (occurrence B x.index).death ≤ c) :
    birthSuffixCount B b c ≤ ((birthEnumeration B b).symm x).val := by
  classical
  let r := (birthEnumeration B b).symm x
  let f : {i : BirthOccurrence B b // c < (occurrence B i.index).death} → Fin r.val :=
    fun i => ⟨((birthEnumeration B b).symm i.val).val,
      (birthEnumeration B b).symm.strictMono
        (lt_of_death_gt B b (hc.trans_lt i.property))⟩
  have hf : Function.Injective f := by
    intro a d h
    apply Subtype.ext
    apply (birthEnumeration B b).symm.injective
    exact Fin.ext (congrArg (fun a : Fin r.val => a.val) h)
  have h := Fintype.card_le_of_injective f hf
  rwa [Fintype.card_fin, suffix_card] at h

/-- A surviving occurrence has ordinal below the same-birth survival count. -/
theorem birthOrdinal_lt_birthSuffixCount (B : Multiset (FiniteInterval s))
    (i : BarcodeOccurrence s B) (c : ℕ) (hc : c < (occurrence B i).death) :
    birthOrdinal B i < birthSuffixCount B (occurrence B i).birth c :=
  ordinal_lt_suffix B _ c ⟨i, rfl⟩ hc

/-- An occurrence dead at the cutoff follows every surviving occurrence of that birth. -/
theorem birthSuffixCount_le_birthOrdinal (B : Multiset (FiniteInterval s))
    (i : BarcodeOccurrence s B) (c : ℕ) (hc : (occurrence B i).death ≤ c) :
    birthSuffixCount B (occurrence B i).birth c ≤ birthOrdinal B i :=
  suffix_le_ordinal B _ c ⟨i, rfl⟩ hc

/-- A same-birth survival count never exceeds that birth group's cardinality. -/
theorem birthSuffixCount_le_card (B : Multiset (FiniteInterval s)) (b c : ℕ) :
    birthSuffixCount B b c ≤ Fintype.card (BirthOccurrence B b) := by
  rw [← suffix_card]
  exact Fintype.card_le_of_injective Subtype.val Subtype.val_injective

variable {k : Type u} [Field k]
variable {M N : PModule.{u,0,u} k (Fin s)}
variable [∀ i, FiniteDimensional k (M.obj i)] [∀ i, FiniteDimensional k (N.obj i)]

private theorem birth_card_le (p : M ⟶ N) (hp : ∀ i, Function.Surjective (p.app i).hom)
    (b : ℕ) : Fintype.card (BirthOccurrence (rankBarcode N) b) ≤
      Fintype.card (BirthOccurrence (rankBarcode M) b) := by
  classical
  by_cases h : Nonempty (BirthOccurrence (rankBarcode N) b)
  · obtain ⟨x⟩ := h
    have hbs : b < s := by
      have := (occurrence (rankBarcode N) x.index).birth_lt_death
      have := (occurrence (rankBarcode N) x.index).death_le_size
      rw [x.birth_eq] at *
      omega
    rw [birth_card, birth_card]
    exact birthSuffixCount_le_of_surjective p hp b b (le_refl b) hbs
  · have := not_nonempty_iff.mp h
    simp

private noncomputable def groupEmbedding (p : M ⟶ N)
    (hp : ∀ i, Function.Surjective (p.app i).hom) (b : ℕ) :
    BirthOccurrence (rankBarcode N) b ↪ BirthOccurrence (rankBarcode M) b :=
  ((birthEnumeration (rankBarcode N) b).symm.toEmbedding.trans
    (Fin.castLEEmb (birth_card_le p hp b))).trans
      (birthEnumeration (rankBarcode M) b).toEmbedding

private theorem groupEmbedding_rank (p : M ⟶ N)
    (hp : ∀ i, Function.Surjective (p.app i).hom) (b : ℕ)
    (x : BirthOccurrence (rankBarcode N) b) :
    ((birthEnumeration (rankBarcode M) b).symm (groupEmbedding p hp b x)).val =
      ((birthEnumeration (rankBarcode N) b).symm x).val := by
  simp [groupEmbedding]

private theorem ordinal_in_group (B : Multiset (FiniteInterval s)) (b : ℕ)
    (x : BirthOccurrence B b) :
    birthOrdinal B x.index = ((birthEnumeration B b).symm x).val := by
  cases x with
  | mk i hi => cases hi; rfl

private noncomputable def mapOccurrence (p : M ⟶ N)
    (hp : ∀ i, Function.Surjective (p.app i).hom) (i : BarcodeOccurrence s (rankBarcode N)) :
    BarcodeOccurrence s (rankBarcode M) :=
  (groupEmbedding p hp (occurrence (rankBarcode N) i).birth ⟨i, rfl⟩).index

private theorem mapOccurrence_birth (p : M ⟶ N)
    (hp : ∀ i, Function.Surjective (p.app i).hom) (i : BarcodeOccurrence s (rankBarcode N)) :
    (occurrence (rankBarcode M) (mapOccurrence p hp i)).birth =
      (occurrence (rankBarcode N) i).birth :=
  (groupEmbedding p hp _ ⟨i, rfl⟩).birth_eq

private theorem mapOccurrence_in_group (p : M ⟶ N)
    (hp : ∀ i, Function.Surjective (p.app i).hom) (b : ℕ)
    (x : BirthOccurrence (rankBarcode N) b) :
    mapOccurrence p hp x.index = (groupEmbedding p hp b x).index := by
  cases x with
  | mk i hi => cases hi; rfl

private theorem mapOccurrence_ordinal (p : M ⟶ N)
    (hp : ∀ i, Function.Surjective (p.app i).hom) (i : BarcodeOccurrence s (rankBarcode N)) :
    birthOrdinal (rankBarcode M) (mapOccurrence p hp i) = birthOrdinal (rankBarcode N) i := by
  let b := (occurrence (rankBarcode N) i).birth
  let x : BirthOccurrence (rankBarcode N) b := ⟨i, rfl⟩
  rw [mapOccurrence_in_group p hp b x, ordinal_in_group,
    groupEmbedding_rank, ← ordinal_in_group]

private theorem occurrence_eq_of_birth_ordinal (B : Multiset (FiniteInterval s))
    (i j : BarcodeOccurrence s B) (hb : (occurrence B i).birth = (occurrence B j).birth)
    (ho : birthOrdinal B i = birthOrdinal B j) : i = j := by
  let b := (occurrence B i).birth
  let x : BirthOccurrence B b := ⟨i, rfl⟩
  let y : BirthOccurrence B b := ⟨j, hb.symm⟩
  have hxy : (birthEnumeration B b).symm x = (birthEnumeration B b).symm y := by
    apply Fin.ext
    rw [← ordinal_in_group B b x, ← ordinal_in_group B b y]
    exact ho
  exact congrArg BirthOccurrence.index ((birthEnumeration B b).symm.injective hxy)

/-- The canonical birth-preserving embedding from target occurrences into source occurrences.
It uses death/index order and assumes only an actual componentwise surjection. -/
noncomputable def epiEmbedding (p : M ⟶ N) (hp : ∀ i, Function.Surjective (p.app i).hom) :
    BarcodeOccurrence s (rankBarcode N) ↪ BarcodeOccurrence s (rankBarcode M) where
  toFun := mapOccurrence p hp
  inj' i i' h := by
    apply occurrence_eq_of_birth_ordinal (rankBarcode N) i i'
    · exact (mapOccurrence_birth p hp i).symm.trans
        ((congrArg (fun a => (occurrence (rankBarcode M) a).birth) h).trans
          (mapOccurrence_birth p hp i'))
    · exact (mapOccurrence_ordinal p hp i).symm.trans
        ((congrArg (birthOrdinal (rankBarcode M)) h).trans (mapOccurrence_ordinal p hp i'))

/-- The embedding preserves each birth exactly. -/
theorem epiEmbedding_birth (p : M ⟶ N) (hp : ∀ i, Function.Surjective (p.app i).hom)
    (i : BarcodeOccurrence s (rankBarcode N)) :
    (occurrence (rankBarcode M) (epiEmbedding p hp i)).birth =
      (occurrence (rankBarcode N) i).birth := mapOccurrence_birth p hp i

/-- Both occurrences have the same ordinal in their death-descending birth group. -/
theorem epiEmbedding_ordinal (p : M ⟶ N) (hp : ∀ i, Function.Surjective (p.app i).hom)
    (i : BarcodeOccurrence s (rankBarcode N)) :
    birthOrdinal (rankBarcode M) (epiEmbedding p hp i) = birthOrdinal (rankBarcode N) i :=
  mapOccurrence_ordinal p hp i

/-- The corresponding source interval dies no earlier than the target interval. -/
theorem epiEmbedding_death_le (p : M ⟶ N) (hp : ∀ i, Function.Surjective (p.app i).hom)
    (i : BarcodeOccurrence s (rankBarcode N)) :
    (occurrence (rankBarcode N) i).death ≤
      (occurrence (rankBarcode M) (epiEmbedding p hp i)).death := by
  let I := occurrence (rankBarcode N) i
  let x : BirthOccurrence (rankBarcode N) I.birth := ⟨i, rfl⟩
  let y := groupEmbedding p hp I.birth x
  change I.death ≤ (occurrence (rankBarcode M) y.index).death
  by_contra h
  have hlo := ordinal_lt_suffix (rankBarcode N) I.birth (I.death - 1) x (by
    change I.death - 1 < I.death
    have := I.birth_lt_death
    omega)
  have hhi := suffix_le_ordinal (rankBarcode M) I.birth (I.death - 1) y (by omega)
  have hcounts := birthSuffixCount_le_of_surjective p hp I.birth (I.death - 1)
    (by have := I.birth_lt_death; omega) (by have := I.death_le_size; have := I.birth_lt_death; omega)
  have he := groupEmbedding_rank p hp I.birth x
  change ((birthEnumeration (rankBarcode N) I.birth).symm x).val <
    birthSuffixCount (rankBarcode N) I.birth (I.death - 1) at hlo
  change ((birthEnumeration (rankBarcode M) I.birth).symm y).val =
    ((birthEnumeration (rankBarcode N) I.birth).symm x).val at he
  omega

/-- Terminal survival is preserved, using the finite-chain upper bound on death. -/
theorem epiEmbedding_terminal (p : M ⟶ N) (hp : ∀ i, Function.Surjective (p.app i).hom)
    (i : BarcodeOccurrence s (rankBarcode N)) (hi : (occurrence (rankBarcode N) i).death = s) :
    (occurrence (rankBarcode M) (epiEmbedding p hp i)).death = s := by
  have h := epiEmbedding_death_le p hp i
  have := (occurrence (rankBarcode M) (epiEmbedding p hp i)).death_le_size
  omega

/-- Birth and ordinal uniquely characterize the canonical correspondence. -/
theorem epiEmbedding_eq_iff (p : M ⟶ N) (hp : ∀ i, Function.Surjective (p.app i).hom)
    (i : BarcodeOccurrence s (rankBarcode N)) (a : BarcodeOccurrence s (rankBarcode M)) :
    epiEmbedding p hp i = a ↔
      (occurrence (rankBarcode M) a).birth = (occurrence (rankBarcode N) i).birth ∧
      birthOrdinal (rankBarcode M) a = birthOrdinal (rankBarcode N) i := by
  constructor
  · rintro rfl
    exact ⟨epiEmbedding_birth p hp i, epiEmbedding_ordinal p hp i⟩
  · rintro ⟨hb, ho⟩
    exact occurrence_eq_of_birth_ordinal (rankBarcode M) _ _
      ((epiEmbedding_birth p hp i).trans hb.symm)
      ((epiEmbedding_ordinal p hp i).trans ho.symm)

/-- A source occurrence is selected exactly when its ordinal fits in the target birth group. -/
theorem epiEmbedding_mem_range_iff (p : M ⟶ N)
    (hp : ∀ i, Function.Surjective (p.app i).hom)
    (a : BarcodeOccurrence s (rankBarcode M)) :
    a ∈ Set.range (epiEmbedding p hp) ↔
      birthOrdinal (rankBarcode M) a <
        Fintype.card (BirthOccurrence (rankBarcode N) (occurrence (rankBarcode M) a).birth) := by
  constructor
  · rintro ⟨i, rfl⟩
    rw [epiEmbedding_birth, epiEmbedding_ordinal]
    exact ((birthEnumeration (rankBarcode N) _).symm ⟨i, rfl⟩).isLt
  · intro ha
    let q : Fin (Fintype.card (BirthOccurrence (rankBarcode N)
      (occurrence (rankBarcode M) a).birth)) := ⟨birthOrdinal (rankBarcode M) a, ha⟩
    let x := birthEnumeration (rankBarcode N) (occurrence (rankBarcode M) a).birth q
    refine ⟨x.index, (epiEmbedding_eq_iff p hp _ a).mpr ⟨x.birth_eq.symm, ?_⟩⟩
    rw [ordinal_in_group (rankBarcode N) _ x]
    simp [x, q]

/-- Identity epimorphisms induce identity occurrence embeddings. -/
theorem epiEmbedding_id (M : PModule.{u,0,u} k (Fin s))
    [∀ i, FiniteDimensional k (M.obj i)] :
    epiEmbedding (𝟙 M) (fun _ => Function.surjective_id) = Function.Embedding.refl _ := by
  apply Function.Embedding.ext
  intro i
  exact occurrence_eq_of_birth_ordinal (rankBarcode M) _ i
    (epiEmbedding_birth (𝟙 M) (fun _ => Function.surjective_id) i)
    (epiEmbedding_ordinal (𝟙 M) (fun _ => Function.surjective_id) i)

/-- The canonical embeddings compose contravariantly on epimorphisms.
No composition law for arbitrary persistence-module morphisms is asserted. -/
theorem epiEmbedding_comp {P : PModule.{u,0,u} k (Fin s)}
    [∀ i, FiniteDimensional k (P.obj i)] (p : M ⟶ N) (q : N ⟶ P)
    (hp : ∀ i, Function.Surjective (p.app i).hom) (hq : ∀ i, Function.Surjective (q.app i).hom) :
    epiEmbedding (p ≫ q) (fun i => (hq i).comp (hp i)) =
      (epiEmbedding q hq).trans (epiEmbedding p hp) := by
  apply Function.Embedding.ext
  intro i
  apply occurrence_eq_of_birth_ordinal (rankBarcode M)
  · exact (epiEmbedding_birth _ _ i).trans
      ((epiEmbedding_birth p hp _).trans (epiEmbedding_birth q hq i)).symm
  · exact (epiEmbedding_ordinal _ _ i).trans
      ((epiEmbedding_ordinal p hp _).trans (epiEmbedding_ordinal q hq i)).symm

end TDA.Persistence.FiniteBarcode
