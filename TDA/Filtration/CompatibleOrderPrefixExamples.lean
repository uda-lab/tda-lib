import TDA.Filtration.CompatibleOrderPrefix

set_option autoImplicit false

/-!
# Executable examples for compatible-order prefixes

These fixtures exercise empty and nonempty face sets, tied and nonconstant grades, a
noncanonical compatible order, absent ambient vertices, and rational thresholds. The
prefixes are checked as actual preabstract complexes; values are also evaluated on concrete
finite presentations.
-/

namespace TDA.Filtration.CompatibleOrderPrefixExamples

open TDA.Simplicial TDA.Simplicial.FiniteComplex
open TDA.Filtration TDA.Filtration.CompatibleOrder

private def empty0 : FiniteComplex 0 where
  faces := ∅
  nonempty := by decide
  downClosed := by decide

private def empty3 : FiniteComplex 3 where
  faces := ∅
  nonempty := by decide
  downClosed := by decide

private def emptyFilter {n : ℕ} (C : FiniteComplex n)
    (h : C.faces = ∅) (α : Type*) [LinearOrder α] :
    FilterFunction C.toPre α where
  value := fun s => by
    have hs : s.val ∈ C.faces := s.property
    rw [h] at hs
    simp at hs
  mono := by
    intro s t _
    have hs : s.val ∈ C.faces := s.property
    rw [h] at hs

private def singleton3 : FiniteComplex 3 where
  faces := {{0}}
  nonempty := by decide
  downClosed := by decide

private def edge3 : FiniteComplex 3 where
  faces := {{0}, {1}, {0, 1}}
  nonempty := by decide
  downClosed := by decide

private def constantFilter {n : ℕ} (C : FiniteComplex n) (v : ℤ) :
    FilterFunction C.toPre ℤ where
  value := fun _ => v
  mono := by intros; exact le_rfl

private def edgeVariableFilter : FilterFunction edge3.toPre ℤ where
  value := fun s => if s.val = ({1} : Finset (Fin 3)) then 0 else 5
  mono := by
    intro s t h
    by_cases hs : s.val = ({1} : Finset (Fin 3))
    · simp only [hs, ↓reduceIte]
      split_ifs <;> omega
    by_cases ht : t.val = ({1} : Finset (Fin 3))
    · have hsne : s.val.Nonempty := edge3.nonempty s.val s.property
      have hst : s.val = t.val :=
        Finset.eq_of_subset_of_card_le h (by simpa [ht] using hsne.card_pos)
      exact (hs (hst.trans ht)).elim
    · simp [hs, ht]

private def rationalFilter : FilterFunction edge3.toPre ℚ where
  value := fun s => if s.val = ({0} : Finset (Fin 3)) then 0
    else if s.val = ({1} : Finset (Fin 3)) then 2 else 5
  mono := by
    intro s t h
    have hsne : s.val.Nonempty := edge3.nonempty s.val s.property
    have hcase : s.val = ({0} : Finset (Fin 3)) ∨
      s.val = {1} ∨ s.val = {0, 1} := by
      have hm : s.val ∈ edge3.faces := s.property
      simpa [edge3] using hm
    have htcase : t.val = ({0} : Finset (Fin 3)) ∨
      t.val = {1} ∨ t.val = {0, 1} := by
      have hm : t.val ∈ edge3.faces := t.property
      simpa [edge3] using hm
    rcases hcase with hs | hs | hs <;> rcases htcase with ht | ht | ht <;>
      simp_all (decide := true)

private theorem edgeCard : Fintype.card (TotalFace edge3.toPre) = 3 := by decide

private theorem enumPreimageCard {α : Type*} [LinearOrder α]
    {f : FilterFunction edge3.toPre α} (e : CompatibleOrder f)
    (s : TotalFace edge3.toPre) :
    (Finset.univ.filter (fun i => e.enum i = s)).card = 1 := by
  have hfilter : Finset.univ.filter (fun i => e.enum i = s) = {e.enum.symm s} := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro hi
      have h := congrArg e.enum.symm hi
      simpa using h
    · intro hi
      subst i
      exact e.enum.apply_symm_apply s
  simp [hfilter]

private theorem variableCountBetween (r : ℤ) (hr0 : 0 ≤ r) (hr5 : r < 5) :
    (ofLex edge3 edgeVariableFilter).sublevelCount r = 1 := by
  let e := ofLex edge3 edgeVariableFilter
  change (Finset.univ.filter
    (fun i => edgeVariableFilter.value (e.enum i) ≤ r)).card = 1
  have hfilter : Finset.univ.filter
      (fun i => edgeVariableFilter.value (e.enum i) ≤ r) =
      Finset.univ.filter
        (fun i => e.enum i = ⟨{1}, by decide⟩) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hi
      by_cases hface : (e.enum i).val = {1}
      · exact Subtype.ext hface
      · have h5 : (5 : ℤ) ≤ r := by
          simpa [edgeVariableFilter, hface] using hi
        exact False.elim ((not_le_of_gt hr5) h5)
    · intro hi
      have hface := congrArg Subtype.val hi
      simp [edgeVariableFilter, hface, hr0]
  rw [hfilter]
  exact enumPreimageCard e ⟨{1}, by decide⟩

private theorem variableCountNeg :
    (ofLex edge3 edgeVariableFilter).sublevelCount (-1) = 0 := by
  let e := ofLex edge3 edgeVariableFilter
  change (Finset.univ.filter
    (fun i => edgeVariableFilter.value (e.enum i) ≤ (-1 : ℤ))).card = 0
  have hfilter : Finset.univ.filter
      (fun i => edgeVariableFilter.value (e.enum i) ≤ (-1 : ℤ)) = ∅ := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hi
      by_cases hface : (e.enum i).val = {1}
      · simp [edgeVariableFilter, hface] at hi
      · simp [edgeVariableFilter, hface] at hi
    · intro hi
      simp at hi
  simp [hfilter]

private theorem variableCountAtLeastFive (r : ℤ) (hr5 : 5 ≤ r) :
    (ofLex edge3 edgeVariableFilter).sublevelCount r = 3 := by
  let e := ofLex edge3 edgeVariableFilter
  change (Finset.univ.filter
    (fun i => edgeVariableFilter.value (e.enum i) ≤ r)).card = 3
  have hfilter : Finset.univ.filter
      (fun i => edgeVariableFilter.value (e.enum i) ≤ r) = Finset.univ := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hface : (e.enum i).val = {1}
    · simp only [edgeVariableFilter, hface]
      constructor
      · intro _
        trivial
      · intro _
        omega
    · simp [edgeVariableFilter, hface, hr5]
  rw [hfilter]
  simp [edgeCard]

private def edgeEnum3 {α : Type*} [LinearOrder α]
    (f : FilterFunction edge3.toPre α) (e : CompatibleOrder f) :
    Fin 3 ≃ TotalFace edge3.toPre where
  toFun := fun i => e.enum (Fin.cast edgeCard.symm i)
  invFun := fun s => Fin.cast edgeCard (e.enum.symm s)
  left_inv := by intro i; simp
  right_inv := by intro s; simp

private def canonicalTied : CompatibleOrder (constantFilter edge3 5) :=
  ofLex edge3 (constantFilter edge3 5)

private theorem ofLexEdgeEnum3_key_strict (f : FilterFunction edge3.toPre ℤ) :
    StrictMono (lexKey edge3 f ∘ edgeEnum3 f (ofLex edge3 f)) := by
  intro i j hij
  change lexKey edge3 f ((ofLex edge3 f).enum (Fin.cast edgeCard.symm i)) <
    lexKey edge3 f ((ofLex edge3 f).enum (Fin.cast edgeCard.symm j))
  apply ofLex_key_strictMono edge3 f
  simpa using hij

private theorem canonicalTiedEnumZero :
    (edgeEnum3 (constantFilter edge3 5) canonicalTied 0).val = {0} := by
  let e := edgeEnum3 (constantFilter edge3 5) canonicalTied
  have hkey01 :
      lexKey edge3 (constantFilter edge3 5) ⟨{0}, by decide⟩ <
        lexKey edge3 (constantFilter edge3 5) ⟨{1}, by decide⟩ := by decide
  have hkey0edge :
      lexKey edge3 (constantFilter edge3 5) ⟨{0}, by decide⟩ <
        lexKey edge3 (constantFilter edge3 5) ⟨{0, 1}, by decide⟩ := by decide
  have hstrict := ofLexEdgeEnum3_key_strict (constantFilter edge3 5)
  have hmem : (e 0).val ∈ edge3.faces := (e 0).property
  have hcases : (e 0).val = {0} ∨ (e 0).val = {1} ∨
      (e 0).val = {0, 1} := by simpa [edge3] using hmem
  rcases hcases with h0 | h1 | hedge
  · exact h0
  · exfalso
    let i : Fin 3 := e.symm ⟨{0}, by decide⟩
    have hne : i ≠ 0 := by
      intro hi
      have happly := e.apply_symm_apply (⟨{0}, by decide⟩ : TotalFace edge3.toPre)
      have henum0 : e 0 = ⟨{0}, by decide⟩ := by simpa [i, hi] using happly
      have hv := congrArg Subtype.val henum0
      have hneq : ({0} : Finset (Fin 3)) ≠ {1} := by decide
      exact hneq (hv.symm.trans h1)
    have hi : (0 : Fin 3) < i := by omega
    have hlt := hstrict hi
    have henum0 : e 0 = ⟨{1}, by decide⟩ := Subtype.ext h1
    have henumi := e.apply_symm_apply (⟨{0}, by decide⟩ : TotalFace edge3.toPre)
    change lexKey edge3 (constantFilter edge3 5) (e 0) <
      lexKey edge3 (constantFilter edge3 5) (e i) at hlt
    rw [henum0, henumi] at hlt
    exact (lt_asymm hkey01 hlt)
  · exfalso
    let i : Fin 3 := e.symm ⟨{0}, by decide⟩
    have hne : i ≠ 0 := by
      intro hi
      have happly := e.apply_symm_apply (⟨{0}, by decide⟩ : TotalFace edge3.toPre)
      have henum0 : e 0 = ⟨{0}, by decide⟩ := by simpa [i, hi] using happly
      have hv := congrArg Subtype.val henum0
      have hneq : ({0} : Finset (Fin 3)) ≠ {0, 1} := by decide
      exact hneq (hv.symm.trans hedge)
    have hi : (0 : Fin 3) < i := by omega
    have hlt := hstrict hi
    have henum0 : e 0 = ⟨{0, 1}, by decide⟩ := Subtype.ext hedge
    have henumi := e.apply_symm_apply (⟨{0}, by decide⟩ : TotalFace edge3.toPre)
    have hkeyorder :
        lexKey edge3 (constantFilter edge3 5) ⟨{0}, by decide⟩ <
          lexKey edge3 (constantFilter edge3 5) ⟨{0, 1}, by decide⟩ := hkey0edge
    change lexKey edge3 (constantFilter edge3 5) (e 0) <
      lexKey edge3 (constantFilter edge3 5) (e i) at hlt
    rw [henum0, henumi] at hlt
    exact (lt_asymm hkeyorder hlt)

private theorem canonicalTiedEnumOne :
    (edgeEnum3 (constantFilter edge3 5) canonicalTied 1).val = {1} := by
  let e := edgeEnum3 (constantFilter edge3 5) canonicalTied
  have hkey1edge :
      lexKey edge3 (constantFilter edge3 5) ⟨{1}, by decide⟩ <
        lexKey edge3 (constantFilter edge3 5) ⟨{0, 1}, by decide⟩ := by decide
  have hstrict := ofLexEdgeEnum3_key_strict (constantFilter edge3 5)
  have hmem : (e 1).val ∈ edge3.faces := (e 1).property
  have hcases : (e 1).val = {0} ∨ (e 1).val = {1} ∨
      (e 1).val = {0, 1} := by simpa [edge3] using hmem
  rcases hcases with h0 | h1 | hedge
  · exfalso
    have hzero : e 0 = ⟨{0}, by decide⟩ := Subtype.ext canonicalTiedEnumZero
    have hone : e 1 = ⟨{0}, by decide⟩ := Subtype.ext h0
    have hEq : e 0 = e 1 := hzero.trans hone.symm
    have hidx := e.injective hEq
    omega
  · exact h1
  · exfalso
    let i : Fin 3 := e.symm ⟨{1}, by decide⟩
    have hne0 : i ≠ 0 := by
      intro hi
      have happly := e.apply_symm_apply (⟨{1}, by decide⟩ : TotalFace edge3.toPre)
      have hone : e 0 = ⟨{1}, by decide⟩ := by simpa [i, hi] using happly
      have hv := congrArg Subtype.val hone
      have hzero : (e 0).val = {0} := canonicalTiedEnumZero
      have hneq : ({0} : Finset (Fin 3)) ≠ {1} := by decide
      exact hneq (hzero.symm.trans hv)
    have hne1 : i ≠ 1 := by
      intro hi
      have happly := e.apply_symm_apply (⟨{1}, by decide⟩ : TotalFace edge3.toPre)
      have hone : e 1 = ⟨{1}, by decide⟩ := by simpa [i, hi] using happly
      have hv := congrArg Subtype.val hone
      exact (by decide : ({1} : Finset (Fin 3)) ≠ {0, 1}) (hv.symm.trans hedge)
    have i2 : i = 2 := by
      apply Fin.ext
      omega
    have hlt := hstrict (by decide : (1 : Fin 3) < 2)
    have hone : e 1 = ⟨{0, 1}, by decide⟩ := Subtype.ext hedge
    have htwo : e 2 = ⟨{1}, by decide⟩ := by
      calc
        e 2 = e i := congrArg e i2.symm
        _ = ⟨{1}, by decide⟩ :=
          e.apply_symm_apply (⟨{1}, by decide⟩ : TotalFace edge3.toPre)
    change lexKey edge3 (constantFilter edge3 5) (e 1) <
      lexKey edge3 (constantFilter edge3 5) (e 2) at hlt
    rw [hone, htwo] at hlt
    exact (lt_asymm hkey1edge hlt)

private theorem canonicalTiedEnumTwo :
    (edgeEnum3 (constantFilter edge3 5) canonicalTied 2).val = {0, 1} := by
  let e := edgeEnum3 (constantFilter edge3 5) canonicalTied
  have hmem : (e 2).val ∈ edge3.faces := (e 2).property
  have hcases : (e 2).val = {0} ∨ (e 2).val = {1} ∨
      (e 2).val = {0, 1} := by simpa [edge3] using hmem
  rcases hcases with h0 | h1 | hedge
  · exfalso
    have hzero : e 0 = ⟨{0}, by decide⟩ := Subtype.ext canonicalTiedEnumZero
    have htwo : e 2 = ⟨{0}, by decide⟩ := Subtype.ext h0
    have hEq : e 0 = e 2 := hzero.trans htwo.symm
    have hidx := e.injective hEq
    omega
  · exfalso
    have hone : e 1 = ⟨{1}, by decide⟩ := Subtype.ext canonicalTiedEnumOne
    have htwo : e 2 = ⟨{1}, by decide⟩ := Subtype.ext h1
    have hEq : e 1 = e 2 := hone.trans htwo.symm
    have hidx := e.injective hEq
    omega
  · exact hedge

private theorem canonicalTiedIndexZero :
    (canonicalTied.enum.symm ⟨{0}, by decide⟩).val = 0 := by
  have hidx : canonicalTied.enum.symm ⟨{0}, by decide⟩ = Fin.cast edgeCard.symm 0 := by
    apply canonicalTied.enum.injective
    calc
      canonicalTied.enum (canonicalTied.enum.symm ⟨{0}, by decide⟩) =
          ⟨{0}, by decide⟩ := canonicalTied.enum.apply_symm_apply _
      _ = canonicalTied.enum (Fin.cast edgeCard.symm 0) := by
        apply Subtype.ext
        exact canonicalTiedEnumZero.symm
  simpa using congrArg Fin.val hidx

private theorem canonicalTiedIndexOne :
    (canonicalTied.enum.symm ⟨{1}, by decide⟩).val = 1 := by
  have hidx : canonicalTied.enum.symm ⟨{1}, by decide⟩ = Fin.cast edgeCard.symm 1 := by
    apply canonicalTied.enum.injective
    calc
      canonicalTied.enum (canonicalTied.enum.symm ⟨{1}, by decide⟩) =
          ⟨{1}, by decide⟩ := canonicalTied.enum.apply_symm_apply _
      _ = canonicalTied.enum (Fin.cast edgeCard.symm 1) := by
        apply Subtype.ext
        exact canonicalTiedEnumOne.symm
  simpa using congrArg Fin.val hidx

private theorem canonicalTiedIndexTwo :
    (canonicalTied.enum.symm ⟨{0, 1}, by decide⟩).val = 2 := by
  have hidx : canonicalTied.enum.symm ⟨{0, 1}, by decide⟩ = Fin.cast edgeCard.symm 2 := by
    apply canonicalTied.enum.injective
    calc
      canonicalTied.enum (canonicalTied.enum.symm ⟨{0, 1}, by decide⟩) =
          ⟨{0, 1}, by decide⟩ := canonicalTied.enum.apply_symm_apply _
      _ = canonicalTied.enum (Fin.cast edgeCard.symm 2) := by
        apply Subtype.ext
        exact canonicalTiedEnumTwo.symm
  simpa using congrArg Fin.val hidx

private def alternateEnum : Fin (Fintype.card (TotalFace edge3.toPre)) ≃
    TotalFace edge3.toPre where
  toFun := fun i =>
    ⟨if Fin.cast edgeCard i = 0 then ({1} : Finset (Fin 3))
      else if Fin.cast edgeCard i = 1 then {0} else {0, 1},
      by fin_cases i <;> decide⟩
  invFun := fun s => Fin.cast edgeCard.symm
    (if s.val = ({1} : Finset (Fin 3)) then 0
      else if s.val = {0} then 1 else 2)
  left_inv := by decide
  right_inv := by decide

private def alternateOrder : CompatibleOrder (constantFilter edge3 5) where
  enum := alternateEnum
  face_lt := by
    intro i j h
    exact (by decide : ∀ i j, (alternateEnum i).val ⊂
      (alternateEnum j).val → i < j) i j h
  monotone := by
    intro i j _
    exact le_rfl

private theorem empty0_all (k : ℕ) :
    (ofLex empty0 (emptyFilter empty0 rfl ℤ)).prefixComplex k = ⊥ := by
  have hc : Fintype.card (TotalFace empty0.toPre) = 0 := by decide
  have h := (ofLex empty0 (emptyFilter empty0 rfl ℤ)).prefixComplex_eq_self_of_card_le k
    (by omega)
  have he : empty0.toPre = ⊥ := by
    apply le_antisymm
    · intro s hs
      have hs' : s ∈ empty0.faces := hs
      simp [empty0] at hs'
    · exact bot_le
  exact h.trans he

private theorem empty3_all (k : ℕ) :
    (ofLex empty3 (emptyFilter empty3 rfl ℤ)).prefixComplex k = ⊥ := by
  have hc : Fintype.card (TotalFace empty3.toPre) = 0 := by decide
  have h := (ofLex empty3 (emptyFilter empty3 rfl ℤ)).prefixComplex_eq_self_of_card_le k
    (by omega)
  have he : empty3.toPre = ⊥ := by
    apply le_antisymm
    · intro s hs
      have hs' : s ∈ empty3.faces := hs
      simp [empty3] at hs'
    · exact bot_le
  exact h.trans he

private theorem emptyVoidReindex :
    reindex (ofLex empty3 (emptyFilter empty3 rfl Empty)).thresholdMap
      (ofLex empty3 (emptyFilter empty3 rfl Empty)).prefixFiltration =
      (emptyFilter empty3 rfl Empty).sublevelFiltration := by
  exact (ofLex empty3 (emptyFilter empty3 rfl Empty)).reindex_prefixFiltration

private theorem empty0Count (r : ℤ) :
    (ofLex empty0 (emptyFilter empty0 rfl ℤ)).sublevelCount r = 0 := by
  have hc : Fintype.card (TotalFace empty0.toPre) = 0 := by decide
  have hle :
      (ofLex empty0 (emptyFilter empty0 rfl ℤ)).sublevelCount r ≤ 0 := by
    simpa [hc] using
      (ofLex empty0 (emptyFilter empty0 rfl ℤ)).sublevelCount_le_card r
  omega

private theorem empty3Count (r : ℤ) :
    (ofLex empty3 (emptyFilter empty3 rfl ℤ)).sublevelCount r = 0 := by
  have hc : Fintype.card (TotalFace empty3.toPre) = 0 := by decide
  have hle :
      (ofLex empty3 (emptyFilter empty3 rfl ℤ)).sublevelCount r ≤ 0 := by
    simpa [hc] using
      (ofLex empty3 (emptyFilter empty3 rfl ℤ)).sublevelCount_le_card r
  omega

private theorem singletonStages :
    (ofLex singleton3 (constantFilter singleton3 3)).prefixComplex 0 = ⊥ ∧
    (ofLex singleton3 (constantFilter singleton3 3)).prefixComplex 1 = singleton3.toPre ∧
    (ofLex singleton3 (constantFilter singleton3 3)).prefixComplex 4 = singleton3.toPre := by
  constructor
  · exact prefixComplex_zero _
  constructor
  · exact prefixComplex_eq_self_of_card_le _ 1 (by decide)
  · exact prefixComplex_eq_self_of_card_le _ 4 (by decide)

private theorem singletonCounts :
    (ofLex singleton3 (constantFilter singleton3 3)).sublevelCount 2 = 0 ∧
    (ofLex singleton3 (constantFilter singleton3 3)).sublevelCount 3 = 1 := by
  constructor
  · simp [sublevelCount, constantFilter]
  · have hc : Fintype.card (TotalFace singleton3.toPre) = 1 := by decide
    simp [sublevelCount, constantFilter, hc]

private theorem singletonAbsentVertex :
    ∀ k : ℕ, ({2} : Finset (Fin 3)) ∉
      (ofLex singleton3 (constantFilter singleton3 3)).prefixComplex k := by
  intro k h
  exact (by decide : ({2} : Finset (Fin 3)) ∉ singleton3.toPre)
    (((ofLex singleton3 (constantFilter singleton3 3)).mem_prefixComplex k {2}).mp h).1

private theorem tiedStages :
    (ofLex edge3 (constantFilter edge3 5)).prefixComplex 0 = ⊥ ∧
    (ofLex edge3 (constantFilter edge3 5)).prefixComplex 3 = edge3.toPre ∧
    (ofLex edge3 (constantFilter edge3 5)).prefixComplex 7 = edge3.toPre := by
  exact ⟨prefixComplex_zero _, prefixComplex_eq_self_of_card_le _ 3 (by decide),
    prefixComplex_eq_self_of_card_le _ 7 (by decide)⟩

private theorem tiedCounts :
    canonicalTied.sublevelCount 4 = 0 ∧ canonicalTied.sublevelCount 5 = 3 := by
  constructor
  · simp [sublevelCount, canonicalTied, constantFilter]
  · simp [sublevelCount, canonicalTied, constantFilter, edgeCard]

private def twoVertices3 : FiniteComplex 3 where
  faces := {{0}, {1}}
  nonempty := by decide
  downClosed := by decide

private theorem canonicalPrefixOne :
    canonicalTied.prefixComplex 1 = singleton3.toPre := by
  ext s
  constructor
  · intro hs
    obtain ⟨hsK, hidx⟩ := (canonicalTied.mem_prefixComplex 1 s).mp hs
    have hcases : s = {0} ∨ s = {1} ∨ s = {0, 1} := by
      have hm : s ∈ edge3.faces := hsK
      simpa [edge3] using hm
    rcases hcases with h0 | h1 | h01
    · subst s
      change ({0} : Finset (Fin 3)) ∈ singleton3.faces
      simp [singleton3]
    · subst s
      have hi : (canonicalTied.enum.symm ⟨({1} : Finset (Fin 3)), hsK⟩).val = 1 := by
        simpa using canonicalTiedIndexOne
      rw [hi] at hidx
      omega
    · subst s
      have hi :
          (canonicalTied.enum.symm ⟨({0, 1} : Finset (Fin 3)), hsK⟩).val = 2 := by
        simpa using canonicalTiedIndexTwo
      rw [hi] at hidx
      omega
  · intro hs
    have hs0 : s = {0} := by
      have hm : s ∈ singleton3.faces := hs
      simp [singleton3] at hm
      exact hm
    subst s
    apply (canonicalTied.mem_prefixComplex 1 {0}).mpr
    refine ⟨by decide, ?_⟩
    simp [canonicalTiedIndexZero]

private theorem canonicalPrefixTwo :
    canonicalTied.prefixComplex 2 = twoVertices3.toPre := by
  ext s
  constructor
  · intro hs
    obtain ⟨hsK, hidx⟩ := (canonicalTied.mem_prefixComplex 2 s).mp hs
    have hcases : s = {0} ∨ s = {1} ∨ s = {0, 1} := by
      have hm : s ∈ edge3.faces := hsK
      simpa [edge3] using hm
    rcases hcases with h0 | h1 | h01
    · subst s
      change ({0} : Finset (Fin 3)) ∈ twoVertices3.faces
      simp [twoVertices3]
    · subst s
      have hi : (canonicalTied.enum.symm ⟨({1} : Finset (Fin 3)), hsK⟩).val = 1 := by
        simpa using canonicalTiedIndexOne
      rw [hi] at hidx
      change ({1} : Finset (Fin 3)) ∈ twoVertices3.faces
      simp [twoVertices3]
    · subst s
      have hi :
          (canonicalTied.enum.symm ⟨({0, 1} : Finset (Fin 3)), hsK⟩).val = 2 := by
        simpa using canonicalTiedIndexTwo
      rw [hi] at hidx
      omega
  · intro hs
    change s ∈ twoVertices3.faces at hs
    simp [twoVertices3] at hs
    have hcases : s = {0} ∨ s = {1} := hs
    rcases hcases with h0 | h1
    · subst s
      apply (canonicalTied.mem_prefixComplex 2 {0}).mpr
      refine ⟨by decide, ?_⟩
      simp [canonicalTiedIndexZero]
    · subst s
      apply (canonicalTied.mem_prefixComplex 2 {1}).mpr
      refine ⟨by decide, ?_⟩
      simp [canonicalTiedIndexOne]

private theorem tiedCanonicalStages :
    canonicalTied.prefixComplex 0 = ⊥ ∧
    canonicalTied.prefixComplex 1 = singleton3.toPre ∧
    canonicalTied.prefixComplex 2 = twoVertices3.toPre ∧
    canonicalTied.prefixComplex 3 = edge3.toPre := by
  exact ⟨prefixComplex_zero _, canonicalPrefixOne, canonicalPrefixTwo,
    prefixComplex_eq_self_of_card_le _ 3 (by decide)⟩

private theorem canonicalTiedIntermediateNotSublevel :
    ¬ ∃ r : ℤ,
      canonicalTied.prefixComplex 1 = (constantFilter edge3 5).sublevel r := by
  rintro ⟨r, hr⟩
  have hone : ({0} : Finset (Fin 3)) ∈ canonicalTied.prefixComplex 1 := by
    rw [canonicalPrefixOne]
    change ({0} : Finset (Fin 3)) ∈ singleton3.faces
    simp [singleton3]
  have hzero : ({1} : Finset (Fin 3)) ∉ canonicalTied.prefixComplex 1 := by
    rw [canonicalPrefixOne]
    change ¬ ({1} : Finset (Fin 3)) ∈ singleton3.faces
    simp [singleton3]
  have hr5 : (5 : ℤ) ≤ r := by
    have hm : ({0} : Finset (Fin 3)) ∈
        (constantFilter edge3 5).sublevel r := hr ▸ hone
    exact ((constantFilter edge3 5).mem_sublevel_iff r {0}).mp hm |>.2
  have hm : ({1} : Finset (Fin 3)) ∈ (constantFilter edge3 5).sublevel r := by
    exact ((constantFilter edge3 5).mem_sublevel_iff r {1}).mpr
      ⟨by decide, by simpa [constantFilter] using hr5⟩
  exact hzero (hr.symm ▸ hm)

private theorem absentVertex :
    ∀ k : ℕ, ({2} : Finset (Fin 3)) ∉
      (ofLex edge3 (constantFilter edge3 5)).prefixComplex k := by
  intro k h
  exact (by decide : ({2} : Finset (Fin 3)) ∉ edge3.toPre)
    (((ofLex edge3 (constantFilter edge3 5)).mem_prefixComplex k {2}).mp h).1

private theorem nonconstantRecovery :
    ∀ r ∈ ({-1, 0, 4, 5, 6} : Finset ℤ),
      edgeVariableFilter.sublevel r =
        (ofLex edge3 edgeVariableFilter).prefixComplex
          ((ofLex edge3 edgeVariableFilter).sublevelCount r) := by
  intro r _
  exact (ofLex edge3 edgeVariableFilter).sublevel_eq_prefixComplex r

private theorem nonconstantCounts :
    (ofLex edge3 edgeVariableFilter).sublevelCount (-1) = 0 ∧
    (ofLex edge3 edgeVariableFilter).sublevelCount 0 = 1 ∧
    (ofLex edge3 edgeVariableFilter).sublevelCount 4 = 1 ∧
    (ofLex edge3 edgeVariableFilter).sublevelCount 5 = 3 ∧
    (ofLex edge3 edgeVariableFilter).sublevelCount 6 = 3 := by
  exact ⟨variableCountNeg, variableCountBetween 0 (by omega) (by omega),
    variableCountBetween 4 (by omega) (by omega),
    variableCountAtLeastFive 5 (by omega), variableCountAtLeastFive 6 (by omega)⟩

private theorem nonconstantConcreteRecovery :
    edgeVariableFilter.sublevel (-1) =
        (ofLex edge3 edgeVariableFilter).prefixComplex 0 ∧
    edgeVariableFilter.sublevel 0 =
        (ofLex edge3 edgeVariableFilter).prefixComplex 1 ∧
    edgeVariableFilter.sublevel 4 =
        (ofLex edge3 edgeVariableFilter).prefixComplex 1 ∧
    edgeVariableFilter.sublevel 5 =
        (ofLex edge3 edgeVariableFilter).prefixComplex 3 ∧
    edgeVariableFilter.sublevel 6 =
        (ofLex edge3 edgeVariableFilter).prefixComplex 3 := by
  rcases nonconstantCounts with ⟨hneg, hzero, hfour, hfive, hsix⟩
  exact ⟨by simpa [hneg] using (ofLex edge3 edgeVariableFilter).sublevel_eq_prefixComplex (-1),
    by simpa [hzero] using (ofLex edge3 edgeVariableFilter).sublevel_eq_prefixComplex 0,
    by simpa [hfour] using (ofLex edge3 edgeVariableFilter).sublevel_eq_prefixComplex 4,
    by simpa [hfive] using (ofLex edge3 edgeVariableFilter).sublevel_eq_prefixComplex 5,
    by simpa [hsix] using (ofLex edge3 edgeVariableFilter).sublevel_eq_prefixComplex 6⟩

private theorem alternateFirst :
    ({1} : Finset (Fin 3)) ∈ alternateOrder.prefixComplex 1 ∧
    ({0} : Finset (Fin 3)) ∉ alternateOrder.prefixComplex 1 := by
  constructor
  · apply (alternateOrder.mem_prefixComplex 1 {1}).mpr
    refine ⟨by decide, ?_⟩
    decide
  · intro h
    obtain ⟨_, hi⟩ := (alternateOrder.mem_prefixComplex 1 {0}).mp h
    have hn : ¬ (alternateOrder.enum.symm ⟨({0} : Finset (Fin 3)), by decide⟩).val < 1 := by
      decide
    exact hn hi

private theorem alternateSecond :
    ({0} : Finset (Fin 3)) ∈ alternateOrder.prefixComplex 2 ∧
    ({1} : Finset (Fin 3)) ∈ alternateOrder.prefixComplex 2 ∧
    ({0, 1} : Finset (Fin 3)) ∉ alternateOrder.prefixComplex 2 := by
  constructor
  · apply (alternateOrder.mem_prefixComplex 2 {0}).mpr
    exact ⟨by decide, by decide⟩
  constructor
  · apply (alternateOrder.mem_prefixComplex 2 {1}).mpr
    exact ⟨by decide, by decide⟩
  · intro h
    obtain ⟨_, hi⟩ := (alternateOrder.mem_prefixComplex 2 {0, 1}).mp h
    have hn : ¬ (alternateOrder.enum.symm
      ⟨({0, 1} : Finset (Fin 3)), by decide⟩).val < 2 := by decide
    exact hn hi

private theorem tiedIntermediateNotSublevel :
    ¬ ∃ r : ℤ, alternateOrder.prefixComplex 1 = (constantFilter edge3 5).sublevel r := by
  rintro ⟨r, hr⟩
  have hone := alternateFirst.1
  have hzero := alternateFirst.2
  have hr5 : (5 : ℤ) ≤ r := by
    have hm : ({1} : Finset (Fin 3)) ∈ (constantFilter edge3 5).sublevel r :=
      hr ▸ hone
    exact ((constantFilter edge3 5).mem_sublevel_iff r {1}).mp hm |>.2
  have hm : ({0} : Finset (Fin 3)) ∈ (constantFilter edge3 5).sublevel r := by
    exact ((constantFilter edge3 5).mem_sublevel_iff r {0}).mpr
      ⟨by decide, by simpa [constantFilter]⟩
  exact hzero (hr.symm ▸ hm)

private theorem alternateRecovery (r : ℤ) :
    (constantFilter edge3 5).sublevel r =
      alternateOrder.prefixComplex (alternateOrder.sublevelCount r) := by
  exact alternateOrder.sublevel_eq_prefixComplex r

private theorem rationalCount :
    (ofLex edge3 rationalFilter).sublevelCount (3 / 2 : ℚ) = 1 := by
  let e := ofLex edge3 rationalFilter
  change (Finset.univ.filter
    (fun i => rationalFilter.value (e.enum i) ≤ (3 / 2 : ℚ))).card = 1
  have hfilter : Finset.univ.filter
      (fun i => rationalFilter.value (e.enum i) ≤ (3 / 2 : ℚ)) =
      Finset.univ.filter (fun i => e.enum i = ⟨{0}, by decide⟩) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hi
      by_cases hzero : (e.enum i).val = {0}
      · exact Subtype.ext hzero
      · by_cases hone : (e.enum i).val = {1}
        · have h2 : (2 : ℚ) ≤ (3 / 2 : ℚ) := by
            simpa [rationalFilter, hzero, hone] using hi
          norm_num at h2
        · have h5 : (5 : ℚ) ≤ (3 / 2 : ℚ) := by
            simpa [rationalFilter, hzero, hone] using hi
          norm_num at h5
    · intro hi
      have hzero := congrArg Subtype.val hi
      norm_num [rationalFilter, hzero]
  rw [hfilter]
  exact enumPreimageCard e ⟨{0}, by decide⟩

private theorem rationalRecovery :
    rationalFilter.sublevel (3 / 2 : ℚ) =
      (ofLex edge3 rationalFilter).prefixComplex 1 := by
  simpa [rationalCount] using
    (ofLex edge3 rationalFilter).sublevel_eq_prefixComplex (3 / 2 : ℚ)

#eval (ofLex empty0 (emptyFilter empty0 rfl ℤ)).sublevelCount 0
#eval (ofLex empty3 (emptyFilter empty3 rfl ℤ)).thresholdMap 5
#eval (ofLex singleton3 (constantFilter singleton3 3)).sublevelCount 2
#eval (ofLex singleton3 (constantFilter singleton3 3)).thresholdMap 3
#eval (ofLex edge3 (constantFilter edge3 5)).sublevelCount 4
#eval (ofLex edge3 (constantFilter edge3 5)).thresholdMap 5
#eval (ofLex edge3 edgeVariableFilter).sublevelCount (-1)
#eval (ofLex edge3 edgeVariableFilter).sublevelCount 0
#eval (ofLex edge3 edgeVariableFilter).sublevelCount 4
#eval (ofLex edge3 edgeVariableFilter).sublevelCount 5
#eval (ofLex edge3 edgeVariableFilter).sublevelCount 6
#eval alternateOrder.sublevelCount 4
#eval alternateOrder.thresholdMap 5
#eval (ofLex edge3 rationalFilter).sublevelCount (3/2 : ℚ)
#eval List.ofFn (fun i => ((ofLex edge3 (constantFilter edge3 5)).enum i).val)
#eval List.ofFn (fun i => ((ofLex edge3 edgeVariableFilter).enum i).val)
#eval List.ofFn (fun i => (alternateOrder.enum i).val)

#print axioms empty0
#print axioms empty3
#print axioms emptyFilter
#print axioms singleton3
#print axioms edge3
#print axioms constantFilter
#print axioms edgeVariableFilter
#print axioms rationalFilter
#print axioms edgeCard
#print axioms enumPreimageCard
#print axioms variableCountBetween
#print axioms variableCountNeg
#print axioms variableCountAtLeastFive
#print axioms edgeEnum3
#print axioms canonicalTied
#print axioms ofLexEdgeEnum3_key_strict
#print axioms canonicalTiedEnumZero
#print axioms canonicalTiedEnumOne
#print axioms canonicalTiedEnumTwo
#print axioms canonicalTiedIndexZero
#print axioms canonicalTiedIndexOne
#print axioms canonicalTiedIndexTwo
#print axioms alternateEnum
#print axioms alternateOrder
#print axioms empty0_all
#print axioms empty3_all
#print axioms emptyVoidReindex
#print axioms empty0Count
#print axioms empty3Count
#print axioms singletonStages
#print axioms singletonCounts
#print axioms singletonAbsentVertex
#print axioms tiedStages
#print axioms tiedCounts
#print axioms twoVertices3
#print axioms canonicalPrefixOne
#print axioms canonicalPrefixTwo
#print axioms tiedCanonicalStages
#print axioms canonicalTiedIntermediateNotSublevel
#print axioms absentVertex
#print axioms nonconstantRecovery
#print axioms nonconstantCounts
#print axioms nonconstantConcreteRecovery
#print axioms alternateFirst
#print axioms alternateSecond
#print axioms tiedIntermediateNotSublevel
#print axioms alternateRecovery
#print axioms rationalCount
#print axioms rationalRecovery

end TDA.Filtration.CompatibleOrderPrefixExamples
