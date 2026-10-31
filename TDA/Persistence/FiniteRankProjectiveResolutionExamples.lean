import TDA.Persistence.FiniteRankProjectiveResolution

/-!
# Examples of finite rank-projective resolutions

These examples exercise the zero-length boundary, a nonzero principal-upset
hook, and a two-term contractible resolution whose repeated hook terms cancel.
-/

set_option autoImplicit false

namespace TDA.Persistence.FiniteRankProjectiveResolutionExamples

open CategoryTheory
open scoped ZeroObject

noncomputable abbrev zeroModule : PModule.{0,0,0} ℚ (Fin 2) := 0

noncomputable abbrev nonzeroHook : PModule.{0,0,0} ℚ (Fin 2) :=
  HookInfinity.module (R := ℚ) (0 : Fin 2)

private theorem zeroIdRankExact (Q : PModule.{0,0,0} ℚ (Fin 2))
    [∀ p, FiniteDimensional ℚ (Q.obj p)] :
    IsRankExact (0 : zeroModule ⟶ Q) (𝟙 Q) := by
  have hshort : IsPointwiseShortExact (0 : zeroModule ⟶ Q) (𝟙 Q) := by
    constructor
    · intro p x y _
      exact (ModuleCat.subsingleton_of_isZero (Functor.zero_obj p)).elim x y
    · intro p x
      exact ⟨x, rfl⟩
    · intro p
      simp
  exact hshort.rankExact_of_section (𝟙 Q) (by simp)

private theorem idZeroRankExact (Q : PModule.{0,0,0} ℚ (Fin 2))
    [∀ p, FiniteDimensional ℚ (Q.obj p)] :
    IsRankExact (𝟙 Q) (0 : Q ⟶ zeroModule) := by
  have hshort : IsPointwiseShortExact (𝟙 Q) (0 : Q ⟶ zeroModule) := by
    constructor
    · intro _ x y h
      exact h
    · intro p y
      have hzero : Subsingleton (zeroModule.obj p) :=
        ModuleCat.subsingleton_of_isZero (Functor.zero_obj p)
      exact ⟨0, hzero.elim _ _⟩
    · intro p
      simp
  exact hshort.rankExact_of_section (0 : zeroModule ⟶ Q) (by simp)

private theorem nonzeroHook_birth_rank :
    rankOfStructureMap nonzeroHook (show (0 : Fin 2) ≤ 0 from le_rfl) = 1 := by
  unfold rankOfStructureMap
  rw [structureMapLinear_self, LinearMap.range_id, finrank_top]
  exact ((HookInfinity.fiberEquivOfLe (R := ℚ) (i := (0 : Fin 2))
    (a := 0) le_rfl).finrank_eq).trans (by simp)

private noncomputable def oneTermKernel :
    Fin 2 → PModule.{0,0,0} ℚ (Fin 2) := fun i =>
      if i.val = 0 then nonzeroHook else zeroModule

private noncomputable def oneTermTerm :
    Fin 1 → PModule.{0,0,0} ℚ (Fin 2) := fun _ => nonzeroHook

private noncomputable def contractibleKernel :
    Fin 3 → PModule.{0,0,0} ℚ (Fin 2) := fun i =>
      if i.val = 1 then nonzeroHook else zeroModule

private noncomputable def contractibleTerm :
    Fin 2 → PModule.{0,0,0} ℚ (Fin 2) := fun _ => nonzeroHook

private noncomputable def oneTermInclusion :
    ∀ i : Fin 1, oneTermKernel i.succ ⟶ oneTermTerm i := by
  intro i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  change zeroModule ⟶ nonzeroHook
  exact 0

private noncomputable def oneTermQuotient :
    ∀ i : Fin 1, oneTermTerm i ⟶ oneTermKernel i.castSucc := by
  intro i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  change nonzeroHook ⟶ nonzeroHook
  exact 𝟙 nonzeroHook

private theorem oneTermRows :
    ∀ i : Fin 1, IsRankExact (oneTermInclusion i) (oneTermQuotient i) := by
  intro i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  change IsRankExact (0 : zeroModule ⟶ nonzeroHook) (𝟙 nonzeroHook)
  exact zeroIdRankExact nonzeroHook

private theorem oneTermProjective :
    ∀ i : Fin 1, IsRankProjective (oneTermTerm i) := by
  intro i
  exact HookInfinity.isRankProjective (i := (0 : Fin 2))

private noncomputable def contractibleInclusion :
    ∀ i : Fin 2, contractibleKernel i.succ ⟶ contractibleTerm i := by
  intro i
  refine Fin.cases ?_ ?_ i
  · change nonzeroHook ⟶ nonzeroHook
    exact 𝟙 nonzeroHook
  · intro j
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    change zeroModule ⟶ nonzeroHook
    exact 0

private noncomputable def contractibleQuotient :
    ∀ i : Fin 2, contractibleTerm i ⟶ contractibleKernel i.castSucc := by
  intro i
  refine Fin.cases ?_ ?_ i
  · change nonzeroHook ⟶ zeroModule
    exact 0
  · intro j
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    change nonzeroHook ⟶ nonzeroHook
    exact 𝟙 nonzeroHook

private theorem contractibleRows :
    ∀ i : Fin 2, IsRankExact (contractibleInclusion i) (contractibleQuotient i) := by
  intro i
  refine Fin.cases ?_ ?_ i
  · change IsRankExact (𝟙 nonzeroHook) (0 : nonzeroHook ⟶ zeroModule)
    exact idZeroRankExact nonzeroHook
  · intro j
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    change IsRankExact (0 : zeroModule ⟶ nonzeroHook) (𝟙 nonzeroHook)
    exact zeroIdRankExact nonzeroHook

private theorem contractibleProjective :
    ∀ i : Fin 2, IsRankProjective (contractibleTerm i) := by
  intro i
  exact HookInfinity.isRankProjective (i := (0 : Fin 2))

/-- The zero module has a resolution with no projective terms. -/
noncomputable def zeroLengthResolution :
    FiniteRankProjectiveResolution (M := zeroModule) where
  toFiniteRankExactResolution := {
    length := 0
    kernel := fun _ => zeroModule
    term := fun i => Fin.elim0 i
    inclusion := fun i => Fin.elim0 i
    quotient := fun i => Fin.elim0 i
    row_rank_exact := fun i => Fin.elim0 i
    initial_iso := Iso.refl zeroModule
    terminal_iso := Iso.refl zeroModule
  }
  term_rank_projective := fun i => Fin.elim0 i

/-- At zero length, both the resolved module rank and its empty alternating sum are zero. -/
theorem zeroLength_rank_zero {a b : Fin 2} (hab : a ≤ b) :
    (rankOfStructureMap zeroModule hab : ℤ) = 0 := by
  exact_mod_cast rankOfStructureMap_zero hab

/-- The zero-length resolution satisfies the empty alternating-sum formula. -/
theorem zeroLength_euler {a b : Fin 2} (hab : a ≤ b) :
    (rankOfStructureMap zeroModule hab : ℤ) =
      ∑ i : Fin zeroLengthResolution.length, (-1 : ℤ) ^ i.val *
        (rankOfStructureMap (zeroLengthResolution.term i) hab : ℤ) :=
  zeroLengthResolution.rank_eq_alternating_sum hab

/-- A one-term resolution by a nonzero projective principal-upset hook. -/
noncomputable def oneTermHookResolution :
    FiniteRankProjectiveResolution nonzeroHook where
  toFiniteRankExactResolution := {
    length := 1
    kernel := oneTermKernel
    term := oneTermTerm
    inclusion := oneTermInclusion
    quotient := oneTermQuotient
    row_rank_exact := oneTermRows
    initial_iso := by simpa [oneTermKernel] using (Iso.refl nonzeroHook)
    terminal_iso := by simpa [oneTermKernel] using (Iso.refl zeroModule)
  }
  term_rank_projective := oneTermProjective

/-- The one-term hook is projective and its birth structure map has rank one. -/
theorem oneTermHook_is_nonzero_projective :
    IsRankProjective nonzeroHook ∧
      0 < rankOfStructureMap nonzeroHook (show (0 : Fin 2) ≤ 0 from le_rfl) := by
  constructor
  · exact HookInfinity.isRankProjective (i := (0 : Fin 2))
  · rw [nonzeroHook_birth_rank]
    norm_num

/-- The one-term example realizes the Euler formula at its birth grade. -/
theorem oneTermHook_rank_euler :
    (rankOfStructureMap nonzeroHook (show (0 : Fin 2) ≤ 0 from le_rfl) : ℤ) =
      ∑ i : Fin oneTermHookResolution.length, (-1 : ℤ) ^ i.val *
        (rankOfStructureMap (oneTermHookResolution.term i)
          (show (0 : Fin 2) ≤ 0 from le_rfl) : ℤ) :=
  oneTermHookResolution.rank_eq_alternating_sum le_rfl

/-- The two-term resolution of zero uses the same nonzero projective hook twice. -/
noncomputable def contractibleZeroResolution :
    FiniteRankProjectiveResolution (M := zeroModule) where
  toFiniteRankExactResolution := {
    length := 2
    kernel := contractibleKernel
    term := contractibleTerm
    inclusion := contractibleInclusion
    quotient := contractibleQuotient
    row_rank_exact := contractibleRows
    initial_iso := by simpa [contractibleKernel] using (Iso.refl zeroModule)
    terminal_iso := by simpa [contractibleKernel] using (Iso.refl zeroModule)
  }
  term_rank_projective := contractibleProjective

/-- The indexed terms are equal as modules, but remain distinct summands in the finite sum. -/
theorem contractibleZero_repeated_terms :
    contractibleZeroResolution.term (0 : Fin 2) =
      contractibleZeroResolution.term (1 : Fin 2) := by
  change contractibleTerm (0 : Fin 2) = contractibleTerm (1 : Fin 2)
  rfl

/-- The map between the repeated hook terms is the identity, so the two-term complex contracts.
-/
theorem contractibleZero_differential_is_identity :
    contractibleZeroResolution.quotient (1 : Fin 2) ≫
        contractibleZeroResolution.inclusion (0 : Fin 2) = 𝟙 nonzeroHook := rfl

/-- The repeated nonzero projective terms cancel in the alternating sum. -/
theorem contractibleZero_rank_cancellation :
    ∑ i : Fin contractibleZeroResolution.length, (-1 : ℤ) ^ i.val *
      (rankOfStructureMap (contractibleZeroResolution.term i)
        (show (0 : Fin 2) ≤ 0 from le_rfl) : ℤ) = 0 := by
  have h := contractibleZeroResolution.rank_eq_alternating_sum
    (show (0 : Fin 2) ≤ 0 from le_rfl)
  simpa [rankOfStructureMap_zero] using h.symm

section CoordinateIdentityAndPadding

open CategoryTheory.Limits
open scoped TDA.Persistence

/-- The rational principal upset at zero in one real coordinate. -/
noncomputable abbrev oneCoordinateHook : PModule.{0,0,0} ℚ (Fin 1 → ℝ) :=
  HookInfinity.module (R := ℚ) (0 : Fin 1 → ℝ)

private theorem oneCoordinateHook_pointwiseFiniteDimensional :
    ∀ p, FiniteDimensional ℚ (oneCoordinateHook.obj p) := by
  intro p
  exact HookInfinity.finiteDimensional (i := (0 : Fin 1 → ℝ)) p

private theorem oneCoordinateHook_rankProjective : IsRankProjective oneCoordinateHook :=
  HookInfinity.isRankProjective (i := (0 : Fin 1 → ℝ))

private theorem oneCoordinateHook_map_nonzero_of_birth_le {a b : Fin 1 → ℝ}
    (hab : a ≤ b) (hia : (0 : Fin 1 → ℝ) ≤ a) :
    structureMapLinear oneCoordinateHook hab ≠ 0 := by
  let ea := HookInfinity.fiberEquivOfLe (R := ℚ) (i := (0 : Fin 1 → ℝ)) hia
  let eb := HookInfinity.fiberEquivOfLe (R := ℚ) (i := (0 : Fin 1 → ℝ)) (hia.trans hab)
  let x := ea.symm 1
  have hx : ea x = 1 := by simp [x]
  intro hzero
  have hmap := HookInfinity.fiberEquivOfLe_structureMap
    (R := ℚ) (i := (0 : Fin 1 → ℝ)) hia hab x
  have hvanish : eb (structureMapLinear oneCoordinateHook hab x) = 0 := by
    rw [hzero]
    exact eb.map_zero
  rw [hmap, hx] at hvanish
  exact (one_ne_zero : (1 : ℚ) ≠ 0) hvanish

private noncomputable abbrev realCoordinateZero : PModule.{0,0,0} ℚ (Fin 1 → ℝ) := 0

private theorem zeroIdRankExactReal (Q : PModule.{0,0,0} ℚ (Fin 1 → ℝ))
    [∀ p, FiniteDimensional ℚ (Q.obj p)] :
    IsRankExact (0 : realCoordinateZero ⟶ Q) (𝟙 Q) := by
  have hshort : IsPointwiseShortExact (0 : realCoordinateZero ⟶ Q) (𝟙 Q) := by
    constructor
    · intro p x y _
      exact (ModuleCat.subsingleton_of_isZero (Functor.zero_obj p)).elim x y
    · intro p x
      exact ⟨x, rfl⟩
    · intro p
      simp
  exact hshort.rankExact_of_section (𝟙 Q) (by simp)

private theorem idZeroRankExactReal (Q : PModule.{0,0,0} ℚ (Fin 1 → ℝ))
    [∀ p, FiniteDimensional ℚ (Q.obj p)] :
    IsRankExact (𝟙 Q) (0 : Q ⟶ realCoordinateZero) := by
  have hshort : IsPointwiseShortExact (𝟙 Q) (0 : Q ⟶ realCoordinateZero) := by
    constructor
    · intro _ x y h
      exact h
    · intro p y
      have hzero : Subsingleton (realCoordinateZero.obj p) :=
        ModuleCat.subsingleton_of_isZero (Functor.zero_obj p)
      exact ⟨0, hzero.elim _ _⟩
    · intro p
      simp
  exact hshort.rankExact_of_section (0 : realCoordinateZero ⟶ Q) (by simp)

/-- The length-one identity resolution of the one-coordinate principal upset. -/
noncomputable def oneCoordinateHookIdentity :
    FiniteRankProjectiveResolution oneCoordinateHook :=
  FiniteRankProjectiveResolution.identity oneCoordinateHook
    oneCoordinateHook_rankProjective oneCoordinateHook_pointwiseFiniteDimensional

/-- Two zero terms pad the identity resolution without changing its terms. -/
noncomputable def oneCoordinateHookPadded :
    FiniteRankProjectiveResolution oneCoordinateHook :=
  oneCoordinateHookIdentity.appendZeros 2

/-- The principal-upset module has a nonzero structure map between distinct grades. -/
theorem oneCoordinateHook_transition_nonzero :
    structureMapLinear oneCoordinateHook
        (show (0 : Fin 1 → ℝ) ≤ (fun _ : Fin 1 => (1 : ℝ)) by
          intro i
          norm_num) ≠ 0 := by
  let a : Fin 1 → ℝ := 0
  let b : Fin 1 → ℝ := fun _ => 1
  have hab : a ≤ b := by
    intro i
    norm_num [a, b]
  let e₀ := HookInfinity.fiberEquivOfLe (R := ℚ) (i := a) (a := a) le_rfl
  let e₁ := HookInfinity.fiberEquivOfLe (R := ℚ) (i := a) (a := b) hab
  let x := e₀.symm 1
  have hx : e₀ x = 1 := by simp [x]
  intro hzero
  have hmap := HookInfinity.fiberEquivOfLe_structureMap
    (R := ℚ) (i := a) (a := a) (b := b) le_rfl hab x
  have hvanish : e₁ (structureMapLinear oneCoordinateHook hab x) = 0 := by
    rw [hzero]
    exact e₁.map_zero
  rw [hmap, hx] at hvanish
  exact (one_ne_zero : (1 : ℚ) ≠ 0) hvanish

/-- The selected identity has length one and records the principal upset in degree zero. -/
theorem oneCoordinateHookIdentity_selected_data :
    oneCoordinateHookIdentity.length = 1 ∧
      oneCoordinateHookIdentity.term (0 : Fin 1) = oneCoordinateHook := by
  simp [oneCoordinateHookIdentity, FiniteRankProjectiveResolution.identity]

/-- Padding by two preserves the identity's degree-zero term and all later zero terms. -/
theorem oneCoordinateHookPadded_termAt (j : ℕ) :
    oneCoordinateHookPadded.termAt j = if j = 0 then oneCoordinateHook else 0 := by
  rw [oneCoordinateHookPadded, FiniteRankProjectiveResolution.termAt_appendZeros]
  simpa [oneCoordinateHookIdentity] using
    (FiniteRankProjectiveResolution.identity_termAt oneCoordinateHook
      oneCoordinateHook_rankProjective oneCoordinateHook_pointwiseFiniteDimensional j)

/-- The padded degree-zero term still has its nonzero map between distinct grades. -/
theorem oneCoordinateHookPadded_transition_nonzero :
    structureMapLinear (oneCoordinateHookPadded.termAt 0)
        (show (0 : Fin 1 → ℝ) ≤ (fun _ : Fin 1 => (1 : ℝ)) by
          intro i
          norm_num) ≠ 0 := by
  rw [oneCoordinateHookPadded_termAt 0]
  simpa using oneCoordinateHook_transition_nonzero

/-- The padded identity has three stored terms, although only degree zero is nonzero. -/
theorem oneCoordinateHookPadded_length : oneCoordinateHookPadded.length = 3 := by
  rw [oneCoordinateHookPadded, FiniteRankProjectiveResolution.appendZeros_length]
  rfl

/-- A genuine length-zero resolution of zero in one real coordinate. -/
noncomputable def coordinateZeroLengthResolution :
    FiniteRankProjectiveResolution
      (0 : PModule.{0,0,0} ℚ (Fin 1 → ℝ)) where
  toFiniteRankExactResolution := {
    length := 0
    kernel := fun _ => 0
    term := fun i => Fin.elim0 i
    inclusion := fun i => Fin.elim0 i
    quotient := fun i => Fin.elim0 i
    row_rank_exact := fun i => Fin.elim0 i
    initial_iso := Iso.refl 0
    terminal_iso := Iso.refl 0
  }
  term_rank_projective := fun i => Fin.elim0 i

/-- Positive padding of the zero-length resolution records exactly the added zero terms. -/
theorem coordinateZeroLengthResolution_padded_length (count : ℕ) :
    (coordinateZeroLengthResolution.appendZeros count).length = count := by
  rw [FiniteRankProjectiveResolution.appendZeros_length]
  simp [coordinateZeroLengthResolution]

/-- Every zero-padded term of a padded zero-length resolution is zero. -/
theorem coordinateZeroLengthResolution_padded_termAt (count j : ℕ) :
    (coordinateZeroLengthResolution.appendZeros count).termAt j = 0 := by
  rw [FiniteRankProjectiveResolution.termAt_appendZeros]
  simp [FiniteRankProjectiveResolution.termAt, coordinateZeroLengthResolution]

/-- The rational principal upset on the zero-dimensional real grid. -/
noncomputable abbrev zeroCoordinateHook : PModule.{0,0,0} ℚ (Fin 0 → ℝ) :=
  HookInfinity.module (R := ℚ) (0 : Fin 0 → ℝ)

private theorem zeroCoordinateHook_pointwiseFiniteDimensional :
    ∀ p, FiniteDimensional ℚ (zeroCoordinateHook.obj p) := by
  intro p
  exact HookInfinity.finiteDimensional (i := (0 : Fin 0 → ℝ)) p

private theorem zeroCoordinateHook_rankProjective : IsRankProjective zeroCoordinateHook :=
  HookInfinity.isRankProjective (i := (0 : Fin 0 → ℝ))

/-- The identity constructor also applies to principal upsets on the zero-dimensional grid. -/
noncomputable def zeroCoordinateHookIdentity :
    FiniteRankProjectiveResolution zeroCoordinateHook :=
  FiniteRankProjectiveResolution.identity zeroCoordinateHook
    zeroCoordinateHook_rankProjective zeroCoordinateHook_pointwiseFiniteDimensional

/-- The zero-dimensional identity resolution obeys the public padded-term law. -/
theorem zeroCoordinateHookIdentity_termAt (j : ℕ) :
    zeroCoordinateHookIdentity.termAt j = if j = 0 then zeroCoordinateHook else 0 := by
  exact FiniteRankProjectiveResolution.identity_termAt zeroCoordinateHook
    zeroCoordinateHook_rankProjective zeroCoordinateHook_pointwiseFiniteDimensional j

/-- In zero coordinate dimensions, a positive shift still exposes the selected lookup iso. -/
theorem zeroCoordinateHookIdentity_shift_termAtIso :
    Nonempty ((zeroCoordinateHookIdentity.shift 1).termAt 0 ≅
      (CoordinateShift.shift 1).obj zeroCoordinateHook) := by
  exact ⟨FiniteRankProjectiveResolution.termAt_shiftIso zeroCoordinateHookIdentity 1 0⟩

/-- The degree-zero tail boundary holds for the moved operation in dimension zero. -/
theorem zeroCoordinateHookIdentity_tail_boundary :
    (zeroCoordinateHookIdentity.tail (by
      simp [zeroCoordinateHookIdentity, FiniteRankProjectiveResolution.identity])).length = 0 ∧
      (zeroCoordinateHookIdentity.tail (by
        simp [zeroCoordinateHookIdentity, FiniteRankProjectiveResolution.identity])).termAt 0 = 0 := by
  have hlen : zeroCoordinateHookIdentity.length = 1 := by
    simp [zeroCoordinateHookIdentity, FiniteRankProjectiveResolution.identity]
  let hpos : 0 < zeroCoordinateHookIdentity.length := by rw [hlen]; omega
  constructor
  · change (zeroCoordinateHookIdentity.tail hpos).length = 0
    rw [FiniteRankProjectiveResolution.length_tail, hlen]
  · change (zeroCoordinateHookIdentity.tail hpos).termAt 0 = 0
    rw [FiniteRankProjectiveResolution.termAt_tail zeroCoordinateHookIdentity hpos 0]
    simp [zeroCoordinateHookIdentity, FiniteRankProjectiveResolution.identity]

private noncomputable def twoRowKernel :
    Fin 3 → PModule.{0,0,0} ℚ (Fin 1 → ℝ) := fun i =>
      if i.val = 1 then oneCoordinateHook else realCoordinateZero

private noncomputable def twoRowTerm :
    Fin 2 → PModule.{0,0,0} ℚ (Fin 1 → ℝ) := fun _ => oneCoordinateHook

private noncomputable def twoRowInclusion :
    ∀ i : Fin 2, twoRowKernel i.succ ⟶ twoRowTerm i := by
  intro i
  refine Fin.cases ?_ ?_ i
  · change oneCoordinateHook ⟶ oneCoordinateHook
    exact 𝟙 oneCoordinateHook
  · intro j
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    change realCoordinateZero ⟶ oneCoordinateHook
    exact 0

private noncomputable def twoRowQuotient :
    ∀ i : Fin 2, twoRowTerm i ⟶ twoRowKernel i.castSucc := by
  intro i
  refine Fin.cases ?_ ?_ i
  · change oneCoordinateHook ⟶ realCoordinateZero
    exact 0
  · intro j
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    change oneCoordinateHook ⟶ oneCoordinateHook
    exact 𝟙 oneCoordinateHook

private theorem twoRowRows :
    ∀ i : Fin 2, IsRankExact (twoRowInclusion i) (twoRowQuotient i) := by
  intro i
  refine Fin.cases ?_ ?_ i
  · change IsRankExact (𝟙 oneCoordinateHook) (0 : oneCoordinateHook ⟶ realCoordinateZero)
    exact idZeroRankExactReal oneCoordinateHook
  · intro j
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    change IsRankExact (0 : realCoordinateZero ⟶ oneCoordinateHook) (𝟙 oneCoordinateHook)
    exact zeroIdRankExactReal oneCoordinateHook

private theorem twoRowProjective : ∀ i : Fin 2, IsRankProjective (twoRowTerm i) := by
  intro i
  exact oneCoordinateHook_rankProjective

/-- A two-row nonminimal resolution of zero whose selected tail is the nonzero hook. -/
noncomputable def twoRowZeroResolution :
    FiniteRankProjectiveResolution (M := realCoordinateZero) where
  toFiniteRankExactResolution := {
    length := 2
    kernel := twoRowKernel
    term := twoRowTerm
    inclusion := twoRowInclusion
    quotient := twoRowQuotient
    row_rank_exact := twoRowRows
    initial_iso := by simpa [twoRowKernel] using (Iso.refl realCoordinateZero)
    terminal_iso := by simpa [twoRowKernel] using (Iso.refl realCoordinateZero)
  }
  term_rank_projective := twoRowProjective

/-- The two selected rows are exactly `(id,0)` and `(0,id)`. -/
theorem twoRowZeroResolution_selected_rows :
    twoRowZeroResolution.inclusion (0 : Fin 2) = 𝟙 oneCoordinateHook ∧
      twoRowZeroResolution.quotient (0 : Fin 2) = 0 ∧
      twoRowZeroResolution.inclusion (1 : Fin 2) = 0 ∧
      twoRowZeroResolution.quotient (1 : Fin 2) = 𝟙 oneCoordinateHook := by
  constructor
  · change twoRowInclusion (0 : Fin 2) = 𝟙 oneCoordinateHook
    ext p
    rfl
  constructor
  · change twoRowQuotient (0 : Fin 2) = 0
    ext p
    rfl
  constructor
  · change twoRowInclusion (1 : Fin 2) = 0
    change twoRowInclusion (Fin.succ (0 : Fin 1)) = 0
    rfl
  · change twoRowQuotient (1 : Fin 2) = 𝟙 oneCoordinateHook
    change twoRowQuotient (Fin.succ (0 : Fin 1)) = 𝟙 oneCoordinateHook
    rfl

/-- The selected middle kernel is the actual principal-upset module. -/
theorem twoRowZeroResolution_middle_kernel :
    twoRowZeroResolution.kernel (⟨1, by norm_num [twoRowZeroResolution]⟩ : Fin 3) =
      oneCoordinateHook := by
  simp [twoRowZeroResolution, twoRowKernel]

/-- The tail selects the actual middle kernel, has length one and records the hook term. -/
theorem twoRowZeroResolution_tail_data :
    (twoRowZeroResolution.tail (by simp [twoRowZeroResolution])).length = 1 ∧
      (twoRowZeroResolution.tail (by simp [twoRowZeroResolution])).termAt 0 =
        oneCoordinateHook ∧
      (twoRowZeroResolution.tail (by simp [twoRowZeroResolution])).termAt 1 = 0 := by
  have hlen : twoRowZeroResolution.length = 2 := rfl
  let hpos : 0 < twoRowZeroResolution.length := by rw [hlen]; omega
  constructor
  · change (twoRowZeroResolution.tail hpos).length = 1
    rw [FiniteRankProjectiveResolution.length_tail, hlen]
  constructor
  · change (twoRowZeroResolution.tail hpos).termAt 0 = oneCoordinateHook
    rw [FiniteRankProjectiveResolution.termAt_tail twoRowZeroResolution hpos 0]
    simp [twoRowZeroResolution, twoRowTerm]
  · change (twoRowZeroResolution.tail hpos).termAt 1 = 0
    rw [FiniteRankProjectiveResolution.termAt_tail twoRowZeroResolution hpos 1]
    simp [twoRowZeroResolution]

/-- The tail carries its actual rank-exact row and projective-term certificate. -/
theorem twoRowZeroResolution_tail_row_data :
    ∃ i : Fin (twoRowZeroResolution.tail (by simp [twoRowZeroResolution])).length,
      IsRankExact
          ((twoRowZeroResolution.tail (by simp [twoRowZeroResolution])).inclusion i)
          ((twoRowZeroResolution.tail (by simp [twoRowZeroResolution])).quotient i) ∧
        IsRankProjective
          ((twoRowZeroResolution.tail (by simp [twoRowZeroResolution])).term i) := by
  let T := twoRowZeroResolution.tail (by simp [twoRowZeroResolution])
  have hlen : T.length = 1 := by
    change twoRowZeroResolution.length - 1 = 1
    simp [twoRowZeroResolution]
  let i : Fin T.length := ⟨0, by rw [hlen]; omega⟩
  exact ⟨i, T.row_rank_exact i, T.term_rank_projective i⟩

/-- The selected tail has a genuine nonzero map between distinct grades. -/
theorem twoRowZeroResolution_tail_transition_nonzero :
    structureMapLinear
      ((twoRowZeroResolution.tail (by simp [twoRowZeroResolution])).termAt 0)
      (show (0 : Fin 1 → ℝ) ≤ (fun _ : Fin 1 => (1 : ℝ)) by
        intro i
        norm_num) ≠ 0 := by
  rw [twoRowZeroResolution_tail_data.2.1]
  exact oneCoordinateHook_transition_nonzero

/-- The positive shift carries the grades `-1` and `0` to `0` and `1`. -/
theorem oneCoordinateHookIdentity_shift_grade_values :
    CoordinateShift.translation 1 (fun _ : Fin 1 => (-1 : ℝ)) = 0 ∧
      CoordinateShift.translation 1 (0 : Fin 1 → ℝ) =
        (fun _ : Fin 1 => (1 : ℝ)) := by
  constructor <;> funext i <;> simp [CoordinateShift.translation]

/-- A positive coordinate shift turns the term's map from grades `-1` to `0`
into the original principal-upset map from `0` to `1`. -/
theorem oneCoordinateHookIdentity_shift_transition_nonzero :
    structureMapLinear
      ((FiniteRankProjectiveResolution.shift oneCoordinateHookIdentity 1).termAt 0)
      (show (fun _ : Fin 1 => (-1 : ℝ)) ≤ 0 by
        intro i
        norm_num) ≠ 0 := by
  let p : Fin 1 → ℝ := fun _ => -1
  let q : Fin 1 → ℝ := 0
  have hp : CoordinateShift.translation 1 p = (0 : Fin 1 → ℝ) := by
    simpa [p] using oneCoordinateHookIdentity_shift_grade_values.1
  have hlen : (oneCoordinateHookIdentity.shift 1).length = 1 := rfl
  have hpos : 0 < (oneCoordinateHookIdentity.shift 1).length := by rw [hlen]; omega
  have hterm :
      (FiniteRankProjectiveResolution.shift oneCoordinateHookIdentity 1).termAt 0 =
        (CoordinateShift.shift 1).obj oneCoordinateHook := by
    rw [FiniteRankProjectiveResolution.termAt_eq_term
      (R := oneCoordinateHookIdentity.shift 1) hpos]
    simp [FiniteRankProjectiveResolution.shift, oneCoordinateHookIdentity,
      FiniteRankProjectiveResolution.identity]
  rw [hterm]
  change structureMapLinear
    (reindex (CoordinateShift.translation 1) oneCoordinateHook)
    (show p ≤ q by intro i; norm_num [p, q]) ≠ 0
  rw [structureMapLinear_reindex]
  exact oneCoordinateHook_map_nonzero_of_birth_le _ (by
    intro i
    calc
      0 ≤ (0 : ℝ) := le_rfl
      _ = (CoordinateShift.translation 1 p) i := (congrFun hp i).symm)

/-- The selected isomorphism identifies an in-range shifted term with its actual shift. -/
theorem oneCoordinateHook_shift_termAtIso_in_range :
    Nonempty ((oneCoordinateHookIdentity.shift 1).termAt 0 ≅
      (CoordinateShift.shift 1).obj oneCoordinateHook) := by
  exact ⟨by
    simpa [oneCoordinateHookIdentity, FiniteRankProjectiveResolution.identity] using
      FiniteRankProjectiveResolution.termAt_shiftIso oneCoordinateHookIdentity 1 0⟩

/-- The out-of-range lookup uses the selected isomorphism between the zero terms. -/
theorem oneCoordinateHook_shift_termAtIso_out_of_range :
    Nonempty ((oneCoordinateHookIdentity.shift 1).termAt 1 ≅
      (CoordinateShift.shift 1).obj (oneCoordinateHookIdentity.termAt 1)) := by
  exact ⟨FiniteRankProjectiveResolution.termAt_shiftIso oneCoordinateHookIdentity 1 1⟩

/-- Zero shift retains the selected identity term through the public lookup isomorphism. -/
theorem oneCoordinateHook_zero_shift_termAtIso :
    Nonempty ((oneCoordinateHookIdentity.shift 0).termAt 0 ≅
      (CoordinateShift.shift 0).obj oneCoordinateHook) := by
  exact ⟨by
    simpa [oneCoordinateHookIdentity, FiniteRankProjectiveResolution.identity] using
      FiniteRankProjectiveResolution.termAt_shiftIso oneCoordinateHookIdentity 0 0⟩

/-- The genuine empty resolution remains empty under a positive shift. -/
theorem coordinateZeroLengthResolution_shift_length :
    (coordinateZeroLengthResolution.shift 1).length = 0 := by
  rfl

/-- The tail of the one-term identity is empty, so its degree-zero lookup is zero. -/
theorem oneCoordinateHookIdentity_tail_boundary :
    (oneCoordinateHookIdentity.tail (by
      simp [oneCoordinateHookIdentity, FiniteRankProjectiveResolution.identity])).length = 0 ∧
      (oneCoordinateHookIdentity.tail (by
        simp [oneCoordinateHookIdentity, FiniteRankProjectiveResolution.identity])).termAt 0 = 0 := by
  have hlen : oneCoordinateHookIdentity.length = 1 := by
    simp [oneCoordinateHookIdentity, FiniteRankProjectiveResolution.identity]
  let hpos : 0 < oneCoordinateHookIdentity.length := by rw [hlen]; omega
  constructor
  · change (oneCoordinateHookIdentity.tail hpos).length = 0
    rw [FiniteRankProjectiveResolution.length_tail, hlen]
  · change (oneCoordinateHookIdentity.tail hpos).termAt 0 = 0
    rw [FiniteRankProjectiveResolution.termAt_tail oneCoordinateHookIdentity hpos 0]
    simp [oneCoordinateHookIdentity, FiniteRankProjectiveResolution.identity]

/-- No terms are added when the public zero-padding operation receives count zero. -/
theorem oneCoordinateHookIdentity_zero_padding_length :
    (oneCoordinateHookIdentity.appendZeros 0).length = 1 := by
  rw [FiniteRankProjectiveResolution.appendZeros_length]
  simp [oneCoordinateHookIdentity, FiniteRankProjectiveResolution.identity]

end CoordinateIdentityAndPadding

section BinaryBiproductConsumers

open CategoryTheory.Limits

private def lateHookBirth : Fin 1 → ℝ := fun _ => 1

/-- A second nonzero principal upset, born one unit after `oneCoordinateHook`. -/
noncomputable abbrev lateCoordinateHook : PModule.{0,0,0} ℚ (Fin 1 → ℝ) :=
  HookInfinity.module (R := ℚ) lateHookBirth

private theorem hookMap_nonzero_of_birth_le {i a b : Fin 1 → ℝ}
    (hab : a ≤ b) (hia : i ≤ a) :
    structureMapLinear (HookInfinity.module (R := ℚ) i) hab ≠ 0 := by
  let ea := HookInfinity.fiberEquivOfLe (R := ℚ) (i := i) (a := a) hia
  let eb := HookInfinity.fiberEquivOfLe (R := ℚ) (i := i) (a := b) (hia.trans hab)
  let x := ea.symm 1
  have hx : ea x = 1 := by simp [x]
  intro hzero
  have hmap := HookInfinity.fiberEquivOfLe_structureMap
    (R := ℚ) (i := i) (a := a) (b := b) hia hab x
  have hvanish : eb (structureMapLinear (HookInfinity.module (R := ℚ) i) hab x) = 0 := by
    rw [hzero]
    exact eb.map_zero
  rw [hmap, hx] at hvanish
  exact (one_ne_zero : (1 : ℚ) ≠ 0) hvanish

private theorem lateCoordinateHook_pointwiseFiniteDimensional :
    ∀ p, FiniteDimensional ℚ (lateCoordinateHook.obj p) := by
  intro p
  exact HookInfinity.finiteDimensional (i := lateHookBirth) p

private theorem lateCoordinateHook_rankProjective : IsRankProjective lateCoordinateHook :=
  HookInfinity.isRankProjective (i := lateHookBirth)

/-- The second principal upset also has a nonzero map between distinct grades. -/
theorem lateCoordinateHook_transition_nonzero :
    structureMapLinear lateCoordinateHook
      (show (fun _ : Fin 1 => (1 : ℝ)) ≤ (fun _ : Fin 1 => (2 : ℝ)) by
        intro i
        norm_num) ≠ 0 := by
  exact hookMap_nonzero_of_birth_le
    (i := lateHookBirth) (a := lateHookBirth) (b := fun _ : Fin 1 => 2)
    (by intro i; norm_num [lateHookBirth]) (by intro i; rfl)

/-- The length-one identity resolution of the later principal upset. -/
noncomputable def lateCoordinateHookIdentity :
    FiniteRankProjectiveResolution lateCoordinateHook :=
  FiniteRankProjectiveResolution.identity lateCoordinateHook
    lateCoordinateHook_rankProjective lateCoordinateHook_pointwiseFiniteDimensional

private theorem earlyLate_resolutions_same_length :
    oneCoordinateHookIdentity.length = lateCoordinateHookIdentity.length := by
  simp [oneCoordinateHookIdentity, lateCoordinateHookIdentity,
    FiniteRankProjectiveResolution.identity]

/-- A length-one resolution whose selected degree-zero term has two nonzero summands. -/
noncomputable def earlyLateBiproductResolution :
    FiniteRankProjectiveResolution (oneCoordinateHook ⊞ lateCoordinateHook) :=
  FiniteRankProjectiveResolution.biprod oneCoordinateHookIdentity
    lateCoordinateHookIdentity earlyLate_resolutions_same_length

/-- The chosen zero-padded term lookup for the two-hook resolution. -/
noncomputable def earlyLateBiproductTermAtLookup :
    earlyLateBiproductResolution.termAt 0 ≅
      oneCoordinateHookIdentity.termAt 0 ⊞ lateCoordinateHookIdentity.termAt 0 :=
  FiniteRankProjectiveResolution.termAt_biprodIso oneCoordinateHookIdentity
    lateCoordinateHookIdentity earlyLate_resolutions_same_length 0

private theorem selectedBiproductConjugateMap
    {A B T : PModule.{0,0,0} ℚ (Fin 1 → ℝ)} (e : T ≅ A ⊞ B)
    {p q : Fin 1 → ℝ} (hpq : p ≤ q) :
    e.inv.app p ≫ structureMap T hpq ≫ e.hom.app q =
      structureMap (A ⊞ B) hpq := by
  change e.inv.app p ≫ T.map (homOfLE hpq) ≫ e.hom.app q =
    (A ⊞ B).map (homOfLE hpq)
  have hnat := e.hom.naturality (homOfLE hpq)
  change T.map (homOfLE hpq) ≫ e.hom.app q =
    e.hom.app p ≫ (A ⊞ B).map (homOfLE hpq) at hnat
  have h := congrArg (fun f => e.inv.app p ≫ f) hnat
  simpa [Category.assoc] using h

private theorem selectedBiproductLeftDirect
    {A B : PModule.{0,0,0} ℚ (Fin 1 → ℝ)} {p q : Fin 1 → ℝ}
    (hpq : p ≤ q) :
    (biprod.inl : A ⟶ A ⊞ B).app p ≫ structureMap (A ⊞ B) hpq ≫
      (biprod.fst : A ⊞ B ⟶ A).app q = structureMap A hpq := by
  have hnat := (biprod.inl : A ⟶ A ⊞ B).naturality (homOfLE hpq)
  change structureMap A hpq ≫ (biprod.inl : A ⟶ A ⊞ B).app q =
    (biprod.inl : A ⟶ A ⊞ B).app p ≫ structureMap (A ⊞ B) hpq at hnat
  have hcomp : (biprod.inl : A ⟶ A ⊞ B).app q ≫
      (biprod.fst : A ⊞ B ⟶ A).app q = 𝟙 _ := by
    have h := congrArg (fun f : A ⟶ A => f.app q)
      (biprod.inl_fst : (biprod.inl : A ⟶ A ⊞ B) ≫ biprod.fst = 𝟙 A)
    simpa only [NatTrans.comp_app, NatTrans.id_app] using h
  calc
    (biprod.inl : A ⟶ A ⊞ B).app p ≫ structureMap (A ⊞ B) hpq ≫
        (biprod.fst : A ⊞ B ⟶ A).app q =
      (structureMap A hpq ≫ (biprod.inl : A ⟶ A ⊞ B).app q) ≫
        (biprod.fst : A ⊞ B ⟶ A).app q := by
      exact congrArg (fun f => f ≫ (biprod.fst : A ⊞ B ⟶ A).app q) hnat.symm
    _ = structureMap A hpq := by
      rw [Category.assoc, hcomp, Category.comp_id]

private theorem selectedBiproductRightDirect
    {A B : PModule.{0,0,0} ℚ (Fin 1 → ℝ)} {p q : Fin 1 → ℝ}
    (hpq : p ≤ q) :
    (biprod.inr : B ⟶ A ⊞ B).app p ≫ structureMap (A ⊞ B) hpq ≫
      (biprod.snd : A ⊞ B ⟶ B).app q = structureMap B hpq := by
  have hnat := (biprod.inr : B ⟶ A ⊞ B).naturality (homOfLE hpq)
  change structureMap B hpq ≫ (biprod.inr : B ⟶ A ⊞ B).app q =
    (biprod.inr : B ⟶ A ⊞ B).app p ≫ structureMap (A ⊞ B) hpq at hnat
  have hcomp : (biprod.inr : B ⟶ A ⊞ B).app q ≫
      (biprod.snd : A ⊞ B ⟶ B).app q = 𝟙 _ := by
    have h := congrArg (fun f : B ⟶ B => f.app q)
      (biprod.inr_snd : (biprod.inr : B ⟶ A ⊞ B) ≫ biprod.snd = 𝟙 B)
    simpa only [NatTrans.comp_app, NatTrans.id_app] using h
  calc
    (biprod.inr : B ⟶ A ⊞ B).app p ≫ structureMap (A ⊞ B) hpq ≫
        (biprod.snd : A ⊞ B ⟶ B).app q =
      (structureMap B hpq ≫ (biprod.inr : B ⟶ A ⊞ B).app q) ≫
        (biprod.snd : A ⊞ B ⟶ B).app q := by
      exact congrArg (fun f => f ≫ (biprod.snd : A ⊞ B ⟶ B).app q) hnat.symm
    _ = structureMap B hpq := by
      rw [Category.assoc, hcomp, Category.comp_id]

private theorem selectedBiproductLeftMap
    {A B T : PModule.{0,0,0} ℚ (Fin 1 → ℝ)} (e : T ≅ A ⊞ B)
    {p q : Fin 1 → ℝ} (hpq : p ≤ q) :
    (biprod.inl : A ⟶ A ⊞ B).app p ≫ e.inv.app p ≫
      structureMap T hpq ≫ e.hom.app q ≫ (biprod.fst : A ⊞ B ⟶ A).app q =
    structureMap A hpq := by
  calc
    _ = (biprod.inl : A ⟶ A ⊞ B).app p ≫
        (e.inv.app p ≫ structureMap T hpq ≫ e.hom.app q) ≫
        (biprod.fst : A ⊞ B ⟶ A).app q := by
      simp only [Category.assoc]
    _ = (biprod.inl : A ⟶ A ⊞ B).app p ≫
        structureMap (A ⊞ B) hpq ≫ (biprod.fst : A ⊞ B ⟶ A).app q := by
      rw [selectedBiproductConjugateMap e hpq]
    _ = structureMap A hpq := selectedBiproductLeftDirect hpq

private theorem selectedBiproductRightMap
    {A B T : PModule.{0,0,0} ℚ (Fin 1 → ℝ)} (e : T ≅ A ⊞ B)
    {p q : Fin 1 → ℝ} (hpq : p ≤ q) :
    (biprod.inr : B ⟶ A ⊞ B).app p ≫ e.inv.app p ≫
      structureMap T hpq ≫ e.hom.app q ≫ (biprod.snd : A ⊞ B ⟶ B).app q =
    structureMap B hpq := by
  calc
    _ = (biprod.inr : B ⟶ A ⊞ B).app p ≫
        (e.inv.app p ≫ structureMap T hpq ≫ e.hom.app q) ≫
        (biprod.snd : A ⊞ B ⟶ B).app q := by
      simp only [Category.assoc]
    _ = (biprod.inr : B ⟶ A ⊞ B).app p ≫
        structureMap (A ⊞ B) hpq ≫ (biprod.snd : A ⊞ B ⟶ B).app q := by
      rw [selectedBiproductConjugateMap e hpq]
    _ = structureMap B hpq := selectedBiproductRightDirect hpq

/-- The first actual structure map is selected by inclusion, lookup and projection. -/
theorem earlyLateBiproduct_left_component_map {p q : Fin 1 → ℝ} (hpq : p ≤ q) :
    (biprod.inl : oneCoordinateHookIdentity.termAt 0 ⟶
        oneCoordinateHookIdentity.termAt 0 ⊞ lateCoordinateHookIdentity.termAt 0).app p ≫
      earlyLateBiproductTermAtLookup.inv.app p ≫
      structureMap (earlyLateBiproductResolution.termAt 0) hpq ≫
      earlyLateBiproductTermAtLookup.hom.app q ≫
      (biprod.fst : oneCoordinateHookIdentity.termAt 0 ⊞
        lateCoordinateHookIdentity.termAt 0 ⟶ oneCoordinateHookIdentity.termAt 0).app q =
    structureMap (oneCoordinateHookIdentity.termAt 0) hpq := by
  exact selectedBiproductLeftMap earlyLateBiproductTermAtLookup hpq

/-- The second actual structure map is selected by inclusion, lookup and projection. -/
theorem earlyLateBiproduct_right_component_map {p q : Fin 1 → ℝ} (hpq : p ≤ q) :
    (biprod.inr : lateCoordinateHookIdentity.termAt 0 ⟶
        oneCoordinateHookIdentity.termAt 0 ⊞ lateCoordinateHookIdentity.termAt 0).app p ≫
      earlyLateBiproductTermAtLookup.inv.app p ≫
      structureMap (earlyLateBiproductResolution.termAt 0) hpq ≫
      earlyLateBiproductTermAtLookup.hom.app q ≫
      (biprod.snd : oneCoordinateHookIdentity.termAt 0 ⊞
        lateCoordinateHookIdentity.termAt 0 ⟶ lateCoordinateHookIdentity.termAt 0).app q =
    structureMap (lateCoordinateHookIdentity.termAt 0) hpq := by
  exact selectedBiproductRightMap earlyLateBiproductTermAtLookup hpq

/-- The earlier summand survives from grade one to grade two, as does the later one. -/
theorem earlyCoordinateHook_selected_term_transition_nonzero :
    structureMapLinear (oneCoordinateHookIdentity.termAt 0)
      (show (fun _ : Fin 1 => (1 : ℝ)) ≤ (fun _ : Fin 1 => (2 : ℝ)) by
        intro i
        norm_num) ≠ 0 := by
  rw [FiniteRankProjectiveResolution.termAt_eq_term
    (R := oneCoordinateHookIdentity) (by
      simp [oneCoordinateHookIdentity, FiniteRankProjectiveResolution.identity])]
  change structureMapLinear oneCoordinateHook _ ≠ 0
  exact hookMap_nonzero_of_birth_le
    (i := (0 : Fin 1 → ℝ)) (a := fun _ : Fin 1 => 1) (b := fun _ : Fin 1 => 2)
    (by intro i; norm_num) (by intro i; norm_num)

/-- The later summand survives its transition from grade one to grade two. -/
theorem lateCoordinateHook_selected_term_transition_nonzero :
    structureMapLinear (lateCoordinateHookIdentity.termAt 0)
      (show (fun _ : Fin 1 => (1 : ℝ)) ≤ (fun _ : Fin 1 => (2 : ℝ)) by
        intro i
        norm_num) ≠ 0 := by
  rw [FiniteRankProjectiveResolution.termAt_eq_term
    (R := lateCoordinateHookIdentity) (by
      simp [lateCoordinateHookIdentity, FiniteRankProjectiveResolution.identity])]
  change structureMapLinear lateCoordinateHook _ ≠ 0
  exact lateCoordinateHook_transition_nonzero

/-- The chosen lookup includes a degree-zero term and its two selected components. -/
theorem earlyLateBiproduct_in_range_lookup :
    Nonempty (earlyLateBiproductResolution.termAt 0 ≅
      oneCoordinateHookIdentity.termAt 0 ⊞ lateCoordinateHookIdentity.termAt 0) :=
  ⟨earlyLateBiproductTermAtLookup⟩

/-- At the common length boundary, lookup selects both zero-padded terms. -/
theorem earlyLateBiproduct_boundary_lookup :
    Nonempty (earlyLateBiproductResolution.termAt 1 ≅
      oneCoordinateHookIdentity.termAt 1 ⊞ lateCoordinateHookIdentity.termAt 1) :=
  ⟨FiniteRankProjectiveResolution.termAt_biprodIso oneCoordinateHookIdentity
    lateCoordinateHookIdentity earlyLate_resolutions_same_length 1⟩

/-- Beyond the common length, the selected lookup still matches the zero-padded terms. -/
theorem earlyLateBiproduct_out_of_range_lookup :
    Nonempty (earlyLateBiproductResolution.termAt 2 ≅
      oneCoordinateHookIdentity.termAt 2 ⊞ lateCoordinateHookIdentity.termAt 2) :=
  ⟨FiniteRankProjectiveResolution.termAt_biprodIso oneCoordinateHookIdentity
    lateCoordinateHookIdentity earlyLate_resolutions_same_length 2⟩

/-- Repeating the same nonzero resolution retains two copies in its selected term. -/
noncomputable def repeatedHookBiproductResolution :
    FiniteRankProjectiveResolution (oneCoordinateHook ⊞ oneCoordinateHook) :=
  FiniteRankProjectiveResolution.biprod oneCoordinateHookIdentity
    oneCoordinateHookIdentity rfl

/-- The repeated input has the chosen two-occurrence degree-zero lookup. -/
theorem repeatedHookBiproduct_lookup :
    Nonempty (repeatedHookBiproductResolution.termAt 0 ≅
      oneCoordinateHookIdentity.termAt 0 ⊞ oneCoordinateHookIdentity.termAt 0) :=
  ⟨FiniteRankProjectiveResolution.termAt_biprodIso oneCoordinateHookIdentity
    oneCoordinateHookIdentity rfl 0⟩

/-- An empty resolution remains empty under the equal-length binary operation. -/
noncomputable def emptyZeroBiproductResolution :
    FiniteRankProjectiveResolution
      ((0 : PModule.{0,0,0} ℚ (Fin 1 → ℝ)) ⊞ 0) :=
  FiniteRankProjectiveResolution.biprod coordinateZeroLengthResolution
    coordinateZeroLengthResolution rfl

/-- The equal-length operation preserves the genuine length-zero boundary. -/
theorem emptyZeroBiproductResolution_length : emptyZeroBiproductResolution.length = 0 := rfl

/-- The empty operation's lookup at zero uses the two selected zero terms. -/
theorem emptyZeroBiproductResolution_boundary_lookup :
    Nonempty (emptyZeroBiproductResolution.termAt 0 ≅
      coordinateZeroLengthResolution.termAt 0 ⊞ coordinateZeroLengthResolution.termAt 0) :=
  ⟨FiniteRankProjectiveResolution.termAt_biprodIso coordinateZeroLengthResolution
    coordinateZeroLengthResolution rfl 0⟩

/-- Zero coordinate dimensions still support the selected binary resolution API. -/
noncomputable def zeroCoordinateRepeatedBiproductResolution :
    FiniteRankProjectiveResolution (zeroCoordinateHook ⊞ zeroCoordinateHook) :=
  FiniteRankProjectiveResolution.biprod zeroCoordinateHookIdentity
    zeroCoordinateHookIdentity rfl

/-- The zero-dimensional example retains both selected summands at degree zero. -/
theorem zeroCoordinateRepeatedBiproduct_lookup :
    Nonempty (zeroCoordinateRepeatedBiproductResolution.termAt 0 ≅
      zeroCoordinateHookIdentity.termAt 0 ⊞ zeroCoordinateHookIdentity.termAt 0) :=
  ⟨FiniteRankProjectiveResolution.termAt_biprodIso zeroCoordinateHookIdentity
    zeroCoordinateHookIdentity rfl 0⟩

private theorem hookAndZero_same_length :
    oneCoordinateHookIdentity.length =
      (coordinateZeroLengthResolution.appendZeros 1).length := by
  rw [FiniteRankProjectiveResolution.appendZeros_length,
    oneCoordinateHookIdentity_selected_data.1]
  simp [coordinateZeroLengthResolution]

/-- A zero summand is explicitly padded to match the nonzero length-one input. -/
noncomputable def hookWithMatchedZeroBiproductResolution :
    FiniteRankProjectiveResolution
      (oneCoordinateHook ⊞ (0 : PModule.{0,0,0} ℚ (Fin 1 → ℝ))) :=
  FiniteRankProjectiveResolution.biprod oneCoordinateHookIdentity
    (coordinateZeroLengthResolution.appendZeros 1) hookAndZero_same_length

/-- The matched summand is zero, and its selected lookup is the actual padded term. -/
theorem hookWithMatchedZero_selected_term_lookup :
    Nonempty (hookWithMatchedZeroBiproductResolution.termAt 0 ≅
      oneCoordinateHookIdentity.termAt 0 ⊞
        (coordinateZeroLengthResolution.appendZeros 1).termAt 0) ∧
      (coordinateZeroLengthResolution.appendZeros 1).termAt 0 = 0 := by
  constructor
  · exact ⟨FiniteRankProjectiveResolution.termAt_biprodIso oneCoordinateHookIdentity
      (coordinateZeroLengthResolution.appendZeros 1) hookAndZero_same_length 0⟩
  · exact coordinateZeroLengthResolution_padded_termAt 1 0

/-- The original one-term and two-row resolutions have unequal stored lengths. -/
theorem oneTerm_twoRow_stored_lengths_unequal :
    oneCoordinateHookIdentity.length ≠ twoRowZeroResolution.length := by
  simp [oneCoordinateHookIdentity, twoRowZeroResolution,
    FiniteRankProjectiveResolution.identity]

private theorem paddedHook_twoRow_same_length :
    (oneCoordinateHookIdentity.appendZeros 1).length = twoRowZeroResolution.length := by
  rw [FiniteRankProjectiveResolution.appendZeros_length,
    oneCoordinateHookIdentity_selected_data.1]
  rfl

/-- The shorter input is explicitly padded before the unchanged equal-length constructor. -/
noncomputable def paddedHookTwoRowBiproductResolution :
    FiniteRankProjectiveResolution (oneCoordinateHook ⊞ realCoordinateZero) :=
  FiniteRankProjectiveResolution.biprod (oneCoordinateHookIdentity.appendZeros 1)
    twoRowZeroResolution paddedHook_twoRow_same_length

/-- The padded construction records the common stored length two. -/
theorem paddedHookTwoRowBiproductResolution_length :
    paddedHookTwoRowBiproductResolution.length = 2 := by
  change (oneCoordinateHookIdentity.appendZeros 1).length = 2
  rw [FiniteRankProjectiveResolution.appendZeros_length,
    oneCoordinateHookIdentity_selected_data.1]

/-- The padded construction uses the public lookup on its actual degree-zero terms. -/
theorem paddedHookTwoRowBiproduct_lookup :
    Nonempty (paddedHookTwoRowBiproductResolution.termAt 0 ≅
      (oneCoordinateHookIdentity.appendZeros 1).termAt 0 ⊞ twoRowZeroResolution.termAt 0) :=
  ⟨FiniteRankProjectiveResolution.termAt_biprodIso
    (oneCoordinateHookIdentity.appendZeros 1) twoRowZeroResolution
    paddedHook_twoRow_same_length 0⟩

end BinaryBiproductConsumers

end TDA.Persistence.FiniteRankProjectiveResolutionExamples
