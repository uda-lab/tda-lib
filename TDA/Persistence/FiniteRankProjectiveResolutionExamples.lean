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

end TDA.Persistence.FiniteRankProjectiveResolutionExamples
