import TDA.Persistence.FiniteRankProjectiveResolutionHookBetti
import TDA.Persistence.FiniteRankProjectiveResolution

/-!
# Examples for resolution hook multisets

The principal upset is already a projective hook. Its identity resolution
therefore has no positive-degree hook occurrences, and uniqueness transfers
that vanishing to every certified minimal resolution.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence.FiniteRankProjectiveResolutionHookBettiExamples

open CategoryTheory
open CategoryTheory.Limits
open scoped ZeroObject

private noncomputable abbrev principalHook : PModule.{0,0,0} ℚ (Fin 2 → ℝ) :=
  HookInfinity.module (R := ℚ) (0 : Fin 2 → ℝ)

private theorem principalHook_finitelyPresented :
    GradedFree.FinitelyPresented (R := ℚ) (P := Fin 2 → ℝ) principalHook :=
  GradedFree.free_finitelyPresented (R := ℚ) (P := Fin 2 → ℝ)
    (HookInfinity.generators (P := Fin 2 → ℝ) (0 : Fin 2 → ℝ))

private theorem principalHook_identity_isRankProjectiveCover :
    IsRankProjectiveCover (𝟙 principalHook) := by
  apply IsRankProjectiveCover.of_identity
  · intro p
    infer_instance
  · exact HookInfinity.isRankProjective (i := (0 : Fin 2 → ℝ))

private noncomputable def principalHookFiniteResolution :
    FiniteRankProjectiveResolution principalHook :=
  FiniteRankProjectiveResolution.ofRankProjective principalHook
    (by intro p; infer_instance)
    (HookInfinity.isRankProjective (i := (0 : Fin 2 → ℝ)))

/-- The identity quotient gives the one-term minimal resolution of this free
principal-upset hook. -/
noncomputable def principalHookIdentityMinimalResolution :
    MinimalFiniteRankProjectiveResolution (k := ℚ) (M := principalHook) where
  resolution := principalHookFiniteResolution
  quotient_is_cover := by
    intro i
    have hlen : principalHookFiniteResolution.length = 1 := rfl
    have hi : i = ⟨0, by rw [hlen]; omega⟩ := by
      apply Fin.ext
      have hval : i.val < 1 := by simpa only [hlen] using i.isLt
      omega
    subst i
    change IsRankProjectiveCover (𝟙 principalHook)
    exact principalHook_identity_isRankProjectiveCover

/-- Since a principal upset is projective, every certified minimal resolution
has zero positive-degree terms and therefore no positive-degree hook tags. -/
theorem principalHook_positive_degree_terms_have_empty_hook_multiset
    (R : MinimalFiniteRankProjectiveResolution (k := ℚ) (M := principalHook))
    {j : ℕ} (hj : 0 < j) :
    R.hookBettiMultiset (k := ℚ) (n := 2) principalHook
      principalHook_finitelyPresented j = 0 := by
  apply R.hookBettiMultiset_eq_zero_of_term_isZero
    (k := ℚ) (n := 2) principalHook principalHook_finitelyPresented
  obtain ⟨e⟩ := R.termAt_nonempty_iso principalHookIdentityMinimalResolution j
  have hzero : principalHookIdentityMinimalResolution.termAt j =
      (0 : PModule.{0,0,0} ℚ (Fin 2 → ℝ)) := by
    apply principalHookIdentityMinimalResolution.termAt_eq_zero
    change 1 ≤ j
    omega
  exact IsZero.of_iso (isZero_zero _) (e.trans (eqToIso hzero))

section HookTagEnumeration

/-- A finite two-dimensional hook tag used in the enumeration examples. -/
def twoDimensionalRepeatedFiniteTag : RealHookTag (n := 2) :=
  .inl ⟨(fun _ : Fin 2 => (0 : ℝ), fun _ : Fin 2 => (1 : ℝ)), by
    apply Pi.lt_def.mpr
    constructor
    · intro i
      norm_num
    · exact ⟨0, by norm_num⟩⟩

/-- A principal two-dimensional hook tag used in the enumeration examples. -/
def twoDimensionalPrincipalTag : RealHookTag (n := 2) :=
  .inr (fun _ : Fin 2 => (0 : ℝ))

/-- Two equal finite tags and one principal tag, indexed by `Fin 3`. -/
def twoDimensionalMixedFamily : Fin 3 → RealHookTag (n := 2) := fun i =>
  if i.val = 0 then twoDimensionalRepeatedFiniteTag
  else if i.val = 1 then twoDimensionalRepeatedFiniteTag
  else twoDimensionalPrincipalTag

/-- The empty two-dimensional family has empty tag multiset. -/
theorem twoDimensionalEmptyFamily_hookTagMultiset_eq_zero :
    hookTagMultiset (Fin.elim0 : Fin 0 → RealHookTag (n := 2)) = 0 := by
  rw [hookTagMultiset_eq_map_univ]
  simp

/-- Reindexing occurrences by a permutation leaves their multiset unchanged. -/
theorem twoDimensionalMixedFamily_comp_perm (σ : Equiv.Perm (Fin 3)) :
    hookTagMultiset (twoDimensionalMixedFamily ∘ σ) =
      hookTagMultiset twoDimensionalMixedFamily := by
  rw [hookTagMultiset_eq_ofFn, hookTagMultiset_eq_ofFn]
  exact Quot.sound (Equiv.Perm.ofFn_comp_perm σ twoDimensionalMixedFamily)

/-- The two-dimensional example retains the repeated finite tag and principal
tag as three separate occurrences. -/
theorem twoDimensionalMixedFamily_hookTagMultiset :
    hookTagMultiset twoDimensionalMixedFamily =
    {twoDimensionalRepeatedFiniteTag, twoDimensionalRepeatedFiniteTag,
      twoDimensionalPrincipalTag} := by
  rw [hookTagMultiset_eq_ofFn]
  rfl

theorem twoDimensionalMixedFamily_card :
    (hookTagMultiset twoDimensionalMixedFamily).card = 3 := by
  rw [hookTagMultiset_eq_map_univ]
  simp

theorem twoDimensionalMixedFamily_count_repeatedFinite :
    (hookTagMultiset twoDimensionalMixedFamily).count
      twoDimensionalRepeatedFiniteTag = 2 := by
  rw [hookTagMultiset_count]
  classical
  rw [Fintype.card_subtype, Fin.card_filter_univ_succ', Fin.card_filter_univ_succ']
  simp [twoDimensionalMixedFamily, twoDimensionalRepeatedFiniteTag,
    twoDimensionalPrincipalTag]

theorem twoDimensionalMixedFamily_count_principal :
    (hookTagMultiset twoDimensionalMixedFamily).count
      twoDimensionalPrincipalTag = 1 := by
  rw [hookTagMultiset_count]
  classical
  rw [Fintype.card_subtype, Fin.card_filter_univ_succ', Fin.card_filter_univ_succ']
  simp [twoDimensionalMixedFamily, twoDimensionalRepeatedFiniteTag,
    twoDimensionalPrincipalTag]

theorem zeroDimensionalPrincipalFamily_card (m : ℕ) (a : Fin 0 → ℝ) :
    (hookTagMultiset
      (fun _ : Fin m => (Sum.inr a : RealHookTag (n := 0)))).card = m := by
  rw [hookTagMultiset_eq_map_univ]
  simp

theorem zeroDimensionalPrincipalFamily_count (m : ℕ) (a : Fin 0 → ℝ) :
    (hookTagMultiset
      (fun _ : Fin m => (Sum.inr a : RealHookTag (n := 0)))).count
        (Sum.inr a) = m := by
  rw [hookTagMultiset_count]
  simp

/-- In dimension zero there are no strict finite-death endpoint pairs. -/
theorem zeroDimensional_has_no_finite_death_pair :
    IsEmpty (FiniteHookDeflation.StrictPair (Fin 0 → ℝ)) := by
  constructor
  intro ab
  have hEndpoints : ab.val.1 = ab.val.2 := by
    funext i
    exact Fin.elim0 i
  have hStrict := ab.property
  rw [hEndpoints] at hStrict
  exact lt_irrefl _ hStrict

end HookTagEnumeration

end TDA.Persistence.FiniteRankProjectiveResolutionHookBettiExamples
