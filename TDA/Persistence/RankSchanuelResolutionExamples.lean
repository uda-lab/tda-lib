import TDA.Persistence.RankSchanuelResolution
import TDA.Persistence.HookEndomorphisms

/-!
# Examples of persistent Schanuel for finite resolutions

These consumers exercise zero and unequal lengths, a one-term projective
resolution, a genuinely nonzero second term, and the zero-shift boundary.
-/

set_option autoImplicit false

namespace TDA.Persistence.RankSchanuelResolutionExamples

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject NNReal

noncomputable abbrev zeroModule : PModule.{0,0,0} ℚ (Fin 0 → ℝ) := 0

noncomputable abbrev hookModule : PModule.{0,0,0} ℚ (Fin 0 → ℝ) :=
  HookInfinity.module (R := ℚ) (0 : Fin 0 → ℝ)

private instance : HasFiniteBiproducts (PModule.{0,0,0} ℚ (Fin 0 → ℝ)) :=
  HasFiniteBiproducts.of_hasFiniteProducts

private theorem hook_finiteDimensional (a : Fin 0 → ℝ) :
    FiniteDimensional ℚ ((hookModule).obj a) := by
  change FiniteDimensional ℚ ((HookInfinity.module (R := ℚ) (0 : Fin 0 → ℝ)).obj a)
  infer_instance

private theorem hook_projective : IsRankProjective hookModule :=
  HookInfinity.isRankProjective (0 : Fin 0 → ℝ)

private theorem zeroIdRankExact (P : PModule.{0,0,0} ℚ (Fin 0 → ℝ))
    [∀ a, FiniteDimensional ℚ (P.obj a)] :
    IsRankExact (0 : zeroModule ⟶ P) (𝟙 P) := by
  have hshort : IsPointwiseShortExact (0 : zeroModule ⟶ P) (𝟙 P) := by
    constructor
    · intro a x y _
      exact (ModuleCat.subsingleton_of_isZero (Functor.zero_obj a)).elim x y
    · intro a x
      exact ⟨x, rfl⟩
    · intro a
      simp
  exact hshort.rankExact_of_section (𝟙 P) (by simp)

private theorem idZeroRankExact (P : PModule.{0,0,0} ℚ (Fin 0 → ℝ))
    [∀ a, FiniteDimensional ℚ (P.obj a)] :
    IsRankExact (𝟙 P) (0 : P ⟶ zeroModule) := by
  have hshort : IsPointwiseShortExact (𝟙 P) (0 : P ⟶ zeroModule) := by
    constructor
    · intro _ x y h
      exact h
    · intro a y
      have hzero : Subsingleton (zeroModule.obj a) :=
        ModuleCat.subsingleton_of_isZero (Functor.zero_obj a)
      exact ⟨0, hzero.elim _ _⟩
    · intro a
      simp
  exact hshort.rankExact_of_section (0 : zeroModule ⟶ P) (by simp)

private noncomputable def twoTermKernel : Fin 3 → PModule.{0,0,0} ℚ (Fin 0 → ℝ) :=
  fun i => if i.val = 1 then hookModule else zeroModule

private noncomputable def twoTermTerm : Fin 2 → PModule.{0,0,0} ℚ (Fin 0 → ℝ) :=
  fun _ => hookModule

private noncomputable def twoTermInclusion :
    ∀ i : Fin 2, twoTermKernel i.succ ⟶ twoTermTerm i := by
  intro i
  refine Fin.cases ?_ ?_ i
  · change hookModule ⟶ hookModule
    exact 𝟙 hookModule
  · intro j
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    change zeroModule ⟶ hookModule
    exact 0

private noncomputable def twoTermQuotient :
    ∀ i : Fin 2, twoTermTerm i ⟶ twoTermKernel i.castSucc := by
  intro i
  refine Fin.cases ?_ ?_ i
  · change hookModule ⟶ zeroModule
    exact 0
  · intro j
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    change hookModule ⟶ hookModule
    exact 𝟙 hookModule

private theorem twoTermRows :
    ∀ i : Fin 2, IsRankExact (twoTermInclusion i) (twoTermQuotient i) := by
  intro i
  refine Fin.cases ?_ ?_ i
  · change IsRankExact (𝟙 hookModule) (0 : hookModule ⟶ zeroModule)
    exact idZeroRankExact hookModule
  · intro j
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    change IsRankExact (0 : zeroModule ⟶ hookModule) (𝟙 hookModule)
    exact zeroIdRankExact hookModule

/-- A two-term resolution of zero with a nonzero projective in its tail. -/
noncomputable def twoTermZeroResolution :
    FiniteRankProjectiveResolution (M := zeroModule) where
  toFiniteRankExactResolution := {
    length := 2
    kernel := twoTermKernel
    term := twoTermTerm
    inclusion := twoTermInclusion
    quotient := twoTermQuotient
    row_rank_exact := twoTermRows
    initial_iso := by simpa [twoTermKernel] using (Iso.refl zeroModule)
    terminal_iso := by simpa [twoTermKernel] using (Iso.refl zeroModule)
  }
  term_rank_projective := fun _ => hook_projective

/-- The homological tail really contains the nonzero hook, rather than zero padding. -/
theorem twoTerm_tail_nonzero :
    ∃ x : (twoTermZeroResolution.term (1 : Fin 2)).obj (0 : Fin 0 → ℝ), x ≠ 0 := by
  change ∃ x : (hookModule).obj (0 : Fin 0 → ℝ), x ≠ 0
  exact ⟨HookInfinity.birth (R := ℚ) (0 : Fin 0 → ℝ),
    HookInfinity.birth_ne_zero (k := ℚ) (0 : Fin 0 → ℝ)⟩

/-- The zero module has an actual resolution of length zero. -/
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

/-- A one-term resolution supplies an actual consumer of the length-one case. -/
noncomputable def oneTermResolution : FiniteRankProjectiveResolution hookModule :=
  FiniteRankProjectiveResolution.identity hookModule hook_projective hook_finiteDimensional

/-- The empty biproduct boundary is used when both resolutions have length zero. -/
noncomputable def zeroLengthComparison (ε : ℝ≥0) :
    CoordinateInterleaving ε
      (FiniteRankProjectiveResolution.schanuelLeftBiproduct
        zeroLengthResolution zeroLengthResolution ε)
      (FiniteRankProjectiveResolution.schanuelRightBiproduct
        zeroLengthResolution zeroLengthResolution ε) :=
  schanuelInterleavingOfResolutions zeroLengthResolution zeroLengthResolution ε
    (CoordinateInterleaving.refl ε zeroModule)

/-- Unequal lengths, including a zero-length side, still produce the public comparison. -/
noncomputable def zeroVsTwoTermComparison (ε : ℝ≥0) :
    CoordinateInterleaving ε
      (FiniteRankProjectiveResolution.schanuelLeftBiproduct
        zeroLengthResolution twoTermZeroResolution ε)
      (FiniteRankProjectiveResolution.schanuelRightBiproduct
        zeroLengthResolution twoTermZeroResolution ε) :=
  schanuelInterleavingOfResolutions zeroLengthResolution twoTermZeroResolution ε
    (CoordinateInterleaving.refl ε zeroModule)

/-- The one-term boundary is exercised through the same public theorem. -/
noncomputable def oneTermComparison (ε : ℝ≥0) :
    CoordinateInterleaving ε
      (FiniteRankProjectiveResolution.schanuelLeftBiproduct
        oneTermResolution oneTermResolution ε)
      (FiniteRankProjectiveResolution.schanuelRightBiproduct
        oneTermResolution oneTermResolution ε) :=
  schanuelInterleavingOfResolutions oneTermResolution oneTermResolution ε
    (CoordinateInterleaving.refl ε hookModule)

/-- The zero-shift case returns a checked interleaving for nonzero tail terms. -/
noncomputable def zeroParameterComparison :
    CoordinateInterleaving 0
      (FiniteRankProjectiveResolution.schanuelLeftBiproduct
        twoTermZeroResolution twoTermZeroResolution 0)
      (FiniteRankProjectiveResolution.schanuelRightBiproduct
        twoTermZeroResolution twoTermZeroResolution 0) :=
  schanuelInterleavingOfResolutions twoTermZeroResolution twoTermZeroResolution 0
    (CoordinateInterleaving.refl 0 zeroModule)

end TDA.Persistence.RankSchanuelResolutionExamples
