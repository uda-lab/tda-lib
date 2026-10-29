import TDA.Persistence.RankSignedStability
import TDA.Persistence.RankSchanuelUnshiftedExamples

/-!
# Consumers of signed hook stability

These examples apply the original-finite-presentation capstone in dimensions
one and two, including zero input distance, and exercise finite-death,
principal-upset, empty, and repeated cross-sign occurrences.
-/

set_option autoImplicit false

namespace TDA.Persistence.RankSignedStabilityExamples

open CategoryTheory CategoryTheory.Limits CoordinateShift HookMatching
open scoped TDA.Persistence NNReal ENNReal ZeroObject

private instance : HasFiniteBiproducts
    (PModule.{0,0,0} ℚ (Fin 1 → ℝ)) :=
  HasFiniteBiproducts.of_hasFiniteProducts

private instance : HasFiniteBiproducts
    (PModule.{0,0,0} ℚ (Fin 2 → ℝ)) :=
  HasFiniteBiproducts.of_hasFiniteProducts

private theorem oneCoordinateHook_finitelyPresented :
    GradedFree.FinitelyPresented (R := ℚ) (P := Fin 1 → ℝ)
      RankSchanuelUnshiftedExamples.oneCoordinateHook :=
  GradedFree.free_finitelyPresented (R := ℚ) (P := Fin 1 → ℝ)
    (HookInfinity.generators (P := Fin 1 → ℝ) (0 : Fin 1 → ℝ))

private noncomputable def oneCoordinateHookMinimalResolution :
    MinimalFiniteRankProjectiveResolution (k := ℚ)
      (M := RankSchanuelUnshiftedExamples.oneCoordinateHook) :=
  Classical.choice
    (FiniteRankProjectiveResolution.finitelyPresented_exists_minimalFiniteRankProjectiveResolution
      (by norm_num) RankSchanuelUnshiftedExamples.oneCoordinateHook
      oneCoordinateHook_finitelyPresented)

/-- The one-coordinate consumer uses the original finite-presentation
hypotheses and produces the actual squared-coefficient matching. -/
theorem oneCoordinate_signedMatching (ε : ℝ≥0) :
    HasMultisetMatching (k := ℚ) (n := 1) ε
      ((oneCoordinateHookMinimalResolution.signedHookBarcode
        (k := ℚ) (n := 1)
        RankSchanuelUnshiftedExamples.oneCoordinateHook
        oneCoordinateHook_finitelyPresented).positive +
       (oneCoordinateHookMinimalResolution.signedHookBarcode
        (k := ℚ) (n := 1)
        RankSchanuelUnshiftedExamples.oneCoordinateHook
        oneCoordinateHook_finitelyPresented).negative)
      ((oneCoordinateHookMinimalResolution.signedHookBarcode
        (k := ℚ) (n := 1)
        RankSchanuelUnshiftedExamples.oneCoordinateHook
        oneCoordinateHook_finitelyPresented).positive +
       (oneCoordinateHookMinimalResolution.signedHookBarcode
        (k := ℚ) (n := 1)
        RankSchanuelUnshiftedExamples.oneCoordinateHook
        oneCoordinateHook_finitelyPresented).negative) := by
  simpa [RectangleStabilityGeometry.stabilityRadius] using
    finitelyPresented_exists_signedHookMultisetMatching
      (k := ℚ) (n := 1) (by norm_num)
      RankSchanuelUnshiftedExamples.oneCoordinateHook
      RankSchanuelUnshiftedExamples.oneCoordinateHook
      oneCoordinateHook_finitelyPresented oneCoordinateHook_finitelyPresented
      oneCoordinateHookMinimalResolution oneCoordinateHookMinimalResolution ε
      (CoordinateInterleaving.refl ε
        RankSchanuelUnshiftedExamples.oneCoordinateHook)

/-- In dimension one, the module-level distance theorem specializes to zero
for a self-comparison of this nonzero finitely presented hook. -/
theorem oneCoordinate_self_signedDistance_zero :
    signedHookBottleneckDissimilarity (k := ℚ)
      (finitelyPresentedSignedHookBarcode (k := ℚ) (n := 1) (by norm_num)
        RankSchanuelUnshiftedExamples.oneCoordinateHook
        oneCoordinateHook_finitelyPresented)
      (finitelyPresentedSignedHookBarcode (k := ℚ) (n := 1) (by norm_num)
        RankSchanuelUnshiftedExamples.oneCoordinateHook
        oneCoordinateHook_finitelyPresented) ≤ 0 := by
  have h := finitelyPresented_moduleSignedHookBottleneckDistance_le
    (k := ℚ) (n := 1) (by norm_num)
    RankSchanuelUnshiftedExamples.oneCoordinateHook
    RankSchanuelUnshiftedExamples.oneCoordinateHook
    oneCoordinateHook_finitelyPresented oneCoordinateHook_finitelyPresented
  simpa [coordinateInterleavingDistance_self] using h

example : ∃ x : RankSchanuelUnshiftedExamples.oneCoordinateHook.obj
    (0 : Fin 1 → ℝ), x ≠ 0 :=
  RankSchanuelUnshiftedExamples.oneCoordinateHook_nonzero_fiber

noncomputable example : HasMultisetMatching (k := ℚ) (n := 1) 0
    ((oneCoordinateHookMinimalResolution.signedHookBarcode
      (k := ℚ) (n := 1)
      RankSchanuelUnshiftedExamples.oneCoordinateHook
      oneCoordinateHook_finitelyPresented).positive +
     (oneCoordinateHookMinimalResolution.signedHookBarcode
      (k := ℚ) (n := 1)
      RankSchanuelUnshiftedExamples.oneCoordinateHook
      oneCoordinateHook_finitelyPresented).negative)
    ((oneCoordinateHookMinimalResolution.signedHookBarcode
      (k := ℚ) (n := 1)
      RankSchanuelUnshiftedExamples.oneCoordinateHook
      oneCoordinateHook_finitelyPresented).positive +
     (oneCoordinateHookMinimalResolution.signedHookBarcode
      (k := ℚ) (n := 1)
      RankSchanuelUnshiftedExamples.oneCoordinateHook
      oneCoordinateHook_finitelyPresented).negative) :=
  oneCoordinate_signedMatching 0

private theorem twoCoordinateHook_finitelyPresented :
    GradedFree.FinitelyPresented (R := ℚ) (P := Fin 2 → ℝ)
      RankSchanuelUnshiftedExamples.twoCoordinateHook :=
  GradedFree.free_finitelyPresented (R := ℚ) (P := Fin 2 → ℝ)
    (HookInfinity.generators (P := Fin 2 → ℝ) (0 : Fin 2 → ℝ))

private noncomputable def twoCoordinateHookMinimalResolution :
    MinimalFiniteRankProjectiveResolution (k := ℚ)
      (M := RankSchanuelUnshiftedExamples.twoCoordinateHook) :=
  Classical.choice
    (FiniteRankProjectiveResolution.finitelyPresented_exists_minimalFiniteRankProjectiveResolution
      (by norm_num) RankSchanuelUnshiftedExamples.twoCoordinateHook
      twoCoordinateHook_finitelyPresented)

/-- The two-coordinate consumer exhibits coefficient nine from the original
finitely presented, nonzero module input. -/
theorem twoCoordinate_signedMatching (ε : ℝ≥0) :
    HasMultisetMatching (k := ℚ) (n := 2) (9 * ε)
      ((twoCoordinateHookMinimalResolution.signedHookBarcode
        (k := ℚ) (n := 2)
        RankSchanuelUnshiftedExamples.twoCoordinateHook
        twoCoordinateHook_finitelyPresented).positive +
       (twoCoordinateHookMinimalResolution.signedHookBarcode
        (k := ℚ) (n := 2)
        RankSchanuelUnshiftedExamples.twoCoordinateHook
        twoCoordinateHook_finitelyPresented).negative)
      ((twoCoordinateHookMinimalResolution.signedHookBarcode
        (k := ℚ) (n := 2)
        RankSchanuelUnshiftedExamples.twoCoordinateHook
        twoCoordinateHook_finitelyPresented).positive +
       (twoCoordinateHookMinimalResolution.signedHookBarcode
        (k := ℚ) (n := 2)
        RankSchanuelUnshiftedExamples.twoCoordinateHook
        twoCoordinateHook_finitelyPresented).negative) := by
  have h := finitelyPresented_exists_signedHookMultisetMatching
      (k := ℚ) (n := 2) (by norm_num)
      RankSchanuelUnshiftedExamples.twoCoordinateHook
      RankSchanuelUnshiftedExamples.twoCoordinateHook
      twoCoordinateHook_finitelyPresented twoCoordinateHook_finitelyPresented
      twoCoordinateHookMinimalResolution twoCoordinateHookMinimalResolution ε
      (CoordinateInterleaving.refl ε
        RankSchanuelUnshiftedExamples.twoCoordinateHook)
  have hcoef : (((2 * 2 - 1 : ℕ) : ℝ≥0) ^ 2) = 9 := by norm_num
  rw [hcoef] at h
  exact h

/-- The two-coordinate self-distance consumer likewise reaches zero. -/
theorem twoCoordinate_self_signedDistance_zero :
    signedHookBottleneckDissimilarity (k := ℚ)
      (finitelyPresentedSignedHookBarcode (k := ℚ) (n := 2) (by norm_num)
        RankSchanuelUnshiftedExamples.twoCoordinateHook
        twoCoordinateHook_finitelyPresented)
      (finitelyPresentedSignedHookBarcode (k := ℚ) (n := 2) (by norm_num)
        RankSchanuelUnshiftedExamples.twoCoordinateHook
        twoCoordinateHook_finitelyPresented) ≤ 0 := by
  have h := finitelyPresented_moduleSignedHookBottleneckDistance_le
    (k := ℚ) (n := 2) (by norm_num)
    RankSchanuelUnshiftedExamples.twoCoordinateHook
    RankSchanuelUnshiftedExamples.twoCoordinateHook
    twoCoordinateHook_finitelyPresented twoCoordinateHook_finitelyPresented
  simpa [coordinateInterleavingDistance_self] using h

example : ∃ x : RankSchanuelUnshiftedExamples.twoCoordinateHook.obj
    (0 : Fin 2 → ℝ), x ≠ 0 :=
  RankSchanuelUnshiftedExamples.twoCoordinateHook_nonzero_fiber

noncomputable example (ε : ℝ≥0) : HasMultisetMatching (k := ℚ) (n := 2)
    (9 * ε)
    ((twoCoordinateHookMinimalResolution.signedHookBarcode
      (k := ℚ) (n := 2)
      RankSchanuelUnshiftedExamples.twoCoordinateHook
      twoCoordinateHook_finitelyPresented).positive +
     (twoCoordinateHookMinimalResolution.signedHookBarcode
      (k := ℚ) (n := 2)
      RankSchanuelUnshiftedExamples.twoCoordinateHook
      twoCoordinateHook_finitelyPresented).negative)
    ((twoCoordinateHookMinimalResolution.signedHookBarcode
      (k := ℚ) (n := 2)
      RankSchanuelUnshiftedExamples.twoCoordinateHook
      twoCoordinateHook_finitelyPresented).positive +
     (twoCoordinateHookMinimalResolution.signedHookBarcode
      (k := ℚ) (n := 2)
      RankSchanuelUnshiftedExamples.twoCoordinateHook
      twoCoordinateHook_finitelyPresented).negative) :=
  twoCoordinate_signedMatching ε

private def finiteDeathPair : HookMatching.FiniteHookTag (n := 1) :=
  ⟨(fun _ : Fin 1 => (0 : ℝ), fun _ : Fin 1 => (2 : ℝ)), by
    rw [Pi.lt_def]
    exact ⟨(by intro i; norm_num), ⟨0, by norm_num⟩⟩⟩

private def finiteDeathTag : RealHookTag (n := 1) := .inl finiteDeathPair

private def principalTag : RealHookTag (n := 1) := .inr (fun _ => (0 : ℝ))

private def finitePositive : SignedHookBarcode 1 := ⟨{finiteDeathTag}, 0⟩

private def finiteNegative : SignedHookBarcode 1 := ⟨0, {finiteDeathTag}⟩

private def repeatedFiniteSource : Fin 2 → RealHookTag (n := 1) :=
  fun _ => finiteDeathTag

private def noFiniteTarget : Fin 0 → RealHookTag (n := 1) := Fin.elim0

/-- Two copies of a finite-death tag on opposite barcode signs remain two
actual left-hand occurrences. Both can be deleted by real radius-one
interleavings at the exact endpoint. -/
theorem repeatedCrossSignFiniteMatching :
    HasMultisetMatching (k := ℚ) (n := 1) 1
      (finitePositive.positive + finiteNegative.negative)
      (finiteNegative.positive + finitePositive.negative) := by
  classical
  have hnot : ¬ HookMatching.finiteSignificant (1 + 1) finiteDeathPair := by
    rintro ⟨i, hi⟩
    fin_cases i
    norm_num [finiteDeathPair] at hi
  let M : OccurrenceMatching (Fin 2) (Fin 0) PEmpty.{1} PEmpty.{1} :=
    ⟨fun _ => none, (by intro i i' j hi; cases hi), Equiv.refl _⟩
  have hM : HookMatching.IsMatching (k := ℚ) 1
      repeatedFiniteSource noFiniteTarget M := by
    refine ⟨?_, ?_, ?_⟩
    · intro i j hij
      simp [M] at hij
    · intro i hi
      exact (HookMatching.finiteInterleaved_zero_iff (k := ℚ)
        finiteDeathPair 1).2 hnot
    · intro j
      exact j.elim0
  apply HasMultisetMatching.intro repeatedFiniteSource noFiniteTarget ?_ ?_ M hM
  · simp [finitePositive, finiteNegative, hookTagMultiset,
      repeatedFiniteSource, finiteDeathTag]
  · simp [finitePositive, finiteNegative, hookTagMultiset]

theorem repeatedCrossSignFinite_leftCount :
    (finitePositive.positive + finiteNegative.negative).count finiteDeathTag = 2 := by
  simp [finitePositive, finiteNegative]

theorem repeatedCrossSignFinite_rightCount :
    (finiteNegative.positive + finitePositive.negative).count finiteDeathTag = 0 := by
  simp [finitePositive, finiteNegative]

theorem repeatedCrossSignFinite_distance_le_one :
    signedHookBottleneckDissimilarity (k := ℚ) finitePositive finiteNegative ≤ 1 := by
  apply hookMultisetBottleneckDistance_le_of_matching
  simpa [signedHookBottleneckDissimilarity] using repeatedCrossSignFiniteMatching

/-- Empty occurrence enumerations give the zero matching for the zero
finite-hook multisets. -/
theorem emptyMultiset_zeroMatching :
    HasMultisetMatching (k := ℚ) (n := 1) 0 0 0 := by
  let F : Fin 0 → RealHookTag (n := 1) := Fin.elim0
  let M : OccurrenceMatching (Fin 0) (Fin 0) PEmpty.{1} PEmpty.{1} :=
    ⟨(fun i => i.elim0), (by intro i; exact i.elim0), Equiv.refl _⟩
  refine HasMultisetMatching.intro F F ?_ ?_ M ?_
  · change hookTagMultiset (fun i : Fin 0 => i.elim0) = 0
    rfl
  · change hookTagMultiset (fun i : Fin 0 => i.elim0) = 0
    rfl
  · exact ⟨by intro i; exact i.elim0,
      by intro i; exact i.elim0,
      by intro i; exact i.elim0⟩

/-- A principal-upset occurrence has its own exact radius-zero self-match. -/
theorem principalOccurrence_zeroMatching :
    HasMultisetMatching (k := ℚ) (n := 1) 0 {principalTag} {principalTag} := by
  let F : Fin 1 → RealHookTag (n := 1) := fun _ => principalTag
  have hI : CoordinateInterleaving 0
      (HookMatching.familyModule (k := ℚ) F)
      (HookMatching.familyModule (k := ℚ) F) :=
    CoordinateInterleaving.refl 0 (HookMatching.familyModule (k := ℚ) F)
  obtain ⟨M, hM⟩ := HookMatching.exists_matching_of_zero_interleaving
    (k := ℚ) F F hI
  exact HasMultisetMatching.intro F F (by simp [F, hookTagMultiset])
    (by simp [F, hookTagMultiset]) M hM

end TDA.Persistence.RankSignedStabilityExamples
