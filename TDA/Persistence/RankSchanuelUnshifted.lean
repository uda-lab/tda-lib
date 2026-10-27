import TDA.Persistence.CoordinateInterleavingDelay
import TDA.Persistence.RankSchanuelResolution
import TDA.Persistence.FiniteRankProjectiveResolutionDimension
import TDA.Persistence.CoordinateInterleavingDistance
import TDA.Persistence.RectangleStabilityGeometry

/-!
# Unshifted Schanuel interleavings

The persistent Schanuel comparison uses degree-dependent shifts. For modules
with an original finite presentation, the degree bound makes all terms beyond
`2*n-2` vanish. An asymmetric comparison removes those shifts at the resulting
radius `(2*n-1)*ε`, independently of the stored resolution lengths.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence

open CategoryTheory CoordinateShift
open CategoryTheory.Limits
open scoped ZeroObject
open scoped TDA.Persistence NNReal ENNReal

variable {k : Type u} [Field k] {n : ℕ}

private instance : HasFiniteBiproducts (PModule.{u,0,u} k (Fin n → ℝ)) :=
  HasFiniteBiproducts.of_hasFiniteProducts

/-- The zero-padded term convention for a certified minimal resolution agrees
with the existing finite-resolution term convention. -/
@[simp] theorem MinimalFiniteRankProjectiveResolution.termAt_eq_resolution_termAt
    {M : PModule.{u,0,u} k (Fin n → ℝ)}
    (R : MinimalFiniteRankProjectiveResolution (k := k) (M := M)) (j : ℕ) :
    R.termAt j = R.resolution.termAt j := by
  simp [MinimalFiniteRankProjectiveResolution.termAt,
    FiniteRankProjectiveResolution.termAt]

/-- Unshifted alternating degree-`j` term on the left side of the Schanuel
comparison. -/
noncomputable def unshiftedSchanuelLeftSummand
    {M N : PModule.{u,0,u} k (Fin n → ℝ)}
    (R : FiniteRankProjectiveResolution M) (S : FiniteRankProjectiveResolution N)
    (j : Fin (max R.length S.length)) : PModule.{u,0,u} k (Fin n → ℝ) :=
  if Even j.val then R.termAt j.val else S.termAt j.val

/-- Unshifted alternating degree-`j` term with the resolutions exchanged. -/
noncomputable def unshiftedSchanuelRightSummand
    {M N : PModule.{u,0,u} k (Fin n → ℝ)}
    (R : FiniteRankProjectiveResolution M) (S : FiniteRankProjectiveResolution N)
    (j : Fin (max R.length S.length)) : PModule.{u,0,u} k (Fin n → ℝ) :=
  if Even j.val then S.termAt j.val else R.termAt j.val

/-- Actual finite biproduct of the unshifted alternating resolution terms. -/
noncomputable def unshiftedSchanuelLeftBiproduct
    {M N : PModule.{u,0,u} k (Fin n → ℝ)}
    (R : FiniteRankProjectiveResolution M) (S : FiniteRankProjectiveResolution N) :
    PModule.{u,0,u} k (Fin n → ℝ) :=
  ⨁ unshiftedSchanuelLeftSummand R S

/-- Actual finite biproduct of the unshifted alternating terms with the
resolutions exchanged. -/
noncomputable def unshiftedSchanuelRightBiproduct
    {M N : PModule.{u,0,u} k (Fin n → ℝ)}
    (R : FiniteRankProjectiveResolution M) (S : FiniteRankProjectiveResolution N) :
    PModule.{u,0,u} k (Fin n → ℝ) :=
  ⨁ unshiftedSchanuelRightSummand R S

/-- Above the finite-presentation dimension bound, every unshifted alternating
summand is zero for any supplied minimal resolutions. -/
theorem finitelyPresented_unshiftedSchanuelLeftSummand_isZero
    (hn : 1 ≤ n) {M N : PModule.{u,0,u} k (Fin n → ℝ)}
    (hM : GradedFree.FinitelyPresented.{u,0,0} (R := k) (P := Fin n → ℝ) M)
    (hN : GradedFree.FinitelyPresented.{u,0,0} (R := k) (P := Fin n → ℝ) N)
    (R : MinimalFiniteRankProjectiveResolution (k := k) (M := M))
    (S : MinimalFiniteRankProjectiveResolution (k := k) (M := N))
    {j : Fin (max R.resolution.length S.resolution.length)}
    (hj : 2 * n - 2 < j.val) :
    IsZero (unshiftedSchanuelLeftSummand R.resolution S.resolution j) := by
  by_cases he : Even j.val
  · simpa [unshiftedSchanuelLeftSummand, he] using
      (FiniteRankProjectiveResolution.finitelyPresented_minimalFiniteRankProjectiveResolution_termAt_isZero
        hn M hM R j.val hj)
  · simpa [unshiftedSchanuelLeftSummand, he] using
      (FiniteRankProjectiveResolution.finitelyPresented_minimalFiniteRankProjectiveResolution_termAt_isZero
        hn N hN S j.val hj)

/-- Above the finite-presentation dimension bound, every unshifted alternating
summand on the exchanged side is zero for any supplied minimal resolutions. -/
theorem finitelyPresented_unshiftedSchanuelRightSummand_isZero
    (hn : 1 ≤ n) {M N : PModule.{u,0,u} k (Fin n → ℝ)}
    (hM : GradedFree.FinitelyPresented.{u,0,0} (R := k) (P := Fin n → ℝ) M)
    (hN : GradedFree.FinitelyPresented.{u,0,0} (R := k) (P := Fin n → ℝ) N)
    (R : MinimalFiniteRankProjectiveResolution (k := k) (M := M))
    (S : MinimalFiniteRankProjectiveResolution (k := k) (M := N))
    {j : Fin (max R.resolution.length S.resolution.length)}
    (hj : 2 * n - 2 < j.val) :
    IsZero (unshiftedSchanuelRightSummand R.resolution S.resolution j) := by
  by_cases he : Even j.val
  · simpa [unshiftedSchanuelRightSummand, he] using
      (FiniteRankProjectiveResolution.finitelyPresented_minimalFiniteRankProjectiveResolution_termAt_isZero
        hn N hN S j.val hj)
  · simpa [unshiftedSchanuelRightSummand, he] using
      (FiniteRankProjectiveResolution.finitelyPresented_minimalFiniteRankProjectiveResolution_termAt_isZero
        hn M hM R j.val hj)

private noncomputable def unshiftedSchanuelLeftDelayComparison
    {M N : PModule.{u,0,u} k (Fin n → ℝ)}
    (R : MinimalFiniteRankProjectiveResolution (k := k) (M := M))
    (S : MinimalFiniteRankProjectiveResolution (k := k) (M := N))
    (ε δ : ℝ≥0) (hbound : ((2 * n - 2 : ℕ) : ℝ≥0) * ε ≤ δ)
    (hδ : ∀ j, 2 * n - 2 < j →
      IsZero (R.resolution.termAt j) ∧ IsZero (S.resolution.termAt j)) :
    CoordinateInterleavingDelayComparison δ
      (unshiftedSchanuelLeftBiproduct R.resolution S.resolution)
      (FiniteRankProjectiveResolution.schanuelLeftBiproduct
        R.resolution S.resolution ε) := by
  let X : Fin (max R.resolution.length S.resolution.length) →
      PModule.{u,0,u} k (Fin n → ℝ) := unshiftedSchanuelLeftSummand
        R.resolution S.resolution
  let t : Fin (max R.resolution.length S.resolution.length) → ℝ≥0 :=
    fun j => (j.val : ℝ≥0) * ε
  have hdelay (j : Fin (max R.resolution.length S.resolution.length)) :
      t j ≤ δ ∨ IsZero (X j) := by
    by_cases hj : j.val ≤ 2 * n - 2
    · left
      dsimp [t]
      exact (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hj) (by positivity)).trans hbound
    · right
      have hj' : 2 * n - 2 < j.val := Nat.lt_of_not_ge hj
      by_cases he : Even j.val
      · simpa [X, unshiftedSchanuelLeftSummand, he] using (hδ j.val hj').1
      · simpa [X, unshiftedSchanuelLeftSummand, he] using (hδ j.val hj').2
  let C := finiteFamilyDelayComparison δ X t hdelay
  refine C

private noncomputable def unshiftedSchanuelRightDelayComparison
    {M N : PModule.{u,0,u} k (Fin n → ℝ)}
    (R : MinimalFiniteRankProjectiveResolution (k := k) (M := M))
    (S : MinimalFiniteRankProjectiveResolution (k := k) (M := N))
    (ε δ : ℝ≥0) (hbound : ((2 * n - 2 : ℕ) : ℝ≥0) * ε ≤ δ)
    (hδ : ∀ j, 2 * n - 2 < j →
      IsZero (R.resolution.termAt j) ∧ IsZero (S.resolution.termAt j)) :
    CoordinateInterleavingDelayComparison δ
      (unshiftedSchanuelRightBiproduct R.resolution S.resolution)
      (FiniteRankProjectiveResolution.schanuelRightBiproduct
        R.resolution S.resolution ε) := by
  let X : Fin (max R.resolution.length S.resolution.length) →
      PModule.{u,0,u} k (Fin n → ℝ) := unshiftedSchanuelRightSummand
        R.resolution S.resolution
  let t : Fin (max R.resolution.length S.resolution.length) → ℝ≥0 :=
    fun j => (j.val : ℝ≥0) * ε
  have hdelay (j : Fin (max R.resolution.length S.resolution.length)) :
      t j ≤ δ ∨ IsZero (X j) := by
    by_cases hj : j.val ≤ 2 * n - 2
    · left
      dsimp [t]
      exact (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hj) (by positivity)).trans hbound
    · right
      have hj' : 2 * n - 2 < j.val := Nat.lt_of_not_ge hj
      by_cases he : Even j.val
      · simpa [X, unshiftedSchanuelRightSummand, he] using (hδ j.val hj').2
      · simpa [X, unshiftedSchanuelRightSummand, he] using (hδ j.val hj').1
  let C := finiteFamilyDelayComparison δ X t hdelay
  refine C

private theorem unshifted_delay_radius (hn : 1 ≤ n) (ε : ℝ≥0) :
    ε + ((2 * n - 2 : ℕ) : ℝ≥0) * ε =
      RectangleStabilityGeometry.stabilityRadius n ε := by
  rw [RectangleStabilityGeometry.stabilityRadius]
  calc
    ε + ((2 * n - 2 : ℕ) : ℝ≥0) * ε =
        (1 + ((2 * n - 2 : ℕ) : ℝ≥0)) * ε := by
          calc
            ε + ((2 * n - 2 : ℕ) : ℝ≥0) * ε =
                1 * ε + ((2 * n - 2 : ℕ) : ℝ≥0) * ε := by simp
            _ = (1 + ((2 * n - 2 : ℕ) : ℝ≥0)) * ε := by rw [add_mul]
    _ = ((2 * n - 1 : ℕ) : ℝ≥0) * ε := by
      congr 2
      exact_mod_cast (show 1 + (2 * n - 2) = 2 * n - 1 by omega)

/-- For any supplied certified minimal resolutions of originally finitely
presented modules, the actual unshifted alternating sums admit an interleaving
at radius `(2*n-1)*ε`. -/
noncomputable def finitelyPresented_unshiftedSchanuel_interleaving
    (hn : 1 ≤ n) (M N : PModule.{u,0,u} k (Fin n → ℝ))
    (hM : GradedFree.FinitelyPresented.{u,0,0} (R := k) (P := Fin n → ℝ) M)
    (hN : GradedFree.FinitelyPresented.{u,0,0} (R := k) (P := Fin n → ℝ) N)
    (R : MinimalFiniteRankProjectiveResolution (k := k) (M := M))
    (S : MinimalFiniteRankProjectiveResolution (k := k) (M := N))
    (ε : ℝ≥0) (i : CoordinateInterleaving ε M N) :
    CoordinateInterleaving (RectangleStabilityGeometry.stabilityRadius n ε)
      (unshiftedSchanuelLeftBiproduct R.resolution S.resolution)
      (unshiftedSchanuelRightBiproduct R.resolution S.resolution) := by
  let δ : ℝ≥0 := ((2 * n - 2 : ℕ) : ℝ≥0) * ε
  have hR :=
    FiniteRankProjectiveResolution.finitelyPresented_minimalFiniteRankProjectiveResolution_termAt_isZero
      hn M hM R
  have hS :=
    FiniteRankProjectiveResolution.finitelyPresented_minimalFiniteRankProjectiveResolution_termAt_isZero
      hn N hN S
  have hδ (j : ℕ) (hj : 2 * n - 2 < j) :
      IsZero (R.resolution.termAt j) ∧ IsZero (S.resolution.termAt j) := by
    simpa using ⟨hR j hj, hS j hj⟩
  let cA := unshiftedSchanuelLeftDelayComparison R S ε δ (by rfl) hδ
  let cB := unshiftedSchanuelRightDelayComparison R S ε δ (by rfl) hδ
  have iShift :=
    schanuelInterleavingOfResolutions R.resolution S.resolution ε i
  have iUnshifted := cA.transport cB iShift
  have hrad : ε + δ = RectangleStabilityGeometry.stabilityRadius n ε := by
    simpa [δ] using unshifted_delay_radius hn ε
  rw [← hrad]
  exact iUnshifted

/-- The original finite-presentation hypotheses also provide minimal
resolutions, so an unshifted Schanuel interleaving exists without choosing
resolution certificates as input. -/
theorem finitelyPresented_exists_unshiftedSchanuel_interleaving
    (hn : 1 ≤ n) (M N : PModule.{u,0,u} k (Fin n → ℝ))
    (hM : GradedFree.FinitelyPresented.{u,0,0} (R := k) (P := Fin n → ℝ) M)
    (hN : GradedFree.FinitelyPresented.{u,0,0} (R := k) (P := Fin n → ℝ) N)
    (ε : ℝ≥0) (i : CoordinateInterleaving ε M N) :
    ∃ R : MinimalFiniteRankProjectiveResolution (k := k) (M := M),
      ∃ S : MinimalFiniteRankProjectiveResolution (k := k) (M := N),
        Nonempty (CoordinateInterleaving (RectangleStabilityGeometry.stabilityRadius n ε)
          (unshiftedSchanuelLeftBiproduct R.resolution S.resolution)
          (unshiftedSchanuelRightBiproduct R.resolution S.resolution)) := by
  obtain ⟨R⟩ := FiniteRankProjectiveResolution.finitelyPresented_exists_minimalFiniteRankProjectiveResolution
    hn M hM
  obtain ⟨S⟩ := FiniteRankProjectiveResolution.finitelyPresented_exists_minimalFiniteRankProjectiveResolution
    hn N hN
  exact ⟨R, S, ⟨finitelyPresented_unshiftedSchanuel_interleaving
    hn M N hM hN R S ε i⟩⟩

/-- The fixed-resolution unshifted parity distance is bounded by the same
coefficient times the original extended interleaving distance. The proof uses
the actual witness construction and commutes finite positive multiplication
through both infima, including empty witness fibers. -/
theorem finitelyPresented_unshiftedSchanuel_distance_le
    (hn : 1 ≤ n) (M N : PModule.{u,0,u} k (Fin n → ℝ))
    (hM : GradedFree.FinitelyPresented.{u,0,0} (R := k) (P := Fin n → ℝ) M)
    (hN : GradedFree.FinitelyPresented.{u,0,0} (R := k) (P := Fin n → ℝ) N)
    (R : MinimalFiniteRankProjectiveResolution (k := k) (M := M))
    (S : MinimalFiniteRankProjectiveResolution (k := k) (M := N)) :
    coordinateInterleavingDistance
        (unshiftedSchanuelLeftBiproduct R.resolution S.resolution)
        (unshiftedSchanuelRightBiproduct R.resolution S.resolution) ≤
      ((2 * n - 1 : ℕ) : ℝ≥0∞) * coordinateInterleavingDistance M N := by
  have hc : 2 * n - 1 ≠ 0 := by omega
  have hc0 : (((2 * n - 1 : ℕ) : ℝ≥0∞)) ≠ 0 := by exact_mod_cast hc
  have hct : (((2 * n - 1 : ℕ) : ℝ≥0∞)) ≠ ⊤ := ENNReal.coe_ne_top
  change coordinateInterleavingDistance
      (unshiftedSchanuelLeftBiproduct R.resolution S.resolution)
      (unshiftedSchanuelRightBiproduct R.resolution S.resolution) ≤
    ((2 * n - 1 : ℕ) : ℝ≥0∞) *
      (⨅ ε : ℝ≥0, ⨅ (_ : Nonempty (CoordinateInterleaving ε M N)),
        (ε : ℝ≥0∞))
  rw [ENNReal.mul_iInf_of_ne hc0 hct]
  apply le_iInf
  intro ε
  rw [ENNReal.mul_iInf_of_ne hc0 hct]
  apply le_iInf
  intro hI
  obtain ⟨i⟩ := hI
  simpa [RectangleStabilityGeometry.stabilityRadius, ENNReal.coe_mul] using
    (finitelyPresented_unshiftedSchanuel_interleaving hn M N hM hN R S ε i).distance_le

end TDA.Persistence
