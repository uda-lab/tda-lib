import TDA.Filtration.SparseRips.NaturalEquivalence
import TDA.Persistence.CechRipsInterleaving
import TDA.Persistence.RealInterleavingLaws

/-!
# Multiplicative sparse Rips approximation on logarithmic scales

The relaxed complex lies between the diameter-scale Rips complexes at
`(1−2η)r` and `r`. Reindexing by `exp` turns the factor
`c = (1−2η)⁻¹` into a shift by `log c`.
-/

namespace TDA.Filtration.SparseRips

open TDA.Simplicial TDA.Persistence CategoryTheory TDA.Filtration
open scoped NNReal ENNReal

noncomputable section

variable {V : Type*} [MetricSpace V] [Fintype V] [LinearOrder V]

/-- Multiplicative approximation factor for the internal sparsification parameter. -/
def approximationFactor (η : ℝ) : ℝ := (1 - 2 * η)⁻¹

theorem approximationFactor_mul {η : ℝ} (hη : 0 < η) (hη' : η ≤ 1 / 3) :
    (1 - 2 * η) * approximationFactor η = 1 := by
  have hden : 1 - 2 * η ≠ 0 := by linarith
  simp [approximationFactor, hden]

theorem one_le_approximationFactor {η : ℝ} (hη : 0 < η) (hη' : η ≤ 1 / 3) :
    1 ≤ approximationFactor η := by
  have hden : 0 < 1 - 2 * η := by linarith
  have hmul := approximationFactor_mul hη hη'
  have hfac : 0 < approximationFactor η := by
    exact inv_pos.mpr hden
  nlinarith

@[simp] theorem approximationFactor_one_third : approximationFactor (1 / 3) = 3 := by
  norm_num [approximationFactor]

/-- Internal sparsification parameter realizing an advertised tolerance. -/
def parameterOfTolerance (τ : ℝ) : ℝ := τ / (2 * (1 + τ))

theorem parameterOfTolerance_pos {τ : ℝ} (hτ : 0 < τ) :
    0 < parameterOfTolerance τ := by
  unfold parameterOfTolerance
  exact div_pos hτ (by positivity)

theorem parameterOfTolerance_le_third {τ : ℝ} (hτ : 0 < τ) (hτ' : τ ≤ 1) :
    parameterOfTolerance τ ≤ 1 / 3 := by
  unfold parameterOfTolerance
  apply (div_le_iff₀ (by positivity : 0 < 2 * (1 + τ))).mpr
  nlinarith

theorem approximationFactor_parameterOfTolerance {τ : ℝ} (hτ : 0 < τ) :
    approximationFactor (parameterOfTolerance τ) = 1 + τ := by
  have hden : 0 < 2 * (1 + τ) := by positivity
  unfold approximationFactor parameterOfTolerance
  field_simp
  ring

/-- Relaxed Rips lies in ordinary Rips at the same positive radius. -/
theorem relaxed_le_rips_log (seed : V) {η : ℝ} (hη : 0 < η)
    (hη' : η ≤ 1 / 3) (t : ℝ) :
    relaxedComplex η (deletionTime seed η) (Real.exp t) ≤
      (Rips.filter inferInstance).sublevel
        (Real.exp (t + logParam (approximationFactor η))) := by
  have hc := one_le_approximationFactor hη hη'
  rw [exp_add_logParam hc]
  exact (relaxedComplex_le_rips hη.le (deletionTime seed η)).trans
    ((Rips.filter inferInstance).sublevel_mono
      (by have hfac : 1 ≤ approximationFactor η := hc
          nlinarith [Real.exp_pos t]))

/-- Ordinary Rips at `exp t` lies in relaxed Rips at `c exp t`. -/
theorem rips_le_relaxed_log (seed : V) {η : ℝ} (hη : 0 < η)
    (hη' : η ≤ 1 / 3) (t : ℝ) :
    (Rips.filter inferInstance).sublevel (Real.exp t) ≤
      relaxedComplex η (deletionTime seed η)
        (Real.exp (t + logParam (approximationFactor η))) := by
  have hc := one_le_approximationFactor hη hη'
  rw [exp_add_logParam hc]
  have heq : (1 - 2 * η) * (approximationFactor η * Real.exp t) = Real.exp t := by
    rw [← mul_assoc, approximationFactor_mul hη hη', one_mul]
  have hr : 0 ≤ approximationFactor η * Real.exp t :=
    mul_nonneg (le_trans zero_le_one hc) (Real.exp_pos t).le
  simpa only [heq] using
    (rips_le_relaxedComplex hη.le (by linarith) hr (deletionTime seed η))

/-- The relaxed and ordinary Rips log-scale modules have an explicit
`log c`-interleaving induced by the two complex inclusions. -/
def relaxedRipsLogInterleaving (R : Type*) [Ring R] (seed : V) {η : ℝ}
    (hη : 0 < η) (hη' : η ≤ 1 / 3) (n : ℕ) :
    RealInterleaving (logParam (approximationFactor η))
      (simplicialHomologyPModule R
        (Filtration.reindex expHom (relaxedFiltration seed hη hη')) n)
      (simplicialHomologyPModule R
        (Filtration.reindex expHom (Rips.filter (V := V) inferInstance).sublevelFiltration) n) :=
  inclusionInterleaving R n
    (relaxed_le_rips_log seed hη hη')
    (rips_le_relaxed_log seed hη hη')

/-- Reindex the natural sparse/relaxed equivalence along the exponential. -/
def sparseRelaxedLogIso (R : Type*) [Ring R] (seed : V) {η : ℝ}
    (hη : 0 < η) (hη' : η ≤ 1 / 3) (n : ℕ) :
    simplicialHomologyPModule R (Filtration.reindex expHom (sparseFiltration seed η)) n ≅
      simplicialHomologyPModule R
        (Filtration.reindex expHom (relaxedFiltration seed hη hη')) n := by
  let e := sparseRelaxedHomologyIso R seed hη hη' n
  letI : IsIso e.hom := Iso.isIso_hom e
  let f : simplicialHomologyPModule R
      (Filtration.reindex expHom (sparseFiltration seed η)) n ⟶
      simplicialHomologyPModule R
        (Filtration.reindex expHom (relaxedFiltration seed hη hη')) n :=
    reindexNatTrans expHom e.hom
  haveI : IsIso f := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro t
    change IsIso (e.hom.app (Real.exp t))
    exact ((NatTrans.isIso_iff_isIso_app e.hom).mp (Iso.isIso_hom e)) (Real.exp t)
  exact asIso f

/-- Sparse Rips homology and diameter-scale Rips homology are interleaved after
logarithmic reindexing, in every degree including zero. -/
def sparseRipsLogInterleaving (R : Type*) [Ring R] (seed : V) {η : ℝ}
    (hη : 0 < η) (hη' : η ≤ 1 / 3) (n : ℕ) :
    RealInterleaving (logParam (approximationFactor η))
      (simplicialHomologyPModule R
        (Filtration.reindex expHom (sparseFiltration seed η)) n)
      (simplicialHomologyPModule R
        (Filtration.reindex expHom (Rips.filter (V := V) inferInstance).sublevelFiltration) n) :=
  (relaxedRipsLogInterleaving R seed hη hη' n).congr
    (sparseRelaxedLogIso R seed hη hη' n).symm (Iso.refl _)

theorem sparseRipsLogDistance_le (R : Type*) [Ring R] (seed : V) {η : ℝ}
    (hη : 0 < η) (hη' : η ≤ 1 / 3) (n : ℕ) :
    realInterleavingDistance
      (simplicialHomologyPModule R
        (Filtration.reindex expHom (sparseFiltration seed η)) n)
      (simplicialHomologyPModule R
        (Filtration.reindex expHom (Rips.filter (V := V) inferInstance).sublevelFiltration) n) ≤
      ENNReal.ofReal (Real.log (approximationFactor η)) :=
  (sparseRipsLogInterleaving R seed hη hη' n).distance_le

end

end TDA.Filtration.SparseRips
