import TDA.Persistence.FiniteSimplicialInterleaving
import TDA.Persistence.FiniteSimplicialPresentation
import TDA.Persistence.RankErosionCertificate
import TDA.Persistence.ERankErosion

/-!
# Rank erosion of finite graded simplicial homology

Coordinatewise grade errors of two gradings of one finite simplicial complex induce an actual
interleaving of their simplicial homology modules (`finiteSimplicialHomology_interleaving`).
Finite input makes every fiber finite-dimensional, so the interleaving gives weak-pair rank
erosion at the grade error, and both the `ℕ`-valued and the extended erosion distances are at
most the grade error, in particular at most `FiniteGraded.supGradeError`.

The homology modules are finitely presented (`finiteSimplicialHomology_finitelyPresented`).
A failed erosion test at a radius is therefore a strict lower bound of the erosion distance,
which is at most the interleaving distance and the maximal grade error. Hence every
grade-error bound, and the maximal grade error, is strictly above a radius at which erosion
fails.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence

open CategoryTheory TDA.Simplicial TDA.Filtration
open scoped TDA.Persistence NNReal ENNReal

variable {m n : ℕ} {C : FiniteComplex m}
variable (k : Type u) [Field k]

/-- Coordinatewise grade errors give weak-pair rank erosion of the actual simplicial homology
modules, for every degree and coefficient field. -/
theorem finiteSimplicialHomology_rankErosion
    (g h : FiniteGraded C n) (q : ℕ) {δ : ℝ≥0}
    (herror : ∀ s i, |g.grade s i - h.grade s i| ≤ (δ : ℝ)) :
    RankErosion δ (finiteSimplicialHomology k g q) (finiteSimplicialHomology k h q) :=
  (finiteSimplicialHomology_interleaving k g h q herror).rankErosion

/-- The maximal grade error is an admissible erosion radius. -/
theorem finiteSimplicialHomology_rankErosion_supGradeError
    (g h : FiniteGraded C n) (q : ℕ) :
    RankErosion (g.supGradeError h) (finiteSimplicialHomology k g q)
      (finiteSimplicialHomology k h q) :=
  finiteSimplicialHomology_rankErosion k g h q (g.abs_grade_sub_le_supGradeError h)

/-- The weak-pair rank erosion distance is bounded by any coordinatewise grade error. -/
theorem rankErosionDistance_finiteSimplicialHomology_le
    (g h : FiniteGraded C n) (q : ℕ) {δ : ℝ≥0}
    (herror : ∀ s i, |g.grade s i - h.grade s i| ≤ (δ : ℝ)) :
    rankErosionDistance (finiteSimplicialHomology k g q)
      (finiteSimplicialHomology k h q) ≤ δ :=
  rankErosionDistance_le_of_erosion (finiteSimplicialHomology_rankErosion k g h q herror)

/-- The weak-pair rank erosion distance is bounded by the maximal grade error. -/
theorem rankErosionDistance_finiteSimplicialHomology_le_supGradeError
    (g h : FiniteGraded C n) (q : ℕ) :
    rankErosionDistance (finiteSimplicialHomology k g q)
      (finiteSimplicialHomology k h q) ≤ g.supGradeError h :=
  rankErosionDistance_le_of_erosion (finiteSimplicialHomology_rankErosion_supGradeError k g h q)

/-- Coordinatewise grade errors give extended-rank erosion of the actual simplicial homology
modules. -/
theorem finiteSimplicialHomology_eRankErosion
    (g h : FiniteGraded C n) (q : ℕ) {δ : ℝ≥0}
    (herror : ∀ s i, |g.grade s i - h.grade s i| ≤ (δ : ℝ)) :
    ERankErosion δ (finiteSimplicialHomology k g q) (finiteSimplicialHomology k h q) :=
  (finiteSimplicialHomology_interleaving k g h q herror).eRankErosion

/-- The maximal grade error is an admissible extended-rank erosion radius. -/
theorem finiteSimplicialHomology_eRankErosion_supGradeError
    (g h : FiniteGraded C n) (q : ℕ) :
    ERankErosion (g.supGradeError h) (finiteSimplicialHomology k g q)
      (finiteSimplicialHomology k h q) :=
  finiteSimplicialHomology_eRankErosion k g h q (g.abs_grade_sub_le_supGradeError h)

/-- The extended-rank erosion distance is bounded by any coordinatewise grade error. -/
theorem eRankErosionDistance_finiteSimplicialHomology_le
    (g h : FiniteGraded C n) (q : ℕ) {δ : ℝ≥0}
    (herror : ∀ s i, |g.grade s i - h.grade s i| ≤ (δ : ℝ)) :
    eRankErosionDistance (finiteSimplicialHomology k g q)
      (finiteSimplicialHomology k h q) ≤ δ :=
  eRankErosionDistance_le_of_erosion (finiteSimplicialHomology_eRankErosion k g h q herror)

/-- The extended-rank erosion distance is bounded by the maximal grade error. -/
theorem eRankErosionDistance_finiteSimplicialHomology_le_supGradeError
    (g h : FiniteGraded C n) (q : ℕ) :
    eRankErosionDistance (finiteSimplicialHomology k g q)
      (finiteSimplicialHomology k h q) ≤ g.supGradeError h :=
  eRankErosionDistance_le_of_erosion
    (finiteSimplicialHomology_eRankErosion_supGradeError k g h q)

/-- On finite graded simplicial homology the extended and `ℕ`-valued erosion distances
agree. -/
theorem eRankErosionDistance_finiteSimplicialHomology_eq_rankErosionDistance
    (g h : FiniteGraded C n) (q : ℕ) :
    eRankErosionDistance (finiteSimplicialHomology k g q) (finiteSimplicialHomology k h q) =
      rankErosionDistance (finiteSimplicialHomology k g q) (finiteSimplicialHomology k h q) :=
  eRankErosionDistance_eq_rankErosionDistance

/-- The certificate of a failed erosion test for finite graded simplicial homology: the radius
is strictly below the erosion distance, which is at most the interleaving distance, which is
at most the maximal grade error. -/
theorem finiteSimplicialHomology_rankErosion_failure_certificate
    (g h : FiniteGraded C n) (q : ℕ) {ε : ℝ≥0}
    (hfail : ¬ RankErosion ε (finiteSimplicialHomology k g q)
      (finiteSimplicialHomology k h q)) :
    (ε : ℝ≥0∞) < rankErosionDistance (finiteSimplicialHomology k g q)
        (finiteSimplicialHomology k h q) ∧
      rankErosionDistance (finiteSimplicialHomology k g q)
          (finiteSimplicialHomology k h q) ≤
        coordinateInterleavingDistance (finiteSimplicialHomology k g q)
          (finiteSimplicialHomology k h q) ∧
      coordinateInterleavingDistance (finiteSimplicialHomology k g q)
          (finiteSimplicialHomology k h q) ≤ g.supGradeError h :=
  ⟨(GradedFree.finitelyPresented_rankErosion_failure_certificate
      (finiteSimplicialHomology_finitelyPresented k g q)
      (finiteSimplicialHomology_finitelyPresented k h q) hfail).1,
    (GradedFree.finitelyPresented_rankErosion_failure_certificate
      (finiteSimplicialHomology_finitelyPresented k g q)
      (finiteSimplicialHomology_finitelyPresented k h q) hfail).2,
    coordinateInterleavingDistance_finiteSimplicialHomology_le_supGradeError k g h q⟩

/-- A failed erosion test at a radius forces every coordinatewise grade error bound above
that radius. -/
theorem lt_of_not_rankErosion_finiteSimplicialHomology
    (g h : FiniteGraded C n) (q : ℕ) {ε δ : ℝ≥0}
    (herror : ∀ s i, |g.grade s i - h.grade s i| ≤ (δ : ℝ))
    (hfail : ¬ RankErosion ε (finiteSimplicialHomology k g q)
      (finiteSimplicialHomology k h q)) : ε < δ := by
  have hlt := (finiteSimplicialHomology_rankErosion_failure_certificate k g h q hfail).1.trans_le
    (rankErosionDistance_finiteSimplicialHomology_le k g h q herror)
  exact_mod_cast hlt

/-- A failed erosion test at a radius forces the maximal grade error above that radius. -/
theorem lt_supGradeError_of_not_rankErosion_finiteSimplicialHomology
    (g h : FiniteGraded C n) (q : ℕ) {ε : ℝ≥0}
    (hfail : ¬ RankErosion ε (finiteSimplicialHomology k g q)
      (finiteSimplicialHomology k h q)) : ε < g.supGradeError h :=
  lt_of_not_rankErosion_finiteSimplicialHomology k g h q
    (g.abs_grade_sub_le_supGradeError h) hfail

/-- The certificate of a failed extended-rank erosion test for finite graded simplicial
homology: the radius is strictly below the extended erosion distance, which is at most the
interleaving distance, which is at most the maximal grade error. -/
theorem finiteSimplicialHomology_eRankErosion_failure_certificate
    (g h : FiniteGraded C n) (q : ℕ) {ε : ℝ≥0}
    (hfail : ¬ ERankErosion ε (finiteSimplicialHomology k g q)
      (finiteSimplicialHomology k h q)) :
    (ε : ℝ≥0∞) < eRankErosionDistance (finiteSimplicialHomology k g q)
        (finiteSimplicialHomology k h q) ∧
      eRankErosionDistance (finiteSimplicialHomology k g q)
          (finiteSimplicialHomology k h q) ≤
        coordinateInterleavingDistance (finiteSimplicialHomology k g q)
          (finiteSimplicialHomology k h q) ∧
      coordinateInterleavingDistance (finiteSimplicialHomology k g q)
          (finiteSimplicialHomology k h q) ≤ g.supGradeError h := by
  rw [eRankErosionDistance_finiteSimplicialHomology_eq_rankErosionDistance]
  exact finiteSimplicialHomology_rankErosion_failure_certificate k g h q
    (fun hr => hfail (eRankErosion_iff_rankErosion.mpr hr))

/-- A failed extended-rank erosion test at a radius forces every coordinatewise grade error
bound above that radius. -/
theorem lt_of_not_eRankErosion_finiteSimplicialHomology
    (g h : FiniteGraded C n) (q : ℕ) {ε δ : ℝ≥0}
    (herror : ∀ s i, |g.grade s i - h.grade s i| ≤ (δ : ℝ))
    (hfail : ¬ ERankErosion ε (finiteSimplicialHomology k g q)
      (finiteSimplicialHomology k h q)) : ε < δ :=
  lt_of_not_rankErosion_finiteSimplicialHomology k g h q herror
    (fun hr => hfail (eRankErosion_iff_rankErosion.mpr hr))

/-- A failed extended-rank erosion test at a radius forces the maximal grade error above that
radius. -/
theorem lt_supGradeError_of_not_eRankErosion_finiteSimplicialHomology
    (g h : FiniteGraded C n) (q : ℕ) {ε : ℝ≥0}
    (hfail : ¬ ERankErosion ε (finiteSimplicialHomology k g q)
      (finiteSimplicialHomology k h q)) : ε < g.supGradeError h :=
  lt_supGradeError_of_not_rankErosion_finiteSimplicialHomology k g h q
    (fun hr => hfail (eRankErosion_iff_rankErosion.mpr hr))

end TDA.Persistence
