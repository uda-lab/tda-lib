import TDA.Persistence.FiniteSimplicialPresentation
import TDA.Persistence.FiniteSimplicialInterleaving
import TDA.Persistence.RankSignedStability

/-!
# Signed hook stability from finite simplicial input

Face-monotone grades on a finite support-aware complex determine actual
inclusion-induced simplicial homology modules. Their finite presentations and
the interleaving induced by a uniform coordinate grade error are derived here
from the input, before applying the canonical signed hook stability theorem.
The signed bottleneck quantity is a dissimilarity.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence

open scoped TDA.Persistence NNReal ENNReal

variable (k : Type u) [Field k] {m n : ℕ} {C : Simplicial.FiniteComplex m}

/-- The canonical signed hook barcode of finite simplicial homology. Its
finite-presentation witness is derived from the finite complex and grades. -/
noncomputable def finiteSimplicialSignedHookBarcode
    (hn : 1 ≤ n) (g : Filtration.FiniteGraded C n) (q : ℕ) :
    SignedHookBarcode n :=
  finitelyPresentedSignedHookBarcode hn (finiteSimplicialHomology k g q)
    (finiteSimplicialHomology_finitelyPresented k g q)

/-- Uniform coordinate error on all faces bounds canonical signed hook
bottleneck dissimilarity by `(2*n-1)^2 * δ`. Neither finite presentation nor an
interleaving is supplied by the caller. Repeated grades and empty complexes
are allowed, and the coefficient field and homology degree are arbitrary. -/
theorem finiteSimplicial_signedHookBottleneckDissimilarity_le
    (hn : 1 ≤ n) (g h : Filtration.FiniteGraded C n) (q : ℕ)
    {δ : ℝ≥0} (error : ∀ s i, |g.grade s i - h.grade s i| ≤ (δ : ℝ)) :
    signedHookBottleneckDissimilarity (k := k)
        (finiteSimplicialSignedHookBarcode k hn g q)
        (finiteSimplicialSignedHookBarcode k hn h q) ≤
      (((2 * n - 1 : ℕ) : ℝ≥0∞) ^ 2) * (δ : ℝ≥0∞) := by
  exact (finitelyPresented_moduleSignedHookBottleneckDistance_le hn
    (finiteSimplicialHomology k g q) (finiteSimplicialHomology k h q)
    (finiteSimplicialHomology_finitelyPresented k g q)
    (finiteSimplicialHomology_finitelyPresented k h q)).trans
      (mul_le_mul' le_rfl
        (coordinateInterleavingDistance_finiteSimplicialHomology_le k g h q error))

/-- The finite maximum of the actual face-coordinate errors supplies the
stability radius, including the empty face index set. -/
theorem finiteSimplicial_signedHookBottleneckDissimilarity_le_supGradeError
    (hn : 1 ≤ n) (g h : Filtration.FiniteGraded C n) (q : ℕ) :
    signedHookBottleneckDissimilarity (k := k)
        (finiteSimplicialSignedHookBarcode k hn g q)
        (finiteSimplicialSignedHookBarcode k hn h q) ≤
      (((2 * n - 1 : ℕ) : ℝ≥0∞) ^ 2) * (g.supGradeError h : ℝ≥0∞) :=
  finiteSimplicial_signedHookBottleneckDissimilarity_le k hn g h q
    (g.abs_grade_sub_le_supGradeError h)

end TDA.Persistence
