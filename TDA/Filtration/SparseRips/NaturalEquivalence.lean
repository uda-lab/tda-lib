import TDA.Filtration.SparseRips.UnionGridHomology
import TDA.Persistence.SublevelInterleaving

/-!
# Natural sparse-to-relaxed homology equivalence

The sparse and relaxed homology modules are compared by the inclusion of
complexes at each real scale. Its components are isomorphisms by the finite
deletion-grid argument. Naturality is the functoriality of those inclusions.
-/

namespace TDA.Filtration.SparseRips

open TDA.Simplicial TDA.Persistence CategoryTheory

noncomputable section

variable {V : Type*} [MetricSpace V] [Fintype V] [LinearOrder V]

/-- The relaxed complexes form an inclusion filtration for the greedy deletion times. -/
def relaxedFiltration (seed : V) {η : ℝ} (hη : 0 < η)
    (hη' : η ≤ 1 / 3) : SimplicialFiltration ℝ V where
  toFun := relaxedComplex η (deletionTime seed η)
  monotone' := relaxedComplex_mono hη.le (by linarith)
    (deletionTime seed η) (deletionTime_nonneg seed hη hη')

/-- The inclusion into the relaxed complex is a homology isomorphism also at
negative scales, where both complexes have no faces. -/
theorem isIso_sparse_relaxed_all (R : Type*) [Ring R] (seed : V) {η : ℝ}
    (hη : 0 < η) (hη' : η ≤ 1 / 3) (r : ℝ) (n : ℕ) :
    IsIso (simplicialHomologyIncl R (sparseComplex_le_relaxedComplex seed hη hη' r) n) := by
  by_cases hr : 0 ≤ r
  · exact isIso_sparse_relaxed R seed hη hη' hr n
  · have hback : relaxedComplex η (deletionTime seed η) r ≤ sparseComplex seed η r := by
      intro σ hσ
      exact False.elim (hr hσ.2.1)
    let e : simplicialHomology (sparseComplex seed η r) R n ≅
        simplicialHomology (relaxedComplex η (deletionTime seed η) r) R n := {
      hom := simplicialHomologyIncl R
        (sparseComplex_le_relaxedComplex seed hη hη' r) n
      inv := simplicialHomologyIncl R hback n
      hom_inv_id := by
        rw [← simplicialHomologyIncl_comp, simplicialHomologyIncl_id]
      inv_hom_id := by
        rw [← simplicialHomologyIncl_comp, simplicialHomologyIncl_id]
    }
    exact Iso.isIso_hom e

/-- The natural transformation induced by sparse-to-relaxed inclusions. -/
def sparseToRelaxedHom (R : Type*) [Ring R] (seed : V) {η : ℝ}
    (hη : 0 < η) (hη' : η ≤ 1 / 3) (n : ℕ) :
    simplicialHomologyPModule R (sparseFiltration seed η) n ⟶
      simplicialHomologyPModule R (relaxedFiltration seed hη hη') n :=
  inclusionHom R n (fun r => sparseComplex_le_relaxedComplex seed hη hη' r)

@[simp] theorem sparseToRelaxedHom_app (R : Type*) [Ring R] (seed : V)
    {η : ℝ} (hη : 0 < η) (hη' : η ≤ 1 / 3) (n : ℕ) (r : ℝ) :
    (sparseToRelaxedHom R seed hη hη' n).app r =
      simplicialHomologyIncl R (sparseComplex_le_relaxedComplex seed hη hη' r) n := rfl

theorem isIso_sparseToRelaxedHom (R : Type*) [Ring R] (seed : V) {η : ℝ}
    (hη : 0 < η) (hη' : η ≤ 1 / 3) (n : ℕ) :
    IsIso (sparseToRelaxedHom R seed hη hη' n) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro r
  exact isIso_sparse_relaxed_all R seed hη hη' r n

/-- Natural equivalence of sparse and relaxed homology persistence, in every
degree and over every coefficient ring supported by the chain model. -/
def sparseRelaxedHomologyIso (R : Type*) [Ring R] (seed : V) {η : ℝ}
    (hη : 0 < η) (hη' : η ≤ 1 / 3) (n : ℕ) :
    simplicialHomologyPModule R (sparseFiltration seed η) n ≅
      simplicialHomologyPModule R (relaxedFiltration seed hη hη') n := by
  letI := isIso_sparseToRelaxedHom R seed hη hη' n
  exact asIso (sparseToRelaxedHom R seed hη hη' n)

end

end TDA.Filtration.SparseRips
