import TDA.Persistence.FinitePFilterStability
import TDA.Persistence.SublevelInterleaving
import TDA.Persistence.FiniteSimplicialStability

/-!
# Client statements of filter-function stability on a finite complex

Regression fixtures for #1249, family 2 of the downstream-use audit (#1207). Each statement is
written as a downstream client writes it: the file opens no scope and declares no instance, and
imports only the public stability modules.

* A pointwise bound on face values gives the diagram bound, its threshold form, the
  interleaving-distance bound and the finite-part `p`-transport bound.
* The maximal face-value difference is symmetric and is bounded exactly by pointwise bounds.
* Multiparameter grades: a coordinatewise error gives the coordinate interleaving bound and
  the signed hook bound.
-/

namespace TDA.Persistence.FilterStabilityClientExamples

/-- Face values within `ε` of each other give sublevel diagrams within `ε`. -/
theorem filter_bottleneck_le {m : ℕ} {K : PreAbstractSimplicialComplex (Fin m)}
    [Fintype (TDA.Simplicial.TotalFace K)] (k : Type) [Field k]
    (f g : TDA.Filtration.FilterFunction K ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (h : ∀ σ, |f.value σ - g.value σ| ≤ ε) (n : ℕ) :
    TDA.Persistence.bottleneck (TDA.Persistence.dgm k f n) (TDA.Persistence.dgm k g n) ≤
      ENNReal.ofReal ε :=
  TDA.Persistence.bottleneck_dgm_le_of_abs_sub_le k f g hε h n

/-- The threshold form, for every real `ε`. -/
theorem exists_face_of_lt_bottleneck {m : ℕ} {K : PreAbstractSimplicialComplex (Fin m)}
    [Fintype (TDA.Simplicial.TotalFace K)] (k : Type) [Field k]
    (f g : TDA.Filtration.FilterFunction K ℝ) {ε : ℝ} (n : ℕ)
    (h : ENNReal.ofReal ε <
      TDA.Persistence.bottleneck (TDA.Persistence.dgm k f n) (TDA.Persistence.dgm k g n)) :
    ∃ σ, ε < |f.value σ - g.value σ| :=
  TDA.Persistence.exists_lt_abs_sub_of_ofReal_lt_bottleneck_dgm k f g n h

/-- A pointwise bound is a bound on the maximal face-value difference, in either order. -/
theorem faceSupDifference_le_of_abs_sub_le {m : ℕ} {K : PreAbstractSimplicialComplex (Fin m)}
    [Fintype (TDA.Simplicial.TotalFace K)] (f g : TDA.Filtration.FilterFunction K ℝ) {ε : ℝ}
    (hε : 0 ≤ ε) (h : ∀ σ, |f.value σ - g.value σ| ≤ ε) :
    TDA.Persistence.faceSupDifference g f ≤ ε :=
  (TDA.Persistence.faceSupDifference_comm f g).symm.trans_le
    ((TDA.Persistence.faceSupDifference_le_iff f g ε).2 ⟨hε, h⟩)

/-- The interleaving distance of the sublevel modules, from a real pointwise bound. The
library statement takes the bound in `NNReal`; no finiteness of the complex is used. -/
theorem sublevel_interleavingDistance_le {m : ℕ} {K : PreAbstractSimplicialComplex (Fin m)}
    (R : Type) [Ring R] (f g : TDA.Filtration.FilterFunction K ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (h : ∀ σ, |f.value σ - g.value σ| ≤ ε) (n : ℕ) :
    TDA.Persistence.realInterleavingDistance (TDA.Persistence.sublevelModule R f n)
        (TDA.Persistence.sublevelModule R g n) ≤ ENNReal.ofReal ε :=
  TDA.Persistence.realInterleavingDistance_sublevel_le R n (ε := ε.toNNReal)
    (fun σ => (h σ).trans (Real.coe_toNNReal ε hε).ge)

/-- The finite-part `p`-transport cost between the diagrams, from a pointwise bound. -/
theorem filter_pTransport_le {m : ℕ} {K : PreAbstractSimplicialComplex (Fin m)}
    [Fintype (TDA.Simplicial.TotalFace K)] {p : ℝ} (hp : 1 ≤ p) (k : Type) [Field k]
    (f g : TDA.Filtration.FilterFunction K ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (h : ∀ σ, |f.value σ - g.value σ| ≤ ε) (n : ℕ) :
    TDA.Persistence.finitePBoundaryTransportCost p
        (fun q : (TDA.Persistence.dgm k f n).finiteOccurrences => q.1)
        (fun q : (TDA.Persistence.dgm k g n).finiteOccurrences => q.1) ≤
      (((Fintype.card (TDA.Persistence.dgm k f n).finiteOccurrences +
        Fintype.card (TDA.Persistence.dgm k g n).finiteOccurrences : ℕ) : ℝ) ^ p⁻¹) * ε :=
  (TDA.Persistence.finitePBoundaryTransportCost_dgm_le_card_rpow_mul_faceSupDifference
      hp k f g n).trans
    (mul_le_mul_of_nonneg_left ((TDA.Persistence.faceSupDifference_le_iff f g ε).2 ⟨hε, h⟩)
      (Real.rpow_nonneg (Nat.cast_nonneg _) _))

/-- Multiparameter grades within `δ` in every coordinate give coordinate interleaving
distance at most `δ`. -/
theorem graded_coordinateInterleavingDistance_le {m n : ℕ}
    {C : TDA.Simplicial.FiniteComplex m} (k : Type) [Field k]
    (g h : TDA.Filtration.FiniteGraded C n) (q : ℕ) {δ : NNReal}
    (error : ∀ s i, |g.grade s i - h.grade s i| ≤ (δ : ℝ)) :
    TDA.Persistence.coordinateInterleavingDistance
        (TDA.Persistence.finiteSimplicialHomology k g q)
        (TDA.Persistence.finiteSimplicialHomology k h q) ≤ δ :=
  TDA.Persistence.coordinateInterleavingDistance_finiteSimplicialHomology_le k g h q error

/-- The same error bounds the signed hook bottleneck dissimilarity by `(2 * n - 1) ^ 2 * δ`. -/
theorem graded_signedHook_le {m n : ℕ} {C : TDA.Simplicial.FiniteComplex m}
    (k : Type) [Field k] (hn : 1 ≤ n) (g h : TDA.Filtration.FiniteGraded C n) (q : ℕ)
    {δ : NNReal} (error : ∀ s i, |g.grade s i - h.grade s i| ≤ (δ : ℝ)) :
    TDA.Persistence.signedHookBottleneckDissimilarity (k := k)
        (TDA.Persistence.finiteSimplicialSignedHookBarcode k hn g q)
        (TDA.Persistence.finiteSimplicialSignedHookBarcode k hn h q) ≤
      (((2 * n - 1 : ℕ) : ENNReal) ^ 2) * (δ : ENNReal) :=
  TDA.Persistence.finiteSimplicial_signedHookBottleneckDissimilarity_le k hn g h q error

end TDA.Persistence.FilterStabilityClientExamples
