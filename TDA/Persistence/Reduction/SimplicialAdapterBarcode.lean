import TDA.Persistence.Reduction.SimplicialAdapterNaturality
import TDA.Persistence.Reduction.PivotBarcode
import TDA.Persistence.FiniteDecomposition

/-!
# Homology semantics of reducer occurrences

The simplicial-to-matrix homology equivalences commute with every prefix inclusion.
Transporting the ranges through that square proves the rank formula. The same
formula holds for the pivot interval realization, so all-map rank reconstruction identifies
its occurrence multiset. Finite decomposition then supplies a genuine natural isomorphism;
the argument never substitutes equality of fiber dimensions for naturality.
-/

set_option maxHeartbeats 800000

universe u w

namespace TDA.Persistence.Reduction

open TDA.Persistence TDA.Simplicial TDA.Filtration

variable {V : Type u} [LinearOrder V]
variable {α : Type w} [LinearOrder α]
variable {K : PreAbstractSimplicialComplex V}
variable [Fintype (TotalFace K)]
variable {f : FilterFunction K α}
variable (k : Type u) [Field k] [DecidableEq k]

private noncomputable def rangeEquivOfSquare
    {A B C D : Type u}
    [AddCommGroup A] [Module k A] [AddCommGroup B] [Module k B]
    [AddCommGroup C] [Module k C] [AddCommGroup D] [Module k D]
    (S : A ≃ₗ[k] B) (T : C ≃ₗ[k] D)
    (F : A →ₗ[k] C) (G : B →ₗ[k] D)
    (h : T.toLinearMap.comp F = G.comp S.toLinearMap) :
    LinearMap.range F ≃ₗ[k] LinearMap.range G where
  toFun y := ⟨T y.1, by
    obtain ⟨x, hx⟩ := y.2
    refine ⟨S x, ?_⟩
    rw [← hx]
    exact (LinearMap.congr_fun h x).symm⟩
  invFun y := ⟨T.symm y.1, by
    obtain ⟨x, hx⟩ := y.2
    refine ⟨S.symm x, ?_⟩
    apply T.injective
    calc
      T (F (S.symm x)) = G (S (S.symm x)) := LinearMap.congr_fun h _
      _ = G x := by rw [S.apply_symm_apply]
      _ = y.1 := hx
      _ = T (T.symm y.1) := (T.apply_symm_apply y.1).symm⟩
  left_inv := by intro y; apply Subtype.ext; exact T.symm_apply_apply y.1
  right_inv := by intro y; apply Subtype.ext; exact T.apply_symm_apply y.1
  map_add' := by intro x y; apply Subtype.ext; simp
  map_smul' := by intro c x; apply Subtype.ext; simp

/-- Each pivot row or unpaired zero column contributes one interval
occurrence at face-entry stages; the terminal stage is `m + 1`. -/
noncomputable def facePivotBarcode (e : CompatibleOrder f) (p : ℕ) :
    Multiset (FiniteInterval (faceCount K + 1)) :=
  let h := faceReduction_normalForm k e
  pivotBarcode (faceDegree e) (reducedFaceBoundary k e) h.2.2.2.1 p

/-- The reducer's interval occurrences reproduce its prefix rank formula. -/
theorem facePivotBarcode_rank (e : CompatibleOrder f) (p : ℕ)
    (s t : Fin (faceCount K + 1)) (hst : s ≤ t) :
    structureMapRank (barcodeModule (k := k) (facePivotBarcode k e p))
        s t hst =
      (deathSurvivorFinset (faceDegree e) (reducedFaceBoundary k e)
        p s.val t.val).card +
      (essentialSurvivorFinset (faceDegree e) (reducedFaceBoundary k e)
        p s.val).card := by
  let h := faceReduction_normalForm k e
  rw [rank_barcodeMap]
  change (pivotBarcode (faceDegree e) (reducedFaceBoundary k e)
    h.2.2.2.1 p).countP
      (fun I => I.birth ≤ s.val ∧ t.val < I.death) = _
  exact pivotBarcode_rank (faceDegree e) (reducedFaceBoundary k e)
    h.2.2.2.1 h.2.2.2.2.1 p s.val t.val hst (by omega)

/-- Every prefix-homology structure map has the reducer's pivot rank. -/
theorem facePrefixHomology_rank (e : CompatibleOrder f) (p : ℕ)
    (s t : Fin (faceCount K + 1)) (hst : s ≤ t) :
    structureMapRank (facePrefixModule k e p) s t hst =
      (deathSurvivorFinset (faceDegree e) (reducedFaceBoundary k e)
        p s.val t.val).card +
      (essentialSurvivorFinset (faceDegree e) (reducedFaceBoundary k e)
        p s.val).card := by
  let F := (simplicialHomologyIncl k (e.prefixComplex_mono hst) p).hom
  let G := faceMatrixHomologyMap k e p s.val t.val
  have hcomm := prefixHomologyEquivMatrixHomology_naturality k e p s.val t.val hst
  have hrange := rangeEquivOfSquare k
    (prefixHomologyEquivMatrixHomology k e s.val p)
    (prefixHomologyEquivMatrixHomology k e t.val p) F G hcomm.symm
  have hrank := hrange.finrank_eq
  change Module.finrank k (LinearMap.range F) = _
  rw [hrank]
  -- Use the original differential's square-zero law separately from reduction.
  -- hChange supplies both inverse laws and filtered degree support for V and W.
  have hSquareZero := faceBoundaryMatrix_sq_zero k e
  rcases faceReduction_normalForm k e with
    ⟨hReducedEq, hChange, hLowersDegree, _, hDistinctPivots, _⟩
  exact originalHomologyMap_rank_formula (faceDegree e)
    (faceBoundaryMatrix k e) (reducedFaceBoundary k e)
    (faceReductionChange k e) (faceReductionChangeInv k e)
    hSquareZero hReducedEq hChange hLowersDegree
    hDistinctPivots p s.val t.val hst (by omega)

/-- The reducer's occurrence multiset is the canonical barcode of prefix simplicial homology. The comparison uses every structure-map rank. -/
theorem facePivotBarcode_eq_facePrefixBarcode
    (e : CompatibleOrder f) (p : ℕ) :
    facePivotBarcode k e p = facePrefixBarcode k e p := by
  have hcomparison :
      rankBarcode (barcodeModule (k := k) (facePivotBarcode k e p)) =
        rankBarcode (facePrefixModule k e p) := by
    apply (rankBarcode_eq_iff
      (barcodeModule (k := k) (facePivotBarcode k e p))
      (facePrefixModule k e p)).2
    intro s t hst
    rw [facePivotBarcode_rank k e p s t hst,
      facePrefixHomology_rank k e p s t hst]
  simpa only [rankBarcode_barcodeModule, facePrefixBarcode] using hcomparison

/-- Prefix homology is naturally isomorphic to the reducer's interval realization.
This uses the constructed finite decomposition and all structure-map ranks; the chosen
isomorphism is generally noncanonical and does not belong to the executable F₂ pipeline. -/
theorem nonempty_facePrefixHomologyIsoPivotBarcode
    (e : CompatibleOrder f) (p : ℕ) :
    Nonempty (facePrefixModule k e p ≅ barcodeModule (k := k) (facePivotBarcode k e p)) := by
  -- Identify the occurrence multiset only after constructing a genuine natural decomposition.
  rw [facePivotBarcode_eq_facePrefixBarcode k e p]
  exact nonempty_rankBarcodeIso (facePrefixModule k e p)

end TDA.Persistence.Reduction
