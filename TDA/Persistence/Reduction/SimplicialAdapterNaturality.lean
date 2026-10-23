import TDA.Persistence.Reduction.SimplicialAdapter

/-! Natural transport from simplicial prefix homology to reducer homology. -/
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
universe u w
namespace TDA.Persistence.Reduction
open TDA.Simplicial TDA.Filtration Module
variable {V : Type u} [LinearOrder V] {α : Type w} [LinearOrder α]
variable {K : PreAbstractSimplicialComplex V} [Fintype (TotalFace K)]
variable {f : FilterFunction K α} (k : Type u) [Field k] [DecidableEq k]
noncomputable local instance naturalityCyclesHasQuotient (e : CompatibleOrder f) (t p : ℕ) :
    HasQuotient (simplicialCycles (e.prefixComplex t) k p)
      (Submodule k (simplicialCycles (e.prefixComplex t) k p)) :=
  Submodule.hasQuotient (R := k) (M := simplicialCycles (e.prefixComplex t) k p)
private noncomputable def originalMapAux (e : CompatibleOrder f) (p s t : ℕ) :=
  let h := faceReduction_normalForm k e
  originalHomologyMap (faceDegree e) (faceBoundaryMatrix k e)
    (reducedFaceBoundary k e) (faceReductionChange k e) (faceReductionChangeInv k e)
    (faceBoundaryMatrix_sq_zero k e) h.1 h.2.1 h.2.2.1 h.2.2.2.2.1 p s t
noncomputable def faceMatrixHomologyMap (e : CompatibleOrder f) (p s t : ℕ) :
    faceMatrixHomology k e p s →ₗ[k] faceMatrixHomology k e p t :=
  originalMapAux k e p s t

theorem faceMatrixHomologyMap_mkQ (e : CompatibleOrder f)
    (p s t : ℕ) (hst : s ≤ t)
    (x : originalCycleSpace (faceDegree e) (faceBoundaryMatrix k e) p s)
    (y : originalCycleSpace (faceDegree e) (faceBoundaryMatrix k e) p t)
    (hxy : x.1 = y.1) :
    faceMatrixHomologyMap k e p s t
      (Submodule.mkQ (R := k)
        (M := originalCycleSpace (faceDegree e) (faceBoundaryMatrix k e) p s)
        (faceMatrixBoundarySubmodule k e p s) x) =
    Submodule.mkQ (R := k)
      (M := originalCycleSpace (faceDegree e) (faceBoundaryMatrix k e) p t)
      (faceMatrixBoundarySubmodule k e p t) y := by
  let h := faceReduction_normalForm k e
  let E := originalHomologyEquivAlive (faceDegree e) (faceBoundaryMatrix k e)
    (reducedFaceBoundary k e) (faceReductionChange k e) (faceReductionChangeInv k e)
    (faceBoundaryMatrix_sq_zero k e) h.1 h.2.1 h.2.2.1 h.2.2.2.2.1 p t
  apply E.injective
  change (originalHomologyEquivAlive (faceDegree e) (faceBoundaryMatrix k e)
    (reducedFaceBoundary k e) (faceReductionChange k e) (faceReductionChangeInv k e)
    (faceBoundaryMatrix_sq_zero k e) h.1 h.2.1 h.2.2.1 h.2.2.2.2.1 p t)
    ((originalHomologyMap (faceDegree e) (faceBoundaryMatrix k e)
      (reducedFaceBoundary k e) (faceReductionChange k e) (faceReductionChangeInv k e)
      (faceBoundaryMatrix_sq_zero k e) h.1 h.2.1 h.2.2.1 h.2.2.2.2.1 p s t)
      (Submodule.Quotient.mk x)) =
    (originalHomologyEquivAlive (faceDegree e) (faceBoundaryMatrix k e)
      (reducedFaceBoundary k e) (faceReductionChange k e) (faceReductionChangeInv k e)
      (faceBoundaryMatrix_sq_zero k e) h.1 h.2.1 h.2.2.1 h.2.2.2.2.1 p t)
      (Submodule.Quotient.mk y)
  rw [originalHomologyMap_mk (faceDegree e) (faceBoundaryMatrix k e)
    (reducedFaceBoundary k e) (faceReductionChange k e) (faceReductionChangeInv k e)
    (faceBoundaryMatrix_sq_zero k e) h.1 h.2.1 h.2.2.1 h.2.2.2.2.1 p s t hst x]
  change _ = (originalLiveMap (faceDegree e) (faceBoundaryMatrix k e)
    (reducedFaceBoundary k e) (faceReductionChange k e) (faceReductionChangeInv k e)
    (faceBoundaryMatrix_sq_zero k e) h.1 h.2.1 h.2.2.1 h.2.2.2.2.1 p t) y
  apply Subtype.ext
  change aliveRepresentative (faceDegree e) (reducedFaceBoundary k e) p t
      (((normalMatrix (reducedFaceBoundary k e) (faceReductionChange k e))⁻¹).mulVec x.1) =
    aliveRepresentative (faceDegree e) (reducedFaceBoundary k e) p t
      (((normalMatrix (reducedFaceBoundary k e) (faceReductionChange k e))⁻¹).mulVec y.1)
  rw [hxy]

theorem prefixQuotientToMatrixHomology_naturality (e : CompatibleOrder f)
    (p s t : ℕ) (hst : s ≤ t) :
    (faceMatrixHomologyMap k e p s t).comp
      (prefixQuotientToMatrixHomology k e s p).toLinearMap =
    (prefixQuotientToMatrixHomology k e t p).toLinearMap.comp
      (simplicialQuotientIncl k (e.prefixComplex_mono hst) p) := by
  apply LinearMap.ext
  intro x
  induction x using Quotient.inductionOn' with
  | _ z =>
    change faceMatrixHomologyMap k e p s t
      (prefixQuotientToMatrixHomology k e s p
        (Submodule.mkQ (R := k) (M := simplicialCycles (e.prefixComplex s) k p)
          (simplicialBoundaries (e.prefixComplex s) k p) z)) =
      prefixQuotientToMatrixHomology k e t p
        (simplicialQuotientIncl k (e.prefixComplex_mono hst) p
          (Submodule.mkQ (R := k) (M := simplicialCycles (e.prefixComplex s) k p)
            (simplicialBoundaries (e.prefixComplex s) k p) z))
    rw [prefixQuotientToMatrixHomology_mkQ, simplicialQuotientIncl_mkQ,
      prefixQuotientToMatrixHomology_mkQ]
    exact faceMatrixHomologyMap_mkQ k e p s t hst _ _
      (prefixCycleCoordinateEquiv_inclusion k e s t p hst z).symm

theorem prefixHomologyEquivMatrixHomology_naturality (e : CompatibleOrder f)
    (p s t : ℕ) (hst : s ≤ t) :
    (faceMatrixHomologyMap k e p s t).comp
      (prefixHomologyEquivMatrixHomology k e s p).toLinearMap =
    (prefixHomologyEquivMatrixHomology k e t p).toLinearMap.comp
      (simplicialHomologyIncl k (e.prefixComplex_mono hst) p).hom := by
  apply LinearMap.ext
  intro x
  let qS := homologyKernelQuotient.{u,u,u} k (simplicialChainComplex (e.prefixComplex s) k) p
  let qT := homologyKernelQuotient.{u,u,u} k (simplicialChainComplex (e.prefixComplex t) k) p
  have hq := congrArg (fun F => F.hom x)
    (simplicialHomologyIncl_quotient_naturality k (e.prefixComplex_mono hst) p)
  have he := congrArg (fun F => F (qS.toLinearEquiv x))
    (prefixQuotientToMatrixHomology_naturality k e p s t hst)
  change faceMatrixHomologyMap k e p s t
      (prefixQuotientToMatrixHomology k e s p (qS.toLinearEquiv x)) =
    prefixQuotientToMatrixHomology k e t p
      (qT.toLinearEquiv ((simplicialHomologyIncl k (e.prefixComplex_mono hst) p).hom x))
  calc
    _ = prefixQuotientToMatrixHomology k e t p
      (simplicialQuotientIncl k (e.prefixComplex_mono hst) p (qS.toLinearEquiv x)) := he
    _ = _ := by
      congr 1
      exact hq.symm

end TDA.Persistence.Reduction
