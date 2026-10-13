import TDA.Persistence.Reduction.SimplicialAdapter

/-! Natural transport from actual simplicial prefix homology to reducer homology. -/
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
  let h := actualReduction_normalForm k e
  originalHomologyMap (faceDegree e) (actualBoundaryMatrix k e)
    (actualReducedBoundary k e) (actualTraceChange k e) (actualTraceChangeInv k e)
    (actualBoundaryMatrix_sq_zero k e) h.1 h.2.1 h.2.2.1 h.2.2.2.2.1 p s t
noncomputable def actualOriginalHomologyMap (e : CompatibleOrder f) (p s t : ℕ) :
    actualOriginalHomology k e p s →ₗ[k] actualOriginalHomology k e p t :=
  originalMapAux k e p s t

theorem actualOriginalHomologyMap_mkQ (e : CompatibleOrder f)
    (p s t : ℕ) (hst : s ≤ t)
    (x : originalCycleSpace (faceDegree e) (actualBoundaryMatrix k e) p s)
    (y : originalCycleSpace (faceDegree e) (actualBoundaryMatrix k e) p t)
    (hxy : x.1 = y.1) :
    actualOriginalHomologyMap k e p s t
      (Submodule.mkQ (R := k)
        (M := originalCycleSpace (faceDegree e) (actualBoundaryMatrix k e) p s)
        (actualMatrixBoundarySubmodule k e p s) x) =
    Submodule.mkQ (R := k)
      (M := originalCycleSpace (faceDegree e) (actualBoundaryMatrix k e) p t)
      (actualMatrixBoundarySubmodule k e p t) y := by
  let h := actualReduction_normalForm k e
  let E := originalHomologyEquivAlive (faceDegree e) (actualBoundaryMatrix k e)
    (actualReducedBoundary k e) (actualTraceChange k e) (actualTraceChangeInv k e)
    (actualBoundaryMatrix_sq_zero k e) h.1 h.2.1 h.2.2.1 h.2.2.2.2.1 p t
  apply E.injective
  change (originalHomologyEquivAlive (faceDegree e) (actualBoundaryMatrix k e)
    (actualReducedBoundary k e) (actualTraceChange k e) (actualTraceChangeInv k e)
    (actualBoundaryMatrix_sq_zero k e) h.1 h.2.1 h.2.2.1 h.2.2.2.2.1 p t)
    ((originalHomologyMap (faceDegree e) (actualBoundaryMatrix k e)
      (actualReducedBoundary k e) (actualTraceChange k e) (actualTraceChangeInv k e)
      (actualBoundaryMatrix_sq_zero k e) h.1 h.2.1 h.2.2.1 h.2.2.2.2.1 p s t)
      (Submodule.Quotient.mk x)) =
    (originalHomologyEquivAlive (faceDegree e) (actualBoundaryMatrix k e)
      (actualReducedBoundary k e) (actualTraceChange k e) (actualTraceChangeInv k e)
      (actualBoundaryMatrix_sq_zero k e) h.1 h.2.1 h.2.2.1 h.2.2.2.2.1 p t)
      (Submodule.Quotient.mk y)
  rw [originalHomologyMap_mk (faceDegree e) (actualBoundaryMatrix k e)
    (actualReducedBoundary k e) (actualTraceChange k e) (actualTraceChangeInv k e)
    (actualBoundaryMatrix_sq_zero k e) h.1 h.2.1 h.2.2.1 h.2.2.2.2.1 p s t hst x]
  change _ = (originalLiveMap (faceDegree e) (actualBoundaryMatrix k e)
    (actualReducedBoundary k e) (actualTraceChange k e) (actualTraceChangeInv k e)
    (actualBoundaryMatrix_sq_zero k e) h.1 h.2.1 h.2.2.1 h.2.2.2.2.1 p t) y
  apply Subtype.ext
  change aliveRepresentative (faceDegree e) (actualReducedBoundary k e) p t
      (((normalMatrix (actualReducedBoundary k e) (actualTraceChange k e))⁻¹).mulVec x.1) =
    aliveRepresentative (faceDegree e) (actualReducedBoundary k e) p t
      (((normalMatrix (actualReducedBoundary k e) (actualTraceChange k e))⁻¹).mulVec y.1)
  rw [hxy]

theorem actualQuotientOriginal_naturality (e : CompatibleOrder f)
    (p s t : ℕ) (hst : s ≤ t) :
    (actualOriginalHomologyMap k e p s t).comp
      (actualQuotientOriginal k e s p).toLinearMap =
    (actualQuotientOriginal k e t p).toLinearMap.comp
      (simplicialQuotientIncl k (e.prefixComplex_mono hst) p) := by
  apply LinearMap.ext
  intro x
  induction x using Quotient.inductionOn' with
  | _ z =>
    change actualOriginalHomologyMap k e p s t
      (actualQuotientOriginal k e s p
        (Submodule.mkQ (R := k) (M := simplicialCycles (e.prefixComplex s) k p)
          (simplicialBoundaries (e.prefixComplex s) k p) z)) =
      actualQuotientOriginal k e t p
        (simplicialQuotientIncl k (e.prefixComplex_mono hst) p
          (Submodule.mkQ (R := k) (M := simplicialCycles (e.prefixComplex s) k p)
            (simplicialBoundaries (e.prefixComplex s) k p) z))
    rw [actualQuotientOriginal_mkQ, simplicialQuotientIncl_mkQ,
      actualQuotientOriginal_mkQ]
    exact actualOriginalHomologyMap_mkQ k e p s t hst _ _
      (actualCycleEquiv_inclusion k e s t p hst z).symm

theorem actualHomologyEquivOriginal_naturality (e : CompatibleOrder f)
    (p s t : ℕ) (hst : s ≤ t) :
    (actualOriginalHomologyMap k e p s t).comp
      (actualHomologyEquivOriginal k e s p).toLinearMap =
    (actualHomologyEquivOriginal k e t p).toLinearMap.comp
      (simplicialHomologyIncl k (e.prefixComplex_mono hst) p).hom := by
  apply LinearMap.ext
  intro x
  let qS := homologyKernelQuotient.{u,u,u} k (simplicialChainComplex (e.prefixComplex s) k) p
  let qT := homologyKernelQuotient.{u,u,u} k (simplicialChainComplex (e.prefixComplex t) k) p
  have hq := congrArg (fun F => F.hom x)
    (simplicialHomologyIncl_quotient_naturality k (e.prefixComplex_mono hst) p)
  have he := congrArg (fun F => F (qS.toLinearEquiv x))
    (actualQuotientOriginal_naturality k e p s t hst)
  change actualOriginalHomologyMap k e p s t
      (actualQuotientOriginal k e s p (qS.toLinearEquiv x)) =
    actualQuotientOriginal k e t p
      (qT.toLinearEquiv ((simplicialHomologyIncl k (e.prefixComplex_mono hst) p).hom x))
  calc
    _ = actualQuotientOriginal k e t p
      (simplicialQuotientIncl k (e.prefixComplex_mono hst) p (qS.toLinearEquiv x)) := he
    _ = _ := by
      congr 1
      exact hq.symm

end TDA.Persistence.Reduction
