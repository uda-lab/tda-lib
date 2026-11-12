import TDA.Persistence.Reduction.FiniteInputRepresentativeChains
import TDA.Simplicial.VertexChainMap

/-!
# Simplicial homology classes of the chosen representative columns

The class is formed from the actual simplicial cycle/boundary quotient. Its
image under the existing homology and normal-form isomorphisms is a unit vector.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

namespace TDA.Persistence.Reduction.FiniteInput

open TDA.Simplicial TDA.Filtration

/-- Interpret one alive normal column as an actual simplicial prefix cycle. -/
noncomputable def columnCycle (xs : Input) (h : Valid xs) (p t : ℕ)
    (i : Fin xs.length) (hi : AliveCoordinate (degree xs) (reduced xs) p t i) :
    letI := faceFintype xs h
    simplicialCycles ((compatibleOrder xs h).prefixComplex t) (ZMod 2) p :=
  simplicialCycle xs h p t (normalColumn (reduced xs) (change xs) i)
    (normalColumn_originalCycle xs h p t i hi)

theorem columnCycle_coordinates (xs : Input) (h : Valid xs) (p t : ℕ)
    (i : Fin xs.length) (hi : AliveCoordinate (degree xs) (reduced xs) p t i) :
    letI := faceFintype xs h
    (prefixChainEquiv (ZMod 2) (compatibleOrder xs h) t p
      (columnCycle xs h p t i hi).1).1 =
      normalColumn (reducedFaceBoundary (ZMod 2) (compatibleOrder xs h))
        (faceReductionChange (ZMod 2) (compatibleOrder xs h))
        ((finCongr (faceCount_eq_length xs h)).symm i) := by
  let := faceFintype xs h
  rw [show (columnCycle xs h p t i hi).1 =
    simplicialChain xs h p t (normalColumn (reduced xs) (change xs) i)
      (normalColumn_originalCycle xs h p t i hi).1
      (normalColumn_originalCycle xs h p t i hi).2.1 from rfl,
    simplicialChain_coordinates, normalColumn_faceVector]

/-- The actual simplicial live map identifies the chosen bar, including multiplicities. -/
theorem columnCycle_liveMap (xs : Input) (h : Valid xs) (p t : ℕ)
    (i : Fin xs.length) (hi : AliveCoordinate (degree xs) (reduced xs) p t i) :
    letI := faceFintype xs h
    (prefixCycleToLive (ZMod 2) (compatibleOrder xs h) t p
      (columnCycle xs h p t i hi)).1 =
      Pi.single ((finCongr (faceCount_eq_length xs h)).symm i) (1 : ZMod 2) := by
  let := faceFintype xs h
  let e := compatibleOrder xs h
  let c := faceReduction_normalForm (ZMod 2) e
  let a := (finCongr (faceCount_eq_length xs h)).symm i
  change aliveRepresentative (faceDegree e) (reducedFaceBoundary (ZMod 2) e) p t
    (((normalMatrix (reducedFaceBoundary (ZMod 2) e)
      (faceReductionChange (ZMod 2) e))⁻¹).mulVec
      ((prefixChainEquiv (ZMod 2) e t p (columnCycle xs h p t i hi).1).1)) = _
  rw [columnCycle_coordinates]
  have hcol : (normalMatrix (reducedFaceBoundary (ZMod 2) e)
      (faceReductionChange (ZMod 2) e)).mulVec (Pi.single a (1 : ZMod 2)) =
      normalColumn (reducedFaceBoundary (ZMod 2) e)
        (faceReductionChange (ZMod 2) e) a := Matrix.mulVec_single_one _ _
  rw [← hcol, normalMatrix_inv_mulVec _ _ c.2.1.upper c.2.1.diag]
  exact aliveRepresentative_single_survives (faceDegree e)
    (reducedFaceBoundary (ZMod 2) e) p t a (alive_faceVector xs h p t i hi)

private noncomputable abbrev cycleQuotient (K : PreAbstractSimplicialComplex ℕ) (p : ℕ) :
    HasQuotient (simplicialCycles K (ZMod 2) p)
      (Submodule (ZMod 2) (simplicialCycles K (ZMod 2) p)) :=
  Submodule.hasQuotient (R := ZMod 2) (M := simplicialCycles K (ZMod 2) p)

attribute [local instance] cycleQuotient

/-- The usual homology class of the actual simplicial cycle. -/
noncomputable def simplicialClass (xs : Input) (h : Valid xs) (p t : ℕ)
    (z : letI := faceFintype xs h
      simplicialCycles ((compatibleOrder xs h).prefixComplex t) (ZMod 2) p) :
    letI := faceFintype xs h
    simplicialHomology ((compatibleOrder xs h).prefixComplex t) (ZMod 2) p := by
  letI := faceFintype xs h
  exact simplicialHomologyClass (ZMod 2) ((compatibleOrder xs h).prefixComplex t) p z

theorem simplicialClass_eq_zero_iff (xs : Input) (h : Valid xs) (p t : ℕ)
    (z : letI := faceFintype xs h
      simplicialCycles ((compatibleOrder xs h).prefixComplex t) (ZMod 2) p) :
    letI := faceFintype xs h
    simplicialClass xs h p t z = 0 ↔
      z ∈ simplicialBoundaries ((compatibleOrder xs h).prefixComplex t) (ZMod 2) p := by
  let := faceFintype xs h
  let E := (homologyKernelQuotient.{0,0,0} (ZMod 2)
    (simplicialChainComplex ((compatibleOrder xs h).prefixComplex t) (ZMod 2)) p).toLinearEquiv
  have hE := simplicialHomologyClass_quotient (ZMod 2)
    ((compatibleOrder xs h).prefixComplex t) p z
  change E (simplicialClass xs h p t z) = _ at hE
  calc
    simplicialClass xs h p t z = 0 ↔ E (simplicialClass xs h p t z) = 0 :=
      (LinearEquiv.map_eq_zero_iff E).symm
    _ ↔ _ := by rw [hE]; exact Submodule.Quotient.mk_eq_zero _

/-- The already proved simplicial-to-matrix and matrix-to-alive isomorphisms. -/
noncomputable def prefixHomologyToAlive (xs : Input) (h : Valid xs) (p t : ℕ) :
    letI := faceFintype xs h
    simplicialHomology ((compatibleOrder xs h).prefixComplex t) (ZMod 2) p ≃ₗ[ZMod 2]
      aliveSpace (faceDegree (compatibleOrder xs h))
        (reducedFaceBoundary (ZMod 2) (compatibleOrder xs h)) p t := by
  letI := faceFintype xs h
  let e := compatibleOrder xs h
  let c := faceReduction_normalForm (ZMod 2) e
  exact (prefixHomologyEquivMatrixHomology (ZMod 2) e t p).trans
    (originalHomologyEquivAlive (faceDegree e) (faceBoundaryMatrix (ZMod 2) e)
      (reducedFaceBoundary (ZMod 2) e) (faceReductionChange (ZMod 2) e)
      (faceReductionChangeInv (ZMod 2) e) (faceBoundaryMatrix_sq_zero (ZMod 2) e)
      c.1 c.2.1 c.2.2.1 c.2.2.2.2.1 p t)

theorem prefixHomologyToAlive_class (xs : Input) (h : Valid xs) (p t : ℕ)
    (z : letI := faceFintype xs h
      simplicialCycles ((compatibleOrder xs h).prefixComplex t) (ZMod 2) p) :
    letI := faceFintype xs h
    prefixHomologyToAlive xs h p t (simplicialClass xs h p t z) =
      prefixCycleToLive (ZMod 2) (compatibleOrder xs h) t p z := by
  let := faceFintype xs h
  let e := compatibleOrder xs h
  let c := faceReduction_normalForm (ZMod 2) e
  let E := (homologyKernelQuotient.{0,0,0} (ZMod 2)
    (simplicialChainComplex (e.prefixComplex t) (ZMod 2)) p).toLinearEquiv
  let F := prefixQuotientToMatrixHomology (ZMod 2) e t p
  let A := originalHomologyEquivAlive (faceDegree e) (faceBoundaryMatrix (ZMod 2) e)
    (reducedFaceBoundary (ZMod 2) e) (faceReductionChange (ZMod 2) e)
    (faceReductionChangeInv (ZMod 2) e) (faceBoundaryMatrix_sq_zero (ZMod 2) e)
    c.1 c.2.1 c.2.2.1 c.2.2.2.2.1 p t
  let q := Submodule.mkQ (R := ZMod 2)
    (M := simplicialCycles (e.prefixComplex t) (ZMod 2) p)
    (simplicialBoundaries (e.prefixComplex t) (ZMod 2) p) z
  have hE : E (simplicialClass xs h p t z) = q :=
    simplicialHomologyClass_quotient (ZMod 2) (e.prefixComplex t) p z
  change A (F (E (simplicialClass xs h p t z))) = _
  calc
    A (F (E (simplicialClass xs h p t z))) = A (F q) := congrArg (fun y => A (F y)) hE
    _ = _ := rfl

theorem columnCycle_not_boundary (xs : Input) (h : Valid xs) (p t : ℕ)
    (i : Fin xs.length) (hi : AliveCoordinate (degree xs) (reduced xs) p t i) :
    letI := faceFintype xs h
    columnCycle xs h p t i hi ∉
      simplicialBoundaries ((compatibleOrder xs h).prefixComplex t) (ZMod 2) p := by
  let := faceFintype xs h
  intro hb
  have hz : prefixCycleToLive (ZMod 2) (compatibleOrder xs h) t p
      (columnCycle xs h p t i hi) = 0 := by
    change columnCycle xs h p t i hi ∈ LinearMap.ker _
    rw [prefixCycleToLive_kernel_eq_boundaries]
    exact hb
  have hv := congrArg (fun v => v.1) hz
  rw [columnCycle_liveMap] at hv
  have hone : (1 : ZMod 2) = 0 := by
    simpa using congrFun hv ((finCongr (faceCount_eq_length xs h)).symm i)
  exact one_ne_zero hone

/-- The class is nonzero in actual simplicial homology, not merely as a chain. -/
theorem columnClass_nonzero (xs : Input) (h : Valid xs) (p t : ℕ)
    (i : Fin xs.length) (hi : AliveCoordinate (degree xs) (reduced xs) p t i) :
    letI := faceFintype xs h
    simplicialClass xs h p t (columnCycle xs h p t i hi) ≠ 0 := by
  let := faceFintype xs h
  rw [ne_eq, simplicialClass_eq_zero_iff]
  exact columnCycle_not_boundary xs h p t i hi

theorem columnClass_coordinate (xs : Input) (h : Valid xs) (p t : ℕ)
    (i : Fin xs.length) (hi : AliveCoordinate (degree xs) (reduced xs) p t i) :
    letI := faceFintype xs h
    (prefixHomologyToAlive xs h p t
      (simplicialClass xs h p t (columnCycle xs h p t i hi))).1 =
      Pi.single ((finCongr (faceCount_eq_length xs h)).symm i) (1 : ZMod 2) := by
  rw [prefixHomologyToAlive_class]
  exact columnCycle_liveMap xs h p t i hi

end TDA.Persistence.Reduction.FiniteInput
