import TDA.Persistence.Reduction.FiniteInputHomologyMapCorrectness

/-! Synthesize actual admitted cycles from the ordered finite F₂ homology coordinates. -/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

namespace TDA.Persistence.Reduction.FiniteInput

open TDA.Simplicial TDA.Filtration

/-- An executable linear combination of the computed basis cycles in original face order. -/
def cycleSynthesis (xs : Input) (p : ℕ) (a : ℤ) :
    (BasisIndex xs p a → ZMod 2) →ₗ[ZMod 2] (Fin xs.length → ZMod 2) where
  toFun coefficients := ∑ i, coefficients i • chainVector (basisRecord xs p a i).cycle
  map_add' := by intros; simp [add_smul, Finset.sum_add_distrib]
  map_smul' := by intros; simp [Finset.smul_sum, smul_smul]

theorem cycleSynthesis_cycleInput (xs : Input) (h : Valid xs) (p : ℕ) (a : ℤ)
    (coefficients : BasisIndex xs p a → ZMod 2) :
    CycleInput xs p a (cycleSynthesis xs p a coefficients) := by
  apply (cycleInput_iff_originalCycle xs h p a _).mpr
  change cycleSynthesis xs p a coefficients ∈ originalCycleSpace (degree xs) (boundary xs) p (sublevelStage xs a)
  change (∑ i, coefficients i • chainVector (basisRecord xs p a i).cycle) ∈ _
  apply Submodule.sum_mem
  intro i _
  apply (originalCycleSpace (degree xs) (boundary xs) p (sublevelStage xs a)).smul_mem
  exact (cycleInput_iff_originalCycle xs h p a _).mp (basisRecord_cycleInput xs h p a i)

/-- Synthesis is a right inverse to the executed coordinate map, including empty groups. -/
theorem rawCycleCoordinates_cycleSynthesis (xs : Input) (p : ℕ) (a : ℤ)
    (coefficients : BasisIndex xs p a → ZMod 2) :
    rawCycleCoordinates xs p a (cycleSynthesis xs p a coefficients) = coefficients := by
  ext j
  simp [cycleSynthesis, map_sum, map_smul, rawCycleCoordinates_basisRecord,
    Finset.sum_apply, Pi.single_apply]

/-- The synthesized cycle realizes the existing complete coordinate inverse on actual homology. -/
theorem cycleSynthesis_class (xs : Input) (h : Valid xs) (p : ℕ) (a : ℤ)
    (coefficients : BasisIndex xs p a → ZMod 2) :
    vectorSublevelClass xs h p a (cycleSynthesis xs p a coefficients)
      (cycleSynthesis_cycleInput xs h p a coefficients) =
      (sublevelCoordinates xs h p a).symm coefficients := by
  apply (sublevelCoordinates xs h p a).injective
  rw [← rawCycleCoordinates_correct, rawCycleCoordinates_cycleSynthesis,
    LinearEquiv.apply_symm_apply]

end TDA.Persistence.Reduction.FiniteInput
