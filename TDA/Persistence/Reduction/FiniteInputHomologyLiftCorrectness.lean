import TDA.Persistence.Reduction.FiniteInputHomologyLifts

/-! Actual induced-map range and signed chain certificates for successful finite lifts. -/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

namespace TDA.Persistence.Reduction.FiniteInput

open TDA.Simplicial TDA.Filtration

private theorem cycleInput_sub (xs : Input) (h : Valid xs) (p : ℕ) (a : ℤ)
    (v w : Fin xs.length → ZMod 2) (hv : CycleInput xs p a v) (hw : CycleInput xs p a w) :
    CycleInput xs p a (v - w) :=
  (cycleInput_iff_originalCycle xs h p a _).mpr
    ((originalCycleSpace (degree xs) (boundary xs) p (sublevelStage xs a)).sub_mem
      ((cycleInput_iff_originalCycle xs h p a v).mp hv)
      ((cycleInput_iff_originalCycle xs h p a w).mp hw))

/-- Successful output decodes to a source cycle with exactly the returned homology coordinates. -/
theorem runHomologyLift_source (xs ys : Input) (p : ℕ) (a b : ℤ) (f : ℕ → ℕ)
    (w : Fin ys.length → ZMod 2)
    (out : HomologyLiftResult xs.length ys.length (activeRepresentatives xs p a).length)
    (hout : runHomologyLift xs ys p a b f w = some out) :
    out.sourceCycle.Nodup ∧ CycleInput xs p a (chainVector out.sourceCycle) ∧
      rawCycleCoordinates xs p a (chainVector out.sourceCycle) = (fun i => out.coefficients[i]) ∧
      (homologyMapMatrix xs ys p a b f).mulVec (fun i => out.coefficients[i]) = rawCycleCoordinates ys p b w := by
  obtain ⟨⟨hx, hy, hm⟩, hw, coefficients, hc, rfl⟩ :=
    (runHomologyLift_eq_some_iff xs ys p a b f w out).mp hout
  simp only [homologyLiftResult_eq]
  rw [chainVector_supportChain]
  exact ⟨supportChain_nodup _, cycleSynthesis_cycleInput xs hx p a _,
    rawCycleCoordinates_cycleSynthesis xs p a _, homologyLiftCoefficients_solution xs ys p a b f w coefficients hc⟩

/-- The target residual is an admitted null cycle and uses precisely the existing selected filling. -/
theorem runHomologyLift_filling (xs ys : Input) (p : ℕ) (a b : ℤ) (f : ℕ → ℕ)
    (w : Fin ys.length → ZMod 2)
    (out : HomologyLiftResult xs.length ys.length (activeRepresentatives xs p a).length)
    (hout : runHomologyLift xs ys p a b f w = some out) :
    runCycleFilling ys p b (w - vertexVector xs ys a f (chainVector out.sourceCycle)) = some out.bounding := by
  obtain ⟨⟨hx, hy, hm⟩, hw, coefficients, hc, rfl⟩ :=
    (runHomologyLift_eq_some_iff xs ys p a b f w out).mp hout
  simp only [homologyLiftResult_eq]
  rw [chainVector_supportChain]
  let v := cycleSynthesis xs p a (fun i => coefficients[i])
  have hv := cycleSynthesis_cycleInput xs hx p a (fun i => coefficients[i])
  apply (runCycleFilling_eq_some_iff ys p b _ _).mpr
  refine ⟨hy, cycleInput_sub ys hy p b _ _ hw
    (vertexVector_cycleInput xs ys hx hy p a b f hm v hv), ?_, rfl⟩
  rw [map_sub, homologyMapMatrix_cycle xs ys hx hy p a b f hm v hv]
  dsimp only [v]
  rw [rawCycleCoordinates_cycleSynthesis, homologyLiftCoefficients_solution xs ys p a b f w coefficients hc,
    sub_self]

/-- The returned target support has the exact signed matrix boundary and admitted degree. -/
theorem runHomologyLift_boundary (xs ys : Input) (p : ℕ) (a b : ℤ) (f : ℕ → ℕ)
    (w : Fin ys.length → ZMod 2)
    (out : HomologyLiftResult xs.length ys.length (activeRepresentatives xs p a).length)
    (hout : runHomologyLift xs ys p a b f w = some out) :
    out.bounding.Nodup ∧ PrefixSupported (sublevelStage ys b) (chainVector out.bounding) ∧
      Homogeneous (degree ys) (p + 1) (chainVector out.bounding) ∧
      (boundary ys).mulVec (chainVector out.bounding) = w - vertexVector xs ys a f (chainVector out.sourceCycle) :=
  runCycleFilling_data ys p b _ out.bounding (runHomologyLift_filling xs ys p a b f w out hout)

/-- Complete finite search detects the range of the actual simplicial homology map. -/
theorem runHomologyLift_exists_iff_range (xs ys : Input) (hx : Valid xs) (hy : Valid ys)
    (p : ℕ) (a b : ℤ) (f : ℕ → ℕ) (hm : VertexMapCondition xs ys a b f)
    (w : Fin ys.length → ZMod 2) (hw : CycleInput ys p b w) :
    (∃ out, runHomologyLift xs ys p a b f w = some out) ↔
      vectorSublevelClass ys hy p b w hw ∈ LinearMap.range
        (simplicialHomologyMap (ZMod 2) (validatedVertexMap xs ys hx hy a b f hm) p).hom := by
  rw [runHomologyLift_exists_iff]
  simp only [VertexMapInput, hx, hy, hm, hw, true_and]
  constructor
  · rintro ⟨coefficients, hc⟩
    refine ⟨(sublevelCoordinates xs hx p a).symm coefficients, ?_⟩
    apply (sublevelCoordinates ys hy p b).injective
    rw [homologyMapMatrix_correct, LinearEquiv.apply_symm_apply, hc,
      rawCycleCoordinates_correct ys hy p b w hw]
  · rintro ⟨x, hxw⟩
    refine ⟨sublevelCoordinates xs hx p a x, ?_⟩
    rw [← homologyMapMatrix_correct xs ys hx hy p a b f hm x, hxw,
      rawCycleCoordinates_correct ys hy p b w hw]

/-- Rejection of an admitted target is exactly failure of actual homology range membership. -/
theorem runHomologyLift_eq_none_iff_not_mem_range (xs ys : Input) (hx : Valid xs) (hy : Valid ys)
    (p : ℕ) (a b : ℤ) (f : ℕ → ℕ) (hm : VertexMapCondition xs ys a b f)
    (w : Fin ys.length → ZMod 2) (hw : CycleInput ys p b w) :
    runHomologyLift xs ys p a b f w = none ↔
      vectorSublevelClass ys hy p b w hw ∉ LinearMap.range
        (simplicialHomologyMap (ZMod 2) (validatedVertexMap xs ys hx hy a b f hm) p).hom := by
  rw [← runHomologyLift_exists_iff_range xs ys hx hy p a b f hm w hw]
  cases runHomologyLift xs ys p a b f w <;> simp

private theorem sublevelChainVector_filling (xs : Input) (h : Valid xs) (p : ℕ) (a : ℤ)
    (v : Fin xs.length → ZMod 2) :
    sublevelChainVector xs h (p + 1) a (fillingSublevelChain xs h p a v) =
      chainVector (fillingSupport xs p a v) := by
  let := faceFintype xs h
  rw [fillingSupport_decode]
  funext i
  have he := congrFun (fillingSublevelChain_coordinates xs h p a v)
    ((finCongr (faceCount_eq_length xs h)).symm i)
  simpa only [sublevelChainVector, LinearMap.coe_mk, AddHom.coe_mk, faceVector,
    finCongr_symm, finCongr_apply, Fin.cast_cast, Fin.cast_eq_self] using he

/-- Success supplies actual cycles and chains, with the returned coefficients and signed boundary. -/
theorem runHomologyLift_correct (xs ys : Input) (p : ℕ) (a b : ℤ) (f : ℕ → ℕ)
    (w : Fin ys.length → ZMod 2)
    (out : HomologyLiftResult xs.length ys.length (activeRepresentatives xs p a).length)
    (hout : runHomologyLift xs ys p a b f w = some out) :
    ∃ (hx : Valid xs) (hy : Valid ys) (hm : VertexMapCondition xs ys a b f)
      (hw : CycleInput ys p b w),
      ∃ (z : simplicialCycles ((gradeFilter xs hx).sublevel a) (ZMod 2) p)
        (B : Chain ((gradeFilter ys hy).sublevel b) (ZMod 2) (p + 1)),
        sublevelChainVector xs hx p a z.1 = chainVector out.sourceCycle ∧
        sublevelCoordinates xs hx p a (simplicialHomologyClass (ZMod 2) _ p z) =
          (fun i => out.coefficients[i]) ∧
        sublevelChainVector ys hy (p + 1) b B = chainVector out.bounding ∧
        TDA.Simplicial.boundary _ (ZMod 2) p B =
          (vectorSublevelCycle ys hy p b w hw).1 -
            vertexChainMap (ZMod 2) (validatedVertexMap xs ys hx hy a b f hm) p z.1 ∧
        (simplicialHomologyMap (ZMod 2) (validatedVertexMap xs ys hx hy a b f hm) p).hom
          (simplicialHomologyClass (ZMod 2) _ p z) = vectorSublevelClass ys hy p b w hw := by
  obtain ⟨⟨hx, hy, hm⟩, hw, coefficients, hc, rfl⟩ :=
    (runHomologyLift_eq_some_iff xs ys p a b f w out).mp hout
  simp only [homologyLiftResult_eq]
  let v := cycleSynthesis xs p a (fun i => coefficients[i])
  have hv := cycleSynthesis_cycleInput xs hx p a (fun i => coefficients[i])
  have hvi := vertexVector_cycleInput xs ys hx hy p a b f hm v hv
  let residual := w - vertexVector xs ys a f v
  have hr := cycleInput_sub ys hy p b w _ hw hvi
  have hz : rawCycleCoordinates ys p b residual = 0 := by
    rw [map_sub, homologyMapMatrix_cycle xs ys hx hy p a b f hm v hv]
    dsimp only [v]
    rw [rawCycleCoordinates_cycleSynthesis,
      homologyLiftCoefficients_solution xs ys p a b f w coefficients hc, sub_self]
  refine ⟨hx, hy, hm, hw, vectorSublevelCycle xs hx p a v hv,
    fillingSublevelChain ys hy p b residual, ?_, ?_, ?_, ?_, ?_⟩
  · rw [chainVector_supportChain]
    exact sublevelChainVector_cycle xs hx p a v hv
  · change sublevelCoordinates xs hx p a (vectorSublevelClass xs hx p a v hv) = (fun i => coefficients[i])
    rw [← rawCycleCoordinates_correct, rawCycleCoordinates_cycleSynthesis]
  · exact sublevelChainVector_filling ys hy p b residual
  · rw [fillingSublevelChain_boundary ys hy p b residual hr hz]
    apply sublevelChainVector_injective ys hy p b
    rw [map_sub, sublevelChainVector_cycle, sublevelChainVector_cycle,
      sublevelChainVector_vertexChainMap, sublevelChainVector_cycle]
  · change (simplicialHomologyMap (ZMod 2) _ p).hom (vectorSublevelClass xs hx p a v hv) = _
    rw [vertexVector_class xs ys hx hy p a b f hm v hv]
    apply (rawCycleCoordinates_eq_iff ys hy p b _ w hvi hw).mp
    rw [homologyMapMatrix_cycle xs ys hx hy p a b f hm v hv,
      rawCycleCoordinates_cycleSynthesis, homologyLiftCoefficients_solution xs ys p a b f w coefficients hc]

end TDA.Persistence.Reduction.FiniteInput
