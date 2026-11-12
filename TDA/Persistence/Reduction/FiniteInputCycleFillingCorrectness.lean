import TDA.Persistence.Reduction.FiniteInputCycleFillings

/-! The selected filling as an actual signed simplicial chain in its sublevel. -/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

namespace TDA.Persistence.Reduction.FiniteInput

open TDA.Simplicial TDA.Filtration

/-- The selected coefficients interpreted in the actual sublevel chain group. -/
noncomputable def fillingSublevelChain (xs : Input) (h : Valid xs) (p : ℕ) (a : ℤ)
    (v : Fin xs.length → ZMod 2) : Chain ((gradeFilter xs h).sublevel a) (ZMod 2) (p + 1) := by
  letI := faceFintype xs h
  let hs := fillingVector_supported xs h p a v
  exact chainIncl (ZMod 2) (prefix_le_sublevel xs h a (sublevelStage xs a) le_rfl) (p + 1)
    (simplicialChain xs h (p + 1) (sublevelStage xs a)
      (fun i => (fillingVector xs p a v)[i]) hs.1 hs.2)

private theorem fillingChain_to_prefix (xs : Input) (h : Valid xs) (p : ℕ) (a : ℤ)
    (v : Fin xs.length → ZMod 2) :
    letI := faceFintype xs h
    chainIncl (ZMod 2) (sublevel_eq_prefix xs h a).le (p + 1) (fillingSublevelChain xs h p a v) =
      simplicialChain xs h (p + 1) (sublevelStage xs a)
        (fun i => (fillingVector xs p a v)[i])
        (fillingVector_supported xs h p a v).1 (fillingVector_supported xs h p a v).2 := by
  let := faceFintype xs h
  unfold fillingSublevelChain
  rw [← LinearMap.comp_apply, ← chainIncl_comp]
  change chainIncl (ZMod 2) (le_refl _) (p + 1) _ = _
  rw [chainIncl_id]
  rfl

theorem fillingSublevelChain_coordinates (xs : Input) (h : Valid xs) (p : ℕ) (a : ℤ)
    (v : Fin xs.length → ZMod 2) :
    letI := faceFintype xs h
    (prefixChainEquiv (ZMod 2) (compatibleOrder xs h) (sublevelStage xs a) (p + 1)
      (chainIncl (ZMod 2) (sublevel_eq_prefix xs h a).le (p + 1)
        (fillingSublevelChain xs h p a v))).1 =
      faceVector xs h (fun i => (fillingVector xs p a v)[i]) := by
  let := faceFintype xs h
  rw [fillingChain_to_prefix]
  exact simplicialChain_coordinates xs h (p + 1) _ _
    (fillingVector_supported xs h p a v).1 (fillingVector_supported xs h p a v).2

/-- The actual signed boundary of the selected filling equals the supplied cycle. -/
theorem fillingSublevelChain_boundary (xs : Input) (h : Valid xs) (p : ℕ) (a : ℤ)
    (v : Fin xs.length → ZMod 2) (hv : CycleInput xs p a v)
    (hz : rawCycleCoordinates xs p a v = 0) :
    TDA.Simplicial.boundary ((gradeFilter xs h).sublevel a) (ZMod 2) p
      (fillingSublevelChain xs h p a v) = (vectorSublevelCycle xs h p a v hv).1 := by
  let := faceFintype xs h
  let hs := fillingVector_supported xs h p a v
  let hc := (cycleInput_iff_originalCycle xs h p a v).mp hv
  let B := simplicialChain xs h (p + 1) (sublevelStage xs a)
    (fun i => (fillingVector xs p a v)[i]) hs.1 hs.2
  let hi := prefix_le_sublevel xs h a (sublevelStage xs a) le_rfl
  have he := LinearMap.congr_fun (boundary_chainIncl (ZMod 2) hi p) B
  change TDA.Simplicial.boundary _ _ p (chainIncl (ZMod 2) hi (p + 1) B) =
    chainIncl (ZMod 2) hi p (TDA.Simplicial.boundary _ _ p B) at he
  rw [simplicialChain_boundary xs h p _ v _ hc.1 hc.2.1 hs.1 hs.2
    (fillingVector_boundary xs h p a v hv hz)] at he
  exact he

theorem runCycleFilling_data (xs : Input) (p : ℕ) (a : ℤ)
    (v : Fin xs.length → ZMod 2) (b : List (Fin xs.length))
    (hb : runCycleFilling xs p a v = some b) :
    b.Nodup ∧ PrefixSupported (sublevelStage xs a) (chainVector b) ∧
      Homogeneous (degree xs) (p + 1) (chainVector b) ∧ (boundary xs).mulVec (chainVector b) = v := by
  obtain ⟨h, hv, hz, rfl⟩ := (runCycleFilling_eq_some_iff xs p a v b).mp hb
  rw [fillingSupport_decode]
  exact ⟨fillingSupport_nodup xs p a v, (fillingVector_supported xs h p a v).1,
    (fillingVector_supported xs h p a v).2, fillingVector_boundary xs h p a v hv hz⟩

/-- Successful execution supplies an actual chain with the returned coefficients and boundary. -/
theorem runCycleFilling_correct (xs : Input) (p : ℕ) (a : ℤ)
    (v : Fin xs.length → ZMod 2) (b : List (Fin xs.length))
    (hb : runCycleFilling xs p a v = some b) :
    ∃ (h : Valid xs) (hv : CycleInput xs p a v),
      ∃ B : Chain ((gradeFilter xs h).sublevel a) (ZMod 2) (p + 1),
        (letI := faceFintype xs h;
          (prefixChainEquiv (ZMod 2) (compatibleOrder xs h) (sublevelStage xs a) (p + 1)
            (chainIncl (ZMod 2) (sublevel_eq_prefix xs h a).le (p + 1) B)).1 =
          faceVector xs h (chainVector b)) ∧
        TDA.Simplicial.boundary ((gradeFilter xs h).sublevel a) (ZMod 2) p B =
          (vectorSublevelCycle xs h p a v hv).1 := by
  obtain ⟨h, hv, hz, rfl⟩ := (runCycleFilling_eq_some_iff xs p a v b).mp hb
  refine ⟨h, hv, fillingSublevelChain xs h p a v, ?_, fillingSublevelChain_boundary xs h p a v hv hz⟩
  rw [fillingSupport_decode]
  exact fillingSublevelChain_coordinates xs h p a v

/-- On admitted cycles, the procedure constructs a filling exactly for actual boundaries. -/
theorem runCycleFilling_exists_iff_boundary (xs : Input) (h : Valid xs) (p : ℕ) (a : ℤ)
    (v : Fin xs.length → ZMod 2) (hv : CycleInput xs p a v) :
    (∃ b, runCycleFilling xs p a v = some b) ↔
      vectorSublevelCycle xs h p a v hv ∈
        simplicialBoundaries ((gradeFilter xs h).sublevel a) (ZMod 2) p := by
  rw [runCycleFilling_exists_iff]
  simp only [h, hv, true_and]
  exact rawCycleCoordinates_eq_zero_iff_boundary xs h p a v hv

theorem fillingSupport_zero (xs : Input) (p : ℕ) (a : ℤ) :
    fillingSupport xs p a (0 : Fin xs.length → ZMod 2) = [] := by
  have he : expiredPreimage (degree xs) (reduced xs) p (sublevelStage xs a)
      (0 : Fin xs.length → ZMod 2) = 0 := by
    funext j
    unfold expiredPreimage
    split <;> simp
  have hz : (fun i : Fin xs.length => (fillingVector xs p a (0 : Fin xs.length → ZMod 2))[i]) = 0 := by
    rw [fillingVector_eq, Matrix.mulVec_zero, he, Matrix.mulVec_zero]
  unfold fillingSupport
  rw [hz]
  simp [supportChain]

theorem runCycleFilling_zero (xs : Input) (h : Valid xs) (p : ℕ) (a : ℤ) :
    runCycleFilling xs p a (0 : Fin xs.length → ZMod 2) = some [] := by
  apply (runCycleFilling_eq_some_iff xs p a 0 []).mpr
  exact ⟨h, cycleInput_zero xs p a, (rawCycleCoordinates xs p a).map_zero,
    (fillingSupport_zero xs p a).symm⟩

end TDA.Persistence.Reduction.FiniteInput
