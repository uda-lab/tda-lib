import TDA.Persistence.Reduction.FiniteInputNormalCoordinates

/-!
# Coordinates of supplied finite F₂ cycles

The executable procedure validates the original simplex list and checks support,
degree and the original signed boundary. Successful coefficients follow the
unchanged degree-specific active query order.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

namespace TDA.Persistence.Reduction.FiniteInput

/-- Exact input conditions for a degree-p cycle in an integer sublevel. -/
def CycleInput (xs : Input) (p : ℕ) (a : ℤ) (v : Fin xs.length → ZMod 2) : Prop :=
  (∀ i, v i ≠ 0 → degree xs i = p ∧ (xs.get i).2 ≤ a) ∧
    (boundary xs).mulVec v = 0

instance (xs : Input) (p : ℕ) (a : ℤ) (v : Fin xs.length → ZMod 2) :
    Decidable (CycleInput xs p a v) := by
  unfold CycleInput
  infer_instance

theorem cycleInput_zero (xs : Input) (p : ℕ) (a : ℤ) :
    CycleInput xs p a (0 : Fin xs.length → ZMod 2) := by
  constructor
  · intro i hi
    exact (hi rfl).elim
  · exact Matrix.mulVec_zero _

theorem cycleInput_mono (xs : Input) (p : ℕ) (a b : ℤ) (hab : a ≤ b)
    (v : Fin xs.length → ZMod 2) (hv : CycleInput xs p a v) : CycleInput xs p b v := by
  refine ⟨?_, hv.2⟩
  intro i hi
  exact ⟨(hv.1 i hi).1, (hv.1 i hi).2.trans hab⟩

theorem cycleInput_iff_originalCycle (xs : Input) (h : Valid xs) (p : ℕ) (a : ℤ)
    (v : Fin xs.length → ZMod 2) :
    CycleInput xs p a v ↔ OriginalCycle (degree xs) (boundary xs) p (sublevelStage xs a) v := by
  constructor
  · intro hv
    refine ⟨?_, ?_, hv.2⟩
    · intro i hi
      by_contra hn
      have hb := (grade_le_iff_index_lt_stage xs h a i).mp (hv.1 i hn).2
      omega
    · intro i hi
      by_contra hn
      exact hi (hv.1 i hn).1
  · intro hv
    refine ⟨?_, hv.2.2⟩
    intro i hi
    constructor
    · by_contra hn
      exact hi (hv.2.1 i hn)
    · apply (grade_le_iff_index_lt_stage xs h a i).mpr
      by_contra hn
      exact hi (hv.1 i (by omega))

theorem basisRecord_cycleInput (xs : Input) (h : Valid xs) (p : ℕ) (a : ℤ)
    (i : BasisIndex xs p a) : CycleInput xs p a (chainVector (basisRecord xs p a i).cycle) := by
  obtain ⟨hr, ha, hp⟩ := basisRecord_spec xs p a i
  have hc := returned_birth_cycle xs h _ hr
  have hb := (aliveAt_prefix_bounds xs h _ hr a ha).1
  apply (cycleInput_iff_originalCycle xs h p a _).mpr
  have hz : OriginalCycle (degree xs) (boundary xs) (basisRecord xs p a i).occurrence.degree
      (sublevelStage xs a) (chainVector (basisRecord xs p a i).cycle) :=
    ⟨fun j hj => hc.1 j (by omega), hc.2⟩
  simpa only [hp] using hz

/-- A linear coordinate map, executable even before checking cycle conditions. -/
def rawCycleCoordinates (xs : Input) (p : ℕ) (a : ℤ) :
    (Fin xs.length → ZMod 2) →ₗ[ZMod 2] (BasisIndex xs p a → ZMod 2) where
  toFun v i := (normalCoordinateVector xs v)[(basisRecord xs p a i).birthIndex]
  map_add' v w := by
    funext i
    simp only [normalCoordinateVector_apply, Matrix.mulVec_add, Pi.add_apply]
  map_smul' c v := by
    funext i
    simp only [normalCoordinateVector_apply, Matrix.mulVec_smul, Pi.smul_apply,
      RingHom.id_apply]

theorem rawCycleCoordinates_apply (xs : Input) (p : ℕ) (a : ℤ)
    (v : Fin xs.length → ZMod 2) (i : BasisIndex xs p a) :
    rawCycleCoordinates xs p a v i =
      ((normalMatrix (reduced xs) (change xs))⁻¹).mulVec v
        (basisRecord xs p a i).birthIndex := normalCoordinateVector_apply xs v _

/-- Every computed basis cycle round-trips to its own ordered unit coordinate. -/
theorem rawCycleCoordinates_basisRecord (xs : Input) (p : ℕ) (a : ℤ)
    (i : BasisIndex xs p a) :
    rawCycleCoordinates xs p a (chainVector (basisRecord xs p a i).cycle) =
      Pi.single i (1 : ZMod 2) := by
  funext j
  rw [rawCycleCoordinates_apply,
    returned_normalColumn xs (basisRecord xs p a i) (basisRecord_spec xs p a i).1]
  have hc : (normalMatrix (reduced xs) (change xs)).mulVec
      (Pi.single (basisRecord xs p a i).birthIndex (1 : ZMod 2)) =
      normalColumn (reduced xs) (change xs) (basisRecord xs p a i).birthIndex :=
    Matrix.mulVec_single_one _ _
  rw [← hc, normalMatrix_inv_mulVec (reduced xs) (change xs)
    (traceChange_isUpperTriangular (trace xs)) (traceChange_apply_diag (trace xs))]
  simp only [Pi.single_apply, (basisRecord_birth_injective xs p a).eq_iff]

/-- Return coefficients in the active query order, rejecting exactly invalid inputs or cycles. -/
def runCycleCoordinates (xs : Input) (p : ℕ) (a : ℤ) (v : Fin xs.length → ZMod 2) :
    Option (List (ZMod 2)) :=
  if validBool xs then
    if CycleInput xs p a v then
      let coefficients := normalCoordinateVector xs v
      some ((activeRepresentatives xs p a).map (fun r => coefficients[r.birthIndex]))
    else none
  else none

theorem runCycleCoordinates_eq_some_iff (xs : Input) (p : ℕ) (a : ℤ)
    (v : Fin xs.length → ZMod 2) (out : List (ZMod 2)) :
    runCycleCoordinates xs p a v = some out ↔
      Valid xs ∧ CycleInput xs p a v ∧
        out = (activeRepresentatives xs p a).map
          (fun r => (normalCoordinateVector xs v)[r.birthIndex]) := by
  simp only [runCycleCoordinates]
  split_ifs with hx hv
  · simp only [Option.some.injEq]
    exact ⟨fun he => ⟨(validBool_iff xs).mp hx, hv, he.symm⟩, fun he => he.2.2.symm⟩
  · simp only [false_iff, not_and]
    exact fun _ hcycle => (hv hcycle).elim
  · simp only [false_iff, not_and]
    exact fun hvalid => (hx ((validBool_iff xs).mpr hvalid)).elim

theorem runCycleCoordinates_eq_none_iff (xs : Input) (p : ℕ) (a : ℤ)
    (v : Fin xs.length → ZMod 2) :
    runCycleCoordinates xs p a v = none ↔ ¬ (Valid xs ∧ CycleInput xs p a v) := by
  simp [runCycleCoordinates, validBool_iff]

theorem runCycleCoordinates_length (xs : Input) (p : ℕ) (a : ℤ)
    (v : Fin xs.length → ZMod 2) (out : List (ZMod 2))
    (hout : runCycleCoordinates xs p a v = some out) :
    out.length = (activeRepresentatives xs p a).length := by
  rw [(runCycleCoordinates_eq_some_iff xs p a v out).mp hout |>.2.2, List.length_map]

theorem runCycleCoordinates_get (xs : Input) (p : ℕ) (a : ℤ)
    (v : Fin xs.length → ZMod 2) (out : List (ZMod 2))
    (hout : runCycleCoordinates xs p a v = some out) (i : BasisIndex xs p a) :
    out[i.val]? = some (rawCycleCoordinates xs p a v i) := by
  rw [(runCycleCoordinates_eq_some_iff xs p a v out).mp hout |>.2.2,
    List.getElem?_map, List.getElem?_eq_getElem i.isLt]
  rfl

theorem runCycleCoordinates_coefficients (xs : Input) (h : Valid xs) (p : ℕ) (a : ℤ)
    (v : Fin xs.length → ZMod 2) (hv : CycleInput xs p a v) :
    runCycleCoordinates xs p a v = some (List.ofFn (rawCycleCoordinates xs p a v)) := by
  apply (runCycleCoordinates_eq_some_iff xs p a v _).mpr
  refine ⟨h, hv, ?_⟩
  exact List.ofFn_getElem_eq_map (activeRepresentatives xs p a)
    (fun r => (normalCoordinateVector xs v)[r.birthIndex])

theorem runCycleCoordinates_basisRecord (xs : Input) (h : Valid xs) (p : ℕ) (a : ℤ)
    (i : BasisIndex xs p a) :
    runCycleCoordinates xs p a (chainVector (basisRecord xs p a i).cycle) =
      some (List.ofFn (Pi.single i (1 : ZMod 2))) := by
  rw [runCycleCoordinates_coefficients xs h p a _ (basisRecord_cycleInput xs h p a i),
    rawCycleCoordinates_basisRecord]

end TDA.Persistence.Reduction.FiniteInput
