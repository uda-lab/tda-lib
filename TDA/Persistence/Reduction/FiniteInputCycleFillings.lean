import TDA.Persistence.Reduction.FiniteInputCycleCoordinatesCorrectness

/-!
# Executable fillings of finite F₂ boundaries

Expired normal coordinates select admitted death columns. Multiplying their
coefficients by the chronological change matrix gives an original-face filling.
The coordinate procedure supplies all input validation and the null-class test.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

namespace TDA.Persistence.Reduction.FiniteInput

private def finiteExpired {n : ℕ} (d : Fin n → ℕ)
    (R : Matrix (Fin n) (Fin n) (ZMod 2)) (p t : ℕ) (x : Fin n → ZMod 2) :
    Fin n → ZMod 2 := fun j => match columnPivot (R.col j) with
    | none => 0
    | some i => if j.val < t ∧ d i = p then x i / R i j else 0

private theorem finiteExpired_eq {n : ℕ} (d : Fin n → ℕ)
    (R : Matrix (Fin n) (Fin n) (ZMod 2)) (p t : ℕ) (x : Fin n → ZMod 2) :
    finiteExpired d R p t x = expiredPreimage d R p t x := by
  funext j
  unfold finiteExpired expiredPreimage
  cases columnPivot (R.col j) <;> rfl

/-- The selected filling coefficients, stored in the original face order. -/
def fillingVector (xs : Input) (p : ℕ) (a : ℤ) (v : Fin xs.length → ZMod 2) :
    Vector (ZMod 2) xs.length :=
  let R := Vector.ofFn fun r => Vector.ofFn fun j => reduced xs r j
  let V := Vector.ofFn fun r => Vector.ofFn fun j => change xs r j
  let coefficients := normalCoordinateVector xs v
  let preimage := Vector.ofFn (finiteExpired (degree xs) (fun r j => R[r][j])
    p (sublevelStage xs a) (fun i => coefficients[i]))
  Vector.ofFn fun r => ∑ j : Fin xs.length, V[r][j] * preimage[j]

theorem fillingVector_eq (xs : Input) (p : ℕ) (a : ℤ) (v : Fin xs.length → ZMod 2) :
    (fun i => (fillingVector xs p a v)[i]) =
      (change xs).mulVec (expiredPreimage (degree xs) (reduced xs) p (sublevelStage xs a)
        (((normalMatrix (reduced xs) (change xs))⁻¹).mulVec v)) := by
  funext i
  simp only [fillingVector, Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta, Matrix.mulVec, dotProduct]
  have hR : (fun r j => reduced xs r j) = reduced xs := by funext r j; rfl
  have hx : (fun j : Fin xs.length => (normalCoordinateVector xs v)[j.val]) =
      ((normalMatrix (reduced xs) (change xs))⁻¹).mulVec v := by
    funext j
    exact normalCoordinateVector_apply xs v j
  rw [hR, hx, finiteExpired_eq]

theorem fillingVector_supported (xs : Input) (h : Valid xs) (p : ℕ) (a : ℤ)
    (v : Fin xs.length → ZMod 2) :
    PrefixSupported (sublevelStage xs a) (fun i => (fillingVector xs p a v)[i]) ∧
      Homogeneous (degree xs) (p + 1) (fun i => (fillingVector xs p a v)[i]) := by
  rw [fillingVector_eq]
  let cert := (reductionNormalForm xs h).2.1
  exact ⟨upper_mulVec_prefix _ cert.upper _ _ (expiredPreimage_prefix _ _ _ _ _),
    grade_preserving_mulVec (degree xs) (change xs) cert.degree_support (p + 1) _
      (expiredPreimage_degree _ _ (reductionNormalForm xs h).2.2.1 _ _ _)⟩

private theorem zero_live (xs : Input) (h : Valid xs) (p : ℕ) (a : ℤ)
    (v : Fin xs.length → ZMod 2) (hz : rawCycleCoordinates xs p a v = 0) :
    aliveRepresentative (degree xs) (reduced xs) p (sublevelStage xs a)
      (((normalMatrix (reduced xs) (change xs))⁻¹).mulVec v) = 0 := by
  classical
  funext i
  by_cases hi : AliveCoordinate (degree xs) (reduced xs) p (sublevelStage xs a) i
  · obtain ⟨j, hj⟩ := (basisRecord_birth_bijective xs h p a).2 ⟨i, hi⟩
    have hb : (basisRecord xs p a j).birthIndex = i := congrArg Subtype.val hj
    have hc := congrFun hz j
    rw [rawCycleCoordinates_apply, hb] at hc
    simpa only [aliveRepresentative, if_pos hi, Pi.zero_apply] using hc
  · simp only [aliveRepresentative, if_neg hi, Pi.zero_apply]

private theorem preimage_normal_eq_change (xs : Input) (h : Valid xs) (p t : ℕ)
    (x : Fin xs.length → ZMod 2) :
    (normalMatrix (reduced xs) (change xs)).mulVec (expiredPreimage (degree xs) (reduced xs) p t x) =
      (change xs).mulVec (expiredPreimage (degree xs) (reduced xs) p t x) := by
  let c := reductionNormalForm xs h
  funext r
  simp only [Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro j _
  cases hj : columnPivot ((reduced xs).col j) with
  | none =>
    have hy : expiredPreimage (degree xs) (reduced xs) p t x j = 0 := by
      unfold expiredPreimage
      rw [hj]
    rw [hy, mul_zero, mul_zero]
  | some i =>
    have hn : ¬ IsPivot (reduced xs) j := by
      intro hp
      have he := pivot_not_death (degree xs) (boundary xs) (reduced xs) (change xs)
        (traceChangeInv (trace xs)) (boundary_sq_zero xs h) c.1 c.2.1 c.2.2.2.2.1 j hp
      rw [hj] at he
      cases he
    change normalColumn (reduced xs) (change xs) j r * _ = _
    rw [normalColumn_nonpivot _ _ j hn]
    rfl

/-- For an admitted null cycle, the selected vector has exactly the supplied boundary. -/
theorem fillingVector_boundary (xs : Input) (h : Valid xs) (p : ℕ) (a : ℤ)
    (v : Fin xs.length → ZMod 2) (hv : CycleInput xs p a v)
    (hz : rawCycleCoordinates xs p a v = 0) :
    (boundary xs).mulVec (fun i => (fillingVector xs p a v)[i]) = v := by
  rw [fillingVector_eq]
  let c := reductionNormalForm xs h
  let x := ((normalMatrix (reduced xs) (change xs))⁻¹).mulVec v
  let y := expiredPreimage (degree xs) (reduced xs) p (sublevelStage xs a) x
  have hxback : (normalMatrix (reduced xs) (change xs)).mulVec x = v :=
    normalMatrix_mulVec_inv _ _ c.2.1.upper c.2.1.diag v
  have hx : NormalCycle (degree xs) (reduced xs) p (sublevelStage xs a) x := by
    apply (normalCycle_iff_originalCycle (degree xs) (boundary xs) (reduced xs) (change xs)
      (traceChangeInv (trace xs)) (boundary_sq_zero xs h) c.1 c.2.1 c.2.2.1 c.2.2.2.2.1
      p (sublevelStage xs a) x).mpr
    rw [hxback]
    exact (cycleInput_iff_originalCycle xs h p a v).mp hv
  have hd := normalCycle_decompose (degree xs) (boundary xs) (reduced xs) (change xs)
    (traceChangeInv (trace xs)) (boundary_sq_zero xs h) c.1 c.2.1 c.2.2.2.2.1
    p (sublevelStage xs a) x hx
  rw [zero_live xs h p a v hz, zero_add] at hd
  have he := normalMatrix_boundary_mulVec (degree xs) (boundary xs) (reduced xs) (change xs)
    (traceChangeInv (trace xs)) (boundary_sq_zero xs h) c.1 c.2.1 c.2.2.2.2.1 y
  rw [preimage_normal_eq_change xs h p (sublevelStage xs a) x, ← hd, hxback] at he
  exact he

/-- The selected, duplicate-free original-index filling support. -/
def fillingSupport (xs : Input) (p : ℕ) (a : ℤ) (v : Fin xs.length → ZMod 2) :
    List (Fin xs.length) := supportChain (fun i => (fillingVector xs p a v)[i])

theorem fillingSupport_decode (xs : Input) (p : ℕ) (a : ℤ) (v : Fin xs.length → ZMod 2) :
    chainVector (fillingSupport xs p a v) = fun i => (fillingVector xs p a v)[i] :=
  chainVector_supportChain _

theorem fillingSupport_nodup (xs : Input) (p : ℕ) (a : ℤ) (v : Fin xs.length → ZMod 2) :
    (fillingSupport xs p a v).Nodup := supportChain_nodup _

/-- Reuse cycle validation and accept precisely an all-zero coordinate list, including `[0]`. -/
def runCycleFilling (xs : Input) (p : ℕ) (a : ℤ) (v : Fin xs.length → ZMod 2) :
    Option (List (Fin xs.length)) :=
  match runCycleCoordinates xs p a v with
  | none => none
  | some coefficients =>
      if coefficients.all (fun z => z == 0) then some (fillingSupport xs p a v) else none

private theorem all_zero_ofFn {n : ℕ} (f : Fin n → ZMod 2) :
    (List.ofFn f).all (fun z => z == 0) = true ↔ f = 0 := by
  rw [List.all_eq_true]
  constructor
  · intro h
    funext i
    exact (beq_iff_eq).mp (h (f i) (List.mem_ofFn.mpr ⟨i, rfl⟩))
  · intro h z hz
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hz
    simp only [h, Pi.zero_apply, beq_self_eq_true]

private theorem runCycleFilling_of_cycle (xs : Input) (h : Valid xs) (p : ℕ) (a : ℤ)
    (v : Fin xs.length → ZMod 2) (hv : CycleInput xs p a v) :
    runCycleFilling xs p a v =
      if rawCycleCoordinates xs p a v = 0 then some (fillingSupport xs p a v) else none := by
  simp only [runCycleFilling, runCycleCoordinates_coefficients xs h p a v hv, all_zero_ofFn]

theorem runCycleFilling_eq_some_iff (xs : Input) (p : ℕ) (a : ℤ)
    (v : Fin xs.length → ZMod 2) (b : List (Fin xs.length)) :
    runCycleFilling xs p a v = some b ↔
      Valid xs ∧ CycleInput xs p a v ∧ rawCycleCoordinates xs p a v = 0 ∧
        b = fillingSupport xs p a v := by
  by_cases h : Valid xs
  · by_cases hv : CycleInput xs p a v
    · rw [runCycleFilling_of_cycle xs h p a v hv]
      by_cases hz : rawCycleCoordinates xs p a v = 0 <;> simp [h, hv, hz, eq_comm]
    · have he : runCycleCoordinates xs p a v = none :=
        (runCycleCoordinates_eq_none_iff _ _ _ _).mpr (fun hc => hv hc.2)
      simp [runCycleFilling, he, hv]
  · have he : runCycleCoordinates xs p a v = none :=
      (runCycleCoordinates_eq_none_iff _ _ _ _).mpr (fun hc => h hc.1)
    simp [runCycleFilling, he, h]

theorem runCycleFilling_exists_iff (xs : Input) (p : ℕ) (a : ℤ)
    (v : Fin xs.length → ZMod 2) :
    (∃ b, runCycleFilling xs p a v = some b) ↔
      Valid xs ∧ CycleInput xs p a v ∧ rawCycleCoordinates xs p a v = 0 := by
  constructor
  · rintro ⟨b, hb⟩
    obtain ⟨h, hv, hz, _⟩ := (runCycleFilling_eq_some_iff xs p a v b).mp hb
    exact ⟨h, hv, hz⟩
  · rintro ⟨h, hv, hz⟩
    exact ⟨_, (runCycleFilling_eq_some_iff xs p a v _).mpr ⟨h, hv, hz, rfl⟩⟩

theorem runCycleFilling_eq_none_iff (xs : Input) (p : ℕ) (a : ℤ)
    (v : Fin xs.length → ZMod 2) :
    runCycleFilling xs p a v = none ↔
      ¬ (Valid xs ∧ CycleInput xs p a v ∧ rawCycleCoordinates xs p a v = 0) := by
  rw [← runCycleFilling_exists_iff]
  cases runCycleFilling xs p a v <;> simp

end TDA.Persistence.Reduction.FiniteInput
