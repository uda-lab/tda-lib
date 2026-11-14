import TDA.Persistence.Reduction.FiniteInputRepresentatives

/-!
# Original-boundary semantics of executable representative columns

The existing reducer supplies every normal-form hypothesis. Executable columns
agree with its theoretical basis and occupy their actual live bar coordinates.
-/

set_option autoImplicit false

namespace TDA.Persistence.Reduction.FiniteInput

/-- All normal-form inputs follow from validity of the original simplex list. -/
theorem reductionNormalForm (xs : Input) (h : Valid xs) :
    reduced xs = boundary xs * change xs ∧
      TraceChangeCertificate (degree xs) (change xs) (traceChangeInv (trace xs)) ∧
      LowersDegree (degree xs) (reduced xs) ∧ StrictBoundary (reduced xs) ∧
      DistinctPivots (reduced xs) ∧
      (∀ j i, columnPivot ((reduced xs).col j) = some i →
        columnPivot ((reduced xs).col i) = none) :=
  matrixReductionTrace_normalForm_input (degree xs) (boundary xs)
    (boundary_sq_zero xs h) (boundary_strict xs h) (boundary_lowersDegree xs h)

/-- The existing original-homology live map for this particular executable input. -/
noncomputable def liveMap (xs : Input) (h : Valid xs) (p t : ℕ) :
    originalCycleSpace (degree xs) (boundary xs) p t →ₗ[ZMod 2]
      aliveSpace (degree xs) (reduced xs) p t :=
  originalLiveMap (degree xs) (boundary xs) (reduced xs) (change xs)
    (traceChangeInv (trace xs)) (boundary_sq_zero xs h)
    (reductionNormalForm xs h).1 (reductionNormalForm xs h).2.1
    (reductionNormalForm xs h).2.2.1 (reductionNormalForm xs h).2.2.2.2.1 p t

theorem paired_alive (xs : Input) (h : Valid xs)
    (q : Fin xs.length × Fin xs.length) (hq : q ∈ pivotPairs xs)
    (t : ℕ) (hbirth : q.1.val < t) (hdeath : t ≤ q.2.val) :
    AliveCoordinate (degree xs) (reduced xs) (degree xs q.1) t q.1 := by
  have hp := (pivotPairs_mem xs q.1 q.2).mp hq
  have hi : IsPivot (reduced xs) q.1 := ⟨q.2, hp⟩
  refine ⟨rfl, Or.inl ⟨hi, hbirth, ?_⟩⟩
  rwa [deathOfPivot_unique (reduced xs) (reductionNormalForm xs h).2.2.2.2.1
    q.1 q.2 hi hp]

theorem essential_alive (xs : Input) (i : Fin xs.length)
    (hi : i ∈ essentialIndices xs) (t : ℕ) (hbirth : i.val < t) :
    AliveCoordinate (degree xs) (reduced xs) (degree xs i) t i :=
  ⟨rfl, Or.inr ⟨(essentialIndices_mem xs i).mp hi, hbirth⟩⟩

/-- A normal basis column represents a cycle whenever its coordinate is alive. -/
theorem normalColumn_originalCycle (xs : Input) (h : Valid xs)
    (p t : ℕ) (i : Fin xs.length)
    (hi : AliveCoordinate (degree xs) (reduced xs) p t i) :
    OriginalCycle (degree xs) (boundary xs) p t
      (normalColumn (reduced xs) (change xs) i) := by
  let c := reductionNormalForm xs h
  have hc := aliveRepresentative_cycle (degree xs) (boundary xs) (reduced xs)
    (change xs) (traceChangeInv (trace xs)) (boundary_sq_zero xs h)
    c.1 c.2.1 c.2.2.2.2.1 p t (Pi.single i (1 : ZMod 2))
  rw [aliveRepresentative_single_survives (degree xs) (reduced xs) p t i hi] at hc
  have hz := (normalCycle_iff_originalCycle (degree xs) (boundary xs) (reduced xs)
    (change xs) (traceChangeInv (trace xs)) (boundary_sq_zero xs h)
    c.1 c.2.1 c.2.2.1 c.2.2.2.2.1 p t (Pi.single i (1 : ZMod 2))).mp hc
  have hcol : (normalMatrix (reduced xs) (change xs)).mulVec
      (Pi.single i (1 : ZMod 2)) = normalColumn (reduced xs) (change xs) i :=
    Matrix.mulVec_single_one _ _
  rwa [hcol] at hz

/-- The actual original-boundary cycle has exactly its unit live coordinate. -/
theorem normalColumn_liveMap (xs : Input) (h : Valid xs)
    (p t : ℕ) (i : Fin xs.length)
    (hi : AliveCoordinate (degree xs) (reduced xs) p t i) :
    (liveMap xs h p t
      ⟨normalColumn (reduced xs) (change xs) i,
        normalColumn_originalCycle xs h p t i hi⟩).1 = Pi.single i (1 : ZMod 2) := by
  change aliveRepresentative (degree xs) (reduced xs) p t
    (((normalMatrix (reduced xs) (change xs))⁻¹).mulVec
      (normalColumn (reduced xs) (change xs) i)) = _
  have hcol : (normalMatrix (reduced xs) (change xs)).mulVec
      (Pi.single i (1 : ZMod 2)) = normalColumn (reduced xs) (change xs) i :=
    Matrix.mulVec_single_one _ _
  rw [← hcol, normalMatrix_inv_mulVec (reduced xs) (change xs)
    (reductionNormalForm xs h).2.1.upper (reductionNormalForm xs h).2.1.diag]
  exact aliveRepresentative_single_survives (degree xs) (reduced xs) p t i hi

theorem pairedVector_birth_cycle (xs : Input) (h : Valid xs)
    (q : Fin xs.length × Fin xs.length) (hq : q ∈ pivotPairs xs) :
    OriginalCycle (degree xs) (boundary xs) (degree xs q.1) (q.1.val + 1)
      (pairedVector xs q) := by
  rw [pairedVector_eq_normalColumn xs q hq]
  apply normalColumn_originalCycle xs h
  apply paired_alive xs h q hq _ (Nat.lt_succ_self _)
  have hp := (pivotPairs_mem xs q.1 q.2).mp hq
  exact Nat.succ_le_of_lt ((reductionNormalForm xs h).2.2.2.1 q.1 q.2
    ((columnPivot_some_iff _ _).mp hp).1)

theorem essentialVector_birth_cycle (xs : Input) (h : Valid xs)
    (i : Fin xs.length) (hi : i ∈ essentialIndices xs) :
    OriginalCycle (degree xs) (boundary xs) (degree xs i) (i.val + 1)
      (essentialVector xs i) := by
  rw [essentialVector_eq_normalColumn xs i hi]
  exact normalColumn_originalCycle xs h _ _ i
    (essential_alive xs i hi _ (Nat.lt_succ_self _))

/-- The corresponding trace column fills the paired cycle with the original boundary. -/
theorem pairedVector_bounding (xs : Input) (h : Valid xs)
    (q : Fin xs.length × Fin xs.length) (hq : q ∈ pivotPairs xs) :
    PrefixSupported (q.2.val + 1) ((change xs).col q.2) ∧
      Homogeneous (degree xs) (degree xs q.1 + 1) ((change xs).col q.2) ∧
      (boundary xs).mulVec ((change xs).col q.2) = pairedVector xs q := by
  let c := reductionNormalForm xs h
  have hp := (pivotPairs_mem xs q.1 q.2).mp hq
  have hd := c.2.2.1 q.1 q.2 ((columnPivot_some_iff _ _).mp hp).1
  refine ⟨?_, ?_, ?_⟩
  · intro r hr
    exact c.2.1.upper (show q.2 < r by omega)
  · intro r hr
    apply c.2.1.degree_support
    intro he
    exact hr (he.trans hd)
  · change (boundary xs * change xs).col q.2 = pairedVector xs q
    rw [← c.1, pairedVector_eq_reduced_column xs q hq]

end TDA.Persistence.Reduction.FiniteInput
