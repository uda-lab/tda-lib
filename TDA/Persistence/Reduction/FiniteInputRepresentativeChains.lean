import TDA.Persistence.Reduction.FiniteInputRepresentativeSemantics

/-!
# Simplicial chains represented by executable list coordinates

The list-cardinality cast connects computed coefficients to the existing actual
simplicial prefix adapter. These semantic transports are not in the executed API.
-/

set_option autoImplicit false

namespace TDA.Persistence.Reduction.FiniteInput

open TDA.Simplicial TDA.Filtration

/-- Read list-position coefficients in the actual adapter's all-face coordinates. -/
noncomputable def faceVector (xs : Input) (h : Valid xs)
    (v : Fin xs.length → ZMod 2) :
    Fin (@faceCount ℕ (complex xs h) (faceFintype xs h)) → ZMod 2 :=
  fun i => v (Fin.cast (faceCount_eq_length xs h) i)

private theorem change_reindex_cast {m n : ℕ} (hn : m = n)
    (D : Matrix (Fin m) (Fin m) (ZMod 2)) :
    traceChange (matrixReductionTrace
      ((Matrix.reindex (finCongr hn) (finCongr hn)) D)) =
      (Matrix.reindex (finCongr hn) (finCongr hn))
        (traceChange (matrixReductionTrace D)) := by
  cases hn
  rfl

theorem change_reindex (xs : Input) (h : Valid xs) :
    letI := faceFintype xs h
    change xs =
      (Matrix.reindex (finCongr (faceCount_eq_length xs h))
        (finCongr (faceCount_eq_length xs h)))
        (faceReductionChange (ZMod 2) (compatibleOrder xs h)) := by
  let := faceFintype xs h
  unfold change trace faceReductionChange
  rw [boundary_reindex xs h]
  exact change_reindex_cast (faceCount_eq_length xs h) _

private theorem normalColumn_reindex_cast {m n : ℕ} (hn : m = n)
    (R V : Matrix (Fin m) (Fin m) (ZMod 2)) (i r : Fin m) :
    normalColumn ((Matrix.reindex (finCongr hn) (finCongr hn)) R)
      ((Matrix.reindex (finCongr hn) (finCongr hn)) V)
      (Fin.cast hn i) (Fin.cast hn r) = normalColumn R V i r := by
  cases hn
  rfl

theorem normalColumn_faceVector (xs : Input) (h : Valid xs) (i : Fin xs.length) :
    letI := faceFintype xs h
    faceVector xs h (normalColumn (reduced xs) (change xs) i) =
      normalColumn (reducedFaceBoundary (ZMod 2) (compatibleOrder xs h))
        (faceReductionChange (ZMod 2) (compatibleOrder xs h))
        ((finCongr (faceCount_eq_length xs h)).symm i) := by
  let := faceFintype xs h
  funext r
  dsimp only [faceVector]
  rw [reduced_reindex xs h, change_reindex xs h]
  simpa using normalColumn_reindex_cast (faceCount_eq_length xs h)
    (reducedFaceBoundary (ZMod 2) (compatibleOrder xs h))
    (faceReductionChange (ZMod 2) (compatibleOrder xs h))
    ((finCongr (faceCount_eq_length xs h)).symm i) r

private theorem alive_reindex_cast {m n : ℕ} (hn : m = n)
    (d : Fin m → ℕ) (R : Matrix (Fin m) (Fin m) (ZMod 2))
    (p t : ℕ) (i : Fin m) :
    AliveCoordinate (fun a => d ((finCongr hn).symm a))
      ((Matrix.reindex (finCongr hn) (finCongr hn)) R) p t (Fin.cast hn i) ↔
      AliveCoordinate d R p t i := by
  cases hn
  rfl

theorem alive_faceVector (xs : Input) (h : Valid xs) (p t : ℕ) (i : Fin xs.length)
    (hi : AliveCoordinate (degree xs) (reduced xs) p t i) :
    letI := faceFintype xs h
    AliveCoordinate (faceDegree (compatibleOrder xs h))
      (reducedFaceBoundary (ZMod 2) (compatibleOrder xs h)) p t
      ((finCongr (faceCount_eq_length xs h)).symm i) := by
  let := faceFintype xs h
  have hd : degree xs = fun a => faceDegree (compatibleOrder xs h)
      ((finCongr (faceCount_eq_length xs h)).symm a) := by
    funext a
    exact degree_eq_faceDegree xs h a
  rw [hd, reduced_reindex xs h] at hi
  apply (alive_reindex_cast (faceCount_eq_length xs h)
    (faceDegree (compatibleOrder xs h))
    (reducedFaceBoundary (ZMod 2) (compatibleOrder xs h)) p t
    ((finCongr (faceCount_eq_length xs h)).symm i)).mp
  simpa using hi

theorem faceVector_prefix (xs : Input) (h : Valid xs) (t : ℕ)
    (v : Fin xs.length → ZMod 2) (hv : PrefixSupported t v) :
    PrefixSupported t (faceVector xs h v) := by
  intro i hi
  exact hv (Fin.cast (faceCount_eq_length xs h) i) hi

theorem faceVector_homogeneous (xs : Input) (h : Valid xs) (p : ℕ)
    (v : Fin xs.length → ZMod 2) (hv : Homogeneous (degree xs) p v) :
    letI := faceFintype xs h
    Homogeneous (faceDegree (compatibleOrder xs h)) p (faceVector xs h v) := by
  let := faceFintype xs h
  intro i hi
  apply hv (Fin.cast (faceCount_eq_length xs h) i)
  have hd : degree xs (Fin.cast (faceCount_eq_length xs h) i) =
      faceDegree (compatibleOrder xs h) i := by
    simpa using degree_eq_faceDegree xs h (Fin.cast (faceCount_eq_length xs h) i)
  exact fun he => hi (hd.symm.trans he)

private theorem mulVec_reindex_cast {m n : ℕ} (hn : m = n)
    (D : Matrix (Fin m) (Fin m) (ZMod 2)) (v : Fin n → ZMod 2) :
    (fun i => (((Matrix.reindex (finCongr hn) (finCongr hn)) D).mulVec v)
      (Fin.cast hn i)) = D.mulVec (fun i => v (Fin.cast hn i)) := by
  cases hn
  rfl

/-- The computed boundary is literally the actual signed simplicial boundary matrix. -/
theorem boundary_faceVector (xs : Input) (h : Valid xs) (v : Fin xs.length → ZMod 2) :
    letI := faceFintype xs h
    faceVector xs h ((boundary xs).mulVec v) =
      (faceBoundaryMatrix (ZMod 2) (compatibleOrder xs h)).mulVec (faceVector xs h v) := by
  let := faceFintype xs h
  unfold faceVector
  rw [boundary_reindex xs h]
  exact mulVec_reindex_cast (faceCount_eq_length xs h) _ v

/-- The actual simplicial prefix chain with the supplied original-list coefficients. -/
noncomputable def simplicialChain (xs : Input) (h : Valid xs) (p t : ℕ)
    (v : Fin xs.length → ZMod 2) (hpre : PrefixSupported t v)
    (hdeg : Homogeneous (degree xs) p v) :
    letI := faceFintype xs h
    Chain ((compatibleOrder xs h).prefixComplex t) (ZMod 2) p := by
  letI := faceFintype xs h
  exact (prefixChainEquiv (ZMod 2) (compatibleOrder xs h) t p).symm
    ⟨faceVector xs h v, (mem_prefixDegreeSpace_iff (ZMod 2) (compatibleOrder xs h)
      t p _).mpr ⟨faceVector_prefix xs h t v hpre,
        faceVector_homogeneous xs h p v hdeg⟩⟩

theorem simplicialChain_coordinates (xs : Input) (h : Valid xs) (p t : ℕ)
    (v : Fin xs.length → ZMod 2) (hpre : PrefixSupported t v)
    (hdeg : Homogeneous (degree xs) p v) :
    letI := faceFintype xs h
    (prefixChainEquiv (ZMod 2) (compatibleOrder xs h) t p
      (simplicialChain xs h p t v hpre hdeg)).1 = faceVector xs h v := by
  let := faceFintype xs h
  exact congrArg Subtype.val
    ((prefixChainEquiv (ZMod 2) (compatibleOrder xs h) t p).apply_symm_apply _)

theorem simplicialChain_isCycle (xs : Input) (h : Valid xs) (p t : ℕ)
    (v : Fin xs.length → ZMod 2) (hv : OriginalCycle (degree xs) (boundary xs) p t v) :
    letI := faceFintype xs h
    simplicialChain xs h p t v hv.1 hv.2.1 ∈
      simplicialCycles ((compatibleOrder xs h).prefixComplex t) (ZMod 2) p := by
  let := faceFintype xs h
  apply (prefixChainEquiv_cycle_iff (ZMod 2) (compatibleOrder xs h) t p _).mpr
  rw [simplicialChain_coordinates]
  refine ⟨faceVector_prefix xs h t v hv.1,
    faceVector_homogeneous xs h p v hv.2.1, ?_⟩
  rw [← boundary_faceVector xs h v, hv.2.2]
  rfl

/-- A proved original cycle, interpreted in the actual signed simplicial chain complex. -/
noncomputable def simplicialCycle (xs : Input) (h : Valid xs) (p t : ℕ)
    (v : Fin xs.length → ZMod 2) (hv : OriginalCycle (degree xs) (boundary xs) p t v) :
    letI := faceFintype xs h
    simplicialCycles ((compatibleOrder xs h).prefixComplex t) (ZMod 2) p :=
  ⟨simplicialChain xs h p t v hv.1 hv.2.1, simplicialChain_isCycle xs h p t v hv⟩

/-- A computed filling identity is an identity for the actual signed boundary. -/
theorem simplicialChain_boundary (xs : Input) (h : Valid xs) (p t : ℕ)
    (v w : Fin xs.length → ZMod 2)
    (hvpre : PrefixSupported t v) (hvdeg : Homogeneous (degree xs) p v)
    (hwpre : PrefixSupported t w) (hwdeg : Homogeneous (degree xs) (p + 1) w)
    (hb : (boundary xs).mulVec w = v) :
    letI := faceFintype xs h
    TDA.Simplicial.boundary ((compatibleOrder xs h).prefixComplex t) (ZMod 2) p
      (simplicialChain xs h (p + 1) t w hwpre hwdeg) =
      simplicialChain xs h p t v hvpre hvdeg := by
  let := faceFintype xs h
  apply (prefixChainEquiv (ZMod 2) (compatibleOrder xs h) t p).injective
  apply Subtype.ext
  rw [← faceBoundaryMatrix_mulVec_prefix, simplicialChain_coordinates,
    simplicialChain_coordinates, ← boundary_faceVector, hb]

end TDA.Persistence.Reduction.FiniteInput
