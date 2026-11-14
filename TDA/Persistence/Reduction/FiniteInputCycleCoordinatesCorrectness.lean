import TDA.Persistence.Reduction.FiniteInputCycleCoordinates

/-!
# Actual homology semantics of computed cycle coordinates

The supplied vector is interpreted in the original signed simplicial chain
complex. Its computed coefficients agree with the complete sublevel basis,
so coordinate equality detects equality of actual homology classes.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

namespace TDA.Persistence.Reduction.FiniteInput

open TDA.Simplicial TDA.Filtration

/-- The actual sublevel cycle with exactly the supplied original-face coefficients. -/
noncomputable def vectorSublevelCycle (xs : Input) (h : Valid xs) (p : ℕ) (a : ℤ)
    (v : Fin xs.length → ZMod 2) (hv : CycleInput xs p a v) :
    simplicialCycles ((gradeFilter xs h).sublevel a) (ZMod 2) p := by
  letI := faceFintype xs h
  exact simplicialCycleIncl (ZMod 2) (prefix_le_sublevel xs h a (sublevelStage xs a) le_rfl) p
    (simplicialCycle xs h p (sublevelStage xs a) v
      ((cycleInput_iff_originalCycle xs h p a v).mp hv))

theorem vectorSublevelCycle_to_prefix (xs : Input) (h : Valid xs) (p : ℕ) (a : ℤ)
    (v : Fin xs.length → ZMod 2) (hv : CycleInput xs p a v) :
    letI := faceFintype xs h
    simplicialCycleIncl (ZMod 2) (sublevel_eq_prefix xs h a).le p
      (vectorSublevelCycle xs h p a v hv) =
      simplicialCycle xs h p (sublevelStage xs a) v
        ((cycleInput_iff_originalCycle xs h p a v).mp hv) := by
  let := faceFintype xs h
  unfold vectorSublevelCycle
  rw [← LinearMap.comp_apply, ← simplicialCycleIncl_comp]
  change simplicialCycleIncl (ZMod 2) (le_refl _) p _ = _
  rw [simplicialCycleIncl_id]
  rfl

theorem vectorSublevelCycle_coordinates (xs : Input) (h : Valid xs) (p : ℕ) (a : ℤ)
    (v : Fin xs.length → ZMod 2) (hv : CycleInput xs p a v) :
    letI := faceFintype xs h
    (prefixChainEquiv (ZMod 2) (compatibleOrder xs h) (sublevelStage xs a) p
      (simplicialCycleIncl (ZMod 2) (sublevel_eq_prefix xs h a).le p
        (vectorSublevelCycle xs h p a v hv)).1).1 = faceVector xs h v := by
  let := faceFintype xs h
  rw [vectorSublevelCycle_to_prefix]
  exact simplicialChain_coordinates xs h p _ v
    ((cycleInput_iff_originalCycle xs h p a v).mp hv).1
    ((cycleInput_iff_originalCycle xs h p a v).mp hv).2.1

/-- The usual actual simplicial homology class of the supplied cycle vector. -/
noncomputable def vectorSublevelClass (xs : Input) (h : Valid xs) (p : ℕ) (a : ℤ)
    (v : Fin xs.length → ZMod 2) (hv : CycleInput xs p a v) :
    simplicialHomology ((gradeFilter xs h).sublevel a) (ZMod 2) p :=
  simplicialHomologyClass (ZMod 2) ((gradeFilter xs h).sublevel a) p
    (vectorSublevelCycle xs h p a v hv)

private theorem class_inclusion {K L : PreAbstractSimplicialComplex ℕ} (h : K ≤ L)
    (p : ℕ) (z : simplicialCycles K (ZMod 2) p) :
    (simplicialHomologyIncl (ZMod 2) h p).hom (simplicialHomologyClass (ZMod 2) K p z) =
      simplicialHomologyClass (ZMod 2) L p (simplicialCycleIncl (ZMod 2) h p z) := by
  rw [← simplicialHomologyMap_inclusion]
  apply simplicialHomologyMap_class
  rw [vertexChainMap_inclusion]
  rfl

private theorem vectorClass_to_prefix (xs : Input) (h : Valid xs) (p : ℕ) (a : ℤ)
    (v : Fin xs.length → ZMod 2) (hv : CycleInput xs p a v) :
    letI := faceFintype xs h
    sublevelHomologyToAlive xs h p a (vectorSublevelClass xs h p a v hv) =
      prefixHomologyToAlive xs h p (sublevelStage xs a)
        (simplicialClass xs h p (sublevelStage xs a)
          (simplicialCycle xs h p (sublevelStage xs a) v
            ((cycleInput_iff_originalCycle xs h p a v).mp hv))) := by
  let := faceFintype xs h
  change prefixHomologyToAlive xs h p (sublevelStage xs a)
    ((simplicialHomologyIncl (ZMod 2) (sublevel_eq_prefix xs h a).le p).hom
      (vectorSublevelClass xs h p a v hv)) = _
  unfold vectorSublevelClass
  rw [class_inclusion, vectorSublevelCycle_to_prefix]
  rfl

private theorem normalMatrix_reindex (xs : Input) (h : Valid xs) :
    letI := faceFintype xs h
    normalMatrix (reduced xs) (change xs) =
      (Matrix.reindex (finCongr (faceCount_eq_length xs h))
        (finCongr (faceCount_eq_length xs h)))
        (normalMatrix (reducedFaceBoundary (ZMod 2) (compatibleOrder xs h))
          (faceReductionChange (ZMod 2) (compatibleOrder xs h))) := by
  let := faceFintype xs h
  ext r i
  have hc := congrFun (normalColumn_faceVector xs h i)
    ((finCongr (faceCount_eq_length xs h)).symm r)
  change normalColumn (reduced xs) (change xs) i r =
    normalColumn (reducedFaceBoundary (ZMod 2) (compatibleOrder xs h))
      (faceReductionChange (ZMod 2) (compatibleOrder xs h))
      ((finCongr (faceCount_eq_length xs h)).symm i)
      ((finCongr (faceCount_eq_length xs h)).symm r)
  simpa only [faceVector, finCongr_symm, finCongr_apply, Fin.cast_cast, Fin.cast_eq_self] using hc

private theorem inverse_mulVec_cast {m n : ℕ} (hn : m = n)
    (A : Matrix (Fin m) (Fin m) (ZMod 2)) (v : Fin n → ZMod 2) (i : Fin n) :
    (((Matrix.reindex (finCongr hn) (finCongr hn)) A)⁻¹).mulVec v i =
      (A⁻¹).mulVec (fun j => v ((finCongr hn) j)) ((finCongr hn).symm i) := by
  cases hn
  rfl

private theorem prefixVectorCycle_coordinates (xs : Input) (h : Valid xs) (p t : ℕ)
    (v : Fin xs.length → ZMod 2) (hv : OriginalCycle (degree xs) (boundary xs) p t v) :
    letI := faceFintype xs h
    (prefixChainEquiv (ZMod 2) (compatibleOrder xs h) t p
      (simplicialCycle xs h p t v hv).1).1 = faceVector xs h v :=
  simplicialChain_coordinates xs h p t v hv.1 hv.2.1

/-- Executed coefficients are the complete basis coordinates of the actual cycle class. -/
theorem rawCycleCoordinates_correct (xs : Input) (h : Valid xs) (p : ℕ) (a : ℤ)
    (v : Fin xs.length → ZMod 2) (hv : CycleInput xs p a v) :
    rawCycleCoordinates xs p a v =
      sublevelCoordinates xs h p a (vectorSublevelClass xs h p a v hv) := by
  let := faceFintype xs h
  funext i
  rw [rawCycleCoordinates_apply, sublevelCoordinates_apply, vectorClass_to_prefix,
    prefixHomologyToAlive_class]
  let e := compatibleOrder xs h
  have hi := alive_faceVector xs h p (sublevelStage xs a) _ (basisRecord_alive xs h p a i)
  change ((normalMatrix (reduced xs) (change xs))⁻¹).mulVec v
      (basisRecord xs p a i).birthIndex =
    aliveRepresentative (faceDegree e) (reducedFaceBoundary (ZMod 2) e) p (sublevelStage xs a)
      (((normalMatrix (reducedFaceBoundary (ZMod 2) e) (faceReductionChange (ZMod 2) e))⁻¹).mulVec
        ((prefixChainEquiv (ZMod 2) e (sublevelStage xs a) p
          (simplicialCycle xs h p (sublevelStage xs a) v
            ((cycleInput_iff_originalCycle xs h p a v).mp hv)).1).1))
      ((finCongr (faceCount_eq_length xs h)).symm (basisRecord xs p a i).birthIndex)
  rw [prefixVectorCycle_coordinates xs h p _ v
    ((cycleInput_iff_originalCycle xs h p a v).mp hv)]
  dsimp only [e]
  simp only [aliveRepresentative, if_pos hi]
  rw [normalMatrix_reindex xs h]
  have hc := inverse_mulVec_cast (faceCount_eq_length xs h)
    (normalMatrix (reducedFaceBoundary (ZMod 2) (compatibleOrder xs h))
      (faceReductionChange (ZMod 2) (compatibleOrder xs h))) v (basisRecord xs p a i).birthIndex
  have hf : (fun j => v ((finCongr (faceCount_eq_length xs h)) j)) = faceVector xs h v := by
    funext j
    rfl
  rw [hf] at hc
  exact hc

theorem rawCycleCoordinates_eq_zero_iff (xs : Input) (h : Valid xs) (p : ℕ) (a : ℤ)
    (v : Fin xs.length → ZMod 2) (hv : CycleInput xs p a v) :
    rawCycleCoordinates xs p a v = 0 ↔ vectorSublevelClass xs h p a v hv = 0 := by
  rw [rawCycleCoordinates_correct xs h p a v hv]
  exact (sublevelCoordinates xs h p a).map_eq_zero_iff

private noncomputable abbrev vectorCyclesQuotient (K : PreAbstractSimplicialComplex ℕ) (p : ℕ) :
    HasQuotient (simplicialCycles K (ZMod 2) p)
      (Submodule (ZMod 2) (simplicialCycles K (ZMod 2) p)) :=
  Submodule.hasQuotient (R := ZMod 2) (M := simplicialCycles K (ZMod 2) p)

attribute [local instance] vectorCyclesQuotient

/-- Vanishing computed coordinates detect the actual boundary submodule, not the zero chain. -/
theorem rawCycleCoordinates_eq_zero_iff_boundary (xs : Input) (h : Valid xs) (p : ℕ) (a : ℤ)
    (v : Fin xs.length → ZMod 2) (hv : CycleInput xs p a v) :
    rawCycleCoordinates xs p a v = 0 ↔
      vectorSublevelCycle xs h p a v hv ∈
        simplicialBoundaries ((gradeFilter xs h).sublevel a) (ZMod 2) p := by
  rw [rawCycleCoordinates_eq_zero_iff xs h p a v hv]
  let E := (homologyKernelQuotient.{0,0,0} (ZMod 2)
    (simplicialChainComplex ((gradeFilter xs h).sublevel a) (ZMod 2)) p).toLinearEquiv
  have hE := simplicialHomologyClass_quotient (ZMod 2) ((gradeFilter xs h).sublevel a) p
    (vectorSublevelCycle xs h p a v hv)
  change E (vectorSublevelClass xs h p a v hv) = _ at hE
  calc
    vectorSublevelClass xs h p a v hv = 0 ↔ E (vectorSublevelClass xs h p a v hv) = 0 :=
      (LinearEquiv.map_eq_zero_iff E).symm
    _ ↔ _ := by rw [hE]; exact Submodule.Quotient.mk_eq_zero _

theorem rawCycleCoordinates_eq_iff (xs : Input) (h : Valid xs) (p : ℕ) (a : ℤ)
    (v w : Fin xs.length → ZMod 2) (hv : CycleInput xs p a v) (hw : CycleInput xs p a w) :
    rawCycleCoordinates xs p a v = rawCycleCoordinates xs p a w ↔
      vectorSublevelClass xs h p a v hv = vectorSublevelClass xs h p a w hw := by
  rw [rawCycleCoordinates_correct xs h p a v hv, rawCycleCoordinates_correct xs h p a w hw]
  exact (sublevelCoordinates xs h p a).injective.eq_iff

private theorem prefixVectorCycle_inclusion (xs : Input) (h : Valid xs) (p s t : ℕ)
    (hst : s ≤ t) (v : Fin xs.length → ZMod 2)
    (hs : OriginalCycle (degree xs) (boundary xs) p s v)
    (ht : OriginalCycle (degree xs) (boundary xs) p t v) :
    letI := faceFintype xs h
    simplicialCycleIncl (ZMod 2) ((compatibleOrder xs h).prefixComplex_mono hst) p
      (simplicialCycle xs h p s v hs) = simplicialCycle xs h p t v ht := by
  let := faceFintype xs h
  apply (prefixCycleCoordinateEquiv (ZMod 2) (compatibleOrder xs h) t p).injective
  apply Subtype.ext
  rw [prefixCycleCoordinateEquiv_inclusion (ZMod 2) (compatibleOrder xs h) s t p hst]
  change (prefixChainEquiv _ _ s p _).1 = (prefixChainEquiv _ _ t p _).1
  rw [prefixVectorCycle_coordinates xs h p s v hs,
    prefixVectorCycle_coordinates xs h p t v ht]

theorem vectorSublevelCycle_naturality (xs : Input) (h : Valid xs) (p : ℕ)
    (a b : ℤ) (hab : a ≤ b) (v : Fin xs.length → ZMod 2)
    (ha : CycleInput xs p a v) (hb : CycleInput xs p b v) :
    simplicialCycleIncl (ZMod 2) ((gradeFilter xs h).sublevel_mono hab) p
      (vectorSublevelCycle xs h p a v ha) = vectorSublevelCycle xs h p b v hb := by
  let := faceFintype xs h
  unfold vectorSublevelCycle
  rw [← prefixVectorCycle_inclusion xs h p (sublevelStage xs a) (sublevelStage xs b)
    (sublevelStage_mono xs hab) v ((cycleInput_iff_originalCycle xs h p a v).mp ha)
    ((cycleInput_iff_originalCycle xs h p b v).mp hb)]
  rw [← LinearMap.comp_apply, ← simplicialCycleIncl_comp,
    ← LinearMap.comp_apply, ← simplicialCycleIncl_comp]

theorem vectorSublevelClass_naturality (xs : Input) (h : Valid xs) (p : ℕ)
    (a b : ℤ) (hab : a ≤ b) (v : Fin xs.length → ZMod 2)
    (ha : CycleInput xs p a v) (hb : CycleInput xs p b v) :
    (simplicialHomologyIncl (ZMod 2) ((gradeFilter xs h).sublevel_mono hab) p).hom
      (vectorSublevelClass xs h p a v ha) = vectorSublevelClass xs h p b v hb := by
  unfold vectorSublevelClass
  rw [class_inclusion, vectorSublevelCycle_naturality xs h p a b hab v ha hb]

theorem rawCycleCoordinates_naturality (xs : Input) (h : Valid xs) (p : ℕ)
    (a b : ℤ) (hab : a ≤ b) (v : Fin xs.length → ZMod 2) (ha : CycleInput xs p a v) :
    rawCycleCoordinates xs p b v =
      (basisTransition xs p a b).mulVec (rawCycleCoordinates xs p a v) := by
  have hb := cycleInput_mono xs p a b hab v ha
  rw [rawCycleCoordinates_correct xs h p a v ha, rawCycleCoordinates_correct xs h p b v hb,
    ← sublevelCoordinates_naturality xs h p a b hab,
    vectorSublevelClass_naturality xs h p a b hab v ha hb]

/-- Successful execution supplies the certificates and the actual homology coordinate equality. -/
theorem runCycleCoordinates_correct (xs : Input) (p : ℕ) (a : ℤ)
    (v : Fin xs.length → ZMod 2) (out : List (ZMod 2))
    (hout : runCycleCoordinates xs p a v = some out) :
    ∃ (h : Valid xs) (hv : CycleInput xs p a v),
      out = List.ofFn (sublevelCoordinates xs h p a (vectorSublevelClass xs h p a v hv)) := by
  obtain ⟨h, hv, _⟩ := (runCycleCoordinates_eq_some_iff xs p a v out).mp hout
  refine ⟨h, hv, ?_⟩
  have he := Option.some.inj (hout.symm.trans (runCycleCoordinates_coefficients xs h p a v hv))
  rw [he, rawCycleCoordinates_correct xs h p a v hv]

end TDA.Persistence.Reduction.FiniteInput
