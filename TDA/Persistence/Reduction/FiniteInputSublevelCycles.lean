import TDA.Persistence.Reduction.FiniteInputSublevelQuery

/-!
# The same computed chain in integer sublevels

A returned cycle is included from its birth prefix into every sublevel at or
above its birth grade. Thus its actual homology class is natural on that domain,
including after its finite death. No prebirth naturality is asserted.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

namespace TDA.Persistence.Reduction.FiniteInput

open TDA.Simplicial TDA.Filtration CategoryTheory

/-- A returned cycle remains a signed cycle at every prefix after its birth. -/
noncomputable def prefixCycleAfterBirth (xs : Input) (h : Valid xs)
    (r : Representative xs.length) (hr : r ∈ representedOccurrences xs)
    (t : ℕ) (ht : r.birthIndex.val < t) :
    letI := faceFintype xs h
    simplicialCycles ((compatibleOrder xs h).prefixComplex t) (ZMod 2) r.occurrence.degree := by
  letI := faceFintype xs h
  have hv := returned_birth_cycle xs h r hr
  exact simplicialCycle xs h r.occurrence.degree t (chainVector r.cycle)
    ⟨fun i hi => hv.1 i (by omega), hv.2⟩

theorem prefixCycleAfterBirth_coordinates (xs : Input) (h : Valid xs)
    (r : Representative xs.length) (hr : r ∈ representedOccurrences xs)
    (t : ℕ) (ht : r.birthIndex.val < t) :
    letI := faceFintype xs h
    (prefixChainEquiv (ZMod 2) (compatibleOrder xs h) t r.occurrence.degree
      (prefixCycleAfterBirth xs h r hr t ht).1).1 = faceVector xs h (chainVector r.cycle) := by
  let := faceFintype xs h
  have hv := returned_birth_cycle xs h r hr
  exact simplicialChain_coordinates xs h r.occurrence.degree t (chainVector r.cycle)
    (fun i hi => hv.1 i (by omega)) hv.2.1

theorem prefixCycleAfterBirth_inclusion (xs : Input) (h : Valid xs)
    (r : Representative xs.length) (hr : r ∈ representedOccurrences xs)
    (s t : ℕ) (hst : s ≤ t) (hs : r.birthIndex.val < s) (ht : r.birthIndex.val < t) :
    letI := faceFintype xs h
    simplicialCycleIncl (ZMod 2) ((compatibleOrder xs h).prefixComplex_mono hst)
      r.occurrence.degree (prefixCycleAfterBirth xs h r hr s hs) =
      prefixCycleAfterBirth xs h r hr t ht := by
  let := faceFintype xs h
  apply (prefixCycleCoordinateEquiv (ZMod 2) (compatibleOrder xs h) t r.occurrence.degree).injective
  apply Subtype.ext
  rw [prefixCycleCoordinateEquiv_inclusion (ZMod 2) (compatibleOrder xs h) s t
    r.occurrence.degree hst]
  change (prefixChainEquiv _ _ s _ _).1 = (prefixChainEquiv _ _ t _ _).1
  rw [prefixCycleAfterBirth_coordinates, prefixCycleAfterBirth_coordinates]

theorem prefixCycleAfterBirth_eq_representedCycle (xs : Input) (h : Valid xs)
    (r : Representative xs.length) (hr : r ∈ representedOccurrences xs)
    (t : Fin (xs.length + 1)) (hb : r.birthIndex.val < t.val)
    (hd : ∀ j, r.deathIndex = some j → t.val ≤ j.val) :
    prefixCycleAfterBirth xs h r hr t.val hb = representedCycle xs h r hr t hb hd := by
  let := faceFintype xs h
  apply (prefixCycleCoordinateEquiv (ZMod 2) (compatibleOrder xs h) t.val r.occurrence.degree).injective
  apply Subtype.ext
  change (prefixChainEquiv _ _ t.val _ _).1 = (prefixChainEquiv _ _ t.val _ _).1
  rw [prefixCycleAfterBirth_coordinates, representedCycle_coordinates]

theorem birth_lt_sublevelStage (xs : Input) (h : Valid xs)
    (r : Representative xs.length) (hr : r ∈ representedOccurrences xs)
    (a : ℤ) (ha : r.occurrence.birth ≤ a) : r.birthIndex.val < sublevelStage xs a := by
  apply (grade_le_iff_index_lt_stage xs h a r.birthIndex).mp
  rwa [← (returned_identity xs r hr).1]

theorem prefix_le_sublevel (xs : Input) (h : Valid xs) (a : ℤ) (t : ℕ)
    (ht : t ≤ sublevelStage xs a) :
    letI := faceFintype xs h
    (compatibleOrder xs h).prefixComplex t ≤ (gradeFilter xs h).sublevel a := by
  let := faceFintype xs h
  rw [sublevel_eq_prefix xs h a]
  exact (compatibleOrder xs h).prefixComplex_mono ht

/-- The returned chain in the actual sublevel, for every grade at or above birth. -/
noncomputable def sublevelCycle (xs : Input) (h : Valid xs)
    (r : Representative xs.length) (hr : r ∈ representedOccurrences xs)
    (a : ℤ) (ha : r.occurrence.birth ≤ a) :
    simplicialCycles ((gradeFilter xs h).sublevel a) (ZMod 2) r.occurrence.degree := by
  letI := faceFintype xs h
  exact simplicialCycleIncl (ZMod 2)
    (prefix_le_sublevel xs h a (r.birthIndex.val + 1)
      (Nat.succ_le_of_lt (birth_lt_sublevelStage xs h r hr a ha))) r.occurrence.degree
    (prefixCycleAfterBirth xs h r hr (r.birthIndex.val + 1) (Nat.lt_succ_self _))

/-- Inclusion keeps exactly the same returned chain, including after death. -/
theorem sublevelCycle_naturality (xs : Input) (h : Valid xs)
    (r : Representative xs.length) (hr : r ∈ representedOccurrences xs)
    (a b : ℤ) (hab : a ≤ b) (ha : r.occurrence.birth ≤ a)
    (hb : r.occurrence.birth ≤ b) :
    simplicialCycleIncl (ZMod 2) ((gradeFilter xs h).sublevel_mono hab) r.occurrence.degree
      (sublevelCycle xs h r hr a ha) = sublevelCycle xs h r hr b hb := by
  let := faceFintype xs h
  unfold sublevelCycle
  rw [← LinearMap.comp_apply, ← simplicialCycleIncl_comp]

theorem sublevelCycle_of_prefix (xs : Input) (h : Valid xs)
    (r : Representative xs.length) (hr : r ∈ representedOccurrences xs)
    (a : ℤ) (ha : r.occurrence.birth ≤ a) (t : ℕ)
    (ht : r.birthIndex.val < t) (hta : t ≤ sublevelStage xs a) :
    letI := faceFintype xs h
    simplicialCycleIncl (ZMod 2) (prefix_le_sublevel xs h a t hta) r.occurrence.degree
      (prefixCycleAfterBirth xs h r hr t ht) = sublevelCycle xs h r hr a ha := by
  let := faceFintype xs h
  rw [← prefixCycleAfterBirth_inclusion xs h r hr (r.birthIndex.val + 1) t
    (Nat.succ_le_of_lt ht) (Nat.lt_succ_self _) ht]
  unfold sublevelCycle
  rw [← LinearMap.comp_apply, ← simplicialCycleIncl_comp]

/-- Reading a sublevel cycle in the equal prefix gives its computed list coefficients. -/
theorem sublevelCycle_to_prefix (xs : Input) (h : Valid xs)
    (r : Representative xs.length) (hr : r ∈ representedOccurrences xs)
    (a : ℤ) (ha : r.occurrence.birth ≤ a) :
    letI := faceFintype xs h
    simplicialCycleIncl (ZMod 2) (sublevel_eq_prefix xs h a).le r.occurrence.degree
      (sublevelCycle xs h r hr a ha) =
      prefixCycleAfterBirth xs h r hr (sublevelStage xs a)
        (birth_lt_sublevelStage xs h r hr a ha) := by
  let := faceFintype xs h
  unfold sublevelCycle
  rw [← LinearMap.comp_apply, ← simplicialCycleIncl_comp]
  exact prefixCycleAfterBirth_inclusion xs h r hr _ _
    (Nat.succ_le_of_lt (birth_lt_sublevelStage xs h r hr a ha)) _ _

theorem sublevelCycle_coordinates (xs : Input) (h : Valid xs)
    (r : Representative xs.length) (hr : r ∈ representedOccurrences xs)
    (a : ℤ) (ha : r.occurrence.birth ≤ a) :
    letI := faceFintype xs h
    (prefixChainEquiv (ZMod 2) (compatibleOrder xs h) (sublevelStage xs a) r.occurrence.degree
      (simplicialCycleIncl (ZMod 2) (sublevel_eq_prefix xs h a).le r.occurrence.degree
        (sublevelCycle xs h r hr a ha)).1).1 = faceVector xs h (chainVector r.cycle) := by
  let := faceFintype xs h
  rw [sublevelCycle_to_prefix, prefixCycleAfterBirth_coordinates]

private theorem class_inclusion {K L : PreAbstractSimplicialComplex ℕ} (h : K ≤ L)
    (p : ℕ) (z : simplicialCycles K (ZMod 2) p) :
    (simplicialHomologyIncl (ZMod 2) h p).hom (simplicialHomologyClass (ZMod 2) K p z) =
      simplicialHomologyClass (ZMod 2) L p (simplicialCycleIncl (ZMod 2) h p z) := by
  rw [← simplicialHomologyMap_inclusion]
  apply simplicialHomologyMap_class
  rw [vertexChainMap_inclusion]
  rfl

/-- The usual actual homology class of the returned chain at this integer sublevel. -/
noncomputable def sublevelClass (xs : Input) (h : Valid xs)
    (r : Representative xs.length) (hr : r ∈ representedOccurrences xs)
    (a : ℤ) (ha : r.occurrence.birth ≤ a) :
    simplicialHomology ((gradeFilter xs h).sublevel a) (ZMod 2) r.occurrence.degree :=
  simplicialHomologyClass (ZMod 2) ((gradeFilter xs h).sublevel a) r.occurrence.degree
    (sublevelCycle xs h r hr a ha)

/-- On the birth-upward domain, actual homology inclusion carries the same class. -/
theorem sublevelClass_naturality (xs : Input) (h : Valid xs)
    (r : Representative xs.length) (hr : r ∈ representedOccurrences xs)
    (a b : ℤ) (hab : a ≤ b) (ha : r.occurrence.birth ≤ a)
    (hb : r.occurrence.birth ≤ b) :
    (simplicialHomologyIncl (ZMod 2) ((gradeFilter xs h).sublevel_mono hab)
      r.occurrence.degree).hom (sublevelClass xs h r hr a ha) = sublevelClass xs h r hr b hb := by
  unfold sublevelClass
  rw [class_inclusion, sublevelCycle_naturality xs h r hr a b hab ha hb]

/-- The existing prefix/alive equivalence, transported along the equal sublevel. -/
noncomputable def sublevelHomologyToAlive (xs : Input) (h : Valid xs) (p : ℕ) (a : ℤ) :
    letI := faceFintype xs h
    simplicialHomology ((gradeFilter xs h).sublevel a) (ZMod 2) p ≃ₗ[ZMod 2]
      aliveSpace (faceDegree (compatibleOrder xs h))
        (reducedFaceBoundary (ZMod 2) (compatibleOrder xs h)) p (sublevelStage xs a) := by
  letI := faceFintype xs h
  let e := sublevel_eq_prefix xs h a
  letI := simplicialHomologyIncl_isIso_of_eq (ZMod 2) e.le e p
  exact (asIso (simplicialHomologyIncl (ZMod 2) e.le p)).toLinearEquiv.trans
    (prefixHomologyToAlive xs h p (sublevelStage xs a))

theorem sublevelHomologyToAlive_class (xs : Input) (h : Valid xs)
    (r : Representative xs.length) (hr : r ∈ representedOccurrences xs)
    (a : ℤ) (ha : r.occurrence.birth ≤ a) :
    letI := faceFintype xs h
    sublevelHomologyToAlive xs h r.occurrence.degree a (sublevelClass xs h r hr a ha) =
      prefixHomologyToAlive xs h r.occurrence.degree (sublevelStage xs a)
        (simplicialClass xs h r.occurrence.degree (sublevelStage xs a)
          (prefixCycleAfterBirth xs h r hr (sublevelStage xs a)
            (birth_lt_sublevelStage xs h r hr a ha))) := by
  let := faceFintype xs h
  change prefixHomologyToAlive xs h r.occurrence.degree (sublevelStage xs a)
    ((simplicialHomologyIncl (ZMod 2) (sublevel_eq_prefix xs h a).le r.occurrence.degree).hom
      (sublevelClass xs h r hr a ha)) = _
  unfold sublevelClass
  rw [class_inclusion, sublevelCycle_to_prefix]
  rfl

end TDA.Persistence.Reduction.FiniteInput
