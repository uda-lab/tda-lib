import TDA.Persistence.Reduction.FiniteInputRepresentativeHomology

/-!
# Correctness for every returned representative

Membership in the computed output supplies the pivot or essential identity.
No representative, cycle, basis or homology certificate is a caller premise.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

namespace TDA.Persistence.Reduction.FiniteInput

open TDA.Simplicial TDA.Filtration

private def finiteData (xs : Input) (q : Fin xs.length × Fin xs.length) :
    Representative xs.length :=
  ⟨⟨degree xs q.1, (xs.get q.1).2, .finite (xs.get q.2).2⟩,
    q.1, some q.2, supportChain (pairedVector xs q),
    some (supportChain ((change xs).col q.2))⟩

private theorem returned_cases (xs : Input) (r : Representative xs.length)
    (hr : r ∈ representedOccurrences xs) (P : Representative xs.length → Prop)
    (hp : ∀ q, q ∈ pivotPairs xs → (xs.get q.1).2 ≠ (xs.get q.2).2 → P (finiteData xs q))
    (he : ∀ i, i ∈ essentialIndices xs → P (essentialRepresentative xs i)) : P r := by
  rcases List.mem_append.mp hr with hpair | hess
  · obtain ⟨q, hq, hqr⟩ := List.mem_filterMap.mp hpair
    unfold pairedRepresentative pairOccurrence at hqr
    split_ifs at hqr with hgrade
    · cases hqr
    · simp only [Option.map_some, Option.some.injEq] at hqr
      subst r
      exact hp q hq hgrade
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hess
    exact he i hi

theorem returned_degree (xs : Input) (r : Representative xs.length)
    (hr : r ∈ representedOccurrences xs) : r.occurrence.degree = degree xs r.birthIndex := by
  apply returned_cases xs r hr (fun r => r.occurrence.degree = degree xs r.birthIndex)
  · intro q _ _; rfl
  · intro i _; rfl

theorem returned_identity (xs : Input) (r : Representative xs.length)
    (hr : r ∈ representedOccurrences xs) :
    r.occurrence.birth = (xs.get r.birthIndex).2 ∧
      r.occurrence.death = (r.deathIndex.map (fun j => Death.finite (xs.get j).2)).getD
        Death.essential ∧ r.bounding.isSome = r.deathIndex.isSome := by
  apply returned_cases xs r hr (fun r =>
    r.occurrence.birth = (xs.get r.birthIndex).2 ∧
      r.occurrence.death = (r.deathIndex.map (fun j => Death.finite (xs.get j).2)).getD
        Death.essential ∧ r.bounding.isSome = r.deathIndex.isSome)
  · intro q _ _; exact ⟨rfl, rfl, rfl⟩
  · intro i _; exact ⟨rfl, rfl, rfl⟩

theorem returned_cycle_nodup (xs : Input) (r : Representative xs.length)
    (hr : r ∈ representedOccurrences xs) : r.cycle.Nodup := by
  apply returned_cases xs r hr (fun r => r.cycle.Nodup)
  · intro q _ _; exact supportChain_nodup _
  · intro i _; exact supportChain_nodup _

/-- Every decoded output cycle is the specified normal-form column. -/
theorem returned_normalColumn (xs : Input) (r : Representative xs.length)
    (hr : r ∈ representedOccurrences xs) :
    chainVector r.cycle = normalColumn (reduced xs) (change xs) r.birthIndex := by
  apply returned_cases xs r hr
    (fun r => chainVector r.cycle = normalColumn (reduced xs) (change xs) r.birthIndex)
  · intro q hq _
    exact (chainVector_supportChain _).trans (pairedVector_eq_normalColumn xs q hq)
  · intro i hi
    exact (chainVector_supportChain _).trans (essentialVector_eq_normalColumn xs i hi)

theorem returned_birth_cycle (xs : Input) (h : Valid xs) (r : Representative xs.length)
    (hr : r ∈ representedOccurrences xs) :
    OriginalCycle (degree xs) (boundary xs) r.occurrence.degree
      (r.birthIndex.val + 1) (chainVector r.cycle) := by
  apply returned_cases xs r hr (fun r => OriginalCycle (degree xs) (boundary xs)
    r.occurrence.degree (r.birthIndex.val + 1) (chainVector r.cycle))
  · intro q hq _
    simpa only [finiteData, chainVector_supportChain] using pairedVector_birth_cycle xs h q hq
  · intro i hi
    simpa only [essentialRepresentative, chainVector_supportChain] using
      essentialVector_birth_cycle xs h i hi

theorem returned_alive (xs : Input) (h : Valid xs) (r : Representative xs.length)
    (hr : r ∈ representedOccurrences xs) (t : ℕ) (hbirth : r.birthIndex.val < t)
    (hdeath : ∀ j, r.deathIndex = some j → t ≤ j.val) :
    AliveCoordinate (degree xs) (reduced xs) r.occurrence.degree t r.birthIndex := by
  apply returned_cases xs r hr (fun r => r.birthIndex.val < t →
    (∀ j, r.deathIndex = some j → t ≤ j.val) →
      AliveCoordinate (degree xs) (reduced xs) r.occurrence.degree t r.birthIndex)
  · intro q hq _ hb hd
    exact paired_alive xs h q hq t hb (hd q.2 rfl)
  · intro i hi hb _
    exact essential_alive xs i hi t hb
  · exact hbirth
  · exact hdeath

/-- Every finite output carries a filling, with the original signed boundary. -/
theorem returned_bounding (xs : Input) (h : Valid xs) (r : Representative xs.length)
    (hr : r ∈ representedOccurrences xs) (j : Fin xs.length)
    (hj : r.deathIndex = some j) :
    ∃ b, r.bounding = some b ∧ PrefixSupported (j.val + 1) (chainVector b) ∧
      Homogeneous (degree xs) (r.occurrence.degree + 1) (chainVector b) ∧
      (boundary xs).mulVec (chainVector b) = chainVector r.cycle := by
  apply returned_cases xs r hr (fun r => ∀ j : Fin xs.length, r.deathIndex = some j →
    ∃ b, r.bounding = some b ∧ PrefixSupported (j.val + 1) (chainVector b) ∧
      Homogeneous (degree xs) (r.occurrence.degree + 1) (chainVector b) ∧
      (boundary xs).mulVec (chainVector b) = chainVector r.cycle)
  · intro q hq _ j hj
    have heq : q.2 = j := Option.some.inj hj
    subst j
    refine ⟨supportChain ((change xs).col q.2), rfl, ?_⟩
    simpa only [finiteData, chainVector_supportChain] using pairedVector_bounding xs h q hq
  · intro i hi j hj
    cases hj
  · exact hj

theorem returned_birth_lt_death (xs : Input) (h : Valid xs)
    (r : Representative xs.length) (hr : r ∈ representedOccurrences xs)
    (j : Fin xs.length) (hj : r.deathIndex = some j) : r.birthIndex.val < j.val := by
  apply returned_cases xs r hr (fun r => ∀ j : Fin xs.length,
    r.deathIndex = some j → r.birthIndex.val < j.val)
  · intro q hq _ j hj
    have heq : q.2 = j := Option.some.inj hj
    subst j
    exact (reductionNormalForm xs h).2.2.2.1 q.1 q.2
      ((columnPivot_some_iff _ _).mp ((pivotPairs_mem xs q.1 q.2).mp hq)).1
  · intro i _ j hj
    cases hj
  · exact hj

/-- A finite representative remains a cycle at its death prefix. -/
theorem returned_death_cycle (xs : Input) (h : Valid xs)
    (r : Representative xs.length) (hr : r ∈ representedOccurrences xs)
    (j : Fin xs.length) (hj : r.deathIndex = some j) :
    OriginalCycle (degree xs) (boundary xs) r.occurrence.degree
      (j.val + 1) (chainVector r.cycle) := by
  have hz := returned_birth_cycle xs h r hr
  have hlt := returned_birth_lt_death xs h r hr j hj
  exact ⟨fun i hi => hz.1 i (by omega), hz.2⟩

/-- The returned filling bounds the returned cycle in the actual simplicial complex
at stage `j + 1`, without a filling or homological certificate from the caller. -/
theorem returned_simplicial_bounding (xs : Input) (h : Valid xs)
    (r : Representative xs.length) (hr : r ∈ representedOccurrences xs)
    (j : Fin xs.length) (hj : r.deathIndex = some j) :
    letI := faceFintype xs h
    ∃ b, r.bounding = some b ∧
      ∃ (hpre : PrefixSupported (j.val + 1) (chainVector b))
        (hdeg : Homogeneous (degree xs) (r.occurrence.degree + 1) (chainVector b)),
      TDA.Simplicial.boundary ((compatibleOrder xs h).prefixComplex (j.val + 1))
        (ZMod 2) r.occurrence.degree
        (simplicialChain xs h (r.occurrence.degree + 1) (j.val + 1)
          (chainVector b) hpre hdeg) =
        (simplicialCycle xs h r.occurrence.degree (j.val + 1) (chainVector r.cycle)
          (returned_death_cycle xs h r hr j hj)).1 := by
  let := faceFintype xs h
  obtain ⟨b, hb, hpre, hdeg, hboundary⟩ := returned_bounding xs h r hr j hj
  refine ⟨b, hb, hpre, hdeg, ?_⟩
  exact simplicialChain_boundary xs h r.occurrence.degree (j.val + 1)
    (chainVector r.cycle) (chainVector b)
    (returned_death_cycle xs h r hr j hj).1
    (returned_death_cycle xs h r hr j hj).2.1 hpre hdeg hboundary

/-- The exact simplicial cycle represented by a returned record at an alive prefix. -/
noncomputable def representedCycle (xs : Input) (h : Valid xs)
    (r : Representative xs.length) (hr : r ∈ representedOccurrences xs)
    (t : Fin (xs.length + 1)) (hbirth : r.birthIndex.val < t.val)
    (hdeath : ∀ j, r.deathIndex = some j → t.val ≤ j.val) :
    letI := faceFintype xs h
    simplicialCycles ((compatibleOrder xs h).prefixComplex t.val) (ZMod 2) r.occurrence.degree :=
  columnCycle xs h r.occurrence.degree t.val r.birthIndex
    (returned_alive xs h r hr t.val hbirth hdeath)

theorem representedCycle_coordinates (xs : Input) (h : Valid xs)
    (r : Representative xs.length) (hr : r ∈ representedOccurrences xs)
    (t : Fin (xs.length + 1)) (hbirth : r.birthIndex.val < t.val)
    (hdeath : ∀ j, r.deathIndex = some j → t.val ≤ j.val) :
    letI := faceFintype xs h
    (prefixChainEquiv (ZMod 2) (compatibleOrder xs h) t.val r.occurrence.degree
      (representedCycle xs h r hr t hbirth hdeath).1).1 = faceVector xs h (chainVector r.cycle) := by
  let := faceFintype xs h
  rw [returned_normalColumn xs r hr, normalColumn_faceVector]
  exact columnCycle_coordinates xs h r.occurrence.degree t.val r.birthIndex _

theorem representedCycle_liveMap (xs : Input) (h : Valid xs)
    (r : Representative xs.length) (hr : r ∈ representedOccurrences xs)
    (t : Fin (xs.length + 1)) (hbirth : r.birthIndex.val < t.val)
    (hdeath : ∀ j, r.deathIndex = some j → t.val ≤ j.val) :
    letI := faceFintype xs h
    (prefixCycleToLive (ZMod 2) (compatibleOrder xs h) t.val r.occurrence.degree
      (representedCycle xs h r hr t hbirth hdeath)).1 =
      Pi.single ((finCongr (faceCount_eq_length xs h)).symm r.birthIndex) (1 : ZMod 2) :=
  columnCycle_liveMap xs h r.occurrence.degree t.val r.birthIndex _

/-- Every returned alive occurrence has a nonzero actual simplicial homology class. -/
theorem representedClass_nonzero (xs : Input) (h : Valid xs)
    (r : Representative xs.length) (hr : r ∈ representedOccurrences xs)
    (t : Fin (xs.length + 1)) (hbirth : r.birthIndex.val < t.val)
    (hdeath : ∀ j, r.deathIndex = some j → t.val ≤ j.val) :
    letI := faceFintype xs h
    simplicialClass xs h r.occurrence.degree t.val
      (representedCycle xs h r hr t hbirth hdeath) ≠ 0 :=
  columnClass_nonzero xs h r.occurrence.degree t.val r.birthIndex _

/-- The existing homology isomorphism identifies precisely this occurrence's coordinate. -/
theorem representedClass_coordinate (xs : Input) (h : Valid xs)
    (r : Representative xs.length) (hr : r ∈ representedOccurrences xs)
    (t : Fin (xs.length + 1)) (hbirth : r.birthIndex.val < t.val)
    (hdeath : ∀ j, r.deathIndex = some j → t.val ≤ j.val) :
    letI := faceFintype xs h
    (prefixHomologyToAlive xs h r.occurrence.degree t.val
      (simplicialClass xs h r.occurrence.degree t.val
        (representedCycle xs h r hr t hbirth hdeath))).1 =
      Pi.single ((finCongr (faceCount_eq_length xs h)).symm r.birthIndex) (1 : ZMod 2) :=
  columnClass_coordinate xs h r.occurrence.degree t.val r.birthIndex _

end TDA.Persistence.Reduction.FiniteInput
