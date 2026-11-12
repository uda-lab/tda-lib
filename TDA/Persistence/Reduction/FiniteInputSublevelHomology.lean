import TDA.Persistence.Reduction.FiniteInputSublevelCycles

/-! Exact birth/death and coordinate laws for computed integer-sublevel classes. -/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

namespace TDA.Persistence.Reduction.FiniteInput

open TDA.Simplicial TDA.Filtration CategoryTheory

theorem returned_death_grade (xs : Input) (r : Representative xs.length)
    (hr : r ∈ representedOccurrences xs) (j : Fin xs.length) (hj : r.deathIndex = some j) :
    r.occurrence.death = .finite (xs.get j).2 := by
  have he := (returned_identity xs r hr).2.1
  simpa only [hj, Option.map_some, Option.getD_some] using he

theorem returned_deathIndex_of_finite (xs : Input) (r : Representative xs.length)
    (hr : r ∈ representedOccurrences xs) (d : ℤ) (hd : r.occurrence.death = .finite d) :
    ∃ j, r.deathIndex = some j ∧ (xs.get j).2 = d := by
  cases hj : r.deathIndex with
  | none =>
    have he := (returned_identity xs r hr).2.1
    simp only [hj, Option.map_none, Option.getD_none] at he
    rw [hd] at he
    cases he
  | some j =>
    exact ⟨j, rfl, Death.finite.inj ((returned_death_grade xs r hr j hj).symm.trans hd)⟩

theorem returned_finite_birth_lt (xs : Input) (h : Valid xs)
    (r : Representative xs.length) (hr : r ∈ representedOccurrences xs)
    (d : ℤ) (hd : r.occurrence.death = .finite d) : r.occurrence.birth < d := by
  apply finite_birth_lt_death xs h r.occurrence _ d hd
  rw [← representedOccurrences_forget xs]
  exact List.mem_map.mpr ⟨r, hr, rfl⟩

theorem aliveAt_prefix_bounds (xs : Input) (h : Valid xs)
    (r : Representative xs.length) (hr : r ∈ representedOccurrences xs)
    (a : ℤ) (ha : r.occurrence.AliveAt a) :
    r.birthIndex.val < sublevelStage xs a ∧
      ∀ j, r.deathIndex = some j → sublevelStage xs a ≤ j.val := by
  refine ⟨birth_lt_sublevelStage xs h r hr a ha.1, ?_⟩
  intro j hj
  have hd := ha.2
  rw [returned_death_grade xs r hr j hj] at hd
  change a < (xs.get j).2 at hd
  by_contra hn
  have hi : j.val < sublevelStage xs a := by omega
  exact (not_le_of_gt hd) ((grade_le_iff_index_lt_stage xs h a j).mpr hi)

/-- An alive queried class has exactly its original birth-face unit coordinate. -/
theorem sublevelClass_coordinate (xs : Input) (h : Valid xs)
    (r : Representative xs.length) (hr : r ∈ representedOccurrences xs)
    (a : ℤ) (ha : r.occurrence.AliveAt a) :
    letI := faceFintype xs h
    (sublevelHomologyToAlive xs h r.occurrence.degree a
      (sublevelClass xs h r hr a ha.1)).1 =
      Pi.single ((finCongr (faceCount_eq_length xs h)).symm r.birthIndex) (1 : ZMod 2) := by
  let := faceFintype xs h
  have hb := aliveAt_prefix_bounds xs h r hr a ha
  rw [sublevelHomologyToAlive_class]
  let t : Fin (xs.length + 1) :=
    ⟨sublevelStage xs a, Nat.lt_succ_of_le (sublevelStage_le_length xs a)⟩
  rw [prefixCycleAfterBirth_eq_representedCycle xs h r hr t hb.1 hb.2]
  exact representedClass_coordinate xs h r hr t hb.1 hb.2

theorem sublevelClass_nonzero (xs : Input) (h : Valid xs)
    (r : Representative xs.length) (hr : r ∈ representedOccurrences xs)
    (a : ℤ) (ha : r.occurrence.AliveAt a) : sublevelClass xs h r hr a ha.1 ≠ 0 := by
  let := faceFintype xs h
  intro hz
  have hc := sublevelClass_coordinate xs h r hr a ha
  rw [hz, map_zero] at hc
  have hone : (1 : ZMod 2) = 0 := by
    simpa using (congrFun hc ((finCongr (faceCount_eq_length xs h)).symm r.birthIndex)).symm
  exact one_ne_zero hone

private theorem included_chain_coordinates (xs : Input) (h : Valid xs)
    (p s : ℕ) (a : ℤ) (hs : s ≤ sublevelStage xs a)
    (v : Fin xs.length → ZMod 2) (hpre : PrefixSupported s v)
    (hdeg : Homogeneous (degree xs) p v) :
    letI := faceFintype xs h
    (prefixChainEquiv (ZMod 2) (compatibleOrder xs h) (sublevelStage xs a) p
      (chainIncl (ZMod 2) (sublevel_eq_prefix xs h a).le p
        (chainIncl (ZMod 2) (prefix_le_sublevel xs h a s hs) p
          (simplicialChain xs h p s v hpre hdeg)))).1 = faceVector xs h v := by
  let := faceFintype xs h
  rw [← LinearMap.comp_apply, ← chainIncl_comp]
  have hc := congrArg Subtype.val (LinearMap.congr_fun
    (prefixChainEquiv_inclusion (ZMod 2) (compatibleOrder xs h) s
      (sublevelStage xs a) p hs) (simplicialChain xs h p s v hpre hdeg))
  change (prefixChainEquiv _ _ (sublevelStage xs a) p _).1 =
    (prefixChainEquiv _ _ s p _).1 at hc
  exact hc.trans (simplicialChain_coordinates xs h p s v hpre hdeg)

/-- The actual returned filling in a sublevel at or above its finite death.
Its coordinates are those of the returned bounding support, not a new witness chain. -/
theorem sublevel_bounding (xs : Input) (h : Valid xs)
    (r : Representative xs.length) (hr : r ∈ representedOccurrences xs)
    (j : Fin xs.length) (hj : r.deathIndex = some j)
    (a : ℤ) (ha : r.occurrence.birth ≤ a) (hja : (xs.get j).2 ≤ a) :
    letI := faceFintype xs h
    ∃ b, r.bounding = some b ∧
      ∃ B : Chain ((gradeFilter xs h).sublevel a) (ZMod 2) (r.occurrence.degree + 1),
        (prefixChainEquiv (ZMod 2) (compatibleOrder xs h) (sublevelStage xs a)
          (r.occurrence.degree + 1)
          (chainIncl (ZMod 2) (sublevel_eq_prefix xs h a).le
            (r.occurrence.degree + 1) B)).1 = faceVector xs h (chainVector b) ∧
        TDA.Simplicial.boundary ((gradeFilter xs h).sublevel a) (ZMod 2)
          r.occurrence.degree B = (sublevelCycle xs h r hr a ha).1 := by
  let := faceFintype xs h
  have ht : j.val + 1 ≤ sublevelStage xs a :=
    Nat.succ_le_of_lt ((grade_le_iff_index_lt_stage xs h a j).mp hja)
  have hbirth : r.birthIndex.val < j.val + 1 :=
    Nat.lt_succ_of_lt (returned_birth_lt_death xs h r hr j hj)
  obtain ⟨b, hb, hpre, hdeg, hboundary⟩ := returned_simplicial_bounding xs h r hr j hj
  let B₀ := simplicialChain xs h (r.occurrence.degree + 1) (j.val + 1)
    (chainVector b) hpre hdeg
  let hi := prefix_le_sublevel xs h a (j.val + 1) ht
  refine ⟨b, hb, chainIncl (ZMod 2) hi (r.occurrence.degree + 1) B₀,
    included_chain_coordinates xs h _ _ a ht _ hpre hdeg, ?_⟩
  have hcomm := LinearMap.congr_fun (boundary_chainIncl (ZMod 2) hi r.occurrence.degree) B₀
  change TDA.Simplicial.boundary _ _ _ _ =
    chainIncl (ZMod 2) hi r.occurrence.degree (TDA.Simplicial.boundary _ _ _ B₀) at hcomm
  rw [hcomm, hboundary]
  have hz : simplicialCycle xs h r.occurrence.degree (j.val + 1) (chainVector r.cycle)
      (returned_death_cycle xs h r hr j hj) =
      prefixCycleAfterBirth xs h r hr (j.val + 1) hbirth := rfl
  rw [hz]
  exact congrArg Subtype.val (sublevelCycle_of_prefix xs h r hr a ha _ hbirth ht)

private noncomputable abbrev cyclesQuotient (K : PreAbstractSimplicialComplex ℕ) (p : ℕ) :
    HasQuotient (simplicialCycles K (ZMod 2) p)
      (Submodule (ZMod 2) (simplicialCycles K (ZMod 2) p)) :=
  Submodule.hasQuotient (R := ZMod 2) (M := simplicialCycles K (ZMod 2) p)
attribute [local instance] cyclesQuotient

private theorem class_zero_of_filling (K : PreAbstractSimplicialComplex ℕ) (p : ℕ)
    (z : simplicialCycles K (ZMod 2) p) (B : Chain K (ZMod 2) (p + 1))
    (hB : TDA.Simplicial.boundary K (ZMod 2) p B = z.1) :
    simplicialHomologyClass (ZMod 2) K p z = 0 := by
  let E := (homologyKernelQuotient.{0,0,0} (ZMod 2)
    (simplicialChainComplex K (ZMod 2)) p).toLinearEquiv
  have hq : (simplicialBoundaries K (ZMod 2) p).mkQ z = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr
    ((mem_simplicialBoundaries_iff (ZMod 2) K p z).mpr ⟨B, hB⟩)
  have hE : E (simplicialHomologyClass (ZMod 2) K p z) = 0 :=
    (simplicialHomologyClass_quotient (ZMod 2) K p z).trans hq
  exact (LinearEquiv.map_eq_zero_iff E).mp hE

/-- The class is zero at and after finite death, through the actual returned filling. -/
theorem sublevelClass_eq_zero_of_death (xs : Input) (h : Valid xs)
    (r : Representative xs.length) (hr : r ∈ representedOccurrences xs)
    (d : ℤ) (hd : r.occurrence.death = .finite d)
    (a : ℤ) (ha : r.occurrence.birth ≤ a) (hda : d ≤ a) :
    sublevelClass xs h r hr a ha = 0 := by
  obtain ⟨j, hj, hjd⟩ := returned_deathIndex_of_finite xs r hr d hd
  obtain ⟨b, _, B, _, hB⟩ := sublevel_bounding xs h r hr j hj a ha (hjd.trans_le hda)
  exact class_zero_of_filling _ _ (sublevelCycle xs h r hr a ha) B hB

/-- Exactly the half-open value interval, rather than the index interval, detects nonzero class. -/
theorem sublevelClass_nonzero_iff (xs : Input) (h : Valid xs)
    (r : Representative xs.length) (hr : r ∈ representedOccurrences xs)
    (a : ℤ) (ha : r.occurrence.birth ≤ a) :
    sublevelClass xs h r hr a ha ≠ 0 ↔ r.occurrence.AliveAt a := by
  constructor
  · intro hn
    refine ⟨ha, ?_⟩
    cases hd : r.occurrence.death with
    | essential => trivial
    | finite d =>
      by_contra hnot
      exact hn (sublevelClass_eq_zero_of_death xs h r hr d hd a ha (le_of_not_gt hnot))
  · intro halive
    exact sublevelClass_nonzero xs h r hr a halive

end TDA.Persistence.Reduction.FiniteInput
