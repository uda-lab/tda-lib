import TDA.Persistence.MatchingInterleavingDistance

/-!
# Matching distance and constructible transport boundary examples

The examples retain repeated finite bars, an empty matching type caused by essential
cardinality mismatch, and a nonzero module presented on grids of different sizes.
-/

set_option autoImplicit false

namespace TDA.Persistence.MatchingInterleavingDistanceExamples

open CategoryTheory CategoryTheory.Limits FiniteConstructible RealBarcode
open scoped NNReal ENNReal ZeroObject Classical

private noncomputable def emptyDiagram : Diagram ℝ := orderedQ 0 0 (Fin.elim0, Fin.elim0)
private noncomputable def copies : Diagram ℝ := orderedQ 2 0 (fun _ => (0, 2), Fin.elim0)
private noncomputable def essentialDiagram : Diagram ℝ := orderedQ 0 1 (Fin.elim0, fun _ => 0)

private theorem empty_positive : emptyDiagram.IsPositive := by
  rw [emptyDiagram, orderedQ_isPositive_iff]
  exact fun i => Fin.elim0 i

private theorem copies_positive : copies.IsPositive := by
  rw [copies, orderedQ_isPositive_iff]
  intro i
  norm_num

private theorem essential_positive : essentialDiagram.IsPositive := by
  rw [essentialDiagram, orderedQ_isPositive_iff]
  exact fun i => Fin.elim0 i

/-- Empty barcodes have zero interleaving distance, without a nonemptiness premise. -/
theorem empty_distance :
    realInterleavingDistance (realize (k := ℚ) emptyDiagram) (realize emptyDiagram) = 0 :=
  realInterleavingDistance_self _

/-- Both repeated bars may be deleted at the exact length `2ε` boundary. -/
theorem duplicate_deletion_bound :
    realInterleavingDistance (realize (k := ℚ) copies) (realize emptyDiagram) ≤ 1 := by
  have hp : bottleneck copies emptyDiagram = 1 := by
    rw [bottleneck_eq_presentation copies emptyDiagram
      (fun _ : Fin 2 => (0, 2)) (Fin.elim0 : Fin 0 → ℝ × ℝ)
      (Fin.elim0 : Fin 0 → ℝ) (Fin.elim0 : Fin 0 → ℝ)]
    · rw [presentationBottleneck_constant_empty]
      norm_num [diagonalCost]
    · simp [copies, finitePart_orderedQ]
      rfl
    · simp [emptyDiagram, finitePart_orderedQ]
    · simp [copies, essentialPart_orderedQ]
    · simp [emptyDiagram, essentialPart_orderedQ]
  exact (RealBarcode.distance_le_bottleneck copies emptyDiagram copies_positive
    empty_positive).trans_eq hp

/-- Essential cardinality mismatch gives an empty matching type. -/
theorem essential_matching_empty : IsEmpty (OccurrenceMatching essentialDiagram.finiteOccurrences
    emptyDiagram.finiteOccurrences essentialDiagram.essentialOccurrences
    emptyDiagram.essentialOccurrences) := by
  apply not_nonempty_iff.mp
  rw [occurrenceMatching_nonempty_iff]
  simp [Diagram.essentialOccurrences, essentialDiagram, emptyDiagram, essentialPart_orderedQ]

/-- The one-sided inequality includes infinite bottleneck without deleting an essential bar. -/
theorem essential_mismatch_bound : bottleneck essentialDiagram emptyDiagram = ⊤ ∧
    realInterleavingDistance (realize (k := ℚ) essentialDiagram) (realize emptyDiagram) ≤
      bottleneck essentialDiagram emptyDiagram := by
  refine ⟨(bottleneck_eq_top_iff _ _).mpr ?_,
    RealBarcode.distance_le_bottleneck _ _ essential_positive empty_positive⟩
  simp [essentialDiagram, emptyDiagram, essentialPart_orderedQ]

private def oneGrid : Fin 1 ↪o ℝ where
  toFun _ := 0
  inj' _ _ _ := Subsingleton.elim _ _
  map_rel_iff' := by intro i j; simp [Subsingleton.elim i j]

private def twoGrid : Fin 2 ↪o ℝ :=
  OrderEmbedding.ofStrictMono (fun i : Fin 2 => (i.val : ℝ))
    (by intro i j h; change (i.val : ℝ) < (j.val : ℝ); exact_mod_cast (show i.val < j.val from h))

private noncomputable def constantRationals : PModule.{0,0,0} ℚ ℝ :=
  (Functor.const ℝ).obj (ModuleCat.of ℚ ℚ)

private noncomputable def step : PModule.{0,0,0} ℚ ℝ :=
  reindex (cellIndex oneGrid) (sample oneGrid constantRationals)

private theorem one_constructible : IsConstructible oneGrid step :=
  isConstructible_reindex oneGrid _ (isZero_zero (ModuleCat ℚ))

private theorem coarse_cells {s t : ℝ} (h : cellIndex twoGrid s = cellIndex twoGrid t) :
    cellIndex oneGrid s = cellIndex oneGrid t := by
  have hzGrid : twoGrid 0 ≤ s ↔ twoGrid 0 ≤ t := by
    rw [← lt_cellIndex_iff, ← lt_cellIndex_iff, h]
  have hzero : twoGrid 0 = 0 := by
    change ((0 : ℕ) : ℝ) = 0
    norm_num
  have hz : 0 ≤ s ↔ 0 ≤ t := by simpa only [hzero] using hzGrid
  by_cases hs : 0 ≤ s
  · rw [cellIndex_of_last_le oneGrid s hs, cellIndex_of_last_le oneGrid t (hz.mp hs)]
  · have ht : t < 0 := lt_of_not_ge (fun ht => hs (hz.mpr ht))
    rw [(cellIndex_eq_zero_iff oneGrid s).mpr (fun _ => lt_of_not_ge hs),
      (cellIndex_eq_zero_iff oneGrid t).mpr (fun _ => ht)]

private theorem two_constructible : IsConstructible twoGrid step where
  zero_left t ht := one_constructible.zero_left t (fun _ => by
    change t < 0
    have h := ht 0
    change t < ((0 : ℕ) : ℝ) at h
    simpa using h)
  isIso_map s t h heq := one_constructible.isIso_map s t h (coarse_cells heq)

private theorem step_finite (t : ℝ) : FiniteDimensional ℚ (step.obj t) := by
  change FiniteDimensional ℚ ((sample oneGrid constantRationals).obj (cellIndex oneGrid t))
  by_cases ht : 0 ≤ t
  · rw [cellIndex_of_last_le oneGrid t ht]
    change FiniteDimensional ℚ ℚ
    infer_instance
  · rw [(cellIndex_eq_zero_iff oneGrid t).mpr (fun _ => lt_of_not_ge ht)]
    change FiniteDimensional ℚ (0 : ModuleCat ℚ)
    have : Subsingleton (0 : ModuleCat ℚ) :=
      ModuleCat.isZero_iff_subsingleton.mp (isZero_zero (ModuleCat ℚ))
    infer_instance

/-- The differing-grid consumer has a nonzero fiber at its critical birth. -/
theorem different_grids_nonzero : ¬ IsZero (step.obj 0) := by
  change ¬ IsZero ((sample oneGrid constantRationals).obj (cellIndex oneGrid 0))
  rw [show cellIndex oneGrid 0 = 1 from cellIndex_critical oneGrid 0]
  change ¬ IsZero (ModuleCat.of ℚ ℚ)
  rw [ModuleCat.isZero_iff_subsingleton]
  exact not_subsingleton ℚ

/-- The module inequality accepts one and two critical values for the same nonzero module. -/
theorem different_grid_bound : realInterleavingDistance step step ≤
    bottleneck (moduleDiagram oneGrid step (fun i => step_finite (oneGrid i)))
      (moduleDiagram twoGrid step (fun j => step_finite (twoGrid j))) :=
  FiniteConstructible.distance_le_bottleneck oneGrid twoGrid step step
    one_constructible two_constructible _ _

private def emptyGrid : Fin 0 ↪o ℝ :=
  ⟨⟨Fin.elim0, fun i => Fin.elim0 i⟩, fun {i} => Fin.elim0 i⟩

private theorem zero_constructible : IsConstructible emptyGrid (0 : PModule.{0,0,0} ℚ ℝ) :=
  (isConstructible_empty_iff emptyGrid _).mpr
    (fun t => (isZero_zero (PModule.{0,0,0} ℚ ℝ)).obj t)

/-- The constructible capstone also covers zero modules on empty grids. -/
theorem empty_grid_bound : realInterleavingDistance (0 : PModule.{0,0,0} ℚ ℝ) 0 ≤
    bottleneck (moduleDiagram (k := ℚ) emptyGrid 0 (fun i => Fin.elim0 i))
      (moduleDiagram (k := ℚ) emptyGrid 0 (fun i => Fin.elim0 i)) :=
  FiniteConstructible.distance_le_bottleneck (k := ℚ) emptyGrid emptyGrid 0 0
    zero_constructible zero_constructible _ _

/-- An explicit empty occurrence matching transports a zero-parameter witness to modules. -/
noncomputable def empty_grid_witness : RealInterleaving 0 (0 : PModule.{0,0,0} ℚ ℝ) 0 := by
  let D := moduleDiagram (k := ℚ) emptyGrid (0 : PModule.{0,0,0} ℚ ℝ) (fun i => Fin.elim0 i)
  have hD : D.points = 0 := moduleDiagram_empty_grid emptyGrid _
  haveI : IsEmpty D.finiteOccurrences := by
    change IsEmpty (finitePart D.points)
    refine ⟨fun i => ?_⟩
    have hi := Multiset.coe_mem (x := i)
    simp [hD, finitePart] at hi
  haveI : IsEmpty D.essentialOccurrences := by
    change IsEmpty (essentialPart D.points)
    refine ⟨fun i => ?_⟩
    have hi := Multiset.coe_mem (x := i)
    simp [hD, essentialPart] at hi
  let matching : OccurrenceMatching D.finiteOccurrences D.finiteOccurrences
      D.essentialOccurrences D.essentialOccurrences :=
    ⟨fun _ => none, by simp, Equiv.refl _⟩
  apply FiniteConstructible.matchingInterleaving emptyGrid emptyGrid 0 0
    zero_constructible zero_constructible (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
    0 matching
  simp [OccurrenceMatching.cost, matching]

end TDA.Persistence.MatchingInterleavingDistanceExamples
