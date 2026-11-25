import TDA.Persistence.Reduction.RipsInputDiagram
import TDA.Persistence.Reduction.RipsInputExamples
import TDA.Persistence.SublevelDiagramMonotone

/-!
# Diagrams of executed Rips simplex lists

The tables are those of `TDA.Persistence.Reduction.RipsInputExamples`.

* `empty`, `single`, `pair`: the records of each degree and the Rips diagram in degree zero.
  A valid table has the empty list of records in a degree without classes.
* `fourCycle`: the kernel-checked reduction of the fifteen faces. One class of degree one is
  born at `1` and dies at `2`; three classes of degree zero die at `1` and one is essential;
  the pairs of equal grade `2` leave no record. The Rips diagram of the table metric in degree
  one is the single point `(1, 2)`, the Rips complex at threshold `1` has one-dimensional
  first homology over `ZMod 2` and the complex at threshold `2` has none, and the first
  homology of the listed complex at threshold `1` is one-dimensional as well.
* `oneWay`, `merged`, `shortcut`, `loop`, `negative`: `none` in every degree.
* `line`, `relabelled`: equal diagrams of the executed lists in every degree.

The boundary matrix of the four-cycle is evaluated through `faceIncidence`, which the kernel
reduces, in place of `FiniteInput.boundary`.
-/

set_option autoImplicit false

namespace TDA.Persistence.Reduction.RipsInputDiagramExamples

open DistanceTable FiniteInput RipsInputExamples TDA.Simplicial TDA.Filtration TDA.Persistence
open CategoryTheory

/-! ## Small tables -/

theorem empty_valid : empty.Valid := by decide +kernel

theorem empty_ripsRunInDegree (p : ℕ) : empty.ripsRunInDegree p = some [] := by
  rw [ripsRunInDegree, empty_ripsRun]
  rfl

/-- The Rips diagram of the empty metric space has no point, in any degree. -/
theorem empty_dgm (p : ℕ) :
    (dgm (ZMod 2) (Rips.filter (empty.metric empty_valid)) p).points = 0 := by
  obtain ⟨_, h⟩ := empty.ripsRunInDegree_correct (empty_ripsRunInDegree p)
  rw [h]
  rfl

theorem single_valid : single.Valid := by decide +kernel

theorem single_ripsRunInDegree_zero :
    single.ripsRunInDegree 0 = some [⟨0, 0, .essential⟩] := by
  rw [ripsRunInDegree, single_ripsRun]
  rfl

/-- One point: one essential class of degree zero, not reduced. -/
theorem single_dgm_zero :
    (dgm (ZMod 2) (Rips.filter (single.metric single_valid)) 0).points =
      {((0 : ℝ), (⊤ : WithTop ℝ))} := by
  obtain ⟨_, h⟩ := single.ripsRunInDegree_correct single_ripsRunInDegree_zero
  rw [h]
  simp [Occurrence.point]

theorem pair_ripsRunInDegree_zero :
    pair.ripsRunInDegree 0 = some [⟨0, 0, .finite 3⟩, ⟨0, 0, .essential⟩] := by
  rw [ripsRunInDegree, pair_ripsRun]
  rfl

/-- A valid table has the empty list of records in a degree without classes. -/
theorem pair_ripsRunInDegree_one : pair.ripsRunInDegree 1 = some [] := by
  rw [ripsRunInDegree, pair_ripsRun]
  rfl

/-- Two points at distance `3`: one class dies at `3` and one is essential. -/
theorem pair_dgm_zero :
    (dgm (ZMod 2) (Rips.filter (pair.metric pair_valid)) 0).points =
      {((0 : ℝ), ((3 : ℝ) : WithTop ℝ)), ((0 : ℝ), (⊤ : WithTop ℝ))} := by
  obtain ⟨_, h⟩ := pair.ripsRunInDegree_correct pair_ripsRunInDegree_zero
  rw [h]
  simp only [Occurrence.point, Multiset.map_coe, List.map_cons, WithTop.coe_ofNat,
    List.map_nil, Int.cast_zero, WithTop.map_ofNat, Int.cast_ofNat, WithTop.map_top,
    Multiset.insert_eq_cons]
  rfl

/-! ## The four-cycle -/

/-- The indicator of the codimension-one faces among the listed faces. -/
private def faceIncidence (xs : Input) : Matrix (Fin xs.length) (Fin xs.length) (ZMod 2) :=
  fun i j =>
    if (xs.get j).1.card = (xs.get i).1.card - 1 + 2 ∧ (xs.get i).1 ⊆ (xs.get j).1 ∧
      (xs.get i).1.Nonempty then 1 else 0

/-- Over `ZMod 2` the boundary matrix is the indicator of the codimension-one faces. -/
private theorem boundary_eq_faceIncidence (xs : Input) : boundary xs = faceIncidence xs := by
  funext i j
  unfold FiniteInput.boundary faceIncidence
  generalize (xs.get i).1 = s
  generalize (xs.get j).1 = t
  have hone : ∀ a : ℕ, (-1 : ZMod 2) ^ a = 1 := fun a => by
    rw [show (-1 : ZMod 2) = 1 from by decide, one_pow]
  by_cases hc : t.card = s.card - 1 + 2
  · simp only [hc, ↓reduceDIte, true_and, hone]
    by_cases hs : s ⊆ t ∧ s.Nonempty
    · simp only [hs, and_self, ↓reduceIte]
      obtain ⟨hst, hne⟩ := hs
      have hcard : (t \ s).card = 1 := by
        rw [Finset.card_sdiff_of_subset hst]
        have := hne.card_pos
        omega
      obtain ⟨v, hv⟩ := Finset.card_eq_one.1 hcard
      have hmem : ∀ x, x ∈ t ∧ x ∉ s ↔ x = v := fun x => by
        rw [← Finset.mem_sdiff, hv, Finset.mem_singleton]
      obtain ⟨a₀, ha₀⟩ : v ∈ Set.range (t.orderEmbOfFin hc) := by
        rw [Finset.range_orderEmbOfFin]
        exact ((hmem v).2 rfl).1
      have hiff : ∀ a, t.erase (t.orderEmbOfFin hc a) = s ↔ a = a₀ := by
        intro a
        constructor
        · intro he
          apply (t.orderEmbOfFin hc).injective
          rw [ha₀]
          exact (hmem _).1 ⟨Finset.orderEmbOfFin_mem t hc a, fun h =>
            Finset.notMem_erase _ _ ((Finset.ext_iff.1 he _).2 h)⟩
        · rintro rfl
          rw [ha₀]
          ext x
          rw [Finset.mem_erase]
          constructor
          · rintro ⟨hx, hxt⟩
            by_contra hxs
            exact hx ((hmem x).1 ⟨hxt, hxs⟩)
          · intro hxs
            exact ⟨fun hx => ((hmem x).2 hx).2 hxs, hst hxs⟩
      simp only [hiff, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    · simp only [hs, ↓reduceIte]
      apply Finset.sum_eq_zero
      intro a _
      have hne : t.erase (t.orderEmbOfFin hc a) ≠ s := by
        intro he
        apply hs
        refine ⟨he ▸ Finset.erase_subset _ _, ?_⟩
        rw [← Finset.card_pos, ← he,
          Finset.card_erase_of_mem (Finset.orderEmbOfFin_mem t hc a)]
        omega
      simp only [hne, ↓reduceIte]
  · simp only [hc, ↓reduceDIte, false_and, ↓reduceIte]

/-- The simplex list of `fourCycle`. -/
def fourCycleInput : Input :=
  [({0}, 0), ({1}, 0), ({2}, 0), ({3}, 0),
    ({0, 1}, 1), ({0, 3}, 1), ({1, 2}, 1), ({2, 3}, 1),
    ({0, 2}, 2), ({1, 3}, 2),
    ({0, 1, 2}, 2), ({0, 1, 3}, 2), ({0, 2, 3}, 2), ({1, 2, 3}, 2),
    ({0, 1, 2, 3}, 2)]

theorem fourCycle_ripsInput_eq : fourCycle.ripsInput = fourCycleInput :=
  ((ripsInput?_eq_some_iff _).1 fourCycle_ripsInput).2.symm

/-- The matrix over `ZMod 2` on the fifteen faces with the given rows of nonzero entries in
each column. -/
def columnMatrix (cols : List (List ℕ)) :
    Matrix (Fin fourCycleInput.length) (Fin fourCycleInput.length) (ZMod 2) := fun r c =>
  if r.val ∈ cols.getD c.val [] then 1 else 0

/-- The boundary matrix: each edge has its two vertices, each triangle its three edges and
the tetrahedron its four triangles. -/
def fourCycleBoundary : Matrix (Fin fourCycleInput.length) (Fin fourCycleInput.length) (ZMod 2) :=
  columnMatrix [[], [], [], [], [0, 1], [0, 3], [1, 2], [2, 3], [0, 2], [1, 3],
    [4, 6, 8], [4, 5, 9], [5, 7, 8], [6, 7, 9], [10, 11, 12, 13]]

/-- The reduced matrix: the columns of the fourth edge, of both diagonals and of the last
triangle are zero. -/
def fourCycleReduced : Matrix (Fin fourCycleInput.length) (Fin fourCycleInput.length) (ZMod 2) :=
  columnMatrix [[], [], [], [], [0, 1], [0, 3], [1, 2], [], [], [],
    [4, 6, 8], [4, 5, 9], [4, 5, 6, 7], [], [10, 11, 12, 13]]

theorem fourCycle_boundary : boundary fourCycleInput = fourCycleBoundary := by
  rw [boundary_eq_faceIncidence]
  decide +kernel

/-- The existing reducer, run by the kernel on the fifteen faces. -/
theorem fourCycle_reduced : reduced fourCycleInput = fourCycleReduced := by
  simp only [reduced, trace]
  rw [fourCycle_boundary]
  decide +kernel

theorem fourCycle_pivotPairs : pivotPairs fourCycleInput =
    [(⟨1, by decide⟩, ⟨4, by decide⟩), (⟨3, by decide⟩, ⟨5, by decide⟩),
      (⟨2, by decide⟩, ⟨6, by decide⟩), (⟨8, by decide⟩, ⟨10, by decide⟩),
      (⟨9, by decide⟩, ⟨11, by decide⟩), (⟨7, by decide⟩, ⟨12, by decide⟩),
      (⟨13, by decide⟩, ⟨14, by decide⟩)] := by
  simp only [pivotPairs]
  rw [fourCycle_reduced]
  decide +kernel

theorem fourCycle_essentialIndices : essentialIndices fourCycleInput = [⟨0, by decide⟩] := by
  simp only [essentialIndices]
  rw [fourCycle_reduced, fourCycle_pivotPairs]
  decide +kernel

/-- The records of the four-cycle: three classes of degree zero die at `1`, one class of
degree one is born at `1` and dies at `2`, and one class of degree zero is essential. The
three pairs of equal grade `2` leave no record. -/
theorem fourCycle_ripsRun : fourCycle.ripsRun = some
    [⟨0, 0, .finite 1⟩, ⟨0, 0, .finite 1⟩, ⟨0, 0, .finite 1⟩, ⟨1, 1, .finite 2⟩,
      ⟨0, 0, .essential⟩] := by
  rw [ripsRun_eq_some_iff, fourCycle_ripsInput_eq]
  refine ⟨fourCycle_valid, ?_⟩
  simp only [occurrences, finiteOccurrences, essentialOccurrences, fourCycle_pivotPairs,
    fourCycle_essentialIndices]
  decide +kernel

theorem fourCycle_ripsRunInDegree_zero : fourCycle.ripsRunInDegree 0 = some
    [⟨0, 0, .finite 1⟩, ⟨0, 0, .finite 1⟩, ⟨0, 0, .finite 1⟩, ⟨0, 0, .essential⟩] := by
  rw [ripsRunInDegree, fourCycle_ripsRun]
  rfl

theorem fourCycle_ripsRunInDegree_one :
    fourCycle.ripsRunInDegree 1 = some [⟨1, 1, .finite 2⟩] := by
  rw [ripsRunInDegree, fourCycle_ripsRun]
  rfl

theorem fourCycle_ripsRunInDegree_two : fourCycle.ripsRunInDegree 2 = some [] := by
  rw [ripsRunInDegree, fourCycle_ripsRun]
  rfl

/-- The Rips diagram of the four-cycle metric in degree one: one class, born at `1` and
dead at `2`. -/
theorem fourCycle_dgm_one :
    (dgm (ZMod 2) (Rips.filter (fourCycle.metric fourCycle_valid)) 1).points =
      {((1 : ℝ), ((2 : ℝ) : WithTop ℝ))} := by
  obtain ⟨_, h⟩ := fourCycle.ripsRunInDegree_correct fourCycle_ripsRunInDegree_one
  rw [h]
  simp [Occurrence.point]

/-- The Rips diagram of the four-cycle metric in degree zero, with multiplicity three and
the essential class. -/
theorem fourCycle_dgm_zero :
    (dgm (ZMod 2) (Rips.filter (fourCycle.metric fourCycle_valid)) 0).points =
      Multiset.replicate 3 ((0 : ℝ), ((1 : ℝ) : WithTop ℝ)) + {((0 : ℝ), (⊤ : WithTop ℝ))} := by
  obtain ⟨_, h⟩ := fourCycle.ripsRunInDegree_correct fourCycle_ripsRunInDegree_zero
  rw [h]
  simp only [Occurrence.point, Multiset.map_coe, List.map_cons, WithTop.coe_one, List.map_nil,
    Int.cast_zero, WithTop.map_one, Int.cast_one, WithTop.map_top, Multiset.replicate_succ,
    Multiset.replicate_zero, Multiset.cons_zero, Multiset.cons_add, Multiset.singleton_add]
  rfl

/-- The Rips diagram of the four-cycle metric has no point in degree two. -/
theorem fourCycle_dgm_two :
    (dgm (ZMod 2) (Rips.filter (fourCycle.metric fourCycle_valid)) 2).points = 0 := by
  obtain ⟨_, h⟩ := fourCycle.ripsRunInDegree_correct fourCycle_ripsRunInDegree_two
  rw [h]
  rfl

/-- The class is present at `1`: the Rips complex of the four-cycle metric at threshold `1`
has one-dimensional first homology over `ZMod 2`. -/
theorem fourCycle_finrank_one :
    Module.finrank (ZMod 2) (simplicialHomology
      ((Rips.filter (fourCycle.metric fourCycle_valid)).sublevel 1) (ZMod 2) 1) = 1 := by
  rw [finrank_sublevelHomology_eq_countP, fourCycle_dgm_one, Multiset.countP_eq_card_filter,
    Multiset.filter_singleton]
  norm_num

/-- The class is filled at `2`: the Rips complex at threshold `2` has no first homology. -/
theorem fourCycle_finrank_two :
    Module.finrank (ZMod 2) (simplicialHomology
      ((Rips.filter (fourCycle.metric fourCycle_valid)).sublevel 2) (ZMod 2) 1) = 0 := by
  rw [finrank_sublevelHomology_eq_countP, fourCycle_dgm_one, Multiset.countP_eq_card_filter,
    Multiset.filter_singleton]
  norm_num

/-- The first homology of the listed complex at threshold `1` is one-dimensional, by the
isomorphism induced by the inclusion of the labels. -/
theorem fourCycle_listed_finrank_one :
    Module.finrank (ZMod 2) (simplicialHomology
      ((gradeFilter fourCycle.ripsInput fourCycle.ripsInput_valid).sublevel 1) (ZMod 2) 1) =
        1 := by
  have := fourCycle.simplicialHomologyMap_ripsLabelMap_isIso (ZMod 2) fourCycle_valid 1 1
  rw [← (asIso (simplicialHomologyMap (ZMod 2)
    (fourCycle.ripsLabelMap fourCycle_valid 1) 1)).toLinearEquiv.finrank_eq]
  have h := fourCycle_finrank_one
  rw [show ((1 : ℤ) : ℝ) = 1 from Int.cast_one]
  exact h

/-! ## Invalid tables -/

theorem oneWay_ripsRunInDegree (p : ℕ) : oneWay.ripsRunInDegree p = none :=
  oneWay.ripsRunInDegree_eq_none_iff.2 (by decide +kernel)

theorem merged_ripsRunInDegree (p : ℕ) : merged.ripsRunInDegree p = none :=
  merged.ripsRunInDegree_eq_none_iff.2 (by decide +kernel)

/-- The table violating the triangle inequality is rejected in every degree, also in the
degrees in which three points have no class. -/
theorem shortcut_ripsRunInDegree (p : ℕ) : shortcut.ripsRunInDegree p = none :=
  shortcut.ripsRunInDegree_eq_none_iff.2 (by decide +kernel)

theorem loop_ripsRunInDegree (p : ℕ) : loop.ripsRunInDegree p = none :=
  loop.ripsRunInDegree_eq_none_iff.2 (by decide +kernel)

theorem negative_ripsRunInDegree (p : ℕ) : negative.ripsRunInDegree p = none :=
  negative.ripsRunInDegree_eq_none_iff.2 (by decide +kernel)

/-- Executed in a degree in which a valid table of three labels has no record. -/
theorem shortcut_ripsRunInDegree_five : shortcut.ripsRunInDegree 5 = none := by
  decide +kernel

/-! ## Relabelling -/

theorem line_valid : line.Valid := by decide +kernel

/-- The table with two labels exchanged has the same diagram in every degree. -/
theorem relabelled_outputDiagram (p : ℕ) :
    outputDiagram relabelled.ripsInput p = outputDiagram line.ripsInput p :=
  outputDiagram_ripsInput_of_relabel (Equiv.swap 0 1) relabelled_dist line_valid p

end TDA.Persistence.Reduction.RipsInputDiagramExamples
