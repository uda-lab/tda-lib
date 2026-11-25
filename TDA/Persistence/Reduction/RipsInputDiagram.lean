import TDA.Persistence.Reduction.RipsInput
import TDA.Persistence.SublevelDiagramVertexMap
import TDA.Persistence.DiagramMap
import TDA.Persistence.RipsGromovHausdorff
import TDA.Persistence.FiniteFilterStability

/-!
# The diagram of the executed Rips simplex list

For a valid `DistanceTable`, the list `ripsInput` of
`TDA.Persistence.Reduction.RipsInput` presents the Rips filtration of the table metric with
the labels `0, …, N - 1` placed in `ℕ` and integer grades. This module compares the executed
list with the Rips filtration of `Rips.filter (D.metric hD)` on `Rips.fullComplex (Fin N)`,
in homology and in the diagrams.

* `intCastOrderEmbedding`: the inclusion of the integers in the real numbers as an order
  embedding, along which `Diagram.map` reads integer grades as real numbers.
* `mem_sublevel_gradeFilter_ripsInput`, `mem_sublevel_rips_filter`: the faces of the executed
  list at an integer threshold, and of the Rips filtration at a real threshold, are the
  nonempty sets of labels of integer diameter at most the threshold.
* `outputDiagram_ripsInput`: `FiniteInput.outputDiagram` of the executed list, mapped along
  `intCastOrderEmbedding`, is `dgm (ZMod 2) (Rips.filter (D.metric hD))` in every degree.
* `ripsLabelMap`: the inclusion of the labels as a vertex map from the Rips complex at an
  integer threshold to the sublevel complex of the executed list. It induces an isomorphism
  in homology in every degree and over every ring
  (`simplicialHomologyMap_ripsLabelMap_isIso`), compatible with raising the threshold
  (`simplicialHomologyMap_ripsLabelMap_naturality`).
* `ripsRunInDegree`: the occurrence records of one degree of `ripsRun`; `none` for an invalid
  table in every degree, also where a valid table would have no record.
  `ripsRunInDegree_correct` reads a returned list as the points of the Rips diagram.
* `valid_of_relabel`, `outputDiagram_ripsInput_of_relabel`: a permutation of the labels of a
  valid table gives a valid table with the same diagram of the executed list.

## Statements

`outputDiagram_ripsInput` composes `FiniteInput.outputDiagram_eq_dgm`, `dgm_map` and
`dgm_eq_of_vertexMaps`, with `Fin.val` in one direction and, for a nonempty set of labels, a
left inverse `ℕ → Fin N` in the other; a table without labels has no face on either side.
Multiplicities, the deletion of pairs of equal grades, essential classes and unaugmented
degree zero are those of `FiniteInput.outputDiagram_eq_dgm`. The comparison is with the Rips
filtration of the metric built from the table: the caller supplies no metric, isomorphism or
certificate.

The homology comparison is stated at integer thresholds. All values of both filters are
integers, so the Rips complex at a real threshold is the one at its floor; the diagram
equality covers every pair of real thresholds.

`ripsRunInDegree p` is `none` exactly when the table is invalid, whatever `p`.
`ripsRunInDegree_correct` compares multisets; the order of the records is that of the
existing reduction and is not part of the comparison. The relabelling statement is an
equality of diagrams, not of lists, and reuses `Rips.dgm_eq_of_isometryEquiv`.

## Cost

`ripsRunInDegree` costs `ripsRun` and one comparison of natural numbers for each record; there
are at most `2 ^ N - 1` records. The cost of the existing reduction is not bounded here. The
semantic statements use the noncomputable homology API.

These are elementary library results, not attributed to a source. See
`docs/math/finite-ph-computation.md`.
-/

set_option autoImplicit false

namespace TDA.Persistence

/-- The inclusion of the integers in the real numbers, as an order embedding. -/
def intCastOrderEmbedding : ℤ ↪o ℝ := OrderEmbedding.ofStrictMono (↑) Int.cast_strictMono

@[simp] theorem intCastOrderEmbedding_apply (a : ℤ) : intCastOrderEmbedding a = (a : ℝ) := rfl

private theorem Diagram.map_injective {α β : Type*} [LinearOrder α] [LinearOrder β]
    (φ : α ↪o β) {d e : Diagram α} (h : d.map φ = e.map φ) : d = e := by
  apply Diagram.ext
  have hp := congrArg Diagram.points h
  rw [Diagram.map_points, Diagram.map_points] at hp
  exact Multiset.map_injective
    (Function.Injective.prodMap φ.injective (WithTop.map_injective φ.injective)) hp

end TDA.Persistence

namespace TDA.Persistence.Reduction

open TDA.Simplicial TDA.Filtration TDA.Persistence CategoryTheory

namespace DistanceTable

variable {N : ℕ} (D : DistanceTable N)

/-! ## Sublevel complexes -/

/-- The faces of the Rips filtration of the table metric at a real threshold. -/
theorem mem_sublevel_rips_filter (hD : D.Valid) {r : ℝ} {s : Finset (Fin N)} :
    s ∈ (Rips.filter (D.metric hD)).sublevel r ↔ s.Nonempty ∧ (D.diameter s : ℝ) ≤ r := by
  rw [FilterFunction.mem_sublevel_iff]
  constructor
  · rintro ⟨hs, hle⟩
    exact ⟨hs, by rw [D.cast_diameter hD]; exact hle⟩
  · rintro ⟨hs, hle⟩
    exact ⟨hs, by rw [Rips.filter_value, ← D.cast_diameter hD]; exact hle⟩

private theorem mem_sublevel_map_gradeFilter {r : ℝ} {t : Finset ℕ} :
    t ∈ ((FiniteInput.gradeFilter D.ripsInput D.ripsInput_valid).map
        intCastOrderEmbedding).sublevel r ↔
      ∃ s : Finset (Fin N), s.Nonempty ∧ (D.diameter s : ℝ) ≤ r ∧
        t = s.map Fin.valEmbedding := by
  rw [FilterFunction.mem_sublevel_iff]
  constructor
  · rintro ⟨ht, hle⟩
    obtain ⟨s, hs, rfl⟩ := D.mem_complex_ripsInput.1 ht
    refine ⟨s, hs, ?_, rfl⟩
    rw [← D.gradeFilter_ripsFace_eq_diameter ⟨s, hs⟩]
    exact hle
  · rintro ⟨s, hs, hle, rfl⟩
    refine ⟨(D.ripsFace ⟨s, hs⟩).2, ?_⟩
    rw [← D.gradeFilter_ripsFace_eq_diameter ⟨s, hs⟩] at hle
    exact hle

/-- The faces of the executed list at an integer threshold: the sets of labels of integer
diameter at most the threshold. -/
theorem mem_sublevel_gradeFilter_ripsInput {a : ℤ} {t : Finset ℕ} :
    t ∈ (FiniteInput.gradeFilter D.ripsInput D.ripsInput_valid).sublevel a ↔
      ∃ s : Finset (Fin N), s.Nonempty ∧ D.diameter s ≤ a ∧ t = s.map Fin.valEmbedding := by
  rw [← FilterFunction.map_sublevel_apply _ intCastOrderEmbedding a, mem_sublevel_map_gradeFilter]
  simp only [intCastOrderEmbedding_apply, Int.cast_le]

/-- A left inverse of the inclusion of the labels, for a nonempty set of labels. -/
private def clamp (hN : 0 < N) (n : ℕ) : Fin N := if h : n < N then ⟨n, h⟩ else ⟨0, hN⟩

private theorem clamp_val (hN : 0 < N) (i : Fin N) : clamp hN i.val = i := by
  simp [clamp]

private theorem image_clamp (hN : 0 < N) (s : Finset (Fin N)) :
    (s.map Fin.valEmbedding).image (clamp hN) = s := by
  ext i
  simp only [Finset.mem_image, Finset.mem_map, Fin.valEmbedding_apply]
  constructor
  · rintro ⟨_, ⟨j, hj, rfl⟩, rfl⟩
    rwa [clamp_val]
  · intro hi
    exact ⟨i.val, ⟨i, hi, rfl⟩, clamp_val hN i⟩

/-! ## The diagram -/

/-- The diagram of the executed list, with grades read as real numbers, is the F₂ diagram of
the Rips filtration of the table metric, in every degree. -/
theorem outputDiagram_ripsInput (hD : D.Valid) (p : ℕ) :
    (FiniteInput.outputDiagram D.ripsInput p).map intCastOrderEmbedding =
      dgm (ZMod 2) (Rips.filter (D.metric hD)) p := by
  let _ := FiniteInput.faceFintype D.ripsInput D.ripsInput_valid
  rw [FiniteInput.outputDiagram_eq_dgm D.ripsInput D.ripsInput_valid p, ← dgm_map]
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have : IsEmpty (TotalFace (Rips.fullComplex (Fin 0))) :=
      ⟨fun s => by obtain ⟨i, -⟩ := s.2; exact i.elim0⟩
    have : IsEmpty (TotalFace (FiniteInput.complex D.ripsInput D.ripsInput_valid)) :=
      ⟨fun t => by obtain ⟨s, -⟩ := D.ripsFace_bijective.2 t; exact isEmptyElim s⟩
    apply Diagram.ext
    rw [dgm_empty_faces, dgm_empty_faces]
  · refine dgm_eq_of_vertexMaps (ZMod 2) _ _ (clamp hN) Fin.val ?_ ?_ ?_ ?_ p
    · intro r t ht
      obtain ⟨s, hs, hle, rfl⟩ := D.mem_sublevel_map_gradeFilter.1 ht
      rw [image_clamp]
      exact (D.mem_sublevel_rips_filter hD).2 ⟨hs, hle⟩
    · intro r s hs
      obtain ⟨hne, hle⟩ := (D.mem_sublevel_rips_filter hD).1 hs
      exact D.mem_sublevel_map_gradeFilter.2
        ⟨s, hne, hle, (Finset.map_eq_image Fin.valEmbedding s).symm⟩
    · intro t ht v hv
      obtain ⟨s, -, rfl⟩ := D.mem_complex_ripsInput.1 ht
      obtain ⟨i, -, rfl⟩ := Finset.mem_map.1 hv
      exact congrArg Fin.val (clamp_val hN i)
    · intro s _ i _
      exact clamp_val hN i

/-! ## Sublevel homology -/

/-- The inclusion of the labels, as a vertex map from the Rips complex of the table metric at
an integer threshold to the sublevel complex of the executed list. -/
def ripsLabelMap (hD : D.Valid) (a : ℤ) :
    VertexMap ((Rips.filter (D.metric hD)).sublevel (a : ℝ))
      ((FiniteInput.gradeFilter D.ripsInput D.ripsInput_valid).sublevel a) where
  toFun := Fin.val
  map_face s hs := by
    obtain ⟨hne, hle⟩ := (D.mem_sublevel_rips_filter hD).1 hs
    have hi : s.image Fin.val = s.map Fin.valEmbedding :=
      (Finset.map_eq_image Fin.valEmbedding s).symm
    have h := D.mem_sublevel_gradeFilter_ripsInput.2 ⟨s, hne, Int.cast_le.1 hle, hi⟩
    convert h

@[simp] theorem ripsLabelMap_apply (hD : D.Valid) (a : ℤ) (i : Fin N) :
    D.ripsLabelMap hD a i = i.val := rfl

private def clampMap (hD : D.Valid) (hN : 0 < N) (a : ℤ) :
    VertexMap ((FiniteInput.gradeFilter D.ripsInput D.ripsInput_valid).sublevel a)
      ((Rips.filter (D.metric hD)).sublevel (a : ℝ)) where
  toFun := clamp hN
  map_face t ht := by
    obtain ⟨s, hs, hle, rfl⟩ := D.mem_sublevel_gradeFilter_ripsInput.1 ht
    have h := (D.mem_sublevel_rips_filter hD).2 ⟨hs, Int.cast_le.2 hle⟩
    rw [← image_clamp hN s] at h
    convert h

/-- The inclusion of the labels induces an isomorphism from the homology of the Rips complex
of the table metric at an integer threshold to the sublevel homology of the executed list,
in every degree and over every ring. -/
theorem simplicialHomologyMap_ripsLabelMap_isIso (R : Type*) [Ring R] (hD : D.Valid) (a : ℤ)
    (n : ℕ) : IsIso (simplicialHomologyMap R (D.ripsLabelMap hD a) n) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have hX : Limits.IsZero
        (simplicialHomology ((Rips.filter (D.metric hD)).sublevel (a : ℝ)) R n) := by
      have hbot : (Rips.filter (D.metric hD)).sublevel (a : ℝ) = ⊥ :=
        le_antisymm (fun s hs => by
          obtain ⟨⟨i, -⟩, -⟩ := (D.mem_sublevel_rips_filter hD).1 hs
          exact i.elim0) bot_le
      rw [hbot]
      exact isZero_simplicialHomology_bot R n
    have hY : Limits.IsZero (simplicialHomology
        ((FiniteInput.gradeFilter D.ripsInput D.ripsInput_valid).sublevel a) R n) := by
      have hbot : (FiniteInput.gradeFilter D.ripsInput D.ripsInput_valid).sublevel a = ⊥ :=
        le_antisymm (fun t ht => by
          obtain ⟨s, ⟨i, -⟩, -⟩ := D.mem_sublevel_gradeFilter_ripsInput.1 ht
          exact i.elim0) bot_le
      rw [hbot]
      exact isZero_simplicialHomology_bot R n
    exact ⟨⟨0, hX.eq_of_src _ _, hY.eq_of_src _ _⟩⟩
  · refine ⟨⟨simplicialHomologyMap R (D.clampMap hD hN a) n, ?_, ?_⟩⟩
    · exact simplicialHomologyMap_comp_eq_id R _ _ (fun s _ i _ => clamp_val hN i) n
    · refine simplicialHomologyMap_comp_eq_id R _ _ (fun t ht v hv => ?_) n
      obtain ⟨s, -, -, rfl⟩ := D.mem_sublevel_gradeFilter_ripsInput.1 ht
      obtain ⟨i, -, rfl⟩ := Finset.mem_map.1 hv
      exact congrArg Fin.val (clamp_val hN i)

/-- The isomorphisms of `simplicialHomologyMap_ripsLabelMap_isIso` commute with the maps
induced by raising the threshold. -/
theorem simplicialHomologyMap_ripsLabelMap_naturality (R : Type*) [Ring R] (hD : D.Valid)
    {a b : ℤ} (hab : a ≤ b) (n : ℕ) :
    simplicialHomologyIncl R
          ((Rips.filter (D.metric hD)).sublevel_mono (Int.cast_le.2 hab)) n ≫
        simplicialHomologyMap R (D.ripsLabelMap hD b) n =
      simplicialHomologyMap R (D.ripsLabelMap hD a) n ≫
        simplicialHomologyIncl R
          ((FiniteInput.gradeFilter D.ripsInput D.ripsInput_valid).sublevel_mono hab) n := by
  rw [← simplicialHomologyMap_inclusion, ← simplicialHomologyMap_inclusion,
    ← simplicialHomologyMap_comp, ← simplicialHomologyMap_comp]
  rfl

/-! ## The records of one degree -/

/-- The occurrence records of degree `p` in the run of a valid table; `none` for an invalid
table, in every degree. -/
def ripsRunInDegree (p : ℕ) : Option (List FiniteInput.Occurrence) :=
  D.ripsRun.map (List.filter fun o => o.degree = p)

theorem ripsRunInDegree_eq_some_iff {p : ℕ} {out : List FiniteInput.Occurrence} :
    D.ripsRunInDegree p = some out ↔
      D.Valid ∧ out = (FiniteInput.occurrences D.ripsInput).filter fun o => o.degree = p := by
  unfold ripsRunInDegree ripsRun
  by_cases h : D.Valid <;> simp [h, eq_comm]

theorem ripsRunInDegree_eq_none_iff {p : ℕ} : D.ripsRunInDegree p = none ↔ ¬ D.Valid := by
  unfold ripsRunInDegree
  rw [Option.map_eq_none_iff, ripsRun_eq_none_iff]

/-- A returned list of records of degree `p` certifies the table and lists, with
multiplicity, the points of the F₂ diagram of the Rips filtration of the table metric in
degree `p`. -/
theorem ripsRunInDegree_correct {p : ℕ} {out : List FiniteInput.Occurrence}
    (h : D.ripsRunInDegree p = some out) :
    ∃ hD : D.Valid, (dgm (ZMod 2) (Rips.filter (D.metric hD)) p).points =
      ((out : Multiset FiniteInput.Occurrence).map FiniteInput.Occurrence.point).map
        fun q => ((q.1 : ℝ), WithTop.map (Int.cast : ℤ → ℝ) q.2) := by
  obtain ⟨hD, rfl⟩ := D.ripsRunInDegree_eq_some_iff.1 h
  refine ⟨hD, ?_⟩
  rw [← D.outputDiagram_ripsInput hD p, Diagram.map_points]
  rfl

/-! ## Relabelling -/

/-- A table obtained from a valid table by a permutation of the labels is valid. -/
theorem valid_of_relabel {D E : DistanceTable N} (σ : Equiv.Perm (Fin N))
    (h : ∀ i j, E.dist i j = D.dist (σ i) (σ j)) (hD : D.Valid) : E.Valid := by
  refine ⟨fun i j => ?_, fun i j => ?_, fun i => ?_, fun i j hij => ?_, fun i j k => ?_⟩
  · rw [h]
    exact hD.1 _ _
  · rw [h, h]
    exact hD.2.1 _ _
  · rw [h]
    exact hD.2.2.1 _
  · rw [h]
    exact hD.2.2.2.1 _ _ (σ.injective.ne hij)
  · rw [h, h, h]
    exact hD.2.2.2.2 _ _ _

/-- Relabelling a valid table does not change the diagram of the executed list, in any
degree. -/
theorem outputDiagram_ripsInput_of_relabel {D E : DistanceTable N} (σ : Equiv.Perm (Fin N))
    (h : ∀ i j, E.dist i j = D.dist (σ i) (σ j)) (hD : D.Valid) (p : ℕ) :
    FiniteInput.outputDiagram E.ripsInput p = FiniteInput.outputDiagram D.ripsInput p := by
  have hE := valid_of_relabel σ h hD
  apply Diagram.map_injective intCastOrderEmbedding
  rw [E.outputDiagram_ripsInput hE p, D.outputDiagram_ripsInput hD p]
  let e : @IsometryEquiv (Fin N) (Fin N)
      (E.metric hE).toPseudoMetricSpace.toPseudoEMetricSpace
      (D.metric hD).toPseudoMetricSpace.toPseudoEMetricSpace :=
    @IsometryEquiv.mk (Fin N) (Fin N) (E.metric hE).toPseudoMetricSpace.toPseudoEMetricSpace
      (D.metric hD).toPseudoMetricSpace.toPseudoEMetricSpace σ
      (@Isometry.of_dist_eq (Fin N) (Fin N) (E.metric hE).toPseudoMetricSpace
        (D.metric hD).toPseudoMetricSpace σ fun i j => by
          change ((D.dist (σ i) (σ j) : ℤ) : ℝ) = ((E.dist i j : ℤ) : ℝ)
          rw [h])
  exact @Rips.dgm_eq_of_isometryEquiv (Fin N) (Fin N) _ _ _ _ (E.metric hE) (D.metric hD)
    (ZMod 2) _ e p

end DistanceTable

end TDA.Persistence.Reduction
