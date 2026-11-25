import TDA.Sheaf.AlternatingDecomposition

/-!
# Fixtures for alternating diagrams

On the three-vertex fork `0 → 1 ← 2`, the interval sums of `[0, 2] + {1}` and of
`[0, 1] + [1, 2]` have the same dimension vector `(1, 2, 1)` and the same ranks of both
arrows, yet different barcodes, so they are not isomorphic: arrow ranks do not determine the
decomposition. Repeated summands keep their multiplicity, the zero diagram has the empty barcode,
and the sink reflection at the middle vertex kills the singleton summand and keeps `[0, 2]`.
-/

universe u

namespace TDA.Sheaf.AlternatingDiagramExamples

open CategoryTheory Limits TDA.Persistence TDA.Sheaf.AlternatingDiagram
open ZeroObject

variable {k : Type u} [Field k]

/-- The fork `0 → 1 ← 2`. -/
def fork : Fin 2 → Bool := ![true, false]

/-- The whole fork `[0, 2]`. -/
def whole : FiniteInterval 3 := ⟨0, 3, by decide, le_rfl⟩

/-- The middle vertex `{1}`. -/
def middle : FiniteInterval 3 := ⟨1, 2, by decide, by decide⟩

/-- The left edge `[0, 1]`. -/
def leftEdge : FiniteInterval 3 := ⟨0, 2, by decide, by decide⟩

/-- The right edge `[1, 2]`. -/
def rightEdge : FiniteInterval 3 := ⟨1, 3, by decide, le_rfl⟩

theorem arrow_zero_one : Arrow fork 0 1 := ⟨0, by decide, by decide⟩

theorem arrow_two_one : Arrow fork 2 1 := ⟨1, by decide, by decide⟩

/-- `[0, 2] + {1}`: both outer vectors map to the same line. -/
noncomputable abbrev crossing : Diagram k fork := intervalSum fork [whole, middle]

/-- `[0, 1] + [1, 2]`: the outer vectors map to independent lines. -/
noncomputable abbrev split : Diagram k fork := intervalSum fork [leftEdge, rightEdge]

theorem finrank_crossing_eq_split (j : Fin 3) :
    Module.finrank k ((crossing (k := k)).obj (vtx fork j)) =
      Module.finrank k ((split (k := k)).obj (vtx fork j)) := by
  rw [finrank_intervalSum_obj, finrank_intervalSum_obj]
  fin_cases j <;> decide

theorem finrank_crossing_middle :
    Module.finrank k ((crossing (k := k)).obj (vtx fork 1)) = 2 := by
  rw [finrank_intervalSum_obj]; decide

theorem rank_left_crossing_eq_split :
    Module.finrank k (LinearMap.range ((crossing (k := k)).map (gen arrow_zero_one)).hom) =
      Module.finrank k (LinearMap.range ((split (k := k)).map (gen arrow_zero_one)).hom) := by
  rw [finrank_range_intervalSum_map, finrank_range_intervalSum_map]; decide

theorem rank_right_crossing_eq_split :
    Module.finrank k (LinearMap.range ((crossing (k := k)).map (gen arrow_two_one)).hom) =
      Module.finrank k (LinearMap.range ((split (k := k)).map (gen arrow_two_one)).hom) := by
  rw [finrank_range_intervalSum_map, finrank_range_intervalSum_map]; decide

theorem rank_left_crossing :
    Module.finrank k (LinearMap.range ((crossing (k := k)).map (gen arrow_zero_one)).hom) = 1 := by
  rw [finrank_range_intervalSum_map]; decide

theorem barcode_crossing : barcode (crossing (k := k)) = {whole, middle} :=
  barcode_intervalSum _ _

theorem barcode_split : barcode (split (k := k)) = {leftEdge, rightEdge} :=
  barcode_intervalSum _ _

/-- Equal dimensions and equal arrow ranks, but no isomorphism. -/
theorem not_nonempty_iso_crossing_split : ¬ Nonempty (crossing (k := k) ≅ split) := by
  rw [nonempty_iso_iff_barcode_eq, barcode_crossing, barcode_split]
  decide

/-- A repeated summand keeps its multiplicity. -/
theorem multiplicity_repeated :
    intervalMultiplicity (intervalSum (k := k) fork [middle, whole, middle]) middle = 2 := by
  unfold intervalMultiplicity
  rw [barcode_intervalSum]
  decide

/-- The zero diagram has the empty barcode. -/
theorem barcode_zero : barcode (0 : Diagram k fork) = 0 :=
  barcode_eq_zero_of_isZero _ (isZero_zero _)

theorem isSink_one : IsSink fork 1 := by
  intro j ⟨a, ha, _⟩
  fin_cases a <;> revert ha <;> decide

/-- Reflecting the crossing at the middle sink kills `{1}` and keeps `[0, 2]`. -/
theorem barcode_reflectSink_crossing :
    barcode ((reflectSink (flipAt fork 1) isSink_one (isFlipAt_flipAt fork 1)).obj
      (crossing (k := k))) = {whole} := by
  rw [barcode_eq_of_iso_intervalSum _ (reflectSinkIntervalSumIso _ _ _)]
  decide

end TDA.Sheaf.AlternatingDiagramExamples
