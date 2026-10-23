import TDA.Persistence.DecoratedRectangleCells
import Mathlib.Analysis.BoxIntegral.Box.Basic

/-!
# Ordinary box preimages of decorated rectangles

Pairing the minus cuts at two real coordinates takes the preimage of a decorated
rectangle to its ordinary half-open box. Consequently finite covers, disjointness and
inclusions of decorated rectangles induce genuine box partitions. This step retains the
decorated point space; it only provides the finite-tiling adapter.
-/

namespace TDA.Persistence.RectangleMeasure

open BoxIntegral Set

/-- The ordinary box with the two coordinate intervals of a decorated rectangle. -/
def rectangleBox (a b c d : ℝ) (hab : a < b) (hcd : c < d) : Box (Fin 2) where
  lower := ![a, c]
  upper := ![b, d]
  lower_lt_upper := by intro i; fin_cases i <;> assumption

/-- Select the minus decoration at each ordinary coordinate. -/
noncomputable def minusCutPair (x : Fin 2 → ℝ) : Cut ℝ × Cut ℝ := (minusCut (x 0), minusCut (x 1))

/-- The preimage of a decorated rectangle is the actual ordinary half-open box. -/
theorem preimage_rectangleCell (a b c d : ℝ) (hab : a < b) (hcd : c < d) :
    minusCutPair ⁻¹' rectangleCell a b c d = (rectangleBox a b c d hab hcd : Set (Fin 2 → ℝ)) := by
  ext x
  simp [rectangleCell, cutCell, minusCutPair, minusCut, Box.mem_def,
    rectangleBox, Fin.forall_fin_two]

/-- A box gives the decorated rectangle with the same endpoints. -/
def boxRectangleCell (I : Box (Fin 2)) : Set (Cut ℝ × Cut ℝ) :=
  rectangleCell (I.lower 0) (I.upper 0) (I.lower 1) (I.upper 1)

/-- Box recovery from decorated-cell preimages needs no classification of arbitrary cuts. -/
theorem preimage_boxRectangleCell (I : Box (Fin 2)) :
    minusCutPair ⁻¹' boxRectangleCell I = (I : Set (Fin 2 → ℝ)) := by
  ext x
  simp [boxRectangleCell, rectangleCell, cutCell, minusCutPair, minusCut, Box.mem_def,
    Fin.forall_fin_two]

/-- Distinct ordinary boxes determine distinct decorated rectangles. -/
theorem boxRectangleCell_injective : Function.Injective boxRectangleCell := by
  intro I J h
  apply Box.injective_coe
  rw [← preimage_boxRectangleCell I, ← preimage_boxRectangleCell J, h]

/-- Every box rectangle is nonempty. -/
theorem boxRectangleCell_nonempty (I : Box (Fin 2)) : (boxRectangleCell I).Nonempty :=
  ⟨minusCutPair I.upper, by
    have h : I.upper ∈ (I : Set (Fin 2 → ℝ)) := I.upper_mem
    rw [← preimage_boxRectangleCell I] at h
    exact h⟩

/-- Every nonempty separated rectangle has a unique ordinary box representing its endpoints. -/
theorem exists_boxRectangleCell {U : Set (Cut ℝ × Cut ℝ)}
    (hU : U ∈ separatedRectangleCells) (hne : U ≠ ∅) :
    ∃ I : Box (Fin 2), I.upper 0 < I.lower 1 ∧ U = boxRectangleCell I := by
  rcases hU with hU | ⟨a, b, c, d, hab, hbc, hcd, rfl⟩
  · exact (hne hU).elim
  · exact ⟨rectangleBox a b c d hab hcd, hbc, rfl⟩

end TDA.Persistence.RectangleMeasure
