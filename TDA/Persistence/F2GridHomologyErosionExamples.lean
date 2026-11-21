import TDA.Persistence.F2GridHomologyErosion
import TDA.Persistence.F2GridHomologyInputExamples
import TDA.Persistence.Reduction.FiniteInputSublevelBasis

/-!
# The triangle against its translate: radius zero fails, radius one half passes

Degree-one homology of `triangle` (vertices and edges at the origin, 2-face at `(2, 2)`)
against `shiftedTriangle` (the same grading translated by `(1/2, 0)`):

* at the origin the actual first Betti numbers are one and zero, computed from the hollow slice
  and the empty slice;
* the run at radius zero reports the failure at the origin, first input wide, with ranks one and
  zero, which is the first comparable pair the test enumerates; these are the actual ranks
  (`triangle_violation_zero`), so `RankErosion` fails at radius zero;
* the grade-error bound gives `RankErosion` at radius `1/2`, so the run passes there;
* hence the actual erosion distance lies in `(0, 1/2]` and is at most the interleaving distance;
* an invalid first input, an invalid second input and a negative radius are reported
  separately.

In this file the kernel evaluates (`decide +kernel`) the reduction of the hollow slice at the
origin, the start of the breakpoint enumeration at radius zero, the face lists and the grade
differences, and `rfl` closes the reduction of the empty slice and the rank comparison at the
origin. The slices at the origin and the validity of the inputs are the kernel-checked facts of
`F2GridHomologyInputExamples`. The Betti numbers and executable ranks follow from
`toF2GridRep_dim` and `toF2GridRep_rankAt` of `F2GridHomologyIso`, and the remaining
conclusions from the theorems of `F2GridHomologyErosion`.
-/

set_option autoImplicit false

namespace TDA.Persistence.F2GridHomologyErosionExamples

open TDA.Persistence RatGradedInput RatGrid F2GridRep F2GridHomologyInputExamples
open TDA.Persistence.Reduction
open scoped NNReal ENNReal

private def hollowSliceMatrix : Matrix (Fin 6) (Fin 6) (ZMod 2) := fun r c =>
  if c.val = 3 then (if r.val = 0 ∨ r.val = 1 then 1 else 0)
  else if c.val = 4 then (if r.val = 0 ∨ r.val = 2 then 1 else 0)
  else if c.val = 5 then (if r.val = 1 ∨ r.val = 2 then 1 else 0)
  else 0

private def hollowSlice : FiniteInput.Input :=
  [({0}, 0), ({1}, 0), ({2}, 0), ({0, 1}, 0), ({0, 2}, 0), ({1, 2}, 0)]

private theorem hollowSlice_boundary : FiniteInput.boundary hollowSlice = hollowSliceMatrix := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [FiniteInput.boundary, hollowSlice, hollowSliceMatrix, Finset.orderEmbOfFin_apply,
      Finset.sort_insert, Finset.sort_singleton] <;> decide +kernel

private theorem hollowSlice_active :
    (FiniteInput.activeRepresentatives hollowSlice 1 0).length = 1 := by
  unfold FiniteInput.activeRepresentatives FiniteInput.representedOccurrences
    FiniteInput.pairedRepresentative FiniteInput.essentialRepresentative
    FiniteInput.pairedVector FiniteInput.essentialVector FiniteInput.change
    FiniteInput.essentialIndices FiniteInput.pivotPairs FiniteInput.reduced FiniteInput.trace
  rw [hollowSlice_boundary]
  decide +kernel

/-- At the origin the actual first Betti number of `triangle` is one. -/
theorem triangle_finrank_origin :
    Module.finrank (ZMod 2)
      ((homology triangle triangle_valid 1).obj (realGrade (![0, 0] : Fin 2 → ℚ))) = 1 := by
  rw [← toF2GridRep_dim triangle_valid 1]
  change (FiniteInput.activeRepresentatives (slice triangle (![0, 0] : Fin 2 → ℚ)) 1 0).length = 1
  rw [triangle_slice_origin]
  exact hollowSlice_active

/-- At the origin the actual first Betti number of `shiftedTriangle` is zero. -/
theorem shiftedTriangle_finrank_origin :
    Module.finrank (ZMod 2)
      ((homology shiftedTriangle shiftedTriangle_valid 1).obj
        (realGrade (![0, 0] : Fin 2 → ℚ))) = 0 := by
  rw [← toF2GridRep_dim shiftedTriangle_valid 1]
  change (FiniteInput.activeRepresentatives
    (slice shiftedTriangle (![0, 0] : Fin 2 → ℚ)) 1 0).length = 0
  rw [shiftedTriangle_slice_origin]
  rfl

private theorem rankOfStructureMap_eq_finrank {M : PModule.{0,0,0} (ZMod 2) (Fin 2 → ℝ)}
    {a b c : Fin 2 → ℝ} (ha : a = c) (hb : b = c) (h : a ≤ b) :
    rankOfStructureMap M h = Module.finrank (ZMod 2) (M.obj c) := by
  subst ha
  subst hb
  unfold rankOfStructureMap
  rw [structureMapLinear_self, LinearMap.range_id, finrank_top]

/-- **The named violation at radius zero.** At the origin, the widened rank of the actual
first homology of `triangle` is one and the rank of that of `shiftedTriangle` is zero. -/
theorem triangle_violation_zero :
    rankOfStructureMap (homology triangle triangle_valid 1)
        (erosionWide_le (radius 0 le_rfl) (le_refl (realGrade (![0, 0] : Fin 2 → ℚ)))) = 1 ∧
      rankOfStructureMap (homology shiftedTriangle shiftedTriangle_valid 1)
        (le_refl (realGrade (![0, 0] : Fin 2 → ℚ))) = 0 := by
  constructor
  · have h0 : radius 0 le_rfl = 0 := NNReal.eq (by simp)
    rw [rankOfStructureMap_eq_finrank (by rw [h0, erosionLower_zero])
      (by rw [h0, erosionUpper_zero]),
      triangle_finrank_origin]
  · rw [rankOfStructureMap_eq_finrank rfl rfl, shiftedTriangle_finrank_origin]

/-- Radius zero fails for the actual first homology modules. -/
theorem triangle_not_rankErosion_zero :
    ¬ RankErosion (radius 0 le_rfl) (homology triangle triangle_valid 1)
      (homology shiftedTriangle shiftedTriangle_valid 1) := by
  rintro ⟨h, -⟩
  have hle := h _ _ (le_refl (realGrade (![0, 0] : Fin 2 → ℚ)))
  rw [triangle_violation_zero.1, triangle_violation_zero.2] at hle
  exact absurd hle (by decide)

private theorem breakpoints_zero_pointList :
    (erosionBreakpoints (gridValues triangle) (gridValues shiftedTriangle) 0).pointList =
      (![0, 0] : Fin 2 → ℚ) :: [![0, 2], ![2, 0], ![2, 2], ![1 / 2, 0], ![1 / 2, 2], ![5 / 2, 0],
        ![5 / 2, 2]] := by
  decide +kernel

private theorem triangle_rankAt_origin :
    (toF2GridRep triangle 1).rankAt (lower 0 (![0, 0] : Fin 2 → ℚ))
      (upper 0 (![0, 0] : Fin 2 → ℚ)) = 1 := by
  have hl : lower 0 (![0, 0] : Fin 2 → ℚ) = ![0, 0] := by funext i; simp [lower]
  have hu : upper 0 (![0, 0] : Fin 2 → ℚ) = ![0, 0] := by funext i; simp [upper]
  rw [hl, hu, toF2GridRep_rankAt triangle_valid 1 le_rfl,
    rankOfStructureMap_eq_finrank rfl rfl, triangle_finrank_origin]

private theorem shiftedTriangle_rankAt_origin :
    (toF2GridRep shiftedTriangle 1).rankAt (![0, 0] : Fin 2 → ℚ) ![0, 0] = 0 := by
  rw [toF2GridRep_rankAt shiftedTriangle_valid 1 le_rfl,
    rankOfStructureMap_eq_finrank rfl rfl, shiftedTriangle_finrank_origin]

/-- **The reported witness at radius zero.** The run at radius zero reports the failure at the
origin in the direction "first wide": the widened rank of `triangle` is one, the rank of
`shiftedTriangle` is zero. This is the first comparable pair the test enumerates. -/
theorem triangle_runErosion_zero :
    runErosion triangle shiftedTriangle 1 0 =
      .fail ⟨true, (![0, 0] : Fin 2 → ℚ), (![0, 0] : Fin 2 → ℚ), 1, 0⟩ := by
  have hat : erosionFailureAt (toF2GridRep triangle 1) (toF2GridRep shiftedTriangle 1) 0
      (![0, 0] : Fin 2 → ℚ) ![0, 0] = some ⟨true, ![0, 0], ![0, 0], 1, 0⟩ := by
    unfold erosionFailureAt
    rw [triangle_rankAt_origin, shiftedTriangle_rankAt_origin]
    rfl
  have hv₁ : (toF2GridRep triangle 1).values = gridValues triangle := by unfold toF2GridRep; rfl
  have hv₂ : (toF2GridRep shiftedTriangle 1).values = gridValues shiftedTriangle := by
    unfold toF2GridRep; rfl
  have he : erosionFailure? (toF2GridRep triangle 1) (toF2GridRep shiftedTriangle 1) 0 =
      some ⟨true, ![0, 0], ![0, 0], 1, 0⟩ := by
    simp only [erosionFailure?, hv₁, hv₂, breakpoints_zero_pointList, List.findSome?_cons,
      le_refl, ↓reduceIte, hat]
  unfold RatGradedInput.runErosion
  rw [ite_eq_right_of_eq_false _ _ (eq_false (not_not.mpr triangle_valid)),
    ite_eq_right_of_eq_false _ _ (eq_false (not_not.mpr shiftedTriangle_valid)),
    ite_eq_right_of_eq_false _ _ (eq_false (lt_irrefl 0)), he]

/-- Every grade of `triangle` and the grade of the same face in `shiftedTriangle` differ by at
most `1/2` in each coordinate. -/
theorem triangle_grade_error :
    ∀ e ∈ triangle, ∀ f ∈ shiftedTriangle, e.1 = f.1 → ∀ i, |e.2 i - f.2 i| ≤ 1 / 2 := by
  decide +kernel

/-- Radius `1/2` holds for the actual first homology modules, from the grade-error bound. -/
theorem triangle_rankErosion_half :
    RankErosion (radius (1 / 2) (by norm_num)) (homology triangle triangle_valid 1)
      (homology shiftedTriangle shiftedTriangle_valid 1) :=
  rankErosion_homology_of_faces_eq triangle_valid shiftedTriangle_valid (by decide +kernel) 1
    _ triangle_grade_error

/-- **Radius `1/2` passes.** -/
theorem triangle_runErosion_half_pass : runErosion triangle shiftedTriangle 1 (1 / 2) = .pass :=
  runErosion_eq_pass_of_faces_eq triangle_valid shiftedTriangle_valid (by decide +kernel) 1
    (by norm_num) triangle_grade_error

/-- The two outcomes bound the actual erosion distance: zero is strictly below it, it is at
most `1/2`, and it is at most the interleaving distance. -/
theorem triangle_rankErosionDistance_bounds :
    (0 : ℝ≥0∞) < rankErosionDistance (homology triangle triangle_valid 1)
        (homology shiftedTriangle shiftedTriangle_valid 1) ∧
      rankErosionDistance (homology triangle triangle_valid 1)
          (homology shiftedTriangle shiftedTriangle_valid 1) ≤
        ((radius (1 / 2) (by norm_num) : ℝ≥0) : ℝ≥0∞) ∧
      rankErosionDistance (homology triangle triangle_valid 1)
          (homology shiftedTriangle shiftedTriangle_valid 1) ≤
        coordinateInterleavingDistance (homology triangle triangle_valid 1)
          (homology shiftedTriangle shiftedTriangle_valid 1) := by
  obtain ⟨_, _, _, _, hlt, hle⟩ := runErosion_eq_fail_certificate triangle_runErosion_zero
  obtain ⟨_, _, _, _, _, hpass, _⟩ := runErosion_eq_pass_certificate triangle_runErosion_half_pass
  refine ⟨lt_of_le_of_lt (le_of_eq ?_) hlt, hpass, hle⟩
  exact (ENNReal.coe_eq_zero.mpr (NNReal.eq (by simp))).symm

/-- Invalid first input is reported as such, before the radius is inspected. -/
theorem nonMonotone_runErosion : runErosion nonMonotone triangle 1 (-1) = .invalidFirst :=
  (runErosion_eq_invalidFirst_iff _ _ _ _).mpr nonMonotone_not_valid

/-- Invalid second input is reported as such. -/
theorem triangle_nonMonotone_runErosion :
    runErosion triangle nonMonotone 1 0 = .invalidSecond :=
  (runErosion_eq_invalidSecond_iff _ _ _ _).mpr ⟨triangle_valid, nonMonotone_not_valid⟩

/-- A negative radius on valid input is reported separately. -/
theorem triangle_runErosion_negative :
    runErosion triangle shiftedTriangle 1 (-1) = .negativeRadius :=
  (runErosion_eq_negativeRadius_iff _ _ _ _).mpr
    ⟨triangle_valid, shiftedTriangle_valid, by norm_num⟩

end TDA.Persistence.F2GridHomologyErosionExamples
