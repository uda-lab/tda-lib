import TDA.Persistence.AlphaRadiusStability
import TDA.Persistence.DiagramBottleneckLaws
import TDA.Persistence.Reduction.AlphaInput
import TDA.Persistence.Reduction.RipsInputDiagramExamples

set_option autoImplicit false

/-!
# Radius and squared bottleneck distances for two squares

Move each corner of the square with coordinates `(±7, ±7)` to the matching corner at
`(±8, ±8)`. The α reducer gives one finite H₁ bar over F₂ in each cloud. Its squared
endpoints are `(49, 98)` and `(64, 128)`; taking square roots gives the radius endpoints.
-/

namespace TDA.Persistence.AlphaRadiusStabilityExamples

open TDA.Filtration TDA.Simplicial RationalAlpha Reduction Reduction.AlphaInput
open scoped Matrix

/-- Four rational corners in cyclic label order. -/
def corners (a : ℚ) : Fin 4 → RationalAlpha.Point := ![(-a, -a), (a, -a), (a, a), (-a, a)]

/-- The square with half-side seven. -/
def smallSquare : Fin 4 ↪ RationalAlpha.Point := ⟨corners 7, by decide +kernel⟩

/-- The square with half-side eight. -/
def largeSquare : Fin 4 ↪ RationalAlpha.Point := ⟨corners 8, by decide +kernel⟩

private def expected (a : ℚ) : List Occurrence :=
  [⟨0, 0, .finite (a ^ 2)⟩, ⟨0, 0, .finite (a ^ 2)⟩, ⟨0, 0, .finite (a ^ 2)⟩,
   ⟨1, a ^ 2, .finite (2 * a ^ 2)⟩, ⟨0, 0, .essential⟩]

private theorem displacement : Cech.displacement (realSites smallSquare) (realSites largeSquare) = Real.sqrt 2 := by
  have step (v : Fin 4) : dist (realSites smallSquare v) (realSites largeSquare v) = Real.sqrt 2 := by
    have h : dist (realSites smallSquare v) (realSites largeSquare v) ^ 2 = 2 := by
      change dist (castPoint (corners 7 v)) (castPoint (corners 8 v)) ^ 2 = 2
      rw [distSq_cast]
      fin_cases v <;> norm_num [corners, sqDist]
    exact (Real.sqrt_sq dist_nonneg).symm.trans (congrArg Real.sqrt h)
  apply le_antisymm
  · exact (Cech.displacement_le_iff _ _ _).2 ⟨Real.sqrt_nonneg _, fun i => (step i).le⟩
  · simpa only [step] using Cech.dist_le_displacement (realSites smallSquare) (realSites largeSquare) (0 : Fin 4)

open RipsInputDiagramExamples RipsInputExamples

-- Both α inputs have the same fifteen ranked faces as the certified four-cycle input.

private theorem fourRun : FiniteInput.run fourCycleInput = some
    [⟨0, 0, .finite 1⟩, ⟨0, 0, .finite 1⟩, ⟨0, 0, .finite 1⟩, ⟨1, 1, .finite 2⟩, ⟨0, 0, .essential⟩] := by
  have h := (DistanceTable.ripsRun_eq_some_iff fourCycle).1 fourCycle_ripsRun
  apply (FiniteInput.run_eq_some_iff _ _).2
  rw [← fourCycle_ripsInput_eq]
  exact ⟨fourCycle.ripsInput_valid, h.2⟩

section GradeCertificates

set_option maxRecDepth 20000
set_option maxHeartbeats 1600000

private def gradeSet (p : Fin 4 ↪ RationalAlpha.Point) := (RationalAlpha.gradedFaces p).image Prod.snd

private theorem smallGradeSet : gradeSet smallSquare = {0, 49, 98} := by decide +kernel

private theorem largeGradeSet : gradeSet largeSquare = {0, 64, 128} := by decide +kernel

private theorem smallSortedGrades : (gradeSet smallSquare).sort = [0, 49, 98] := by
  rw [smallGradeSet]
  norm_num [Finset.sort_insert, Finset.sort_singleton]

private theorem largeSortedGrades : (gradeSet largeSquare).sort = [0, 64, 128] := by
  rw [largeGradeSet]
  norm_num [Finset.sort_insert, Finset.sort_singleton]

private theorem smallInput : simplexInput smallSquare = fourCycleInput := by
  unfold simplexInput
  dsimp only
  rw [show (Finset.sort ((RationalAlpha.gradedFaces smallSquare).image Prod.snd) (· ≤ ·)) = _
    from smallSortedGrades]
  decide +kernel

private theorem largeInput : simplexInput largeSquare = fourCycleInput := by
  unfold simplexInput
  dsimp only
  rw [show (Finset.sort ((RationalAlpha.gradedFaces largeSquare).image Prod.snd) (· ≤ ·)) = _
    from largeSortedGrades]
  decide +kernel

private def decodeList (g : List ℚ) (o : FiniteInput.Occurrence) : Occurrence :=
  ⟨o.degree, g[o.birth.toNat]?.getD 0, match o.death with
    | .finite d => .finite (g[d.toNat]?.getD 0)
    | .essential => .essential⟩

private theorem runEq (p : Fin 4 ↪ RationalAlpha.Point) :
    run p = (FiniteInput.run (simplexInput p)).map (List.map (decodeList (gradeSet p).sort)) := by
  unfold run
  rw [dite_eq_left p.injective]
  rfl

private theorem small_run : run smallSquare = some (expected 7) := by
  rw [runEq, smallInput, fourRun, smallSortedGrades]
  decide +kernel

private theorem large_run : run largeSquare = some (expected 8) := by
  rw [runEq, largeInput, fourRun, largeSortedGrades]
  decide +kernel

end GradeCertificates

noncomputable section

-- When matching costs at most the larger bar’s deletion cost, pairing the bars is optimal.

private theorem singletonCost {D F : Diagram ℝ} {x y : ℝ × ℝ}
    (hD : D.points = {(x.1, (x.2 : WithTop ℝ))})
    (hF : F.points = {(y.1, (y.2 : WithTop ℝ))})
    (cheap : finitePairCost x y ≤ diagonalCost x) :
    bottleneck D F = finitePairCost x y := by
  let X : Fin 1 → ℝ × ℝ := fun _ => x
  let Y : Fin 1 → ℝ × ℝ := fun _ => y
  rw [bottleneck_eq_presentation D F X Y (Fin.elim0 : Fin 0 → ℝ) (Fin.elim0 : Fin 0 → ℝ)
    (by simp [hD, finitePart, X]; rfl) (by simp [hF, finitePart, Y]; rfl)
    (by simp [hD, essentialPart]; rfl) (by simp [hF, essentialPart]; rfl)]
  apply le_antisymm
  · let M : OccurrenceMatching (Fin 1) (Fin 1) (Fin 0) (Fin 0) :=
      ⟨fun _ => some 0, fun _ _ _ _ _ => Subsingleton.elim _ _, Equiv.refl _⟩
    apply (presentationBottleneck_le_cost X Y Fin.elim0 Fin.elim0 M).trans
    simp [OccurrenceMatching.cost, M, X, Y]
  · unfold presentationBottleneck
    apply le_iInf
    intro M
    have hs := M.source_le_cost X Y Fin.elim0 Fin.elim0 0
    cases hm : M.finite 0 with
    | none => exact cheap.trans (by simpa [hm, X] using hs)
    | some j => simpa [hm, X, Y] using hs

private theorem squaredCost {D F : Diagram ℝ}
    (hD : D.points = {((64 : ℝ), ((128 : ℝ) : WithTop ℝ))})
    (hF : F.points = {((49 : ℝ), ((98 : ℝ) : WithTop ℝ))}) :
    bottleneck D F = 30 := by
  rw [singletonCost (x := (64, 128)) (y := (49, 98)) hD hF (by norm_num [finitePairCost, diagonalCost])]
  norm_num [finitePairCost]

private theorem radiusCost {D F : Diagram ℝ}
    (hD : D.points = {((8 : ℝ), ((8 * Real.sqrt 2 : ℝ) : WithTop ℝ))})
    (hF : F.points = {((7 : ℝ), ((7 * Real.sqrt 2 : ℝ) : WithTop ℝ))}) :
    bottleneck D F = ENNReal.ofReal (Real.sqrt 2) := by
  let s := Real.sqrt 2
  have hs : 4 / 3 < s := by
    dsimp [s]
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  have hpair : finitePairCost (8, 8 * s) (7, 7 * s) = ENNReal.ofReal s := by
    unfold finitePairCost
    congr 1
    change max |(8 : ℝ) - 7| |8 * s - 7 * s| = s
    rw [show 8 * s - 7 * s = s by ring, abs_of_pos (by linarith : 0 < s), max_eq_right (by norm_num; linarith)]
  have hdiag : finitePairCost (8, 8 * s) (7, 7 * s) ≤ diagonalCost (8, 8 * s) := by
    rw [hpair]
    apply ENNReal.ofReal_le_ofReal
    change s ≤ |8 * s - 8| / 2
    rw [abs_of_nonneg (by linarith)]
    linarith
  exact (singletonCost (x := (8, 8 * s)) (y := (7, 7 * s)) hD hF hdiag).trans hpair

/-- The squared-grade H₁ diagram of four embedded rational sites over F₂. -/
abbrev squaredH1Diagram (p : Fin 4 ↪ RationalAlpha.Point) :=
  letI := Fintype.ofFinite (TotalFace (Alpha.carrier (realSites p)))
  dgm (ZMod 2) (Alpha.filter (realSites p)) 1

private theorem sqPoints (p : Fin 4 ↪ RationalAlpha.Point) (a : ℚ) (h : run p = some (expected a)) :
    (squaredH1Diagram p).points = {(((a : ℝ) ^ 2), ((2 * (a : ℝ) ^ 2 : ℝ) : WithTop ℝ))} := by
  rw [show (squaredH1Diagram p).points = points (expected a) 1 from (run_correct h p.injective 1).symm]
  simp [points, expected, Occurrence.point]

private theorem radPoints (p : Fin 4 ↪ RationalAlpha.Point) (a : ℚ) (ha : 0 ≤ a)
    (h : run p = some (expected a)) :
    (alphaRadiusDiagram (ZMod 2) (realSites p) 1).points = {((a : ℝ), ((a * Real.sqrt 2 : ℝ) : WithTop ℝ))} := by
  let := Fintype.ofFinite (TotalFace (Alpha.carrier (realSites p)))
  rw [alphaRadiusDiagram_eq_map, Diagram.map_points, sqPoints p a h]
  have ha' : (0 : ℝ) ≤ a := by exact_mod_cast ha
  have e1 : alphaSquaredGradeToRadius.toOrderEmbedding ((a : ℝ) ^ 2) = a :=
    (alphaSquaredGradeToRadius_of_nonneg (sq_nonneg _)).trans (Real.sqrt_sq ha')
  have e2 : alphaSquaredGradeToRadius.toOrderEmbedding (2 * (a : ℝ) ^ 2) = (a : ℝ) * Real.sqrt 2 := by
    change alphaSquaredGradeToRadius _ = _
    rw [alphaSquaredGradeToRadius_of_nonneg (by positivity), Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_sq ha', mul_comm]
  simp only [Multiset.map_singleton, WithTop.map_coe, e1, e2]

private theorem squareCosts :
    bottleneck (alphaRadiusDiagram (ZMod 2) (realSites smallSquare) 1)
      (alphaRadiusDiagram (ZMod 2) (realSites largeSquare) 1) = ENNReal.ofReal (Real.sqrt 2) ∧
    bottleneck (squaredH1Diagram smallSquare) (squaredH1Diagram largeSquare) = 30 := by
  constructor
  · rw [bottleneck_comm]
    apply radiusCost
    · simpa using radPoints largeSquare 8 (by norm_num) large_run
    · simpa using radPoints smallSquare 7 (by norm_num) small_run
  · rw [bottleneck_comm]
    apply squaredCost
    · convert sqPoints largeSquare 8 large_run using 1; norm_num
    · convert sqPoints smallSquare 7 small_run using 1; norm_num

/-- Exact matched displacement and the two degree-one bottleneck distances. -/
theorem square_bottlenecks :
    Cech.displacement (realSites smallSquare) (realSites largeSquare) = Real.sqrt 2 ∧
    bottleneck (alphaRadiusDiagram (ZMod 2) (realSites smallSquare) 1)
      (alphaRadiusDiagram (ZMod 2) (realSites largeSquare) 1) = ENNReal.ofReal (Real.sqrt 2) ∧
    bottleneck (squaredH1Diagram smallSquare) (squaredH1Diagram largeSquare) = 30 ∧
    ENNReal.ofReal (Cech.displacement (realSites smallSquare) (realSites largeSquare)) <
      bottleneck (squaredH1Diagram smallSquare) (squaredH1Diagram largeSquare) := by
  have h := squareCosts
  refine ⟨displacement, h.1, h.2, ?_⟩
  rw [h.2, displacement]
  have hr : Real.sqrt 2 < 30 := by nlinarith [Real.sq_sqrt (by norm_num : 0 ≤ (2 : ℝ))]
  exact_mod_cast (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ Real.sqrt 2)).2 hr

/-- Empty clouds have radius diagram distance zero in every degree. -/
theorem empty_radius_bottleneck (k : Type) [Field k] (p q : Fin 0 → ℝ) (n : ℕ) :
    bottleneck (alphaRadiusDiagram k p n) (alphaRadiusDiagram k q n) = 0 := by
  apply le_antisymm _ zero_le
  simpa only [Cech.displacement_of_isEmpty, ENNReal.ofReal_zero] using
    bottleneck_alphaRadiusDiagram_le_displacement k p q n

/-- Two coincident labels at the origin may separate to opposite sites. -/
theorem coincident_radius_bottleneck (k : Type) [Field k] (n : ℕ) :
    bottleneck (alphaRadiusDiagram k (fun _ : Fin 2 => (0 : ℝ)) n)
      (alphaRadiusDiagram k (![(-1 : ℝ), 1] : Fin 2 → ℝ) n) ≤ 1 := by
  let p : Fin 2 → ℝ := fun _ => 0
  let q : Fin 2 → ℝ := ![-1, 1]
  have h : Cech.displacement p q ≤ 1 := (Cech.displacement_le_iff p q 1).2
    ⟨zero_le_one, fun i => by fin_cases i <;> norm_num [p, q, Real.dist_eq]⟩
  simpa only [ENNReal.ofReal_one] using
    (bottleneck_alphaRadiusDiagram_le_displacement k p q n).trans (ENNReal.ofReal_le_ofReal h)

end
end TDA.Persistence.AlphaRadiusStabilityExamples
