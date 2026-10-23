import TDA.Persistence.BoundaryTransportGeometry
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

/-!
# Finite boundary plans

Plans on pairs of closed birth–death coordinates exclude diagonal–diagonal pairs.
Only their interior marginals are prescribed. Every admissible plan has mass at
most the sum of the input masses. Sending both inputs to their nearest diagonal
points gives an explicit finite-cost competitor when the diagonal persistence
moments are finite.
-/

set_option autoImplicit false

noncomputable section
namespace TDA.Persistence.BoundaryTransport
open Set MeasureTheory
open scoped ENNReal

/-- The canonical inclusion of strict bars in the closed half-plane. -/
def interiorIncl (x : Interior) : ClosedHalfPlane := ⟨x.1, x.2.le⟩

/-- The closest diagonal point in the maximum-coordinate norm. -/
def diagonalProjection (x : Interior) : ClosedHalfPlane :=
  ⟨((x.1.1 + x.1.2) / 2, (x.1.1 + x.1.2) / 2), le_rfl⟩

/-- Ordered pairs of closed half-plane points with at least one interior endpoint. -/
abbrev PlanSpace := {z : ClosedHalfPlane × ClosedHalfPlane //
  z.1.1.1 < z.1.1.2 ∨ z.2.1.1 < z.2.1.2}

/-- In the closed half-plane, the plan carrier is precisely the complement of
diagonal–diagonal pairs. -/
theorem planSpace_iff_not_both_diagonal (z : ClosedHalfPlane × ClosedHalfPlane) :
    z ∈ Set.range (Subtype.val : PlanSpace → ClosedHalfPlane × ClosedHalfPlane) ↔
      ¬ (z.1.1.1 = z.1.1.2 ∧ z.2.1.1 = z.2.1.2) := by
  constructor
  · rintro ⟨e, rfl⟩ ⟨h₁, h₂⟩
    rcases e.2 with h | h
    · exact (ne_of_lt h) h₁
    · exact (ne_of_lt h) h₂
  · intro h
    by_cases h₁ : z.1.1.1 < z.1.1.2
    · exact ⟨⟨z, Or.inl h₁⟩, rfl⟩
    · have heq₁ : z.1.1.1 = z.1.1.2 :=
        le_antisymm z.1.2 (le_of_not_gt h₁)
      have h₂ : z.2.1.1 < z.2.1.2 := by
        by_contra hn
        exact h ⟨heq₁, le_antisymm z.2.2 (le_of_not_gt hn)⟩
      exact ⟨⟨z, Or.inr h₂⟩, rfl⟩

/-- The bars with an interior first endpoint lying in `s`. -/
def firstFiber (s : Set Interior) : Set PlanSpace :=
  {z | z.1.1 ∈ interiorIncl '' s}

/-- The bars with an interior second endpoint lying in `s`. -/
def secondFiber (s : Set Interior) : Set PlanSpace :=
  {z | z.1.2 ∈ interiorIncl '' s}

/-- A boundary plan has the specified two interior marginals; boundary marginals are free. -/
structure IsBoundaryPlan (π : Measure PlanSpace) (μ ν : Measure Interior) : Prop where
  first : ∀ s, MeasurableSet s → π (firstFiber s) = μ s
  second : ∀ s, MeasurableSet s → π (secondFiber s) = ν s

private theorem planSpace_cover :
    (Set.univ : Set PlanSpace) = firstFiber Set.univ ∪ secondFiber Set.univ := by
  ext z
  constructor
  · intro _
    rcases z.2 with h | h
    · left
      exact ⟨⟨z.1.1.1, h⟩, Set.mem_univ _, Subtype.ext rfl⟩
    · right
      exact ⟨⟨z.1.2.1, h⟩, Set.mem_univ _, Subtype.ext rfl⟩
  · intro _
    trivial

/-- Every admissible boundary plan has total mass at most the two input masses. -/
theorem boundaryPlan_mass_le {π : Measure PlanSpace} {μ ν : Measure Interior}
    (hπ : IsBoundaryPlan π μ ν) : π Set.univ ≤ μ Set.univ + ν Set.univ := by
  rw [planSpace_cover]
  exact (measure_union_le _ _).trans_eq
    (congrArg₂ (· + ·) (hπ.first _ MeasurableSet.univ)
      (hπ.second _ MeasurableSet.univ))

/-- Finite input masses force every admissible boundary plan to be finite. -/
theorem boundaryPlan_mass_lt_top {π : Measure PlanSpace} {μ ν : Measure Interior}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hπ : IsBoundaryPlan π μ ν) :
    π Set.univ < ∞ :=
  (boundaryPlan_mass_le hπ).trans_lt
    (ENNReal.add_lt_top.mpr ⟨measure_lt_top μ _, measure_lt_top ν _⟩)

theorem boundaryPlan_isFiniteMeasure {π : Measure PlanSpace} {μ ν : Measure Interior}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hπ : IsBoundaryPlan π μ ν) :
    IsFiniteMeasure π :=
  ⟨boundaryPlan_mass_lt_top hπ⟩

/-- A source bar is sent to its closest diagonal point. -/
def deleteLeg (x : Interior) : PlanSpace :=
  ⟨(interiorIncl x, diagonalProjection x), Or.inl x.2⟩

/-- A target bar is born at its closest diagonal point. -/
def insertLeg (x : Interior) : PlanSpace :=
  ⟨(diagonalProjection x, interiorIncl x), Or.inr x.2⟩

theorem continuous_interiorIncl : Continuous interiorIncl := by
  unfold interiorIncl
  fun_prop

private instance : PolishSpace Interior := by
  have h : IsOpen {x : ℝ × ℝ | x.1 < x.2} :=
    isOpen_lt continuous_fst continuous_snd
  exact h.polishSpace

theorem interiorIncl_injective : Function.Injective interiorIncl := by
  intro x y h
  have h' : x.1 = y.1 := by
    simpa only [interiorIncl] using congrArg Subtype.val h
  exact Subtype.ext h'

theorem measurableEmbedding_interiorIncl : MeasurableEmbedding interiorIncl :=
  continuous_interiorIncl.measurableEmbedding interiorIncl_injective

private theorem continuous_diagonalProjection : Continuous diagonalProjection := by
  unfold diagonalProjection
  fun_prop

theorem measurable_deleteLeg : Measurable deleteLeg := by
  apply Continuous.measurable
  unfold deleteLeg
  exact (continuous_interiorIncl.prodMk continuous_diagonalProjection).subtype_mk _

theorem measurable_insertLeg : Measurable insertLeg := by
  apply Continuous.measurable
  unfold insertLeg
  exact (continuous_diagonalProjection.prodMk continuous_interiorIncl).subtype_mk _

theorem measurableSet_firstFiber {s : Set Interior} (hs : MeasurableSet s) :
    MeasurableSet (firstFiber s) := by
  exact (measurableEmbedding_interiorIncl.measurableSet_image.mpr hs).preimage
    (by fun_prop : Measurable (fun z : PlanSpace => z.1.1))

theorem measurableSet_secondFiber {s : Set Interior} (hs : MeasurableSet s) :
    MeasurableSet (secondFiber s) := by
  exact (measurableEmbedding_interiorIncl.measurableSet_image.mpr hs).preimage
    (by fun_prop : Measurable (fun z : PlanSpace => z.1.2))

/-- Explicit unmatched deletion and insertion measure. -/
def diagonalBoundaryPlan (μ ν : Measure Interior) : Measure PlanSpace :=
  μ.map deleteLeg + ν.map insertLeg

/-- The explicit nearest-diagonal plan has the required marginals. -/
theorem diagonalBoundaryPlan_admissible (μ ν : Measure Interior) :
    IsBoundaryPlan (diagonalBoundaryPlan μ ν) μ ν := by
  have hfirstDelete (s : Set Interior) : deleteLeg ⁻¹' firstFiber s = s := by
    ext x
    change interiorIncl x ∈ interiorIncl '' s ↔ x ∈ s
    constructor
    · rintro ⟨y, hy, hxy⟩
      exact (interiorIncl_injective hxy).symm ▸ hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  have hfirstInsert (s : Set Interior) : insertLeg ⁻¹' firstFiber s = ∅ := by
    ext x
    change diagonalProjection x ∈ interiorIncl '' s ↔ False
    constructor
    · rintro ⟨y, _, heq⟩
      have h : (diagonalProjection x).1.1 < (diagonalProjection x).1.2 := by
        rw [← heq]
        exact y.2
      simp [diagonalProjection] at h
    · intro h
      exact False.elim h
  have hsecondDelete (s : Set Interior) : deleteLeg ⁻¹' secondFiber s = ∅ := by
    ext x
    change diagonalProjection x ∈ interiorIncl '' s ↔ False
    constructor
    · rintro ⟨y, _, heq⟩
      have h : (diagonalProjection x).1.1 < (diagonalProjection x).1.2 := by
        rw [← heq]
        exact y.2
      simp [diagonalProjection] at h
    · intro h
      exact False.elim h
  have hsecondInsert (s : Set Interior) : insertLeg ⁻¹' secondFiber s = s := by
    ext x
    change interiorIncl x ∈ interiorIncl '' s ↔ x ∈ s
    constructor
    · rintro ⟨y, hy, hxy⟩
      exact (interiorIncl_injective hxy).symm ▸ hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  constructor
  · intro s hs
    rw [diagonalBoundaryPlan, Measure.add_apply,
      Measure.map_apply measurable_deleteLeg (measurableSet_firstFiber hs),
      Measure.map_apply measurable_insertLeg (measurableSet_firstFiber hs)]
    rw [hfirstDelete, hfirstInsert]
    simp
  · intro s hs
    rw [diagonalBoundaryPlan, Measure.add_apply,
      Measure.map_apply measurable_deleteLeg (measurableSet_secondFiber hs),
      Measure.map_apply measurable_insertLeg (measurableSet_secondFiber hs)]
    rw [hsecondDelete, hsecondInsert]
    simp

/-- Its mass is exactly the sum of input masses, including zero and unequal masses. -/
theorem diagonalBoundaryPlan_mass (μ ν : Measure Interior) :
    diagonalBoundaryPlan μ ν Set.univ = μ Set.univ + ν Set.univ := by
  rw [diagonalBoundaryPlan, Measure.add_apply,
    Measure.map_apply measurable_deleteLeg MeasurableSet.univ,
    Measure.map_apply measurable_insertLeg MeasurableSet.univ]
  simp

/-- Each deletion leg realizes the native diagonal cost. -/
theorem deleteLeg_distance (x : Interior) :
    dist (interiorIncl x) (diagonalProjection x) = depth x := by
  rw [depth_eq]
  change dist x.1 ((x.1.1 + x.1.2) / 2, (x.1.1 + x.1.2) / 2) =
    (x.1.2 - x.1.1) / 2
  rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
  rw [← diagonalCost_midpoint x.1.1 x.1.2]
  rw [abs_of_pos (sub_pos.mpr x.2)]

theorem insertLeg_distance (x : Interior) :
    dist (diagonalProjection x) (interiorIncl x) = depth x := by
  rw [dist_comm]
  exact deleteLeg_distance x

/-- Powered maximum-coordinate transport cost on the genuine boundary-plan space. -/
def planPowerCost (p : ℝ) (z : PlanSpace) : ℝ≥0∞ :=
  ENNReal.ofReal ((dist z.1.1 z.1.2) ^ p)

theorem measurable_planPowerCost (p : ℝ) : Measurable (planPowerCost p) := by
  unfold planPowerCost
  fun_prop

/-- The explicit plan has exactly the two diagonal persistence moments as cost. -/
theorem diagonalBoundaryPlan_cost (p : ℝ) (μ ν : Measure Interior) :
    ∫⁻ z, planPowerCost p z ∂diagonalBoundaryPlan μ ν =
      (∫⁻ x, ENNReal.ofReal (depth x ^ p) ∂μ) +
      (∫⁻ x, ENNReal.ofReal (depth x ^ p) ∂ν) := by
  rw [diagonalBoundaryPlan, lintegral_add_measure,
    lintegral_map (measurable_planPowerCost p) measurable_deleteLeg,
    lintegral_map (measurable_planPowerCost p) measurable_insertLeg]
  simp only [planPowerCost, deleteLeg, insertLeg, deleteLeg_distance, insertLeg_distance]

/-- Finite p-persistence on both inputs gives one finite-cost admissible plan. -/
theorem diagonalBoundaryPlan_cost_lt_top (p : ℝ) (μ ν : Measure Interior)
    (hμ : (∫⁻ x, ENNReal.ofReal (depth x ^ p) ∂μ) < ∞)
    (hν : (∫⁻ x, ENNReal.ofReal (depth x ^ p) ∂ν) < ∞) :
    (∫⁻ z, planPowerCost p z ∂diagonalBoundaryPlan μ ν) < ∞ := by
  rw [diagonalBoundaryPlan_cost]
  exact ENNReal.add_lt_top.mpr ⟨hμ, hν⟩

/-- The finite-persistence hypotheses provide a real admissible finite-cost competitor. -/
theorem exists_finite_cost_boundaryPlan (p : ℝ) (μ ν : Measure Interior)
    (hμ : (∫⁻ x, ENNReal.ofReal (depth x ^ p) ∂μ) < ∞)
    (hν : (∫⁻ x, ENNReal.ofReal (depth x ^ p) ∂ν) < ∞) :
    ∃ π : Measure PlanSpace, IsBoundaryPlan π μ ν ∧
      (∫⁻ z, planPowerCost p z ∂π) < ∞ :=
  ⟨diagonalBoundaryPlan μ ν, diagonalBoundaryPlan_admissible μ ν,
    diagonalBoundaryPlan_cost_lt_top p μ ν hμ hν⟩

/-- Powered boundary transport value over all admissible Borel plans. -/
def boundaryTransportPowerValue (p : ℝ) (μ ν : Measure Interior) : ℝ≥0∞ :=
  ⨅ (π : Measure PlanSpace) (_ : IsBoundaryPlan π μ ν),
    ∫⁻ z, planPowerCost p z ∂π

theorem boundaryTransportPowerValue_le_diagonalPlan (p : ℝ) (μ ν : Measure Interior) :
    boundaryTransportPowerValue p μ ν ≤
      ∫⁻ z, planPowerCost p z ∂diagonalBoundaryPlan μ ν := by
  exact (iInf_le (fun π : Measure PlanSpace =>
    ⨅ (_ : IsBoundaryPlan π μ ν), ∫⁻ z, planPowerCost p z ∂π)
    (diagonalBoundaryPlan μ ν)).trans
      (iInf_le (fun _ : IsBoundaryPlan (diagonalBoundaryPlan μ ν) μ ν =>
        ∫⁻ z, planPowerCost p z ∂diagonalBoundaryPlan μ ν)
        (diagonalBoundaryPlan_admissible μ ν))

theorem boundaryTransportPowerValue_lt_top (p : ℝ) (μ ν : Measure Interior)
    (hμ : (∫⁻ x, ENNReal.ofReal (depth x ^ p) ∂μ) < ∞)
    (hν : (∫⁻ x, ENNReal.ofReal (depth x ^ p) ∂ν) < ∞) :
    boundaryTransportPowerValue p μ ν < ∞ :=
  (boundaryTransportPowerValue_le_diagonalPlan p μ ν).trans_lt
    (diagonalBoundaryPlan_cost_lt_top p μ ν hμ hν)

end TDA.Persistence.BoundaryTransport
