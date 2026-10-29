import TDA.Persistence.BoundaryPlanLaws
import TDA.Persistence.BoundaryTransportForward
import TDA.Persistence.FiniteWeightedBoundaryTransport

/-!
# Atomic finite weighted diagrams and boundary transport

Native finite weighted diagrams define positive atomic measures. Feasible
matrices give boundary plans of exactly the same powered cost, and every Borel
competitor between these atomic measures gives a matrix of no greater cost.
The two optimized values agree, and the native optimizer attains the all-plan
value. The comparison permits arbitrary diagonal endpoints and infinite costs.
-/
set_option autoImplicit false
noncomputable section
namespace TDA.Persistence.BoundaryTransport
open Set MeasureTheory
open scoped ENNReal NNReal Classical

/-- The exact positive atomic measure of a native finite weighted diagram. -/
def atomicMeasure (D : FiniteWeightedDiagram) : Measure Interior :=
  ∑ i : D.supportLabels, (D.weights i : ℝ≥0∞) • Measure.dirac i.1

/-- Pair of native support labels as an interior–interior boundary-plan point. -/
def directLeg {D E : FiniteWeightedDiagram}
    (i : D.supportLabels) (j : E.supportLabels) : PlanSpace :=
  ⟨(interiorIncl i.1, interiorIncl j.1), Or.inl i.1.2⟩

/-- Convert one feasible native weighted matrix into an actual Borel boundary plan. -/
def atomicBoundaryPlan (D E : FiniteWeightedDiagram)
    (a : FiniteWeightedBoundaryPlan D.weights E.weights) : Measure PlanSpace :=
  (∑ i : D.supportLabels, ∑ j : E.supportLabels,
    ENNReal.ofReal (a.mass i j) • Measure.dirac (directLeg i j)) +
  (∑ i : D.supportLabels,
    ENNReal.ofReal (a.deletionMass i) • Measure.dirac (deleteLeg i.1)) +
  ∑ j : E.supportLabels,
    ENNReal.ofReal (a.insertionMass j) • Measure.dirac (insertLeg j.1)

@[simp] theorem directLeg_firstFiber {D E : FiniteWeightedDiagram}
    (i : D.supportLabels) (j : E.supportLabels) (s : Set Interior) :
    directLeg i j ∈ firstFiber s ↔ i.1 ∈ s := by
  change interiorIncl i.1 ∈ interiorIncl '' s ↔ i.1 ∈ s
  constructor
  · rintro ⟨x, hx, heq⟩
    exact (interiorIncl_injective heq).symm ▸ hx
  · exact fun hi => ⟨i.1, hi, rfl⟩

@[simp] theorem directLeg_secondFiber {D E : FiniteWeightedDiagram}
    (i : D.supportLabels) (j : E.supportLabels) (s : Set Interior) :
    directLeg i j ∈ secondFiber s ↔ j.1 ∈ s := by
  change interiorIncl j.1 ∈ interiorIncl '' s ↔ j.1 ∈ s
  constructor
  · rintro ⟨x, hx, heq⟩
    exact (interiorIncl_injective heq).symm ▸ hx
  · exact fun hj => ⟨j.1, hj, rfl⟩

private theorem diagonalProjection_not_image (x : Interior) (s : Set Interior) :
    diagonalProjection x ∉ interiorIncl '' s := by
  rintro ⟨y, _, heq⟩
  have h : (diagonalProjection x).1.1 < (diagonalProjection x).1.2 := by
    rw [← heq]
    exact y.2
  simp [diagonalProjection] at h

@[simp] theorem deleteLeg_firstFiber (x : Interior) (s : Set Interior) :
    deleteLeg x ∈ firstFiber s ↔ x ∈ s := by
  change interiorIncl x ∈ interiorIncl '' s ↔ x ∈ s
  constructor
  · rintro ⟨y, hy, heq⟩
    exact (interiorIncl_injective heq).symm ▸ hy
  · exact fun hx => ⟨x, hx, rfl⟩

@[simp] theorem insertLeg_secondFiber (x : Interior) (s : Set Interior) :
    insertLeg x ∈ secondFiber s ↔ x ∈ s := by
  change interiorIncl x ∈ interiorIncl '' s ↔ x ∈ s
  constructor
  · rintro ⟨y, hy, heq⟩
    exact (interiorIncl_injective heq).symm ▸ hy
  · exact fun hx => ⟨x, hx, rfl⟩

@[simp] theorem insertLeg_not_firstFiber (x : Interior) (s : Set Interior) :
    insertLeg x ∉ firstFiber s := diagonalProjection_not_image x s

@[simp] theorem deleteLeg_not_secondFiber (x : Interior) (s : Set Interior) :
    deleteLeg x ∉ secondFiber s := diagonalProjection_not_image x s

theorem atomicMeasure_apply (D : FiniteWeightedDiagram) (s : Set Interior)
    (hs : MeasurableSet s) :
    atomicMeasure D s =
      ∑ i : D.supportLabels, if i.1 ∈ s then (D.weights i : ℝ≥0∞) else 0 := by
  simp [atomicMeasure, Set.indicator, hs]

theorem atomicMeasure_mass (D : FiniteWeightedDiagram) :
    atomicMeasure D Set.univ = ∑ i : D.supportLabels, (D.weights i : ℝ≥0∞) := by
  rw [atomicMeasure_apply D Set.univ MeasurableSet.univ]
  simp

theorem atomicMeasure_isFinite (D : FiniteWeightedDiagram) :
    IsFiniteMeasure (atomicMeasure D) := by
  refine ⟨?_⟩
  rw [atomicMeasure_mass]
  exact ENNReal.sum_lt_top.mpr (fun i _ => ENNReal.coe_lt_top)

@[simp] theorem atomicMeasure_zero :
    atomicMeasure (0 : FiniteWeightedDiagram) = 0 := by
  simp [atomicMeasure]

/-- Coalesced native occurrences are represented by their single Finsupp atom mass. -/
theorem atomicMeasure_singleton (D : FiniteWeightedDiagram) (x : Interior) :
    atomicMeasure D {x} = (D x : ℝ≥0∞) := by
  rw [atomicMeasure_apply D {x} (measurableSet_singleton x)]
  by_cases hx : x ∈ D.support
  · let i : D.supportLabels := ⟨x, hx⟩
    rw [Finset.sum_eq_single i]
    · simp [i, FiniteWeightedDiagram.weights]
    · intro j _ hji
      have hne : j.1 ≠ x := by
        intro heq
        exact hji (Subtype.ext heq)
      simp [hne]
    · intro hi
      exact (hi (Finset.mem_univ i)).elim
  · have hzero : D x = 0 := Finsupp.notMem_support_iff.mp hx
    rw [hzero]
    apply Finset.sum_eq_zero
    intro i _
    have hne : i.1 ≠ x := by
      intro heq
      exact hx (heq ▸ i.2)
    simp [hne]

private theorem sourceBalance_ennreal (D E : FiniteWeightedDiagram)
    (a : FiniteWeightedBoundaryPlan D.weights E.weights) (i : D.supportLabels) :
    (∑ j : E.supportLabels, ENNReal.ofReal (a.mass i j)) +
      ENNReal.ofReal (a.deletionMass i) = (D.weights i : ℝ≥0∞) := by
  rw [← ENNReal.ofReal_sum_of_nonneg (s := Finset.univ)
    (fun j _ => a.nonneg i j),
    ← ENNReal.ofReal_add (Finset.sum_nonneg fun j _ => a.nonneg i j)
      (a.deletionMass_nonneg i), a.source_balance]
  simp

private theorem targetBalance_ennreal (D E : FiniteWeightedDiagram)
    (a : FiniteWeightedBoundaryPlan D.weights E.weights) (j : E.supportLabels) :
    (∑ i : D.supportLabels, ENNReal.ofReal (a.mass i j)) +
      ENNReal.ofReal (a.insertionMass j) = (E.weights j : ℝ≥0∞) := by
  rw [← ENNReal.ofReal_sum_of_nonneg (s := Finset.univ)
    (fun i _ => a.nonneg i j),
    ← ENNReal.ofReal_add (Finset.sum_nonneg fun i _ => a.nonneg i j)
      (a.insertionMass_nonneg j), a.target_balance]
  simp

theorem atomicBoundaryPlan_admissible (D E : FiniteWeightedDiagram)
    (a : FiniteWeightedBoundaryPlan D.weights E.weights) :
    IsBoundaryPlan (atomicBoundaryPlan D E a) (atomicMeasure D) (atomicMeasure E) := by
  constructor
  · intro s hs
    rw [atomicMeasure_apply D s hs]
    simp [atomicBoundaryPlan, Set.indicator,
      measurableSet_firstFiber hs]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i.1 ∈ s
    · simp only [if_pos hi]
      exact sourceBalance_ennreal D E a i
    · simp [hi]
  · intro s hs
    rw [atomicMeasure_apply E s hs]
    simp [atomicBoundaryPlan, Set.indicator,
      measurableSet_secondFiber hs]
    rw [Finset.sum_comm, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j.1 ∈ s
    · simp only [if_pos hj]
      exact targetBalance_ennreal D E a j
    · simp [hj]

@[simp] theorem planPowerCost_directLeg (p : ℝ) {D E : FiniteWeightedDiagram}
    (i : D.supportLabels) (j : E.supportLabels) :
    planPowerCost p (directLeg i j) =
      ENNReal.ofReal ((finitePairCost (D.coordinates i) (E.coordinates j)).toReal ^ p) := by
  simp [planPowerCost, directLeg, interiorIncl, FiniteWeightedDiagram.coordinates,
    Subtype.dist_eq, finitePairCost_toReal, dist_eq_norm]

@[simp] theorem planPowerCost_deleteLeg (p : ℝ) (x : Interior) :
    planPowerCost p (deleteLeg x) =
      ENNReal.ofReal ((diagonalCost x.1).toReal ^ p) := by
  simp [planPowerCost, deleteLeg, deleteLeg_distance, depth]

@[simp] theorem planPowerCost_insertLeg (p : ℝ) (x : Interior) :
    planPowerCost p (insertLeg x) =
      ENNReal.ofReal ((diagonalCost x.1).toReal ^ p) := by
  simp [planPowerCost, insertLeg, insertLeg_distance, depth]

/-- Exact powered cost of the Borel plan induced by a native matrix, still in
extended nonnegative arithmetic before comparison with the native real objective. -/
theorem atomicBoundaryPlan_cost_sum (p : ℝ) (D E : FiniteWeightedDiagram)
    (a : FiniteWeightedBoundaryPlan D.weights E.weights) :
    (∫⁻ z, planPowerCost p z ∂atomicBoundaryPlan D E a) =
      (∑ i : D.supportLabels, ∑ j : E.supportLabels,
        ENNReal.ofReal (a.mass i j) *
          ENNReal.ofReal ((finitePairCost (D.coordinates i) (E.coordinates j)).toReal ^ p)) +
      (∑ i : D.supportLabels, ENNReal.ofReal (a.deletionMass i) *
        ENNReal.ofReal ((diagonalCost (D.coordinates i)).toReal ^ p)) +
      ∑ j : E.supportLabels, ENNReal.ofReal (a.insertionMass j) *
        ENNReal.ofReal ((diagonalCost (E.coordinates j)).toReal ^ p) := by
  simp [atomicBoundaryPlan, lintegral_add_measure, lintegral_finsetSum_measure,
    lintegral_smul_measure, FiniteWeightedDiagram.coordinates]

/-- The cost of an actual atomic boundary measure equals the native real matrix
objective after the canonical embedding into extended nonnegative reals. -/
theorem atomicBoundaryPlan_cost_native (p : ℝ) (D E : FiniteWeightedDiagram)
    (a : FiniteWeightedBoundaryPlan D.weights E.weights) :
    (∫⁻ z, planPowerCost p z ∂atomicBoundaryPlan D E a) =
      ENNReal.ofReal (a.powerCost p D.coordinates E.coordinates) := by
  let c : D.supportLabels → E.supportLabels → ℝ := fun i j =>
    (finitePairCost (D.coordinates i) (E.coordinates j)).toReal ^ p
  let d : D.supportLabels → ℝ := fun i =>
    (diagonalCost (D.coordinates i)).toReal ^ p
  let e : E.supportLabels → ℝ := fun j =>
    (diagonalCost (E.coordinates j)).toReal ^ p
  have hc (i : D.supportLabels) (j : E.supportLabels) : 0 ≤ c i j :=
    Real.rpow_nonneg ENNReal.toReal_nonneg _
  have hd (i : D.supportLabels) : 0 ≤ d i :=
    Real.rpow_nonneg ENNReal.toReal_nonneg _
  have he (j : E.supportLabels) : 0 ≤ e j :=
    Real.rpow_nonneg ENNReal.toReal_nonneg _
  rw [atomicBoundaryPlan_cost_sum]
  change (∑ i, ∑ j, ENNReal.ofReal (a.mass i j) * ENNReal.ofReal (c i j)) +
      (∑ i, ENNReal.ofReal (a.deletionMass i) * ENNReal.ofReal (d i)) +
      (∑ j, ENNReal.ofReal (a.insertionMass j) * ENNReal.ofReal (e j)) = _
  simp_rw [← ENNReal.ofReal_mul (a.nonneg _ _),
    ← ENNReal.ofReal_mul (a.deletionMass_nonneg _),
    ← ENNReal.ofReal_mul (a.insertionMass_nonneg _)]
  simp_rw [← ENNReal.ofReal_sum_of_nonneg (s := Finset.univ)
    (fun j _ => mul_nonneg (a.nonneg _ j) (hc _ j))]
  rw [← ENNReal.ofReal_sum_of_nonneg (s := Finset.univ)
    (fun i _ => Finset.sum_nonneg fun j _ => mul_nonneg (a.nonneg i j) (hc i j)),
    ← ENNReal.ofReal_sum_of_nonneg (s := Finset.univ)
      (fun i _ => mul_nonneg (a.deletionMass_nonneg i) (hd i)),
    ← ENNReal.ofReal_sum_of_nonneg (s := Finset.univ)
      (fun j _ => mul_nonneg (a.insertionMass_nonneg j) (he j))]
  rw [← ENNReal.ofReal_add
      (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
        mul_nonneg (a.nonneg i j) (hc i j))
      (Finset.sum_nonneg fun i _ => mul_nonneg (a.deletionMass_nonneg i) (hd i)),
    ← ENNReal.ofReal_add
      (add_nonneg
        (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
          mul_nonneg (a.nonneg i j) (hc i j))
        (Finset.sum_nonneg fun i _ => mul_nonneg (a.deletionMass_nonneg i) (hd i)))
      (Finset.sum_nonneg fun j _ => mul_nonneg (a.insertionMass_nonneg j) (he j))]
  rfl

/-- Every native finite matrix supplies a genuine admissible Borel competitor. -/
theorem boundaryTransportPowerValue_atomic_le_plan (p : ℝ)
    (D E : FiniteWeightedDiagram)
    (a : FiniteWeightedBoundaryPlan D.weights E.weights) :
    boundaryTransportPowerValue p (atomicMeasure D) (atomicMeasure E) ≤
      ENNReal.ofReal (a.powerCost p D.coordinates E.coordinates) := by
  exact (boundaryTransportPowerValue_le_plan p
    (atomicBoundaryPlan_admissible D E a)).trans_eq
      (atomicBoundaryPlan_cost_native p D E a)

/-- One direction of the atomic bridge, including empty diagrams, fractional masses,
and coalesced occurrences represented by the native Finsupp support. -/
theorem boundaryTransportPowerValue_atomic_le_native (p : ℝ)
    (D E : FiniteWeightedDiagram) :
    boundaryTransportPowerValue p (atomicMeasure D) (atomicMeasure E) ≤
      ENNReal.ofReal (FiniteWeightedDiagram.powerBoundaryTransportCost p D E) := by
  obtain ⟨a, ha⟩ := FiniteWeightedDiagram.exists_minimizing_powerPlan p D E
  exact (boundaryTransportPowerValue_atomic_le_plan p D E a).trans_eq
    (congrArg ENNReal.ofReal ha)

/-- Exact interior–interior cell for a pair of native support labels. -/
def atomicPairCell {D E : FiniteWeightedDiagram}
    (i : D.supportLabels) (j : E.supportLabels) : Set PlanSpace :=
  firstFiber {i.1} ∩ secondFiber {j.1}

theorem measurableSet_atomicPairCell {D E : FiniteWeightedDiagram}
    (i : D.supportLabels) (j : E.supportLabels) :
    MeasurableSet (atomicPairCell i j) :=
  (measurableSet_firstFiber (measurableSet_singleton i.1)).inter
    (measurableSet_secondFiber (measurableSet_singleton j.1))

/-- For a fixed source label, distinct target cells are disjoint. -/
private theorem atomicPairCell_disjoint_right {D E : FiniteWeightedDiagram}
    (i : D.supportLabels) {j k : E.supportLabels} (hjk : j ≠ k) :
    Disjoint (atomicPairCell i j) (atomicPairCell i k) := by
  apply Set.disjoint_left.mpr
  intro z hzj hzk
  have hj : z ∈ secondFiber {j.1} := hzj.2
  have hk : z ∈ secondFiber {k.1} := hzk.2
  rcases hj with ⟨x, hx, heqj⟩
  rcases hk with ⟨y, hy, heqk⟩
  have hxy : x = y := interiorIncl_injective (heqj.trans heqk.symm)
  have hjk' : j.1 = k.1 := by simpa using hx.symm.trans (hxy.trans hy)
  exact hjk (Subtype.ext hjk')

/-- For a fixed target label, distinct source cells are disjoint. -/
private theorem atomicPairCell_disjoint_left {D E : FiniteWeightedDiagram}
    (j : E.supportLabels) {i k : D.supportLabels} (hik : i ≠ k) :
    Disjoint (atomicPairCell i j) (atomicPairCell k j) := by
  apply Set.disjoint_left.mpr
  intro z hzi hzk
  have hi : z ∈ firstFiber {i.1} := hzi.1
  have hk : z ∈ firstFiber {k.1} := hzk.1
  rcases hi with ⟨x, hx, heqi⟩
  rcases hk with ⟨y, hy, heqk⟩
  have hxy : x = y := interiorIncl_injective (heqi.trans heqk.symm)
  have hik' : i.1 = k.1 := by simpa using hx.symm.trans (hxy.trans hy)
  exact hik (Subtype.ext hik')

private theorem atomicPairCell_row_measure_le {D E : FiniteWeightedDiagram}
    (π : Measure PlanSpace) (i : D.supportLabels) :
    (∑ j : E.supportLabels, π (atomicPairCell i j)) ≤
      π (firstFiber {i.1}) := by
  have hdisj : PairwiseDisjoint (Set.univ : Set E.supportLabels)
      (fun j => atomicPairCell i j) := by
    intro j _ k _ hjk
    exact atomicPairCell_disjoint_right i hjk
  have hsum := measure_biUnion_finset (μ := π) (s := Finset.univ) (by simpa using hdisj)
    (fun j _ => measurableSet_atomicPairCell i j)
  rw [← hsum]
  exact measure_mono (by
    intro z hz
    simp only [Set.mem_iUnion] at hz
    rcases hz with ⟨j, _, hzj⟩
    exact hzj.1)

private theorem atomicPairCell_col_measure_le {D E : FiniteWeightedDiagram}
    (π : Measure PlanSpace) (j : E.supportLabels) :
    (∑ i : D.supportLabels, π (atomicPairCell i j)) ≤
      π (secondFiber {j.1}) := by
  have hdisj : PairwiseDisjoint (Set.univ : Set D.supportLabels)
      (fun i => atomicPairCell i j) := by
    intro i _ k _ hik
    exact atomicPairCell_disjoint_left j hik
  have hsum := measure_biUnion_finset (μ := π) (s := Finset.univ) (by simpa using hdisj)
    (fun i _ => measurableSet_atomicPairCell i j)
  rw [← hsum]
  exact measure_mono (by
    intro z hz
    simp only [Set.mem_iUnion] at hz
    rcases hz with ⟨i, _, hzi⟩
    exact hzi.2)

/-- The interior–interior singleton masses of a Borel plan form a feasible native
weighted matrix. Finiteness comes from the two finite atomic marginals. -/
def extractedAtomicPlan {D E : FiniteWeightedDiagram} (π : Measure PlanSpace)
    (hπ : IsBoundaryPlan π (atomicMeasure D) (atomicMeasure E)) :
    FiniteWeightedBoundaryPlan D.weights E.weights := by
  letI : IsFiniteMeasure (atomicMeasure D) := atomicMeasure_isFinite D
  letI : IsFiniteMeasure (atomicMeasure E) := atomicMeasure_isFinite E
  letI : IsFiniteMeasure π := boundaryPlan_isFiniteMeasure hπ
  let m : D.supportLabels → E.supportLabels → ℝ :=
    fun i j => (π (atomicPairCell i j)).toReal
  have hfinite (s : Set PlanSpace) : π s ≠ ∞ :=
    ((measure_mono (subset_univ s)).trans_lt (measure_lt_top π Set.univ)).ne
  refine ⟨m, (fun i j => ENNReal.toReal_nonneg), ?_, ?_⟩
  · intro i
    have hrow := atomicPairCell_row_measure_le (D := D) (E := E) π i
    rw [hπ.first {i.1} (measurableSet_singleton i.1),
      atomicMeasure_singleton] at hrow
    have hreal := (ENNReal.toReal_le_toReal
      (by exact (ENNReal.sum_lt_top.mpr (fun j _ => (hfinite _).lt_top)).ne)
      ENNReal.coe_ne_top).2 hrow
    simpa only [m, FiniteWeightedDiagram.weights, ENNReal.toReal_sum
      (fun j _ => hfinite _), ENNReal.coe_toReal] using hreal
  · intro j
    have hcol := atomicPairCell_col_measure_le (D := D) (E := E) π j
    rw [hπ.second {j.1} (measurableSet_singleton j.1),
      atomicMeasure_singleton] at hcol
    have hreal := (ENNReal.toReal_le_toReal
      (by exact (ENNReal.sum_lt_top.mpr (fun i _ => (hfinite _).lt_top)).ne)
      ENNReal.coe_ne_top).2 hcol
    simpa only [m, FiniteWeightedDiagram.weights, ENNReal.toReal_sum
      (fun i _ => hfinite _), ENNReal.coe_toReal] using hreal

/-- A source atom paired with any (possibly non-nearest) diagonal endpoint. -/
def atomicDeleteCell {D : FiniteWeightedDiagram} (i : D.supportLabels) :
    Set PlanSpace := firstFiber {i.1} \ secondFiber Set.univ

/-- A target atom paired with any (possibly non-nearest) diagonal endpoint. -/
def atomicInsertCell {E : FiniteWeightedDiagram} (j : E.supportLabels) :
    Set PlanSpace := secondFiber {j.1} \ firstFiber Set.univ

theorem measurableSet_atomicDeleteCell {D : FiniteWeightedDiagram}
    (i : D.supportLabels) : MeasurableSet (atomicDeleteCell i) :=
  (measurableSet_firstFiber (measurableSet_singleton i.1)).diff
    (measurableSet_secondFiber MeasurableSet.univ)

theorem measurableSet_atomicInsertCell {E : FiniteWeightedDiagram}
    (j : E.supportLabels) : MeasurableSet (atomicInsertCell j) :=
  (measurableSet_secondFiber (measurableSet_singleton j.1)).diff
    (measurableSet_firstFiber MeasurableSet.univ)

private theorem collapse_eq_boundary_of_not_secondFiber (z : PlanSpace)
    (hz : z ∉ secondFiber Set.univ) : collapse z.1.2 = Space.boundary := by
  have h : ¬ z.1.2.1.1 < z.1.2.1.2 := by
    intro h
    exact hz ⟨⟨z.1.2.1, h⟩, Set.mem_univ _, Subtype.ext rfl⟩
  simp [collapse, h]

private theorem collapse_eq_boundary_of_not_firstFiber (z : PlanSpace)
    (hz : z ∉ firstFiber Set.univ) : collapse z.1.1 = Space.boundary := by
  have h : ¬ z.1.1.1.1 < z.1.1.1.2 := by
    intro h
    exact hz ⟨⟨z.1.1.1, h⟩, Set.mem_univ _, Subtype.ext rfl⟩
  simp [collapse, h]

/-- The native deletion charge is bounded by the cost of every arbitrary
diagonal endpoint in this cell. -/
private theorem atomicDeleteCell_cost_le (p : ℝ) (hp : 0 ≤ p)
    {D : FiniteWeightedDiagram} (i : D.supportLabels) {z : PlanSpace}
    (hz : z ∈ atomicDeleteCell i) :
    ENNReal.ofReal ((diagonalCost (D.coordinates i)).toReal ^ p) ≤
      planPowerCost p z := by
  have hfirst : z.1.1 = interiorIncl i.1 := by
    rcases hz.1 with ⟨x, hx, heq⟩
    have hxi : x = i.1 := hx
    exact hxi ▸ heq.symm
  have hbound := collapsePlanPair_powerCost_le p hp z
  rw [hfirst, collapse_eq_boundary_of_not_secondFiber z hz.2] at hbound
  simpa only [interiorIncl, collapse_interior, dist_point_boundary,
    depth, FiniteWeightedDiagram.coordinates] using hbound

/-- The native insertion charge is bounded by the cost of every arbitrary
diagonal endpoint in this cell. -/
private theorem atomicInsertCell_cost_le (p : ℝ) (hp : 0 ≤ p)
    {E : FiniteWeightedDiagram} (j : E.supportLabels) {z : PlanSpace}
    (hz : z ∈ atomicInsertCell j) :
    ENNReal.ofReal ((diagonalCost (E.coordinates j)).toReal ^ p) ≤
      planPowerCost p z := by
  have hsecond : z.1.2 = interiorIncl j.1 := by
    rcases hz.1 with ⟨x, hx, heq⟩
    have hxj : x = j.1 := hx
    exact hxj ▸ heq.symm
  have hbound := collapsePlanPair_powerCost_le p hp z
  rw [hsecond, collapse_eq_boundary_of_not_firstFiber z hz.2] at hbound
  simpa only [interiorIncl, collapse_interior, dist_boundary_point,
    depth, FiniteWeightedDiagram.coordinates] using hbound

private theorem secondFiber_support_eq_iUnion (E : FiniteWeightedDiagram) :
    secondFiber (↑E.support : Set Interior) =
      ⋃ j : E.supportLabels, secondFiber {j.1} := by
  ext z
  constructor
  · rintro ⟨x, hx, heq⟩
    exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, x, rfl, heq⟩
  · intro hz
    obtain ⟨j, x, hx, heq⟩ := Set.mem_iUnion.mp hz
    exact ⟨x, hx ▸ j.2, heq⟩

private theorem firstFiber_support_eq_iUnion (D : FiniteWeightedDiagram) :
    firstFiber (↑D.support : Set Interior) =
      ⋃ i : D.supportLabels, firstFiber {i.1} := by
  ext z
  constructor
  · rintro ⟨x, hx, heq⟩
    exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, x, rfl, heq⟩
  · intro hz
    obtain ⟨i, x, hx, heq⟩ := Set.mem_iUnion.mp hz
    exact ⟨x, hx ▸ i.2, heq⟩

private theorem atomicMeasure_support_compl_zero (D : FiniteWeightedDiagram) :
    atomicMeasure D (↑D.support : Set Interior)ᶜ = 0 := by
  rw [atomicMeasure_apply D _ (D.support.finite_toSet.measurableSet.compl)]
  apply Finset.sum_eq_zero
  intro i _
  simp

private theorem secondFiber_outside_support_null {E : FiniteWeightedDiagram}
    {π : Measure PlanSpace} {μ : Measure Interior}
    (hπ : IsBoundaryPlan π μ (atomicMeasure E)) :
    π (secondFiber Set.univ \ secondFiber (↑E.support : Set Interior)) = 0 := by
  apply le_antisymm ?_ bot_le
  calc
    _ ≤ π (secondFiber (↑E.support : Set Interior)ᶜ) := by
      apply measure_mono
      rintro z ⟨⟨x, _, heq⟩, hnot⟩
      refine ⟨x, ?_, heq⟩
      intro hx
      exact hnot ⟨x, hx, heq⟩
    _ = atomicMeasure E (↑E.support : Set Interior)ᶜ :=
      hπ.second _ (E.support.finite_toSet.measurableSet.compl)
    _ = 0 := atomicMeasure_support_compl_zero E

private theorem firstFiber_outside_support_null {D : FiniteWeightedDiagram}
    {π : Measure PlanSpace} {ν : Measure Interior}
    (hπ : IsBoundaryPlan π (atomicMeasure D) ν) :
    π (firstFiber Set.univ \ firstFiber (↑D.support : Set Interior)) = 0 := by
  apply le_antisymm ?_ bot_le
  calc
    _ ≤ π (firstFiber (↑D.support : Set Interior)ᶜ) := by
      apply measure_mono
      rintro z ⟨⟨x, _, heq⟩, hnot⟩
      refine ⟨x, ?_, heq⟩
      intro hx
      exact hnot ⟨x, hx, heq⟩
    _ = atomicMeasure D (↑D.support : Set Interior)ᶜ :=
      hπ.first _ (D.support.finite_toSet.measurableSet.compl)
    _ = 0 := atomicMeasure_support_compl_zero D

private theorem atomicPairCell_row_measure_eq {D E : FiniteWeightedDiagram}
    (π : Measure PlanSpace) (i : D.supportLabels) :
    (∑ j : E.supportLabels, π (atomicPairCell i j)) =
      π (firstFiber {i.1} ∩ secondFiber (↑E.support : Set Interior)) := by
  have hdisj : PairwiseDisjoint (Set.univ : Set E.supportLabels)
      (fun j => atomicPairCell i j) := by
    intro j _ k _ hjk
    exact atomicPairCell_disjoint_right i hjk
  rw [← measure_biUnion_finset (μ := π) (s := Finset.univ)
    (by simpa using hdisj) (fun j _ => measurableSet_atomicPairCell i j)]
  congr 1
  ext z
  simp only [Finset.mem_univ, Set.iUnion_true, Set.mem_iUnion, atomicPairCell,
    Set.mem_inter_iff]
  rw [secondFiber_support_eq_iUnion]
  simp only [Set.mem_iUnion]
  tauto

private theorem atomicPairCell_col_measure_eq {D E : FiniteWeightedDiagram}
    (π : Measure PlanSpace) (j : E.supportLabels) :
    (∑ i : D.supportLabels, π (atomicPairCell i j)) =
      π (secondFiber {j.1} ∩ firstFiber (↑D.support : Set Interior)) := by
  have hdisj : PairwiseDisjoint (Set.univ : Set D.supportLabels)
      (fun i => atomicPairCell i j) := by
    intro i _ k _ hik
    exact atomicPairCell_disjoint_left j hik
  rw [← measure_biUnion_finset (μ := π) (s := Finset.univ)
    (by simpa using hdisj) (fun i _ => measurableSet_atomicPairCell i j)]
  congr 1
  ext z
  simp only [Finset.mem_univ, Set.iUnion_true, Set.mem_iUnion, atomicPairCell,
    Set.mem_inter_iff]
  rw [firstFiber_support_eq_iUnion]
  simp only [Set.mem_iUnion]
  tauto

private theorem measure_sdiff_eq_of_null_between {α : Type*} [MeasurableSpace α]
    (π : Measure α) (s t u : Set α) (htu : t ⊆ u)
    (hu : MeasurableSet u) (hnull : π (u \ t) = 0) :
    π (s \ t) = π (s \ u) := by
  have hpart := measure_sdiff_add_inter (μ := π) (s \ t) hu
  have hzero : π ((s \ t) ∩ u) = 0 := by
    apply le_antisymm ?_ bot_le
    calc
      _ ≤ π (u \ t) := by
        apply measure_mono
        rintro x ⟨⟨_, hxt⟩, hxu⟩
        exact ⟨hxu, hxt⟩
      _ = 0 := hnull
  have heq : (s \ t) \ u = s \ u := by
    ext x
    simp only [Set.mem_sdiff]
    constructor
    · exact fun h => ⟨h.1.1, h.2⟩
    · exact fun h => ⟨⟨h.1, fun hxt => h.2 (htu hxt)⟩, h.2⟩
  rw [hzero, add_zero, heq] at hpart
  exact hpart.symm

private theorem atomicPairCell_row_delete_balance {D E : FiniteWeightedDiagram}
    {π : Measure PlanSpace}
    (hπ : IsBoundaryPlan π (atomicMeasure D) (atomicMeasure E))
    (i : D.supportLabels) :
    (∑ j : E.supportLabels, π (atomicPairCell i j)) +
      π (atomicDeleteCell i) = (D.weights i : ℝ≥0∞) := by
  rw [atomicPairCell_row_measure_eq]
  have hpart := measure_inter_add_sdiff (μ := π) (firstFiber {i.1})
    (measurableSet_secondFiber E.support.finite_toSet.measurableSet)
  rw [measure_sdiff_eq_of_null_between π (firstFiber {i.1})
    (secondFiber (↑E.support : Set Interior)) (secondFiber Set.univ)
    (by
      rintro z ⟨x, _, heq⟩
      exact ⟨x, Set.mem_univ _, heq⟩)
    (measurableSet_secondFiber MeasurableSet.univ)
    (secondFiber_outside_support_null hπ)] at hpart
  change π (firstFiber {i.1} ∩ secondFiber (↑E.support : Set Interior)) +
    π (atomicDeleteCell i) = (D.weights i : ℝ≥0∞)
  exact hpart.trans ((hπ.first _ (measurableSet_singleton i.1)).trans
    (atomicMeasure_singleton D i.1))

private theorem atomicPairCell_col_insert_balance {D E : FiniteWeightedDiagram}
    {π : Measure PlanSpace}
    (hπ : IsBoundaryPlan π (atomicMeasure D) (atomicMeasure E))
    (j : E.supportLabels) :
    (∑ i : D.supportLabels, π (atomicPairCell i j)) +
      π (atomicInsertCell j) = (E.weights j : ℝ≥0∞) := by
  rw [atomicPairCell_col_measure_eq]
  have hpart := measure_inter_add_sdiff (μ := π) (secondFiber {j.1})
    (measurableSet_firstFiber D.support.finite_toSet.measurableSet)
  rw [measure_sdiff_eq_of_null_between π (secondFiber {j.1})
    (firstFiber (↑D.support : Set Interior)) (firstFiber Set.univ)
    (by
      rintro z ⟨x, _, heq⟩
      exact ⟨x, Set.mem_univ _, heq⟩)
    (measurableSet_firstFiber MeasurableSet.univ)
    (firstFiber_outside_support_null hπ)] at hpart
  change π (secondFiber {j.1} ∩ firstFiber (↑D.support : Set Interior)) +
    π (atomicInsertCell j) = (E.weights j : ℝ≥0∞)
  exact hpart.trans ((hπ.second _ (measurableSet_singleton j.1)).trans
    (atomicMeasure_singleton E j.1))

/-- Each extracted matrix entry is precisely the real mass of its Borel pair cell. -/
theorem extractedAtomicPlan_mass {D E : FiniteWeightedDiagram}
    {π : Measure PlanSpace}
    (hπ : IsBoundaryPlan π (atomicMeasure D) (atomicMeasure E))
    (i : D.supportLabels) (j : E.supportLabels) :
    (extractedAtomicPlan π hπ).mass i j = (π (atomicPairCell i j)).toReal := rfl

private theorem extractedAtomicPlan_deletionMass {D E : FiniteWeightedDiagram}
    {π : Measure PlanSpace}
    (hπ : IsBoundaryPlan π (atomicMeasure D) (atomicMeasure E))
    (i : D.supportLabels) :
    (extractedAtomicPlan π hπ).deletionMass i = (π (atomicDeleteCell i)).toReal := by
  have : IsFiniteMeasure (atomicMeasure D) := atomicMeasure_isFinite D
  have : IsFiniteMeasure (atomicMeasure E) := atomicMeasure_isFinite E
  have : IsFiniteMeasure π := boundaryPlan_isFiniteMeasure hπ
  have hfinite (s : Set PlanSpace) : π s ≠ ∞ :=
    ((measure_mono (subset_univ s)).trans_lt (measure_lt_top π Set.univ)).ne
  have hbal := atomicPairCell_row_delete_balance hπ i
  have hreal := congrArg ENNReal.toReal hbal
  rw [ENNReal.toReal_add (by exact (ENNReal.sum_lt_top.mpr
      (fun j _ => (hfinite _).lt_top)).ne) (hfinite _),
    ENNReal.toReal_sum (fun j _ => hfinite _)] at hreal
  simp only [ENNReal.coe_toReal] at hreal
  simp only [FiniteWeightedBoundaryPlan.deletionMass, extractedAtomicPlan_mass]
  linarith only [hreal]

private theorem extractedAtomicPlan_insertionMass {D E : FiniteWeightedDiagram}
    {π : Measure PlanSpace}
    (hπ : IsBoundaryPlan π (atomicMeasure D) (atomicMeasure E))
    (j : E.supportLabels) :
    (extractedAtomicPlan π hπ).insertionMass j = (π (atomicInsertCell j)).toReal := by
  have : IsFiniteMeasure (atomicMeasure D) := atomicMeasure_isFinite D
  have : IsFiniteMeasure (atomicMeasure E) := atomicMeasure_isFinite E
  have : IsFiniteMeasure π := boundaryPlan_isFiniteMeasure hπ
  have hfinite (s : Set PlanSpace) : π s ≠ ∞ :=
    ((measure_mono (subset_univ s)).trans_lt (measure_lt_top π Set.univ)).ne
  have hbal := atomicPairCell_col_insert_balance hπ j
  have hreal := congrArg ENNReal.toReal hbal
  rw [ENNReal.toReal_add (by exact (ENNReal.sum_lt_top.mpr
      (fun i _ => (hfinite _).lt_top)).ne) (hfinite _),
    ENNReal.toReal_sum (fun i _ => hfinite _)] at hreal
  simp only [ENNReal.coe_toReal] at hreal
  simp only [FiniteWeightedBoundaryPlan.insertionMass, extractedAtomicPlan_mass]
  linarith only [hreal]

private theorem firstFiber_singleton_label_eq {D : FiniteWeightedDiagram}
    {i k : D.supportLabels} {z : PlanSpace}
    (hi : z ∈ firstFiber {i.1}) (hk : z ∈ firstFiber {k.1}) : i = k := by
  rcases hi with ⟨x, hx, heqx⟩
  rcases hk with ⟨y, hy, heqy⟩
  have hxy : x = y := interiorIncl_injective (heqx.trans heqy.symm)
  exact Subtype.ext (hx.symm.trans (hxy.trans hy))

private theorem secondFiber_singleton_label_eq {E : FiniteWeightedDiagram}
    {j k : E.supportLabels} {z : PlanSpace}
    (hj : z ∈ secondFiber {j.1}) (hk : z ∈ secondFiber {k.1}) : j = k := by
  rcases hj with ⟨x, hx, heqx⟩
  rcases hk with ⟨y, hy, heqy⟩
  have hxy : x = y := interiorIncl_injective (heqx.trans heqy.symm)
  exact Subtype.ext (hx.symm.trans (hxy.trans hy))

private abbrev AtomicCellIndex (D E : FiniteWeightedDiagram) :=
  (D.supportLabels × E.supportLabels) ⊕ (D.supportLabels ⊕ E.supportLabels)

private def atomicCell {D E : FiniteWeightedDiagram} :
    AtomicCellIndex D E → Set PlanSpace
  | .inl (i, j) => atomicPairCell i j
  | .inr (.inl i) => atomicDeleteCell i
  | .inr (.inr j) => atomicInsertCell j

private def atomicCellCharge (p : ℝ) {D E : FiniteWeightedDiagram} :
    AtomicCellIndex D E → ℝ≥0∞
  | .inl (i, j) =>
      ENNReal.ofReal ((finitePairCost (D.coordinates i) (E.coordinates j)).toReal ^ p)
  | .inr (.inl i) =>
      ENNReal.ofReal ((diagonalCost (D.coordinates i)).toReal ^ p)
  | .inr (.inr j) =>
      ENNReal.ofReal ((diagonalCost (E.coordinates j)).toReal ^ p)

private theorem measurableSet_atomicCell {D E : FiniteWeightedDiagram}
    (a : AtomicCellIndex D E) : MeasurableSet (atomicCell a) := by
  rcases a with ⟨i, j⟩ | i | j
  · exact measurableSet_atomicPairCell i j
  · exact measurableSet_atomicDeleteCell i
  · exact measurableSet_atomicInsertCell j

private theorem atomicCell_unique {D E : FiniteWeightedDiagram}
    {a b : AtomicCellIndex D E} {z : PlanSpace}
    (ha : z ∈ atomicCell a) (hb : z ∈ atomicCell b) : a = b := by
  rcases a with ⟨i, j⟩ | i | j <;> rcases b with ⟨k, l⟩ | k | l
  · exact congrArg Sum.inl (Prod.ext
      (firstFiber_singleton_label_eq ha.1 hb.1)
      (secondFiber_singleton_label_eq ha.2 hb.2))
  · exact False.elim (hb.2 (by
      rcases ha.2 with ⟨x, _, heq⟩
      exact ⟨x, Set.mem_univ _, heq⟩))
  · exact False.elim (hb.2 (by
      rcases ha.1 with ⟨x, _, heq⟩
      exact ⟨x, Set.mem_univ _, heq⟩))
  · exact False.elim (ha.2 (by
      rcases hb.2 with ⟨x, _, heq⟩
      exact ⟨x, Set.mem_univ _, heq⟩))
  · exact congrArg (Sum.inr ∘ Sum.inl)
      (firstFiber_singleton_label_eq ha.1 hb.1)
  · exact False.elim (hb.2 (by
      rcases ha.1 with ⟨x, _, heq⟩
      exact ⟨x, Set.mem_univ _, heq⟩))
  · exact False.elim (ha.2 (by
      rcases hb.1 with ⟨x, _, heq⟩
      exact ⟨x, Set.mem_univ _, heq⟩))
  · exact False.elim (ha.2 (by
      rcases hb.1 with ⟨x, _, heq⟩
      exact ⟨x, Set.mem_univ _, heq⟩))
  · exact congrArg (Sum.inr ∘ Sum.inr)
      (secondFiber_singleton_label_eq ha.1 hb.1)

private theorem atomicCell_charge_le (p : ℝ) (hp : 0 ≤ p)
    {D E : FiniteWeightedDiagram} (a : AtomicCellIndex D E)
    {z : PlanSpace} (hz : z ∈ atomicCell a) :
    atomicCellCharge p a ≤ planPowerCost p z := by
  rcases a with ⟨i, j⟩ | i | j
  · have hfirst : z.1.1 = interiorIncl i.1 := by
      rcases hz.1 with ⟨x, hx, heq⟩
      exact hx ▸ heq.symm
    have hsecond : z.1.2 = interiorIncl j.1 := by
      rcases hz.2 with ⟨x, hx, heq⟩
      exact hx ▸ heq.symm
    have heq : z = directLeg i j := by
      apply Subtype.ext
      exact Prod.ext hfirst hsecond
    simpa only [heq, atomicCellCharge, planPowerCost_directLeg] using
      (le_refl (atomicCellCharge p (Sum.inl (i, j))))
  · exact atomicDeleteCell_cost_le p hp i hz
  · exact atomicInsertCell_cost_le p hp j hz

private theorem atomicCell_charge_integral_le (p : ℝ) (hp : 0 ≤ p)
    {D E : FiniteWeightedDiagram} (π : Measure PlanSpace)
    (a : AtomicCellIndex D E) :
    atomicCellCharge p a * π (atomicCell a) ≤
      ∫⁻ z in atomicCell a, planPowerCost p z ∂π := by
  let s := atomicCell a
  have hs : MeasurableSet s := measurableSet_atomicCell a
  calc
    _ = ∫⁻ z, s.indicator (fun _ => atomicCellCharge p a) z ∂π := by
      rw [lintegral_indicator_const hs]
    _ ≤ ∫⁻ z, s.indicator (planPowerCost p) z ∂π := by
      apply lintegral_mono
      intro z
      by_cases hz : z ∈ s
      · simpa [Set.indicator_of_mem hz] using atomicCell_charge_le p hp a hz
      · simp [Set.indicator_of_notMem hz]
    _ = _ := lintegral_indicator hs (planPowerCost p)

private theorem atomicCell_charge_sum_le_cost (p : ℝ) (hp : 0 ≤ p)
    {D E : FiniteWeightedDiagram} (π : Measure PlanSpace) :
    (∑ a : AtomicCellIndex D E,
      atomicCellCharge p a * π (atomicCell a)) ≤
      ∫⁻ z, planPowerCost p z ∂π := by
  have hdisj : Pairwise (fun a b : AtomicCellIndex D E =>
      Disjoint (atomicCell a) (atomicCell b)) := by
    intro a b hab
    apply Set.disjoint_left.mpr
    intro z ha hb
    exact hab (atomicCell_unique ha hb)
  have hrestr : π.restrict (⋃ a : AtomicCellIndex D E, atomicCell a) =
      Measure.sum (fun a : AtomicCellIndex D E => π.restrict (atomicCell a)) :=
    Measure.restrict_iUnion hdisj measurableSet_atomicCell
  calc
    _ ≤ ∑ a : AtomicCellIndex D E,
        ∫⁻ z in atomicCell a, planPowerCost p z ∂π :=
      Finset.sum_le_sum (fun a _ => atomicCell_charge_integral_le p hp π a)
    _ = ∫⁻ z in (⋃ a : AtomicCellIndex D E, atomicCell a),
        planPowerCost p z ∂π := by
      rw [hrestr, lintegral_sum_measure, tsum_fintype]
    _ ≤ ∫⁻ z, planPowerCost p z ∂π := by
      simpa only [Measure.restrict_univ] using
        (lintegral_mono_set (μ := π) (f := planPowerCost p) (Set.subset_univ _))

private theorem extractedAtomicPlan_cost_eq_cell_sum (p : ℝ)
    {D E : FiniteWeightedDiagram} {π : Measure PlanSpace}
    (hπ : IsBoundaryPlan π (atomicMeasure D) (atomicMeasure E)) :
    ENNReal.ofReal ((extractedAtomicPlan π hπ).powerCost p
      D.coordinates E.coordinates) =
      ∑ a : AtomicCellIndex D E,
        atomicCellCharge p a * π (atomicCell a) := by
  have : IsFiniteMeasure (atomicMeasure D) := atomicMeasure_isFinite D
  have : IsFiniteMeasure (atomicMeasure E) := atomicMeasure_isFinite E
  have : IsFiniteMeasure π := boundaryPlan_isFiniteMeasure hπ
  have hfinite (s : Set PlanSpace) : π s ≠ ∞ :=
    ((measure_mono (subset_univ s)).trans_lt (measure_lt_top π Set.univ)).ne
  rw [← atomicBoundaryPlan_cost_native p D E (extractedAtomicPlan π hπ),
    atomicBoundaryPlan_cost_sum]
  simp_rw [extractedAtomicPlan_mass hπ, extractedAtomicPlan_deletionMass hπ,
    extractedAtomicPlan_insertionMass hπ]
  simp_rw [ENNReal.ofReal_toReal (hfinite _)]
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, atomicCell,
    atomicCellCharge, add_assoc]
  simp only [mul_comm]

/-- Every admissible Borel competitor, including one of infinite powered cost,
dominates the native finite matrix extracted from its singleton pair cells. -/
theorem extractedAtomicPlan_cost_le (p : ℝ) (hp : 0 ≤ p)
    {D E : FiniteWeightedDiagram} {π : Measure PlanSpace}
    (hπ : IsBoundaryPlan π (atomicMeasure D) (atomicMeasure E)) :
    ENNReal.ofReal ((extractedAtomicPlan π hπ).powerCost p
      D.coordinates E.coordinates) ≤
      ∫⁻ z, planPowerCost p z ∂π := by
  rw [extractedAtomicPlan_cost_eq_cell_sum p hπ]
  exact atomicCell_charge_sum_le_cost p hp π

/-- No boundary plan between atomic inputs can beat the native finite weighted
optimum, even with continuously distributed non-nearest diagonal endpoints or infinite cost. -/
theorem native_le_boundaryTransportPowerValue_atomic (p : ℝ) (hp : 0 ≤ p)
    (D E : FiniteWeightedDiagram) :
    ENNReal.ofReal (FiniteWeightedDiagram.powerBoundaryTransportCost p D E) ≤
      boundaryTransportPowerValue p (atomicMeasure D) (atomicMeasure E) := by
  apply le_iInf
  intro π
  apply le_iInf
  intro hπ
  exact (ENNReal.ofReal_le_ofReal
    (weightedPowerBoundaryTransportCost_le_plan p D.weights E.weights
      D.coordinates E.coordinates (extractedAtomicPlan π hπ))).trans
    (extractedAtomicPlan_cost_le p hp hπ)

/-- Exact powered equality between the all-Borel-plan value and the native
finite weighted optimizer for every nonnegative exponent. -/
theorem boundaryTransportPowerValue_atomic_eq_native (p : ℝ) (hp : 0 ≤ p)
    (D E : FiniteWeightedDiagram) :
    boundaryTransportPowerValue p (atomicMeasure D) (atomicMeasure E) =
      ENNReal.ofReal (FiniteWeightedDiagram.powerBoundaryTransportCost p D E) := by
  exact le_antisymm (boundaryTransportPowerValue_atomic_le_native p D E)
    (native_le_boundaryTransportPowerValue_atomic p hp D E)

/-- The native finite optimizer yields a genuine minimizing Borel boundary
measure, including empty inputs and fractional or coalesced atom masses. -/
theorem exists_atomic_minimizing_boundaryPlan (p : ℝ) (hp : 0 ≤ p)
    (D E : FiniteWeightedDiagram) :
    ∃ π : Measure PlanSpace,
      IsBoundaryPlan π (atomicMeasure D) (atomicMeasure E) ∧
      (∫⁻ z, planPowerCost p z ∂π) =
        boundaryTransportPowerValue p (atomicMeasure D) (atomicMeasure E) := by
  obtain ⟨a, ha⟩ := FiniteWeightedDiagram.exists_minimizing_powerPlan p D E
  refine ⟨atomicBoundaryPlan D E a, atomicBoundaryPlan_admissible D E a, ?_⟩
  rw [atomicBoundaryPlan_cost_native, ha,
    boundaryTransportPowerValue_atomic_eq_native p hp]

/-- The rooted atomic distance agrees exactly with the native finite weighted
root, with the same maximum-norm geometry and linear mass coefficients. -/
theorem boundaryTransportDistance_atomic_eq_native (p : ℝ) (hp : 1 ≤ p)
    (D E : FiniteWeightedDiagram) :
    boundaryTransportDistance p (atomicMeasure D) (atomicMeasure E) =
      ENNReal.ofReal (FiniteWeightedDiagram.pBoundaryTransportCost p D E) := by
  rw [boundaryTransportDistance,
    boundaryTransportPowerValue_atomic_eq_native p (zero_le_one.trans hp) D E]
  change (ENNReal.ofReal (FiniteWeightedDiagram.powerBoundaryTransportCost p D E)) ^
      (1 / p) =
    ENNReal.ofReal ((FiniteWeightedDiagram.powerBoundaryTransportCost p D E) ^ p⁻¹)
  have hnonneg : 0 ≤ FiniteWeightedDiagram.powerBoundaryTransportCost p D E :=
    weightedPowerBoundaryTransportCost_nonneg p D.weights E.weights
      D.coordinates E.coordinates
  simpa only [one_div] using
    (ENNReal.ofReal_rpow_of_nonneg hnonneg
      (one_div_nonneg.mpr (zero_le_one.trans hp)))

end TDA.Persistence.BoundaryTransport
