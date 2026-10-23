import TDA.Persistence.BoundaryPlans
import TDA.Persistence.ReservoirMeasure
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.MeanInequalitiesPow

/-!
# From reservoir competitors to boundary plans

Retain direct interior pairs when their ground distance is smaller. Split the
remaining interior pairs into nearest-diagonal legs, retain the interior–boundary
legs and discard boundary–boundary mass. Measurable restrictions and pushforwards
preserve both interior marginals and do not increase powered cost for p at least one.
-/

set_option autoImplicit false
noncomputable section
namespace TDA.Persistence.BoundaryTransport.Reverse
open Set MeasureTheory
open scoped ENNReal

private def fallback : Interior := ⟨(0, 1), by norm_num⟩
private def unpoint : Space → Interior
  | .point x => x
  | .boundary => fallback

@[simp] private theorem unpoint_point (x : Interior) : unpoint (.point x) = x := rfl

private theorem measurable_unpoint : Measurable unpoint := by
  intro s hs
  apply (measurableSet_iff_interior _).mpr
  have h : Space.point ⁻¹' (unpoint ⁻¹' s) = s := by ext x; rfl
  rw [h]
  exact hs

private def directLeg (z : Interior × Interior) : PlanSpace :=
  ⟨(interiorIncl z.1, interiorIncl z.2), Or.inl z.1.2⟩

private theorem measurable_directLeg : Measurable directLeg := by
  apply Continuous.measurable
  unfold directLeg
  exact ((continuous_interiorIncl.comp continuous_fst).prodMk
    (continuous_interiorIncl.comp continuous_snd)).subtype_mk _

private def endpoints (z : Space × Space) : Interior × Interior :=
  (unpoint z.1, unpoint z.2)

private theorem measurable_endpoints : Measurable endpoints :=
  (measurable_unpoint.comp measurable_fst).prodMk (measurable_unpoint.comp measurable_snd)

private def firstInterior : Set (Space × Space) := Prod.fst ⁻¹' range Space.point
private def secondInterior : Set (Space × Space) := Prod.snd ⁻¹' range Space.point

private theorem measurableSet_firstInterior : MeasurableSet firstInterior :=
  measurableEmbedding_point.measurableSet_range.preimage measurable_fst

private theorem measurableSet_secondInterior : MeasurableSet secondInterior :=
  measurableEmbedding_point.measurableSet_range.preimage measurable_snd

private def directRegion : Set (Space × Space) :=
  firstInterior ∩ secondInterior ∩
    {z | dist (unpoint z.1) (unpoint z.2) ≤ depth (unpoint z.1) + depth (unpoint z.2)}

private def deleteRegion : Set (Space × Space) := firstInterior ∩ directRegionᶜ
private def insertRegion : Set (Space × Space) := secondInterior ∩ directRegionᶜ

private theorem measurable_depth : Measurable depth := by
  change Measurable (fun x : Interior => depth x)
  simp_rw [depth_eq]
  fun_prop

private theorem measurableSet_directRegion : MeasurableSet directRegion := by
  apply (measurableSet_firstInterior.inter measurableSet_secondInterior).inter
  exact measurableSet_le
    ((measurable_unpoint.comp measurable_fst).dist (measurable_unpoint.comp measurable_snd))
    ((measurable_depth.comp (measurable_unpoint.comp measurable_fst)).add
      (measurable_depth.comp (measurable_unpoint.comp measurable_snd)))

private theorem measurableSet_deleteRegion : MeasurableSet deleteRegion :=
  measurableSet_firstInterior.inter measurableSet_directRegion.compl

private theorem measurableSet_insertRegion : MeasurableSet insertRegion :=
  measurableSet_secondInterior.inter measurableSet_directRegion.compl

private def directMap : Space × Space → PlanSpace := directLeg ∘ endpoints
private def deleteMap : Space × Space → PlanSpace := deleteLeg ∘ unpoint ∘ Prod.fst
private def insertMap : Space × Space → PlanSpace := insertLeg ∘ unpoint ∘ Prod.snd

private theorem measurable_directMap : Measurable directMap :=
  measurable_directLeg.comp measurable_endpoints

private theorem measurable_deleteMap : Measurable deleteMap :=
  measurable_deleteLeg.comp (measurable_unpoint.comp measurable_fst)

private theorem measurable_insertMap : Measurable insertMap :=
  measurable_insertLeg.comp (measurable_unpoint.comp measurable_snd)

/-- The direct part is retained; every remaining interior endpoint receives its nearest
boundary leg. The boundary–boundary mass is discarded. -/
def boundaryPlan (γ : Measure (Space × Space)) : Measure PlanSpace :=
  (γ.restrict directRegion).map directMap +
    (γ.restrict deleteRegion).map deleteMap +
    (γ.restrict insertRegion).map insertMap

@[simp] theorem interiorIncl_mem_image (x : Interior) (s : Set Interior) :
    interiorIncl x ∈ interiorIncl '' s ↔ x ∈ s := by
  exact interiorIncl_injective.mem_set_image

@[simp] theorem diagonalProjection_not_mem_image (x : Interior) (s : Set Interior) :
    diagonalProjection x ∉ interiorIncl '' s := by
  rintro ⟨y, _, h⟩
  have hy : (diagonalProjection x).1.1 < (diagonalProjection x).1.2 := by
    rw [← h]
    exact y.2
  simp [diagonalProjection] at hy

private def firstCut (s : Set Interior) : Set (Space × Space) :=
  Prod.fst ⁻¹' (Space.point '' s)
private def secondCut (s : Set Interior) : Set (Space × Space) :=
  Prod.snd ⁻¹' (Space.point '' s)

private theorem direct_preimage_first (s : Set Interior) :
    directMap ⁻¹' firstFiber s = {z | unpoint z.1 ∈ s} := by
  ext z
  change interiorIncl (unpoint z.1) ∈ interiorIncl '' s ↔ unpoint z.1 ∈ s
  exact interiorIncl_mem_image _ _

private theorem delete_preimage_first (s : Set Interior) :
    deleteMap ⁻¹' firstFiber s = {z | unpoint z.1 ∈ s} := by
  ext z
  change interiorIncl (unpoint z.1) ∈ interiorIncl '' s ↔ unpoint z.1 ∈ s
  exact interiorIncl_mem_image _ _

private theorem direct_preimage_second (s : Set Interior) :
    directMap ⁻¹' secondFiber s = {z | unpoint z.2 ∈ s} := by
  ext z
  change interiorIncl (unpoint z.2) ∈ interiorIncl '' s ↔ unpoint z.2 ∈ s
  exact interiorIncl_mem_image _ _

private theorem insert_preimage_second (s : Set Interior) :
    insertMap ⁻¹' secondFiber s = {z | unpoint z.2 ∈ s} := by
  ext z
  change interiorIncl (unpoint z.2) ∈ interiorIncl '' s ↔ unpoint z.2 ∈ s
  exact interiorIncl_mem_image _ _

private theorem direct_first (s : Set Interior) :
    directMap ⁻¹' firstFiber s ∩ directRegion = firstCut s ∩ directRegion := by
  rw [direct_preimage_first]
  ext ⟨x, y⟩
  cases x <;> cases y <;>
    simp [firstCut, directRegion, firstInterior, secondInterior]

private theorem delete_first (s : Set Interior) :
    deleteMap ⁻¹' firstFiber s ∩ deleteRegion = firstCut s \ directRegion := by
  rw [delete_preimage_first]
  ext ⟨x, y⟩
  cases x <;> cases y <;>
    simp [firstCut, deleteRegion, directRegion, firstInterior, secondInterior]

private theorem insert_first (s : Set Interior) : insertMap ⁻¹' firstFiber s = ∅ := by
  ext z
  change diagonalProjection (unpoint z.2) ∈ interiorIncl '' s ↔ False
  exact ⟨fun h => diagonalProjection_not_mem_image _ _ h, False.elim⟩

private theorem direct_second (s : Set Interior) :
    directMap ⁻¹' secondFiber s ∩ directRegion = secondCut s ∩ directRegion := by
  rw [direct_preimage_second]
  ext ⟨x, y⟩
  cases x <;> cases y <;>
    simp [secondCut, directRegion, firstInterior, secondInterior]

private theorem insert_second (s : Set Interior) :
    insertMap ⁻¹' secondFiber s ∩ insertRegion = secondCut s \ directRegion := by
  rw [insert_preimage_second]
  ext ⟨x, y⟩
  cases x <;> cases y <;>
    simp [secondCut, insertRegion, directRegion, firstInterior, secondInterior]

private theorem delete_second (s : Set Interior) : deleteMap ⁻¹' secondFiber s = ∅ := by
  ext z
  change diagonalProjection (unpoint z.1) ∈ interiorIncl '' s ↔ False
  exact ⟨fun h => diagonalProjection_not_mem_image _ _ h, False.elim⟩

private theorem boundaryPlan_first (γ : Measure (Space × Space)) (s : Set Interior)
    (hs : MeasurableSet s) : boundaryPlan γ (firstFiber s) = γ (firstCut s) := by
  rw [boundaryPlan, Measure.add_apply, Measure.add_apply,
    Measure.map_apply measurable_directMap (measurableSet_firstFiber hs),
    Measure.map_apply measurable_deleteMap (measurableSet_firstFiber hs),
    Measure.map_apply measurable_insertMap (measurableSet_firstFiber hs),
    Measure.restrict_apply ((measurableSet_firstFiber hs).preimage measurable_directMap),
    Measure.restrict_apply ((measurableSet_firstFiber hs).preimage measurable_deleteMap),
    insert_first, measure_empty, add_zero, direct_first, delete_first]
  exact measure_inter_add_sdiff _ measurableSet_directRegion

private theorem boundaryPlan_second (γ : Measure (Space × Space)) (s : Set Interior)
    (hs : MeasurableSet s) : boundaryPlan γ (secondFiber s) = γ (secondCut s) := by
  rw [boundaryPlan, Measure.add_apply, Measure.add_apply,
    Measure.map_apply measurable_directMap (measurableSet_secondFiber hs),
    Measure.map_apply measurable_deleteMap (measurableSet_secondFiber hs),
    Measure.map_apply measurable_insertMap (measurableSet_secondFiber hs),
    Measure.restrict_apply ((measurableSet_secondFiber hs).preimage measurable_directMap),
    Measure.restrict_apply ((measurableSet_secondFiber hs).preimage measurable_insertMap),
    delete_second, measure_empty, add_zero, direct_second, insert_second]
  exact measure_inter_add_sdiff _ measurableSet_directRegion

/-- Ordinary reservoir marginal equalities imply the required interior marginal equalities. -/
theorem boundaryPlan_admissible (γ : Measure (Space × Space))
    (μ ν : Measure Interior) (R : ℝ≥0∞)
    (hfirst : γ.map Prod.fst = reservoirMeasure μ R)
    (hsecond : γ.map Prod.snd = reservoirMeasure ν R) :
    IsBoundaryPlan (boundaryPlan γ) μ ν := by
  have hpoint (s : Set Interior) : Space.point ⁻¹' (Space.point '' s) = s := by
    ext x
    simp
  constructor
  · intro s hs
    rw [boundaryPlan_first γ s hs]
    change γ (Prod.fst ⁻¹' (Space.point '' s)) = μ s
    rw [← Measure.map_apply measurable_fst
      (measurableEmbedding_point.measurableSet_image.mpr hs), hfirst,
      reservoirMeasure_apply_interior μ R
        (measurableEmbedding_point.measurableSet_image.mpr hs) (by simp), hpoint]
  · intro s hs
    rw [boundaryPlan_second γ s hs]
    change γ (Prod.snd ⁻¹' (Space.point '' s)) = ν s
    rw [← Measure.map_apply measurable_snd
      (measurableEmbedding_point.measurableSet_image.mpr hs), hsecond,
      reservoirMeasure_apply_interior ν R
        (measurableEmbedding_point.measurableSet_image.mpr hs) (by simp), hpoint]

private theorem directMap_cost (p : ℝ) (z : Space × Space) :
    planPowerCost p (directMap z) = ENNReal.ofReal (dist (unpoint z.1) (unpoint z.2) ^ p) := rfl

private theorem deleteMap_cost (p : ℝ) (z : Space × Space) :
    planPowerCost p (deleteMap z) = ENNReal.ofReal (depth (unpoint z.1) ^ p) := by
  change ENNReal.ofReal (dist (interiorIncl _) (diagonalProjection _) ^ p) = _
  rw [deleteLeg_distance]
  rfl

private theorem insertMap_cost (p : ℝ) (z : Space × Space) :
    planPowerCost p (insertMap z) = ENNReal.ofReal (depth (unpoint z.2) ^ p) := by
  change ENNReal.ofReal (dist (diagonalProjection _) (interiorIncl _) ^ p) = _
  rw [insertLeg_distance]
  rfl

/-- The cost charged by the three restriction/pushforward pieces at each original pair. -/
private def reverseCost (p : ℝ) : Space × Space → ℝ≥0∞ :=
  directRegion.indicator (planPowerCost p ∘ directMap) +
    deleteRegion.indicator (planPowerCost p ∘ deleteMap) +
    insertRegion.indicator (planPowerCost p ∘ insertMap)

private theorem depth_power_sum_le (p : ℝ) (hp : 1 ≤ p) (x y : Interior) :
    ENNReal.ofReal (depth x ^ p) + ENNReal.ofReal (depth y ^ p) ≤
      ENNReal.ofReal ((depth x + depth y) ^ p) := by
  rw [← ENNReal.ofReal_add (Real.rpow_nonneg (depth_nonneg x) p)
    (Real.rpow_nonneg (depth_nonneg y) p)]
  exact ENNReal.ofReal_le_ofReal
    (Real.add_rpow_le_rpow_add (depth_nonneg x) (depth_nonneg y) hp)

private theorem directRegion_points (x y : Interior) :
    (Space.point x, Space.point y) ∈ directRegion ↔ dist x y ≤ depth x + depth y := by
  change ((Space.point x ∈ range Space.point ∧ Space.point y ∈ range Space.point) ∧
    dist x y ≤ depth x + depth y) ↔ _
  simp

private theorem reverseCost_points (p : ℝ) (x y : Interior) :
    reverseCost p (Space.point x, Space.point y) =
      if dist x y ≤ depth x + depth y then ENNReal.ofReal (dist x y ^ p)
      else ENNReal.ofReal (depth x ^ p) + ENNReal.ofReal (depth y ^ p) := by
  by_cases h : dist x y ≤ depth x + depth y
  · have hD := (directRegion_points x y).mpr h
    have hA : (Space.point x, Space.point y) ∉ deleteRegion := by
      exact fun ha => ha.2 hD
    have hB : (Space.point x, Space.point y) ∉ insertRegion := by
      exact fun hb => hb.2 hD
    simp only [reverseCost, Pi.add_apply, Set.indicator_of_mem hD,
      Set.indicator_of_notMem hA, Set.indicator_of_notMem hB, Function.comp_apply,
      directMap_cost, unpoint_point, add_zero, if_pos h]
  · have hD : (Space.point x, Space.point y) ∉ directRegion := by
      exact fun hd => h ((directRegion_points x y).mp hd)
    have hA : (Space.point x, Space.point y) ∈ deleteRegion :=
      ⟨⟨x, rfl⟩, hD⟩
    have hB : (Space.point x, Space.point y) ∈ insertRegion :=
      ⟨⟨y, rfl⟩, hD⟩
    simp only [reverseCost, Pi.add_apply, Set.indicator_of_notMem hD,
      Set.indicator_of_mem hA, Set.indicator_of_mem hB, Function.comp_apply,
      deleteMap_cost, insertMap_cost, unpoint_point, zero_add, if_neg h]

/-- Pointwise comparison includes shortcut pairs, where both boundary legs are charged. -/
private theorem reverseCost_le (p : ℝ) (hp : 1 ≤ p) (z : Space × Space) :
    reverseCost p z ≤ ENNReal.ofReal (dist z.1 z.2 ^ p) := by
  rcases z with ⟨x, y⟩
  cases x with
  | boundary =>
    cases y with
    | boundary =>
      simp [reverseCost, directRegion, deleteRegion, insertRegion, firstInterior,
        secondInterior]
    | point y =>
      simp [reverseCost, directRegion, deleteRegion, insertRegion, firstInterior,
        secondInterior, insertMap_cost]
  | point x =>
    cases y with
    | boundary =>
      simp [reverseCost, directRegion, deleteRegion, insertRegion, firstInterior,
        secondInterior, deleteMap_cost]
    | point y =>
      rw [reverseCost_points]
      change _ ≤ ENNReal.ofReal (dist (Space.point x) (Space.point y) ^ p)
      rw [dist_point_point]
      split_ifs with h
      · rw [min_eq_left h]
      · rw [min_eq_right (lt_of_not_ge h).le]
        exact depth_power_sum_le p hp x y

/-- The concrete reverse plan's cost is the integral of the three explicit charges. -/
private theorem boundaryPlan_cost_eq (p : ℝ) (γ : Measure (Space × Space)) :
    (∫⁻ z, planPowerCost p z ∂boundaryPlan γ) = ∫⁻ z, reverseCost p z ∂γ := by
  rw [boundaryPlan, lintegral_add_measure, lintegral_add_measure,
    lintegral_map (measurable_planPowerCost p) measurable_directMap,
    lintegral_map (measurable_planPowerCost p) measurable_deleteMap,
    lintegral_map (measurable_planPowerCost p) measurable_insertMap]
  rw [← lintegral_indicator measurableSet_directRegion,
    ← lintegral_indicator measurableSet_deleteRegion,
    ← lintegral_indicator measurableSet_insertRegion]
  have hD : Measurable (directRegion.indicator (planPowerCost p ∘ directMap)) :=
    ((measurable_planPowerCost p).comp measurable_directMap).indicator
      measurableSet_directRegion
  have hA : Measurable (deleteRegion.indicator (planPowerCost p ∘ deleteMap)) :=
    ((measurable_planPowerCost p).comp measurable_deleteMap).indicator
      measurableSet_deleteRegion
  simp only [reverseCost, Pi.add_apply]
  rw [lintegral_add_left (show Measurable (fun z =>
    directRegion.indicator (planPowerCost p ∘ directMap) z +
      deleteRegion.indicator (planPowerCost p ∘ deleteMap) z) from hD.add hA),
    lintegral_add_left hD]
  rfl

/-- The reverse plan never increases cost, including competitors whose cost is infinite. -/
theorem boundaryPlan_cost_le (p : ℝ) (hp : 1 ≤ p) (γ : Measure (Space × Space)) :
    (∫⁻ z, planPowerCost p z ∂boundaryPlan γ) ≤
      ∫⁻ z, ENNReal.ofReal (dist z.1 z.2 ^ p) ∂γ := by
  rw [boundaryPlan_cost_eq]
  exact lintegral_mono (reverseCost_le p hp)

/-- Every ordinary reservoir competitor produces an admissible boundary competitor
with no greater cost. No attainment, disintegration, or finite-cost premise is used. -/
theorem exists_boundaryPlan_cost_le (p : ℝ) (hp : 1 ≤ p)
    (γ : Measure (Space × Space)) (μ ν : Measure Interior) (R : ℝ≥0∞)
    (hfirst : γ.map Prod.fst = reservoirMeasure μ R)
    (hsecond : γ.map Prod.snd = reservoirMeasure ν R) :
    ∃ π : Measure PlanSpace, IsBoundaryPlan π μ ν ∧
      (∫⁻ z, planPowerCost p z ∂π) ≤
        ∫⁻ z, ENNReal.ofReal (dist z.1 z.2 ^ p) ∂γ :=
  ⟨boundaryPlan γ, boundaryPlan_admissible γ μ ν R hfirst hsecond,
    boundaryPlan_cost_le p hp γ⟩

/-- Finite original masses force the reverse plan to be finite, without restricting cost. -/
theorem boundaryPlan_finite (γ : Measure (Space × Space))
    (μ ν : Measure Interior) [IsFiniteMeasure μ] [IsFiniteMeasure ν] (R : ℝ≥0∞)
    (hfirst : γ.map Prod.fst = reservoirMeasure μ R)
    (hsecond : γ.map Prod.snd = reservoirMeasure ν R) :
    IsFiniteMeasure (boundaryPlan γ) :=
  boundaryPlan_isFiniteMeasure (boundaryPlan_admissible γ μ ν R hfirst hsecond)

theorem boundaryPlan_zero : boundaryPlan 0 = 0 := by
  simp [boundaryPlan]

theorem boundaryPlan_boundaryAtom :
    boundaryPlan (Measure.dirac (Space.boundary, Space.boundary)) = 0 := by
  classical
  simp [boundaryPlan, restrict_dirac, directRegion, deleteRegion, insertRegion,
    firstInterior, secondInterior]

def farSource : Interior := ⟨(0, 2), by norm_num⟩
def farTarget : Interior := ⟨(10, 12), by norm_num⟩

/-- A distant interior pair is actually split: its squared leg cost is two. -/
theorem far_shortcut_reverse_cost :
    (∫⁻ z, planPowerCost 2 z ∂boundaryPlan
      (Measure.dirac (Space.point farSource, Space.point farTarget))) = 2 := by
  rw [boundaryPlan_cost_eq]
  rw [lintegral_dirac]
  rw [reverseCost_points]
  norm_num [farSource, farTarget, depth_eq, Subtype.dist_eq, Prod.dist_eq, Real.dist_eq]

/-- The same collapsed-space competitor pays four, so this comparison is strict. -/
theorem far_shortcut_original_cost :
    (∫⁻ z : Space × Space, ENNReal.ofReal (dist z.1 z.2 ^ (2 : ℝ))
      ∂Measure.dirac (Space.point farSource, Space.point farTarget)) = 4 := by
  rw [lintegral_dirac]
  change ENNReal.ofReal (dist (Space.point farSource) (Space.point farTarget) ^ (2 : ℝ)) = 4
  rw [show dist (Space.point farSource) (Space.point farTarget) = 2 from far_points_shortcut]
  norm_num

/-- A unit interior pair plus one unit of boundary padding has reservoir capacity two. -/
def singlePairReservoirCompetitor (x y : Interior) : Measure (Space × Space) :=
  Measure.dirac (Space.point x, Space.point y) +
    Measure.dirac (Space.boundary, Space.boundary)

theorem singlePairReservoirCompetitor_first (x y : Interior) :
    (singlePairReservoirCompetitor x y).map Prod.fst =
      reservoirMeasure (Measure.dirac x) 2 := by
  rw [singlePairReservoirCompetitor, Measure.map_add _ _ measurable_fst,
    Measure.map_dirac' measurable_fst, Measure.map_dirac' measurable_fst]
  have hsub : (2 : ℝ≥0∞) - 1 = 1 := by
    exact ENNReal.sub_eq_of_eq_add (b := 1) (by norm_num) (by norm_num)
  simp [reservoirMeasure, Measure.map_dirac' continuous_point.measurable, hsub]

theorem singlePairReservoirCompetitor_second (x y : Interior) :
    (singlePairReservoirCompetitor x y).map Prod.snd =
      reservoirMeasure (Measure.dirac y) 2 := by
  rw [singlePairReservoirCompetitor, Measure.map_add _ _ measurable_snd,
    Measure.map_dirac' measurable_snd, Measure.map_dirac' measurable_snd]
  have hsub : (2 : ℝ≥0∞) - 1 = 1 := by
    exact ENNReal.sub_eq_of_eq_add (b := 1) (by norm_num) (by norm_num)
  simp [reservoirMeasure, Measure.map_dirac' continuous_point.measurable, hsub]

theorem singlePairReservoirCompetitor_admissible (x y : Interior) :
    IsBoundaryPlan (boundaryPlan (singlePairReservoirCompetitor x y))
      (Measure.dirac x) (Measure.dirac y) :=
  boundaryPlan_admissible _ _ _ 2 (singlePairReservoirCompetitor_first x y)
    (singlePairReservoirCompetitor_second x y)

/-- The actual capacity-two reservoir competitor exhibits the strict four-to-two reduction. -/
theorem far_reservoir_cost_reduction :
    (∫⁻ z, planPowerCost 2 z ∂boundaryPlan (singlePairReservoirCompetitor farSource farTarget)) = 2 ∧
    (∫⁻ z : Space × Space, ENNReal.ofReal (dist z.1 z.2 ^ (2 : ℝ))
      ∂singlePairReservoirCompetitor farSource farTarget) = 4 := by
  constructor
  · rw [boundaryPlan_cost_eq, singlePairReservoirCompetitor, lintegral_add_measure,
      ← boundaryPlan_cost_eq, far_shortcut_reverse_cost, lintegral_dirac]
    simp [reverseCost, directRegion, deleteRegion, insertRegion, firstInterior,
      secondInterior]
  · rw [singlePairReservoirCompetitor, lintegral_add_measure,
      far_shortcut_original_cost, lintegral_dirac]
    norm_num


end TDA.Persistence.BoundaryTransport.Reverse
