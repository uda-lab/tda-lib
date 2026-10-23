import TDA.Persistence.AdditiveFeatures
import TDA.Persistence.DiagramBottleneckLaws
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Geometry of the collapsed diagonal

The strict upper birth–death half-plane is enlarged by one boundary point. Its metric
charges the smaller of the direct maximum-coordinate distance and the path through
the boundary. The topology and Borel structure below are induced by this metric.
-/

noncomputable section

namespace TDA.Persistence.BoundaryTransport

open Set Filter Topology TopologicalSpace

/-- Finite birth–death coordinates strictly above the diagonal. -/
abbrev Interior := {x : ℝ × ℝ // x.1 < x.2}

/-- The upper half-plane with its entire diagonal represented by one point. -/
inductive Space
  | boundary : Space
  | point : Interior → Space

instance : Inhabited Space := ⟨Space.boundary⟩

/-- Distance of an interior point to the diagonal in the maximum norm. -/
def depth (x : Interior) : ℝ := (diagonalCost x.1).toReal

@[simp] theorem depth_eq (x : Interior) : depth x = (x.1.2 - x.1.1) / 2 := by
  simp [depth, diagonalCost_toReal, abs_of_pos (sub_pos.mpr x.2)]

theorem depth_pos (x : Interior) : 0 < depth x := by
  rw [depth_eq]
  exact div_pos (sub_pos.mpr x.2) (by norm_num)

theorem depth_nonneg (x : Interior) : 0 ≤ depth x := (depth_pos x).le

private theorem plane_depth_le_dist_add (x y : ℝ × ℝ) :
    (diagonalCost x).toReal ≤ dist x y + (diagonalCost y).toReal := by
  have h := ENNReal.toReal_mono
    (show finitePairCost x y + diagonalCost y ≠ ⊤ by simp [finitePairCost, diagonalCost])
    (diagonalCost_le_pair_add x y)
  rw [ENNReal.toReal_add (by simp [finitePairCost]) (by simp [diagonalCost])] at h
  simpa only [finitePairCost_toReal, dist_eq_norm] using h

private theorem depth_le_dist_add (x y : Interior) : depth x ≤ dist x y + depth y :=
  plane_depth_le_dist_add x.1 y.1

/-- The collapsed-boundary distance, with no disjoint-sum metric involved. -/
def rho : Space → Space → ℝ
  | .boundary, .boundary => 0
  | .point x, .boundary => depth x
  | .boundary, .point y => depth y
  | .point x, .point y => min (dist x y) (depth x + depth y)

@[simp] theorem rho_boundary_boundary : rho .boundary .boundary = 0 := rfl
@[simp] theorem rho_point_boundary (x : Interior) : rho (.point x) .boundary = depth x := rfl
@[simp] theorem rho_boundary_point (x : Interior) : rho .boundary (.point x) = depth x := rfl
@[simp] theorem rho_point_point (x y : Interior) :
    rho (.point x) (.point y) =
      min (finitePairCost x.1 y.1).toReal (depth x + depth y) := by
  simp [rho, finitePairCost_toReal, Subtype.dist_eq, dist_eq_norm]

private theorem rho_nonneg (x y : Space) : 0 ≤ rho x y := by
  cases x <;> cases y <;> simp only [rho]
  · exact le_rfl
  · exact depth_nonneg _
  · exact depth_nonneg _
  · exact le_min dist_nonneg (add_nonneg (depth_nonneg _) (depth_nonneg _))

@[simp] theorem rho_self (x : Space) : rho x x = 0 := by
  cases x with
  | boundary => rfl
  | point x =>
    change min (dist x x) (depth x + depth x) = 0
    rw [dist_self]
    exact min_eq_left (add_nonneg (depth_nonneg x) (depth_nonneg x))

theorem rho_comm (x y : Space) : rho x y = rho y x := by
  cases x <;> cases y <;> simp [rho, dist_comm, add_comm]

private theorem depth_le_rho_add (x y : Interior) :
    depth x ≤ rho (.point x) (.point y) + depth y := by
  dsimp [rho]
  rw [min_add, le_min_iff]
  exact ⟨depth_le_dist_add x y, by linarith [depth_nonneg y]⟩

/-- The shortcut metric satisfies the sharp triangle inequality. -/
theorem rho_triangle (x y z : Space) : rho x z ≤ rho x y + rho y z := by
  cases x with
  | boundary =>
    cases y with
    | boundary => simp
    | point y =>
      cases z with
      | boundary => simpa using add_nonneg (depth_nonneg y) (depth_nonneg y)
      | point z => simpa [rho_comm, add_comm] using depth_le_rho_add z y
  | point x =>
    cases y with
    | boundary =>
      cases z with
      | boundary => simp
      | point z => exact min_le_right _ _
    | point y =>
      cases z with
      | boundary => exact depth_le_rho_add x y
      | point z =>
        dsimp [rho]
        rcases le_total (dist x y) (depth x + depth y) with hxy | hxy <;>
          rcases le_total (dist y z) (depth y + depth z) with hyz | hyz
        · rw [min_eq_left hxy, min_eq_left hyz]
          exact (min_le_left _ _).trans (dist_triangle x y z)
        · rw [min_eq_left hxy, min_eq_right hyz]
          exact (min_le_right _ _).trans (by linarith [depth_le_dist_add x y])
        · rw [min_eq_right hxy, min_eq_left hyz]
          exact (min_le_right _ _).trans (by linarith [depth_le_dist_add z y, dist_comm z y])
        · rw [min_eq_right hxy, min_eq_right hyz]
          exact (min_le_right _ _).trans (by linarith [depth_nonneg y])

/-- Zero collapsed distance identifies the actual points. -/
theorem rho_eq_zero_iff (x y : Space) : rho x y = 0 ↔ x = y := by
  constructor
  · intro h
    cases x with
    | boundary =>
      cases y with
      | boundary => rfl
      | point y => exact False.elim ((depth_pos y).ne' h)
    | point x =>
      cases y with
      | boundary => exact False.elim ((depth_pos x).ne' h)
      | point y =>
        have hd : dist x y = 0 := by
          rcases min_eq_iff.mp h with h | h
          · exact h.1
          · exact False.elim ((add_pos (depth_pos x) (depth_pos y)).ne' h.1)
        exact congrArg Space.point (dist_eq_zero.mp hd)
  · rintro rfl
    exact rho_self x

instance : MetricSpace Space where
  dist := rho
  dist_self := rho_self
  dist_comm := rho_comm
  dist_triangle := rho_triangle
  eq_of_dist_eq_zero := (rho_eq_zero_iff _ _).mp

@[simp] theorem dist_point_boundary (x : Interior) :
    dist (.point x) (Space.boundary) = depth x := rfl
@[simp] theorem dist_boundary_point (x : Interior) :
    dist Space.boundary (.point x) = depth x := rfl
@[simp] theorem dist_point_point (x y : Interior) :
    dist (Space.point x) (Space.point y) = min (dist x y) (depth x + depth y) := rfl

/-- Inclusion of the interior is distance-nonincreasing. -/
theorem lipschitz_point : LipschitzWith 1 Space.point := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  simp only [NNReal.coe_one, one_mul, dist_point_point]
  exact min_le_left _ _

theorem continuous_point : Continuous Space.point := lipschitz_point.continuous

instance : SeparableSpace Space := by
  apply isSeparable_univ_iff.mp
  have h : (Set.univ : Set Space) = Set.range Space.point ∪ {Space.boundary} := by
    ext x
    cases x <;> simp
  rw [h]
  exact (isSeparable_range continuous_point).union (Set.countable_singleton Space.boundary).isSeparable

/-- A Cauchy sequence for the collapsed metric has a limit, even when its
birth coordinates escape along the diagonal. -/
theorem cauchySeq_exists_tendsto (u : ℕ → Space) (hu : CauchySeq u) :
    ∃ x, Tendsto u atTop (𝓝 x) := by
  let d : ℕ → ℝ := fun n => dist (u n) Space.boundary
  have hd : CauchySeq d := by
    apply Metric.cauchySeq_iff.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hu ε hε
    exact ⟨N, fun m hm n hn =>
      (dist_dist_dist_le_left (u m) (u n) Space.boundary).trans_lt (hN m hm n hn)⟩
  obtain ⟨a, ha⟩ := cauchySeq_tendsto_of_complete hd
  have ha0 : 0 ≤ a := ge_of_tendsto' ha (fun _ => dist_nonneg)
  by_cases haz : a = 0
  · refine ⟨Space.boundary, ?_⟩
    exact tendsto_iff_dist_tendsto_zero.mpr (haz ▸ ha)
  · have hap : 0 < a := lt_of_le_of_ne ha0 (Ne.symm haz)
    have hevent : ∀ᶠ n in atTop, a / 2 < d n :=
      (tendsto_order.mp ha).1 (a / 2) (by linarith)
    obtain ⟨N, hN⟩ := eventually_atTop.mp hevent
    have hpoint (n : ℕ) (hn : N ≤ n) : ∃ x : Interior, u n = Space.point x := by
      cases h : u n with
      | boundary =>
        have := hN n hn
        simp [d, h] at this
        linarith
      | point x => exact ⟨x, rfl⟩
    choose v hv using fun n => hpoint (n + N) (Nat.le_add_left N n)
    have hdepth (n : ℕ) : a / 2 < depth (v n) := by
      simpa [d, hv n] using hN (n + N) (Nat.le_add_left N n)
    have hvC : CauchySeq (fun n => (v n).1) := by
      apply Metric.cauchySeq_iff.mpr
      intro ε hε
      obtain ⟨M, hM⟩ := Metric.cauchySeq_iff.mp hu (min ε (a / 2))
        (lt_min hε (by linarith))
      refine ⟨M, fun m hm n hn => ?_⟩
      have hc := hM (m + N) (hm.trans (Nat.le_add_right m N))
        (n + N) (hn.trans (Nat.le_add_right n N))
      rw [hv m, hv n, dist_point_point] at hc
      rcases min_lt_iff.mp hc with hc | hc
      · exact hc.trans_le (min_le_left _ _)
      · have hh := hc.trans_le (min_le_right _ _)
        linarith [hdepth m, hdepth n]
    obtain ⟨z, hz⟩ := cauchySeq_tendsto_of_complete hvC
    have hpers : a ≤ z.2 - z.1 := by
      have ht : Tendsto (fun n => (v n).1.2 - (v n).1.1) atTop (𝓝 (z.2 - z.1)) :=
        (continuous_snd.tendsto z |>.comp hz).sub (continuous_fst.tendsto z |>.comp hz)
      apply ge_of_tendsto' ht
      intro n
      have hh := hdepth n
      rw [depth_eq] at hh
      linarith
    let z' : Interior := ⟨z, by linarith⟩
    have hvz : Tendsto v atTop (𝓝 z') :=
      tendsto_subtype_rng.mpr hz
    have htail : Tendsto (fun n => u (n + N)) atTop (𝓝 (Space.point z')) := by
      have h := continuous_point.tendsto z' |>.comp hvz
      simpa only [hv, Function.comp_def] using h
    exact ⟨Space.point z', (tendsto_add_atTop_iff_nat N).mp htail⟩

instance : CompleteSpace Space := Metric.complete_of_cauchySeq_tendsto cauchySeq_exists_tendsto

instance : SecondCountableTopology Space :=
  UniformSpace.secondCountable_of_separable Space

instance : PolishSpace Space := inferInstance

/-- The metric on the interior gives exactly its ordinary half-plane topology. -/
theorem isOpenEmbedding_point : IsOpenEmbedding Space.point := by
  apply IsOpenEmbedding.of_continuous_injective_isOpenMap continuous_point (fun _ _ h => Space.point.inj h)
  intro s hs
  apply Metric.isOpen_iff.mpr
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hs x hx
  refine ⟨min ε (depth x), lt_min hε (depth_pos x), ?_⟩
  intro y hy
  have hy' : dist y (Space.point x) < min ε (depth x) := hy
  cases y with
  | boundary =>
    have : depth x < depth x := (lt_min_iff.mp hy').2
    exact (lt_irrefl _ this).elim
  | point y =>
    refine ⟨y, hball ?_, rfl⟩
    have hdirect : dist y x < ε := by
      rcases min_lt_iff.mp hy' with h | h
      · exact h.trans_le (min_le_left _ _)
      · have : depth y + depth x < depth x := h.trans_le (min_le_right _ _)
        linarith [depth_nonneg y]
    exact hdirect

instance : MeasurableSpace Space := borel Space
instance : BorelSpace Space := ⟨rfl⟩

/-- Interior Borel sets remain Borel in the collapsed metric space. -/
theorem measurableEmbedding_point : MeasurableEmbedding Space.point :=
  isOpenEmbedding_point.measurableEmbedding

/-- Borel sets are precisely a Borel interior part and an arbitrary boundary atom. -/
theorem measurableSet_iff_interior (s : Set Space) :
    MeasurableSet s ↔ MeasurableSet (Space.point ⁻¹' s) := by
  classical
  constructor
  · exact fun h => measurableEmbedding_point.measurable h
  · intro h
    have heq : s = Space.point '' (Space.point ⁻¹' s) ∪
        (if Space.boundary ∈ s then {Space.boundary} else ∅) := by
      ext x
      cases x <;> simp
    rw [heq]
    apply (measurableEmbedding_point.measurableSet_image.mpr h).union
    split_ifs <;> simp

/-- The closed upper half-plane, carrying its ordinary maximum-coordinate metric. -/
abbrev ClosedHalfPlane := {x : ℝ × ℝ // x.1 ≤ x.2}

/-- Collapse every point of the diagonal to the one boundary point. -/
def collapse (x : ClosedHalfPlane) : Space :=
  if h : x.1.1 < x.1.2 then Space.point ⟨x.1, h⟩ else Space.boundary

@[simp] theorem collapse_interior (x : Interior) : collapse ⟨x.1, x.2.le⟩ = Space.point x := by
  simp [collapse, x.2]

@[simp] theorem collapse_diagonal (t : ℝ) : collapse ⟨(t, t), le_rfl⟩ = Space.boundary := by
  simp [collapse]

private theorem diagonalCost_eq_zero_of_not_lt (x : ClosedHalfPlane) (h : ¬ x.1.1 < x.1.2) :
    (diagonalCost x.1).toReal = 0 := by
  have heq : x.1.1 = x.1.2 := le_antisymm x.2 (le_of_not_gt h)
  simp [diagonalCost_toReal, heq]

/-- Collapse is distance-nonincreasing for the ordinary maximum norm. -/
theorem lipschitz_collapse : LipschitzWith 1 collapse := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  simp only [NNReal.coe_one, one_mul]
  unfold collapse
  split_ifs with hx hy hy
  · exact min_le_left _ _
  · change (diagonalCost x.1).toReal ≤ dist x.1 y.1
    simpa only [diagonalCost_eq_zero_of_not_lt y hy, add_zero] using
      plane_depth_le_dist_add x.1 y.1
  · change (diagonalCost y.1).toReal ≤ dist x.1 y.1
    simpa only [diagonalCost_eq_zero_of_not_lt x hx, add_zero, dist_comm] using
      plane_depth_le_dist_add y.1 x.1
  · exact dist_nonneg

/-- Every point of the collapsed space comes from the closed upper half-plane. -/
theorem collapse_surjective : Function.Surjective collapse := by
  intro x
  cases x with
  | boundary => exact ⟨⟨(0, 0), le_rfl⟩, collapse_diagonal 0⟩
  | point x => exact ⟨⟨x.1, x.2.le⟩, collapse_interior x⟩

theorem continuous_collapse : Continuous collapse := lipschitz_collapse.continuous

theorem measurable_collapse : Measurable collapse := continuous_collapse.measurable

/-- Distance to the boundary is exactly persistence, without a birth-coordinate moment. -/
theorem dist_collapse_boundary (x : ClosedHalfPlane) :
    dist (collapse x) Space.boundary = (x.1.2 - x.1.1) / 2 := by
  unfold collapse
  split_ifs with h
  · exact depth_eq ⟨x.1, h⟩
  · have heq : x.1.1 = x.1.2 := le_antisymm x.2 (le_of_not_gt h)
    simp [heq]

/-- Direct transport between distant bars can be strictly more expensive than the shortcut. -/
theorem far_points_shortcut :
    dist (Space.point ⟨(0, 2), by norm_num⟩)
      (Space.point ⟨(10, 12), by norm_num⟩) = 2 := by
  rw [dist_point_point]
  norm_num [depth_eq, Subtype.dist_eq, Prod.dist_eq, Real.dist_eq]

/-- Squaring a shortcut length differs from summing the squared boundary legs. -/
theorem far_points_squared_shortcut_and_boundary_legs :
    dist (Space.point ⟨(0, 2), by norm_num⟩)
        (Space.point ⟨(10, 12), by norm_num⟩) ^ 2 = 4 ∧
      depth ⟨(0, 2), by norm_num⟩ ^ 2 + depth ⟨(10, 12), by norm_num⟩ ^ 2 = 2 := by
  constructor
  · rw [far_points_shortcut]
    norm_num
  · norm_num [depth_eq]

/-- The metric has arbitrarily small positive interior distances to its boundary. -/
theorem exists_point_dist_boundary_lt {ε : ℝ} (hε : 0 < ε) :
    ∃ x : Interior, 0 < dist (Space.point x) Space.boundary ∧
      dist (Space.point x) Space.boundary < ε := by
  refine ⟨⟨(0, ε), hε⟩, ?_, ?_⟩
  · exact depth_pos _
  · simp only [dist_point_boundary, depth_eq, sub_zero]
    linarith

/-- Interior points are dense, including at the collapsed boundary. -/
theorem denseRange_point : DenseRange Space.point := by
  apply Metric.denseRange_iff.mpr
  intro x ε hε
  cases x with
  | boundary =>
    obtain ⟨y, _, hy⟩ := exists_point_dist_boundary_lt hε
    exact ⟨y, by simpa only [dist_comm] using hy⟩
  | point x => exact ⟨x, by simpa using hε⟩

end TDA.Persistence.BoundaryTransport
