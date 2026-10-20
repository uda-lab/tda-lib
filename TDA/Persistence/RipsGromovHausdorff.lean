import TDA.Persistence.RipsRelationInterleaving
import TDA.Persistence.DiagramBottleneckLaws
import Mathlib.Topology.MetricSpace.GromovHausdorff

/-!
# Gromov–Hausdorff stability of finite Rips persistence

Finite nonempty metric spaces have full actual Rips diagrams at bottleneck distance
at most twice their Gromov–Hausdorff distance. Rips time is diameter, not ball radius.
The proof uses a closed Hausdorff correspondence in mathlib's optimal coupling and
the existing canonical relation interleaving. Compactness of the two finite images
supplies nearest points; compactness or properness of the ambient space is unnecessary.

The order-free entry point `diagram` uses finite labels in the coefficient field's
universe. Its comparison with `dgm` makes the auxiliary enumeration irrelevant.
Infinite-space diagram existence and q-tameness are not asserted here.
-/

universe u v w z

namespace TDA.Persistence.Rips

open TDA.Filtration Set Metric GromovHausdorff
open scoped ENNReal NNReal Topology

noncomputable section

/-- Isometric compact nonempty images give a total correspondence of distortion at
most twice their ambient Hausdorff distance. The witness uses the closed distance bound. -/
theorem exists_relation_distortion_le_hausdorffDist
    {X : Type u} {Y : Type v} {Z : Type w}
    [MetricSpace X] [CompactSpace X] [Nonempty X]
    [MetricSpace Y] [CompactSpace Y] [Nonempty Y] [MetricSpace Z]
    {f : X → Z} {g : Y → Z} (hf : Isometry f) (hg : Isometry g) :
    ∃ C : SetRel X Y,
      Relator.LeftTotal (fun x y => (x, y) ∈ C) ∧
      Relator.LeftTotal (fun y x => (y, x) ∈ C.inv) ∧
      ∀ x x' y y', (x, y) ∈ C → (x', y') ∈ C →
        |dist x x' - dist y y'| ≤ 2 * hausdorffDist (range f) (range g) := by
  let r := hausdorffDist (range f) (range g)
  let C : SetRel X Y := {p | dist (f p.1) (g p.2) ≤ r}
  have hfin : hausdorffEDist (range f) (range g) ≠ ⊤ :=
    hausdorffEDist_ne_top_of_nonempty_of_bounded (range_nonempty _) (range_nonempty _)
      (isCompact_range hf.continuous).isBounded (isCompact_range hg.continuous).isBounded
  refine ⟨C, ?_, ?_, ?_⟩
  · intro x
    obtain ⟨_, ⟨y, rfl⟩, hy⟩ :=
      (isCompact_range hg.continuous).exists_infDist_eq_dist (range_nonempty g) (f x)
    refine ⟨y, ?_⟩
    change dist (f x) (g y) ≤ r
    rw [← hy]
    exact infDist_le_hausdorffDist_of_mem (mem_range_self x) hfin
  · intro y
    obtain ⟨_, ⟨x, rfl⟩, hx⟩ :=
      (isCompact_range hf.continuous).exists_infDist_eq_dist (range_nonempty f) (g y)
    refine ⟨x, ?_⟩
    change dist (f x) (g y) ≤ r
    rw [dist_comm, ← hx]
    dsimp only [r]
    rw [hausdorffDist_comm]
    exact infDist_le_hausdorffDist_of_mem (mem_range_self y)
      (by simpa only [hausdorffEDist_comm] using hfin)
  · intro x x' y y' hxy hx'y'
    change dist (f x) (g y) ≤ r at hxy
    change dist (f x') (g y') ≤ r at hx'y'
    rw [← hf.dist_eq, ← hg.dist_eq]
    apply abs_sub_le_iff.mpr
    constructor
    · have h₁ := dist_triangle (f x) (g y) (f x')
      have h₂ := dist_triangle (g y) (g y') (f x')
      rw [dist_comm (g y') (f x')] at h₂
      linarith
    · have h₁ := dist_triangle (g y) (f x) (g y')
      have h₂ := dist_triangle (f x) (f x') (g y')
      rw [dist_comm (g y) (f x)] at h₁
      linarith

section Ordered

variable {X Y : Type u} [LinearOrder X] [LinearOrder Y]
  [Fintype X] [Fintype Y] [MetricSpace X] [MetricSpace Y]
  [Nonempty X] [Nonempty Y]

/-- Ambient Hausdorff sampling controls the full actual diagrams in every degree.
The finite images, rather than the ambient space, supply compactness. -/
theorem bottleneck_dgm_le_two_mul_hausdorffDist (k : Type u) [Field k]
    {Z : Type w} [MetricSpace Z] {f : X → Z} {g : Y → Z}
    (hf : Isometry f) (hg : Isometry g) (n : ℕ) :
    bottleneck (dgm k (Rips.filter (inferInstance : MetricSpace X)) n)
      (dgm k (Rips.filter (inferInstance : MetricSpace Y)) n) ≤
      ENNReal.ofReal (2 * hausdorffDist (range f) (range g)) := by
  obtain ⟨C, hC, hI, hdist⟩ := exists_relation_distortion_le_hausdorffDist hf hg
  let ε : ℝ≥0 := ⟨2 * hausdorffDist (range f) (range g),
    mul_nonneg (by norm_num) hausdorffDist_nonneg⟩
  calc
    _ ≤ (ε : ℝ≥0∞) := bottleneck_dgm_le_of_relation (C := C) (ε := ε)
      inferInstance inferInstance hC hI hdist k n
    _ = _ := ENNReal.coe_nnreal_eq ε

/-- Finite Gromov–Hausdorff stability with diameter time and the standard factor two. -/
theorem bottleneck_dgm_le_two_mul_ghDist (k : Type u) [Field k] (n : ℕ) :
    bottleneck (dgm k (Rips.filter (inferInstance : MetricSpace X)) n)
      (dgm k (Rips.filter (inferInstance : MetricSpace Y)) n) ≤
      ENNReal.ofReal (2 * ghDist X Y) := by
  simpa only [hausdorffDist_optimal] using
    bottleneck_dgm_le_two_mul_hausdorffDist k
      (isometry_optimalGHInjl X Y) (isometry_optimalGHInjr X Y) n

omit [Nonempty X] [Nonempty Y] in
/-- Isometric relabelling preserves the actual full diagram; it need not preserve
vertex order. This also compares different auxiliary linear orders. -/
theorem dgm_eq_of_isometryEquiv (k : Type u) [Field k] (e : X ≃ᵢ Y) (n : ℕ) :
    dgm k (Rips.filter (inferInstance : MetricSpace X)) n =
      dgm k (Rips.filter (inferInstance : MetricSpace Y)) n := by
  apply (bottleneck_eq_zero_iff _ _).mp
  apply le_antisymm _ zero_le
  have h := bottleneck_dgm_le_of_relation (C := Function.graph e) (ε := 0)
    (inferInstance : MetricSpace X) (inferInstance : MetricSpace Y)
    (fun x => ⟨e x, rfl⟩)
    (fun y => ⟨e.symm y, e.apply_symm_apply y⟩)
    (by
      rintro x x' y y' rfl rfl
      simp only [e.dist_eq, sub_self, abs_zero, NNReal.coe_zero, le_refl]) k n
  simpa only [ENNReal.coe_zero] using h

end Ordered

/-- A finite metric space can be labelled in any coefficient universe. -/
private abbrev FiniteLabels (X : Type u) [Fintype X] := ULift.{v} (Fin (Fintype.card X))

/-- The auxiliary enumeration; all public diagram statements are independent of it. -/
private def labelsEquiv (X : Type u) [Fintype X] : FiniteLabels.{u, v} X ≃ X :=
  Equiv.ulift.trans (Fintype.equivFin X).symm

/-- Transport the metric to the finite labels, without a global metric instance. -/
private abbrev labelsMetric {X : Type u} [Fintype X] (dX : MetricSpace X) :
    MetricSpace (FiniteLabels.{u, v} X) :=
  @MetricSpace.induced _ X (labelsEquiv X) (labelsEquiv X).injective dX

/-- The enumeration is an actual isometric equivalence. -/
private def labelsIsometryEquiv (X : Type u) [Fintype X] [MetricSpace X] :
    letI : MetricSpace (FiniteLabels.{u, v} X) := labelsMetric (inferInstance : MetricSpace X)
    FiniteLabels.{u, v} X ≃ᵢ X := by
  letI : MetricSpace (FiniteLabels.{u, v} X) := labelsMetric (inferInstance : MetricSpace X)
  exact { labelsEquiv X with
    isometry_toFun := MetricSpace.isometry_induced _ (labelsEquiv X).injective }

/-- The full actual Rips diagram of a finite metric space over any field, with no
vertex order required. It is the existing actual diagram on isometric finite labels. -/
def diagram (k : Type v) [Field k] (X : Type u) [Fintype X] [MetricSpace X] (n : ℕ) :
    Diagram ℝ :=
  dgm k (Rips.filter (labelsMetric (inferInstance : MetricSpace X) :
    MetricSpace (FiniteLabels.{u, v} X))) n

/-- The order-free actual diagram has strictly positive lifetimes, including its
possible essential occurrences. -/
theorem diagram_isPositive (k : Type v) [Field k] (X : Type u)
    [Fintype X] [MetricSpace X] (n : ℕ) : (diagram k X n).IsPositive :=
  dgm_isPositive k (Rips.filter (labelsMetric (inferInstance : MetricSpace X) :
    MetricSpace (FiniteLabels.{u, v} X))) n

/-- The order-free finite-space entry point agrees with the existing actual diagram
for every auxiliary vertex order, including orders unrelated to the enumeration. -/
theorem diagram_eq_dgm (k : Type u) [Field k] (X : Type u) [Fintype X]
    [MetricSpace X] [LinearOrder X] (n : ℕ) :
    diagram k X n = dgm k (Rips.filter (inferInstance : MetricSpace X)) n := by
  let : MetricSpace (FiniteLabels.{u, u} X) := labelsMetric (inferInstance : MetricSpace X)
  exact dgm_eq_of_isometryEquiv k (labelsIsometryEquiv X) n

/-- Ambient Hausdorff sampling, for arbitrary finite nonempty metric spaces and
arbitrary coefficient fields, independently of all auxiliary vertex enumerations. -/
theorem bottleneck_diagram_le_two_mul_hausdorffDist (k : Type z) [Field k]
    {X : Type u} {Y : Type v} {Z : Type w}
    [Fintype X] [Fintype Y] [MetricSpace X] [MetricSpace Y]
    [Nonempty X] [Nonempty Y] [MetricSpace Z]
    {f : X → Z} {g : Y → Z} (hf : Isometry f) (hg : Isometry g) (n : ℕ) :
    bottleneck (diagram k X n) (diagram k Y n) ≤
      ENNReal.ofReal (2 * hausdorffDist (range f) (range g)) := by
  let : MetricSpace (FiniteLabels.{u, z} X) := labelsMetric (inferInstance : MetricSpace X)
  let : MetricSpace (FiniteLabels.{v, z} Y) := labelsMetric (inferInstance : MetricSpace Y)
  let : Nonempty (FiniteLabels.{u, z} X) := (labelsEquiv X).nonempty
  let : Nonempty (FiniteLabels.{v, z} Y) := (labelsEquiv Y).nonempty
  have h := bottleneck_dgm_le_two_mul_hausdorffDist k
    (hf.comp (labelsIsometryEquiv X).isometry)
    (hg.comp (labelsIsometryEquiv Y).isometry) n
  simpa only [diagram, range_comp, IsometryEquiv.range_eq_univ, image_univ] using h

/-- The finite GH–Rips endpoint on arbitrary finite nonempty metric spaces.
The coefficient field may have a different universe from both vertex types. -/
theorem bottleneck_diagram_le_two_mul_ghDist (k : Type z) [Field k]
    (X : Type u) (Y : Type v) [Fintype X] [Fintype Y]
    [MetricSpace X] [MetricSpace Y] [Nonempty X] [Nonempty Y] (n : ℕ) :
    bottleneck (diagram k X n) (diagram k Y n) ≤ ENNReal.ofReal (2 * ghDist X Y) := by
  simpa only [hausdorffDist_optimal] using
    bottleneck_diagram_le_two_mul_hausdorffDist k
      (isometry_optimalGHInjl X Y) (isometry_optimalGHInjr X Y) n

/-- Order-free diagrams identify isometric finite spaces, without requiring an
order-preserving map or a common vertex/field universe. Empty spaces are allowed. -/
theorem diagram_eq_of_isometryEquiv (k : Type z) [Field k]
    {X : Type u} {Y : Type v} [Fintype X] [Fintype Y]
    [MetricSpace X] [MetricSpace Y]
    (e : X ≃ᵢ Y) (n : ℕ) : diagram k X n = diagram k Y n := by
  let : MetricSpace (FiniteLabels.{u, z} X) := labelsMetric (inferInstance : MetricSpace X)
  let : MetricSpace (FiniteLabels.{v, z} Y) := labelsMetric (inferInstance : MetricSpace Y)
  exact dgm_eq_of_isometryEquiv k
    (((labelsIsometryEquiv X).trans e).trans (labelsIsometryEquiv Y).symm) n

/-- A supplied sampling-error bound gives the diameter-scale factor two. -/
theorem bottleneck_diagram_le_two_mul_of_hausdorffDist_le (k : Type z) [Field k]
    {X : Type u} {Y : Type v} {Z : Type w}
    [Fintype X] [Fintype Y] [MetricSpace X] [MetricSpace Y]
    [Nonempty X] [Nonempty Y] [MetricSpace Z]
    {f : X → Z} {g : Y → Z} (hf : Isometry f) (hg : Isometry g)
    {r : ℝ} (hr : hausdorffDist (range f) (range g) ≤ r) (n : ℕ) :
    bottleneck (diagram k X n) (diagram k Y n) ≤ ENNReal.ofReal (2 * r) :=
  (bottleneck_diagram_le_two_mul_hausdorffDist k hf hg n).trans
    (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hr (by norm_num)))

/-- Two finite samples of a common possibly infinite target have close diagrams.
Extended Hausdorff errors keep unbounded or empty-target degeneracies explicit;
no diagram of the target is assumed or constructed. -/
theorem bottleneck_diagram_le_two_mul_sampling_errors (k : Type z) [Field k]
    {X : Type u} {Y : Type v} {Z : Type w}
    [Fintype X] [Fintype Y] [MetricSpace X] [MetricSpace Y]
    [Nonempty X] [Nonempty Y] [MetricSpace Z]
    {f : X → Z} {g : Y → Z} (hf : Isometry f) (hg : Isometry g)
    (S : Set Z) {ε δ : ℝ} (hε : 0 ≤ ε) (hδ : 0 ≤ δ)
    (hX : hausdorffEDist (range f) S ≤ ENNReal.ofReal ε)
    (hY : hausdorffEDist (range g) S ≤ ENNReal.ofReal δ) (n : ℕ) :
    bottleneck (diagram k X n) (diagram k Y n) ≤ ENNReal.ofReal (2 * (ε + δ)) := by
  apply bottleneck_diagram_le_two_mul_of_hausdorffDist_le k hf hg _ n
  apply ENNReal.toReal_le_of_le_ofReal (add_nonneg hε hδ)
  have h : hausdorffEDist (range f) (range g) ≤
      ENNReal.ofReal ε + ENNReal.ofReal δ :=
    hausdorffEDist_triangle.trans (add_le_add hX (by
      simpa only [hausdorffEDist_comm] using hY))
  simpa only [ENNReal.ofReal_add hε hδ] using h

/-- Finite samples converging in ambient Hausdorff distance to a fixed finite
nonempty space have full actual diagrams converging in bottleneck distance.
The sample carrier, cardinality and label universe may vary with the index. -/
theorem tendsto_bottleneck_diagram_of_hausdorffDist_tendsto_zero
    (k : Type z) [Field k] {ι : Type*} {l : Filter ι}
    (X : ι → Type u) (Y : Type v) {Z : Type w}
    [∀ i, Fintype (X i)] [Fintype Y] [∀ i, MetricSpace (X i)] [MetricSpace Y]
    [∀ i, Nonempty (X i)] [Nonempty Y] [MetricSpace Z]
    {f : ∀ i, X i → Z} {g : Y → Z}
    (hf : ∀ i, Isometry (f i)) (hg : Isometry g)
    (h : Filter.Tendsto (fun i => hausdorffDist (range (f i)) (range g)) l (𝓝 0))
    (n : ℕ) :
    Filter.Tendsto (fun i => bottleneck (diagram k (X i) n) (diagram k Y n)) l (𝓝 0) := by
  have hlim : Filter.Tendsto
      (fun i => ENNReal.ofReal (2 * hausdorffDist (range (f i)) (range g))) l (𝓝 0) := by
    simpa only [mul_zero, ENNReal.ofReal_zero] using
      ENNReal.tendsto_ofReal (h.const_mul 2)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ => bot_le) (fun i => bottleneck_diagram_le_two_mul_hausdorffDist k (hf i) hg n)

end
end TDA.Persistence.Rips
