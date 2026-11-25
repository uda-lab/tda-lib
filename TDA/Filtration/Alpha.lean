import TDA.Filtration.CechRelation
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.HausdorffDistance

set_option autoImplicit false

/-!
# The closed Voronoi alpha filtration

The α complex `complex sites t` is, by definition, the nerve of the closed Voronoi cells of
the sites, each intersected with the closed ball of squared radius `t` about its own site
(for `t ≥ 0`; see `complex_eq_nerve_closedBall`). This is the *nerve form* of the α complex.
Nearest-site ties are retained, so in degenerate configurations the full closed-cell nerve is
used: for cocircular sites, such as the four corners of a square, a common witness at the
circumcenter makes the simplex spanned by all cocircular sites a face once the grade reaches
the squared circumradius, whereas a Delaunay triangulation contains only a triangulated
subcomplex. For sites in general position the two coincide.

Conventions at negative squared grades. The α complex is empty below zero
(`complex_eq_bot_of_neg`). The canonical Čech target for squared-grade comparisons is
`Alpha.squaredCechFiltration` (module `TDA.Filtration.AlphaLabelled`), which is also empty
below zero; the canonical inclusion is `Alpha.filtration_le_squaredCech` and its naturality is
`Alpha.inclusion_natural_squaredCech`. The legacy comparison `filtration_le_cech` reindexes the
radius-indexed Čech filtration by `radius`, which sends every negative grade to radius zero, so
its target at `t < 0` is the radius-zero Čech complex (nonempty on a nonempty label type) and
not the empty complex. The two targets agree at every `t ≥ 0`
(`reindex_radius_cech_eq_squaredCech_of_nonneg`) and differ at every `t < 0` on a nonempty label
type. `filtration_le_cech` and `inclusion_natural` keep their statements and behaviour for the
migration period; new squared-grade results should use the canonical counterparts.

In a finite-dimensional real inner-product space, `filter` assigns each nonempty face of
the full closed-cell nerve `carrier` its least entrance grade; `isLeast_sq_dist` identifies
this grade with the least squared distance from any vertex of the face over the common
closed cells, and `sublevel_eq_complex` identifies the sublevels of `filter` with the
stages `complex sites t`. These results are stated and proved in the library's own terms.
Bauer–Edelsbrunner (arXiv:1312.1231) is background; no numbered result of it is attributed
here. See the source register entry `BE-1312.1231` in `docs/math/references.md`.
-/

namespace TDA.Filtration.Alpha

open TDA.Topology TDA.Simplicial

variable {V E : Type*} [NormedAddCommGroup E] (sites : V ↪ E)

/-- The closed Voronoi domain of each labelled site, including all nearest-site ties. -/
def voronoiFamily : CoverFamily E V :=
  fun v => {x | ∀ w, dist x (sites v) ≤ dist x (sites w)}

/-- The common closed Voronoi domain of a finite set of labels. -/
def commonCells (s : Finset V) : Set E :=
  {x | ∀ v ∈ s, x ∈ voronoiFamily sites v}

/-- Every site in the face is at the same distance from a common Voronoi witness. -/
theorem dist_eq_of_mem_commonCells {s : Finset V} {v w : V} (hv : v ∈ s) (hw : w ∈ s)
    {x : E} (hx : x ∈ commonCells sites s) : dist x (sites v) = dist x (sites w) :=
  le_antisymm (hx v hv w) (hx w hw v)

/-- The nerve of the cells cut off at squared distance `t`. -/
def complex (t : ℝ) : PreAbstractSimplicialComplex V :=
  nerve fun v => voronoiFamily sites v ∩ {x | dist x (sites v) ^ 2 ≤ t}

/-- At nonnegative grades the cutoff is the closed ball of radius `√t`. -/
theorem complex_eq_nerve_closedBall {t : ℝ} (ht : 0 ≤ t) :
    complex sites t = nerve (fun v => voronoiFamily sites v ∩ Metric.closedBall (sites v)
      (Real.sqrt t)) := by
  unfold complex
  congr 1
  funext v
  ext x
  exact and_congr_right fun _ => (Real.le_sqrt dist_nonneg ht).symm

/-- At a common Voronoi witness it suffices to test the squared distance to any face vertex. -/
theorem mem_complex_iff {s : Finset V} {v : V} (hv : v ∈ s) (t : ℝ) :
    s ∈ complex sites t ↔ ∃ x ∈ commonCells sites s, dist x (sites v) ^ 2 ≤ t := by
  constructor
  · rintro ⟨_, x, hx⟩
    exact ⟨x, fun w hw => (hx w hw).1, (hx v hv).2⟩
  · rintro ⟨x, hx, hxt⟩
    refine ⟨⟨v, hv⟩, x, fun w hw => ⟨hx w hw, ?_⟩⟩
    change dist x (sites w) ^ 2 ≤ t
    rwa [dist_eq_of_mem_commonCells sites hw hv hx]

theorem complex_mono : Monotone (complex sites) :=
  fun _ _ h => nerve_mono fun _ _ hx => ⟨hx.1, hx.2.trans h⟩

/-- The closed alpha filtration on squared-radius grades. -/
def complexFiltration : SimplicialFiltration ℝ V :=
  ⟨complex sites, complex_mono sites⟩

theorem complex_eq_bot_of_neg {t : ℝ} (ht : t < 0) : complex sites t = ⊥ := by
  apply le_antisymm _ bot_le
  rintro s ⟨⟨v, hv⟩, x, hx⟩
  exact absurd ((sq_nonneg _).trans (hx v hv).2) ht.not_ge

/-- Each site witnesses its own singleton from grade zero onwards. -/
theorem singleton_mem_complex_iff (v : V) (t : ℝ) :
    ({v} : Finset V) ∈ complex sites t ↔ 0 ≤ t := by
  rw [mem_complex_iff sites (Finset.mem_singleton_self v)]
  constructor
  · rintro ⟨x, _, hx⟩
    exact (sq_nonneg _).trans hx
  · intro ht
    refine ⟨sites v, ?_, by simpa using ht⟩
    intro w hw u
    obtain rfl := Finset.mem_singleton.mp hw
    simp

theorem mem_support_iff (v : V) (t : ℝ) :
    v ∈ support (complexFiltration sites) t ↔ 0 ≤ t :=
  singleton_mem_complex_iff sites v t

/-- Conversion from alpha grades to the ambient Čech radius parameter. -/
noncomputable def radius : ℝ →o ℝ := ⟨Real.sqrt, Real.sqrt_monotone⟩

/-- Forgetting the Voronoi inequalities includes each stage into Čech at radius `√t`.

Legacy statement: the target `reindex radius (Cech.complexFiltration sites)` is the radius-zero
Čech complex at every negative grade. The canonical counterpart with the empty-below-zero
target is `Alpha.filtration_le_squaredCech`; the two targets agree for `0 ≤ t`
(`reindex_radius_cech_eq_squaredCech_of_nonneg`). -/
theorem filtration_le_cech :
    complexFiltration sites ≤ reindex radius (Cech.complexFiltration sites) := by
  intro t
  exact nerve_mono fun _ _ hx => Real.le_sqrt_of_sq_le hx.2

/-- The identity on labels commutes with both filtrations' structure maps.

Legacy statement against the radius-zero-below-zero target; the canonical counterpart is
`Alpha.inclusion_natural_squaredCech`. -/
theorem inclusion_natural {s t : ℝ} (hst : s ≤ t) :
    VertexMap.comp (inclusionVertexMap ((complexFiltration sites).monotone hst))
        (inclusionVertexMap (filtration_le_cech sites t)) =
      VertexMap.comp (inclusionVertexMap (filtration_le_cech sites s))
        (inclusionVertexMap ((reindex radius (Cech.complexFiltration sites)).monotone hst)) :=
  VertexMap.ext fun _ => rfl

/-- All feasible nonempty faces, including those arising from degenerate site configurations. -/
def carrier : PreAbstractSimplicialComplex V := nerve (voronoiFamily sites)

theorem finite_carrier_faces [Finite V] : Finite (TotalFace (carrier sites)) := inferInstance

/-- A nonempty face occurs at some finite squared radius exactly when its cells meet. -/
theorem exists_mem_complex_iff (s : Finset V) :
    (∃ t : ℝ, s ∈ complex sites t) ↔ s ∈ carrier sites := by
  constructor
  · rintro ⟨_, hs, x, hx⟩
    exact ⟨hs, x, fun v hv => (hx v hv).1⟩
  · rintro ⟨⟨v, hv⟩, x, hx⟩
    exact ⟨_, (mem_complex_iff sites hv _).2 ⟨x, hx, le_rfl⟩⟩

private theorem isClosed_commonCells (s : Finset V) : IsClosed (commonCells sites s) := by
  simp only [commonCells, voronoiFamily, Set.ofPred_forall]
  exact isClosed_iInter fun v => isClosed_iInter fun _ => isClosed_iInter fun w =>
    isClosed_le (continuous_id.dist continuous_const) (continuous_id.dist continuous_const)

variable [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

private theorem exists_min_dist (s : TotalFace (carrier sites)) (v : V) :
    ∃ y ∈ commonCells sites s.val, ∀ x ∈ commonCells sites s.val,
      dist y (sites v) ≤ dist x (sites v) := by
  obtain ⟨_, x₀, hx₀⟩ := (mem_nerve_iff _ _).1 s.property
  obtain ⟨y, hy, hdist⟩ :=
    (isClosed_commonCells sites _).exists_infDist_eq_dist ⟨x₀, hx₀⟩ (sites v)
  refine ⟨y, hy, fun x hx => ?_⟩
  rw [dist_comm y, ← hdist, dist_comm x]
  exact Metric.infDist_le_dist_of_mem hx

private theorem exists_least_grade (s : TotalFace (carrier sites)) :
    ∃ a, IsLeast {t : ℝ | s.val ∈ complex sites t} a := by
  obtain ⟨v, hv⟩ := ((mem_nerve_iff _ _).1 s.property).1
  obtain ⟨y, hy, hmin⟩ := exists_min_dist sites s v
  refine ⟨dist y (sites v) ^ 2, (mem_complex_iff sites hv _).2 ⟨y, hy, le_rfl⟩, ?_⟩
  intro t ht
  obtain ⟨x, hx, hxt⟩ := (mem_complex_iff sites hv t).1 ht
  exact ((sq_le_sq₀ dist_nonneg dist_nonneg).2 (hmin x hx)).trans hxt

/-- The squared-radius function on feasible faces. Its value is the least occupied grade. -/
noncomputable def filter : FilterFunction (carrier sites) ℝ where
  value s := (exists_least_grade sites s).choose
  mono := by
    intro τ σ h
    apply (exists_least_grade sites τ).choose_spec.2
    exact ((complex sites _).isRelLowerSet_faces (exists_least_grade sites σ).choose_spec.1).2 h
      (((mem_nerve_iff _ _).1 τ.property).1)

theorem isLeast_grade (s : TotalFace (carrier sites)) :
    IsLeast {t : ℝ | s.val ∈ complex sites t} ((filter sites).value s) :=
  (exists_least_grade sites s).choose_spec

/-- For every choice of face vertex, the same value is attained on the common closed cells
and bounds all squared distances there from below. -/
theorem isLeast_sq_dist (s : TotalFace (carrier sites)) {v : V} (hv : v ∈ s.val) :
    IsLeast ((fun x => dist x (sites v) ^ 2) '' commonCells sites s.val)
      ((filter sites).value s) := by
  have hleast := isLeast_grade sites s
  have lower (x : E) (hx : x ∈ commonCells sites s.val) :
      (filter sites).value s ≤ dist x (sites v) ^ 2 :=
    hleast.2 ((mem_complex_iff sites hv _).2 ⟨x, hx, le_rfl⟩)
  obtain ⟨y, hy, hyt⟩ := (mem_complex_iff sites hv _).1 hleast.1
  refine ⟨⟨y, hy, le_antisymm hyt (lower y hy)⟩, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  exact lower x hx

/-- At every squared grade `t`, the sublevel of the squared-radius filter is exactly the closed
alpha complex. -/
theorem sublevel_eq_complex (t : ℝ) : (filter sites).sublevel t = complex sites t := by
  apply le_antisymm
  · intro s hs
    obtain ⟨hsc, hst⟩ := (FilterFunction.mem_sublevel_iff _ _ _).1 hs
    exact complex_mono sites hst (isLeast_grade sites ⟨s, hsc⟩).1
  · intro s hs
    have hsc := (exists_mem_complex_iff sites s).1 ⟨t, hs⟩
    exact (FilterFunction.mem_sublevel_iff _ _ _).2 ⟨hsc, (isLeast_grade sites ⟨s, hsc⟩).2 hs⟩

/-- The sublevels identify the two filtrations on the same labels and grades. -/
theorem sublevelFiltration_eq : (filter sites).sublevelFiltration = complexFiltration sites :=
  OrderHom.ext _ _ (funext (sublevel_eq_complex sites))

/-- For finitely many labels, a single finite threshold suffices for all feasible faces. -/
theorem eventually_eq_carrier [Finite V] :
    ∃ a : ℝ, ∀ t ≥ a, complex sites t = carrier sites := by
  obtain ⟨a, ha⟩ := (Set.finite_range (filter sites).value).bddAbove
  refine ⟨a, fun t ht => ?_⟩
  rw [← sublevel_eq_complex]
  exact (filter sites).sublevel_eq_self_of_forall_le t fun s =>
    (ha (Set.mem_range_self s)).trans ht

end TDA.Filtration.Alpha
