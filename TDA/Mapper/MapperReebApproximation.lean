import TDA.Mapper.CoverComponentsConstructible
import TDA.Mapper.RetainedCover
import TDA.Mapper.UniformCover
import TDA.Mapper.GraphPLReebQuotient
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Categorical Mapper reconstruction and the Reeb quotient

Finite bounded interval covers yield constructible categorical Mapper assemblies. Applying
the existing reconstruction equivalence gives a finite real graph. Its geometric
interleaving distance from the graph-PL Reeb quotient is bounded by the full cover
resolution. The construction is abstract and noncomputable; it does not assert an executable
component algorithm or identify the ordinary Mapper simple graph with this reconstruction.
-/

open Set CategoryTheory Filter
open scoped NNReal ENNReal Topology

namespace TDA.Mapper

open TDA.Reeb TDA.Reeb.OpenInterval TDA.Reeb.GraphPL TDA.Reeb.GraphRealization

noncomputable section

variable {ι : Type} {X : Type} [TopologicalSpace X]

/-- A chosen colimit model of `P_K C_K`, with its interval maps induced by saturation inclusions.
`categoricalMapperIsColimit` proves the colimit universal property for each value. -/
def categoricalMapperAssembly (f : C(X, ℝ)) (U : ι → OpenInterval) :
    OpenInterval ⥤ Type := coverComponents f U

variable [Finite ι]

/-- The finite constructible assembly supplied to the reconstruction equivalence. -/
def categoricalMapperConstructible (f : C(X, ℝ)) (a b : ι → ℝ)
    (hfinite : ∀ i, Finite ((intervalComponents f).obj (ioo (a i) (b i)))) :
    ConstructibleCosheafCat :=
  ⟨categoricalMapperAssembly f (fun i => ioo (a i) (b i)),
    isConstructibleCosheaf_coverComponents a b f hfinite⟩

/-- `D P_K C_K`, realized as a finite real graph. -/
def categoricalMapperReconstruction (f : C(X, ℝ)) (a b : ι → ℝ)
    (hfinite : ∀ i, Finite ((intervalComponents f).obj (ioo (a i) (b i)))) :
    RGraph.RGraphCat :=
  RGraph.ofCosheafFunctor.obj (categoricalMapperConstructible f a b hfinite)

/-- The reconstruction's interval components are naturally the categorical assembly. -/
def categoricalMapperReconstructionIso (f : C(X, ℝ)) (a b : ι → ℝ)
    (hfinite : ∀ i, Finite ((intervalComponents f).obj (ioo (a i) (b i)))) :
    (RGraph.cosheafFunctor.obj (categoricalMapperReconstruction f a b hfinite)).obj ≅
      categoricalMapperAssembly f (fun i => ioo (a i) (b i)) :=
  (ObjectProperty.ι _).mapIso
    (RGraph.ofCosheafCounitIso.app (categoricalMapperConstructible f a b hfinite))

/-- The full bounded-interval resolution, including a zero value for the empty index type. -/
def coverResolution (a b : ι → ℝ) : ℝ≥0 :=
  letI := Fintype.ofFinite ι
  Finset.univ.sup (fun i => Real.toNNReal (b i - a i))

/-- The distinct attained-range resolution. This clips each interval to the height
range; it is not the resolution in the categorical reconstruction bound. -/
def clippedCoverResolution (f : C(X, ℝ)) (a b : ι → ℝ) : ℝ≥0 :=
  letI := Fintype.ofFinite ι
  Finset.univ.sup (fun i => Real.toNNReal
    (Metric.diam ((ioo (a i) (b i) : Set ℝ) ∩ Set.range f)))

/-- A cover member's full width is bounded by the resolution. -/
theorem width_le_coverResolution (a b : ι → ℝ) (i : ι) :
    b i - a i ≤ (coverResolution a b : ℝ) := by
  let _ := Fintype.ofFinite ι
  exact (Real.le_coe_toNNReal _).trans
    (NNReal.coe_le_coe.mpr (Finset.le_sup (f := fun i => Real.toNNReal (b i - a i))
      (Finset.mem_univ i)))

/-- Full interval widths bound pairwise distances within each cover member. -/
theorem diameter_le_coverResolution (a b : ι → ℝ) (i : ι) (x : ℝ)
    (hx : x ∈ ioo (a i) (b i)) (y : ℝ) (hy : y ∈ ioo (a i) (b i)) :
    |x - y| ≤ (coverResolution a b : ℝ) := by
  apply abs_le.mpr
  have hw := width_le_coverResolution a b i
  constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]


/-- Full interval resolution after removing exactly the members with empty pullback. -/
def retainedCoverResolution (f : C(X, ℝ)) (a b : ι → ℝ) : ℝ≥0 :=
  coverResolution (fun i : RetainedCoverMember f (fun i => ioo (a i) (b i)) => a i.val)
    (fun i => b i.val)

variable {V : Type} [Finite V] (G : SimpleGraph V) (h : V → ℝ)


omit [Finite ι] in
/-- Every categorical Mapper intersection value for finite graph-PL input is genuinely finite.
This uses the interval presentation of the finite intersection, including empty fibers. -/
theorem finite_graphPL_categoricalMapperData (U : ι → OpenInterval) (s : CoverSimplex U) :
    Finite ((categoricalMapperData (plHeight G h) U).obj s) := by
  change Finite ((componentFunctor (plHeight G h)).obj (coverIntersection U s))
  rw [← toOpens_coverIntersectionInterval U s]
  exact finite_zerothHomotopy G h (coverIntersectionInterval U s)

/-- Categorical Mapper reconstruction for finite graph-PL input, with finite fibers. -/
def graphPLMapperReconstruction (a b : ι → ℝ) : RGraph.RGraphCat :=
  categoricalMapperReconstruction (plHeight G h) a b
    (fun i => finite_zerothHomotopy G h (ioo (a i) (b i)))

/-- The geometric reconstruction error equals the assembled component distance.
No coverage assumption is needed for this comparison of the two graph objects. -/
theorem geometricInterleavingDistance_mapperReeb_eq (a b : ι → ℝ) :
    RGraph.geometricInterleavingDistance (graphPLMapperReconstruction G h a b)
      (GraphPL.graphPLReebGraph G h) =
    interleavingDistance (coverComponents (plHeight G h) (fun i => ioo (a i) (b i)))
      (intervalComponents (plHeight G h)) := by
  rw [RGraph.geometricInterleavingDistance_eq_interleavingDistance]
  change interleavingDistance
    (RGraph.cosheafFunctor.obj (categoricalMapperReconstruction (plHeight G h) a b
      (fun i => finite_zerothHomotopy G h (ioo (a i) (b i))))).obj
    (intervalComponents (ReebQuotient.height (plHeight G h))) = _
  exact interleavingDistance_congr
    (categoricalMapperReconstructionIso (plHeight G h) a b
      (fun i => finite_zerothHomotopy G h (ioo (a i) (b i))))
    (asIso (ReebQuotient.intervalComponentComparison (plHeight G h))).symm

/-- The geometric reconstruction error is bounded by the full cover resolution.
Coverage is needed only on the attained height range; horizontal edges, repeated heights and
disconnected graphs are allowed. -/
theorem geometricInterleavingDistance_mapperReeb_le (a b : ι → ℝ)
    (hcov : ∀ x, ∃ i, plHeight G h x ∈ ioo (a i) (b i)) :
    RGraph.geometricInterleavingDistance (graphPLMapperReconstruction G h a b)
      (GraphPL.graphPLReebGraph G h) ≤ (coverResolution a b : ℝ≥0∞) := by
  rw [geometricInterleavingDistance_mapperReeb_eq]
  exact interleavingDistance_coverComponents_le (plHeight G h)
    (fun i => ioo (a i) (b i)) (coverResolution a b) hcov
    (diameter_le_coverResolution a b)

/-- The sharper bound uses only retained members, with each retained interval's full width. -/
theorem geometricInterleavingDistance_mapperReeb_le_retained (a b : ι → ℝ)
    (hcov : ∀ x, ∃ i, plHeight G h x ∈ ioo (a i) (b i)) :
    RGraph.geometricInterleavingDistance (graphPLMapperReconstruction G h a b)
      (GraphPL.graphPLReebGraph G h) ≤
        (retainedCoverResolution (plHeight G h) a b : ℝ≥0∞) := by
  rw [geometricInterleavingDistance_mapperReeb_eq,
    interleavingDistance_congr
      (coverComponentsRetainedIso (plHeight G h) (fun i => ioo (a i) (b i)))
      (Iso.refl _)]
  exact interleavingDistance_coverComponents_le (plHeight G h)
    (retainedCover (plHeight G h) (fun i => ioo (a i) (b i)))
    (retainedCoverResolution (plHeight G h) a b)
    (retainedCover_covers (plHeight G h) (fun i => ioo (a i) (b i)) hcov)
    (diameter_le_coverResolution
      (fun i : RetainedCoverMember (plHeight G h) (fun i => ioo (a i) (b i)) => a i.val)
      (fun i => b i.val))

omit [Finite V] in
/-- Every positive width admits a finite cover with at most that full resolution.
The interval count is allowed to grow as the prescribed width decreases. -/
theorem exists_graphPLMapperCover_resolution_le_of_bounds {m M r : ℝ}
    (hh : ∀ v, h v ∈ Icc m M) (hr : 0 < r) :
    ∃ n : ℕ, ∃ a b : Fin n → ℝ,
      (∀ x, ∃ i, plHeight G h x ∈ ioo (a i) (b i)) ∧
      coverResolution a b ≤ Real.toNNReal r := by
  obtain ⟨n, hn, hM⟩ := exists_uniformCover_window (by linarith : 0 < r / 2)
    (by linarith : r / 2 < r) (m - r) M
  let a : Fin n → ℝ := fun i => m - r + i.val * (r - r / 2)
  let b : Fin n → ℝ := fun i => a i + r
  have hcov : ∀ x, ∃ i, plHeight G h x ∈ ioo (a i) (b i) := by
    intro x
    exact uniformCover_covers_range hh (by linarith : m - r < m) hM
      (by linarith : 0 < r / 2) hn _ ⟨x, rfl⟩
  refine ⟨n, a, b, hcov, ?_⟩
  unfold coverResolution
  exact Finset.sup_le (fun _ _ => by simp [b])

/-- Finite vertex heights supply a bounded interval cover at any positive resolution. -/
theorem exists_graphPLMapperCover_resolution_le {r : ℝ} (hr : 0 < r) :
    ∃ n : ℕ, ∃ a b : Fin n → ℝ,
      (∀ x, ∃ i, plHeight G h x ∈ ioo (a i) (b i)) ∧
      coverResolution a b ≤ Real.toNNReal r := by
  obtain ⟨n, S, hS⟩ := GraphPL.exists_coversVertexHeights h
  apply exists_graphPLMapperCover_resolution_le_of_bounds G h (m := S.value 0)
    (M := S.value (Fin.last n)) _ hr
  intro v
  obtain ⟨i, hi⟩ := hS v
  rw [← hi]
  exact ⟨S.strictMono.monotone (Fin.zero_le i), S.strictMono.monotone (Fin.le_last i)⟩

/-- Any positive error admits a finite bounded cover attaining it. This supplies nontrivial
shrinking families even when the graph-PL height has a nondegenerate attained interval. -/
theorem exists_graphPLMapperReconstruction_error_le_of_bounds {m M r : ℝ}
    (hh : ∀ v, h v ∈ Icc m M) (hr : 0 < r) :
    ∃ n : ℕ, ∃ a b : Fin n → ℝ,
      (∀ x, ∃ i, plHeight G h x ∈ ioo (a i) (b i)) ∧
      RGraph.geometricInterleavingDistance (graphPLMapperReconstruction G h a b)
        (GraphPL.graphPLReebGraph G h) ≤ (Real.toNNReal r : ℝ≥0∞) := by
  obtain ⟨n, a, b, hcov, hres⟩ :=
    exists_graphPLMapperCover_resolution_le_of_bounds G h hh hr
  exact ⟨n, a, b, hcov, (geometricInterleavingDistance_mapperReeb_le G h a b hcov).trans
    (ENNReal.coe_le_coe.mpr hres)⟩

/-- Every finite graph-PL input admits finite categorical Mapper reconstruction at any positive
prescribed geometric error. Finite vertex heights supply the needed range bounds. -/
theorem exists_graphPLMapperReconstruction_error_le {r : ℝ} (hr : 0 < r) :
    ∃ n : ℕ, ∃ a b : Fin n → ℝ,
      (∀ x, ∃ i, plHeight G h x ∈ ioo (a i) (b i)) ∧
      RGraph.geometricInterleavingDistance (graphPLMapperReconstruction G h a b)
        (GraphPL.graphPLReebGraph G h) ≤ (Real.toNNReal r : ℝ≥0∞) := by
  obtain ⟨n, a, b, hcov, hres⟩ := exists_graphPLMapperCover_resolution_le G h hr
  exact ⟨n, a, b, hcov, (geometricInterleavingDistance_mapperReeb_le G h a b hcov).trans
    (ENNReal.coe_le_coe.mpr hres)⟩

/-- Vanishing cover resolution gives convergence in the geometric interleaving distance. -/
theorem tendsto_geometricInterleavingDistance_mapperReeb
    {α : Type*} {l : Filter α} (κ : α → Type) [∀ t, Finite (κ t)]
    (a b : ∀ t, κ t → ℝ)
    (hcov : ∀ t x, ∃ i, plHeight G h x ∈ ioo (a t i) (b t i))
    (hres : Tendsto (fun t => (coverResolution (a t) (b t) : ℝ≥0∞)) l (𝓝 0)) :
    Tendsto (fun t => RGraph.geometricInterleavingDistance
      (graphPLMapperReconstruction G h (a t) (b t)) (GraphPL.graphPLReebGraph G h))
      l (𝓝 0) := by
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hres
    (fun _ => bot_le) (fun t => geometricInterleavingDistance_mapperReeb_le G h
      (a t) (b t) (hcov t))


/-- Vanishing retained full-width resolution suffices for geometric convergence, even when
unretained cover members keep large ambient widths. -/
theorem tendsto_geometricInterleavingDistance_mapperReeb_retained
    {α : Type*} {l : Filter α} (κ : α → Type) [∀ t, Finite (κ t)]
    (a b : ∀ t, κ t → ℝ)
    (hcov : ∀ t x, ∃ i, plHeight G h x ∈ ioo (a t i) (b t i))
    (hres : Tendsto (fun t => (retainedCoverResolution (plHeight G h) (a t) (b t) : ℝ≥0∞))
      l (𝓝 0)) :
    Tendsto (fun t => RGraph.geometricInterleavingDistance
      (graphPLMapperReconstruction G h (a t) (b t)) (GraphPL.graphPLReebGraph G h))
      l (𝓝 0) := by
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hres
    (fun _ => bot_le) (fun t => geometricInterleavingDistance_mapperReeb_le_retained G h
      (a t) (b t) (hcov t))

end

end TDA.Mapper
