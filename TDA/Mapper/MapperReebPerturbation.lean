import TDA.Mapper.MapperReebApproximation
import TDA.Mapper.GraphPLReebExtremal
import TDA.Reeb.PerturbationDistance
import TDA.Reeb.Stability

/-!
# Two inputs: Mapper reconstructions of perturbed heights

The categorical Mapper approximation compares the reconstruction of one height with its Reeb
quotient. This module compares reconstructions of two heights, each with its own finite
bounded-interval cover.

For continuous `f g : C(X, ℝ)` with `|f x - g x| ≤ ε` and covers `U`, `U'` of the attained
ranges whose members have diameters at most `r`, `r'`, the assembled precosheaves are at
interleaving distance at most `r + ε + r'`
(`interleavingDistance_coverComponents_le_add`), and at most `r + edist f g + r'` for the
uniform extended distance (`interleavingDistance_coverComponents_le_add_edist`).

For vertex heights `h g` on one finite graph `G`, with `res`, `res'` the cover resolutions,
write `M_h`, `M_g` for the reconstructions `graphPLMapperReconstruction G h a b`,
`graphPLMapperReconstruction G g a' b'` and `ℛ(h)`, `ℛ(g)` for the Reeb quotients.

* Upper bound (`geometricInterleavingDistance_mapperReeb_le_add_edist`):
  `d_geo(M_h, M_g) ≤ res + edist h g + res'`, with budget, retained-resolution and
  same-cover forms.
* Sandwich (`geometricInterleavingDistance_graphPLReebGraph_le_mapperReeb_add`,
  `geometricInterleavingDistance_mapperReeb_le_graphPLReebGraph_add`): `d_geo(M_h, M_g)` and
  `d_geo(ℛ(h), ℛ(g))` differ by at most `res + res'`; for nonempty `V` this gives the lower
  bounds `ofReal |sup' h - sup' g| ≤ d_geo(M_h, M_g) + res + res'`
  (`ofReal_abs_sup'_sub_le_geometricInterleavingDistance_mapperReeb_add`) and the `inf'` form.
* Convergence (`tendsto_geometricInterleavingDistance_mapperReeb_pair`): along covers whose
  resolutions tend to `0`, `d_geo(M_h^t, M_g^t)` tends to `d_geo(ℛ(h), ℛ(g))`.
* Existence (`exists_graphPLMapperReconstruction_pair_le`): for every `r > 0` there are finite
  covers with `d_geo(M_h, M_g) ≤ edist h g + 2 r`.

Every cover must cover the attained range of its own height. None of the bounds is claimed to
be sharp; no comparison across different graphs is made. The two-input bounds compose the
one-input approximation with the triangle inequality and attribute nothing new to the sources.
-/

open Set CategoryTheory Filter
open scoped NNReal ENNReal Topology

namespace TDA.Mapper

open TDA.Reeb TDA.Reeb.OpenInterval TDA.Reeb.GraphPL TDA.Mapper.GraphPL

noncomputable section

section Cosheaf

variable {ι ι' : Type} {X : Type} [TopologicalSpace X]

private theorem interleavingDistance_coverComponents_le_add_of_le
    {f g : C(X, ℝ)} {U : ι → OpenInterval} {U' : ι' → OpenInterval} {r r' : ℝ≥0} {D : ℝ≥0∞}
    (hcovf : ∀ x, ∃ i, f x ∈ U i) (hdiam : ∀ i x, x ∈ U i → ∀ y, y ∈ U i → |x - y| ≤ r)
    (hcovg : ∀ x, ∃ i, g x ∈ U' i) (hdiam' : ∀ i x, x ∈ U' i → ∀ y, y ∈ U' i → |x - y| ≤ r')
    (hD : interleavingDistance (intervalComponents f) (intervalComponents g) ≤ D) :
    interleavingDistance (coverComponents f U) (coverComponents g U') ≤ r + D + r' := by
  have h1 := interleavingDistance_coverComponents_le f U r hcovf hdiam
  have h3 := interleavingDistance_coverComponents_le g U' r' hcovg hdiam'
  rw [interleavingDistance_comm] at h3
  calc _ ≤ interleavingDistance (coverComponents f U) (intervalComponents f) +
        interleavingDistance (intervalComponents f) (coverComponents g U') :=
        interleavingDistance_triangle _ _ _
    _ ≤ interleavingDistance (coverComponents f U) (intervalComponents f) +
        (interleavingDistance (intervalComponents f) (intervalComponents g) +
          interleavingDistance (intervalComponents g) (coverComponents g U')) :=
        add_le_add_right (interleavingDistance_triangle _ _ _) _
    _ ≤ r + (D + r') := add_le_add h1 (add_le_add hD h3)
    _ = r + D + r' := (add_assoc _ _ _).symm

/-- Assembled precosheaves of two uniformly close heights, over covers of their attained
ranges with member diameters at most `r` and `r'`, are at interleaving distance at most
`r + ε + r'`. -/
theorem interleavingDistance_coverComponents_le_add {f g : C(X, ℝ)} {ε : ℝ≥0}
    (hfg : ∀ x, |f x - g x| ≤ ε) {U : ι → OpenInterval} {U' : ι' → OpenInterval} {r r' : ℝ≥0}
    (hcovf : ∀ x, ∃ i, f x ∈ U i) (hdiam : ∀ i x, x ∈ U i → ∀ y, y ∈ U i → |x - y| ≤ r)
    (hcovg : ∀ x, ∃ i, g x ∈ U' i) (hdiam' : ∀ i x, x ∈ U' i → ∀ y, y ∈ U' i → |x - y| ≤ r') :
    interleavingDistance (coverComponents f U) (coverComponents g U') ≤ r + ε + r' :=
  interleavingDistance_coverComponents_le_add_of_le hcovf hdiam hcovg hdiam'
    (interleavingDistance_intervalComponents_le hfg)

/-- The same bound with the uniform extended distance of `f` and `g`. -/
theorem interleavingDistance_coverComponents_le_add_edist {f g : C(X, ℝ)}
    {U : ι → OpenInterval} {U' : ι' → OpenInterval} {r r' : ℝ≥0}
    (hcovf : ∀ x, ∃ i, f x ∈ U i) (hdiam : ∀ i x, x ∈ U i → ∀ y, y ∈ U i → |x - y| ≤ r)
    (hcovg : ∀ x, ∃ i, g x ∈ U' i) (hdiam' : ∀ i x, x ∈ U' i → ∀ y, y ∈ U' i → |x - y| ≤ r') :
    interleavingDistance (coverComponents f U) (coverComponents g U') ≤
      r + edist (UniformFun.ofFun (⇑f)) (UniformFun.ofFun (⇑g)) + r' :=
  interleavingDistance_coverComponents_le_add_of_le hcovf hdiam hcovg hdiam'
    (interleavingDistance_intervalComponents_le_edist f g)

/-- With one cover for both heights the bound is `2 r + ε`. -/
theorem interleavingDistance_coverComponents_le_two_mul_add {f g : C(X, ℝ)} {ε : ℝ≥0}
    (hfg : ∀ x, |f x - g x| ≤ ε) {U : ι → OpenInterval} {r : ℝ≥0}
    (hcovf : ∀ x, ∃ i, f x ∈ U i) (hcovg : ∀ x, ∃ i, g x ∈ U i)
    (hdiam : ∀ i x, x ∈ U i → ∀ y, y ∈ U i → |x - y| ≤ r) :
    interleavingDistance (coverComponents f U) (coverComponents g U) ≤ 2 * r + ε :=
  (interleavingDistance_coverComponents_le_add hfg hcovf hdiam hcovg hdiam).trans_eq
    (by ring)

end Cosheaf

section Graph

variable {ι ι' : Type} [Finite ι] [Finite ι'] {V : Type} [Finite V] (G : SimpleGraph V)
  (h g : V → ℝ)

/-- The geometric distance between two reconstructions is the interleaving distance of the
assembled precosheaves. -/
theorem geometricInterleavingDistance_graphPLMapperReconstruction_eq (a b : ι → ℝ)
    (a' b' : ι' → ℝ) :
    RGraph.geometricInterleavingDistance (graphPLMapperReconstruction G h a b)
      (graphPLMapperReconstruction G g a' b') =
    interleavingDistance (coverComponents (plHeight G h) (fun i => ioo (a i) (b i)))
      (coverComponents (plHeight G g) (fun i => ioo (a' i) (b' i))) := by
  rw [RGraph.geometricInterleavingDistance_eq_interleavingDistance]
  exact interleavingDistance_congr
    (categoricalMapperReconstructionIso (plHeight G h) a b
      (fun i => finite_zerothHomotopy G h (ioo (a i) (b i))))
    (categoricalMapperReconstructionIso (plHeight G g) a' b'
      (fun i => finite_zerothHomotopy G g (ioo (a' i) (b' i))))

variable {a b : ι → ℝ} {a' b' : ι' → ℝ}

private theorem geometricInterleavingDistance_mapperReeb_le_add_of_le {D : ℝ≥0∞} {ρ ρ' : ℝ≥0∞}
    (hρ : RGraph.geometricInterleavingDistance (graphPLMapperReconstruction G h a b)
      (graphPLReebGraph G h) ≤ ρ)
    (hρ' : RGraph.geometricInterleavingDistance (graphPLMapperReconstruction G g a' b')
      (graphPLReebGraph G g) ≤ ρ')
    (hD : RGraph.geometricInterleavingDistance (graphPLReebGraph G h) (graphPLReebGraph G g) ≤ D) :
    RGraph.geometricInterleavingDistance (graphPLMapperReconstruction G h a b)
      (graphPLMapperReconstruction G g a' b') ≤ ρ + D + ρ' := by
  rw [RGraph.geometricInterleavingDistance_comm _ (graphPLReebGraph G g)] at hρ'
  calc _ ≤ _ := RGraph.geometricInterleavingDistance_triangle _ (graphPLReebGraph G h) _
    _ ≤ _ := add_le_add_right (RGraph.geometricInterleavingDistance_triangle _
      (graphPLReebGraph G g) _) _
    _ ≤ ρ + (D + ρ') := add_le_add hρ (add_le_add hD hρ')
    _ = ρ + D + ρ' := (add_assoc _ _ _).symm

private theorem geometricInterleavingDistance_graphPLReebGraph_le_add_of_le {ρ ρ' : ℝ≥0∞}
    (hρ : RGraph.geometricInterleavingDistance (graphPLMapperReconstruction G h a b)
      (graphPLReebGraph G h) ≤ ρ)
    (hρ' : RGraph.geometricInterleavingDistance (graphPLMapperReconstruction G g a' b')
      (graphPLReebGraph G g) ≤ ρ') :
    RGraph.geometricInterleavingDistance (graphPLReebGraph G h) (graphPLReebGraph G g) ≤
      RGraph.geometricInterleavingDistance (graphPLMapperReconstruction G h a b)
        (graphPLMapperReconstruction G g a' b') + ρ + ρ' := by
  rw [RGraph.geometricInterleavingDistance_comm _ (graphPLReebGraph G h)] at hρ
  calc _ ≤ _ := RGraph.geometricInterleavingDistance_triangle _
        (graphPLMapperReconstruction G h a b) _
    _ ≤ _ := add_le_add_right (RGraph.geometricInterleavingDistance_triangle _
        (graphPLMapperReconstruction G g a' b') _) _
    _ ≤ ρ + (RGraph.geometricInterleavingDistance (graphPLMapperReconstruction G h a b)
          (graphPLMapperReconstruction G g a' b') + ρ') :=
        add_le_add hρ (add_le_add le_rfl hρ')
    _ = _ := by ring

variable (hcov : ∀ x, ∃ i, plHeight G h x ∈ ioo (a i) (b i))
  (hcov' : ∀ x, ∃ i, plHeight G g x ∈ ioo (a' i) (b' i))
include hcov hcov'

/-- The geometric distance between the reconstructions of two vertex-height functions is at
most the two cover resolutions plus the product extended distance of the heights. -/
theorem geometricInterleavingDistance_mapperReeb_le_add_edist [Fintype V] :
    RGraph.geometricInterleavingDistance (graphPLMapperReconstruction G h a b)
      (graphPLMapperReconstruction G g a' b') ≤
      (coverResolution a b : ℝ≥0∞) + edist h g + coverResolution a' b' :=
  geometricInterleavingDistance_mapperReeb_le_add_of_le G h g
    (geometricInterleavingDistance_mapperReeb_le G h a b hcov)
    (geometricInterleavingDistance_mapperReeb_le G g a' b' hcov')
    (geometricInterleavingDistance_graphPLReebGraph_le_edist G h g)

/-- Vertex-budget form: `|h v - g v| ≤ ε` gives the bound `res + ε + res'`. -/
theorem geometricInterleavingDistance_mapperReeb_le_add {ε : ℝ≥0}
    (hhg : ∀ v, |h v - g v| ≤ ε) :
    RGraph.geometricInterleavingDistance (graphPLMapperReconstruction G h a b)
      (graphPLMapperReconstruction G g a' b') ≤
      (coverResolution a b : ℝ≥0∞) + ε + coverResolution a' b' :=
  geometricInterleavingDistance_mapperReeb_le_add_of_le G h g
    (geometricInterleavingDistance_mapperReeb_le G h a b hcov)
    (geometricInterleavingDistance_mapperReeb_le G g a' b' hcov')
    (geometricInterleavingDistance_graphPLReebGraph_le G hhg)

/-- Retained-resolution form of the product-distance bound. -/
theorem geometricInterleavingDistance_mapperReeb_le_add_edist_retained [Fintype V] :
    RGraph.geometricInterleavingDistance (graphPLMapperReconstruction G h a b)
      (graphPLMapperReconstruction G g a' b') ≤
      (retainedCoverResolution (plHeight G h) a b : ℝ≥0∞) + edist h g +
        retainedCoverResolution (plHeight G g) a' b' :=
  geometricInterleavingDistance_mapperReeb_le_add_of_le G h g
    (geometricInterleavingDistance_mapperReeb_le_retained G h a b hcov)
    (geometricInterleavingDistance_mapperReeb_le_retained G g a' b' hcov')
    (geometricInterleavingDistance_graphPLReebGraph_le_edist G h g)

/-- Retained-resolution form of the vertex-budget bound. -/
theorem geometricInterleavingDistance_mapperReeb_le_add_retained {ε : ℝ≥0}
    (hhg : ∀ v, |h v - g v| ≤ ε) :
    RGraph.geometricInterleavingDistance (graphPLMapperReconstruction G h a b)
      (graphPLMapperReconstruction G g a' b') ≤
      (retainedCoverResolution (plHeight G h) a b : ℝ≥0∞) + ε +
        retainedCoverResolution (plHeight G g) a' b' :=
  geometricInterleavingDistance_mapperReeb_le_add_of_le G h g
    (geometricInterleavingDistance_mapperReeb_le_retained G h a b hcov)
    (geometricInterleavingDistance_mapperReeb_le_retained G g a' b' hcov')
    (geometricInterleavingDistance_graphPLReebGraph_le G hhg)

/-- The Reeb distance is at most the Mapper distance plus the two cover resolutions. -/
theorem geometricInterleavingDistance_graphPLReebGraph_le_mapperReeb_add :
    RGraph.geometricInterleavingDistance (graphPLReebGraph G h) (graphPLReebGraph G g) ≤
      RGraph.geometricInterleavingDistance (graphPLMapperReconstruction G h a b)
        (graphPLMapperReconstruction G g a' b') +
        (coverResolution a b : ℝ≥0∞) + coverResolution a' b' :=
  geometricInterleavingDistance_graphPLReebGraph_le_add_of_le G h g
    (geometricInterleavingDistance_mapperReeb_le G h a b hcov)
    (geometricInterleavingDistance_mapperReeb_le G g a' b' hcov')

/-- The Mapper distance is at most the Reeb distance plus the two cover resolutions. -/
theorem geometricInterleavingDistance_mapperReeb_le_graphPLReebGraph_add :
    RGraph.geometricInterleavingDistance (graphPLMapperReconstruction G h a b)
      (graphPLMapperReconstruction G g a' b') ≤
      RGraph.geometricInterleavingDistance (graphPLReebGraph G h) (graphPLReebGraph G g) +
        (coverResolution a b : ℝ≥0∞) + coverResolution a' b' := by
  exact geometricInterleavingDistance_mapperReeb_le_add_of_le G h g
    (geometricInterleavingDistance_mapperReeb_le G h a b hcov)
    (geometricInterleavingDistance_mapperReeb_le G g a' b' hcov') le_rfl |>.trans_eq
    (by ring)

/-- Lower bound by the maximal vertex heights. -/
theorem ofReal_abs_sup'_sub_le_geometricInterleavingDistance_mapperReeb_add [Fintype V] [Nonempty V] :
    ENNReal.ofReal |Finset.univ.sup' Finset.univ_nonempty h -
        Finset.univ.sup' Finset.univ_nonempty g| ≤
      RGraph.geometricInterleavingDistance (graphPLMapperReconstruction G h a b)
        (graphPLMapperReconstruction G g a' b') +
        (coverResolution a b : ℝ≥0∞) + coverResolution a' b' :=
  (ofReal_abs_sup'_sub_le_geometricInterleavingDistance_graphPLReebGraph G h g).trans
    (geometricInterleavingDistance_graphPLReebGraph_le_mapperReeb_add G h g hcov hcov')

/-- Lower bound by the minimal vertex heights. -/
theorem ofReal_abs_inf'_sub_le_geometricInterleavingDistance_mapperReeb_add [Fintype V] [Nonempty V] :
    ENNReal.ofReal |Finset.univ.inf' Finset.univ_nonempty h -
        Finset.univ.inf' Finset.univ_nonempty g| ≤
      RGraph.geometricInterleavingDistance (graphPLMapperReconstruction G h a b)
        (graphPLMapperReconstruction G g a' b') +
        (coverResolution a b : ℝ≥0∞) + coverResolution a' b' :=
  (ofReal_abs_inf'_sub_le_geometricInterleavingDistance_graphPLReebGraph G h g).trans
    (geometricInterleavingDistance_graphPLReebGraph_le_mapperReeb_add G h g hcov hcov')

end Graph

section SameCover

variable {ι : Type} [Finite ι] {V : Type} [Finite V] (G : SimpleGraph V) (h g : V → ℝ)
  (a b : ι → ℝ)

/-- With one cover for both heights, the bound is twice the resolution plus the distance of
the heights. -/
theorem geometricInterleavingDistance_mapperReeb_le_two_mul_add_edist [Fintype V]
    (hcov : ∀ x, ∃ i, plHeight G h x ∈ ioo (a i) (b i))
    (hcov' : ∀ x, ∃ i, plHeight G g x ∈ ioo (a i) (b i)) :
    RGraph.geometricInterleavingDistance (graphPLMapperReconstruction G h a b)
      (graphPLMapperReconstruction G g a b) ≤ 2 * (coverResolution a b : ℝ≥0∞) + edist h g :=
  (geometricInterleavingDistance_mapperReeb_le_add_edist G h g hcov hcov').trans_eq (by ring)

omit [Finite ι] in
/-- Every positive width admits finite covers of both heights whose reconstructions are within
`edist h g` plus twice that width. -/
theorem exists_graphPLMapperReconstruction_pair_le [Fintype V] {r : ℝ} (hr : 0 < r) :
    ∃ n n' : ℕ, ∃ (a b : Fin n → ℝ) (a' b' : Fin n' → ℝ),
      (∀ x, ∃ i, plHeight G h x ∈ ioo (a i) (b i)) ∧
      (∀ x, ∃ i, plHeight G g x ∈ ioo (a' i) (b' i)) ∧
      RGraph.geometricInterleavingDistance (graphPLMapperReconstruction G h a b)
        (graphPLMapperReconstruction G g a' b') ≤
        edist h g + 2 * (Real.toNNReal r : ℝ≥0∞) := by
  obtain ⟨n, a, b, hcov, hres⟩ := exists_graphPLMapperCover_resolution_le G h hr
  obtain ⟨n', a', b', hcov', hres'⟩ := exists_graphPLMapperCover_resolution_le G g hr
  refine ⟨n, n', a, b, a', b', hcov, hcov', ?_⟩
  calc _ ≤ _ := geometricInterleavingDistance_mapperReeb_le_add_edist G h g hcov hcov'
    _ ≤ (Real.toNNReal r : ℝ≥0∞) + edist h g + (Real.toNNReal r : ℝ≥0∞) :=
      add_le_add (add_le_add (ENNReal.coe_le_coe.2 hres) le_rfl) (ENNReal.coe_le_coe.2 hres')
    _ = _ := by ring

end SameCover

section Limit

variable {V : Type} [Finite V] (G : SimpleGraph V) (h g : V → ℝ)
  {α : Type*} {l : Filter α} {κ κ' : α → Type} [∀ t, Finite (κ t)] [∀ t, Finite (κ' t)]
  {a b : ∀ t, κ t → ℝ} {a' b' : ∀ t, κ' t → ℝ}

private theorem tendsto_of_add_sandwich {d : ℝ≥0∞} {m ρ : α → ℝ≥0∞}
    (hρ : Tendsto ρ l (𝓝 0)) (hlow : ∀ t, d ≤ m t + ρ t) (hup : ∀ t, m t ≤ d + ρ t) :
    Tendsto m l (𝓝 d) := by
  have hl : Tendsto (fun t => d - ρ t) l (𝓝 d) := by
    simpa using ENNReal.Tendsto.sub tendsto_const_nhds hρ (Or.inr ENNReal.zero_ne_top)
  have hu : Tendsto (fun t => d + ρ t) l (𝓝 d) := by
    simpa using (tendsto_const_nhds (x := d)).add hρ
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hl hu
    (fun t => tsub_le_iff_right.2 (hlow t)) hup

/-- Along cover families with vanishing resolutions, the Mapper distance of two vertex heights
converges to the Reeb distance. -/
theorem tendsto_geometricInterleavingDistance_mapperReeb_pair
    (hcov : ∀ t x, ∃ i, plHeight G h x ∈ ioo (a t i) (b t i))
    (hcov' : ∀ t x, ∃ i, plHeight G g x ∈ ioo (a' t i) (b' t i))
    (hres : Tendsto (fun t => (coverResolution (a t) (b t) : ℝ≥0∞)) l (𝓝 0))
    (hres' : Tendsto (fun t => (coverResolution (a' t) (b' t) : ℝ≥0∞)) l (𝓝 0)) :
    Tendsto (fun t => RGraph.geometricInterleavingDistance
      (graphPLMapperReconstruction G h (a t) (b t))
      (graphPLMapperReconstruction G g (a' t) (b' t))) l
      (𝓝 (RGraph.geometricInterleavingDistance (graphPLReebGraph G h)
        (graphPLReebGraph G g))) := by
  refine tendsto_of_add_sandwich (ρ := fun t => (coverResolution (a t) (b t) : ℝ≥0∞) +
    coverResolution (a' t) (b' t)) (by simpa using hres.add hres') (fun t => ?_) (fun t => ?_)
  · rw [← add_assoc]
    exact geometricInterleavingDistance_graphPLReebGraph_le_mapperReeb_add G h g (hcov t) (hcov' t)
  · rw [← add_assoc]
    exact geometricInterleavingDistance_mapperReeb_le_graphPLReebGraph_add G h g (hcov t) (hcov' t)

/-- Retained-resolution form of the convergence theorem. -/
theorem tendsto_geometricInterleavingDistance_mapperReeb_pair_retained
    (hcov : ∀ t x, ∃ i, plHeight G h x ∈ ioo (a t i) (b t i))
    (hcov' : ∀ t x, ∃ i, plHeight G g x ∈ ioo (a' t i) (b' t i))
    (hres : Tendsto (fun t => (retainedCoverResolution (plHeight G h) (a t) (b t) : ℝ≥0∞))
      l (𝓝 0))
    (hres' : Tendsto (fun t => (retainedCoverResolution (plHeight G g) (a' t) (b' t) : ℝ≥0∞))
      l (𝓝 0)) :
    Tendsto (fun t => RGraph.geometricInterleavingDistance
      (graphPLMapperReconstruction G h (a t) (b t))
      (graphPLMapperReconstruction G g (a' t) (b' t))) l
      (𝓝 (RGraph.geometricInterleavingDistance (graphPLReebGraph G h)
        (graphPLReebGraph G g))) := by
  refine tendsto_of_add_sandwich (ρ := fun t =>
    (retainedCoverResolution (plHeight G h) (a t) (b t) : ℝ≥0∞) +
      retainedCoverResolution (plHeight G g) (a' t) (b' t)) (by simpa using hres.add hres')
    (fun t => ?_) (fun t => ?_)
  · rw [← add_assoc]
    exact geometricInterleavingDistance_graphPLReebGraph_le_add_of_le G h g
      (geometricInterleavingDistance_mapperReeb_le_retained G h (a t) (b t) (hcov t))
      (geometricInterleavingDistance_mapperReeb_le_retained G g (a' t) (b' t) (hcov' t))
  · rw [← add_assoc]
    exact (geometricInterleavingDistance_mapperReeb_le_add_of_le G h g
      (geometricInterleavingDistance_mapperReeb_le_retained G h (a t) (b t) (hcov t))
      (geometricInterleavingDistance_mapperReeb_le_retained G g (a' t) (b' t) (hcov' t))
      le_rfl).trans_eq (by ring)

end Limit

end

end TDA.Mapper
