import TDA.Mapper.MapperReebApproximation
import TDA.Mapper.GraphPLConstructible
import TDA.Reeb.ConstructibleComparison

/-!
# Categorical Mapper reconstruction of constructible ℝ-spaces

Let `A` be a constructible ℝ-space in universe zero, with structure map `f = overBaseMap A.obj`,
and let `U i = (a i, b i)` be a finite family of open intervals. The path-component cosheaf of
`A` is constructible, so every value `f⁻¹(U i)` has finitely many path components
(`finite_intervalComponents_constructibleSpace`). This supplies the finiteness hypothesis of
`categoricalMapperReconstruction`, giving `constructibleMapperReconstruction A a b`, the
reconstruction `D P_K C_K` of the categorical Mapper assembly `coverComponents f U`. Callers
supply no finiteness assumption. No Hausdorff, graph-PL or nonempty-input hypothesis is made,
and the label type may be empty.

* **Distance identification**
  (`geometricInterleavingDistance_constructibleMapperReeb_eq`): the geometric interleaving
  distance from the reconstruction to the actual Reeb quotient
  `quotientRGraphFunctor.obj A` equals the interleaving distance between `coverComponents f U`
  and `intervalComponents f`. It combines the reconstruction counit with the natural
  comparison isomorphism `constructibleCosheafComparisonIso` (de Silva–Munch–Patel,
  Theorem 3.17). No coverage assumption is needed.
* **Error bounds** (`geometricInterleavingDistance_constructibleMapperReeb_le_retained`,
  `geometricInterleavingDistance_constructibleMapperReeb_le`): if the intervals cover every
  attained height, the geometric error is at most `retainedCoverResolution f a b`, the
  maximum full width of the members with nonempty pullback, and at most the full resolution
  `coverResolution a b`; `retainedCoverResolution_le_coverResolution` compares the two.
* **Convergence** (`tendsto_geometricInterleavingDistance_constructibleMapperReeb` and its
  `_retained` form): along any filter of finite covers, with label types allowed to vary, each
  covering the attained heights, vanishing full or retained resolution gives vanishing
  geometric error.

For a finite graph-PL input, `graphPLSpace G h` has structure map `plHeight G h` and Reeb
quotient `graphPLReebGraph G h`, both definitionally; the reconstruction is definitionally
`graphPLMapperReconstruction G h a b` (`constructibleMapperReconstruction_graphPLSpace`), so the
graph-PL results are recovered as specializations.

The resolutions use full ambient interval widths, never widths clipped to the attained range.
The construction is abstract and noncomputable; it asserts no executable component algorithm,
no identification with the ordinary Mapper simple graph and no higher-dimensional Reeb-space
theorem.
-/

open Set CategoryTheory Filter
open scoped NNReal ENNReal Topology

namespace TDA.Mapper

open TDA.Reeb TDA.Reeb.OpenInterval TDA.Reeb.GraphPL TDA.Mapper.GraphPL

noncomputable section

section Resolution

variable {ι : Type} [Finite ι] {X : Type} [TopologicalSpace X]

/-- Removing exactly the members with empty pullback does not increase the full-width
resolution. -/
theorem retainedCoverResolution_le_coverResolution (f : C(X, ℝ)) (a b : ι → ℝ) :
    retainedCoverResolution f a b ≤ coverResolution a b := by
  let _ := Fintype.ofFinite (RetainedCoverMember f (fun i => ioo (a i) (b i)))
  unfold retainedCoverResolution coverResolution
  refine Finset.sup_le fun i _ => ?_
  rw [← NNReal.coe_le_coe, Real.coe_toNNReal']
  exact max_le (width_le_coverResolution a b i.val) (coverResolution a b).coe_nonneg

end Resolution

/-- **Finite values.** The path components of every interval preimage of a constructible
ℝ-space form a finite set, because its path-component cosheaf is constructible
(de Silva–Munch–Patel, Proposition 3.16). -/
theorem finite_intervalComponents_constructibleSpace (A : ConstructibleSpaceCat)
    (I : OpenInterval) : Finite ((intervalComponents (overBaseMap A.obj)).obj I) := by
  obtain ⟨_, _, h, -⟩ := exists_isConstructibleAt_of_isConstructibleSpace A.property
  exact h.finite I

variable {ι : Type} [Finite ι] (A : ConstructibleSpaceCat)

/-- Categorical Mapper reconstruction `D P_K C_K` of a constructible ℝ-space over the open
intervals `(a i, b i)`. The finiteness hypothesis of `categoricalMapperReconstruction` is
discharged by constructibility. -/
def constructibleMapperReconstruction (a b : ι → ℝ) : RGraph.RGraphCat :=
  categoricalMapperReconstruction (overBaseMap A.obj) a b
    (fun i => finite_intervalComponents_constructibleSpace A (ioo (a i) (b i)))

/-- The constructible reconstruction is the categorical reconstruction for every proof of the
finiteness hypothesis. -/
theorem constructibleMapperReconstruction_eq (a b : ι → ℝ)
    (hfinite : ∀ i, Finite ((intervalComponents (overBaseMap A.obj)).obj (ioo (a i) (b i)))) :
    constructibleMapperReconstruction A a b =
      categoricalMapperReconstruction (overBaseMap A.obj) a b hfinite :=
  rfl

/-- The reconstruction's interval components are naturally the categorical assembly. -/
def constructibleMapperReconstructionIso (a b : ι → ℝ) :
    (RGraph.cosheafFunctor.obj (constructibleMapperReconstruction A a b)).obj ≅
      coverComponents (overBaseMap A.obj) (fun i => ioo (a i) (b i)) :=
  categoricalMapperReconstructionIso (overBaseMap A.obj) a b
    (fun i => finite_intervalComponents_constructibleSpace A (ioo (a i) (b i)))

/-- **Distance identification.** The geometric interleaving distance from the reconstruction to
the Reeb quotient of `A` equals the interleaving distance from the categorical assembly to the
path-component cosheaf of `A`. No coverage assumption is needed. -/
theorem geometricInterleavingDistance_constructibleMapperReeb_eq (a b : ι → ℝ) :
    RGraph.geometricInterleavingDistance (constructibleMapperReconstruction A a b)
      (quotientRGraphFunctor.obj A) =
    interleavingDistance (coverComponents (overBaseMap A.obj) (fun i => ioo (a i) (b i)))
      (intervalComponents (overBaseMap A.obj)) := by
  rw [RGraph.geometricInterleavingDistance_eq_interleavingDistance]
  exact interleavingDistance_congr (constructibleMapperReconstructionIso A a b)
    ((ObjectProperty.ι _).mapIso (constructibleCosheafComparisonIso.app A)).symm

/-- **Retained error bound.** If the intervals cover every attained height, the geometric error
is at most the maximum full width of the members with nonempty pullback. -/
theorem geometricInterleavingDistance_constructibleMapperReeb_le_retained (a b : ι → ℝ)
    (hcov : ∀ x, ∃ i, overBaseMap A.obj x ∈ ioo (a i) (b i)) :
    RGraph.geometricInterleavingDistance (constructibleMapperReconstruction A a b)
      (quotientRGraphFunctor.obj A) ≤
        (retainedCoverResolution (overBaseMap A.obj) a b : ℝ≥0∞) := by
  rw [geometricInterleavingDistance_constructibleMapperReeb_eq,
    interleavingDistance_congr
      (coverComponentsRetainedIso (overBaseMap A.obj) (fun i => ioo (a i) (b i)))
      (Iso.refl _)]
  exact interleavingDistance_coverComponents_le (overBaseMap A.obj)
    (retainedCover (overBaseMap A.obj) (fun i => ioo (a i) (b i)))
    (retainedCoverResolution (overBaseMap A.obj) a b)
    (retainedCover_covers (overBaseMap A.obj) (fun i => ioo (a i) (b i)) hcov)
    (diameter_le_coverResolution
      (fun i : RetainedCoverMember (overBaseMap A.obj) (fun i => ioo (a i) (b i)) => a i.val)
      (fun i => b i.val))

/-- **Full error bound.** If the intervals cover every attained height, the geometric error is
at most the full cover resolution. -/
theorem geometricInterleavingDistance_constructibleMapperReeb_le (a b : ι → ℝ)
    (hcov : ∀ x, ∃ i, overBaseMap A.obj x ∈ ioo (a i) (b i)) :
    RGraph.geometricInterleavingDistance (constructibleMapperReconstruction A a b)
      (quotientRGraphFunctor.obj A) ≤ (coverResolution a b : ℝ≥0∞) :=
  (geometricInterleavingDistance_constructibleMapperReeb_le_retained A a b hcov).trans
    (ENNReal.coe_le_coe.mpr (retainedCoverResolution_le_coverResolution _ a b))

/-- **Convergence.** Along any filter of finite covers of the attained heights, with varying
label types, vanishing full resolution gives vanishing geometric error. -/
theorem tendsto_geometricInterleavingDistance_constructibleMapperReeb
    {α : Type*} {l : Filter α} (κ : α → Type) [∀ t, Finite (κ t)]
    (a b : ∀ t, κ t → ℝ)
    (hcov : ∀ t x, ∃ i, overBaseMap A.obj x ∈ ioo (a t i) (b t i))
    (hres : Tendsto (fun t => (coverResolution (a t) (b t) : ℝ≥0∞)) l (𝓝 0)) :
    Tendsto (fun t => RGraph.geometricInterleavingDistance
      (constructibleMapperReconstruction A (a t) (b t)) (quotientRGraphFunctor.obj A))
      l (𝓝 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hres
    (fun _ => bot_le) (fun t => geometricInterleavingDistance_constructibleMapperReeb_le A
      (a t) (b t) (hcov t))

/-- **Retained convergence.** Vanishing retained full-width resolution suffices, even when
members with empty pullback keep large ambient widths. -/
theorem tendsto_geometricInterleavingDistance_constructibleMapperReeb_retained
    {α : Type*} {l : Filter α} (κ : α → Type) [∀ t, Finite (κ t)]
    (a b : ∀ t, κ t → ℝ)
    (hcov : ∀ t x, ∃ i, overBaseMap A.obj x ∈ ioo (a t i) (b t i))
    (hres : Tendsto (fun t => (retainedCoverResolution (overBaseMap A.obj) (a t) (b t) : ℝ≥0∞))
      l (𝓝 0)) :
    Tendsto (fun t => RGraph.geometricInterleavingDistance
      (constructibleMapperReconstruction A (a t) (b t)) (quotientRGraphFunctor.obj A))
      l (𝓝 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hres
    (fun _ => bot_le) (fun t => geometricInterleavingDistance_constructibleMapperReeb_le_retained
      A (a t) (b t) (hcov t))

/-! ### Graph-PL input -/

section GraphPL

variable {V : Type} [Finite V] (G : SimpleGraph V) (h : V → ℝ)

/-- On the graph-PL constructible ℝ-space, the constructible reconstruction is the graph-PL
reconstruction. -/
theorem constructibleMapperReconstruction_graphPLSpace (a b : ι → ℝ) :
    constructibleMapperReconstruction (graphPLSpace G h) a b =
      graphPLMapperReconstruction G h a b :=
  rfl

end GraphPL

end

end TDA.Mapper
