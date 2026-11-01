import TDA.Mapper.MapperReebConstructible
import TDA.Mapper.MapperReebApproximationExamples
import TDA.Reeb.ThickeningConstructibleExamples
import TDA.Reeb.InterleavingCardinality

/-!
# Constructible categorical Mapper reconstruction examples

The examples exercise `TDA.Mapper.MapperReebConstructible` on four kinds of input.

* **Graph-PL input.** The existing graph-PL distance identity, both error bounds and both
  convergence statements are recovered verbatim from the constructible results at
  `graphPLSpace G h`. A nonconstant edge has finite covers whose constructible reconstructions
  converge to its Reeb quotient.
* **A non-Hausdorff input.** The indiscrete two-point space at height zero is constructible
  and not Hausdorff. A two-member cover whose second member has empty pullback has full
  resolution at least `95`, while its retained resolution and geometric error are at most `2`.
  Symmetric shrinking one-member covers give geometric convergence.
* **Empty input.** The empty space with the empty label type has geometric error zero; with a
  wide member it still has error zero, because the member is removed.
* **The coverage boundary.** Empty labels cannot cover the nonempty indiscrete input; their
  reconstruction is at geometric distance `⊤` from the Reeb quotient although the full
  resolution is `0`.
-/

open Set CategoryTheory Filter
open scoped NNReal ENNReal Topology

namespace TDA.Mapper.MapperReebConstructibleExamples

open TDA.Reeb TDA.Reeb.OpenInterval TDA.Reeb.GraphPL TDA.Mapper.GraphPL
open TDA.Reeb.Examples.GraphPL
open TDA.Reeb.Examples.GraphRealization (edgeGraph)
open TDA.Reeb.Examples.ThickeningConstructible (IndiscreteBool constOver
  isConstructibleSpace_constOver_indiscreteBool isConstructibleSpace_constOver_empty
  not_t2Space_indiscreteBool)

noncomputable section

/-! ### Graph-PL input -/

section GraphPL

variable {ι : Type} [Finite ι] {V : Type} [Finite V] (G : SimpleGraph V) (h : V → ℝ)

/-- The graph-PL distance identity, recovered from the constructible one. -/
theorem graphPL_eq_of_constructible (a b : ι → ℝ) :
    RGraph.geometricInterleavingDistance (graphPLMapperReconstruction G h a b)
      (GraphPL.graphPLReebGraph G h) =
    interleavingDistance (coverComponents (plHeight G h) (fun i => ioo (a i) (b i)))
      (intervalComponents (plHeight G h)) :=
  geometricInterleavingDistance_constructibleMapperReeb_eq (graphPLSpace G h) a b

/-- The graph-PL full-resolution bound, recovered from the constructible one. -/
theorem graphPL_le_of_constructible (a b : ι → ℝ)
    (hcov : ∀ x, ∃ i, plHeight G h x ∈ ioo (a i) (b i)) :
    RGraph.geometricInterleavingDistance (graphPLMapperReconstruction G h a b)
      (GraphPL.graphPLReebGraph G h) ≤ (coverResolution a b : ℝ≥0∞) :=
  geometricInterleavingDistance_constructibleMapperReeb_le (graphPLSpace G h) a b hcov

/-- The graph-PL retained-resolution bound, recovered from the constructible one. -/
theorem graphPL_le_retained_of_constructible (a b : ι → ℝ)
    (hcov : ∀ x, ∃ i, plHeight G h x ∈ ioo (a i) (b i)) :
    RGraph.geometricInterleavingDistance (graphPLMapperReconstruction G h a b)
      (GraphPL.graphPLReebGraph G h) ≤
        (retainedCoverResolution (plHeight G h) a b : ℝ≥0∞) :=
  geometricInterleavingDistance_constructibleMapperReeb_le_retained (graphPLSpace G h) a b hcov

/-- The graph-PL convergence statement, recovered from the constructible one. -/
theorem graphPL_tendsto_of_constructible
    {α : Type*} {l : Filter α} (κ : α → Type) [∀ t, Finite (κ t)]
    (a b : ∀ t, κ t → ℝ)
    (hcov : ∀ t x, ∃ i, plHeight G h x ∈ ioo (a t i) (b t i))
    (hres : Tendsto (fun t => (coverResolution (a t) (b t) : ℝ≥0∞)) l (𝓝 0)) :
    Tendsto (fun t => RGraph.geometricInterleavingDistance
      (graphPLMapperReconstruction G h (a t) (b t)) (GraphPL.graphPLReebGraph G h))
      l (𝓝 0) :=
  tendsto_geometricInterleavingDistance_constructibleMapperReeb (graphPLSpace G h) κ a b
    hcov hres

/-- The graph-PL retained convergence statement, recovered from the constructible one. -/
theorem graphPL_tendsto_retained_of_constructible
    {α : Type*} {l : Filter α} (κ : α → Type) [∀ t, Finite (κ t)]
    (a b : ∀ t, κ t → ℝ)
    (hcov : ∀ t x, ∃ i, plHeight G h x ∈ ioo (a t i) (b t i))
    (hres : Tendsto (fun t => (retainedCoverResolution (plHeight G h) (a t) (b t) : ℝ≥0∞))
      l (𝓝 0)) :
    Tendsto (fun t => RGraph.geometricInterleavingDistance
      (graphPLMapperReconstruction G h (a t) (b t)) (GraphPL.graphPLReebGraph G h))
      l (𝓝 0) :=
  tendsto_geometricInterleavingDistance_constructibleMapperReeb_retained (graphPLSpace G h) κ
    a b hcov hres

end GraphPL

/-- A nonconstant edge, as a constructible ℝ-space, has finite covers of its attained heights
whose constructible reconstructions converge to its actual Reeb quotient. -/
theorem nonconstant_edge_constructible_convergence :
    ∃ n : ℕ → ℕ, ∃ a b : ∀ t, Fin (n t) → ℝ,
      (∀ t x, ∃ i, overBaseMap (graphPLSpace edgeGraph h02).obj x ∈ ioo (a t i) (b t i)) ∧
      Tendsto (fun t => RGraph.geometricInterleavingDistance
        (constructibleMapperReconstruction (graphPLSpace edgeGraph h02) (a t) (b t))
        (quotientRGraphFunctor.obj (graphPLSpace edgeGraph h02))) atTop (𝓝 0) := by
  obtain ⟨n, a, b, hcov, -, hres, -⟩ :=
    MapperReebApproximationExamples.nonconstant_edge_convergent_reconstructions
  exact ⟨n, a, b, hcov, tendsto_geometricInterleavingDistance_constructibleMapperReeb
    (graphPLSpace edgeGraph h02) (fun t => Fin (n t)) a b hcov hres⟩

/-! ### A non-Hausdorff input -/

/-- The indiscrete two-point space at constant height zero, as a constructible ℝ-space. -/
def indiscretePoint : ConstructibleSpaceCat :=
  ⟨constOver IndiscreteBool 0, isConstructibleSpace_constOver_indiscreteBool 0⟩

/-- The input space is not Hausdorff. -/
theorem not_t2Space_indiscretePoint : ¬ T2Space indiscretePoint.obj.left :=
  not_t2Space_indiscreteBool

/-- Every point has height zero. -/
theorem indiscretePoint_height (x : indiscretePoint.obj.left) :
    overBaseMap indiscretePoint.obj x = 0 :=
  rfl

/-- Left endpoints of a cover with one member far from the attained height. -/
def indiscreteLeft : Fin 2 → ℝ := ![-1, 5]

/-- Right endpoints of the same cover. -/
def indiscreteRight : Fin 2 → ℝ := ![1, 100]

/-- The first member covers every attained height. -/
theorem indiscrete_covers (x : indiscretePoint.obj.left) :
    ∃ i, overBaseMap indiscretePoint.obj x ∈ ioo (indiscreteLeft i) (indiscreteRight i) :=
  ⟨0, by rw [indiscretePoint_height]; norm_num [indiscreteLeft, indiscreteRight, mem_ioo]⟩

/-- Only the first member is retained; the far member has empty pullback. -/
theorem indiscrete_retained_eq_zero
    (i : RetainedCoverMember (overBaseMap indiscretePoint.obj)
      (fun i => ioo (indiscreteLeft i) (indiscreteRight i))) : i.val = 0 := by
  obtain ⟨i, x, hx⟩ := i
  change overBaseMap indiscretePoint.obj x ∈ ioo (indiscreteLeft i) (indiscreteRight i) at hx
  rw [indiscretePoint_height] at hx
  fin_cases i
  · rfl
  · norm_num [indiscreteLeft, indiscreteRight, mem_ioo] at hx

/-- The far member keeps the full resolution at least `95`. -/
theorem indiscrete_coverResolution_ge :
    (95 : ℝ) ≤ coverResolution indiscreteLeft indiscreteRight := by
  have h := width_le_coverResolution indiscreteLeft indiscreteRight 1
  norm_num [indiscreteLeft, indiscreteRight] at h
  exact h

/-- The retained resolution is at most the width `2` of the first member. -/
theorem indiscrete_retainedCoverResolution_le :
    retainedCoverResolution (overBaseMap indiscretePoint.obj) indiscreteLeft indiscreteRight ≤
      2 := by
  let _ := Fintype.ofFinite (RetainedCoverMember (overBaseMap indiscretePoint.obj)
    (fun i => ioo (indiscreteLeft i) (indiscreteRight i)))
  unfold retainedCoverResolution coverResolution
  refine Finset.sup_le fun i _ => ?_
  dsimp only
  rw [indiscrete_retained_eq_zero i, ← NNReal.coe_le_coe, Real.coe_toNNReal']
  norm_num [indiscreteLeft, indiscreteRight]

/-- **Retained-cover removal on non-Hausdorff input.** The geometric error is at most `2`,
far below the full resolution. -/
theorem indiscrete_geometric_error_le :
    RGraph.geometricInterleavingDistance
      (constructibleMapperReconstruction indiscretePoint indiscreteLeft indiscreteRight)
      (quotientRGraphFunctor.obj indiscretePoint) ≤ 2 := by
  refine (geometricInterleavingDistance_constructibleMapperReeb_le_retained indiscretePoint
    indiscreteLeft indiscreteRight indiscrete_covers).trans ?_
  exact_mod_cast indiscrete_retainedCoverResolution_le

/-- Symmetric one-member covers of half-width `1 / (t + 1)`. -/
def shrinkingLeft (t : ℕ) : Unit → ℝ := fun _ => -(1 / ((t : ℝ) + 1))

/-- Right endpoints of the symmetric shrinking covers. -/
def shrinkingRight (t : ℕ) : Unit → ℝ := fun _ => 1 / ((t : ℝ) + 1)

/-- **Convergence on non-Hausdorff input.** The shrinking covers give geometric convergence to
the Reeb quotient of the indiscrete two-point space. -/
theorem indiscrete_shrinking_convergence :
    Tendsto (fun t => RGraph.geometricInterleavingDistance
      (constructibleMapperReconstruction indiscretePoint (shrinkingLeft t) (shrinkingRight t))
      (quotientRGraphFunctor.obj indiscretePoint)) atTop (𝓝 0) := by
  have hcov (t : ℕ) (x : indiscretePoint.obj.left) :
      ∃ i, overBaseMap indiscretePoint.obj x ∈ ioo (shrinkingLeft t i) (shrinkingRight t i) := by
    refine ⟨(), ?_⟩
    rw [indiscretePoint_height]
    have : (0 : ℝ) < 1 / ((t : ℝ) + 1) := by positivity
    change -(1 / ((t : ℝ) + 1)) < 0 ∧ 0 < 1 / ((t : ℝ) + 1)
    exact ⟨neg_lt_zero.mpr this, this⟩
  have hres (t : ℕ) : coverResolution (shrinkingLeft t) (shrinkingRight t) ≤
      Real.toNNReal (2 * (1 / ((t : ℝ) + 1))) := by
    unfold coverResolution
    exact Finset.sup_le fun _ _ => Real.toNNReal_le_toNNReal (by
      simp only [shrinkingLeft, shrinkingRight]; linarith)
  have hinner : Tendsto (fun t : ℕ =>
      Real.toNNReal (2 * (1 / ((t : ℝ) + 1)))) atTop (𝓝 0) := by
    have h2 := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 2
    rw [mul_zero] at h2
    simpa only [Function.comp_def, Real.toNNReal_zero] using
      (continuous_real_toNNReal.tendsto 0).comp h2
  have hlim : Tendsto (fun t : ℕ =>
      (Real.toNNReal (2 * (1 / ((t : ℝ) + 1))) : ℝ≥0∞)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.coe_zero] using
      (ENNReal.continuous_coe.tendsto 0).comp hinner
  exact tendsto_geometricInterleavingDistance_constructibleMapperReeb indiscretePoint
    (fun _ => Unit) shrinkingLeft shrinkingRight hcov
    (tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun _ => bot_le) (fun t => ENNReal.coe_le_coe.mpr (hres t)))

/-! ### Empty input -/

/-- The empty space at height zero, as a constructible ℝ-space. -/
def emptySpace : ConstructibleSpaceCat :=
  ⟨constOver Empty 0, isConstructibleSpace_constOver_empty 0⟩

/-- **Empty input and empty labels.** The geometric error is zero. -/
theorem empty_input_empty_labels_error_zero (a b : Empty → ℝ) :
    RGraph.geometricInterleavingDistance (constructibleMapperReconstruction emptySpace a b)
      (quotientRGraphFunctor.obj emptySpace) = 0 := by
  apply le_antisymm _ bot_le
  have h := geometricInterleavingDistance_constructibleMapperReeb_le emptySpace a b
    (fun x => Empty.elim x)
  norm_num [coverResolution] at h
  exact h.le

/-- **Empty input with a wide member.** The member is removed, so the geometric error is zero
although the full resolution is `2`. -/
theorem empty_input_wide_member_error_zero :
    coverResolution (fun _ : Unit => (-1 : ℝ)) (fun _ => 1) = 2 ∧
    RGraph.geometricInterleavingDistance
      (constructibleMapperReconstruction emptySpace (fun _ : Unit => (-1 : ℝ)) (fun _ => 1))
      (quotientRGraphFunctor.obj emptySpace) = 0 := by
  constructor
  · norm_num [coverResolution]
  · apply le_antisymm _ bot_le
    refine (geometricInterleavingDistance_constructibleMapperReeb_le_retained emptySpace
      (fun _ : Unit => (-1 : ℝ)) (fun _ => 1) (fun x => Empty.elim x)).trans ?_
    let _ := Fintype.ofFinite (RetainedCoverMember (overBaseMap emptySpace.obj)
      (fun _ : Unit => ioo (-1) 1))
    have : retainedCoverResolution (overBaseMap emptySpace.obj)
        (fun _ : Unit => (-1 : ℝ)) (fun _ => 1) = 0 := by
      unfold retainedCoverResolution coverResolution
      exact le_antisymm (Finset.sup_le fun i _ => Empty.elim i.property.some) bot_le
    rw [this]
    rfl

/-! ### The coverage boundary -/

/-- **Empty labels cannot cover nonempty input.** -/
theorem empty_labels_not_cover (a b : Empty → ℝ) :
    ¬ ∀ x : indiscretePoint.obj.left, ∃ i, overBaseMap indiscretePoint.obj x ∈ ioo (a i) (b i) :=
  fun h => (h (true : Bool)).choose.elim

/-- Without coverage the bound fails: empty labels have full resolution `0`, while their
reconstruction is at geometric distance `⊤` from the Reeb quotient of nonempty input. -/
theorem empty_labels_error_top (a b : Empty → ℝ) :
    coverResolution a b = 0 ∧
    RGraph.geometricInterleavingDistance (constructibleMapperReconstruction indiscretePoint a b)
      (quotientRGraphFunctor.obj indiscretePoint) = ⊤ := by
  constructor
  · norm_num [coverResolution]
  · rw [geometricInterleavingDistance_constructibleMapperReeb_eq]
    apply interleavingDistance_eq_top_of_card_ne
    have hempty : IsEmpty ((coverComponents (overBaseMap indiscretePoint.obj)
        (fun i => ioo (a i) (b i))).obj ⊤) := by
      constructor
      intro c
      induction c using ZerothHomotopy.rec with
      | mk x =>
        obtain ⟨i, -⟩ := mem_coverSaturation.mp x.property
        exact i.elim
    have := finite_intervalComponents_constructibleSpace indiscretePoint ⊤
    have hne : Nonempty ((intervalComponents (overBaseMap indiscretePoint.obj)).obj ⊤) :=
      ⟨ZerothHomotopy.mk ⟨(true : Bool), trivial⟩⟩
    rw [Nat.card_of_isEmpty]
    exact (Nat.card_pos (α := (intervalComponents (overBaseMap indiscretePoint.obj)).obj ⊤)).ne

end

end TDA.Mapper.MapperReebConstructibleExamples
