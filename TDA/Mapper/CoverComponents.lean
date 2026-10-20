import TDA.Reeb.PerturbationDistance
import Mathlib.Data.Finite.Sigma

/-!
# Components over cover saturations

For an interval `I`, its saturation by an interval family `U` is the union of all members
meeting `I`. Applying the actual inverse-image path-component functor to these unions gives
an interval precosheaf. A uniform diameter bound on the members and coverage of the attained
range give an explicit interleaving with the original interval-component precosheaf.

This module proves the component-of-union estimate used in Munch--Wang's Theorem 4.1.
The categorical colimit identification and finite geometric reconstruction are separate
bridges; the present construction does not identify ordinary Mapper with a Reeb graph.
-/

open Set CategoryTheory
open scoped NNReal ENNReal

universe u v

namespace TDA.Mapper

open TDA.Reeb TDA.Reeb.OpenInterval

variable {ι : Type v}

/-- The union of the cover intervals meeting a test interval. -/
def coverSaturation (U : ι → OpenInterval) (I : OpenInterval) : TopologicalSpace.Opens ℝ :=
  ⨆ i, ⨆ (_ : ((U i : Set ℝ) ∩ I).Nonempty), toOpens (U i)

/-- Membership records a cover member and a point where it meets the test interval. -/
theorem mem_coverSaturation {U : ι → OpenInterval} {I : OpenInterval} {x : ℝ} :
    x ∈ coverSaturation U I ↔ ∃ i, x ∈ U i ∧ ∃ y, y ∈ U i ∧ y ∈ I := by
  simp only [coverSaturation, TopologicalSpace.Opens.mem_iSup]
  constructor
  · rintro ⟨i, ⟨y, hyU, hyI⟩, hx⟩
    exact ⟨i, hx, y, hyU, hyI⟩
  · rintro ⟨i, hx, y, hyU, hyI⟩
    exact ⟨i, ⟨y, hyU, hyI⟩, hx⟩

/-- Saturation is monotone in the test interval. -/
theorem coverSaturation_mono (U : ι → OpenInterval) {I J : OpenInterval} (h : I ≤ J) :
    coverSaturation U I ≤ coverSaturation U J := by
  intro x hx
  obtain ⟨i, hx, y, hy, hyI⟩ := mem_coverSaturation.mp hx
  exact mem_coverSaturation.mpr ⟨i, hx, y, hy, h hyI⟩

/-- The monotone saturation construction, valued in actual open subsets of the line. -/
def coverSaturationFunctor (U : ι → OpenInterval) :
    OpenInterval ⥤ TopologicalSpace.Opens ℝ where
  obj := coverSaturation U
  map h := homOfLE (coverSaturation_mono U (leOfHom h))

/-- A diameter bound gives the actual inclusion of the saturation into the thickening. -/
theorem coverSaturation_le_thicken (U : ι → OpenInterval) (r : ℝ≥0)
    (hdiam : ∀ i x, x ∈ U i → ∀ y, y ∈ U i → |x - y| ≤ r) (I : OpenInterval) :
    coverSaturation U I ≤ toOpens (thicken r I) := by
  intro x hx
  obtain ⟨i, hx, y, hy, hyI⟩ := mem_coverSaturation.mp hx
  exact mem_thicken.mpr ⟨y, hyI, hdiam i x hx y hy⟩

variable {X : Type u} [TopologicalSpace X]

/-- Path components of inverse images of the actual saturated open sets. -/
def coverComponents (f : C(X, ℝ)) (U : ι → OpenInterval) : OpenInterval ⥤ Type u :=
  coverSaturationFunctor U ⋙ componentFunctor f

/-- Cover labels whose intervals meet the test interval. -/
abbrev ActiveCoverMember (U : ι → OpenInterval) (I : OpenInterval) :=
  {i : ι // ((U i : Set ℝ) ∩ I).Nonempty}

/-- An active member is contained in the actual saturation. -/
theorem coverMember_le_saturation (U : ι → OpenInterval) (I : OpenInterval)
    (i : ActiveCoverMember U I) : toOpens (U i.val) ≤ coverSaturation U I := by
  intro x hx
  obtain ⟨y, hyU, hyI⟩ := i.property
  exact mem_coverSaturation.mpr ⟨i.val, hx, y, hyU, hyI⟩

/-- The actual component map from a selected cover member to the saturated inverse image. -/
def coverComponentGenerator (f : C(X, ℝ)) (U : ι → OpenInterval) (I : OpenInterval) :
    (Σ i : ActiveCoverMember U I, (intervalComponents f).obj (U i.val)) →
      (coverComponents f U).obj I :=
  fun p => (componentFunctor f).map (homOfLE (coverMember_le_saturation U I p.1)) p.2

/-- Each saturated inverse-image component has a representative over an active cover member. -/
theorem coverComponentGenerator_surjective (f : C(X, ℝ)) (U : ι → OpenInterval)
    (I : OpenInterval) : Function.Surjective (coverComponentGenerator f U I) := by
  intro c
  induction c using ZerothHomotopy.rec with
  | mk x =>
    obtain ⟨i, hxi, y, hyU, hyI⟩ := mem_coverSaturation.mp x.2
    exact ⟨⟨⟨i, y, hyU, hyI⟩, ZerothHomotopy.mk ⟨x.1, hxi⟩⟩, rfl⟩

/-- A finite cover with finitely many pullback components has finite assembled values. -/
theorem finite_coverComponents [Finite ι] (f : C(X, ℝ)) (U : ι → OpenInterval)
    (hfinite : ∀ i, Finite ((intervalComponents f).obj (U i))) (I : OpenInterval) :
    Finite ((coverComponents f U).obj I) := by
  let : ∀ i : ActiveCoverMember U I, Finite ((intervalComponents f).obj (U i.val)) :=
    fun i => hfinite i.val
  exact Finite.of_surjective _ (coverComponentGenerator_surjective f U I)

/-- Coverage is required only on values actually attained by `f`. -/
theorem preimage_subset_coverSaturation (f : C(X, ℝ)) (U : ι → OpenInterval)
    (hcov : ∀ x, ∃ i, f x ∈ U i) (I : OpenInterval) :
    f ⁻¹' (I : Set ℝ) ⊆ f ⁻¹' (coverSaturation U I : Set ℝ) := by
  intro x hx
  obtain ⟨i, hi⟩ := hcov x
  exact mem_coverSaturation.mpr ⟨i, hi, f x, hi, hx⟩

/-- The comparison from a saturated inverse image to the thickened original inverse image. -/
def coverComponentsToOriginal (f : C(X, ℝ)) (U : ι → OpenInterval) (r : ℝ≥0)
    (hdiam : ∀ i x, x ∈ U i → ∀ y, y ∈ U i → |x - y| ≤ r) :
    coverComponents f U ⟶ (smoothing r).obj (intervalComponents f) where
  app I := (componentFunctor f).map (homOfLE (coverSaturation_le_thicken U r hdiam I))
  naturality I J h := by
    ext c
    induction c using ZerothHomotopy.rec with
    | mk x => rfl

/-- The reverse comparison is induced by the identity on points and attained-range coverage. -/
def originalToCoverComponents (f : C(X, ℝ)) (U : ι → OpenInterval) (r : ℝ≥0)
    (hcov : ∀ x, ∃ i, f x ∈ U i) :
    intervalComponents f ⟶ (smoothing r).obj (coverComponents f U) where
  app I := TypeCat.ofHom (componentMap (ContinuousMap.inclusion
    (s := f ⁻¹' (I : Set ℝ)) (t := f ⁻¹' (coverSaturation U (thicken r I) : Set ℝ))
    (fun x hx => preimage_subset_coverSaturation f U hcov (thicken r I)
      (le_thicken r I hx))))
  naturality I J h := by
    ext c
    induction c using ZerothHomotopy.rec with
    | mk x => rfl

/-- Explicit comparison interleaving, with both composites induced by interval inclusions. -/
def coverComponentsInterleaving (f : C(X, ℝ)) (U : ι → OpenInterval) (r : ℝ≥0)
    (hcov : ∀ x, ∃ i, f x ∈ U i)
    (hdiam : ∀ i x, x ∈ U i → ∀ y, y ∈ U i → |x - y| ≤ r) :
    Interleaving r (coverComponents f U) (intervalComponents f) :=
  Interleaving.ofApp (coverComponentsToOriginal f U r hdiam)
    (originalToCoverComponents f U r hcov)
    (fun I => by
      ext c
      induction c using ZerothHomotopy.rec with
      | mk x => rfl)
    (fun I => by
      ext c
      induction c using ZerothHomotopy.rec with
      | mk x => rfl)

/-- The component-of-union precosheaf has interleaving error at most the member diameter. -/
theorem interleavingDistance_coverComponents_le (f : C(X, ℝ)) (U : ι → OpenInterval)
    (r : ℝ≥0) (hcov : ∀ x, ∃ i, f x ∈ U i)
    (hdiam : ∀ i x, x ∈ U i → ∀ y, y ∈ U i → |x - y| ≤ r) :
    interleavingDistance (coverComponents f U) (intervalComponents f) ≤ (r : ℝ≥0∞) :=
  (coverComponentsInterleaving f U r hcov hdiam).interleavingDistance_le

end TDA.Mapper
