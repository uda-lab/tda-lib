import TDA.Mapper.CoverComponents

/-!
# Removing members with empty inverse image

Empty pullbacks contribute no components to categorical Mapper. Their removal preserves the
assembled interval functor by the natural comparison induced by the identity on input points.
The geometric error may therefore use the full widths of retained members only.
-/

open Set CategoryTheory

universe u v

namespace TDA.Mapper

open TDA.Reeb TDA.Reeb.OpenInterval

variable {X : Type u} [TopologicalSpace X] {ι : Type v}

/-- The original labels of cover members whose inverse images are nonempty. -/
abbrev RetainedCoverMember (f : C(X, ℝ)) (U : ι → OpenInterval) :=
  {i : ι // (f ⁻¹' (U i : Set ℝ)).Nonempty}

/-- The retained interval family, without clipping any interval to the attained range. -/
def retainedCover (f : C(X, ℝ)) (U : ι → OpenInterval) :
    RetainedCoverMember f U → OpenInterval := fun i => U i.val

/-- Retained saturation is included in the original saturation. -/
theorem retainedCoverSaturation_le (f : C(X, ℝ)) (U : ι → OpenInterval)
    (I : OpenInterval) : coverSaturation (retainedCover f U) I ≤ coverSaturation U I := by
  intro y hy
  obtain ⟨i, hyi, z, hzi, hzI⟩ := mem_coverSaturation.mp hy
  exact mem_coverSaturation.mpr ⟨i.val, hyi, z, hzi, hzI⟩

/-- Original and retained saturation have exactly the same inverse image. -/
theorem preimage_coverSaturation_eq_retained (f : C(X, ℝ)) (U : ι → OpenInterval)
    (I : OpenInterval) :
    f ⁻¹' (coverSaturation U I : Set ℝ) =
      f ⁻¹' (coverSaturation (retainedCover f U) I : Set ℝ) := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, hxi, z, hzi, hzI⟩ := mem_coverSaturation.mp hx
    exact mem_coverSaturation.mpr ⟨⟨i, x, hxi⟩, hxi, z, hzi, hzI⟩
  · intro hx
    exact retainedCoverSaturation_le f U I hx

/-- Removing empty pullbacks preserves the assembly by a natural component isomorphism. -/
def coverComponentsRetainedIso (f : C(X, ℝ)) (U : ι → OpenInterval) :
    coverComponents f U ≅ coverComponents f (retainedCover f U) :=
  NatIso.ofComponents (fun I =>
    { hom := TypeCat.ofHom (componentMap (ContinuousMap.inclusion
        (preimage_coverSaturation_eq_retained f U I).le))
      inv := (componentFunctor f).map (homOfLE (retainedCoverSaturation_le f U I))
      hom_inv_id := by
        ext c
        induction c using ZerothHomotopy.rec with
        | mk x => rfl
      inv_hom_id := by
        ext c
        induction c using ZerothHomotopy.rec with
        | mk x => rfl }) (fun h => by
    ext c
    induction c using ZerothHomotopy.rec with
    | mk x => rfl)

/-- Attained-range coverage passes to the retained family. -/
theorem retainedCover_covers (f : C(X, ℝ)) (U : ι → OpenInterval)
    (hcov : ∀ x, ∃ i, f x ∈ U i) (x : X) : ∃ i, f x ∈ retainedCover f U i := by
  obtain ⟨i, hi⟩ := hcov x
  exact ⟨⟨i, x, hi⟩, hi⟩

end TDA.Mapper
