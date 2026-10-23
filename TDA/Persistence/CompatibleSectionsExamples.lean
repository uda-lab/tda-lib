import TDA.Persistence.CompatibleSections

/-!
# Compatible sections with nonidentity transition maps

These examples use rational one-dimensional fibers. A change of sign at zero gives
invertible transition maps that are not all identities. Prescribed nonzero vectors
lift on open, closed, unbounded, and singleton real subsets.
-/

namespace TDA.Persistence.CompatibleSectionsExamples

open CategoryTheory CompatibleSections

private noncomputable def signFrame (t : ℝ) : ℚ ≃ₗ[ℚ] ℚ :=
  if t ≤ 0 then LinearEquiv.refl ℚ ℚ else LinearEquiv.neg ℚ

/-- Rational scalar fibers, with a sign change when crossing zero. -/
noncomputable def signChangeModule (I : Set ℝ) : PModule.{0,0,0} ℚ I where
  obj _ := ModuleCat.of ℚ ℚ
  map {s t} _ := ModuleCat.ofHom ((signFrame t.val).toLinearMap.comp
    (signFrame s.val).symm.toLinearMap)
  map_id t := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact (signFrame t.val).apply_symm_apply x
  map_comp {s t r} _ _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change signFrame r.val ((signFrame s.val).symm x) =
      signFrame r.val ((signFrame t.val).symm (signFrame t.val ((signFrame s.val).symm x)))
    rw [LinearEquiv.symm_apply_apply]

/-- Every transition in the sign-change system is surjective. -/
theorem signChangeModule_surjective (I : Set ℝ) (s t : I) (h : s ≤ t) :
    Function.Surjective (structureMapLinear (signChangeModule I) h) :=
  ((signFrame s.val).symm.trans (signFrame t.val)).surjective

/-- The surjective lift theorem supplies a section through a nonzero rational vector. -/
theorem exists_prescribed_section (I : Set ℝ) (t : I) :
    ∃ x : sections (signChangeModule I), x.val t = (1 : ℚ) :=
  evaluation_surjective_real (signChangeModule I) (signChangeModule_surjective I) t (1 : ℚ)

/-- The left-unbounded open interval admits a section through the value one at zero. -/
theorem exists_section_open_left_tail :
    ∃ x : sections (signChangeModule (Set.Iio 1)), x.val ⟨0, by norm_num⟩ = (1 : ℚ) :=
  exists_prescribed_section _ _

/-- Closed endpoints also admit the prescribed lift. -/
theorem exists_section_closed_interval :
    ∃ x : sections (signChangeModule (Set.Icc (-1) 1)), x.val ⟨0, by norm_num⟩ = (1 : ℚ) :=
  exists_prescribed_section _ _

/-- A singleton index set preserves the prescribed nonzero vector. -/
theorem exists_section_singleton :
    ∃ x : sections (signChangeModule {0}), x.val ⟨0, rfl⟩ = (1 : ℚ) :=
  exists_prescribed_section _ _

/-- The example includes a transition sending one to minus one. -/
theorem crossing_zero_map_one :
    structureMapLinear (signChangeModule Set.univ)
      (show (⟨-1, Set.mem_univ _⟩ : (Set.univ : Set ℝ)) ≤ ⟨1, Set.mem_univ _⟩ by norm_num)
      (1 : ℚ) = (-1 : ℚ) := by
  change signFrame 1 ((signFrame (-1)).symm (1 : ℚ)) = -1
  norm_num [signFrame]

end TDA.Persistence.CompatibleSectionsExamples
