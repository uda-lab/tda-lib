import TDA.Persistence.RankExactPushout

/-!
# A nonzero pushout of a split rank-exact sequence

This example starts with the identity quotient of a one-dimensional persistence
module and pushes its zero submodule out to another copy of that module. The
resulting middle module is nonzero and has the rank-exact canonical row.
-/

set_option autoImplicit false

namespace TDA.Persistence.RankExactPushoutExamples

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

private def constantLine : PModule.{0,0,0} ℚ (Fin 2) where
  obj _ := ModuleCat.of ℚ ℚ
  map _ := 𝟙 _
  map_id _ := by simp
  map_comp _ _ := by simp

private instance constantLine_finiteDimensional (p : Fin 2) :
    FiniteDimensional ℚ (constantLine.obj p) := by
  change FiniteDimensional ℚ ℚ
  infer_instance

private theorem identityQuotient :
    IsRankExact (0 : (0 : PModule.{0,0,0} ℚ (Fin 2)) ⟶ constantLine)
      (𝟙 constantLine) := by
  have hs : IsPointwiseShortExact
      (0 : (0 : PModule.{0,0,0} ℚ (Fin 2)) ⟶ constantLine) (𝟙 constantLine) := by
    constructor
    · intro p x y _
      exact (ModuleCat.subsingleton_of_isZero (Functor.zero_obj p)).elim _ _
    · intro p n
      exact ⟨n, rfl⟩
    · intro p
      simp
  exact hs.rankExact_of_section (𝟙 constantLine) (by simp)

private noncomputable abbrev zeroModule : PModule.{0,0,0} ℚ (Fin 2) := 0

private noncomputable abbrev zeroToLine : zeroModule ⟶ constantLine := 0

/-- The canonical row from the actual pushout is rank exact. -/
theorem pushed_row_rankExact :
    IsRankExact (Limits.pushout.inr zeroToLine zeroToLine)
      (identityQuotient.toIsPointwiseShortExact.pushoutQuotient zeroToLine) := by
  letI : ∀ p : Fin 2, FiniteDimensional ℚ (constantLine.obj p) := fun _ => inferInstance
  exact identityQuotient.pushout zeroToLine

/-- The pushout middle fiber contains the image of a nonzero vector. -/
theorem pushed_middle_nontrivial :
    ∃ x : (Limits.pushout zeroToLine zeroToLine).obj 0, x ≠ 0 := by
  have hnontrivial : Nontrivial (constantLine.obj (0 : Fin 2)) := by
    change Nontrivial ℚ
    infer_instance
  letI := hnontrivial
  obtain ⟨v, hv⟩ := exists_ne (0 : constantLine.obj (0 : Fin 2))
  refine ⟨((Limits.pushout.inr zeroToLine zeroToLine).app 0).hom v, ?_⟩
  intro hx
  have hx' : ((Limits.pushout.inr zeroToLine zeroToLine).app 0).hom v =
      ((Limits.pushout.inr zeroToLine zeroToLine).app 0).hom 0 := by
    rw [map_zero]
    exact hx
  exact hv ((pushed_row_rankExact.toIsPointwiseShortExact.injective 0 hx'))

end TDA.Persistence.RankExactPushoutExamples
