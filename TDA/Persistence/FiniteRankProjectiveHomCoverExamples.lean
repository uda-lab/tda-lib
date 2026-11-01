import TDA.Persistence.FiniteRankProjectiveHomCover

/-!
# Finite-rank projective Hom-cover examples

These examples check the zero and nonzero principal-upset identity covers for
the actual hook-generator Hom modules.
-/

set_option autoImplicit false

namespace TDA.Persistence.FiniteRankProjectiveHomCover.Examples

open CategoryTheory CategoryTheory.Limits
open TDA.Persistence.FiniteRankProjectiveHomExact
open scoped ZeroObject

private noncomputable abbrev QF :=
  TDA.Persistence.FiniteRankProjectiveHomExact.homFunctor (k := ℚ) (S := Fin 2)
private abbrev QE :=
  TDA.Persistence.FiniteRankProjectiveHomExact.HomScalars (k := ℚ) (S := Fin 2)
private noncomputable abbrev QL :=
  TDA.Persistence.FiniteRankProjectiveEndAlgebra.HookSum (k := ℚ) (S := Fin 2)

/-- The zero identity cover satisfies the ordinary Hom cover conditions. -/
theorem zero_identity_homCover :
    Module.Projective QE (QL ⟶ (0 : PModule ℚ (Fin 2))) ∧
    Function.Surjective (postcompose (k := ℚ) (S := Fin 2)
      (𝟙 (0 : PModule ℚ (Fin 2)))) ∧
    (∀ T : End (QF.obj (0 : PModule ℚ (Fin 2))),
      T ≫ QF.map (𝟙 (0 : PModule ℚ (Fin 2))) =
        QF.map (𝟙 (0 : PModule ℚ (Fin 2))) → IsIso T) := by
  let hfd : ∀ a, FiniteDimensional ℚ ((0 : PModule ℚ (Fin 2)).obj a) := by
    intro a
    letI : Subsingleton ((0 : PModule ℚ (Fin 2)).obj a) :=
      ModuleCat.subsingleton_of_isZero (Functor.zero_obj a)
    infer_instance
  exact (rankProjectiveCover_iff (k := ℚ) (S := Fin 2)
    (𝟙 (0 : PModule ℚ (Fin 2))) hfd).mp
    (IsRankProjectiveCover.of_identity (k := ℚ) (P := Fin 2)
      (M := (0 : PModule ℚ (Fin 2))) hfd
      (hM := by
        intro L A B ι π hs α
        refine ⟨0, ?_⟩
        exact Subsingleton.elim _ _))

/-- The nonzero principal upset identity cover satisfies the ordinary Hom
conditions, and its birth fiber has a nonzero vector. -/
theorem principalUpset_identity_homCover (a : Fin 2) :
    (Module.Projective QE (QL ⟶ HookInfinity.module (R := ℚ) a) ∧
    Function.Surjective (postcompose (k := ℚ) (S := Fin 2)
      (𝟙 (HookInfinity.module (R := ℚ) a))) ∧
    (∀ T : End (QF.obj (HookInfinity.module (R := ℚ) a)),
      T ≫ QF.map (𝟙 (HookInfinity.module (R := ℚ) a)) =
        QF.map (𝟙 (HookInfinity.module (R := ℚ) a)) → IsIso T)) ∧
    ∃ x : (HookInfinity.module (R := ℚ) a).obj a, x ≠ 0 := by
  let hfd : ∀ p, FiniteDimensional ℚ ((HookInfinity.module (R := ℚ) a).obj p) := by
    intro p
    infer_instance
  constructor
  · exact (rankProjectiveCover_iff (k := ℚ) (S := Fin 2)
      (𝟙 (HookInfinity.module (R := ℚ) a)) hfd).mp
      (IsRankProjectiveCover.of_identity (k := ℚ) (P := Fin 2)
        (M := HookInfinity.module (R := ℚ) a) hfd
        (HookInfinity.isRankProjective a))
  · let e := HookInfinity.fiberEquivOfLe (R := ℚ) (i := a) (a := a) le_rfl
    refine ⟨e.symm 1, ?_⟩
    intro hx
    have hone := congrArg e hx
    exact (one_ne_zero : (1 : ℚ) ≠ 0) (by simpa using hone)

end TDA.Persistence.FiniteRankProjectiveHomCover.Examples
