import TDA.Persistence.GeneratedUpsetResolution

/-!
# Examples for join-indexed upset resolutions

These fixtures specialize the general resolution to a singleton, repeated labels, a
three-generator family, and the empty family.
-/

set_option autoImplicit false

namespace TDA.Persistence.GeneratedUpsetResolution.Examples

open TDA.Persistence.GeneratedUpsetResolution
open CategoryTheory
open CategoryTheory.Limits

abbrev singletonFamily : Fin 1 → ℕ := fun _ => 2

/-- The singleton-family augmentation is onto at every index. -/
theorem singleton_augmentation_surjective (p : ℕ) :
    Function.Surjective ((augmentation (k := ℚ) singletonFamily).app p).hom :=
  augmentation_surjective_at (k := ℚ) singletonFamily p

/-- The degree-zero kernel for one generator is filled by the next term. -/
theorem singleton_exact_at_zero (p : ℕ)
    (x : (term (k := ℚ) singletonFamily 0).obj p)
    (hx : ((augmentation (k := ℚ) singletonFamily).app p).hom x = 0) :
    ∃ y : (term (k := ℚ) singletonFamily 1).obj p,
      ((differential (k := ℚ) singletonFamily 0).app p).hom y = x :=
  augmentation_exact_at_zero (k := ℚ) singletonFamily p x hx

abbrev repeatedFamily : Fin 2 → ℕ := fun _ => 1

def repeatedFaceZero : FaceIndex 2 0 := singletonFaceIndex (0 : Fin 2)
def repeatedFaceOne : FaceIndex 2 0 := singletonFaceIndex (1 : Fin 2)

/-- Equal generator values still give separate degree-zero summands. -/
theorem repeated_occurrences_are_distinct :
    repeatedFaceZero ≠ repeatedFaceOne := by
  intro h
  have hsets := congrArg Subtype.val h
  norm_num [repeatedFaceZero, repeatedFaceOne, singletonFaceIndex] at hsets

/-- At the common birth, the two equal-valued occurrences remain distinct active vertices. -/
theorem repeated_active_faces_are_distinct :
    activeFaceEquiv repeatedFamily 1
      ⟨repeatedFaceZero, by simp [repeatedFamily, repeatedFaceZero,
        faceJoin_singleton]⟩ ≠
    activeFaceEquiv repeatedFamily 1
      ⟨repeatedFaceOne, by simp [repeatedFamily, repeatedFaceOne,
        faceJoin_singleton]⟩ := by
  intro h
  apply repeated_occurrences_are_distinct
  exact congrArg Subtype.val ((activeFaceEquiv repeatedFamily 1).injective h)

abbrev threeFamily : Fin 3 → ℕ := fun i => i.val

/-- A cycle in the nontrivial three-generator fiber is a boundary in the actual resolution. -/
theorem three_generator_cycle_is_boundary
    (x : (term (k := ℚ) threeFamily 1).obj 2)
    (hx : ((differential (k := ℚ) threeFamily 0).app 2).hom x = 0) :
    ∃ y : (term (k := ℚ) threeFamily 2).obj 2,
      ((differential (k := ℚ) threeFamily 1).app 2).hom y = x :=
  differential_exact_at_succ (k := ℚ) threeFamily 2 0 x hx

abbrev emptyFamily : Fin 0 → ℕ := fun i => Fin.elim0 i

/-- The empty family has empty support, zero support module, and zero face-sum fibers. -/
theorem empty_family_boundary :
    generatedSupport emptyFamily = ∅ ∧
      IsZero (SupportInterval.module (k := ℚ)
        (generatedSupport emptyFamily)
        (generatedSupport_ordConnected emptyFamily)) ∧
      ∀ r (p : ℕ) (x : (term (k := ℚ) emptyFamily r).obj p), x = 0 := by
  refine ⟨generatedSupport_fin_zero _, generatedSupport_fin_zero_module_isZero _, ?_⟩
  intro r p x
  exact term_fin_zero_eq_zero (k := ℚ) _ r p x

end TDA.Persistence.GeneratedUpsetResolution.Examples
