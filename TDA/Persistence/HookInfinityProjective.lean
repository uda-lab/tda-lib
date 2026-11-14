import TDA.Persistence.HookInfinity
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.EpiMono
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import Mathlib.CategoryTheory.Preadditive.Projective.Basic

/-!
# Ordinary projectivity of principal-upset modules

For a ring and a preorder, the principal-upset module is projective in the
ordinary categorical sense: every map from it factors through each categorical
epimorphism. Such an epimorphism is epi at the birth grade, hence surjective as
a module map there; `HookInfinity.exists_lift_of_birth_surjective` constructs
the required factorization. Import this module to use the canonical instance.
-/

set_option autoImplicit false

universe u v

namespace TDA.Persistence.HookInfinity

open CategoryTheory

variable {R : Type u} [Ring R] {P : Type v} [Preorder P]

/-- Principal-upset modules are ordinary projective objects. -/
instance projective (i : P) : Projective (module (R := R) i) where
  factors {E X} α e _ := by
    have hcomponent : Epi (e.app i) :=
      (NatTrans.epi_iff_epi_app e).mp inferInstance i
    have hsurj : Function.Surjective (e.app i).hom :=
      (ModuleCat.epi_iff_surjective (e.app i)).mp hcomponent
    exact exists_lift_of_birth_surjective e hsurj α

end TDA.Persistence.HookInfinity
