import TDA.Persistence.Basic
import Mathlib.CategoryTheory.Linear.FunctorCategory
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Finite-dimensionality of morphism spaces

For a finite indexing preorder, natural transformations between pointwise
finite-dimensional persistence modules form a finite-dimensional vector
space. The proof records all component maps in a finite product; naturality
then makes that recording map injective.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence.FiniteHomDimension

open CategoryTheory

variable {k : Type u} [Field k] {S : Type} [Preorder S]

noncomputable section

/-- Record a persistence morphism by its component linear maps. -/
def componentMapPi (X Y : PModule.{u,0,u} k S) :
    (X ⟶ Y) →ₗ[k] ∀ p, X.obj p →ₗ[k] Y.obj p :=
  LinearMap.pi fun p =>
    (ModuleCat.homLinearEquiv (R := k) (S := k)).toLinearMap.comp
      (NatTrans.appLinearMap p)

/-- The component-map recording map is injective by natural-transformation
extensionality. -/
theorem componentMapPi_injective (X Y : PModule.{u,0,u} k S) :
    Function.Injective (componentMapPi (k := k) X Y) := by
  intro f g h
  apply NatTrans.ext
  funext p
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  have hp : (componentMapPi (k := k) X Y f) p =
      (componentMapPi (k := k) X Y g) p := congrFun h p
  have hx := congrArg (fun φ : X.obj p →ₗ[k] Y.obj p => φ x) hp
  simpa [componentMapPi] using hx

/-- A natural-transformation space is finite-dimensional when its index set
and all source and target fibers are finite-dimensional. -/
theorem finiteDimensional_hom [Fintype S]
    (X Y : PModule.{u,0,u} k S)
    (hX : ∀ p, FiniteDimensional k (X.obj p))
    (hY : ∀ p, FiniteDimensional k (Y.obj p)) :
    FiniteDimensional k (X ⟶ Y) := by
  haveI : ∀ p, FiniteDimensional k (X.obj p) := hX
  haveI : ∀ p, FiniteDimensional k (Y.obj p) := hY
  exact FiniteDimensional.of_injective (componentMapPi (k := k) X Y)
    (componentMapPi_injective (k := k) X Y)

end

end TDA.Persistence.FiniteHomDimension
