import TDA.Persistence.RealInterleavingLaws
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Finite-dimensional images of persistence maps

A real persistence module is q-tame when every structure map across a strict
inequality has finite-dimensional image. This condition allows individual fibers
to be infinite-dimensional. A factorization through a finite-dimensional fiber
of an interleaved module proves the required finiteness.
-/

universe u v w z

namespace TDA.Persistence

open CategoryTheory
open scoped NNReal

variable {k : Type u} [Field k]

/-- A linear map factoring through a finite-dimensional space has finite-dimensional image. -/
theorem finiteDimensional_range_of_factorization
    {U : Type v} {V : Type w} {W : Type z}
    [AddCommGroup U] [Module k U] [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] [FiniteDimensional k V]
    (f : U →ₗ[k] W) (g : U →ₗ[k] V) (h : V →ₗ[k] W)
    (hf : f = h.comp g) : FiniteDimensional k (LinearMap.range f) := by
  rw [hf]
  exact Submodule.finiteDimensional_of_le (LinearMap.range_comp_le_range g h)

namespace PModule

/-- Every strict forward structure map has finite-dimensional image over the coefficient field. -/
def QTame (M : PModule.{u,0,w} k ℝ) : Prop :=
  ∀ (a b : ℝ) (hab : a < b),
    FiniteDimensional k (LinearMap.range (structureMapLinear M hab.le))

/-- Finite-dimensional fibers imply q-tameness. -/
theorem qTame_of_finiteDimensional (M : PModule.{u,0,w} k ℝ)
    (hM : ∀ t, FiniteDimensional k (M.obj t)) : M.QTame := by
  intro a b hab
  let := hM a
  exact LinearMap.finiteDimensional_range _

end PModule

namespace RealInterleaving

variable {ε : ℝ≥0} {M N : PModule.{u,0,w} k ℝ}

/-- The interleaving equation factors the double-shift structure map through the middle fiber. -/
theorem finiteDimensional_range_structureMap (i : RealInterleaving ε M N) (a : ℝ)
    [FiniteDimensional k (N.obj (a + (ε : ℝ)))] :
    FiniteDimensional k (LinearMap.range (structureMapLinear M
      (show a ≤ (a + (ε : ℝ)) + (ε : ℝ) from
        (le_add_of_nonneg_right ε.coe_nonneg).trans
          (le_add_of_nonneg_right ε.coe_nonneg)))) := by
  let f : M.obj a →ₗ[k] N.obj (a + (ε : ℝ)) := (i.φ.app a).hom
  let g : N.obj (a + (ε : ℝ)) →ₗ[k] M.obj ((a + (ε : ℝ)) + (ε : ℝ)) :=
    (i.ψ.app (a + (ε : ℝ))).hom
  apply finiteDimensional_range_of_factorization _ f g
  exact congrArg ModuleCat.Hom.hom (i.φ_ψ_structureMap a).symm

end RealInterleaving

end TDA.Persistence
