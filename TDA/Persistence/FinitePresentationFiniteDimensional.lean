import TDA.Persistence.FinitePresentation
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Finite-dimensional fibers of finitely presented modules

Over a field, every fiber of a finitely presented persistence module is finite-dimensional.
The proof uses the finite free cover at each index and transports finite-dimensionality
across the presentation isomorphism.
-/

set_option autoImplicit false

universe u v w

namespace TDA.Persistence

namespace GradedFree

variable {k : Type u} [Field k] {P : Type v} [Preorder P]

/-- A graded free module on finitely many generators has finite-dimensional fibers. -/
theorem finiteDimensional_fiber (W : GradedGenerators.{v,w} P)
    [Finite W.Carrier] (a : P) :
    FiniteDimensional k ((module (R := k) W).obj a) := by
  change FiniteDimensional k (fiber (R := k) W a)
  infer_instance

namespace Presentation

/-- A presentation with finitely many generators has finite-dimensional fibers.
Finiteness of the relation family is not needed for this conclusion. -/
theorem finiteDimensional_of_finite_generators
    (D : GradedFree.Presentation.{u,v,w} (R := k) (P := P))
    (hW : Finite D.generators.Carrier) (a : P) :
    FiniteDimensional k (D.presented.obj a) := by
  letI : Finite D.generators.Carrier := hW
  haveI : FiniteDimensional k ((module (R := k) D.generators).obj a) :=
    finiteDimensional_fiber D.generators a
  apply FiniteDimensional.of_surjective (D.cover.app a).hom
  exact D.cover_surjective a

end Presentation

/-- Every fiber of a finitely presented persistence module over a field is
finite-dimensional. -/
theorem finitelyPresented_finiteDimensional
    (M : PModule.{u,v,max u w} k P)
    (hM : FinitelyPresented (R := k) (P := P) M) (a : P) :
    FiniteDimensional k (M.obj a) := by
  classical
  obtain ⟨D, hD, ⟨e⟩⟩ := hM
  letI : FiniteDimensional k (D.presented.obj a) :=
    D.finiteDimensional_of_finite_generators hD.1 a
  exact (e.app a).toLinearEquiv.finiteDimensional

end GradedFree

end TDA.Persistence
