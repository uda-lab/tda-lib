import TDA.Filtration.FiniteGraded
import TDA.Persistence.Simplicial
import TDA.Persistence.RealCoordinates
import TDA.Simplicial.FiniteDimensionalHomology

set_option autoImplicit false

/-!
# Homology of finite coordinate-graded simplicial complexes

The module here is the existing inclusion-induced simplicial homology module of
the sublevel filtration. Its fibres are finite-dimensional over every coefficient
field, in every homological degree, as a consequence of the finite input.
-/

universe u

namespace TDA.Persistence

open CategoryTheory TDA.Simplicial TDA.Filtration
open scoped TDA.Persistence

variable {m n : ℕ} {C : FiniteComplex m}

/-- Actual inclusion-induced homology of the coordinate sublevel filtration. -/
noncomputable def finiteSimplicialHomology
    (k : Type u) [Ring k] (g : FiniteGraded C n) (q : ℕ) :
    PModule.{u,0,u} k (Fin n → ℝ) :=
  simplicialHomologyPModule k g.sublevelFiltration q

/-- Its value is the existing simplicial homology of the sublevel complex. -/
theorem finiteSimplicialHomology_obj
    (k : Type u) [Ring k] (g : FiniteGraded C n) (q : ℕ) (a : Fin n → ℝ) :
    (finiteSimplicialHomology k g q).obj a = simplicialHomology (g.sublevel a) k q := rfl

/-- The structure morphism is the actual map induced by subcomplex inclusion. -/
theorem finiteSimplicialHomology_structureMap
    (k : Type u) [Ring k] (g : FiniteGraded C n) (q : ℕ)
    {a b : Fin n → ℝ} (h : a ≤ b) :
    structureMap (finiteSimplicialHomology k g q) h =
      simplicialHomologyIncl k (g.sublevel_mono h) q := rfl

/-- Finite input implies finite-dimensional homology at every parameter. -/
noncomputable instance finiteSimplicialHomology_finiteDimensional
    (k : Type u) [Field k] (g : FiniteGraded C n) (q : ℕ) (a : Fin n → ℝ) :
    FiniteDimensional k ((finiteSimplicialHomology k g q).obj a) := by
  change FiniteDimensional k (simplicialHomology (g.sublevel a) k q)
  infer_instance

end TDA.Persistence
