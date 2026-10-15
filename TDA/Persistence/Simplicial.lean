import TDA.Simplicial.Homology
import TDA.Persistence.Basic

/-! Actual simplicial homology as a covariant persistence module. -/

universe u v w

namespace TDA.Persistence

open CategoryTheory TDA.Simplicial

variable {V : Type u} [LinearOrder V]
variable (R : Type v) [Ring R]
variable {P : Type w} [Preorder P]

noncomputable def simplicialHomologyPModule
    (F : Filtration.SimplicialFiltration P V) (n : ℕ) :
    PModule.{v,w,max u v} R P where
  obj p := simplicialHomology (F p) R n
  map f := simplicialHomologyIncl R (F.monotone (leOfHom f)) n
  map_id := by
    intro p
    simpa using simplicialHomologyIncl_id R (F p) n
  map_comp := by
    intro p q r f g
    simpa using
      (simplicialHomologyIncl_comp R (F.monotone (leOfHom f))
        (F.monotone (leOfHom g)) n)

theorem simplicialHomologyPModule_obj
    (F : Filtration.SimplicialFiltration P V) (n : ℕ) (p : P) :
    (simplicialHomologyPModule R F n).obj p = simplicialHomology (F p) R n := rfl

theorem simplicialHomologyPModule_structureMap
    (F : Filtration.SimplicialFiltration P V) (n : ℕ)
    {p q : P} (h : p ≤ q) :
    structureMap (simplicialHomologyPModule R F n) h =
      simplicialHomologyIncl R (F.monotone h) n := rfl

end TDA.Persistence
