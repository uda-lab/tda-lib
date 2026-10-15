import TDA.Simplicial.Homology
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

universe u v
namespace TDA.Simplicial
open CategoryTheory
variable {V : Type u} [LinearOrder V]

noncomputable instance simplicialHomology_finiteDimensional
    (K : PreAbstractSimplicialComplex V) (k : Type v) [Field k]
    (n : ℕ) [Finite (Face K n)] :
    FiniteDimensional k (simplicialHomology K k n) := by
  letI : FiniteDimensional k (Chain K k n) := finiteDimensional_finsupp
  letI : HasQuotient (simplicialCycles K k n)
      (Submodule k (simplicialCycles K k n)) :=
    Submodule.hasQuotient (R := k) (M := simplicialCycles K k n)
  letI : FiniteDimensional k (simplicialCycles K k n) := inferInstance
  letI : FiniteDimensional k
      (simplicialCycles K k n ⧸ simplicialBoundaries K k n) := inferInstance
  letI : FiniteDimensional k
      (↑(ModuleCat.of k (LinearMap.ker
        ((simplicialChainComplex K k).sc n).g.hom ⧸
        LinearMap.range ((simplicialChainComplex K k).sc n).moduleCatToCycles))) := by
    change FiniteDimensional k
      (simplicialCycles K k n ⧸ simplicialBoundaries K k n)
    infer_instance
  exact ((homologyKernelQuotient.{v,u,v} k
    (simplicialChainComplex K k) n).toLinearEquiv.symm).finiteDimensional

end TDA.Simplicial

-- Consumer regression: the degree-n face premise alone synthesizes the instance
-- with independent vertex and coefficient universes.
example {V : Type u} [LinearOrder V] (K : PreAbstractSimplicialComplex V)
    (k : Type v) [Field k] (n : ℕ) [Finite (TDA.Simplicial.Face K n)] :
    FiniteDimensional k (TDA.Simplicial.simplicialHomology K k n) := by
  infer_instance
