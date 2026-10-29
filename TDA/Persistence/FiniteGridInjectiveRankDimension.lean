import TDA.Persistence.FiniteLatticeComplementCardinality
import TDA.Persistence.FiniteInjectiveRankDimension
import TDA.Persistence.FiniteRankProjectiveHomDimension
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects

/-!
# Injective Hom dimension on finite coordinate grids

The proved complement count for a finite coordinate grid gives the numerical
bound for the existing Hom functor on every pointwise finite-dimensional
ordinary injective. The conclusion is the grid bound `n - 1`; no projective
dimension bound is supplied as input, and the coefficient field is arbitrary.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence.FiniteGridInjectiveRankDimension

open CategoryTheory CategoryTheory.Limits
open TDA.Persistence.FiniteInjectiveRankDimension
open TDA.Persistence.FiniteRankProjectiveHomDimension
open TDA.Persistence.FiniteRankProjectiveHomExact

variable {k : Type u} [Field k] {n : ℕ} (G : CoordinateGrid n)

noncomputable section

/-- The actual hook-Hom functor used for the finite grid. -/
private abbrev gridHomFunctor := homFunctor (k := k) (S := G.Point)

/-- Every pointwise finite-dimensional ordinary injective on a nonempty-factor
coordinate grid has the numerical Hom projective-dimension bound `n - 1`. -/
theorem hasProjectiveDimensionLE_of_coordinateGrid
    (M : PModule.{u,0,u} k G.Point)
    [∀ p, FiniteDimensional k (M.obj p)] [Injective M]
    (hG : ∀ i : Fin n, (G i).Nonempty) :
    letI : BoundedOrder G.Point :=
      FiniteLatticeComplementCardinality.coordinateGridBoundedOrder G hG
    HasProjectiveDimensionLE (gridHomFunctor (k := k) G |>.obj M) (n - 1) := by
  letI : BoundedOrder G.Point :=
    FiniteLatticeComplementCardinality.coordinateGridBoundedOrder G hG
  have hgrid : maxComplementCard (S := G.Point) ≤ n :=
    FiniteLatticeComplementCardinality.maxComplementCard_coordinateGrid_le G hG
  apply FiniteInjectiveRankDimension.hasProjectiveDimensionLE
  intro p
  exact Nat.sub_le_sub_right
    ((FiniteInjectiveRankDimension.complementCard_le_maxComplementCard
      (S := G.Point) p).trans hgrid) 1

/-- Every supplied minimal rank-projective resolution of such an ordinary
injective vanishes above the same grid bound. -/
theorem termAt_isZero_of_coordinateGrid
    (M : PModule.{u,0,u} k G.Point)
    [∀ p, FiniteDimensional k (M.obj p)] [Injective M]
    (hG : ∀ i : Fin n, (G i).Nonempty)
    (R : MinimalFiniteRankProjectiveResolution (k := k) (M := M))
    (j : ℕ) (hj : n - 1 < j) : IsZero (R.termAt j) := by
  letI : BoundedOrder G.Point :=
    FiniteLatticeComplementCardinality.coordinateGridBoundedOrder G hG
  have hdim := hasProjectiveDimensionLE_of_coordinateGrid
    (k := k) G M hG
  exact (FiniteRankProjectiveHomDimension.hasProjectiveDimensionLE_iff
    (k := k) (S := G.Point) R (n - 1)).mp hdim j hj

end

end TDA.Persistence.FiniteGridInjectiveRankDimension
