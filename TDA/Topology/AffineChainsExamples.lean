import TDA.Topology.SubdivisionDiameter
import Mathlib.Algebra.Category.ModuleCat.Colimits

/-!
# Examples for affine chains and the subdivision diameter bound

The cone boundary formula on a segment, `∂(b · [p, q]) = [p, q] - [b, q] + [b, p]`, with
coefficients in any ring, and the diameter bound `2 / 3` for a simplex of the barycentric
subdivision of the standard `2`-simplex, in any norm.
-/

namespace TDA.Topology.AffineChainsExamples

open CategoryTheory Convexity Metric Set TDA.Topology.AffineChains

noncomputable section

universe u

/-- **Cone boundary on a segment**: `∂(b · [p, q]) = [p, q] - [b, q] + [b, p]` in the affine
chains with coefficients in a ring `k`. -/
theorem cone_boundary_segment {k X : Type u} [Ring k] (b p q : X) :
    (affineSSet.{u} X).ιChainComplex (R := ModuleCat.of k k) (affineSSet.mk ![p, q]) ≫
        coneMap.{u} (ModuleCat.of k k) b 1 ≫
          ((affineSSet.{u} X).chainComplex (ModuleCat.of k k)).d 2 1 =
      (affineSSet.{u} X).ιChainComplex (affineSSet.mk ![p, q]) -
        (affineSSet.{u} X).ιChainComplex (affineSSet.mk ![b, q]) +
        (affineSSet.{u} X).ιChainComplex (affineSSet.mk ![b, p]) := by
  rw [ιChainComplex_coneMap_d, Fin.sum_univ_two]
  have h₀ : cone b (![p, q] ∘ (0 : Fin 2).succAbove) = ![b, q] := by
    funext j
    fin_cases j <;> rfl
  have h₁ : cone b (![p, q] ∘ (1 : Fin 2).succAbove) = ![b, p] := by
    funext j
    fin_cases j <;> rfl
  rw [h₀, h₁]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_smul]
  abel

/-- The standard `2`-simplex as a convex subset of itself. -/
abbrev triangle : Set (StdSimplex ℝ (Fin 3)) := univ

lemma isConvexSet_triangle : IsConvexSet ℝ triangle := IsConvexSet.univ

/-- The vertices of the standard `2`-simplex. -/
def triangleVertex (i : Fin 3) : triangle := ⟨.single i, trivial⟩

/-- The simplex `(b_Δ, b_e, v)` of the barycentric subdivision of the standard `2`-simplex `Δ`,
where `e` is the facet opposite vertex `0` and `v` the vertex of `e` opposite vertex `1`. -/
def subdivisionTriangle : Fin 3 → triangle :=
  cone (simplexBarycenter isConvexSet_triangle triangleVertex)
    (cone (simplexBarycenter isConvexSet_triangle (triangleVertex ∘ (0 : Fin 3).succAbove))
      (triangleVertex ∘ (0 : Fin 3).succAbove ∘ (0 : Fin 2).succAbove))

theorem isSubdivisionSimplex_subdivisionTriangle :
    IsSubdivisionSimplex isConvexSet_triangle triangleVertex subdivisionTriangle :=
  .cone triangleVertex 0 (.cone _ 0 (.vertex _))

/-- **Diameter bound on a `2`-simplex**: in any norm, this simplex of the barycentric
subdivision has diameter at most `2 / 3` of that of the standard `2`-simplex. -/
theorem diam_subdivisionTriangle_le {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (L : (Fin 3 →₀ ℝ) →ₗ[ℝ] E) :
    diam (range (position L ∘ realize isConvexSet_triangle subdivisionTriangle)) ≤
      2 / 3 * diam (range (position L ∘ realize isConvexSet_triangle triangleVertex)) := by
  have h := isSubdivisionSimplex_subdivisionTriangle.diam_range_realize_le (L := L)
  norm_num at h
  exact h

/-- After `N` subdivisions, the factor for a `2`-simplex is `(2 / 3) ^ N`. -/
theorem diam_iterated_triangle_le {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (L : (Fin 3 →₀ ℝ) →ₗ[ℝ] E) {N : ℕ} {τ : Fin 3 → triangle}
    (h : IsIteratedSubdivisionSimplex isConvexSet_triangle N triangleVertex τ) :
    diam (range (position L ∘ realize isConvexSet_triangle τ)) ≤
      (2 / 3) ^ N * diam (range (position L ∘ realize isConvexSet_triangle triangleVertex)) := by
  have h' := h.diam_range_realize_le (L := L)
  norm_num at h'
  exact h'

end

end TDA.Topology.AffineChainsExamples
