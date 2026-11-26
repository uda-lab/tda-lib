import TDA.Topology.SmallChainsQuasiIso
import TDA.Topology.SingularMayerVietorisExamples

/-!
# Examples for small chains of a cover

The open rays `(-∞, 1)` and `(0, ∞)` of `TDA.Topology.SingularMayerVietorisExamples` are open
and cover the real line, so their small chains compute the singular homology of the line, for
coefficients in any module, and the Mayer–Vietoris sequence of the two rays is exact. The
affine segment from `2` to `-1` is not small for the rays, but its iterated singular
subdivisions are small from some step on.

On the model `1`-simplex, the two open parts where the weight of vertex `0` is below `2/3`
and above `1/3` cover the simplex; from some `N` on, every simplex of the `N`-fold barycentric
subdivision of the identity `1`-simplex lies in one of them.
-/

namespace TDA.Topology.SmallChainsQuasiIsoExamples

open CategoryTheory Convexity Simplicial TDA.Topology.AffineChains
open TDA.Topology.SingularMayerVietorisExamples

noncomputable section

/-- The interiors of the two open rays cover the real line. -/
theorem interior_lowerRay_union_interior_upperRay :
    interior lowerRay ∪ interior upperRay = Set.univ := by
  have h₁ : IsOpen lowerRay := isOpen_Iio
  have h₂ : IsOpen upperRay := isOpen_Ioi
  rw [h₁.interior_eq, h₂.interior_eq]
  exact lowerRay_union_upperRay

/-- **The small chains of the two rays compute the singular homology of the line**, for
coefficients in any module. -/
theorem quasiIso_smallChainsι_rays {k : Type} [Ring k] (M : ModuleCat.{0} k) :
    QuasiIso (smallChainsι lowerRay upperRay M) :=
  quasiIso_smallChainsι lowerRay upperRay M interior_lowerRay_union_interior_upperRay

/-- The segment from `2` to `-1` is not small for the rays, but from some step on its iterated
singular subdivisions are small. -/
theorem segmentSimplex_not_small_and_eventually_small {k : Type} [Ring k]
    (M : ModuleCat.{0} k) :
    segmentSimplex ∉ (smallSimplices lowerRay upperRay).obj (Opposite.op ⦋1⦌) ∧
      ∃ N : ℕ, ∀ N' ≥ N, ∀ r : M,
        (⇑((singularSubdivision M lineSpace).f 1).hom)^[N']
            (((TopCat.toSSet.obj lineSpace).ιChainComplex (R := M) segmentSimplex).hom r) ∈
          LinearMap.range ((smallChainsι lowerRay upperRay M).f 1).hom :=
  ⟨segmentSimplex_not_mem_smallSimplices,
    exists_iterate_singularSubdivision_ιChainComplex_mem_range lowerRay upperRay M
      interior_lowerRay_union_interior_upperRay segmentSimplex⟩

/-- **The Mayer–Vietoris sequence of the two rays** is exact at the homology of their
intersection, at the homology of the two rays and at the homology of the line. -/
theorem mayerVietoris_exact_rays {k : Type} [Ring k] (M : ModuleCat.{0} k) (n : ℕ) :
    (ShortComplex.mk _ _ (mayerVietorisδ_comp_mayerVietorisInterMap lowerRay upperRay M
        interior_lowerRay_union_interior_upperRay n)).Exact ∧
      (ShortComplex.mk _ _
        (mayerVietorisInterMap_comp_mayerVietorisSumMap lowerRay upperRay M n)).Exact ∧
      (ShortComplex.mk _ _ (mayerVietorisSumMap_comp_mayerVietorisδ lowerRay upperRay M
        interior_lowerRay_union_interior_upperRay n)).Exact :=
  ⟨mayerVietoris_exact_inter _ _ M _ n, mayerVietoris_exact_sum _ _ M
    interior_lowerRay_union_interior_upperRay n, mayerVietoris_exact_space _ _ M _ n⟩

/-- The part of the model `1`-simplex where the weight of vertex `0` is below `2/3`. -/
def lowerPart : Set (modelSimplex 1) := {x | x.1.weights 0 < 2 / 3}

/-- The part of the model `1`-simplex where the weight of vertex `0` is above `1/3`. -/
def upperPart : Set (modelSimplex 1) := {x | 1 / 3 < x.1.weights 0}

/-- **A Lebesgue step on the `1`-simplex.** From some `N` on, every simplex of the `N`-fold
barycentric subdivision of the identity `1`-simplex lies in `lowerPart` or in `upperPart`. -/
theorem exists_isIteratedSubdivisionSimplex_one_subset :
    ∃ N : ℕ, ∀ N' ≥ N, ∀ τ : Fin 2 → modelSimplex 1,
      IsIteratedSubdivisionSimplex (isConvexSet_modelSimplex 1) N' (idSimplex 1) τ →
        Set.range (realize (isConvexSet_modelSimplex 1) τ) ⊆ lowerPart ∨
          Set.range (realize (isConvexSet_modelSimplex 1) τ) ⊆ upperPart := by
  have hw : Continuous fun x : modelSimplex 1 => x.1.weights 0 :=
    (StdSimplex.continuous_weights_apply ℝ (0 : Fin 2)).comp continuous_subtype_val
  have hopen : ∀ b : Bool, IsOpen (cond b lowerPart upperPart) := by
    intro b
    cases b
    · exact isOpen_lt continuous_const hw
    · exact isOpen_lt hw continuous_const
  have hcov : ⋃ b : Bool, cond b lowerPart upperPart = Set.univ := by
    refine Set.iUnion_eq_univ_iff.2 fun x => ?_
    by_cases hx : x.1.weights 0 < 2 / 3
    · exact ⟨true, hx⟩
    · refine ⟨false, ?_⟩
      change 1 / 3 < x.1.weights 0
      linarith [not_lt.1 hx]
  obtain ⟨N, hN⟩ := exists_isIteratedSubdivisionSimplex_subset hopen hcov
  refine ⟨N, fun N' hN' τ hτ => ?_⟩
  obtain ⟨b, hb⟩ := hN N' hN' τ hτ
  cases b
  · exact Or.inr hb
  · exact Or.inl hb

end

end TDA.Topology.SmallChainsQuasiIsoExamples
