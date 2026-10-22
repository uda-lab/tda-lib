import TDA.Persistence.FinitePMatchingCostBottleneck
import TDA.Persistence.FiniteFilterStability

/-!
# Finite-part boundary transport under filtration perturbations

The existing bottleneck stability theorem compares sublevel diagrams,
including across pairing changes. Its finite radius therefore controls the
finite-part real-plan optimum, with an explicit occurrence-count factor.
Essential bars may exist in the diagrams and remain outside this finite cost.
-/

universe u
namespace TDA.Persistence
open TDA.Filtration TDA.Simplicial

variable {V : Type u} [LinearOrder V]
variable {K : PreAbstractSimplicialComplex V} [Fintype (TotalFace K)]

/-- Finite-part real-p transport is bounded by the face-value perturbation
times the reciprocal-power occurrence-count factor, without a fixed pairing. -/
theorem finitePBoundaryTransportCost_dgm_le_card_rpow_mul_faceSupDifference
    {p : ℝ} (hp : 1 ≤ p) (k : Type u) [Field k]
    (f g : FilterFunction K ℝ) (n : ℕ) :
    finitePBoundaryTransportCost p (fun q : (dgm k f n).finiteOccurrences => q.1)
        (fun q : (dgm k g n).finiteOccurrences => q.1) ≤
      (((Fintype.card (dgm k f n).finiteOccurrences +
        Fintype.card (dgm k g n).finiteOccurrences : ℕ) : ℝ) ^ p⁻¹) *
        faceSupDifference f g :=
  finitePBoundaryTransportCost_le_card_rpow_mul_of_bottleneck_le hp _ _
    (faceSupDifference_nonneg f g) (bottleneck_dgm_le_faceSupDifference k f g n)

/-- An explicit cardinality budget gives a uniform filtration perturbation bound. -/
theorem finitePBoundaryTransportCost_dgm_le_cardBound_rpow_mul_faceSupDifference
    {p : ℝ} (hp : 1 ≤ p) (k : Type u) [Field k]
    (f g : FilterFunction K ℝ) (n : ℕ) {m : ℕ}
    (hcard : Fintype.card (dgm k f n).finiteOccurrences +
      Fintype.card (dgm k g n).finiteOccurrences ≤ m) :
    finitePBoundaryTransportCost p (fun q : (dgm k f n).finiteOccurrences => q.1)
        (fun q : (dgm k g n).finiteOccurrences => q.1) ≤
      (m : ℝ) ^ p⁻¹ * faceSupDifference f g :=
  finitePBoundaryTransportCost_le_cardBound_rpow_mul_of_bottleneck_le hp _ _ hcard
    (faceSupDifference_nonneg f g) (bottleneck_dgm_le_faceSupDifference k f g n)

end TDA.Persistence
