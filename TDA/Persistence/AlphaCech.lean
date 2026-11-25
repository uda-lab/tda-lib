import TDA.Persistence.AlphaH0
import TDA.Topology.ConvexNerveInclusion

set_option autoImplicit false

/-!
# Euclidean α–Čech persistence

At nonnegative squared grades, the compact convex restricted balls and ambient balls cover
the same union. Their labelled nerve inclusion therefore induces an isomorphism. Below zero
both stages are empty. These are the components of the existing filtration inclusion.
-/

namespace TDA.Persistence

open CategoryTheory TDA.Filtration TDA.Simplicial TDA.Topology

variable {V E : Type*} [LinearOrder V] [Finite V]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable (sites : V → E) (R : Type*) [Ring R] (n : ℕ)

/-- At nonnegative squared grades the actual inclusion of the restricted-ball nerve
in the ambient Čech complex induces an isomorphism over any ring. -/
theorem isIso_alphaIncl_cech {t : ℝ} (ht : 0 ≤ t) :
    IsIso (simplicialHomologyIncl R (K := Alpha.labelledComplex sites t)
      (L := Cech.complex sites (Real.sqrt t))
      (nerve_mono (Alpha.restrictedBall_subset_closedBall sites t)) n) :=
  ConvexNerve.isIso_simplicialHomologyIncl_of_compact
    (Alpha.isCompact_restrictedBall sites t) (fun _ => isCompact_closedBall _ _)
    (Alpha.convex_restrictedBall sites ht) (fun _ => convex_closedBall _ _)
    (Alpha.restrictedBall_subset_closedBall sites t) (Alpha.iUnion_restrictedBall sites ht) R n

/-- For embedded sites the same result applies to the original α-to-Čech filtration map. -/
theorem isIso_alpha_filtration_le_cech (p : V ↪ E) {t : ℝ} (ht : 0 ≤ t) :
    IsIso (simplicialHomologyIncl R (Alpha.filtration_le_cech p t) n) :=
  isIso_alphaIncl_cech p R n ht

/-- Each component of the persistence comparison is invertible, including at negative grades. -/
theorem isIso_alphaCechComparison_app (t : ℝ) :
    IsIso ((inclusionHom R n (Alpha.labelledComplexFiltration_le_squaredCech sites)).app t) := by
  by_cases ht : t < 0
  · apply simplicialHomologyIncl_isIso_of_eq
    exact (Alpha.labelledComplex_eq_bot_of_neg sites ht).trans
      (Alpha.squaredCechFiltration_apply_of_neg sites ht).symm
  have hnonneg := le_of_not_gt ht
  suffices ∀ i : Alpha.labelledComplex sites t ≤ Alpha.squaredCechFiltration sites t,
      IsIso (simplicialHomologyIncl R i n) from this _
  rw [Alpha.squaredCechFiltration_apply_of_nonneg sites hnonneg]
  exact fun _ => isIso_alphaIncl_cech sites R n hnonneg

/-- The inclusion-induced natural isomorphism of squared-grade α and Čech persistence. -/
noncomputable def alphaCechIso :
    simplicialHomologyPModule R (Alpha.labelledComplexFiltration sites) n ≅
      simplicialHomologyPModule R (Alpha.squaredCechFiltration sites) n := by
  let : ∀ t, IsIso ((inclusionHom R n (Alpha.labelledComplexFiltration_le_squaredCech sites)).app t) :=
    isIso_alphaCechComparison_app sites R n
  let := NatIso.isIso_of_isIso_app (inclusionHom R n (Alpha.labelledComplexFiltration_le_squaredCech sites))
  exact asIso (inclusionHom R n (Alpha.labelledComplexFiltration_le_squaredCech sites))

/-- The forward morphism is induced by the same-label filtration inclusion. -/
@[simp] theorem alphaCechIso_hom :
    (alphaCechIso sites R n).hom = inclusionHom R n (Alpha.labelledComplexFiltration_le_squaredCech sites) := rfl

/-- At each grade the forward component is the canonical simplicial homology inclusion. -/
theorem alphaCechIso_hom_app (t : ℝ) :
    (alphaCechIso sites R n).hom.app t =
      simplicialHomologyIncl R (Alpha.labelledComplexFiltration_le_squaredCech sites t) n := rfl

/-- The actual horizontal and vertical homology maps commute across any two squared grades. -/
theorem alphaCechIso_naturality {s t : ℝ} (hst : s ≤ t) :
    simplicialHomologyIncl R ((Alpha.labelledComplexFiltration sites).monotone hst) n ≫
        (alphaCechIso sites R n).hom.app t =
      (alphaCechIso sites R n).hom.app s ≫
        simplicialHomologyIncl R ((Alpha.squaredCechFiltration sites).monotone hst) n :=
  (alphaCechIso sites R n).hom.naturality (homOfLE hst)

/-- On Euclidean sites, degree zero recovers the existing H₀ isomorphism over a field. -/
theorem alphaCechIso_zero (k : Type*) [Field k] : alphaCechIso sites k 0 = alphaH0Iso sites k := by
  apply Iso.ext
  rfl

end TDA.Persistence
