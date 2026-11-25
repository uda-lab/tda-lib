import TDA.Filtration.AlphaLabelled
import TDA.Persistence.SublevelInterleaving
import TDA.Simplicial.H0EdgePaths

set_option autoImplicit false

/-!
# Degree-zero α–Čech persistence comparison

For finitely many labelled sites in a real normed vector space, the same-label inclusion
from closed α to ambient Čech on squared grades induces a natural isomorphism in ordinary
degree zero over a field.
Both complexes are empty at negative grades.
-/

namespace TDA.Persistence

open CategoryTheory TDA.Filtration TDA.Simplicial

variable {V E : Type*} [LinearOrder V] [NormedAddCommGroup E]
variable (sites : V → E) (k : Type*) [Field k]

/-- The morphism on ordinary degree-zero persistence induced by the labelled inclusion. -/
noncomputable def alphaH0Comparison :
    simplicialHomologyPModule k (Alpha.labelledComplexFiltration sites) 0 ⟶
      simplicialHomologyPModule k (Alpha.squaredCechFiltration sites) 0 :=
  inclusionHom k 0 (Alpha.labelledComplexFiltration_le_squaredCech sites)

@[simp]
theorem alphaH0Comparison_app (t : ℝ) :
    (alphaH0Comparison sites k).app t =
      simplicialHomologyIncl k (Alpha.labelledComplexFiltration_le_squaredCech sites t) 0 := rfl

variable [Finite V] [NormedSpace ℝ E]

/-- The actual labelled inclusion induces an isomorphism in degree zero at every grade. -/
theorem alphaH0Comparison_isIso_app (t : ℝ) : IsIso ((alphaH0Comparison sites k).app t) := by
  rw [alphaH0Comparison_app]
  by_cases ht : t < 0
  · apply simplicialHomologyIncl_isIso_of_eq
    exact (Alpha.labelledComplex_eq_bot_of_neg sites ht).trans
      (Alpha.squaredCechFiltration_apply_of_neg sites ht).symm
  · have ht' := le_of_not_gt ht
    apply simplicialHomologyIncl_zero_isIso_of_edge_reachable k _
      (fun v => Alpha.singleton_mem_labelledComplex sites v ht')
    intro u v huv
    rw [Alpha.squaredCechFiltration_apply_of_nonneg sites ht'] at huv
    exact Alpha.cech_edge_reachable sites ht' huv

/-- The inclusion-induced natural isomorphism in ordinary degree-zero persistence. -/
noncomputable def alphaH0Iso :
    simplicialHomologyPModule k (Alpha.labelledComplexFiltration sites) 0 ≅
      simplicialHomologyPModule k (Alpha.squaredCechFiltration sites) 0 := by
  letI : ∀ t, IsIso ((alphaH0Comparison sites k).app t) := alphaH0Comparison_isIso_app sites k
  letI := NatIso.isIso_of_isIso_app (alphaH0Comparison sites k)
  exact asIso (alphaH0Comparison sites k)

@[simp]
theorem alphaH0Iso_hom : (alphaH0Iso sites k).hom = alphaH0Comparison sites k := rfl

end TDA.Persistence
