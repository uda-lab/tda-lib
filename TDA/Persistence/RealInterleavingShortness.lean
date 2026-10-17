import TDA.Persistence.RealInterleavingLaws
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

/-!
# Actual defects of real interleaving morphisms

The categorical kernel and cokernel of an epsilon-interleaving morphism have
zero double-shift transition. This proves Bauer--Lesnick v4, Lemma 6.3, directly
from the two interleaving equations, over rings without dimension assumptions.
-/

set_option autoImplicit false

universe u w

namespace TDA.Persistence.RealInterleaving

open CategoryTheory CategoryTheory.Limits RealShift
open scoped NNReal

variable {R : Type u} [Ring R] {ε : ℝ≥0}
variable {M N : PModule.{u,0,w} R ℝ}

-- First annihilate maps to the nested index used by the component interleaving
-- equations. Functoriality then transports that zero to the additive shift index.
private theorem transition_double_eq_zero (A : PModule.{u,0,w} R ℝ)
    (h : ∀ t, structureMap A (show t ≤ (t + (ε : ℝ)) + (ε : ℝ) from
      (le_add_of_nonneg_right ε.coe_nonneg).trans
        (le_add_of_nonneg_right ε.coe_nonneg)) = 0) :
    transition (ε + ε) A = 0 := by
  apply NatTrans.ext
  funext t
  have he : structureMap A (le_add_of_nonneg_right (NNReal.coe_nonneg (ε + ε))) =
        structureMap A (show t ≤ (t + (ε : ℝ)) + (ε : ℝ) from
          (le_add_of_nonneg_right ε.coe_nonneg).trans
            (le_add_of_nonneg_right ε.coe_nonneg)) ≫
          A.map (eqToHom (show (t + (ε : ℝ)) + (ε : ℝ) =
            t + ((ε + ε : ℝ≥0) : ℝ) by simp [add_assoc])) := by
      change A.map _ = A.map _ ≫ A.map _
      rw [← A.map_comp]
      congr 1
  change structureMap A (le_add_of_nonneg_right (NNReal.coe_nonneg (ε + ε))) = 0
  rw [he, h t, zero_comp]

/-- The actual kernel of the forward interleaving morphism is `2ε`-trivial.
Finite dimensionality and constructibility are not needed. -/
theorem kernel_transition_eq_zero (i : RealInterleaving ε M N) :
    transition (ε + ε) (kernel i.φ) = 0 := by
  apply transition_double_eq_zero
  intro t
  let h : t ≤ (t + (ε : ℝ)) + (ε : ℝ) :=
    (le_add_of_nonneg_right ε.coe_nonneg).trans
      (le_add_of_nonneg_right ε.coe_nonneg)
  have hn : structureMap (kernel i.φ) h ≫
      (kernel.ι i.φ).app ((t + (ε : ℝ)) + (ε : ℝ)) =
      (kernel.ι i.φ).app t ≫ structureMap M h :=
    (kernel.ι i.φ).naturality (homOfLE h)
  apply (cancel_mono ((kernel.ι i.φ).app ((t + (ε : ℝ)) + (ε : ℝ)))).mp
  rw [zero_comp, hn]
  change (kernel.ι i.φ).app t ≫ structureMap M h = 0
  erw [← i.φ_ψ_structureMap t, ← Category.assoc]
  have hc := congrArg (fun f => f.app t) (kernel.condition i.φ)
  change (kernel.ι i.φ).app t ≫ i.φ.app t = 0 at hc
  erw [hc, zero_comp]

/-- The actual cokernel of the forward interleaving morphism is `2ε`-trivial.
Its target is the shifted module, so the reverse equation is evaluated at `t+ε`. -/
theorem cokernel_transition_eq_zero (i : RealInterleaving ε M N) :
    transition (ε + ε) (cokernel i.φ) = 0 := by
  apply transition_double_eq_zero
  intro t
  let h : t ≤ (t + (ε : ℝ)) + (ε : ℝ) :=
    (le_add_of_nonneg_right ε.coe_nonneg).trans
      (le_add_of_nonneg_right ε.coe_nonneg)
  have hn : structureMap ((shift ε).obj N) h ≫
      (cokernel.π i.φ).app ((t + (ε : ℝ)) + (ε : ℝ)) =
      (cokernel.π i.φ).app t ≫ structureMap (cokernel i.φ) h :=
    (cokernel.π i.φ).naturality (homOfLE h)
  apply (cancel_epi ((cokernel.π i.φ).app t)).mp
  rw [comp_zero, ← hn]
  change structureMap N (add_le_add h le_rfl) ≫
    (cokernel.π i.φ).app ((t + (ε : ℝ)) + (ε : ℝ)) = 0
  erw [← i.symm.φ_ψ_structureMap (t + (ε : ℝ)), Category.assoc]
  have hc := congrArg (fun f => f.app ((t + (ε : ℝ)) + (ε : ℝ)))
    (cokernel.condition i.φ)
  change i.φ.app ((t + (ε : ℝ)) + (ε : ℝ)) ≫
    (cokernel.π i.φ).app ((t + (ε : ℝ)) + (ε : ℝ)) = 0 at hc
  erw [hc, comp_zero]

end TDA.Persistence.RealInterleaving
