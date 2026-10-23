import TDA.Persistence.FinitePresentationTests
import TDA.Persistence.FinitePresentationGrid
import TDA.Persistence.CoordinateShift

/-!
# Right continuity of Hom from a finitely presented module

For two finitely presented modules, increasing any fixed diagonal shift by a
sufficiently small amount induces a bijection on the Hom set. The source's
generator and relation grades give finitely many tests; the target's finite
critical coordinates provide a common positive slack for those tests.
-/

set_option autoImplicit false

universe u v w

namespace TDA.Persistence.GradedFree

open CategoryTheory CoordinateShift
open scoped TDA.Persistence NNReal

private theorem finite_uniform_right_slack {ι : Type v} (S : Set ι) (hS : S.Finite)
    (Q : ι → ℝ → Prop)
    (h : ∀ a ∈ S, ∃ ε : ℝ, 0 < ε ∧
      ∀ δ : ℝ, 0 ≤ δ → δ ≤ ε → Q a δ) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ δ : ℝ, 0 ≤ δ → δ ≤ ε → ∀ a ∈ S, Q a δ := by
  classical
  refine Set.Finite.induction_on_subset
    (motive := fun T _ => ∃ ε : ℝ, 0 < ε ∧
      ∀ δ : ℝ, 0 ≤ δ → δ ≤ ε → ∀ a ∈ T, Q a δ)
    S hS ?_ ?_
  · refine ⟨1, zero_lt_one, ?_⟩
    intro δ _ _ a ha
    cases ha
  · intro a T haS _ _ hT
    obtain ⟨εa, hεa, hQa⟩ := h a haS
    obtain ⟨εT, hεT, hQT⟩ := hT
    refine ⟨min εa εT, lt_min hεa hεT, ?_⟩
    intro δ hδ hδmin b hb
    rcases Set.mem_insert_iff.mp hb with rfl | hbT
    · exact hQa δ hδ (le_trans hδmin (min_le_left _ _))
    · exact hQT δ hδ (le_trans hδmin (min_le_right _ _)) b hbT

variable {R : Type u} [Ring R] {n : ℕ}

/-- Hom sets from a finitely presented module are unchanged by a sufficiently
small increase of a fixed shift of another finitely presented module. -/
theorem finitelyPresented_exists_pos_postcomp_shiftLE_bijective
    (M N : PModule.{u,0,max u w} R (Fin n → ℝ))
    (hM : FinitelyPresented (R := R) M) (hN : FinitelyPresented (R := R) N)
    (ε : ℝ≥0) :
    ∃ η : ℝ≥0, 0 < η ∧ ∀ δ : ℝ≥0, δ ≤ η →
      Function.Bijective (fun f : M ⟶ (shift ε).obj N =>
        f ≫ shiftLE (show ε ≤ ε + δ from le_self_add) N) := by
  obtain ⟨S, hS, htest⟩ := finitelyPresented_exists_finite_postcomp_tests M hM
  let Q : (Fin n → ℝ) → ℝ → Prop := fun a δ => ∀ hδ : 0 ≤ δ,
    IsIso (structureMap N
      (show translation ε a ≤ (fun i => translation ε a i + δ) from
        fun _ => le_add_of_nonneg_right hδ))
  have hlocal : ∀ a ∈ S, ∃ η : ℝ, 0 < η ∧
      ∀ δ : ℝ, 0 ≤ δ → δ ≤ η → Q a δ := by
    intro a _
    obtain ⟨η, hη, hstable⟩ :=
      finitelyPresented_exists_pos_structureMap_isIso N hN (translation ε a)
    exact ⟨η, hη, fun δ hδ hδη _ => hstable δ hδ hδη⟩
  obtain ⟨η, hη, huniform⟩ := finite_uniform_right_slack S hS Q hlocal
  refine ⟨⟨η, hη.le⟩, hη, ?_⟩
  intro δ hδ
  apply htest
  intro a ha
  have hstable := huniform δ δ.coe_nonneg hδ a ha δ.coe_nonneg
  have htarget : translation (ε + δ) a =
      (fun i => translation ε a i + (δ : ℝ)) := by
    funext i
    simp only [translation_apply, NNReal.coe_add, add_assoc]
  have hiso : IsIso ((shiftLE (show ε ≤ ε + δ from le_self_add) N).app a) := by
    let e := N.mapIso (eqToIso htarget.symm)
    have hcomparison : (shiftLE (show ε ≤ ε + δ from le_self_add) N).app a =
        structureMap N
          (show translation ε a ≤ (fun i => translation ε a i + (δ : ℝ)) from
            fun _ => le_add_of_nonneg_right δ.coe_nonneg) ≫ e.hom := by
      change N.map _ = N.map _ ≫ N.map _
      erw [← N.map_comp]
      congr 1
    rw [hcomparison]
    exact IsIso.comp_isIso' hstable e.isIso_hom
  exact (ConcreteCategory.isIso_iff_bijective _).mp hiso

end TDA.Persistence.GradedFree
