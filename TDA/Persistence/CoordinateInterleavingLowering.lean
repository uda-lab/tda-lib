import TDA.Persistence.CoordinateInterleaving

/-!
# Lowering diagonal interleavings through Hom maps

The algebraic step in removing parameter slack: lift both interleaving maps
through comparison maps on Hom sets, then use injectivity on the twice-shifted
endomorphism Hom sets to recover both composite equations.
-/

set_option autoImplicit false

universe u w

namespace TDA.Persistence

open CategoryTheory CoordinateShift
open scoped TDA.Persistence NNReal

namespace CoordinateInterleaving

variable {R : Type u} [Ring R] {n : ℕ}
  {ε δ : ℝ≥0} {M N : PModule.{u,0,w} R (Fin n → ℝ)}

/-- Increasing a transition parameter factors through the corresponding shift comparison. -/
theorem transition_inflate (h : ε ≤ δ)
    (M : PModule.{u,0,w} R (Fin n → ℝ)) :
    transition ε M ≫ shiftLE h M = transition δ M := by
  apply NatTrans.ext
  funext a
  change M.map _ ≫ M.map _ = M.map _
  rw [← M.map_comp]
  congr 1

/-- Inflating the two maps of a putative interleaving inflates their composite. -/
theorem inflated_composite (h : ε ≤ δ)
    (f : M ⟶ (shift ε).obj N) (g : N ⟶ (shift ε).obj M) :
    (f ≫ (shift ε).map g ≫ (compIso ε ε M).hom) ≫
        shiftLE (add_le_add h h) M =
      (f ≫ shiftLE h N) ≫
        (shift δ).map (g ≫ shiftLE h M) ≫
          (compIso δ δ M).hom := by
  rw [Functor.map_comp]
  apply NatTrans.ext
  funext a
  dsimp only [NatTrans.comp_app, shift_map_app, shiftLE_app, compIso_hom_app]
  repeat' erw [Category.assoc]
  erw [g.naturality_assoc]
  change f.app a ≫ g.app (translation ε a) ≫ M.map _ ≫ M.map _ =
    f.app a ≫ g.app (translation ε a) ≫ M.map _ ≫ M.map _ ≫ M.map _
  repeat' erw [← M.map_comp]
  congr 1

/-- Lower an interleaving parameter when the two map lifts exist and both
twice-shifted comparison maps detect equality on endomorphism Hom sets. -/
noncomputable def of_postcomp_lifting (h : ε ≤ δ) (i : CoordinateInterleaving δ M N)
    (surjMN : Function.Surjective
      (fun f : M ⟶ (shift ε).obj N => f ≫ shiftLE h N))
    (surjNM : Function.Surjective
      (fun g : N ⟶ (shift ε).obj M => g ≫ shiftLE h M))
    (injMM : Function.Injective
      (fun f : M ⟶ (shift (ε + ε)).obj M =>
        f ≫ shiftLE (add_le_add h h) M))
    (injNN : Function.Injective
      (fun g : N ⟶ (shift (ε + ε)).obj N =>
        g ≫ shiftLE (add_le_add h h) N)) :
    CoordinateInterleaving ε M N := by
  let f := Classical.choose (surjMN i.φ)
  let g := Classical.choose (surjNM i.ψ)
  have hf : f ≫ shiftLE h N = i.φ := Classical.choose_spec (surjMN i.φ)
  have hg : g ≫ shiftLE h M = i.ψ := Classical.choose_spec (surjNM i.ψ)
  refine ⟨f, g, ?_, ?_⟩
  · apply injMM
    calc
      (f ≫ (shift ε).map g ≫ (compIso ε ε M).hom) ≫
          shiftLE (add_le_add h h) M =
        (f ≫ shiftLE h N) ≫
          (shift δ).map (g ≫ shiftLE h M) ≫
            (compIso δ δ M).hom := inflated_composite h f g
      _ = transition (δ + δ) M := by rw [hf, hg]; exact i.φ_ψ
      _ = transition (ε + ε) M ≫ shiftLE (add_le_add h h) M :=
        (transition_inflate (add_le_add h h) M).symm
  · apply injNN
    calc
      (g ≫ (shift ε).map f ≫ (compIso ε ε N).hom) ≫
          shiftLE (add_le_add h h) N =
        (g ≫ shiftLE h M) ≫
          (shift δ).map (f ≫ shiftLE h N) ≫
            (compIso δ δ N).hom := inflated_composite h g f
      _ = transition (δ + δ) N := by rw [hg, hf]; exact i.ψ_φ
      _ = transition (ε + ε) N ≫ shiftLE (add_le_add h h) N :=
        (transition_inflate (add_le_add h h) N).symm

end CoordinateInterleaving
end TDA.Persistence
