import TDA.Persistence.RealInterleaving

/-!
# Enlargement, composition and transport of real interleavings

All comparisons use the original module maps at translated real indices. These are the
operations of Bauer--Lesnick, arXiv:1311.3681v4, Remark 3.1, extended from fields to rings.
-/

set_option autoImplicit false

universe u w

namespace TDA.Persistence

open CategoryTheory RealShift
open scoped NNReal

variable {R : Type u} [Ring R]

namespace RealShift

/-- Increasing the translation parameter gives the original forward structure maps. -/
def shiftLE {ε δ : ℝ≥0} (h : ε ≤ δ) (M : PModule.{u,0,w} R ℝ) :
    (shift ε).obj M ⟶ (shift δ).obj M where
  app t := structureMap M (add_le_add (le_refl t) (show (ε : ℝ) ≤ δ from h))
  naturality s t f := by
    change M.map _ ≫ M.map _ = M.map _ ≫ M.map _
    erw [← M.map_comp, ← M.map_comp]
    congr 1

/-- Components of parameter enlargement are the translated structure maps. -/
@[simp] theorem shiftLE_app {ε δ : ℝ≥0} (h : ε ≤ δ)
    (M : PModule.{u,0,w} R ℝ) (t : ℝ) :
    (shiftLE h M).app t =
      structureMap M (add_le_add (le_refl t) (show (ε : ℝ) ≤ δ from h)) := rfl

end RealShift

namespace RealInterleaving

variable {ε δ σ : ℝ≥0} {M N P : PModule.{u,0,w} R ℝ}

/-- The first interleaving equation before reparenthesizing the translated index. -/
@[reassoc] theorem φ_ψ_structureMap (i : RealInterleaving ε M N) (t : ℝ) :
    i.φ.app t ≫ i.ψ.app (t + (ε : ℝ)) =
      structureMap M (show t ≤ (t + (ε : ℝ)) + (ε : ℝ) from
        (le_add_of_nonneg_right ε.coe_nonneg).trans (le_add_of_nonneg_right ε.coe_nonneg)) := by
  apply (cancel_mono ((compIso ε ε M).hom.app t)).mp
  erw [Category.assoc, i.φ_ψ_app]
  change M.map _ = M.map _ ≫ M.map _
  erw [← M.map_comp]
  congr 1

private def ofStructureMapEquations (f : M ⟶ (shift ε).obj N) (g : N ⟶ (shift ε).obj M)
    (hf : ∀ t, f.app t ≫ g.app (t + (ε : ℝ)) =
      structureMap M (show t ≤ (t + (ε : ℝ)) + (ε : ℝ) from
        (le_add_of_nonneg_right ε.coe_nonneg).trans (le_add_of_nonneg_right ε.coe_nonneg)))
    (hg : ∀ t, g.app t ≫ f.app (t + (ε : ℝ)) =
      structureMap N (show t ≤ (t + (ε : ℝ)) + (ε : ℝ) from
        (le_add_of_nonneg_right ε.coe_nonneg).trans (le_add_of_nonneg_right ε.coe_nonneg))) :
    RealInterleaving ε M N :=
  ofApp f g (fun t => by
    erw [← Category.assoc, hf]
    change M.map _ ≫ M.map _ = M.map _
    erw [← M.map_comp]
    congr 1) (fun t => by
    erw [← Category.assoc, hg]
    change N.map _ ≫ N.map _ = N.map _
    erw [← N.map_comp]
    congr 1)

private theorem enlarge_equation (h : ε ≤ δ) (i : RealInterleaving ε M N) (t : ℝ) :
    (i.φ ≫ shiftLE h N).app t ≫ (i.ψ ≫ shiftLE h M).app (t + (δ : ℝ)) =
      structureMap M (show t ≤ (t + (δ : ℝ)) + (δ : ℝ) from
        (le_add_of_nonneg_right δ.coe_nonneg).trans (le_add_of_nonneg_right δ.coe_nonneg)) := by
  dsimp only [NatTrans.comp_app, shiftLE, shift, reindex]
  repeat' erw [Category.assoc]
  erw [i.ψ.naturality_assoc]
  erw [← Category.assoc, i.φ_ψ_structureMap]
  change M.map _ ≫ M.map _ ≫ M.map _ = M.map _
  erw [← M.map_comp, ← M.map_comp]
  congr 1

/-- Enlarge an interleaving without changing its modules. -/
def mono (i : RealInterleaving ε M N) (h : ε ≤ δ) : RealInterleaving δ M N :=
  ofStructureMapEquations (i.φ ≫ shiftLE h N) (i.ψ ≫ shiftLE h M)
    (enlarge_equation h i) (enlarge_equation h i.symm)

private def composeMap (f : M ⟶ (shift ε).obj N) (g : N ⟶ (shift δ).obj P)
    (h : ε + δ = σ) : M ⟶ (shift σ).obj P :=
  f ≫ (shift ε).map g ≫ (compIso ε δ P).hom ≫ (congrIso h P).hom

private theorem compose_equation (i : RealInterleaving ε M N)
    (j : RealInterleaving δ N P) (h : ε + δ = σ) (h' : δ + ε = σ) (t : ℝ) :
    (composeMap i.φ j.φ h).app t ≫
        (composeMap j.ψ i.ψ h').app (t + (σ : ℝ)) =
      structureMap M (show t ≤ (t + (σ : ℝ)) + (σ : ℝ) from
        (le_add_of_nonneg_right σ.coe_nonneg).trans (le_add_of_nonneg_right σ.coe_nonneg)) := by
  dsimp only [composeMap, NatTrans.comp_app, shift_map_app]
  simp only [compIso_hom_app, congrIso_hom_app]
  repeat' erw [Category.assoc]
  -- Move the two index-equality transports past the reverse comparisons.
  erw [j.ψ.naturality_assoc]
  erw [j.ψ.naturality_assoc]
  erw [i.ψ.naturality_assoc]
  erw [i.ψ.naturality_assoc]
  -- Collapse the inner interleaving, then use naturality to collapse the outer one.
  erw [← Category.assoc (j.φ.app (t + (ε : ℝ))) (j.ψ.app ((t + (ε : ℝ)) + (δ : ℝ))),
    j.φ_ψ_structureMap]
  erw [i.ψ.naturality_assoc]
  erw [← Category.assoc (i.φ.app t) (i.ψ.app (t + (ε : ℝ))),
    i.φ_ψ_structureMap]
  change M.map _ ≫ M.map _ ≫ M.map _ ≫ M.map _ ≫ M.map _ ≫ M.map _ = M.map _
  repeat' erw [← M.map_comp]
  congr 1

/-- Compose two interleavings, adding their finite parameters. -/
def trans (i : RealInterleaving ε M N) (j : RealInterleaving δ N P) :
    RealInterleaving (ε + δ) M P :=
  ofStructureMapEquations (composeMap i.φ j.φ rfl) (composeMap j.ψ i.ψ (add_comm δ ε))
    (compose_equation i j rfl (add_comm δ ε))
    (compose_equation j.symm i.symm (add_comm δ ε) rfl)

/-- Transport both modules along natural isomorphisms at the same parameter. -/
def congr {M' N' : PModule.{u,0,w} R ℝ} (i : RealInterleaving ε M N)
    (e : M ≅ M') (d : N ≅ N') : RealInterleaving ε M' N' := by
  have comp {A B A' B' : PModule.{u,0,w} R ℝ}
      (f : A ⟶ (shift ε).obj B) (g : B ⟶ (shift ε).obj A)
      (h : f ≫ (shift ε).map g ≫ (compIso ε ε A).hom = transition (ε + ε) A)
      (a : A ≅ A') (b : B ≅ B') :
      (a.inv ≫ f ≫ (shift ε).map b.hom) ≫
        (shift ε).map (b.inv ≫ g ≫ (shift ε).map a.hom) ≫
          (compIso ε ε A').hom = transition (ε + ε) A' := by
    simp only [Functor.map_comp, Category.assoc]
    rw [← Functor.map_comp_assoc, b.hom_inv_id, (shift ε).map_id, Category.id_comp]
    rw [compIso_naturality]
    have hh := congrArg (fun m => a.inv ≫ m ≫ (shift (ε + ε)).map a.hom) h
    simp only [Category.assoc] at hh
    rw [hh]
    rw [← transition_naturality, Iso.inv_hom_id_assoc]
  exact ⟨e.inv ≫ i.φ ≫ (shift ε).map d.hom,
    d.inv ≫ i.ψ ≫ (shift ε).map e.hom,
    comp i.φ i.ψ i.φ_ψ e d, comp i.ψ i.φ i.ψ_φ d e⟩

end RealInterleaving
end TDA.Persistence
