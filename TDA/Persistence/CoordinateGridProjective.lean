import TDA.Persistence.CoordinateGridRankExact
import TDA.Persistence.RankProjective
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts

/-!
# Relative projectivity and finite sums under grid Kan extension

The left Kan extension along a finite coordinate-grid inclusion preserves
rank projectivity by its actual adjunction with restriction. Its finite
biproduct comparison is the canonical Mathlib comparison.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence.CoordinateGrid

open CategoryTheory CategoryTheory.Limits
open scoped TDA.Persistence

variable {k : Type u} [Ring k] {n : ℕ} (G : CoordinateGrid n)

private instance moduleHasFiniteBiproducts {P : Type} [Preorder P] :
    HasFiniteBiproducts (PModule.{u,0,u} k P) :=
  HasFiniteBiproducts.of_hasFiniteProducts

private noncomputable instance lanAdditive :
    (G.embedding.monotone.functor.lan :
      PModule.{u,0,u} k G.Point ⥤ PModule.{u,0,u} k (Fin n → ℝ)).Additive := by
  let adj := G.embedding.monotone.functor.lanAdjunction (ModuleCat.{u} k)
  exact adj.left_adjoint_additive

section Field

variable {k : Type u} [Field k] {n : ℕ} (G : CoordinateGrid n)

/-- Finite-grid left Kan extension preserves the existing relative
rank-projectivity lifting property. The lift is obtained by applying the
grid object's own lifting property to the restricted rank-exact sequence. -/
theorem lan_isRankProjective (P : PModule.{u,0,u} k G.Point)
    (hP : IsRankProjective P) : IsRankProjective (G.lan.obj P) := by
  intro L M N ι π hs α
  let adj := G.embedding.monotone.functor.lanAdjunction (ModuleCat.{u} k)
  let α' : P ⟶ G.embedding.monotone.functor ⋙ N := (adj.homEquiv P N) α
  have hs' :
      IsRankExact (reindexNatTrans G.embedding.toOrderHom ι)
        (reindexNatTrans G.embedding.toOrderHom π) := hs.reindex G.embedding.toOrderHom
  obtain ⟨β', hβ'⟩ := hP _ _ _ _ _ hs' α'
  let β : G.lan.obj P ⟶ M := (adj.homEquiv P M).symm β'
  refine ⟨β, ?_⟩
  apply (adj.homEquiv P N).injective
  rw [adj.homEquiv_naturality_right]
  have hβcomp : (adj.homEquiv P M) β = β' := Equiv.apply_symm_apply _ _
  rw [hβcomp]
  change β' ≫ reindexNatTrans G.embedding.toOrderHom π = (adj.homEquiv P N) α
  exact hβ'

end Field

/-- The canonical comparison from the Kan extension of a finite biproduct
to the biproduct of the Kan extensions. -/
noncomputable abbrev lanBiproductIso {J : Type} [Fintype J]
    (F : J → PModule.{u,0,u} k G.Point) :
    G.lan.obj (⨁ F) ≅ ⨁ fun j => G.lan.obj (F j) :=
  G.lan.mapBiproduct F

/-- The finite-biproduct comparison identifies each projection with the
actual Kan image of the grid projection. -/
theorem lanBiproductIso_hom_π {J : Type} [Fintype J]
    (F : J → PModule.{u,0,u} k G.Point) (j : J) :
    (G.lanBiproductIso F).hom ≫ biproduct.π (fun j => G.lan.obj (F j)) j =
      G.lan.map (biproduct.π F j) := by
  rw [lanBiproductIso, Functor.mapBiproduct_hom, biproduct.lift_π]

/-- The inverse finite-biproduct comparison identifies each inclusion with
the actual Kan image of the grid inclusion. -/
theorem lanBiproductIso_inv_ι {J : Type} [Fintype J]
    (F : J → PModule.{u,0,u} k G.Point) (j : J) :
    biproduct.ι (fun j => G.lan.obj (F j)) j ≫ (G.lanBiproductIso F).inv =
      G.lan.map (biproduct.ι F j) := by
  rw [lanBiproductIso, Functor.mapBiproduct_inv, biproduct.ι_desc]

end TDA.Persistence.CoordinateGrid
