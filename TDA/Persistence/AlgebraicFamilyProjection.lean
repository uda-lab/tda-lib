import TDA.Persistence.AlgebraicFamily

/-!
# Coordinate projections of algebraic sums

`projection F j : familyModule F ⟶ F j` is the natural map that reads the `j`-th coordinate of
the algebraic sum at each parameter. It is a retraction of `inclusion F j` and vanishes on the
other summands.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence.AlgebraicFamily

open CategoryTheory

variable {k : Type u} [Field k] {ι : Type}

/-- The natural coordinate projection from the algebraic sum onto the summand at `j`. -/
noncomputable def projection (F : ι → PModule.{u,0,u} k ℝ) (j : ι) :
    familyModule F ⟶ F j where
  app t := ModuleCat.ofHom (DirectSum.component k ι (fun i => (F i).obj t) j)
  naturality := by
    intro s t f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact structureMap_apply F (leOfHom f) x j

/-- The projection reads the coordinate of the direct sum. -/
@[simp] theorem projection_app_apply (F : ι → PModule.{u,0,u} k ℝ) (j : ι) (t : ℝ)
    (x : (familyModule F).obj t) :
    ((projection F j).app t).hom x = DirectSum.component k ι (fun i => (F i).obj t) j x :=
  rfl

/-- The projection is a retraction of the inclusion at the same index. -/
@[simp] theorem inclusion_comp_projection_self (F : ι → PModule.{u,0,u} k ℝ) (j : ι) :
    inclusion F j ≫ projection F j = 𝟙 (F j) := by
  ext t x
  exact inclusion_apply_self F j t x

/-- The projection kills the other summands. -/
theorem inclusion_comp_projection_ne (F : ι → PModule.{u,0,u} k ℝ) {i j : ι} (hij : i ≠ j) :
    inclusion F i ≫ projection F j = 0 := by
  ext t x
  exact inclusion_apply_ne F hij t x

end TDA.Persistence.AlgebraicFamily
