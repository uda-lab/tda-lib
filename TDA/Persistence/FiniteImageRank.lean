import TDA.Persistence.FiniteImage

/-!
# Ranks of image structure maps

An image structure map has the same rank as the original component followed by
the target structure map. Corestriction is surjective and inclusion of a range
preserves dimension; no finite-dimensional source fibers are needed.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence

open CategoryTheory

variable {s : ℕ} {k : Type u} [Field k]
variable {M N : PModule.{u,0,u} k (Fin s)}

/-- The image transition acts by the target transition on the underlying vector. -/
@[simp] theorem finiteImage_structureMap_val (φ : M ⟶ N) {i j : Fin s} (hij : i ≤ j)
    (x : (finiteImage φ).obj i) :
    ((fromFiniteImage φ).app j).hom (structureMapLinear (finiteImage φ) hij x) =
      structureMapLinear N hij (((fromFiniteImage φ).app i).hom x) := rfl

/-- The composite across stages factors through the actual image structure map. -/
theorem finiteImage_crossStage_factorization (φ : M ⟶ N) {i j : Fin s} (hij : i ≤ j) :
    (structureMapLinear N hij).comp (φ.app i).hom =
      ((fromFiniteImage φ).app j).hom.comp
        ((structureMapLinear (finiteImage φ) hij).comp ((toFiniteImage φ).app i).hom) := rfl

/-- Image persistence measures the rank of the component followed by the target transition.
Only the target fibers must be finite-dimensional. -/
theorem finiteImage_structureMapRank (φ : M ⟶ N)
    [∀ i, FiniteDimensional k (N.obj i)] (i j : Fin s) (hij : i ≤ j) :
    structureMapRank (finiteImage φ) i j hij =
      Module.finrank k (LinearMap.range ((structureMapLinear N hij).comp (φ.app i).hom)) := by
  rw [finiteImage_crossStage_factorization, ← LinearMap.comp_assoc,
    LinearMap.range_comp_of_range_eq_top _
      (LinearMap.range_eq_top.mpr (toFiniteImage_surjective φ i)), LinearMap.range_comp]
  exact (Submodule.finrank_map_subtype_eq _ _).symm

/-- A zero transformation has zero image rank at every comparable pair. -/
@[simp] theorem finiteImage_zero_structureMapRank
    [∀ i, FiniteDimensional k (N.obj i)] (i j : Fin s) (hij : i ≤ j) :
    structureMapRank (finiteImage (0 : M ⟶ N)) i j hij = 0 := by
  rw [finiteImage_structureMapRank]
  simp

/-- Taking the image of the identity recovers the ordinary structure-map rank. -/
@[simp] theorem finiteImage_id_structureMapRank
    [∀ i, FiniteDimensional k (M.obj i)] (i j : Fin s) (hij : i ≤ j) :
    structureMapRank (finiteImage (𝟙 M)) i j hij = structureMapRank M i j hij := by
  rw [finiteImage_structureMapRank]
  rfl

end TDA.Persistence
