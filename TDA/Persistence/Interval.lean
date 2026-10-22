import TDA.Persistence.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Finite discrete interval modules

An interval on `Fin N` is represented by natural endpoints `birth < death ≤ N` and uses the
half-open convention `[birth, death)`. Its fibers are the top and bottom submodules of the
coefficient field, so all carriers live in the field's universe. The endpoint `death = N` means
that the interval is present at the final observed index; it does not assert an infinite lifetime.
-/

universe u

namespace TDA.Persistence

open CategoryTheory

/-- A finite interval `[birth, death)` on the observed index set `Fin N`. -/
structure FiniteInterval (N : ℕ) where
  birth : ℕ
  death : ℕ
  birth_lt_death : birth < death
  death_le_size : death ≤ N
deriving DecidableEq, Repr

namespace FiniteInterval

/-- Whether the index lies in the half-open interval. -/
def alive {N : ℕ} (I : FiniteInterval N) (i : Fin N) : Prop :=
  I.birth ≤ i.val ∧ i.val < I.death

/-- The interval fiber is the full field while alive and its zero submodule otherwise. -/
noncomputable def fiber {N : ℕ} {k : Type u} [Field k] (I : FiniteInterval N) (i : Fin N) :
    Submodule k k := by
  classical
  exact if I.alive i then ⊤ else ⊥

private theorem alive_middle {N : ℕ} (I : FiniteInterval N) {i j ℓ : Fin N}
    (hij : i ≤ j) (hjℓ : j ≤ ℓ) (hi : I.alive i) (hℓ : I.alive ℓ) : I.alive j := by
  exact ⟨hi.1.trans (Fin.le_iff_val_le_val.mp hij),
    (Fin.le_iff_val_le_val.mp hjℓ).trans_lt hℓ.2⟩

end FiniteInterval

open FiniteInterval

/-- The transition map is the identity on a pair of alive fibers and zero otherwise. -/
noncomputable def intervalMap {N : ℕ} {k : Type u} [Field k]
    (I : FiniteInterval N) {i j : Fin N} (_hij : i ≤ j) :
    FiniteInterval.fiber (k := k) I i →ₗ[k] FiniteInterval.fiber (k := k) I j := by
  classical
  exact if h : I.alive i ∧ I.alive j then
    Submodule.inclusion (by simp [FiniteInterval.fiber, h.1, h.2])
  else 0

/-- The covariant persistence module associated to a finite discrete interval. -/
noncomputable def intervalModule {N : ℕ} {k : Type u} [Field k]
    (I : FiniteInterval N) : PModule.{u,0,u} k (Fin N) where
  obj i := ModuleCat.of k (FiniteInterval.fiber (k := k) I i)
  map {i j} f := ModuleCat.ofHom (intervalMap (k := k) I (leOfHom f))
  map_id i := by
    classical
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change intervalMap (k := k) I (leOfHom (𝟙 i)) x = x
    by_cases h : I.alive i
    · apply Subtype.ext
      simp [intervalMap, h]
    · apply Subtype.ext
      have hx : (x : k) = 0 := by
        simpa [FiniteInterval.fiber, h] using x.property
      simp [intervalMap, h, hx]
  map_comp {i j ℓ} f g := by
    classical
    apply ModuleCat.hom_ext
    change intervalMap (k := k) I (leOfHom (f ≫ g)) =
      (intervalMap (k := k) I (leOfHom g)).comp
        (intervalMap (k := k) I (leOfHom f))
    apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply]
    have hconv := alive_middle I (leOfHom f) (leOfHom g)
    by_cases hi : I.alive i
    · by_cases hℓ : I.alive ℓ
      · have hj : I.alive j := hconv hi hℓ
        apply Subtype.ext
        simp [intervalMap, hi, hj, hℓ]
      ·
        apply Subtype.ext
        simp [intervalMap, hℓ]
    ·
      apply Subtype.ext
      simp [intervalMap, hi]

private theorem structureMapLinear_intervalModule {N : ℕ} {k : Type u} [Field k]
    (I : FiniteInterval N) {i j : Fin N} (hij : i ≤ j) :
    structureMapLinear (intervalModule (k := k) I) hij = intervalMap (k := k) I hij := rfl

/-- Every fiber of a finite interval module is finite-dimensional over its field. -/
instance intervalModule_finiteDimensional {N : ℕ} {k : Type u} [Field k]
    (I : FiniteInterval N) (i : Fin N) :
    FiniteDimensional k ((intervalModule (k := k) I).obj i) := by
  classical
  unfold intervalModule
  dsimp
  infer_instance

/-- The rank of a structure map, defined as the dimension of its linear-map range.

The finite-dimensional hypothesis is on the source fiber; the range inherits finite
dimensionality as a submodule. -/
noncomputable def structureMapRank {N : ℕ} {k : Type u} [Field k]
    (M : PModule.{u,0,u} k (Fin N)) (i j : Fin N) (hij : i ≤ j)
    [FiniteDimensional k (M.obj i)] : ℕ :=
  Module.finrank k (LinearMap.range (structureMapLinear M hij))

/-- The interval transition has rank one exactly when both endpoints are alive. -/
theorem intervalMap_finrank_range {N : ℕ} {k : Type u} [Field k]
    (I : FiniteInterval N) {i j : Fin N} (hij : i ≤ j)
    [decAlive : Decidable (I.alive i ∧ I.alive j)] :
    Module.finrank k (LinearMap.range (intervalMap (k := k) I hij)) =
      if I.alive i ∧ I.alive j then 1 else 0 := by
  by_cases h : I.alive i ∧ I.alive j
  · rw [if_pos h]
    have hi : I.fiber (k := k) i = ⊤ := by simp [FiniteInterval.fiber, h.1]
    have hmap : intervalMap (k := k) I hij =
        Submodule.inclusion (by simp [FiniteInterval.fiber, h.1, h.2]) := by
      simp [intervalMap, h]
    have hinj : Function.Injective (intervalMap (k := k) I hij) := by
      rw [hmap]
      exact Submodule.inclusion_injective _
    rw [LinearMap.finrank_range_of_inj hinj, hi]
    simp
  · rw [if_neg h]
    have hmap : intervalMap (k := k) I hij = 0 := by simp [intervalMap, h]
    rw [hmap]
    simp [LinearMap.range_zero]

/-- On an ordered pair of indices, the active-endpoint condition is the barcode condition. -/
theorem interval_alive_endpoints_iff {N : ℕ} (I : FiniteInterval N)
    {i j : Fin N} (hij : i ≤ j) :
    (I.alive i ∧ I.alive j) ↔ I.birth ≤ i.val ∧ j.val < I.death := by
  constructor
  · rintro ⟨hi, hj⟩
    exact ⟨hi.1, hj.2⟩
  · rintro ⟨hb, jd⟩
    exact ⟨⟨hb, (Fin.le_iff_val_le_val.mp hij).trans_lt jd⟩,
      ⟨hb.trans (Fin.le_iff_val_le_val.mp hij), jd⟩⟩

end TDA.Persistence
