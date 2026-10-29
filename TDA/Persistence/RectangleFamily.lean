import TDA.Persistence.RectangleStabilityGeometry
import TDA.Persistence.CoordinateInterleaving
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Products

/-!
# Finite families of bounded rectangle modules

The finite family is the categorical biproduct of its rectangle modules. This
keeps occurrences distinct even when two rectangles have identical endpoints.
The component maps below are the entries of the interleaving matrices in
Bjerkevik's Lemma 4.9.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence.RectangleFamily

open CategoryTheory CategoryTheory.Limits CoordinateShift
open scoped TDA.Persistence NNReal

variable {k : Type u} [Field k] {n : ℕ}

private instance : HasFiniteBiproducts (PModule.{u,0,u} k (Fin n → ℝ)) :=
  HasFiniteBiproducts.of_hasFiniteProducts

private instance (ε : ℝ≥0) :
    (shift (R := k) (n := n) ε).Additive where
  map_add := by
    intro M N f g
    rfl

/-- Finite sum of rectangle modules, indexed by occurrences. -/
noncomputable def module {ι : Type} [Finite ι] (R : ι → Rectangle n) :
    PModule.{u,0,u} k (Fin n → ℝ) :=
  ⨁ (fun i : ι => (R i).module (k := k))

/-- Canonical inclusion of an occurrence. -/
noncomputable def inclusion {ι : Type} [Finite ι] (R : ι → Rectangle n) (i : ι) :
    (R i).module (k := k) ⟶ module (k := k) R :=
  biproduct.ι (fun i : ι => (R i).module (k := k)) i

/-- Canonical projection onto an occurrence. -/
noncomputable def projection {ι : Type} [Finite ι] (R : ι → Rectangle n) (i : ι) :
    module (k := k) R ⟶ (R i).module :=
  biproduct.π (fun i : ι => (R i).module (k := k)) i

@[simp] theorem inclusion_projection_self {ι : Type} [Finite ι]
    (R : ι → Rectangle n) (i : ι) :
    inclusion (k := k) R i ≫ projection R i = 𝟙 ((R i).module) := by
  exact biproduct.ι_π_self (fun j : ι => (R j).module (k := k)) i

@[simp] theorem inclusion_projection_ne {ι : Type} [Finite ι]
    (R : ι → Rectangle n) {i j : ι} (h : i ≠ j) :
    inclusion (k := k) R i ≫ projection R j = 0 := by
  exact biproduct.ι_π_ne (fun j : ι => (R j).module (k := k)) h

/-- The finite family identity is the sum of its coordinate projections and
inclusions. This is the algebraic expansion used in Lemma 4.9. -/
theorem sum_projection_inclusion {ι : Type} [Fintype ι]
    (R : ι → Rectangle n) :
    ∑ i, projection (k := k) R i ≫ inclusion R i = 𝟙 (module (k := k) R) :=
  biproduct.total (f := fun j : ι => (R j).module (k := k))

/-- The `(i,j)` entry of a shifted map between finite rectangle families. -/
noncomputable def component {ι κ : Type} [Finite ι] [Finite κ]
    (R : ι → Rectangle n) (S : κ → Rectangle n) (ε : ℝ≥0)
    (f : module (k := k) R ⟶ (shift ε).obj (module S)) (i : ι) (j : κ) :
    (R i).module (k := k) ⟶ (shift ε).obj ((S j).module (k := k)) :=
  inclusion (k := k) R i ≫ f ≫ (shift ε).map (projection (k := k) S j)

/-- The matrix entries of a composite across the middle finite family sum
to the entry of the composite. -/
theorem component_composite {ι κ ν : Type}
    [Finite ι] [Fintype κ] [Finite ν]
    (R : ι → Rectangle n) (S : κ → Rectangle n) (T : ν → Rectangle n)
    (ε : ℝ≥0)
    (f : module (k := k) R ⟶ (shift ε).obj (module S))
    (g : module (k := k) S ⟶ (shift ε).obj (module T))
    (i : ι) (i' : ν) :
    ∑ j : κ, component (k := k) R S ε f i j ≫
        (shift ε).map (component (k := k) S T ε g j i') =
      inclusion (k := k) R i ≫ f ≫ (shift ε).map g ≫
        (shift ε).map ((shift ε).map (projection (k := k) T i')) := by
  classical
  simp only [component, Functor.map_comp, Category.assoc]
  rw [← Preadditive.comp_sum]
  simp only [← Category.assoc]
  rw [← Preadditive.sum_comp]
  simp only [Category.assoc, ← Functor.map_comp]
  rw [← Preadditive.comp_sum]
  rw [← Functor.map_sum]
  have hs : (∑ a : κ, projection (k := k) S a ≫ inclusion S a ≫ g) = g := by
    simp only [← Category.assoc]
    rw [← Preadditive.sum_comp, sum_projection_inclusion, Category.id_comp]
  rw [hs]
  simp only [Functor.map_comp, Category.assoc]

/-- The two interleaving maps give the actual finite sum of two-step
component paths. The right-hand side is the family structure map, restricted
to its source and target occurrences. -/
theorem component_interleaving_sum {ι κ : Type}
    [Fintype ι] [Fintype κ]
    (R : ι → Rectangle n) (S : κ → Rectangle n) (ε : ℝ≥0)
    (I : CoordinateInterleaving ε (module (k := k) R) (module S))
    (i i' : ι) :
    (∑ j : κ, component (k := k) R S ε I.φ i j ≫
      (shift ε).map (component S R ε I.ψ j i')) ≫
        (compIso ε ε ((R i').module (k := k))).hom =
      inclusion (k := k) R i ≫ transition (ε + ε) (module R) ≫
        (shift (ε + ε)).map (projection R i') := by
  classical
  rw [component_composite]
  simp only [Category.assoc]
  rw [compIso_naturality ε ε (projection (k := k) R i')]
  simp only [← Category.assoc, I.φ_ψ]

/-- Distinct rectangle occurrences give zero entries in the interleaving
composite matrix. -/
theorem component_interleaving_sum_ne {ι κ : Type}
    [Fintype ι] [Fintype κ]
    (R : ι → Rectangle n) (S : κ → Rectangle n) (ε : ℝ≥0)
    (I : CoordinateInterleaving ε (module (k := k) R) (module S))
    {i i' : ι} (h : i ≠ i') :
    (∑ j : κ, component (k := k) R S ε I.φ i j ≫
      (shift ε).map (component S R ε I.ψ j i')) ≫
        (compIso ε ε ((R i').module (k := k))).hom = 0 := by
  rw [component_interleaving_sum R S ε I i i']
  simp only [← Category.assoc]
  rw [transition_naturality (ε + ε) (inclusion (k := k) R i)]
  simp only [Category.assoc, ← Functor.map_comp, inclusion_projection_ne R h,
    Functor.map_zero, comp_zero]

/-- A diagonal entry of the interleaving composite matrix is precisely the
rectangle's own structure map. -/
theorem component_interleaving_sum_self {ι κ : Type}
    [Fintype ι] [Fintype κ]
    (R : ι → Rectangle n) (S : κ → Rectangle n) (ε : ℝ≥0)
    (I : CoordinateInterleaving ε (module (k := k) R) (module S))
    (i : ι) :
    (∑ j : κ, component (k := k) R S ε I.φ i j ≫
      (shift ε).map (component S R ε I.ψ j i)) ≫
        (compIso ε ε ((R i).module (k := k))).hom =
      transition (ε + ε) ((R i).module (k := k)) := by
  rw [component_interleaving_sum R S ε I i i]
  simp only [← Category.assoc]
  rw [transition_naturality (ε + ε) (inclusion (k := k) R i)]
  simp only [Category.assoc, ← Functor.map_comp, inclusion_projection_self]
  simp

end TDA.Persistence.RectangleFamily
