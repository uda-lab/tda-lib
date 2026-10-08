import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Whiskering
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Data.ZMod.Basic

/-!
# Preorder-indexed persistence modules

A persistence module is a covariant functor from a preorder, viewed as a category, to the category
of modules over a ring. An inequality `p ≤ q` induces a morphism from the value at `p` to the value
at `q`. Reindexing is precomposition by a monotone map, and natural transformations reindex by
left whiskering.

This API uses mathlib's preorder category and `ModuleCat` at the pinned revision
`0df444a360eaa60ab8c11dca51a86af692955474`, in particular
`Mathlib/CategoryTheory/Category/Preorder.lean`, `Mathlib/CategoryTheory/Whiskering.lean`, and
`Mathlib/Algebra/Category/ModuleCat/Basic.lean`. The ring, index, module-carrier, and reindex-domain
universes are independent. The core requires only a ring and preorders; no field or
finite-dimensional assumptions are imposed.
-/

universe u v w x y

namespace TDA.Persistence

open CategoryTheory

/-- A covariant persistence module on a preorder `P` over a ring `R`.

`R : Type u`, the index `P : Type v`, and the carrier universe `w` of `ModuleCat.{w} R` are
independent. -/
abbrev PModule (R : Type u) [Ring R] (P : Type v) [Preorder P] :=
  P ⥤ ModuleCat.{w} R

variable {R : Type u} [Ring R] {P : Type v} [Preorder P]

/-- The covariant structure morphism induced by `h : p ≤ q`. -/
def structureMap (M : PModule.{u,v,w} R P) {p q : P} (h : p ≤ q) :
    M.obj p ⟶ M.obj q :=
  M.map (homOfLE h)

/-- The underlying `R`-linear map of a persistence-module structure morphism. -/
def structureMapLinear (M : PModule.{u,v,w} R P) {p q : P} (h : p ≤ q) :
    M.obj p →ₗ[R] M.obj q :=
  (structureMap M h).hom

/-- A structure map at an index to itself is the identity morphism. -/
@[simp]
theorem structureMap_self (M : PModule.{u,v,w} R P) {p : P} (h : p ≤ p) :
    structureMap M h = 𝟙 (M.obj p) := by
  simp [structureMap]

/-- Structure maps compose in the covariant order: first `p → q`, then `q → r`. -/
theorem structureMap_comp (M : PModule.{u,v,w} R P) {p q r : P}
    (hpq : p ≤ q) (hqr : q ≤ r) :
    structureMap M hpq ≫ structureMap M hqr = structureMap M (hpq.trans hqr) := by
  change M.map (homOfLE hpq) ≫ M.map (homOfLE hqr) =
    M.map (homOfLE (hpq.trans hqr))
  rw [← M.map_comp, CategoryTheory.homOfLE_comp]

/-- The underlying linear map of a self-structure map is the identity. -/
@[simp]
theorem structureMapLinear_self (M : PModule.{u,v,w} R P) {p : P} (h : p ≤ p) :
    structureMapLinear M h = LinearMap.id := by
  simp [structureMapLinear, structureMap_self]

/-- The linear map of a composite structure map is the later map after the earlier map. -/
theorem structureMapLinear_comp (M : PModule.{u,v,w} R P) {p q r : P}
    (hpq : p ≤ q) (hqr : q ≤ r) :
    structureMapLinear M (hpq.trans hqr) =
      (structureMapLinear M hqr).comp (structureMapLinear M hpq) := by
  change (structureMap M (hpq.trans hqr)).hom = _
  rw [← structureMap_comp M hpq hqr]
  exact ModuleCat.hom_comp _ _

/-- Restrict a persistence module along a monotone map, by precomposition. -/
def reindex {Q : Type x} [Preorder Q] (u : Q →o P) (M : PModule.{u,v,w} R P) :
    PModule.{u,x,w} R Q :=
  u.toFunctor ⋙ M

/-- The value of a reindexed persistence module at `q` is the original value at `u q`. -/
@[simp]
theorem reindex_obj {Q : Type x} [Preorder Q] (u : Q →o P)
    (M : PModule.{u,v,w} R P) (q : Q) :
    (reindex u M).obj q = M.obj (u q) := rfl

/-- The structure map of a reindexed module is the original structure map at the mapped
inequality. -/
@[simp]
theorem structureMap_reindex {Q : Type x} [Preorder Q] (u : Q →o P)
    (M : PModule.{u,v,w} R P) {q₁ q₂ : Q} (h : q₁ ≤ q₂) :
    structureMap (reindex u M) h = structureMap M (u.monotone' h) := rfl

/-- The underlying linear structure map is preserved by reindexing. -/
@[simp]
theorem structureMapLinear_reindex {Q : Type x} [Preorder Q] (u : Q →o P)
    (M : PModule.{u,v,w} R P) {q₁ q₂ : Q} (h : q₁ ≤ q₂) :
    structureMapLinear (reindex u M) h = structureMapLinear M (u.monotone' h) := rfl

/-- Reindexing along the identity order hom is definitionally equal to the original module. -/
theorem reindex_id (M : PModule.{u,v,w} R P) :
    reindex (OrderHom.id : P →o P) M = M := rfl

/-- Successive reindexing is definitionally equal to precomposition by the composite order hom.
-/
theorem reindex_comp {Q : Type x} [Preorder Q] {S : Type y} [Preorder S]
    (u : Q →o P) (v : S →o Q) (M : PModule.{u,v,w} R P) :
    reindex v (reindex u M) = reindex (u.comp v) M := rfl

/-- Reindex a natural transformation by left whiskering with the indexing functor. -/
def reindexNatTrans {Q : Type x} [Preorder Q] (u : Q →o P)
    {M N : PModule.{u,v,w} R P} (α : M ⟶ N) : reindex u M ⟶ reindex u N :=
  Functor.whiskerLeft u.toFunctor α

/-- The component of a reindexed natural transformation at `q` is the original component at
`u q`. -/
@[simp]
theorem reindexNatTrans_app {Q : Type x} [Preorder Q] (u : Q →o P)
    {M N : PModule.{u,v,w} R P} (α : M ⟶ N) (q : Q) :
    (reindexNatTrans u α).app q = α.app (u q) := rfl

/-- Reindexing preserves identity natural transformations. -/
@[simp]
theorem reindexNatTrans_id {Q : Type x} [Preorder Q] (u : Q →o P)
    (M : PModule.{u,v,w} R P) :
    reindexNatTrans u (𝟙 M) = 𝟙 (reindex u M) := by
  change Functor.whiskerLeft u.toFunctor (𝟙 M) = 𝟙 (u.toFunctor ⋙ M)
  rfl

/-- Reindexing preserves composition of natural transformations. -/
@[simp]
theorem reindexNatTrans_comp {Q : Type x} [Preorder Q]
    (u : Q →o P) {M N L : PModule.{u,v,w} R P} (α : M ⟶ N) (β : N ⟶ L) :
    reindexNatTrans u (α ≫ β) = reindexNatTrans u α ≫ reindexNatTrans u β := by
  change Functor.whiskerLeft u.toFunctor (α ≫ β) =
    Functor.whiskerLeft u.toFunctor α ≫ Functor.whiskerLeft u.toFunctor β
  rfl

/-! ### Two-stage regression diagrams -/

/-- On the `Fin 2` preorder, the off-diagonal structure map is zero and the self maps are identity.
The equality-based construction is intentionally limited to `Fin 2`. -/
def zeroTransitionDiagram (S : Type u) [Ring S] :
    PModule.{u,0,u} S (Fin 2) where
  obj _ := ModuleCat.of S S
  map {p q} _ := if p = q then 𝟙 (ModuleCat.of S S) else 0
  map_id p := by simp
  map_comp {p q r} f g := by
    have hpq : p ≤ q := leOfHom f
    have hqr : q ≤ r := leOfHom g
    fin_cases p <;> fin_cases q <;> fin_cases r <;> simp_all

/-- A zero-transition diagram over the integers. -/
def integerZeroTransition : PModule.{0,0,0} ℤ (Fin 2) :=
  zeroTransitionDiagram ℤ

/-- The integer two-stage example has zero as its `0 → 1` structure map. -/
theorem integerZeroTransition_map :
    structureMapLinear integerZeroTransition (show (0 : Fin 2) ≤ 1 by decide) = 0 := rfl

/-- The integer two-stage example has a nonidentity transition map. -/
theorem integerZeroTransition_nonidentity :
    structureMapLinear integerZeroTransition (show (0 : Fin 2) ≤ 1 by decide) ≠ LinearMap.id := by
  intro h
  have h₁ := congrArg (fun f : ℤ →ₗ[ℤ] ℤ => f 1) h
  change (0 : ℤ) = 1 at h₁
  exact zero_ne_one h₁

/-- A zero-transition diagram over the field `ZMod 2`. -/
def zmodTwoZeroTransition : PModule.{0,0,0} (ZMod 2) (Fin 2) :=
  zeroTransitionDiagram (ZMod 2)

/-- The `ZMod 2` two-stage example has zero as its `0 → 1` structure map. -/
theorem zmodTwoZeroTransition_map :
    structureMapLinear zmodTwoZeroTransition (show (0 : Fin 2) ≤ 1 by decide) = 0 := rfl

/-- The `ZMod 2` two-stage example has a nonidentity transition map. -/
theorem zmodTwoZeroTransition_nonidentity :
    structureMapLinear zmodTwoZeroTransition (show (0 : Fin 2) ≤ 1 by decide) ≠ LinearMap.id := by
  intro h
  have h₁ := congrArg (fun f : ZMod 2 →ₗ[ZMod 2] ZMod 2 => f 1) h
  change (0 : ZMod 2) = 1 at h₁
  exact zero_ne_one h₁

/-- On the same two-stage index, the identity diagram has identity as its transition map. -/
def identityTransitionDiagram (S : Type u) [Ring S] :
    PModule.{u,0,u} S (Fin 2) where
  obj _ := ModuleCat.of S S
  map _ := 𝟙 (ModuleCat.of S S)
  map_id _ := by simp
  map_comp _ _ := by simp

/-- The integer identity diagram has the identity `0 → 1` structure map. -/
theorem integerIdentityTransition_map :
    structureMap (identityTransitionDiagram ℤ)
      (show (0 : Fin 2) ≤ 1 by decide) = 𝟙 (ModuleCat.of ℤ ℤ) := rfl

end TDA.Persistence
