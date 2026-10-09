import Mathlib.Topology.Connected.PathConnected
import Mathlib.Topology.Sets.Opens
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Types.Basic

/-!
# Open-set path-component functors

For a continuous map `f : C(X, Y)` and an open set `U` of `Y`, `componentFunctor f` assigns
the path components `ZerothHomotopy {x : X // f x ∈ U}` of the inverse-image subtype with its
induced topology. Paths therefore stay inside the inverse image; these are neither connected
components nor ambient path components intersected with the inverse image. An inclusion
`U ≤ V` acts by sending the class of a point to the class of the same point in the larger
inverse image, giving a covariant functor `TopologicalSpace.Opens Y ⥤ Type u`.

A continuous map `h : C(X, Z)` with `g (h x) = f x` for every `x` restricts to every inverse
image and induces the natural transformation `componentNatTrans h comm : componentFunctor f ⟶
componentFunctor g`. The domains `X` and `Z` share the carrier universe `u`, so both functors
land in `Type u`; the base universe of `Y` is independent. The raw map `componentMap` on
`ZerothHomotopy` allows independent carrier universes.

No local path connectedness, compactness, finiteness, Hausdorffness or nonemptiness is
assumed. The construction follows de Silva–Munch–Patel, *Categorified Reeb Graphs*, §3.1
Example 3.3 and §3.4, generalized from open intervals of `ℝ` to all open sets of an arbitrary
topological space; see `docs/math/reeb-components.md`.
-/

open CategoryTheory

namespace TDA.Reeb

universe u v w

section componentMap

variable {X : Type u} {Z : Type w} {W : Type*}
  [TopologicalSpace X] [TopologicalSpace Z] [TopologicalSpace W]

/-- Path components are mapped by a continuous map (raw map; carrier universes independent). -/
def componentMap (h : C(X, Z)) : ZerothHomotopy X → ZerothHomotopy Z :=
  ZerothHomotopy.lift (fun x => ZerothHomotopy.mk (h x))
    (fun _ _ p => ZerothHomotopy.sound (p.map h.continuous))

@[simp]
theorem componentMap_mk (h : C(X, Z)) (x : X) :
    componentMap h (ZerothHomotopy.mk x) = ZerothHomotopy.mk (h x) := rfl

theorem componentMap_id : componentMap (ContinuousMap.id X) = id := by
  funext c
  induction c using ZerothHomotopy.rec with
  | mk x => rfl

theorem componentMap_comp (k : C(Z, W)) (h : C(X, Z)) :
    componentMap (k.comp h) = componentMap k ∘ componentMap h := by
  funext c
  induction c using ZerothHomotopy.rec with
  | mk x => rfl

end componentMap

section functor

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/-- The continuous inclusion `f ⁻¹ U → f ⁻¹ V` for `U ≤ V`. -/
def preimageInclusion (f : C(X, Y)) {U V : TopologicalSpace.Opens Y} (hUV : U ≤ V) :
    C({x : X // f x ∈ U}, {x : X // f x ∈ V}) where
  toFun x := ⟨x.1, hUV x.2⟩
  continuous_toFun := by fun_prop

/-- The inclusion coincides definitionally with mathlib's `ContinuousMap.inclusion` on the
inverse-image sets. -/
theorem preimageInclusion_eq_inclusion (f : C(X, Y)) {U V : TopologicalSpace.Opens Y}
    (hUV : U ≤ V) :
    preimageInclusion f hUV =
      ContinuousMap.inclusion (s := f ⁻¹' (U : Set Y)) (t := f ⁻¹' (V : Set Y))
        (fun _ hx => hUV hx) := rfl

/-- `U ↦ π₀ (f ⁻¹ U)`, covariant in inclusions of opens. -/
def componentFunctor (f : C(X, Y)) : TopologicalSpace.Opens Y ⥤ Type u where
  obj U := ZerothHomotopy {x : X // f x ∈ U}
  map {U V} i := TypeCat.ofHom (componentMap (preimageInclusion f (leOfHom i)))
  map_id U := by
    ext c
    induction c using ZerothHomotopy.rec with
    | mk x => rfl
  map_comp i j := by
    ext c
    induction c using ZerothHomotopy.rec with
    | mk x => rfl

theorem componentFunctor_obj (f : C(X, Y)) (U : TopologicalSpace.Opens Y) :
    (componentFunctor f).obj U = ZerothHomotopy {x : X // f x ∈ U} := rfl

@[simp]
theorem componentFunctor_map_mk (f : C(X, Y)) {U V : TopologicalSpace.Opens Y} (i : U ⟶ V)
    (x : {x : X // f x ∈ U}) :
    (componentFunctor f).map i (ZerothHomotopy.mk x) =
      ZerothHomotopy.mk (⟨x.1, leOfHom i x.2⟩ : {x : X // f x ∈ V}) := rfl

/-- Bridge: the functor action is `componentMap` of the preimage inclusion. -/
theorem componentFunctor_map_apply (f : C(X, Y)) {U V : TopologicalSpace.Opens Y} (i : U ⟶ V)
    (c : (componentFunctor f).obj U) :
    (componentFunctor f).map i c = componentMap (preimageInclusion f (leOfHom i)) c := rfl

/-- Bottom emptiness, for every `X` and `f`. -/
instance componentFunctor_obj_bot_isEmpty (f : C(X, Y)) :
    IsEmpty ((componentFunctor f).obj ⊥) :=
  ⟨fun c => by
    induction c using ZerothHomotopy.rec with
    | mk x => exact x.2⟩

/-- Empty domain: every value is empty. -/
theorem componentFunctor_obj_isEmpty_of_isEmpty [IsEmpty X] (f : C(X, Y))
    (U : TopologicalSpace.Opens Y) : IsEmpty ((componentFunctor f).obj U) :=
  ⟨fun c => by
    induction c using ZerothHomotopy.rec with
    | mk x => exact isEmptyElim x.1⟩

/-- Empty base, whenever a map into it exists. -/
theorem componentFunctor_obj_isEmpty_of_base_isEmpty [IsEmpty Y] (f : C(X, Y))
    (U : TopologicalSpace.Opens Y) : IsEmpty ((componentFunctor f).obj U) :=
  ⟨fun c => by
    induction c using ZerothHomotopy.rec with
    | mk x => exact isEmptyElim (f x.1)⟩

end functor

section natTrans

variable {X Z : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Z]
  [TopologicalSpace Y]

/-- Restriction of `h` to `f ⁻¹ U → g ⁻¹ U` under `g ∘ h = f`. -/
def preimageRestrict {f : C(X, Y)} {g : C(Z, Y)} (h : C(X, Z)) (comm : ∀ x, g (h x) = f x)
    (U : TopologicalSpace.Opens Y) : C({x : X // f x ∈ U}, {z : Z // g z ∈ U}) where
  toFun x := ⟨h x.1, by rw [comm]; exact x.2⟩
  continuous_toFun := by fun_prop

/-- The natural transformation `C_f ⟶ C_g` induced by `h` with `g ∘ h = f`.
`X` and `Z` share the carrier universe `u`; the base universe `v` is independent. -/
def componentNatTrans {f : C(X, Y)} {g : C(Z, Y)} (h : C(X, Z)) (comm : ∀ x, g (h x) = f x) :
    componentFunctor f ⟶ componentFunctor g where
  app U := TypeCat.ofHom (componentMap (preimageRestrict h comm U))
  naturality U V i := by
    ext c
    induction c using ZerothHomotopy.rec with
    | mk x => rfl

@[simp]
theorem componentNatTrans_app_mk {f : C(X, Y)} {g : C(Z, Y)} (h : C(X, Z))
    (comm : ∀ x, g (h x) = f x) (U : TopologicalSpace.Opens Y) (x : {x : X // f x ∈ U}) :
    (componentNatTrans h comm).app U (ZerothHomotopy.mk x) =
      ZerothHomotopy.mk (⟨h x.1, by rw [comm]; exact x.2⟩ : {z : Z // g z ∈ U}) := rfl

/-- Bridge: the component at `U` is `componentMap` of the restriction. -/
theorem componentNatTrans_app_apply {f : C(X, Y)} {g : C(Z, Y)} (h : C(X, Z))
    (comm : ∀ x, g (h x) = f x) (U : TopologicalSpace.Opens Y) (c : (componentFunctor f).obj U) :
    (componentNatTrans h comm).app U c = componentMap (preimageRestrict h comm U) c := rfl

/-- The naturality square, stated pointwise on representatives. -/
theorem componentNatTrans_naturality_mk {f : C(X, Y)} {g : C(Z, Y)} (h : C(X, Z))
    (comm : ∀ x, g (h x) = f x) {U V : TopologicalSpace.Opens Y} (i : U ⟶ V)
    (x : {x : X // f x ∈ U}) :
    (componentFunctor g).map i ((componentNatTrans h comm).app U (ZerothHomotopy.mk x)) =
      (componentNatTrans h comm).app V ((componentFunctor f).map i (ZerothHomotopy.mk x)) :=
  rfl

theorem componentNatTrans_naturality {f : C(X, Y)} {g : C(Z, Y)} (h : C(X, Z))
    (comm : ∀ x, g (h x) = f x) {U V : TopologicalSpace.Opens Y} (i : U ⟶ V) :
    (componentFunctor f).map i ≫ (componentNatTrans h comm).app V =
      (componentNatTrans h comm).app U ≫ (componentFunctor g).map i :=
  (componentNatTrans h comm).naturality i

theorem componentNatTrans_id (f : C(X, Y)) (comm : ∀ x, f (ContinuousMap.id X x) = f x) :
    componentNatTrans (ContinuousMap.id X) comm = 𝟙 (componentFunctor f) := by
  ext U c
  induction c using ZerothHomotopy.rec with
  | mk x => rfl

theorem componentNatTrans_comp {W : Type u} [TopologicalSpace W] {f : C(X, Y)} {g : C(Z, Y)}
    {e : C(W, Y)} (h : C(X, Z)) (hh : ∀ x, g (h x) = f x) (k : C(Z, W))
    (hk : ∀ z, e (k z) = g z) (hkh : ∀ x, e ((k.comp h) x) = f x) :
    componentNatTrans (k.comp h) hkh = componentNatTrans h hh ≫ componentNatTrans k hk := by
  ext U c
  induction c using ZerothHomotopy.rec with
  | mk x => rfl

/-- Pointwise composite equation on representatives. -/
theorem componentNatTrans_comp_app_mk {W : Type u} [TopologicalSpace W] {f : C(X, Y)}
    {g : C(Z, Y)} {e : C(W, Y)} (h : C(X, Z)) (hh : ∀ x, g (h x) = f x) (k : C(Z, W))
    (hk : ∀ z, e (k z) = g z) (U : TopologicalSpace.Opens Y) (x : {x : X // f x ∈ U}) :
    (componentNatTrans k hk).app U ((componentNatTrans h hh).app U (ZerothHomotopy.mk x)) =
      ZerothHomotopy.mk (⟨k (h x.1), by rw [hk, hh]; exact x.2⟩ : {w : W // e w ∈ U}) := rfl

/-- The map does not depend on the commuting-equation proof. -/
theorem componentNatTrans_proof_irrel {f : C(X, Y)} {g : C(Z, Y)} (h : C(X, Z))
    (comm comm' : ∀ x, g (h x) = f x) :
    componentNatTrans h comm = componentNatTrans h comm' := rfl

end natTrans

end TDA.Reeb
