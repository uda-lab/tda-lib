import TDA.Reeb.Components
import TDA.Reeb.Quotient
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.Topology.Category.TopCat.Basic

/-!
# The Reeb quotient functor and its comparison with path components

A continuous `h : C(X, Z)` with `g ∘ h = f`, height-preserving over an arbitrary topological
target `Y`, induces `Q_h = ReebQuotient.map h comm : C(Q_f, Q_g)`. It is the unique continuous
map with `Q_h ∘ q_f = q_g ∘ h`, it satisfies `ḡ ∘ Q_h = f̄`, and it preserves identities and
composition. The carrier universes of `X`, `Y` and `Z` are independent.

The comparison `η_f = ReebQuotient.componentComparison f : C_f ⟶ C_{f̄}` is #24's
`componentNatTrans` applied to `q_f`. It is natural in the open set and in `h`, and it is
surjective on every open. It need not be injective: de Silva, Munch and Patel, Example 3.21,
give a non-constructible space where it is not (source-established, not machine-checked here).
No injectivity or isomorphism is claimed.

On the slice category `Over (TopCat.of Y)`, `ReebQuotient.quotientFunctor Y` with the point
`ReebQuotient.projNatTrans Y : 𝟭 ⟶ quotientFunctor Y` is the pointed endofunctor of the source;
idempotence is not claimed. `ReebQuotient.componentFunctorOver Y` packages path components over
`Y`, and `ReebQuotient.componentComparisonOver Y` is `η` as a natural transformation
`C ⟶ Q ⋙ C`. `TopCat.{u}` places `Y` and every carrier of the slice packaging in one universe
`u`; the real-valued case is `u = 0`.

Source: de Silva, Munch and Patel, *Categorified Reeb Graphs*, Proposition 2.10,
Observation 2.11, §3.4 and the proof of Theorem 3.17; see
`docs/math/reeb-quotient-comparison.md`.
-/

open CategoryTheory

universe u v w

namespace TDA.Reeb

section map

variable {X : Type u} {Y : Type v} {Z : Type w}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- A height-preserving map respects the Reeb relation: compose the constant-value path. -/
theorem ReebRel.map {f : C(X, Y)} {g : C(Z, Y)} (h : C(X, Z)) (comm : ∀ x, g (h x) = f x)
    {x x' : X} (hr : ReebRel f x x') : ReebRel g (h x) (h x') := by
  obtain ⟨γ, hγ⟩ := hr
  exact ⟨γ.map h.continuous, fun t => by simp [comm, hγ]⟩

namespace ReebQuotient

/-- `Q_h : Q_f → Q_g`, the descent of `q_g ∘ h` (DMP Prop. 2.10). Carrier universes are
independent. -/
def map {f : C(X, Y)} {g : C(Z, Y)} (h : C(X, Z)) (comm : ∀ x, g (h x) = f x) :
    C(ReebQuotient f, ReebQuotient g) :=
  lift ((proj g).comp h) fun _ _ hr => (mk_eq_mk_iff g).2 (hr.map h comm)

@[simp]
theorem map_mk {f : C(X, Y)} {g : C(Z, Y)} (h : C(X, Z)) (comm : ∀ x, g (h x) = f x) (x : X) :
    map h comm (mk f x) = mk g (h x) := rfl

/-- `Q_h ∘ q_f = q_g ∘ h`. -/
theorem map_comp_proj {f : C(X, Y)} {g : C(Z, Y)} (h : C(X, Z)) (comm : ∀ x, g (h x) = f x) :
    (map h comm).comp (proj f) = (proj g).comp h := rfl

/-- `Q_h` is the unique continuous map with `Q_h ∘ q_f = q_g ∘ h`. -/
theorem map_unique {f : C(X, Y)} {g : C(Z, Y)} (h : C(X, Z)) (comm : ∀ x, g (h x) = f x)
    (k : C(ReebQuotient f, ReebQuotient g)) (hk : ∀ x, k (mk f x) = mk g (h x)) :
    k = map h comm :=
  hom_ext hk

/-- `ḡ ∘ Q_h = f̄`: `Q_h` is height-preserving. -/
@[simp]
theorem height_map_apply {f : C(X, Y)} {g : C(Z, Y)} (h : C(X, Z)) (comm : ∀ x, g (h x) = f x)
    (q : ReebQuotient f) : height g (map h comm q) = height f q := by
  induction q using ReebQuotient.ind with
  | h x => exact comm x

theorem height_comp_map {f : C(X, Y)} {g : C(Z, Y)} (h : C(X, Z)) (comm : ∀ x, g (h x) = f x) :
    (height g).comp (map h comm) = height f :=
  ContinuousMap.ext (height_map_apply h comm)

theorem map_id (f : C(X, Y)) (comm : ∀ x, f (ContinuousMap.id X x) = f x) :
    map (ContinuousMap.id X) comm = ContinuousMap.id (ReebQuotient f) :=
  hom_ext fun _ => rfl

theorem map_comp {W : Type*} [TopologicalSpace W] {f : C(X, Y)} {g : C(Z, Y)} {e : C(W, Y)}
    (h : C(X, Z)) (hh : ∀ x, g (h x) = f x) (k : C(Z, W)) (hk : ∀ z, e (k z) = g z)
    (hkh : ∀ x, e ((k.comp h) x) = f x) :
    map (k.comp h) hkh = (map k hk).comp (map h hh) :=
  hom_ext fun _ => rfl

theorem map_surjective {f : C(X, Y)} {g : C(Z, Y)} (h : C(X, Z)) (comm : ∀ x, g (h x) = f x)
    (hs : Function.Surjective h) : Function.Surjective (map h comm) := by
  intro q
  induction q using ReebQuotient.ind with
  | h z =>
    obtain ⟨x, rfl⟩ := hs z
    exact ⟨mk f x, rfl⟩

end ReebQuotient

end map

/-! ## The comparison `η_f : C_f ⟶ C_{f̄}` -/

section comparison

variable {X Z : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Z]
  [TopologicalSpace Y]

namespace ReebQuotient

/-- `η_f : C_f ⟶ C_{f̄}`, #24's `componentNatTrans` applied to `q_f` (`f̄ ∘ q_f = f`). It sends
the class of `x` in `f ⁻¹ U` to the class of `q_f x` in `f̄ ⁻¹ U`. It is surjective on every open
(`componentComparison_app_surjective`) but need not be injective: de Silva–Munch–Patel,
Example 3.21 (source-established, not machine-checked here). -/
def componentComparison (f : C(X, Y)) : componentFunctor f ⟶ componentFunctor (height f) :=
  componentNatTrans (proj f) (fun _ => rfl)

/-- Representative formula for `η`. -/
@[simp]
theorem componentComparison_app_mk (f : C(X, Y)) (U : TopologicalSpace.Opens Y)
    (x : {x : X // f x ∈ U}) :
    (componentComparison f).app U (ZerothHomotopy.mk x) =
      ZerothHomotopy.mk (⟨mk f x.1, x.2⟩ : {q : ReebQuotient f // height f q ∈ U}) := rfl

/-- Naturality in `U`, pointwise (the `NatTrans` field). -/
theorem componentComparison_naturality (f : C(X, Y)) {U V : TopologicalSpace.Opens Y}
    (i : U ⟶ V) :
    (componentFunctor f).map i ≫ (componentComparison f).app V =
      (componentComparison f).app U ≫ (componentFunctor (height f)).map i :=
  (componentComparison f).naturality i

/-- Naturality in the height-preserving map `h`: `C_h ≫ η_g = η_f ≫ C_{Q_h}`. -/
theorem componentComparison_natural {f : C(X, Y)} {g : C(Z, Y)} (h : C(X, Z))
    (comm : ∀ x, g (h x) = f x) :
    componentNatTrans h comm ≫ componentComparison g =
      componentComparison f ≫ componentNatTrans (map h comm) (height_map_apply h comm) := by
  ext U c
  induction c using ZerothHomotopy.rec with
  | mk x => rfl

/-- `η_f` is surjective on every open: every point of `f̄ ⁻¹ U` is `q_f x` with `f x ∈ U`. -/
theorem componentComparison_app_surjective (f : C(X, Y)) (U : TopologicalSpace.Opens Y) :
    Function.Surjective ((componentComparison f).app U) := by
  intro c
  induction c using ZerothHomotopy.rec with
  | mk q =>
    obtain ⟨q, hq⟩ := q
    obtain ⟨x, rfl⟩ := mk_surjective f q
    exact ⟨ZerothHomotopy.mk ⟨x, hq⟩, rfl⟩

end ReebQuotient

end comparison

/-! ## Slice-category packaging (forces `Y` into the carrier universe) -/

section overBase

/-- The structure map of an object over `Y` as a bundled continuous map. -/
def overBaseMap {Y : Type u} [TopologicalSpace Y] (A : Over (TopCat.of Y)) : C(A.left, Y) :=
  A.hom.hom

theorem overBaseMap_comm {Y : Type u} [TopologicalSpace Y] {A B : Over (TopCat.of Y)}
    (φ : A ⟶ B) (x : A.left) : overBaseMap B (φ.left.hom x) = overBaseMap A x := by
  rw [overBaseMap, overBaseMap, ← Over.w φ]
  rfl

end overBase

namespace ReebQuotient

section over

variable (Y : Type u) [TopologicalSpace Y]

/-- `(Q_f, f̄)` as an object over `Y`. -/
def toOver {Y : Type u} [TopologicalSpace Y] {X : Type u} [TopologicalSpace X] (f : C(X, Y)) :
    Over (TopCat.of Y) :=
  Over.mk (TopCat.ofHom (height f))

/-- `q_f` as a morphism over `Y`. -/
def projOver {Y : Type u} [TopologicalSpace Y] {X : Type u} [TopologicalSpace X] (f : C(X, Y)) :
    Over.mk (TopCat.ofHom f) ⟶ toOver f :=
  Over.homMk (TopCat.ofHom (proj f)) (by ext x; rfl)

/-- The quotient endofunctor of spaces over `Y`. -/
def quotientFunctor : Over (TopCat.of Y) ⥤ Over (TopCat.of Y) where
  obj A := toOver (overBaseMap A)
  map {A B} φ := Over.homMk (TopCat.ofHom (map φ.left.hom (overBaseMap_comm φ)))
    (by ext q; exact height_map_apply φ.left.hom (overBaseMap_comm φ) q)
  map_id A := by
    ext q
    induction q using ReebQuotient.ind with
    | h x => rfl
  map_comp φ ψ := by
    ext q
    induction q using ReebQuotient.ind with
    | h x => rfl

/-- The point `ρ : 𝟭 ⟶ Q` (DMP Prop. 2.10): `q_f` at each object. -/
def projNatTrans : 𝟭 (Over (TopCat.of Y)) ⟶ quotientFunctor Y where
  app A := Over.homMk (TopCat.ofHom (proj (overBaseMap A))) (by ext x; rfl)
  naturality A B φ := by
    ext x
    rfl

/-- Path components over `Y`, functorial in maps over `Y` (#24's `componentNatTrans`). -/
def componentFunctorOver : Over (TopCat.of Y) ⥤ (TopologicalSpace.Opens Y ⥤ Type u) where
  obj A := componentFunctor (overBaseMap A)
  map φ := componentNatTrans φ.left.hom (overBaseMap_comm φ)
  map_id A := by
    ext U c
    induction c using ZerothHomotopy.rec with
    | mk x => rfl
  map_comp φ ψ := by
    ext U c
    induction c using ZerothHomotopy.rec with
    | mk x => rfl

/-- `η` as a natural transformation `C ⟶ Q ⋙ C` of functors on spaces over `Y`. -/
def componentComparisonOver :
    componentFunctorOver Y ⟶ quotientFunctor Y ⋙ componentFunctorOver Y where
  app A := componentComparison (overBaseMap A)
  naturality A B φ := by
    ext U c
    induction c using ZerothHomotopy.rec with
    | mk x => rfl

end over

end ReebQuotient

end TDA.Reeb
