import TDA.Persistence.Interval
import Mathlib.CategoryTheory.PathCategory.Basic
import Mathlib.CategoryTheory.Preadditive.FunctorCategory
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
import Mathlib.CategoryTheory.Limits.FunctorCategory.BinaryBiproducts
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.LinearAlgebra.Projection

/-!
# Finite alternating diagrams

An orientation `o : Fin n → Bool` of the path with vertices `Fin (n + 1)` points arrow `a`
from `a.castSucc` to `a.succ` when `o a = true` and from `a.succ` to `a.castSucc` otherwise.
A diagram is a functor from the free category on this quiver to `k`-vector spaces, so it is
given by one linear map per arrow and no relations. Intervals are the library's
`FiniteInterval (n + 1)` read as segments `[birth, death - 1]` of the path; the interval
diagram has the field on the segment and zero elsewhere.

This file supplies constructors from generators, subdiagrams, a criterion for a diagram to be
isomorphic to an interval diagram, the internal direct sum of complementary subdiagrams, and
finite interval sums as iterated biproducts together with their dimension vectors.
-/

universe u

namespace TDA.Sheaf.AlternatingDiagram

open CategoryTheory Limits TDA.Persistence
open ZeroObject

variable {n : ℕ}

/-- The source of arrow `a`. -/
def src (o : Fin n → Bool) (a : Fin n) : Fin (n + 1) := if o a then a.castSucc else a.succ

/-- The target of arrow `a`. -/
def tgt (o : Fin n → Bool) (a : Fin n) : Fin (n + 1) := if o a then a.succ else a.castSucc

/-- There is an arrow from `i` to `j`. -/
def Arrow (o : Fin n → Bool) (i j : Fin (n + 1)) : Prop := ∃ a, src o a = i ∧ tgt o a = j

instance arrowDecidableRel (o : Fin n → Bool) : DecidableRel (Arrow o) := fun i j => by
  unfold Arrow; infer_instance

/-- An arrow joins adjacent vertices. -/
theorem Arrow.adjacent {o : Fin n → Bool} {i j : Fin (n + 1)} (h : Arrow o i j) :
    i.val + 1 = j.val ∨ j.val + 1 = i.val := by
  obtain ⟨a, rfl, rfl⟩ := h
  unfold src tgt
  cases o a <;> simp

/-- Adjacent vertices are joined by exactly one arrow, in one of the two directions. -/
theorem arrow_or_arrow (o : Fin n → Bool) {i j : Fin (n + 1)}
    (h : i.val + 1 = j.val ∨ j.val + 1 = i.val) : Arrow o i j ∨ Arrow o j i := by
  rcases h with h | h
  · have hi : i.val < n := by omega
    have hc : (⟨i.val, hi⟩ : Fin n).castSucc = i := Fin.ext rfl
    have hs : (⟨i.val, hi⟩ : Fin n).succ = j := Fin.ext (by simp [h])
    cases ho : o ⟨i.val, hi⟩
    · exact Or.inr ⟨⟨i.val, hi⟩, by simp [src, ho, hs], by simp [tgt, ho, hc]⟩
    · exact Or.inl ⟨⟨i.val, hi⟩, by simp [src, ho, hc], by simp [tgt, ho, hs]⟩
  · have hj : j.val < n := by omega
    have hc : (⟨j.val, hj⟩ : Fin n).castSucc = j := Fin.ext rfl
    have hs : (⟨j.val, hj⟩ : Fin n).succ = i := Fin.ext (by simp [h])
    cases ho : o ⟨j.val, hj⟩
    · exact Or.inl ⟨⟨j.val, hj⟩, by simp [src, ho, hs], by simp [tgt, ho, hc]⟩
    · exact Or.inr ⟨⟨j.val, hj⟩, by simp [src, ho, hc], by simp [tgt, ho, hs]⟩

/-- No vertex has arrows in both directions to the same neighbour. -/
theorem Arrow.not_symm {o : Fin n → Bool} {i j : Fin (n + 1)} (h : Arrow o i j) :
    ¬ Arrow o j i := by
  rintro ⟨b, hb, hb'⟩
  obtain ⟨a, rfl, rfl⟩ := h
  have hab : a = b := by
    unfold src tgt at *
    apply Fin.ext
    cases ha : o a <;> cases hb2 : o b <;> simp_all [Fin.ext_iff] <;> omega
  subst hab
  unfold src tgt at *
  cases ha : o a <;> simp_all [Fin.ext_iff]

/-- No arrow is a loop. -/
theorem Arrow.ne {o : Fin n → Bool} {i j : Fin (n + 1)} (h : Arrow o i j) : i ≠ j := by
  rintro rfl
  rcases h.adjacent with h | h <;> omega

/-- The vertices of the oriented path, as a quiver with one arrow per edge. -/
def Vertex (_o : Fin n → Bool) : Type := Fin (n + 1)

instance vertexQuiver (o : Fin n → Bool) : Quiver (Vertex o) := ⟨fun i j => PLift (Arrow o i j)⟩

/-- Diagrams of `k`-vector spaces on the oriented path: functors from its free category. -/
abbrev Diagram (k : Type u) [Field k] (o : Fin n → Bool) :=
  Paths (Vertex o) ⥤ ModuleCat.{u} k

/-- The vertex `j` as an object of the free category. -/
def vtx (o : Fin n → Bool) (j : Fin (n + 1)) : Paths (Vertex o) := j

/-- The generating morphism of the free category attached to an arrow. -/
def gen {o : Fin n → Bool} {i j : Fin (n + 1)} (h : Arrow o i j) : vtx o i ⟶ vtx o j :=
  (Paths.of (Vertex o)).map (V := Vertex o) (X := i) (Y := j) (⟨h⟩ : PLift (Arrow o i j))

variable {k : Type u} [Field k] {o : Fin n → Bool}

/-- To check a property of all morphisms of the free category it suffices to check identities
and composites with generators. -/
theorem natural_of_gen {F G : Diagram k o}
    (app : ∀ X : Paths (Vertex o), F.obj X ⟶ G.obj X)
    (w : ∀ {i j : Fin (n + 1)} (h : Arrow o i j),
      F.map (gen h) ≫ app (vtx o j) = app (vtx o i) ≫ G.map (gen h))
    {X Y : Paths (Vertex o)} (f : X ⟶ Y) :
    F.map f ≫ app Y = app X ≫ G.map f := by
  induction f using Paths.induction with
  | id => erw [F.map_id, G.map_id, Category.id_comp]
  | @comp a b c p q ih =>
    have hq := w q.down
    erw [F.map_comp, G.map_comp, Category.assoc, hq, ← Category.assoc, ih, Category.assoc]

/-- A natural transformation of diagrams from components commuting with the generators. -/
def homMk {F G : Diagram k o} (app : ∀ X : Paths (Vertex o), F.obj X ⟶ G.obj X)
    (w : ∀ {i j : Fin (n + 1)} (h : Arrow o i j),
      F.map (gen h) ≫ app (vtx o j) = app (vtx o i) ≫ G.map (gen h)) : F ⟶ G where
  app := app
  naturality _ _ f := natural_of_gen app w f

@[simp]
theorem homMk_app {F G : Diagram k o} (app : ∀ X : Paths (Vertex o), F.obj X ⟶ G.obj X) (w)
    (X : Paths (Vertex o)) : (homMk app w).app X = app X := rfl

/-- A natural isomorphism of diagrams from componentwise isomorphisms commuting with the
generators. -/
def isoMk {F G : Diagram k o} (app : ∀ X : Paths (Vertex o), F.obj X ≅ G.obj X)
    (w : ∀ {i j : Fin (n + 1)} (h : Arrow o i j),
      F.map (gen h) ≫ (app (vtx o j)).hom = (app (vtx o i)).hom ≫ G.map (gen h)) : F ≅ G :=
  NatIso.ofComponents app (fun f => natural_of_gen (fun X => (app X).hom) w f)

@[simp]
theorem isoMk_hom_app {F G : Diagram k o} (app : ∀ X : Paths (Vertex o), F.obj X ≅ G.obj X) (w)
    (X : Paths (Vertex o)) : (isoMk app w).hom.app X = (app X).hom := rfl

/-- The linear map of a diagram along an arrow, and zero between vertices that are not joined
by an arrow in this direction. -/
noncomputable def arr (M : Diagram k o) (i j : Fin (n + 1)) :
    M.obj (vtx o i) →ₗ[k] M.obj (vtx o j) := by
  classical
  exact if h : Arrow o i j then (M.map (gen h)).hom else 0

theorem arr_of_arrow (M : Diagram k o) {i j : Fin (n + 1)} (h : Arrow o i j) :
    arr M i j = (M.map (gen h)).hom := by
  classical
  simp [arr, h]

theorem arr_of_not_arrow (M : Diagram k o) {i j : Fin (n + 1)} (h : ¬ Arrow o i j) :
    arr M i j = 0 := by
  classical
  simp [arr, h]

/-- Components of a morphism of diagrams commute with `arr`. -/
theorem arr_naturality {M N : Diagram k o} (φ : M ⟶ N) (i j : Fin (n + 1))
    (x : M.obj (vtx o i)) :
    arr N i j ((φ.app (vtx o i)).hom x) = (φ.app (vtx o j)).hom (arr M i j x) := by
  classical
  by_cases h : Arrow o i j
  · rw [arr_of_arrow _ h, arr_of_arrow _ h]
    exact (congrArg (fun g => g.hom x) (φ.naturality (gen h))).symm
  · simp [arr_of_not_arrow _ h]

/-- A diagram from vertex spaces and one linear map for each arrow. -/
def ofArrows (V : Fin (n + 1) → ModuleCat.{u} k)
    (f : ∀ {i j : Fin (n + 1)}, Arrow o i j → (V i ⟶ V j)) : Diagram k o :=
  Paths.lift
    { obj := V
      map := fun {i j} e => f (i := i) (j := j) e.down }

@[simp]
theorem ofArrows_obj (V : Fin (n + 1) → ModuleCat.{u} k)
    (f : ∀ {i j : Fin (n + 1)}, Arrow o i j → (V i ⟶ V j)) (j : Fin (n + 1)) :
    (ofArrows V f).obj (vtx o j) = V j := rfl

@[simp]
theorem ofArrows_map_gen (V : Fin (n + 1) → ModuleCat.{u} k)
    (f : ∀ {i j : Fin (n + 1)}, Arrow o i j → (V i ⟶ V j)) {i j : Fin (n + 1)}
    (h : Arrow o i j) : (ofArrows V f).map (gen h) = f h := by
  unfold ofArrows gen
  exact Paths.lift_toPath _ _

/-! ### Interval diagrams -/

/-- The transition between interval fibres: the identity of the field when both vertices lie in
the interval, and zero otherwise. -/
def fiberMap (J : FiniteInterval (n + 1)) (i j : Fin (n + 1)) :
    J.fiber (k := k) i →ₗ[k] J.fiber (k := k) j :=
  if h : J.alive i ∧ J.alive j then
    Submodule.inclusion (by simp [FiniteInterval.fiber, h.1, h.2]) else 0

theorem fiberMap_val (J : FiniteInterval (n + 1)) (i j : Fin (n + 1))
    (x : J.fiber (k := k) i) :
    (fiberMap J i j x : k) = if J.alive i ∧ J.alive j then (x : k) else 0 := by
  by_cases h : J.alive i ∧ J.alive j <;> simp [fiberMap, h]

/-- A fibre element outside the interval is zero. -/
theorem fiber_val_eq_zero {J : FiniteInterval (n + 1)} {j : Fin (n + 1)} (hj : ¬ J.alive j)
    (x : J.fiber (k := k) j) : (x : k) = 0 := by
  simpa [FiniteInterval.fiber, hj] using x.property

/-- The interval diagram: the field on the segment `[J.birth, J.death - 1]`, zero elsewhere,
identity maps along arrows inside the segment. -/
def interval (o : Fin n → Bool) (J : FiniteInterval (n + 1)) : Diagram k o :=
  ofArrows (fun j => ModuleCat.of k (J.fiber (k := k) j))
    (fun {i j} _ => ModuleCat.ofHom (fiberMap J i j))

/-- A diagram is isomorphic to an interval diagram when it has a spanning vector at each vertex,
nonzero exactly on the interval, and the arrows inside the interval match these vectors. -/
noncomputable def intervalIso (D : Diagram k o) (J : FiniteInterval (n + 1))
    (v : ∀ j : Fin (n + 1), D.obj (vtx o j))
    (hspan : ∀ (j : Fin (n + 1)) (x : D.obj (vtx o j)), ∃ c : k, x = c • v j)
    (hne : ∀ j, J.alive j → v j ≠ 0) (hzero : ∀ j, ¬ J.alive j → v j = 0)
    (harr : ∀ {i j : Fin (n + 1)} (h : Arrow o i j), J.alive i → J.alive j →
      (D.map (gen h)).hom (v i) = v j) :
    interval (k := k) o J ≅ D := by
  classical
  let φ : ∀ j : Fin (n + 1), J.fiber (k := k) j →ₗ[k] D.obj (vtx o j) := fun j =>
    (J.fiber (k := k) j).subtype.smulRight (v j)
  have hφ : ∀ j x, φ j x = (x : k) • v j := fun _ _ => rfl
  have hb : ∀ j, Function.Bijective (φ j) := by
    intro j
    constructor
    · rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
      intro x hx
      rw [LinearMap.mem_ker, hφ] at hx
      apply Subtype.ext
      by_cases hj : J.alive j
      · exact (smul_eq_zero.mp hx).resolve_right (hne j hj)
      · exact fiber_val_eq_zero hj x
    · intro y
      obtain ⟨c, rfl⟩ := hspan j y
      by_cases hj : J.alive j
      · exact ⟨⟨c, by simp [FiniteInterval.fiber, hj]⟩, rfl⟩
      · exact ⟨0, by simp [hφ, hzero j hj]⟩
  refine isoMk (fun X => (LinearEquiv.ofBijective (φ X) (hb X)).toModuleIso) ?_
  intro i j h
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  let y : J.fiber (k := k) i := x
  change ((fiberMap J i j y : k)) • v j = (D.map (gen h)).hom ((y : k) • v i)
  rw [fiberMap_val, map_smul]
  by_cases hi : J.alive i
  · by_cases hj : J.alive j
    · simp [hi, hj, harr h hi hj]
    · obtain ⟨c, hc⟩ := hspan j ((D.map (gen h)).hom (v i))
      rw [hzero j hj, smul_zero] at hc
      simp [hi, hj, hc]
  · rw [fiber_val_eq_zero hi y]
    simp [hi]

/-! ### Subdiagrams and internal direct sums -/

/-- The subdiagram on a family of subspaces stable under all arrows. -/
def sub (M : Diagram k o) (A : ∀ j : Fin (n + 1), Submodule k (M.obj (vtx o j)))
    (hA : ∀ {i j : Fin (n + 1)} (h : Arrow o i j), A i ≤ (A j).comap (M.map (gen h)).hom) :
    Diagram k o :=
  ofArrows (fun j => ModuleCat.of k (A j))
    (fun {_ _} h => ModuleCat.ofHom ((M.map (gen h)).hom.restrict (hA h)))

/-- The inclusion of a subdiagram. -/
def subι (M : Diagram k o) (A : ∀ j : Fin (n + 1), Submodule k (M.obj (vtx o j))) (hA) :
    sub M A hA ⟶ M :=
  homMk (fun X => ModuleCat.ofHom (A X).subtype) (fun h => by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl)

/-- Projection onto a stable subspace along a stable complement commutes with the arrows. -/
theorem projectionOnto_map (M : Diagram k o)
    (A B : ∀ j : Fin (n + 1), Submodule k (M.obj (vtx o j)))
    (hA : ∀ {i j : Fin (n + 1)} (h : Arrow o i j), A i ≤ (A j).comap (M.map (gen h)).hom)
    (hB : ∀ {i j : Fin (n + 1)} (h : Arrow o i j), B i ≤ (B j).comap (M.map (gen h)).hom)
    (hc : ∀ j, IsCompl (A j) (B j)) {i j : Fin (n + 1)} (h : Arrow o i j)
    (x : M.obj (vtx o i)) :
    Submodule.projectionOnto (A j) (B j) (hc j) ((M.map (gen h)).hom x) =
      (M.map (gen h)).hom.restrict (hA h)
        (Submodule.projectionOnto (A i) (B i) (hc i) x) := by
  obtain ⟨a, ha, b, hb, rfl⟩ : ∃ a ∈ A i, ∃ b ∈ B i, a + b = x :=
    Submodule.mem_sup.mp ((hc i).sup_eq_top ▸ Submodule.mem_top)
  apply Subtype.ext
  have ha' : (M.map (gen h)).hom a ∈ A j := hA h ha
  have hb' : (M.map (gen h)).hom b ∈ B j := hB h hb
  rw [map_add, map_add, map_add, Submodule.projectionOnto_apply_of_mem_left _ ha',
    Submodule.projectionOnto_apply_of_mem_right _ hb',
    Submodule.projectionOnto_apply_of_mem_left _ ha,
    Submodule.projectionOnto_apply_of_mem_right _ hb]
  simp

/-- A diagram is the biproduct of the subdiagrams on two stable families of complementary
subspaces. -/
noncomputable def isoBiprodOfIsCompl (M : Diagram k o)
    (A B : ∀ j : Fin (n + 1), Submodule k (M.obj (vtx o j)))
    (hA : ∀ {i j : Fin (n + 1)} (h : Arrow o i j), A i ≤ (A j).comap (M.map (gen h)).hom)
    (hB : ∀ {i j : Fin (n + 1)} (h : Arrow o i j), B i ≤ (B j).comap (M.map (gen h)).hom)
    (hc : ∀ j, IsCompl (A j) (B j)) : M ≅ sub M A hA ⊞ sub M B hB := by
  let fst : M ⟶ sub M A hA :=
    homMk (fun X => ModuleCat.ofHom (Submodule.projectionOnto (A X) (B X) (hc X))) (fun h => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      exact projectionOnto_map M A B hA hB hc h x)
  let snd : M ⟶ sub M B hB :=
    homMk (fun X => ModuleCat.ofHom (Submodule.projectionOnto (B X) (A X) (hc X).symm))
      (fun h => by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        exact projectionOnto_map M B A hB hA (fun j => (hc j).symm) h x)
  let b : BinaryBicone (sub M A hA) (sub M B hB) :=
    { pt := M
      fst := fst
      snd := snd
      inl := subι M A hA
      inr := subι M B hB
      inl_fst := by
        ext X x
        exact Submodule.projectionOnto_apply_left (hc X) x
      inl_snd := by
        ext X x
        exact Submodule.projectionOnto_apply_right (hc X).symm x
      inr_fst := by
        ext X x
        exact Submodule.projectionOnto_apply_right (hc X) x
      inr_snd := by
        ext X x
        exact Submodule.projectionOnto_apply_left (hc X).symm x }
  refine biprod.uniqueUpToIso _ _ (b := b) (isBinaryBilimitOfTotal b ?_)
  ext X x
  exact Submodule.projection_add_projection_eq_self (hc X) x

/-! ### Finite interval sums and dimension vectors -/

/-- The fibre of a biproduct of diagrams is the product of the fibres. -/
noncomputable def biprodObjLinearEquiv (A B : Diagram k o) (X : Paths (Vertex o)) :
    (A ⊞ B).obj X ≃ₗ[k] A.obj X × B.obj X :=
  haveI := preservesBinaryBiproducts_of_preservesBiproducts
    ((evaluation (Paths (Vertex o)) (ModuleCat.{u} k)).obj X)
  ((((evaluation (Paths (Vertex o)) (ModuleCat.{u} k)).obj X).mapBiprod A B) ≪≫
    ModuleCat.biprodIsoProd _ _).toLinearEquiv

instance biprod_finiteDimensional (A B : Diagram k o) (X : Paths (Vertex o))
    [FiniteDimensional k (A.obj X)] [FiniteDimensional k (B.obj X)] :
    FiniteDimensional k ((A ⊞ B).obj X) :=
  LinearEquiv.finiteDimensional (biprodObjLinearEquiv A B X).symm

theorem finrank_biprod_obj (A B : Diagram k o) (X : Paths (Vertex o))
    [FiniteDimensional k (A.obj X)] [FiniteDimensional k (B.obj X)] :
    Module.finrank k ((A ⊞ B).obj X) =
      Module.finrank k (A.obj X) + Module.finrank k (B.obj X) := by
  rw [(biprodObjLinearEquiv A B X).finrank_eq, Module.finrank_prod]

instance interval_finiteDimensional (J : FiniteInterval (n + 1)) (X : Paths (Vertex o)) :
    FiniteDimensional k ((interval (k := k) o J).obj X) := by
  change FiniteDimensional k (J.fiber (k := k) X)
  infer_instance

/-- An interval diagram has dimension one on its segment and zero elsewhere. -/
theorem finrank_interval_obj (J : FiniteInterval (n + 1)) (j : Fin (n + 1)) :
    Module.finrank k ((interval (k := k) o J).obj (vtx o j)) = if J.alive j then 1 else 0 := by
  change Module.finrank k (J.fiber (k := k) j) = _
  by_cases hj : J.alive j
  · rw [show J.fiber (k := k) j = ⊤ by simp [FiniteInterval.fiber, hj], finrank_top,
      Module.finrank_self]
    simp [hj]
  · rw [show J.fiber (k := k) j = ⊥ by simp [FiniteInterval.fiber, hj], finrank_bot]
    simp [hj]

instance zero_finiteDimensional (X : Paths (Vertex o)) :
    FiniteDimensional k ((0 : Diagram k o).obj X) := by
  have : Subsingleton ((0 : Diagram k o).obj X) :=
    ModuleCat.subsingleton_of_isZero ((isZero_zero (Diagram k o)).obj X)
  infer_instance

/-- The diagram of a list of intervals: the iterated biproduct of the interval diagrams. -/
noncomputable def intervalSum (o : Fin n → Bool) : List (FiniteInterval (n + 1)) → Diagram k o
  | [] => 0
  | J :: xs => interval o J ⊞ intervalSum o xs

@[simp]
theorem intervalSum_nil : intervalSum (k := k) o [] = 0 := rfl

@[simp]
theorem intervalSum_cons (J : FiniteInterval (n + 1)) (xs : List (FiniteInterval (n + 1))) :
    intervalSum (k := k) o (J :: xs) = (interval o J ⊞ intervalSum o xs) := rfl

theorem isZero_intervalSum_nil : IsZero (intervalSum (k := k) o []) := isZero_zero (Diagram k o)

instance intervalSum_finiteDimensional (xs : List (FiniteInterval (n + 1)))
    (X : Paths (Vertex o)) : FiniteDimensional k ((intervalSum (k := k) o xs).obj X) := by
  induction xs with
  | nil =>
    change FiniteDimensional k ((0 : Diagram k o).obj X)
    have : Subsingleton ((0 : Diagram k o).obj X) :=
      ModuleCat.subsingleton_of_isZero ((isZero_zero _).obj X)
    infer_instance
  | cons J xs ih =>
    change FiniteDimensional k ((interval o J ⊞ intervalSum o xs).obj X)
    exact biprod_finiteDimensional _ _ X

/-- The dimension at a vertex of an interval sum counts the intervals containing it. -/
theorem finrank_intervalSum_obj (xs : List (FiniteInterval (n + 1))) (j : Fin (n + 1)) :
    Module.finrank k ((intervalSum (k := k) o xs).obj (vtx o j)) =
      xs.countP (fun J => decide (J.alive j)) := by
  induction xs with
  | nil =>
    have : Subsingleton ((intervalSum (k := k) o []).obj (vtx o j)) :=
      ModuleCat.subsingleton_of_isZero ((isZero_zero (Diagram k o)).obj _)
    rw [Module.finrank_zero_of_subsingleton]
    rfl
  | cons J xs ih =>
    rw [intervalSum_cons, finrank_biprod_obj, ih, finrank_interval_obj, List.countP_cons]
    by_cases hj : J.alive j <;> simp [hj, add_comm]

/-- Natural isomorphisms preserve the dimension at every vertex. -/
theorem finrank_obj_eq_of_iso {M N : Diagram k o} (e : M ≅ N) (X : Paths (Vertex o)) :
    Module.finrank k (M.obj X) = Module.finrank k (N.obj X) :=
  (e.app X).toLinearEquiv.finrank_eq

/-- The fibre of a biproduct as a product, through the projections and inclusions. -/
noncomputable def biprodEquiv (A B : Diagram k o) (X : Paths (Vertex o)) :
    (A ⊞ B).obj X ≃ₗ[k] A.obj X × B.obj X where
  toFun x := (((biprod.fst : A ⊞ B ⟶ A).app X).hom x, ((biprod.snd : A ⊞ B ⟶ B).app X).hom x)
  invFun y := ((biprod.inl : A ⟶ A ⊞ B).app X).hom y.1 + ((biprod.inr : B ⟶ A ⊞ B).app X).hom y.2
  map_add' x y := by simp
  map_smul' c x := by simp
  left_inv x := by
    have := congrArg (fun φ : A ⊞ B ⟶ A ⊞ B => (φ.app X).hom x) (biprod.total (X := A) (Y := B))
    simp only [NatTrans.app_add, NatTrans.comp_app, NatTrans.id_app, ModuleCat.hom_add,
      ModuleCat.hom_comp, ModuleCat.hom_id, LinearMap.add_apply, LinearMap.comp_apply,
      LinearMap.id_apply] at this
    exact this
  right_inv y := by
    have h1 := congrArg (fun φ : A ⟶ A => (φ.app X).hom y.1) (biprod.inl_fst (X := A) (Y := B))
    have h2 := congrArg (fun φ : B ⟶ B => (φ.app X).hom y.2) (biprod.inr_snd (X := A) (Y := B))
    have h3 := congrArg (fun φ : A ⟶ B => (φ.app X).hom y.1) (biprod.inl_snd (X := A) (Y := B))
    have h4 := congrArg (fun φ : B ⟶ A => (φ.app X).hom y.2) (biprod.inr_fst (X := A) (Y := B))
    simp only [NatTrans.comp_app, ModuleCat.hom_comp, LinearMap.comp_apply, NatTrans.id_app,
      ModuleCat.hom_id, LinearMap.id_apply, zero_app, ModuleCat.hom_zero,
      LinearMap.zero_apply] at h1 h2 h3 h4
    ext <;> simp [h1, h2, h3, h4]

/-- The rank of an arrow map of a biproduct is the sum of the two ranks. -/
theorem finrank_range_biprod_map (A B : Diagram k o) {X Y : Paths (Vertex o)} (f : X ⟶ Y)
    [FiniteDimensional k (A.obj X)] [FiniteDimensional k (B.obj X)]
    [FiniteDimensional k (A.obj Y)] [FiniteDimensional k (B.obj Y)] :
    Module.finrank k (LinearMap.range ((A ⊞ B).map f).hom) =
      Module.finrank k (LinearMap.range (A.map f).hom) +
        Module.finrank k (LinearMap.range (B.map f).hom) := by
  have hcomm : (biprodEquiv A B Y).toLinearMap ∘ₗ ((A ⊞ B).map f).hom =
      ((A.map f).hom.prodMap (B.map f).hom) ∘ₗ (biprodEquiv A B X).toLinearMap := by
    apply LinearMap.ext
    intro x
    apply Prod.ext
    · exact congrArg (fun φ => φ.hom x) ((biprod.fst : A ⊞ B ⟶ A).naturality f)
    · exact congrArg (fun φ => φ.hom x) ((biprod.snd : A ⊞ B ⟶ B).naturality f)
  rw [← LinearEquiv.finrank_map_eq (biprodEquiv A B Y), ← LinearMap.range_comp, hcomm,
    LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _), LinearMap.range_prodMap,
    (Submodule.prodEquiv _ _).finrank_eq, Module.finrank_prod]

/-- An arrow of an interval diagram has rank one inside the interval and zero otherwise. -/
theorem finrank_range_interval_map (J : FiniteInterval (n + 1)) {i j : Fin (n + 1)}
    (h : Arrow o i j) :
    Module.finrank k (LinearMap.range ((interval (k := k) o J).map (gen h)).hom) =
      if J.alive i ∧ J.alive j then 1 else 0 := by
  change Module.finrank k (LinearMap.range (fiberMap (k := k) J i j)) = _
  by_cases hij : J.alive i ∧ J.alive j
  · rw [if_pos hij, LinearMap.range_eq_top.mpr, finrank_top]
    · rw [show J.fiber (k := k) j = ⊤ by simp [FiniteInterval.fiber, hij.2], finrank_top,
        Module.finrank_self]
    · intro y
      refine ⟨⟨y, by simp [FiniteInterval.fiber, hij.1]⟩, Subtype.ext ?_⟩
      rw [fiberMap_val, if_pos hij]
  · rw [if_neg hij]
    have : fiberMap (k := k) J i j = 0 := by simp [fiberMap, hij]
    rw [this, LinearMap.range_zero, finrank_bot]

/-- The rank of an arrow of an interval sum counts the intervals containing both ends. -/
theorem finrank_range_intervalSum_map (xs : List (FiniteInterval (n + 1))) {i j : Fin (n + 1)}
    (h : Arrow o i j) :
    Module.finrank k (LinearMap.range ((intervalSum (k := k) o xs).map (gen h)).hom) =
      xs.countP (fun J => decide (J.alive i ∧ J.alive j)) := by
  induction xs with
  | nil =>
    have : Subsingleton ((intervalSum (k := k) o []).obj (vtx o j)) :=
      ModuleCat.subsingleton_of_isZero ((isZero_zero (Diagram k o)).obj _)
    rw [Module.finrank_zero_of_subsingleton]
    rfl
  | cons J xs ih =>
    rw [intervalSum_cons, finrank_range_biprod_map, ih, finrank_range_interval_map,
      List.countP_cons]
    by_cases hJ : J.alive i ∧ J.alive j <;> simp [hJ, add_comm]

/-- The total dimension of a diagram: the sum of its vertex dimensions. -/
noncomputable def totalDim (M : Diagram k o) : ℕ :=
  ∑ j : Fin (n + 1), Module.finrank k (M.obj (vtx o j))

theorem totalDim_eq_of_iso {M N : Diagram k o} (e : M ≅ N) : totalDim M = totalDim N :=
  Finset.sum_congr rfl fun j _ => finrank_obj_eq_of_iso e _

theorem totalDim_biprod (A B : Diagram k o) [∀ X, FiniteDimensional k (A.obj X)]
    [∀ X, FiniteDimensional k (B.obj X)] : totalDim (A ⊞ B) = totalDim A + totalDim B := by
  unfold totalDim
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun _ _ => finrank_biprod_obj A B _

/-- An interval diagram has positive total dimension. -/
theorem totalDim_interval_pos (J : FiniteInterval (n + 1)) :
    0 < totalDim (interval (k := k) o J) := by
  have hb : J.birth < n + 1 := lt_of_lt_of_le J.birth_lt_death J.death_le_size
  refine lt_of_lt_of_le ?_ (Finset.single_le_sum (fun j _ => Nat.zero_le _)
    (Finset.mem_univ (⟨J.birth, hb⟩ : Fin (n + 1))))
  rw [finrank_interval_obj, if_pos ⟨le_refl _, J.birth_lt_death⟩]
  exact Nat.one_pos

/-- Interval sums of permuted lists are isomorphic. -/
noncomputable def intervalSumPermIso {xs ys : List (FiniteInterval (n + 1))} (h : xs.Perm ys) :
    intervalSum (k := k) o xs ≅ intervalSum o ys := by
  classical
  exact Classical.choice <| by
    induction h with
    | nil => exact ⟨Iso.refl _⟩
    | cons J _ ih => exact ⟨biprod.mapIso (Iso.refl _) ih.some⟩
    | swap J K xs =>
      exact ⟨(biprod.associator _ _ _).symm ≪≫ biprod.mapIso (biprod.braiding _ _) (Iso.refl _) ≪≫
        biprod.associator _ _ _⟩
    | trans _ _ ih ih' => exact ⟨ih.some ≪≫ ih'.some⟩

/-- The diagram of a finite barcode, through the chosen list representative. -/
noncomputable def barcodeDiagram (o : Fin n → Bool) (B : Multiset (FiniteInterval (n + 1))) :
    Diagram k o :=
  intervalSum o B.toList

instance barcodeDiagram_finiteDimensional (B : Multiset (FiniteInterval (n + 1)))
    (X : Paths (Vertex o)) : FiniteDimensional k ((barcodeDiagram (k := k) o B).obj X) :=
  intervalSum_finiteDimensional _ X

/-- A list decomposition is a decomposition by its multiset. -/
noncomputable def intervalSumIsoBarcodeDiagram (xs : List (FiniteInterval (n + 1))) :
    intervalSum (k := k) o xs ≅ barcodeDiagram o (xs : Multiset (FiniteInterval (n + 1))) :=
  intervalSumPermIso (Multiset.coe_eq_coe.mp
    (Multiset.coe_toList (xs : Multiset (FiniteInterval (n + 1)))).symm)

end TDA.Sheaf.AlternatingDiagram
