import TDA.Topology.IndexedCover
import TDA.Topology.PathComponents
import Mathlib.Topology.Connected.LocallyPathConnected

/-!
# Path-component pullback covers

For a continuous map `f : C(X, Y)` and an indexed family `U : I → Set Y`, this module
decomposes every inverse image `f ⁻¹' U i` into its path components.  The resulting cover
keeps both the original index and the path-component class.  Selected refinements of target
families induce selected refinements of these component covers.

The construction is set-theoretic for arbitrary topological spaces and arbitrary target
members.  Openness is stated separately under local path connectedness of `X` and openness of
the target members.
-/

open Function Set

namespace TDA.Mapper

noncomputable section

universe u v w z

variable {X : Type u} {Y : Type v} {I : Type w} {J : Type z}
  [TopologicalSpace X] [TopologicalSpace Y]

/-- The inverse-image subspace over the member `U i`. -/
abbrev PullbackSpace (f : C(X, Y)) (U : I → Set Y) (i : I) :=
  {x : X // f x ∈ U i}

/-- Indices of the path-component pullback cover retain the original family index. -/
def ComponentIndex (f : C(X, Y)) (U : I → Set Y) :=
  Σ i, ZerothHomotopy (PullbackSpace f U i)

/-- The member labelled by `(i, c)` consists of the points whose class in the inverse-image
subspace over `U i` is `c`. -/
def componentCover (f : C(X, Y)) (U : I → Set Y) :
    TDA.Topology.CoverFamily X (ComponentIndex f U) :=
  fun a => {x | ∃ hx : f x ∈ U a.1,
    ZerothHomotopy.mk (⟨x, hx⟩ : PullbackSpace f U a.1) = a.2}

/-- The component class of a point does not depend on the proof that it lies in the target
member. -/
theorem componentClass_proof_irrel (f : C(X, Y)) (U : I → Set Y) {i : I} {x : X}
    (hx hx' : f x ∈ U i) :
    ZerothHomotopy.mk (⟨x, hx⟩ : PullbackSpace f U i) =
      ZerothHomotopy.mk (⟨x, hx'⟩ : PullbackSpace f U i) := by
  rfl

/-- Membership can be tested using any supplied proof that the point is in the inverse image. -/
theorem mem_componentCover_iff (f : C(X, Y)) (U : I → Set Y) {i : I}
    (c : ZerothHomotopy (PullbackSpace f U i)) {x : X} (hx : f x ∈ U i) :
    x ∈ componentCover f U ⟨i, c⟩ ↔
      ZerothHomotopy.mk (⟨x, hx⟩ : PullbackSpace f U i) = c := by
  constructor
  · rintro ⟨hx', hclass⟩
    exact (componentClass_proof_irrel f U hx hx').trans hclass
  · intro hclass
    exact ⟨hx, hclass⟩

/-- Every labelled component member is nonempty. -/
theorem componentCover_nonempty (f : C(X, Y)) (U : I → Set Y)
    (a : ComponentIndex f U) : (componentCover f U a).Nonempty := by
  rcases a with ⟨i, c⟩
  induction c using ZerothHomotopy.rec with
  | mk x => exact ⟨x.1, x.2, rfl⟩

/-- For a fixed original index, distinct component members are disjoint. -/
theorem componentCover_disjoint (f : C(X, Y)) (U : I → Set Y) {i : I}
    {c d : ZerothHomotopy (PullbackSpace f U i)} (hcd : c ≠ d) :
    Disjoint (componentCover f U ⟨i, c⟩) (componentCover f U ⟨i, d⟩) := by
  rw [Set.disjoint_left]
  intro x hxc hxd
  rcases hxc with ⟨hxi, hc⟩
  rcases hxd with ⟨hxi', hd⟩
  apply hcd
  exact hc.symm.trans ((componentClass_proof_irrel f U hxi hxi').trans hd)

/-- For a fixed original index, the component members partition its inverse image. -/
theorem iUnion_componentCover_fiber (f : C(X, Y)) (U : I → Set Y) (i : I) :
    (⋃ c : ZerothHomotopy (PullbackSpace f U i), componentCover f U ⟨i, c⟩) =
      f ⁻¹' U i := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_preimage]
  constructor
  · rintro ⟨c, hx⟩
    exact hx.1
  · intro hx
    exact ⟨ZerothHomotopy.mk (⟨x, hx⟩ : PullbackSpace f U i), hx, rfl⟩

/-- The union of the component cover is the inverse image of the union of the target family. -/
theorem iUnion_componentCover (f : C(X, Y)) (U : I → Set Y) :
    (⋃ a : ComponentIndex f U, componentCover f U a) = f ⁻¹' (⋃ i, U i) := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_preimage]
  constructor
  · rintro ⟨⟨i, c⟩, hx⟩
    exact ⟨i, hx.1⟩
  · rintro ⟨i, hxi⟩
    exact ⟨⟨i, ZerothHomotopy.mk (⟨x, hxi⟩ : PullbackSpace f U i)⟩, hxi, rfl⟩

/-- Coverage of a target support induces coverage of its inverse image by component members. -/
theorem componentCover_covers (f : C(X, Y)) (U : I → Set Y) {A : Set Y}
    (hU : TDA.Topology.Covers U A) :
    TDA.Topology.Covers (componentCover f U) (f ⁻¹' A) := by
  intro x hx
  obtain ⟨i, hxi⟩ := hU (f x) hx
  exact ⟨⟨i, ZerothHomotopy.mk (⟨x, hxi⟩ : PullbackSpace f U i)⟩, hxi, rfl⟩

/-- Coverage of the range of `f` gives a full component cover of `X`. -/
theorem componentCover_covers_range (f : C(X, Y)) (U : I → Set Y)
    (hU : TDA.Topology.Covers U (Set.range f)) :
    TDA.Topology.Covers (componentCover f U) Set.univ := by
  intro x _
  obtain ⟨i, hxi⟩ := hU (f x) ⟨x, rfl⟩
  exact ⟨⟨i, ZerothHomotopy.mk (⟨x, hxi⟩ : PullbackSpace f U i)⟩, hxi, rfl⟩

/-- An empty inverse-image subspace has no path-component class. -/
theorem componentType_isEmpty (f : C(X, Y)) (U : I → Set Y) (i : I)
    (h : IsEmpty (PullbackSpace f U i)) :
    IsEmpty (ZerothHomotopy (PullbackSpace f U i)) :=
  ⟨fun c => by
    induction c using ZerothHomotopy.rec with
    | mk x => exact h.false x⟩

/-- An empty inverse-image member contributes no index to the component cover. -/
theorem no_componentIndex_of_isEmpty (f : C(X, Y)) (U : I → Set Y) (i : I)
    (h : IsEmpty (PullbackSpace f U i)) :
    ¬ ∃ a : ComponentIndex f U, a.1 = i := by
  rintro ⟨⟨j, c⟩, hj⟩
  change j = i at hj
  subst j
  exact (componentType_isEmpty f U i h).false c

/-- Distinct original family indices remain distinct component-cover indices. -/
theorem componentIndex_ne_of_index_ne (f : C(X, Y)) (U : I → Set Y) {i j : I}
    (hij : i ≠ j) (c : ZerothHomotopy (PullbackSpace f U i))
    (d : ZerothHomotopy (PullbackSpace f U j)) :
    (⟨i, c⟩ : ComponentIndex f U) ≠ ⟨j, d⟩ := by
  intro h
  exact hij (congrArg Sigma.fst h)

/-! ## Refinements -/

/-- The inverse-image inclusion selected by a target-family refinement. -/
def refinementInclusion (f : C(X, Y)) {U : I → Set Y} {V : J → Set Y}
    (R : TDA.Topology.Refinement U V) (i : I) :
    C(PullbackSpace f U i, PullbackSpace f V (R.selector i)) :=
  TDA.Topology.preimageSetInclusion f (R.subset i)

/-- The map on path components induced by a selected refinement inclusion. -/
def componentRefinementMap (f : C(X, Y)) {U : I → Set Y} {V : J → Set Y}
    (R : TDA.Topology.Refinement U V) (i : I) :
    ZerothHomotopy (PullbackSpace f U i) →
      ZerothHomotopy (PullbackSpace f V (R.selector i)) :=
  TDA.Topology.componentMap (refinementInclusion f R i)

/-- A selected target-family refinement induces a selected refinement of component covers.
The destination component is determined by the supplied selector and is unique inside that
selected target member; without a selector there is no globally canonical destination label. -/
def componentRefinement (f : C(X, Y)) {U : I → Set Y} {V : J → Set Y}
    (R : TDA.Topology.Refinement U V) :
    TDA.Topology.Refinement (componentCover f U) (componentCover f V) where
  selector a := ⟨R.selector a.1, componentRefinementMap f R a.1 a.2⟩
  subset a x hx := by
    rcases a with ⟨i, c⟩
    rcases hx with ⟨hxi, hclass⟩
    change ZerothHomotopy.mk (⟨x, hxi⟩ : PullbackSpace f U i) = c at hclass
    refine ⟨R.subset i hxi, ?_⟩
    change TDA.Topology.componentMap (refinementInclusion f R i)
        (ZerothHomotopy.mk (⟨x, hxi⟩ : PullbackSpace f U i)) =
      componentRefinementMap f R i c
    exact congrArg (componentRefinementMap f R i) hclass

/-- Representative formula for the selected component refinement. -/
@[simp]
theorem componentRefinement_selector_mk (f : C(X, Y)) {U : I → Set Y} {V : J → Set Y}
    (R : TDA.Topology.Refinement U V) (i : I) (x : PullbackSpace f U i) :
    (componentRefinement f R).selector ⟨i, ZerothHomotopy.mk x⟩ =
      ⟨R.selector i, ZerothHomotopy.mk (refinementInclusion f R i x)⟩ := rfl

/-- Component refinement preserves the identity selected refinement. -/
theorem componentRefinement_id (f : C(X, Y)) (U : I → Set Y) :
    componentRefinement f (TDA.Topology.Refinement.id U) =
      TDA.Topology.Refinement.id (componentCover f U) := by
  apply TDA.Topology.Refinement.ext
  rintro ⟨i, c⟩
  refine Sigma.ext rfl (heq_of_eq ?_)
  change TDA.Topology.componentMap (refinementInclusion f (TDA.Topology.Refinement.id U) i) c = c
  rw [show refinementInclusion f (TDA.Topology.Refinement.id U) i =
      ContinuousMap.id (PullbackSpace f U i) by
    ext x
    rfl]
  exact congrFun TDA.Topology.componentMap_id c

/-- Component refinement preserves composition of selected refinements. -/
theorem componentRefinement_comp {K : Type*} (f : C(X, Y))
    {U : I → Set Y} {V : J → Set Y} {W : K → Set Y}
    (R : TDA.Topology.Refinement U V) (S : TDA.Topology.Refinement V W) :
    componentRefinement f (TDA.Topology.Refinement.comp R S) =
      TDA.Topology.Refinement.comp (componentRefinement f R) (componentRefinement f S) := by
  apply TDA.Topology.Refinement.ext
  rintro ⟨i, c⟩
  refine Sigma.ext rfl (heq_of_eq ?_)
  change TDA.Topology.componentMap
      (refinementInclusion f (TDA.Topology.Refinement.comp R S) i) c =
    componentRefinementMap f S (R.selector i) (componentRefinementMap f R i c)
  rw [show refinementInclusion f (TDA.Topology.Refinement.comp R S) i =
      (refinementInclusion f S (R.selector i)).comp (refinementInclusion f R i) by
    ext x
    rfl]
  exact congrFun (TDA.Topology.componentMap_comp
    (refinementInclusion f S (R.selector i)) (refinementInclusion f R i)) c

/-! ## Openness -/

/-- The member represented by `x` is the relative path component of `x` in the corresponding
inverse image. -/
theorem componentCover_mk_eq_pathComponentIn (f : C(X, Y)) (U : I → Set Y) (i : I)
    (x : PullbackSpace f U i) :
    componentCover f U ⟨i, ZerothHomotopy.mk x⟩ = pathComponentIn (f ⁻¹' U i) x.1 := by
  ext y
  constructor
  · rintro ⟨hy, hclass⟩
    change JoinedIn (f ⁻¹' U i) x.1 y
    rw [joinedIn_iff_joined
      (show x.1 ∈ f ⁻¹' U i from x.2) (show y ∈ f ⁻¹' U i from hy)]
    exact (Quotient.exact hclass).symm
  · intro hjoined
    change JoinedIn (f ⁻¹' U i) x.1 y at hjoined
    have hjoined' : Joined x (⟨y, hjoined.target_mem⟩ : PullbackSpace f U i) :=
      (joinedIn_iff_joined
        (show x.1 ∈ f ⁻¹' U i from x.2)
        (show y ∈ f ⁻¹' U i from hjoined.target_mem)).1 hjoined
    exact ⟨hjoined.target_mem, (ZerothHomotopy.sound hjoined'.somePath).symm⟩

/-- If `X` is locally path connected and every target member is open, then every member of the
component pullback cover is open in `X`. -/
theorem componentCover_isOpen [LocallyPathConnectedSpace X] (f : C(X, Y)) (U : I → Set Y)
    (hU : ∀ i, IsOpen (U i)) (a : ComponentIndex f U) : IsOpen (componentCover f U a) := by
  rcases a with ⟨i, c⟩
  induction c using ZerothHomotopy.rec with
  | mk x =>
      rw [componentCover_mk_eq_pathComponentIn]
      exact ((hU i).preimage f.continuous).pathComponentIn x.1

end

end TDA.Mapper
