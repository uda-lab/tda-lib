import TDA.Topology.Nerve
import TDA.Topology.PathComponents

/-!
# Multinerves of indexed families

For an indexed family `V : CoverFamily X I` on a topological space, the multinerve records,
for every nonempty finite index set `σ`, every path component of the subspace
`interMember V σ = ⋂ i ∈ σ, V i`. A cell is such a pair; an empty intersection contributes no
cell. Inclusion of intersections induces face maps on path components, and the face relation
is a partial order in which the lower set of every cell is order-isomorphic to the nonempty
subsets of its index set (Carrière–Oudot, CO16-v3 Definitions 3.1 and 3.2).

Forgetting the component gives a monotone projection onto the faces of the ordinary
support-aware nerve `TDA.Topology.nerve V`. It is surjective (CO16-v3 Lemma 3.4), its fibre
over a face `σ` is in bijection with the path components of `interMember V σ`, and it is an
order isomorphism exactly when every nonempty finite intersection has at most one path
component. The last criterion and its path-connected sufficient condition are elementary
consequences proved here; they are not attributed to the paper.

No openness, local path connectedness, finiteness or nonemptiness is assumed. No geometric
realization, homology or Nerve Lemma is constructed.
-/

namespace TDA.Topology

open Finset Set

noncomputable section

universe u v

variable {X : Type u} {I : Type v}

/-! ## Finite intersections -/

section interMember

variable (V : CoverFamily X I)

/-- The intersection of the members of `V` indexed by a finite index set. -/
def interMember (σ : Finset I) : Set X := ⋂ i ∈ σ, V i

/-- A point lies in a finite intersection exactly when it lies in every indexed member. -/
theorem mem_interMember_iff {σ : Finset I} {x : X} :
    x ∈ interMember V σ ↔ ∀ i ∈ σ, x ∈ V i :=
  Set.mem_iInter₂

/-- Finite intersections are antitone in the index set. -/
theorem interMember_anti {σ τ : Finset I} (h : τ ⊆ σ) :
    interMember V σ ⊆ interMember V τ := fun _ hx =>
  (mem_interMember_iff V).2 fun i hi => (mem_interMember_iff V).1 hx i (h hi)

/-- A finite intersection is contained in each of its members. -/
theorem interMember_subset {σ : Finset I} {i : I} (hi : i ∈ σ) :
    interMember V σ ⊆ V i := fun _ hx =>
  (mem_interMember_iff V).1 hx i hi

/-- The intersection over a singleton is its member. -/
theorem interMember_singleton (i : I) : interMember V {i} = V i :=
  Finset.set_biInter_singleton i V

/-- The intersection over an inserted index splits off that member. -/
theorem interMember_insert [DecidableEq I] (i : I) (σ : Finset I) :
    interMember V (insert i σ) = V i ∩ interMember V σ :=
  Finset.set_biInter_insert i σ V

end interMember

variable [TopologicalSpace X]

/-! ## Face maps on path components -/

section faceMap

variable (V : CoverFamily X I)

/-- For `τ ⊆ σ`, the map on path components induced by the inclusion
`interMember V σ ⊆ interMember V τ`. -/
def faceMap {σ τ : Finset I} (h : τ ⊆ σ) :
    ZerothHomotopy (interMember V σ) → ZerothHomotopy (interMember V τ) :=
  componentMap (preimageSetInclusion (ContinuousMap.id X) (interMember_anti V h))

/-- Representative formula for face maps. -/
@[simp]
theorem faceMap_mk {σ τ : Finset I} (h : τ ⊆ σ) (x : interMember V σ) :
    faceMap V h (ZerothHomotopy.mk x) =
      ZerothHomotopy.mk (⟨x.1, interMember_anti V h x.2⟩ : interMember V τ) := rfl

/-- The face map of reflexive inclusion is the identity. -/
theorem faceMap_refl (σ : Finset I) : faceMap V (Finset.Subset.refl σ) = id := by
  funext c
  induction c using ZerothHomotopy.rec with
  | mk x => rfl

/-- Any face map from an index set to itself is the identity. -/
theorem faceMap_self {σ : Finset I} (h : σ ⊆ σ) (c : ZerothHomotopy (interMember V σ)) :
    faceMap V h c = c :=
  congrFun (faceMap_refl V σ) c

/-- Face maps compose along nested index sets. -/
theorem faceMap_trans {ρ τ σ : Finset I} (hρτ : ρ ⊆ τ) (hτσ : τ ⊆ σ) :
    faceMap V hρτ ∘ faceMap V hτσ = faceMap V (hρτ.trans hτσ) := by
  funext c
  induction c using ZerothHomotopy.rec with
  | mk x => rfl

/-- Pointwise form of `faceMap_trans`. -/
theorem faceMap_faceMap {ρ τ σ : Finset I} (hρτ : ρ ⊆ τ) (hτσ : τ ⊆ σ)
    (c : ZerothHomotopy (interMember V σ)) :
    faceMap V hρτ (faceMap V hτσ c) = faceMap V (hρτ.trans hτσ) c :=
  congrFun (faceMap_trans V hρτ hτσ) c

end faceMap

/-! ## Cells -/

/-- The cells of the multinerve of `V`: a nonempty finite index set together with a path
component of the intersection of its members. -/
def MultiNerveCell (V : CoverFamily X I) : Type (max u v) :=
  Σ σ : {σ : Finset I // σ.Nonempty}, ZerothHomotopy (interMember V σ.1)

/-- An intersection has no path component exactly when it is empty; such an index set carries
no multinerve cell. -/
theorem isEmpty_cellsOver_iff (V : CoverFamily X I) (σ : Finset I) :
    IsEmpty (ZerothHomotopy (interMember V σ)) ↔ interMember V σ = ∅ := by
  constructor
  · intro h
    ext x
    simp only [Set.mem_empty_iff_false, iff_false]
    exact fun hx => h.false (ZerothHomotopy.mk ⟨x, hx⟩)
  · intro h
    refine ⟨fun c => ?_⟩
    obtain ⟨x, -⟩ := ZerothHomotopy.mk_surjective c
    exact (Set.ext_iff.1 h x.1).1 x.2

namespace MultiNerveCell

variable {V : CoverFamily X I}

/-- The cell over a nonempty index set represented by a path component of its intersection. -/
def mk (σ : Finset I) (hσ : σ.Nonempty) (c : ZerothHomotopy (interMember V σ)) :
    MultiNerveCell V :=
  ⟨⟨σ, hσ⟩, c⟩

/-- The index set of a cell. -/
def support (a : MultiNerveCell V) : Finset I := a.1.1

/-- The path component of a cell, in the intersection over its support. -/
def component (a : MultiNerveCell V) : ZerothHomotopy (interMember V a.support) := a.2

/-- The points of the intersection over the support whose path component is that of the cell. -/
def carrier (a : MultiNerveCell V) : Set X :=
  {x | ∃ hx : x ∈ interMember V a.support,
    ZerothHomotopy.mk (⟨x, hx⟩ : interMember V a.support) = a.component}

@[simp] theorem support_mk (σ : Finset I) (hσ : σ.Nonempty)
    (c : ZerothHomotopy (interMember V σ)) : (mk σ hσ c).support = σ := rfl

@[simp] theorem component_mk (σ : Finset I) (hσ : σ.Nonempty)
    (c : ZerothHomotopy (interMember V σ)) : (mk σ hσ c).component = c := rfl

/-- The support of a cell is nonempty. -/
theorem support_nonempty (a : MultiNerveCell V) : a.support.Nonempty := a.1.2

/-- Every cell is of the form `mk`. -/
theorem eta (a : MultiNerveCell V) : mk a.support a.support_nonempty a.component = a := rfl

/-- Two cells with equal supports are equal when their components agree after transport by
the identity face map. -/
theorem ext_of_support_eq {a b : MultiNerveCell V} (h : b.support = a.support)
    (hc : faceMap V h.le a.component = b.component) : b = a := by
  rcases a with ⟨⟨σ, hσ⟩, c⟩
  rcases b with ⟨⟨τ, hτ⟩, d⟩
  change τ = σ at h
  subst h
  obtain rfl : c = d := (faceMap_self V _ c).symm.trans hc
  rfl

/-- The carrier of a cell lies in the intersection over its support. -/
theorem carrier_subset (a : MultiNerveCell V) : a.carrier ⊆ interMember V a.support :=
  fun _ hx => hx.1

/-- Every cell has a nonempty carrier. -/
theorem carrier_nonempty (a : MultiNerveCell V) : a.carrier.Nonempty := by
  obtain ⟨x, hx⟩ := ZerothHomotopy.mk_surjective a.component
  exact ⟨x.1, x.2, hx⟩

/-! ## The face order -/

/-- The face relation is a partial order. -/
instance instPartialOrder : PartialOrder (MultiNerveCell V) where
  le b a := ∃ h : b.support ⊆ a.support, faceMap V h a.component = b.component
  le_refl a := ⟨Finset.Subset.refl _, faceMap_self V _ _⟩
  le_trans c b a := by
    rintro ⟨h₁, e₁⟩ ⟨h₂, e₂⟩
    refine ⟨h₁.trans h₂, ?_⟩
    rw [← faceMap_faceMap V h₁ h₂, e₂, e₁]
  le_antisymm b a := by
    rintro ⟨h₁, e₁⟩ ⟨h₂, -⟩
    exact ext_of_support_eq (Finset.Subset.antisymm h₁ h₂) e₁

/-- The face relation: `b ≤ a` exactly when the support of `b` is contained in that of `a` and
the face map sends the component of `a` to the component of `b`. -/
theorem le_def {a b : MultiNerveCell V} :
    b ≤ a ↔ ∃ h : b.support ⊆ a.support, faceMap V h a.component = b.component :=
  Iff.rfl

/-- The face order forces containment of supports. -/
theorem support_mono {a b : MultiNerveCell V} (h : b ≤ a) : b.support ⊆ a.support :=
  h.1

/-- The face of a cell over a nonempty subset of its support. -/
def face (a : MultiNerveCell V) (τ : Finset I) (hτ : τ.Nonempty) (hτa : τ ⊆ a.support) :
    MultiNerveCell V :=
  mk τ hτ (faceMap V hτa a.component)

@[simp] theorem support_face (a : MultiNerveCell V) (τ : Finset I) (hτ : τ.Nonempty)
    (hτa : τ ⊆ a.support) : (a.face τ hτ hτa).support = τ := rfl

/-- Every face of a cell lies below it. -/
theorem face_le (a : MultiNerveCell V) (τ : Finset I) (hτ : τ.Nonempty)
    (hτa : τ ⊆ a.support) : a.face τ hτ hτa ≤ a :=
  ⟨hτa, rfl⟩

/-- A cell below `a` is the face of `a` over its own support. -/
theorem eq_face_of_le {a b : MultiNerveCell V} (h : b ≤ a) :
    b = a.face b.support b.support_nonempty (support_mono h) := by
  obtain ⟨h, e⟩ := h
  exact ext_of_support_eq (a := a.face b.support b.support_nonempty h) (b := b) rfl
    ((faceMap_faceMap V (Finset.Subset.refl _) h a.component).trans e)

/-- Faces of one cell are ordered by inclusion of their index sets. -/
theorem face_le_face_iff (a : MultiNerveCell V) {τ τ' : Finset I} (hτ : τ.Nonempty)
    (hτ' : τ'.Nonempty) (hτa : τ ⊆ a.support) (hτ'a : τ' ⊆ a.support) :
    a.face τ hτ hτa ≤ a.face τ' hτ' hτ'a ↔ τ ⊆ τ' :=
  ⟨support_mono, fun h => ⟨h, faceMap_faceMap V h hτ'a a.component⟩⟩

/-- The simplicial-poset axiom (CO16-v3 Definition 3.1): the lower set of every cell is
order-isomorphic to the poset of nonempty subsets of its support. -/
def lowerSetOrderIso (a : MultiNerveCell V) :
    {b // b ≤ a} ≃o {τ : Finset I // τ.Nonempty ∧ τ ⊆ a.support} where
  toFun b := ⟨b.1.support, b.1.support_nonempty, support_mono b.2⟩
  invFun τ := ⟨a.face τ.1 τ.2.1 τ.2.2, a.face_le τ.1 τ.2.1 τ.2.2⟩
  left_inv b := Subtype.ext (eq_face_of_le b.2).symm
  right_inv _ := rfl
  map_rel_iff' {b b'} := by
    change b.1.support ⊆ b'.1.support ↔ b.1 ≤ b'.1
    refine ⟨fun h => ?_, support_mono⟩
    exact (eq_face_of_le b.2).le.trans
      (((face_le_face_iff a _ _ _ _).2 h).trans (eq_face_of_le b'.2).ge)

@[simp] theorem lowerSetOrderIso_apply (a : MultiNerveCell V) (b : {b // b ≤ a}) :
    (lowerSetOrderIso a b).1 = b.1.support := rfl

/-! ## Projection to the ordinary nerve -/

/-- The support of every cell is a face of the ordinary nerve. -/
theorem support_mem_nerve (a : MultiNerveCell V) : a.support ∈ nerve V := by
  obtain ⟨x, -⟩ := ZerothHomotopy.mk_surjective a.component
  exact (mem_nerve_iff V _).2 ⟨a.support_nonempty, x.1, (mem_interMember_iff V).1 x.2⟩

/-- Every face of the ordinary nerve is the support of a cell. -/
theorem exists_cell_of_mem_nerve {σ : Finset I} (hσ : σ ∈ nerve V) :
    ∃ a : MultiNerveCell V, a.support = σ := by
  obtain ⟨hne, x, hx⟩ := (mem_nerve_iff V σ).1 hσ
  exact ⟨mk σ hne (ZerothHomotopy.mk ⟨x, (mem_interMember_iff V).2 hx⟩), rfl⟩

end MultiNerveCell

open MultiNerveCell

variable (V : CoverFamily X I)

/-- The projection of the multinerve onto the faces of the ordinary nerve, forgetting the
path component. -/
def projection : MultiNerveCell V → {s : Finset I // s ∈ nerve V} :=
  fun a => ⟨a.support, a.support_mem_nerve⟩

@[simp] theorem projection_coe (a : MultiNerveCell V) : (projection V a).1 = a.support := rfl

/-- The projection is monotone for the face order and inclusion of nerve faces. -/
theorem projection_monotone : Monotone (projection V) := fun _ _ h => support_mono h

/-- The image of the projection is exactly the set of nerve faces (CO16-v3 Lemma 3.4). -/
theorem projection_surjective : Function.Surjective (projection V) := by
  rintro ⟨σ, hσ⟩
  obtain ⟨a, ha⟩ := exists_cell_of_mem_nerve hσ
  exact ⟨a, Subtype.ext ha⟩

/-- The cells over a nonempty index set are the path components of its intersection. -/
def cellsOverEquiv (σ : Finset I) (hσ : σ.Nonempty) :
    {a : MultiNerveCell V // a.support = σ} ≃ ZerothHomotopy (interMember V σ) where
  toFun a := faceMap V (le_of_eq a.2.symm) a.1.component
  invFun c := ⟨mk σ hσ c, rfl⟩
  left_inv a := Subtype.ext (ext_of_support_eq a.2.symm rfl)
  right_inv c := faceMap_self V _ c

@[simp] theorem cellsOverEquiv_symm_apply (σ : Finset I) (hσ : σ.Nonempty)
    (c : ZerothHomotopy (interMember V σ)) :
    ((cellsOverEquiv V σ hσ).symm c).1 = mk σ hσ c := rfl

/-! ## Isomorphism criterion -/

/-- Every nonempty finite intersection of members has at most one path component. -/
def IntersectionsPathSubsingleton : Prop :=
  ∀ σ : Finset I, σ.Nonempty → Subsingleton (ZerothHomotopy (interMember V σ))

/-- The projection to the ordinary nerve is injective exactly when every nonempty finite
intersection has at most one path component. -/
theorem projection_injective_iff :
    Function.Injective (projection V) ↔ IntersectionsPathSubsingleton V := by
  constructor
  · intro hinj σ hσ
    refine ⟨fun c d => ?_⟩
    have h := hinj (a₁ := mk σ hσ c) (a₂ := mk σ hσ d) rfl
    exact eq_of_heq (Sigma.mk.inj_iff.1 h).2
  · intro hsub a b hab
    have hs : b.support = a.support := (congrArg Subtype.val hab).symm
    exact (ext_of_support_eq hs
      (@Subsingleton.elim _ (hsub _ b.support_nonempty) _ _)).symm

/-- Under `IntersectionsPathSubsingleton`, the projection is an order isomorphism from the
multinerve onto the faces of the ordinary nerve, ordered by inclusion. -/
def multiNerveOrderIso (h : IntersectionsPathSubsingleton V) :
    MultiNerveCell V ≃o {s : Finset I // s ∈ nerve V} where
  toEquiv := Equiv.ofBijective (projection V)
    ⟨(projection_injective_iff V).2 h, projection_surjective V⟩
  map_rel_iff' {b a} := by
    change b.support ⊆ a.support ↔ b ≤ a
    exact ⟨fun hs => ⟨hs, @Subsingleton.elim _ (h _ b.support_nonempty) _ _⟩, support_mono⟩

/-- The underlying map of `multiNerveOrderIso` is the projection. -/
@[simp] theorem coe_multiNerveOrderIso (h : IntersectionsPathSubsingleton V) :
    ⇑(multiNerveOrderIso V h) = projection V := rfl

/-- A path-connected subspace has at most one path component. -/
theorem subsingleton_zerothHomotopy_of_isPathConnected {S : Set X} (hS : IsPathConnected S) :
    Subsingleton (ZerothHomotopy S) := by
  have := isPathConnected_iff_pathConnectedSpace.1 hS
  exact (pathConnectedSpace_iff_zerothHomotopy.1 inferInstance).2

/-- Path-connected nonempty finite intersections give `IntersectionsPathSubsingleton`. -/
theorem intersectionsPathSubsingleton_of_isPathConnected
    (h : ∀ σ : Finset I, σ.Nonempty → (interMember V σ).Nonempty →
      IsPathConnected (interMember V σ)) :
    IntersectionsPathSubsingleton V := by
  intro σ hσ
  refine ⟨fun c d => ?_⟩
  obtain ⟨x, rfl⟩ := ZerothHomotopy.mk_surjective c
  exact @Subsingleton.elim _
    (subsingleton_zerothHomotopy_of_isPathConnected (h σ hσ ⟨x.1, x.2⟩)) _ _

end

end TDA.Topology
