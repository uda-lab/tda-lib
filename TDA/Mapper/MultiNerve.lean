import TDA.Mapper.Basic
import TDA.Topology.MultiNerve

/-!
# The MultiNerve Mapper

For a continuous map `f : C(X, Y)` and a target family `U : I → Set Y`, the MultiNerve Mapper
is the multinerve of the path-component pullback cover `componentCover f U`
(Carrière–Oudot, CO16-v3 Definition 3.3). Ordinary Mapper is the nerve of the same cover
(`mapper f U`, CO16-v3 Definition 2.12), so the generic projection of a multinerve onto its
nerve projects the MultiNerve Mapper onto ordinary Mapper and is surjective (CO16-v3
Lemma 3.4).

Every component member is path-connected, so the projection is a bijection on cells with
one-element support. A target multiplicity bound `CoverMultiplicityAtMost f U m` bounds the
support size of every cell; at `m = 2` all cells are vertices or edges, and one Mapper edge may
carry several edge cells. The projection is an order isomorphism under
`IntersectionsPathSubsingleton (componentCover f U)`, and in particular under the target-side
condition `PreimageIntersectionsPathConnected f U`.

`IntersectionsPathSubsingleton (componentCover f U)` is the hypothesis under which
component-sensitive statements about the MultiNerve Mapper, of the type studied by
Munch–Wang and Carrière–Oudot, transfer to ordinary Mapper. No such transfer, no geometric
realization, no homology and no approximation or stability statement is proved here.
-/

namespace TDA.Mapper

open Finset Set
open TDA.Topology TDA.Topology.MultiNerveCell

noncomputable section

universe u v w

variable {X : Type u} {Y : Type v} {I : Type w}
  [TopologicalSpace X] [TopologicalSpace Y]

local instance (α : Type*) : DecidableEq α := Classical.decEq α

/-- The MultiNerve Mapper: the multinerve of the path-component pullback cover. -/
abbrev multiNerveMapper (f : C(X, Y)) (U : I → Set Y) :=
  MultiNerveCell (componentCover f U)

/-- The projection of the MultiNerve Mapper onto the faces of ordinary Mapper. -/
def multiNerveMapper_projection (f : C(X, Y)) (U : I → Set Y) :
    multiNerveMapper f U → {s // s ∈ mapper f U} :=
  projection (componentCover f U)

@[simp] theorem multiNerveMapper_projection_coe (f : C(X, Y)) (U : I → Set Y)
    (c : multiNerveMapper f U) : (multiNerveMapper_projection f U c).1 = c.support := rfl

/-- Every ordinary Mapper face is the support of a MultiNerve Mapper cell. -/
theorem multiNerveMapper_projection_surjective (f : C(X, Y)) (U : I → Set Y) :
    Function.Surjective (multiNerveMapper_projection f U) :=
  projection_surjective (componentCover f U)

/-- The projection onto ordinary Mapper is monotone. -/
theorem multiNerveMapper_projection_monotone (f : C(X, Y)) (U : I → Set Y) :
    Monotone (multiNerveMapper_projection f U) :=
  projection_monotone (componentCover f U)

/-! ## Cells with one-element support -/

/-- Every member of the path-component pullback cover is path-connected. -/
theorem componentCover_isPathConnected (f : C(X, Y)) (U : I → Set Y)
    (a : ComponentIndex f U) : IsPathConnected (componentCover f U a) := by
  rcases a with ⟨i, c⟩
  induction c using ZerothHomotopy.rec with
  | mk x =>
      rw [componentCover_mk_eq_pathComponentIn]
      exact isPathConnected_pathComponentIn x.2

/-- Over every component index there is exactly one MultiNerve Mapper cell. -/
theorem existsUnique_cell_support_singleton (f : C(X, Y)) (U : I → Set Y)
    (a : ComponentIndex f U) : ∃! c : multiNerveMapper f U, c.support = {a} := by
  have hpc : IsPathConnected (interMember (componentCover f U) {a}) := by
    rw [interMember_singleton]
    exact componentCover_isPathConnected f U a
  have hsub := subsingleton_zerothHomotopy_of_isPathConnected hpc
  obtain ⟨c, hc⟩ := exists_cell_of_mem_nerve (componentIndex_supported f U a)
  refine ⟨c, hc, fun d hd => ?_⟩
  have e := cellsOverEquiv (componentCover f U) {a} (Finset.singleton_nonempty a)
  exact congrArg Subtype.val (e.injective (a₁ := ⟨d, hd⟩) (a₂ := ⟨c, hc⟩)
    (@Subsingleton.elim _ hsub _ _))

/-- The unique MultiNerve Mapper cell over a component index. -/
def vertexCell (f : C(X, Y)) (U : I → Set Y) (a : ComponentIndex f U) : multiNerveMapper f U :=
  (existsUnique_cell_support_singleton f U a).exists.choose

@[simp] theorem support_vertexCell (f : C(X, Y)) (U : I → Set Y) (a : ComponentIndex f U) :
    (vertexCell f U a).support = {a} :=
  (existsUnique_cell_support_singleton f U a).exists.choose_spec

/-- A cell over `{a}` is the vertex cell of `a`. -/
theorem eq_vertexCell_of_support_eq (f : C(X, Y)) (U : I → Set Y) {a : ComponentIndex f U}
    {c : multiNerveMapper f U} (hc : c.support = {a}) : c = vertexCell f U a :=
  (existsUnique_cell_support_singleton f U a).unique hc (support_vertexCell f U a)

/-- The cells with one-element support are the component indices, a cell going to the unique
element of its support. -/
def vertexCellEquiv (f : C(X, Y)) (U : I → Set Y) :
    {c : multiNerveMapper f U // c.support.card = 1} ≃ ComponentIndex f U where
  toFun c := (Finset.card_eq_one.1 c.2).choose
  invFun a := ⟨vertexCell f U a, by rw [support_vertexCell, Finset.card_singleton]⟩
  left_inv c := Subtype.ext
    (eq_vertexCell_of_support_eq f U (Finset.card_eq_one.1 c.2).choose_spec).symm
  right_inv a := by
    have hcard : (vertexCell f U a).support.card = 1 := by
      rw [support_vertexCell, Finset.card_singleton]
    have h := (Finset.card_eq_one.1 hcard).choose_spec
    exact Finset.singleton_inj.1 (h.symm.trans (support_vertexCell f U a))

/-- The support of a cell with one-element support is the singleton of its image under
`vertexCellEquiv`. -/
theorem support_eq_singleton_vertexCellEquiv (f : C(X, Y)) (U : I → Set Y)
    (c : {c : multiNerveMapper f U // c.support.card = 1}) :
    c.1.support = {vertexCellEquiv f U c} :=
  (Finset.card_eq_one.1 c.2).choose_spec

/-! ## Multiplicity -/

/-- Target-cover multiplicity bounds the support size of every MultiNerve Mapper cell. At
`m = 2` every cell is a vertex or an edge cell; several edge cells may lie over one Mapper
edge. -/
theorem multiNerveMapper_card_le_of_multiplicity (f : C(X, Y)) (U : I → Set Y) {m : ℕ}
    (hmult : CoverMultiplicityAtMost f U m) (c : multiNerveMapper f U) :
    c.support.card ≤ m :=
  mapper_face_card_le_of_multiplicity f U hmult c.support_mem_nerve

/-! ## Isomorphism with ordinary Mapper -/

/-- If every nonempty finite intersection of component members has at most one path
component, the projection is an order isomorphism from the MultiNerve Mapper onto the faces of
ordinary Mapper. This is the hypothesis under which component-sensitive statements of
Munch–Wang/Carrière–Oudot type transfer to ordinary Mapper; no such transfer is proved here. -/
def multiNerveMapperOrderIso (f : C(X, Y)) (U : I → Set Y)
    (h : IntersectionsPathSubsingleton (componentCover f U)) :
    multiNerveMapper f U ≃o {s // s ∈ mapper f U} :=
  multiNerveOrderIso (componentCover f U) h

/-- The underlying map of `multiNerveMapperOrderIso` is the projection. -/
@[simp] theorem coe_multiNerveMapperOrderIso (f : C(X, Y)) (U : I → Set Y)
    (h : IntersectionsPathSubsingleton (componentCover f U)) :
    ⇑(multiNerveMapperOrderIso f U h) = multiNerveMapper_projection f U := rfl

/-- Every nonempty inverse image of a nonempty finite intersection of target members is
path-connected. -/
def PreimageIntersectionsPathConnected (f : C(X, Y)) (U : I → Set Y) : Prop :=
  ∀ τ : Finset I, τ.Nonempty → (f ⁻¹' ⋂ i ∈ τ, U i).Nonempty →
    IsPathConnected (f ⁻¹' ⋂ i ∈ τ, U i)

/-- The target-side condition implies that every nonempty finite intersection of component
members has at most one path component. -/
theorem intersectionsPathSubsingleton_of_preimage (f : C(X, Y)) (U : I → Set Y)
    (h : PreimageIntersectionsPathConnected f U) :
    IntersectionsPathSubsingleton (componentCover f U) := by
  intro s hs
  refine ⟨fun c d => ?_⟩
  obtain ⟨x, rfl⟩ := ZerothHomotopy.mk_surjective c
  obtain ⟨y, rfl⟩ := ZerothHomotopy.mk_surjective d
  have hx := (mem_interMember_iff _).1 x.2
  let τ : Finset I := s.image Sigma.fst
  have hmem : ∀ z ∈ interMember (componentCover f U) s, z ∈ f ⁻¹' ⋂ i ∈ τ, U i := by
    intro z hz
    rw [Set.mem_preimage, mem_iInter₂]
    intro i hi
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hi
    exact ((mem_interMember_iff _).1 hz a ha).1
  have hP := h τ (hs.image _) ⟨x.1, hmem _ x.2⟩
  have hsub : f ⁻¹' (⋂ i ∈ τ, U i) ⊆ interMember (componentCover f U) s := by
    intro z hz
    rw [mem_interMember_iff]
    intro a ha
    have hτa : a.1 ∈ τ := Finset.mem_image_of_mem _ ha
    have hzU : f z ∈ U a.1 := mem_iInter₂.1 hz a.1 hτa
    obtain ⟨hxU, hxc⟩ := hx a ha
    have hxz : JoinedIn (f ⁻¹' U a.1) x.1 z :=
      (hP.joinedIn _ (hmem _ x.2) _ hz).mono fun w hw => mem_iInter₂.1 hw a.1 hτa
    exact ⟨hzU, (mk_eq_of_joinedIn f (U a.1) hxz hxU hzU).symm.trans hxc⟩
  have hxy : JoinedIn (f ⁻¹' ⋂ i ∈ τ, U i) x.1 y.1 :=
    hP.joinedIn _ (hmem _ x.2) _ (hmem _ y.2)
  exact ZerothHomotopy.sound (hxy.mono hsub).joined_subtype.somePath

end

end TDA.Mapper
