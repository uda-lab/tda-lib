import TDA.Mapper.PullbackCover
import TDA.Reeb.ComponentsDiscrete
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Topology.Order.IntermediateValue

/-!
# Path-component pullback-cover fixtures

Concrete regression fixtures for empty and duplicate indices, disconnected discrete fibers,
and a refinement that merges two real path components.
-/

namespace TDA.Mapper.Examples

noncomputable section

open Set

/-! ## Empty fibers -/

/-- The unique covered target point receives the empty inverse image from an empty domain. -/
def emptyDomainMap : C(Empty, Unit) := ContinuousMap.const Empty ()

/-- A one-member full cover of `Unit`. -/
def unitCover : Unit → Set Unit := fun _ => Set.univ

/-- An empty domain produces no component-cover index. -/
theorem emptyDomain_componentIndex_isEmpty :
    IsEmpty (ComponentIndex emptyDomainMap unitCover) :=
  ⟨fun a => by
    rcases a with ⟨i, c⟩
    have h : IsEmpty (PullbackSpace emptyDomainMap unitCover i) :=
      ⟨fun x => isEmptyElim x.1⟩
    exact (componentType_isEmpty emptyDomainMap unitCover i h).false c⟩

/-- A one-member family whose sole member is empty. -/
def emptyMemberFamily : Unit → Set Unit := fun _ => ∅

/-- An empty pullback member contributes no component-cover index. -/
theorem emptyMember_no_component_index :
    ¬ ∃ a : ComponentIndex (ContinuousMap.id Unit) emptyMemberFamily, a.1 = () :=
  no_componentIndex_of_isEmpty (ContinuousMap.id Unit) emptyMemberFamily ()
    ⟨fun x => x.2⟩

/-! ## Discrete two-point fibers and duplicate labels -/

/-- The constant map from discrete `Bool` to the covered point. -/
def boolToUnit : C(Bool, Unit) := ContinuousMap.const Bool ()

/-- A point of the full inverse-image subspace. -/
def boolPoint (b : Bool) : PullbackSpace boolToUnit unitCover () := ⟨b, Set.mem_univ ()⟩

/-- The component-cover index represented by `b`. -/
def boolComponentIndex (b : Bool) : ComponentIndex boolToUnit unitCover :=
  ⟨(), ZerothHomotopy.mk (boolPoint b)⟩

/-- In the discrete two-point fiber, the component member represented by `b` is `{b}`. -/
theorem bool_component_member (b : Bool) :
    componentCover boolToUnit unitCover (boolComponentIndex b) = {b} := by
  ext x
  constructor
  · rintro ⟨hx, hclass⟩
    change x = b
    exact congrArg Subtype.val (TDA.Reeb.joined_eq_of_discrete (Quotient.exact hclass))
  · intro hxb
    change x = b at hxb
    subst x
    exact ⟨Set.mem_univ (), rfl⟩

/-- The two discrete component classes are distinct. -/
theorem bool_component_classes_ne :
    ZerothHomotopy.mk (boolPoint false) ≠ ZerothHomotopy.mk (boolPoint true) := by
  intro h
  exact Bool.false_ne_true
    (congrArg Subtype.val (TDA.Reeb.joined_eq_of_discrete (Quotient.exact h)))

/-- The constant map from discrete `Bool` into one covered point has two distinct component
members. -/
theorem bool_component_indices_ne : boolComponentIndex false ≠ boolComponentIndex true := by
  intro h
  have hsnd : ZerothHomotopy.mk (boolPoint false) = ZerothHomotopy.mk (boolPoint true) :=
    eq_of_heq (Sigma.ext_iff.mp h).2
  exact bool_component_classes_ne hsnd

/-- The two displayed component indices exhaust the component cover of the discrete fiber. -/
theorem bool_component_indices_exhaustive (a : ComponentIndex boolToUnit unitCover) :
    a = boolComponentIndex false ∨ a = boolComponentIndex true := by
  rcases a with ⟨i, c⟩
  rcases i with ⟨⟩
  induction c using ZerothHomotopy.rec with
  | mk x =>
      rcases x with ⟨b, hb⟩
      cases b with
      | false =>
          left
          refine Sigma.ext rfl (heq_of_eq ?_)
          exact congrArg ZerothHomotopy.mk (Subtype.ext rfl)
      | true =>
          right
          refine Sigma.ext rfl (heq_of_eq ?_)
          exact congrArg ZerothHomotopy.mk (Subtype.ext rfl)

/-- Two duplicate target labels, each covering the same point. -/
def duplicateUnitCover : Bool → Set Unit := fun _ => Set.univ

/-- The copy, at label `i`, of the component represented by `b`. -/
def duplicateComponentIndex (i b : Bool) : ComponentIndex boolToUnit duplicateUnitCover :=
  ⟨i, ZerothHomotopy.mk ⟨b, Set.mem_univ ()⟩⟩

/-- Duplicate labels give equal underlying component members. -/
theorem duplicate_component_member (i b : Bool) :
    componentCover boolToUnit duplicateUnitCover (duplicateComponentIndex i b) = {b} := by
  ext x
  constructor
  · rintro ⟨hx, hclass⟩
    change x = b
    exact congrArg Subtype.val (TDA.Reeb.joined_eq_of_discrete (Quotient.exact hclass))
  · intro hxb
    change x = b at hxb
    subst x
    exact ⟨Set.mem_univ (), rfl⟩

/-- Duplicate original labels remain distinct copies in the component-cover index. -/
theorem duplicate_labels_remain_distinct :
    duplicateComponentIndex false false ≠ duplicateComponentIndex true false :=
  componentIndex_ne_of_index_ne boolToUnit duplicateUnitCover Bool.false_ne_true _ _

/-! ## A refinement that merges two real components -/

/-- The identity map on the real line. -/
def realMap : C(ℝ, ℝ) := ContinuousMap.id ℝ

/-- Two disjoint source intervals. -/
def twoIntervalCover : Unit → Set ℝ :=
  fun _ => Set.Ioo (-2) (-1) ∪ Set.Ioo 1 2

/-- A target interval containing both source intervals and the gap between them. -/
def middleIntervalCover : Unit → Set ℝ :=
  fun _ => Set.Ioo (-3) 3

/-- A still wider interval, used for the nonidentity composition fixture. -/
def wideIntervalCover : Unit → Set ℝ :=
  fun _ => Set.Ioo (-4) 4

/-- The selected proper inclusion from the two source intervals into the middle interval. -/
def intervalRefinement : TDA.Topology.Refinement twoIntervalCover middleIntervalCover where
  selector _ := ()
  subset _ x hx := by
    rcases hx with ⟨hx₁, hx₂⟩ | ⟨hx₁, hx₂⟩ <;> constructor <;> linarith

/-- The selected proper inclusion from the middle interval into the wider interval. -/
def wideIntervalRefinement : TDA.Topology.Refinement middleIntervalCover wideIntervalCover where
  selector _ := ()
  subset _ x hx := by
    rcases hx with ⟨hx₁, hx₂⟩
    constructor <;> linarith

/-- The point `-3/2` in the left source interval. -/
def leftSourcePoint : PullbackSpace realMap twoIntervalCover () :=
  ⟨(-3 / 2 : ℝ), by left; constructor <;> norm_num [realMap]⟩

/-- The point `3/2` in the right source interval. -/
def rightSourcePoint : PullbackSpace realMap twoIntervalCover () :=
  ⟨(3 / 2 : ℝ), by right; constructor <;> norm_num [realMap]⟩

/-- The source family is nonempty. -/
theorem twoIntervalCover_nonempty : (twoIntervalCover ()).Nonempty :=
  ⟨-3 / 2, leftSourcePoint.2⟩

/-- The source member is a proper subset of the selected target member. -/
theorem intervalRefinement_proper :
    twoIntervalCover () ⊆ middleIntervalCover () ∧
      twoIntervalCover () ≠ middleIntervalCover () := by
  refine ⟨intervalRefinement.subset (), ?_⟩
  intro h
  have hzero : (0 : ℝ) ∈ twoIntervalCover () := h.symm ▸ (show (0 : ℝ) ∈ middleIntervalCover () by
    constructor <;> norm_num)
  norm_num [twoIntervalCover] at hzero

/-- The classes of `-3/2` and `3/2` are distinct in the disconnected source inverse image. -/
theorem source_interval_classes_ne :
    ZerothHomotopy.mk leftSourcePoint ≠ ZerothHomotopy.mk rightSourcePoint := by
  intro h
  obtain ⟨γ⟩ := Quotient.exact h
  let q : Path (-3 / 2 : ℝ) (3 / 2 : ℝ) := γ.map continuous_subtype_val
  have hzero : (0 : ℝ) ∈ Set.range q := by
    apply intermediate_value_univ (0 : unitInterval) (1 : unitInterval) q.continuous
    change q 0 ≤ 0 ∧ 0 ≤ q 1
    rw [q.source, q.target]
    norm_num
  rcases hzero with ⟨t, ht⟩
  have hval : (γ t).1 = (0 : ℝ) := by
    change q t = 0
    exact ht
  have : (0 : ℝ) ∈ twoIntervalCover () := hval ▸ (γ t).2
  norm_num [twoIntervalCover] at this

/-- The corresponding component-cover indices are distinct before refinement. -/
theorem source_interval_indices_ne :
    (⟨(), ZerothHomotopy.mk leftSourcePoint⟩ : ComponentIndex realMap twoIntervalCover) ≠
      ⟨(), ZerothHomotopy.mk rightSourcePoint⟩ := by
  intro h
  apply source_interval_classes_ne
  exact eq_of_heq (Sigma.ext_iff.mp h).2

/-- The two source classes become equal after transport into the connected target interval. -/
theorem interval_transport_merges_classes :
    componentRefinementMap realMap intervalRefinement ()
        (ZerothHomotopy.mk leftSourcePoint) =
      componentRefinementMap realMap intervalRefinement ()
        (ZerothHomotopy.mk rightSourcePoint) := by
  change ZerothHomotopy.mk (refinementInclusion realMap intervalRefinement () leftSourcePoint) =
    ZerothHomotopy.mk (refinementInclusion realMap intervalRefinement () rightSourcePoint)
  have hpath : IsPathConnected (Set.Ioo (-3 : ℝ) 3) :=
    (convex_Ioo (-3 : ℝ) 3).isPathConnected ⟨0, by constructor <;> norm_num⟩
  let _ : PathConnectedSpace (PullbackSpace realMap middleIntervalCover ()) :=
    isPathConnected_iff_pathConnectedSpace.mp hpath
  exact ZerothHomotopy.sound (PathConnectedSpace.somePath _ _)

/-- The selected component refinement itself identifies the two displayed source indices. -/
theorem interval_componentRefinement_merges :
    (componentRefinement realMap intervalRefinement).selector
        ⟨(), ZerothHomotopy.mk leftSourcePoint⟩ =
      (componentRefinement realMap intervalRefinement).selector
        ⟨(), ZerothHomotopy.mk rightSourcePoint⟩ := by
  refine Sigma.ext rfl (heq_of_eq ?_)
  exact interval_transport_merges_classes

/-- Representative formula for the nonempty proper interval inclusion. -/
theorem interval_refinement_left_representative :
    (componentRefinement realMap intervalRefinement).selector
        ⟨(), ZerothHomotopy.mk leftSourcePoint⟩ =
      ⟨(), ZerothHomotopy.mk
        (refinementInclusion realMap intervalRefinement () leftSourcePoint)⟩ :=
  componentRefinement_selector_mk realMap intervalRefinement () leftSourcePoint

/-- Identity refinement fixes the represented left source component. -/
theorem interval_identity_left_representative :
    (componentRefinement realMap (TDA.Topology.Refinement.id twoIntervalCover)).selector
        ⟨(), ZerothHomotopy.mk leftSourcePoint⟩ =
      ⟨(), ZerothHomotopy.mk leftSourcePoint⟩ := by
  rw [componentRefinement_id]
  rfl

/-- Composition of the two nonidentity interval refinements agrees on the represented left
source component. -/
theorem interval_composition_left_representative :
    (componentRefinement realMap
        (TDA.Topology.Refinement.comp intervalRefinement wideIntervalRefinement)).selector
        ⟨(), ZerothHomotopy.mk leftSourcePoint⟩ =
      (TDA.Topology.Refinement.comp
        (componentRefinement realMap intervalRefinement)
        (componentRefinement realMap wideIntervalRefinement)).selector
        ⟨(), ZerothHomotopy.mk leftSourcePoint⟩ := by
  rw [componentRefinement_comp]

end

end TDA.Mapper.Examples
