import TDA.Reeb.Components
import Mathlib.Topology.Connected.TotallyDisconnected

/-!
# Path-component functor fixtures

Regression fixtures for `TDA.Reeb.componentFunctor` and `TDA.Reeb.componentNatTrans`:

* empty domain and empty base values;
* a disconnected domain, the discrete two-point space `Bool` over a one-point base, whose
  components at `⊤` are exactly two distinct classes;
* a noninjective natural map, the collapse from that `Bool` space to the one-point domain;
* the composition law at two nonidentity maps, the swap `Bool.not` followed by the collapse;
* a proper inclusion of open sets `{false} ≤ ⊤` for the identity on discrete `Bool`, where the
  inverse-image support changes.

The discrete classification uses only pinned totally-disconnected facts; it does not identify
path components with connected components. No global `Inhabited` or `Nonempty` instance is
added.
-/

open CategoryTheory

namespace TDA.Reeb.Examples

universe u v

example {Y : Type v} [TopologicalSpace Y] (f : C(Empty, Y)) (U : TopologicalSpace.Opens Y) :
    IsEmpty ((componentFunctor f).obj U) :=
  componentFunctor_obj_isEmpty_of_isEmpty f U

example (f : C(PEmpty.{u + 1}, Empty)) (U : TopologicalSpace.Opens Empty) :
    IsEmpty ((componentFunctor f).obj U) :=
  componentFunctor_obj_isEmpty_of_base_isEmpty f U

/-- In a discrete space, joined points are equal (pinned totally-disconnected facts). -/
theorem eq_of_joined_of_discrete {T : Type*} [TopologicalSpace T] [DiscreteTopology T]
    {a b : T} (hab : Joined a b) : a = b := by
  obtain ⟨p⟩ := hab
  have hs := (isPreconnected_range p.continuous).subsingleton
  simpa using hs ⟨0, rfl⟩ ⟨1, rfl⟩

/-- The constant map from discrete `Bool` to a one-point base. -/
def boolToUnit : C(Bool, Unit) := ContinuousMap.const Bool ()

/-- The class of `b` in `C_{boolToUnit}(⊤)`. -/
def boolClass (b : Bool) : (componentFunctor boolToUnit).obj ⊤ :=
  ZerothHomotopy.mk ⟨b, TopologicalSpace.Opens.mem_top _⟩

/-- Exhaustive classification: `C_{boolToUnit}(⊤) ≃ Bool`. -/
def boolComponentsEquiv : (componentFunctor boolToUnit).obj ⊤ ≃ Bool where
  toFun := ZerothHomotopy.lift (fun x => x.1)
    (fun _ _ p => congrArg Subtype.val (eq_of_joined_of_discrete ⟨p⟩))
  invFun := boolClass
  left_inv c := by
    induction c using ZerothHomotopy.rec with
    | mk x => rfl
  right_inv _ := rfl

theorem boolComponentsEquiv_boolClass (b : Bool) : boolComponentsEquiv (boolClass b) = b := rfl

theorem boolClass_false_ne_true : boolClass false ≠ boolClass true := fun hc => by
  have hb := congrArg boolComponentsEquiv hc
  rw [boolComponentsEquiv_boolClass, boolComponentsEquiv_boolClass] at hb
  exact Bool.false_ne_true hb

theorem boolClass_exhaustive (c : (componentFunctor boolToUnit).obj ⊤) :
    c = boolClass false ∨ c = boolClass true := by
  rcases hb : boolComponentsEquiv c with _ | _
  · left; rw [← boolComponentsEquiv.symm_apply_apply c, hb]; rfl
  · right; rw [← boolComponentsEquiv.symm_apply_apply c, hb]; rfl

/-- Collapse `Bool → Unit` over the same constant base map, as a natural transformation. -/
def collapseNatTrans : componentFunctor boolToUnit ⟶ componentFunctor (ContinuousMap.id Unit) :=
  componentNatTrans (ContinuousMap.const Bool ()) (fun _ => rfl)

theorem collapseNatTrans_identifies :
    collapseNatTrans.app ⊤ (boolClass false) = collapseNatTrans.app ⊤ (boolClass true) := rfl

theorem collapseNatTrans_not_injective : ¬ Function.Injective (collapseNatTrans.app ⊤) :=
  fun hinj => boolClass_false_ne_true (hinj collapseNatTrans_identifies)

/-- Identity laws instantiated at the nonidentity collapse. -/
example : componentNatTrans (ContinuousMap.id Bool) (fun _ => rfl) ≫ collapseNatTrans =
    collapseNatTrans := by
  rw [componentNatTrans_id]; exact Category.id_comp _

example : collapseNatTrans ≫
    componentNatTrans (g := ContinuousMap.id Unit) (ContinuousMap.id Unit) (fun _ => rfl) =
    collapseNatTrans := by
  rw [componentNatTrans_id]; exact Category.comp_id _

/-- The nonidentity swap `Bool.not` over the same constant base map. -/
def boolNot : C(Bool, Bool) := ⟨not, continuous_of_discreteTopology⟩

/-- The swap as a natural transformation `C_{boolToUnit} ⟶ C_{boolToUnit}`. -/
def swapNatTrans : componentFunctor boolToUnit ⟶ componentFunctor boolToUnit :=
  componentNatTrans boolNot (fun _ => rfl)

theorem swapNatTrans_boolClass (b : Bool) : swapNatTrans.app ⊤ (boolClass b) = boolClass (!b) :=
  rfl

/-- Composition law at two nonidentity maps: swap, then collapse. -/
theorem collapse_comp_swap :
    componentNatTrans ((ContinuousMap.const Bool ()).comp boolNot) (fun _ => rfl) =
      swapNatTrans ≫ collapseNatTrans :=
  componentNatTrans_comp boolNot (fun _ => rfl) (ContinuousMap.const Bool ()) (fun _ => rfl)
    (fun _ => rfl)

example : (swapNatTrans ≫ collapseNatTrans).app ⊤ (boolClass false) =
    collapseNatTrans.app ⊤ (boolClass true) := rfl

/-- Proper open inclusion: identity on discrete `Bool`, `U = {false}`, `V = ⊤`. -/
def falseOpen : TopologicalSpace.Opens Bool := ⟨{false}, isOpen_discrete _⟩

theorem falseOpen_le_top : falseOpen ≤ ⊤ := le_top

theorem falseOpen_ne_top : falseOpen ≠ ⊤ := fun hU => by
  have : (true : Bool) ∈ falseOpen := hU ▸ TopologicalSpace.Opens.mem_top true
  simp [falseOpen] at this

theorem true_absent_falseOpen (x : {b : Bool // ContinuousMap.id Bool b ∈ falseOpen}) :
    x.1 = false := x.2

theorem falseOpen_inclusion_mk :
    (componentFunctor (ContinuousMap.id Bool)).map (homOfLE falseOpen_le_top)
        (ZerothHomotopy.mk ⟨false, rfl⟩) =
      ZerothHomotopy.mk ⟨false, TopologicalSpace.Opens.mem_top _⟩ := rfl

end TDA.Reeb.Examples
