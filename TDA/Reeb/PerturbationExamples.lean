import TDA.Reeb.Perturbation
import TDA.Reeb.ComponentsExamples

/-!
# Uniform perturbation fixtures

Regression fixtures for `TDA.Reeb.perturbationInterleaving`:

* `f = g` at parameter `0`, and enlargement of the parameter;
* the witness inhabits the perturbation hypothesis over `toOpensFunctor ⋙ componentFunctor f`;
* a constant height translation by `c` is interleaved at the attained bound `|c|`; the bound is
  sharp on a one-point domain but not optimal in general;
* the points at heights `0` and `1` are not `0`-interleaved;
* an empty domain, where every parameter works, and the empty interval;
* a nontrivial disconnected domain: two sheets over discrete `Bool` at heights `{0, 1}` and
  `{0, 2}` are `1`-interleaved with an injective `φ`, have two distinct components over
  `(-1/2, 3/2)`, and are not `0`-interleaved.

The discreteness lemma `eq_of_joined_of_discrete` is reused from the component-functor
fixtures.
-/

open Set CategoryTheory
open scoped NNReal

namespace TDA.Reeb.Examples

open TDA.Reeb TDA.Reeb.OpenInterval

/-- `f = g` at `ε = 0`. -/
example {X : Type*} [TopologicalSpace X] (f : C(X, ℝ)) :
    Interleaving 0 (intervalComponents f) (intervalComponents f) :=
  perturbationInterleaving (fun x => by simp)

/-- The witness inhabits the perturbation hypothesis stated directly over
`toOpensFunctor ⋙ componentFunctor f`, taking `f`, `g`, `ε` and the bound in that order. -/
example : ∀ {X : Type} [TopologicalSpace X] (f g : C(X, ℝ)) (ε : ℝ≥0),
    (∀ x, |f x - g x| ≤ ε) →
      Interleaving ε (toOpensFunctor ⋙ componentFunctor f) (toOpensFunctor ⋙ componentFunctor g) :=
  fun _ _ _ hfg => perturbationInterleaving hfg

/-- Monotonicity in `ε` via `Interleaving.mono`. -/
example {X : Type*} [TopologicalSpace X] {f g : C(X, ℝ)} {ε ε' : ℝ≥0}
    (hfg : ∀ x, |f x - g x| ≤ ε) (h : ε ≤ ε') :
    Interleaving ε' (intervalComponents f) (intervalComponents g) :=
  (perturbationInterleaving hfg).mono h

/-- The constant height translation `x ↦ f x + c`. -/
def heightShift {X : Type*} [TopologicalSpace X] (f : C(X, ℝ)) (c : ℝ) : C(X, ℝ) :=
  ⟨fun x => f x + c, f.continuous.add continuous_const⟩

/-- The bound of a constant height translation is `|c|`. -/
theorem abs_sub_heightShift_le {X : Type*} [TopologicalSpace X] (f : C(X, ℝ)) (c : ℝ) :
    ∀ x, |f x - heightShift f c x| ≤ Real.nnabs c := fun x => by
  change |f x - (f x + c)| ≤ (Real.nnabs c : ℝ)
  rw [sub_add_cancel_left, abs_neg, Real.coe_nnabs]

/-- Constant height translation: an interleaving at the attained bound `|c|`. The bound is sharp
on a point (`isEmpty_interleaving_const`) but not optimal in general: for `X = ℝ`, `f = id`,
`C_f|Int ≅ C_{f+c}|Int` for every `c`, and for empty `X` every parameter works. -/
def heightShiftInterleaving {X : Type*} [TopologicalSpace X] (f : C(X, ℝ)) (c : ℝ) :
    Interleaving (Real.nnabs c) (intervalComponents f) (intervalComponents (heightShift f c)) :=
  perturbationInterleaving (abs_sub_heightShift_le f c)

/-- Sharpness of the translation bound on a one-point domain: below `|c|` there is no
interleaving. -/
theorem isEmpty_interleaving_const {c : ℝ} {ε : ℝ≥0} (hε : (ε : ℝ) < |c|) :
    IsEmpty (Interleaving ε (intervalComponents (ContinuousMap.const Unit (0 : ℝ)))
      (intervalComponents (ContinuousMap.const Unit c))) := by
  refine ⟨fun i => ?_⟩
  set η : ℝ := (|c| - ε) / 2 with hη
  have hη0 : 0 < η := by rw [hη]; linarith
  have pt : (intervalComponents (ContinuousMap.const Unit (0 : ℝ))).obj (ioo (-η) η) :=
    ZerothHomotopy.mk ⟨(), show (0 : ℝ) ∈ Ioo (-η) η from ⟨by linarith, hη0⟩⟩
  have q := i.φ.app (ioo (-η) η) pt
  induction q using ZerothHomotopy.rec with
  | mk y =>
    have hy : c ∈ thicken ε (ioo (-η) η) := y.2
    obtain ⟨z, hz, hcz⟩ := mem_thicken.1 hy
    have hz' : |z| < η := abs_lt.2 hz
    have htri : |c| ≤ |c - z| + |z| := by
      simpa using abs_add_le (c - z) z
    linarith

/-- A pair with no `0`-interleaving: the points at heights `0` and `1`. -/
example : IsEmpty (Interleaving 0 (intervalComponents (ContinuousMap.const Unit (0 : ℝ)))
    (intervalComponents (ContinuousMap.const Unit (1 : ℝ)))) :=
  isEmpty_interleaving_const (by simp)

/-- Empty domain: the hypothesis is vacuous and every value is empty. -/
example {X : Type*} [TopologicalSpace X] [IsEmpty X] (f g : C(X, ℝ)) (ε : ℝ≥0) :
    Interleaving ε (intervalComponents f) (intervalComponents g) :=
  perturbationInterleaving (fun x => isEmptyElim x)

example {X : Type*} [TopologicalSpace X] [IsEmpty X] (f : C(X, ℝ)) (I : OpenInterval) :
    IsEmpty ((intervalComponents f).obj I) :=
  componentFunctor_obj_isEmpty_of_isEmpty f _

/-- Empty interval: source and target of the component of `φ` at `∅` are empty. -/
example {X : Type*} [TopologicalSpace X] {f g : C(X, ℝ)} {ε : ℝ≥0}
    (_hfg : ∀ x, |f x - g x| ≤ ε) :
    IsEmpty ((intervalComponents f).obj ⊥) ∧
      IsEmpty (((smoothing ε).obj (intervalComponents g)).obj ⊥) := by
  refine ⟨inferInstance, ?_⟩
  rw [smoothing_obj_obj, thicken_bot]
  infer_instance

/-! #### Nontrivial disconnected domain: two sheets over discrete `Bool` -/

/-- Heights `0` (at `false`) and `1` (at `true`). -/
def sheetsF : C(Bool, ℝ) := ⟨fun b => if b then 1 else 0, continuous_of_discreteTopology⟩
/-- Heights `0` (at `false`) and `2` (at `true`). -/
def sheetsG : C(Bool, ℝ) := ⟨fun b => if b then 2 else 0, continuous_of_discreteTopology⟩

theorem sheets_bound : ∀ b, |sheetsF b - sheetsG b| ≤ (1 : ℝ≥0) := by
  intro b; cases b <;> norm_num [sheetsF, sheetsG]

/-- The underlying point of a component over discrete `Bool`. -/
def sheetLift (h : C(Bool, ℝ)) (U : TopologicalSpace.Opens ℝ) :
    (componentFunctor h).obj U → Bool :=
  ZerothHomotopy.lift (fun x => x.1)
    (fun _ _ p => congrArg Subtype.val (eq_of_joined_of_discrete ⟨p⟩))

theorem sheetLift_injective (h : C(Bool, ℝ)) (U : TopologicalSpace.Opens ℝ) :
    Function.Injective (sheetLift h U) := by
  intro c d hcd
  induction c using ZerothHomotopy.rec with
  | mk x =>
    induction d using ZerothHomotopy.rec with
    | mk y => exact congrArg ZerothHomotopy.mk (Subtype.ext hcd)

/-- The witness `φ` is injective at every interval: both sheets stay distinct. -/
theorem sheets_φ_injective (I : OpenInterval) :
    Function.Injective ((perturbationInterleaving sheets_bound).φ.app I) := by
  intro c d hcd
  apply sheetLift_injective sheetsF (toOpens I)
  have := congrArg (sheetLift sheetsG (toOpens (thicken 1 I))) hcd
  induction c using ZerothHomotopy.rec with
  | mk x =>
    induction d using ZerothHomotopy.rec with
    | mk y => exact this

/-- At `I = (-1/2, 3/2)` both sheets are present: two distinct components. -/
theorem sheets_two_components :
    (ZerothHomotopy.mk ⟨false, show sheetsF false ∈ Ioo (-1/2 : ℝ) (3/2) by norm_num [sheetsF]⟩ :
        (intervalComponents sheetsF).obj (ioo (-1/2) (3/2))) ≠
      ZerothHomotopy.mk ⟨true, show sheetsF true ∈ Ioo (-1/2 : ℝ) (3/2) by norm_num [sheetsF]⟩ :=
      fun h => by
  have := congrArg (sheetLift sheetsF _) h
  exact Bool.false_ne_true this

/-- The sheets are not `0`-interleaved: `C_f(1/2, 3/2)` is nonempty, `C_g(1/2, 3/2)` empty. -/
theorem sheets_not_zero_interleaved :
    IsEmpty (Interleaving 0 (intervalComponents sheetsF) (intervalComponents sheetsG)) := by
  refine ⟨fun i => ?_⟩
  have q := i.toIso.hom.app (ioo (1/2) (3/2))
    (ZerothHomotopy.mk ⟨true, show sheetsF true ∈ Ioo (1/2 : ℝ) (3/2) by norm_num [sheetsF]⟩)
  induction q using ZerothHomotopy.rec with
  | mk y =>
    obtain ⟨b, hb⟩ := y
    have hb' : sheetsG b ∈ Ioo (1/2 : ℝ) (3/2) := hb
    cases b <;> norm_num [sheetsG] at hb'

end TDA.Reeb.Examples
