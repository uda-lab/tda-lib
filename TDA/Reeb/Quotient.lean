import Mathlib.Topology.Connected.PathConnected
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Homeomorph.Quotient

/-!
# The path-component Reeb quotient

For a continuous map `f : C(X, Y)` into an arbitrary topological space `Y`, two points are
Reeb-related when some path joins them along which `f` is constant (`ReebRel`); equivalently,
they have equal value and lie in the same path component of that fibre. The Reeb quotient
`ReebQuotient f` is `X` modulo this equivalence with the quotient topology, with projection
`ReebQuotient.mk f` and the descended map `ReebQuotient.height f`, the height when `Y = ℝ`.
Every continuous map constant on Reeb classes descends uniquely (`ReebQuotient.existsUnique_lift`).

The acceptance cases are an empty domain, an injective map (the quotient is homeomorphic to `X`)
and a constant map (the quotient is homeomorphic to `ZerothHomotopy X`). Nothing here claims
that the projection is open or that the quotient is Hausdorff.

Source: de Silva, Munch and Patel, *Categorified Reeb Graphs*, §2.4: the object-level
construction of Proposition 2.10, not its functor; see `docs/math/reeb-quotient.md`.
-/

open Topology

universe u v w

namespace TDA.Reeb

variable {X : Type u} {Y : Type v} {Z : Type w}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-! ## Constant-value path relation -/

/-- `x ~_f x'`: some path from `x` to `x'` stays at the value `f x`. -/
def ReebRel (f : C(X, Y)) (x x' : X) : Prop :=
  ∃ γ : Path x x', ∀ t, f (γ t) = f x

/-- The relation is literally `JoinedIn` the fibre `f ⁻¹' {f x}` of the source point. -/
theorem reebRel_iff_joinedIn (f : C(X, Y)) (x x' : X) :
    ReebRel f x x' ↔ JoinedIn (f ⁻¹' {f x}) x x' := Iff.rfl

theorem ReebRel.apply_eq {f : C(X, Y)} {x x' : X} (h : ReebRel f x x') : f x' = f x := by
  obtain ⟨γ, hγ⟩ := h
  simpa using hγ 1

/-- Contract form: equal value and the same path component of that fibre subtype. -/
theorem reebRel_iff_joined_fiber (f : C(X, Y)) (x x' : X) :
    ReebRel f x x' ↔
      ∃ h : f x' = f x,
        Joined (⟨x, rfl⟩ : f ⁻¹' {f x}) (⟨x', h⟩ : f ⁻¹' {f x}) := by
  constructor
  · intro hr
    exact ⟨hr.apply_eq, (joinedIn_iff_joined (F := f ⁻¹' {f x}) rfl hr.apply_eq).1 hr⟩
  · rintro ⟨h, hj⟩
    exact (joinedIn_iff_joined (F := f ⁻¹' {f x}) rfl h).2 hj

/-! ## Setoid -/

theorem ReebRel.refl (f : C(X, Y)) (x : X) : ReebRel f x x :=
  ⟨Path.refl x, fun _ => rfl⟩

theorem ReebRel.symm {f : C(X, Y)} {x x' : X} (h : ReebRel f x x') : ReebRel f x' x := by
  obtain ⟨γ, hγ⟩ := h
  refine ⟨γ.symm, fun t => ?_⟩
  show f (γ (unitInterval.symm t)) = f x'
  rw [hγ]
  simpa using (hγ 1).symm

theorem ReebRel.trans {f : C(X, Y)} {x x' x'' : X} (h₁ : ReebRel f x x')
    (h₂ : ReebRel f x' x'') : ReebRel f x x'' := by
  have e := h₁.apply_eq
  obtain ⟨γ, hγ⟩ := h₁
  obtain ⟨δ, hδ⟩ := h₂
  refine ⟨γ.trans δ, fun t => ?_⟩
  rw [Path.trans_apply]
  split_ifs
  · exact hγ _
  · rw [hδ, e]

/-- The Reeb equivalence of `f` as a setoid on `X`. -/
def reebSetoid (f : C(X, Y)) : Setoid X where
  r := ReebRel f
  iseqv := ⟨ReebRel.refl f, ReebRel.symm, ReebRel.trans⟩

theorem reebSetoid_r (f : C(X, Y)) (x x' : X) : reebSetoid f x x' ↔ ReebRel f x x' := Iff.rfl

/-! ## Quotient with the quotient topology -/

/-- The Reeb quotient `Q_f = X / ~_f`. -/
def ReebQuotient (f : C(X, Y)) : Type u := Quotient (reebSetoid f)

instance (f : C(X, Y)) : TopologicalSpace (ReebQuotient f) :=
  inferInstanceAs (TopologicalSpace (Quotient (reebSetoid f)))

namespace ReebQuotient

variable (f : C(X, Y))

/-- The projection `q_f : X → Q_f`. -/
def mk (x : X) : ReebQuotient f := Quotient.mk (reebSetoid f) x

theorem mk_surjective : Function.Surjective (mk f) := Quotient.mk_surjective

theorem isQuotientMap_mk : IsQuotientMap (mk f) := isQuotientMap_quotient_mk'

@[continuity, fun_prop]
theorem continuous_mk : Continuous (mk f) := (isQuotientMap_mk f).continuous

/-- `q_f` as a bundled continuous map. -/
def proj : C(X, ReebQuotient f) := ⟨mk f, continuous_mk f⟩

@[simp] theorem proj_apply (x : X) : proj f x = mk f x := rfl

theorem mk_eq_mk_iff {x x' : X} : mk f x = mk f x' ↔ ReebRel f x x' := Quotient.eq

theorem mk_eq_mk_of_path {x x' : X} (γ : Path x x') (hγ : ∀ t, f (γ t) = f x) :
    mk f x = mk f x' := (mk_eq_mk_iff f).2 ⟨γ, hγ⟩

@[elab_as_elim]
theorem ind {motive : ReebQuotient f → Prop} (h : ∀ x, motive (mk f x)) (q : ReebQuotient f) :
    motive q := Quotient.ind h q

/-! ## Universal property and the descended map -/

variable {f}

/-- Descent of a continuous map constant on `~_f` classes (any target `Z`). -/
def lift (k : C(X, Z)) (hk : ∀ x x', ReebRel f x x' → k x = k x') :
    C(ReebQuotient f, Z) :=
  ⟨Quotient.lift k hk, k.continuous.quotient_lift hk⟩

@[simp] theorem lift_mk (k : C(X, Z)) (hk : ∀ x x', ReebRel f x x' → k x = k x') (x : X) :
    lift k hk (mk f x) = k x := rfl

theorem lift_comp_proj (k : C(X, Z)) (hk : ∀ x x', ReebRel f x x' → k x = k x') :
    (lift k hk).comp (proj f) = k := rfl

/-- Uniqueness via surjectivity of `q_f`. -/
theorem lift_unique (k : C(X, Z)) (hk : ∀ x x', ReebRel f x x' → k x = k x')
    (g : C(ReebQuotient f, Z)) (hg : ∀ x, g (mk f x) = k x) : g = lift k hk := by
  ext q
  induction q using ind with
  | h x => exact hg x

theorem hom_ext {g g' : C(ReebQuotient f, Z)} (h : ∀ x, g (mk f x) = g' (mk f x)) : g = g' := by
  ext q
  induction q using ind with
  | h x => exact h x

theorem existsUnique_lift (k : C(X, Z)) (hk : ∀ x x', ReebRel f x x' → k x = k x') :
    ∃! g : C(ReebQuotient f, Z), g.comp (proj f) = k :=
  ⟨lift k hk, rfl, fun g hg =>
    lift_unique k hk g fun x => by simpa using congrArg (· x) hg⟩

/-- Any continuous map that factors through `q_f` is constant on classes (converse). -/
theorem apply_eq_of_reebRel (g : C(ReebQuotient f, Z)) {x x' : X} (h : ReebRel f x x') :
    g (mk f x) = g (mk f x') := by rw [(mk_eq_mk_iff f).2 h]

variable (f)

/-- `f̄ : Q_f → Y`, the descended map; the height when `Y = ℝ`. -/
def height : C(ReebQuotient f, Y) :=
  lift f fun _ _ h => h.apply_eq.symm

@[simp] theorem height_mk (x : X) : height f (mk f x) = f x := rfl

theorem height_comp_proj : (height f).comp (proj f) = f := rfl

/-! ## Acceptance theorems (any target `Y`) -/

/-- Empty domain: the quotient is empty. -/
instance instIsEmpty [IsEmpty X] : IsEmpty (ReebQuotient f) :=
  ⟨fun q => by induction q using ReebQuotient.ind with | h x => exact isEmptyElim x⟩

end ReebQuotient

theorem reebRel_iff_eq_of_injective {f : C(X, Y)} (hf : Function.Injective f) (x x' : X) :
    ReebRel f x x' ↔ x = x' := by
  constructor
  · rintro ⟨γ, hγ⟩
    simpa using (hf (hγ 1)).symm
  · rintro rfl; exact ReebRel.refl f x

theorem reebRel_const_iff (c : Y) (x x' : X) :
    ReebRel (ContinuousMap.const X c) x x' ↔ Joined x x' :=
  ⟨fun ⟨γ, _⟩ => ⟨γ⟩, fun ⟨γ⟩ => ⟨γ, fun _ => rfl⟩⟩

namespace ReebQuotient

/-- Injective `f`: the quotient is canonically homeomorphic to `X`. -/
def homeomorphOfInjective {f : C(X, Y)} (hf : Function.Injective f) : ReebQuotient f ≃ₜ X :=
  (Homeomorph.Quotient.congrRight (r := reebSetoid f) (r' := ⊥) fun x x' => by
      rw [Setoid.bot_def, reebSetoid_r, reebRel_iff_eq_of_injective hf]).trans
    Homeomorph.quotientBot

@[simp] theorem homeomorphOfInjective_mk {f : C(X, Y)} (hf : Function.Injective f) (x : X) :
    homeomorphOfInjective hf (mk f x) = x := rfl

/-- Constant `f`: the quotient is the existing path-component quotient `ZerothHomotopy X`
with its quotient topology. -/
def homeomorphZerothHomotopy (c : Y) :
    ReebQuotient (ContinuousMap.const X c) ≃ₜ ZerothHomotopy X :=
  Homeomorph.Quotient.congrRight (r := reebSetoid (ContinuousMap.const X c))
    (r' := pathSetoid X) fun x x' => reebRel_const_iff c x x'

@[simp] theorem homeomorphZerothHomotopy_mk (c : Y) (x : X) :
    homeomorphZerothHomotopy c (mk (ContinuousMap.const X c) x) = ZerothHomotopy.mk x := rfl

/-- If `X` is path connected, the quotient of a constant map is a subsingleton. The
hypothesis cannot be dropped (see `Examples.boolConst_mk_false_ne_true`); no Hausdorff or
openness claim is made. -/
instance subsingleton_of_const [PathConnectedSpace X] (c : Y) :
    Subsingleton (ReebQuotient (ContinuousMap.const X c)) :=
  ⟨fun q q' => by
    induction q using ReebQuotient.ind with
    | h x => induction q' using ReebQuotient.ind with
      | h x' => exact (mk_eq_mk_iff _).2 ((reebRel_const_iff c x x').2 (PathConnectedSpace.joined x x'))⟩

end ReebQuotient

/-! ## Fixtures (`Y := ℝ` and one non-real target) -/

namespace Examples

open ReebQuotient

/-- Discrete two-point domain, constant real height: the two classes are distinct. -/
theorem boolConst_mk_false_ne_true :
    mk (ContinuousMap.const Bool (0 : ℝ)) false ≠ mk (ContinuousMap.const Bool (0 : ℝ)) true := by
  intro h
  obtain ⟨γ, -⟩ := (mk_eq_mk_iff _).1 h
  have := PreconnectedSpace.constant inferInstance γ.continuous (x := 0) (y := 1)
  simp at this

/-- Every class of that quotient is one of the two. -/
theorem boolConst_eq_mk_false_or_mk_true (q : ReebQuotient (ContinuousMap.const Bool (0 : ℝ))) :
    q = mk _ false ∨ q = mk _ true := by
  induction q using ReebQuotient.ind with
  | h b => cases b <;> simp

example (f : C(X, ℝ)) : (height f).comp (proj f) = f := height_comp_proj f
example (f : C(X, ℝ)) : Function.Surjective (mk f) := mk_surjective f
example (f : C(X, ℝ)) : IsQuotientMap (mk f) := isQuotientMap_mk f
example (f : C(X, ℝ)) (k : C(X, Z)) (hk : ∀ x x', ReebRel f x x' → k x = k x') :
    ∃! g : C(ReebQuotient f, Z), g.comp (proj f) = k := existsUnique_lift k hk
example [IsEmpty X] (f : C(X, ℝ)) : IsEmpty (ReebQuotient f) := inferInstance

/-- Identity height on `ℝ`: `Q_id ≃ₜ ℝ`. -/
def realIdHomeomorph : ReebQuotient (ContinuousMap.id ℝ) ≃ₜ ℝ :=
  homeomorphOfInjective (f := ContinuousMap.id ℝ) Function.injective_id

example (X : Type) [TopologicalSpace X] (c : ℝ) :
    ReebQuotient (ContinuousMap.const X c) ≃ₜ ZerothHomotopy X := homeomorphZerothHomotopy c

/-- Non-real target sanity check: the identity of `ℝ × ℝ`. -/
example : ReebQuotient (ContinuousMap.id (ℝ × ℝ)) ≃ₜ ℝ × ℝ :=
  homeomorphOfInjective Function.injective_id

end Examples

end TDA.Reeb
