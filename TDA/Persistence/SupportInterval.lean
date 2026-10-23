import TDA.Persistence.Basic
import Mathlib.Order.Interval.Set.OrdConnected

/-!
# Modules supported on order-convex sets

An order-convex subset of a preorder supports a persistence module with one copy
of the coefficient field at each point of the subset. Structure maps preserve
coefficients when both indices belong to the subset and vanish otherwise.
Order convexity is precisely what makes these maps compose.

The naturality arguments for coefficients and support boundaries are those of
Bjerkevik, *On the Stability of Interval Decomposable Persistence Modules*,
Lemmas 4.4–4.5, DOI `10.1007/s00454-021-00298-0`.
-/

set_option autoImplicit false

universe u v

namespace TDA.Persistence.SupportInterval

open CategoryTheory
open scoped Classical

variable {k : Type u} [Field k] {P : Type v} [Preorder P]

/-- The coefficient field on the support, and its zero submodule elsewhere. -/
noncomputable def fiber (S : Set P) (p : P) : Submodule k k := by
  classical
  exact if p ∈ S then ⊤ else ⊥

omit [Preorder P] in
/-- A coefficient outside the support is zero. -/
theorem val_eq_zero (S : Set P) {p : P} (hp : p ∉ S)
    (x : fiber (k := k) S p) : (x : k) = 0 := by
  simpa [fiber, hp] using x.property

private noncomputable def map (S : Set P) {p q : P} :
    fiber (k := k) S p →ₗ[k] fiber (k := k) S q := by
  classical
  exact if h : p ∈ S ∧ q ∈ S then
    Submodule.inclusion (by simp [fiber, h.1, h.2]) else 0

/-- The persistence module of an order-convex support. Nonemptiness and
connectivity are unnecessary for the construction. -/
@[reducible]
noncomputable def module (S : Set P) (hS : S.OrdConnected) : PModule.{u,v,u} k P where
  obj p := ModuleCat.of k (fiber (k := k) S p)
  map _ := ModuleCat.ofHom (map S)
  map_id p := by
    classical
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    by_cases hp : p ∈ S
    · simp [map, hp]
    · simp [map, hp, val_eq_zero S hp x]
  map_comp {p q r} f g := by
    classical
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    by_cases hp : p ∈ S
    · by_cases hr : r ∈ S
      · have hq := hS.out hp hr ⟨leOfHom f, leOfHom g⟩
        simp [map, hp, hq, hr]
      · simp [map, hr]
    · simp [map, hp]

/-- Structure maps preserve the scalar exactly on the target support. -/
theorem structureMap_val (S : Set P) (hS : S.OrdConnected) {p q : P}
    (h : p ≤ q) (x : fiber (k := k) S p) :
    ((structureMapLinear (module S hS) h x) : k) = if q ∈ S then (x : k) else 0 := by
  classical
  change ((map S x) : k) = _
  by_cases hp : p ∈ S <;> by_cases hq : q ∈ S
  · simp [map, hp, hq]
  · simp [map, hp, hq]
  · simp [map, hp, hq, val_eq_zero S hp x]
  · simp [map, hp, hq]

/-- The unit coefficient in a supported fiber. -/
noncomputable def one (S : Set P) {p : P} (hp : p ∈ S) : fiber (k := k) S p :=
  ⟨1, by classical exact by simp [fiber, hp]⟩

/-- A transition is zero exactly when at least one index is outside the support. -/
theorem structureMap_eq_zero_iff (S : Set P) (hS : S.OrdConnected)
    {p q : P} (h : p ≤ q) :
    structureMapLinear (module (k := k) S hS) h = 0 ↔ ¬ (p ∈ S ∧ q ∈ S) := by
  classical
  constructor
  · intro hz ⟨hp, hq⟩
    have he := congrArg (fun f => (f (one (k := k) S hp) : k)) hz
    rw [structureMap_val] at he
    simp [hq, one] at he
  · intro hz
    change map S = 0
    simp [map, hz]

private noncomputable def comparisonLinear (S T : Set P) (c : k) (p : P) :
    fiber (k := k) S p →ₗ[k] fiber (k := k) T p := by
  classical
  exact if h : p ∈ T then
    c • Submodule.inclusion (show fiber (k := k) S p ≤ fiber (k := k) T p by
      simp [fiber, h]) else 0

omit [Preorder P] in
private theorem comparisonLinear_val (S T : Set P) (c : k) (p : P)
    (x : fiber (k := k) S p) :
    (comparisonLinear S T c p x : k) = if p ∈ T then c * (x : k) else 0 := by
  classical
  by_cases h : p ∈ T <;> simp [comparisonLinear, h]

/-- Multiplication by a scalar on the overlap. The support condition excludes
the two boundary configurations that obstruct naturality: entering the target
while still in the source, and leaving the source while still in the target.
-/
noncomputable def comparison (S T : Set P) (hS : S.OrdConnected)
    (hT : T.OrdConnected) (c : k)
    (hcompat : ∀ p q, p ≤ q → p ∈ S → q ∈ T → (q ∈ S ↔ p ∈ T)) :
    module (k := k) S hS ⟶ module T hT where
  app p := ModuleCat.ofHom (comparisonLinear S T c p)
  naturality {p q} f := by
    classical
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change (comparisonLinear S T c q
      (structureMapLinear (module S hS) (leOfHom f) x) : k) =
      (structureMapLinear (module T hT) (leOfHom f)
        (comparisonLinear S T c p x) : k)
    rw [comparisonLinear_val, structureMap_val, structureMap_val, comparisonLinear_val]
    by_cases hp : p ∈ S
    · by_cases hq : q ∈ T
      · have hc := hcompat p q (leOfHom f) hp hq
        by_cases hqs : q ∈ S
        · simp [hq, hqs, hc.mp hqs]
        · have hpt : p ∉ T := fun h => hqs (hc.mpr h)
          simp [hq, hqs, hpt]
      · simp [hq]
    · simp [val_eq_zero S hp x]

/-- The component coefficient of a comparison map. -/
theorem comparison_app_val (S T : Set P) (hS : S.OrdConnected)
    (hT : T.OrdConnected) (c : k)
    (hcompat : ∀ p q, p ≤ q → p ∈ S → q ∈ T → (q ∈ S ↔ p ∈ T))
    (p : P) (x : fiber (k := k) S p) :
    (((comparison S T hS hT c hcompat).app p).hom x : k) =
      if p ∈ T then c * (x : k) else 0 :=
  comparisonLinear_val S T c p x

/-- A normalized comparison is nonzero precisely when its scalar and overlap
are nonzero. In particular, disjoint supports admit only the zero comparison. -/
theorem comparison_ne_zero_iff (S T : Set P) (hS : S.OrdConnected)
    (hT : T.OrdConnected) (c : k)
    (hcompat : ∀ p q, p ≤ q → p ∈ S → q ∈ T → (q ∈ S ↔ p ∈ T)) :
    comparison S T hS hT c hcompat ≠ 0 ↔ c ≠ 0 ∧ (S ∩ T).Nonempty := by
  classical
  constructor
  · intro h
    constructor
    · intro hc
      apply h
      ext p x
      change (((comparison S T hS hT c hcompat).app p).hom x : k) = 0
      rw [comparison_app_val, hc]
      simp
    · by_contra hn
      apply h
      ext p x
      change (((comparison S T hS hT c hcompat).app p).hom x : k) = 0
      by_cases hs : p ∈ S
      · have ht : p ∉ T := fun ht => hn ⟨p, hs, ht⟩
        rw [comparison_app_val, if_neg ht]
      · rw [comparison_app_val, val_eq_zero S hs x]
        simp
  · rintro ⟨hc, p, hp, ht⟩ hz
    have he := congrArg (fun f => (((f.app p).hom (one (k := k) S hp)) : k)) hz
    rw [comparison_app_val] at he
    exact hc (by simpa [ht, one] using he)

/-- A component map is multiplication by its value on the unit coefficient. -/
theorem app_val_eq_mul (S T : Set P) (hS : S.OrdConnected)
    (hT : T.OrdConnected) (α : module (k := k) S hS ⟶ module T hT)
    {p : P} (hp : p ∈ S) (x : fiber (k := k) S p) :
    (((α.app p).hom x) : k) =
      (x : k) * (((α.app p).hom (one (k := k) S hp)) : k) := by
  have hx : x = (x : k) • one (k := k) S hp := by
    apply Subtype.ext
    simp [one]
  conv_lhs => rw [hx, map_smul]
  rfl

/-- A morphism is nonzero exactly when some unit coefficient is nonzero. -/
theorem ne_zero_iff_exists_coefficient (S T : Set P) (hS : S.OrdConnected)
    (hT : T.OrdConnected) (α : module (k := k) S hS ⟶ module T hT) :
    α ≠ 0 ↔ ∃ (p : P) (hp : p ∈ S),
      (((α.app p).hom (one (k := k) S hp)) : k) ≠ 0 := by
  classical
  constructor
  · intro h
    by_contra hn
    push Not at hn
    apply h
    ext p x
    by_cases hp : p ∈ S
    · simp [app_val_eq_mul S T hS hT α hp x, hn]
    · have hx : x = 0 := Subtype.ext (val_eq_zero S hp x)
      simp [hx]
  · rintro ⟨p, hp, hne⟩ hz
    apply hne
    rw [hz]
    rfl

/-- Naturality propagates component coefficients along a comparable pair in
the intersection of the two supports. -/
theorem coefficient_eq_of_le (S T : Set P) (hS : S.OrdConnected)
    (hT : T.OrdConnected) (α : module (k := k) S hS ⟶ module T hT)
    {p q : P} (h : p ≤ q) (hp : p ∈ S) (hq : q ∈ S) (ht : q ∈ T) :
    (((α.app p).hom (one (k := k) S hp)) : k) =
      (((α.app q).hom (one (k := k) S hq)) : k) := by
  have hn := congrArg (fun f => (f.hom (one (k := k) S hp) : k))
    (α.naturality (homOfLE h))
  have hm : structureMapLinear (module (k := k) S hS) h (one S hp) = one S hq := by
    apply Subtype.ext
    rw [structureMap_val]
    simp [hq, one]
  change (((α.app q).hom (structureMapLinear (module S hS) h (one S hp))) : k) =
    (structureMapLinear (module T hT) h ((α.app p).hom (one S hp)) : k) at hn
  rw [hm, structureMap_val, if_pos ht] at hn
  exact hn.symm

/-- A nonzero coefficient forces every earlier source point into the target.
This is the lower-bound obstruction in the Hom criterion for rectangles. -/
theorem mem_target_of_nonzero (S T : Set P) (hS : S.OrdConnected)
    (hT : T.OrdConnected) (α : module (k := k) S hS ⟶ module T hT)
    {p q : P} (h : q ≤ p) (hp : p ∈ S) (hq : q ∈ S)
    (hne : (((α.app p).hom (one (k := k) S hp)) : k) ≠ 0) : q ∈ T := by
  by_contra hqt
  have hpT : p ∈ T := by
    by_contra hpT
    exact hne (val_eq_zero T hpT _)
  have he := coefficient_eq_of_le S T hS hT α h hq hp hpT
  rw [val_eq_zero T hqt] at he
  exact hne he.symm

/-- A nonzero coefficient forces every later target point into the source.
This is the upper-bound obstruction in the Hom criterion for rectangles. -/
theorem mem_source_of_nonzero (S T : Set P) (hS : S.OrdConnected)
    (hT : T.OrdConnected) (α : module (k := k) S hS ⟶ module T hT)
    {p q : P} (h : p ≤ q) (hp : p ∈ S) (hq : q ∈ T)
    (hne : (((α.app p).hom (one (k := k) S hp)) : k) ≠ 0) : q ∈ S := by
  by_contra hqs
  have hn := congrArg (fun f => (f.hom (one (k := k) S hp) : k))
    (α.naturality (homOfLE h))
  change (((α.app q).hom (structureMapLinear (module S hS) h (one S hp))) : k) =
    (structureMapLinear (module T hT) h ((α.app p).hom (one S hp)) : k) at hn
  have hm : structureMapLinear (module (k := k) S hS) h = 0 :=
    (structureMap_eq_zero_iff S hS h).mpr (fun hh => hqs hh.2)
  rw [hm, LinearMap.zero_apply, map_zero, ZeroMemClass.coe_zero,
    structureMap_val, if_pos hq] at hn
  exact hne hn.symm

end TDA.Persistence.SupportInterval
