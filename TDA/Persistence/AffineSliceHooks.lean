import TDA.Persistence.PositiveAffineSlice
import TDA.Persistence.FinitePresentationReindex
import TDA.Persistence.RankSignedBarcodeOneDimensional
import TDA.Persistence.IntervalCompatibility

/-!
# Hooks restricted to positive affine lines

The actual restriction of a finite hook is the half-open interval between
its two entrance times. These times can coincide even for a nonzero hook.
Principal hooks give essential intervals. Endpoint extraction discards empty
finite intervals and retains every surviving occurrence, including duplicates.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

namespace TDA.Persistence.PositiveAffineLine

open CategoryTheory CategoryTheory.Limits
open scoped TDA.Persistence ZeroObject

variable {n : ℕ} [NeZero n] (L : PositiveAffineLine n)
variable {k : Type u} [Field k]

/-- Restriction identifies both the fibres and all structure maps of a finite
hook with the existing half-open interval, including collapsed endpoints. -/
theorem finiteHook_reindex_eq (p q : Fin n → ℝ) :
    reindex L.orderHom (Hook.module (k := k) p q) =
      RealBarcode.intervalModule (k := k)
        (L.entrance p, (L.entrance q : WithTop ℝ)) := by
  let S : Set ℝ := {t | p ≤ L.orderHom t ∧ ¬ q ≤ L.orderHom t}
  have hS : S.OrdConnected := by
    constructor
    intro s hs t ht v hv
    exact ⟨hs.1.trans (L.orderHom.monotone hv.1),
      fun h => ht.2 (h.trans (L.orderHom.monotone hv.2))⟩
  have he : S = IntervalCompatibility.support
      (L.entrance p, (L.entrance q : WithTop ℝ)) := by
    ext t
    simp only [S, Set.mem_ofPred_eq, IntervalCompatibility.support, RealBarcode.alive,
      ← L.entrance_le_iff p t, ← L.entrance_le_iff q t, not_le, WithTop.coe_lt_coe]
  change SupportInterval.module (k := k) S hS = _
  simp only [he]
  rfl

/-- The coefficient equation for every actual restricted finite-hook map. -/
theorem finiteHook_structureMap_val (p q : Fin n → ℝ)
    {s t : ℝ} (hst : s ≤ t)
    (x : (reindex L.orderHom (Hook.module (k := k) p q)).obj s) :
    (structureMapLinear (reindex L.orderHom (Hook.module (k := k) p q)) hst x :
      SupportInterval.fiber (k := k) (Hook.support p q) (L.orderHom t)).val =
      if L.entrance p ≤ t ∧ t < L.entrance q then
        (x : SupportInterval.fiber (k := k) (Hook.support p q) (L.orderHom s)).val else 0 := by
  change (structureMapLinear (Hook.module (k := k) p q)
    (L.orderHom.monotone hst) x :
      SupportInterval.fiber (k := k) (Hook.support p q) (L.orderHom t)).val = _
  rw [SupportInterval.structureMap_val]
  simp only [Hook.support, Set.mem_ofPred_eq, ← L.entrance_le_iff p t,
    ← L.entrance_le_iff q t, not_le]

/-- A principal hook restricts naturally to the essential interval beginning
at its entrance time. -/
noncomputable def principalHook_reindexIso (p : Fin n → ℝ) :
    reindex L.orderHom (HookInfinity.module (R := k) p) ≅
      RealBarcode.intervalModule (k := k) (L.entrance p, (⊤ : WithTop ℝ)) := by
  have hc : GaloisConnection CoordinateRealBridge.evaluate CoordinateRealBridge.diagonal := by
    intro p q
    simp [CoordinateRealBridge.diagonal, CoordinateRealBridge.evaluate, Pi.le_def,
      Fin.forall_fin_one]
  exact (GradedFree.reindexIso L.orderHom L.entrance L.galoisConnection
      (HookInfinity.generators p)).symm ≪≫
    GradedFree.reindexIso CoordinateRealBridge.diagonal CoordinateRealBridge.evaluate hc
      (HookInfinity.generators (CoordinateRealBridge.diagonal (L.entrance p))) ≪≫
    Functor.isoWhiskerLeft CoordinateRealBridge.diagonal.toFunctor
      (principalHook_intervalIso (k := k) (CoordinateRealBridge.diagonal (L.entrance p)))

omit [NeZero n] in
/-- Every actual restricted principal-hook map retains the generator coefficient. -/
theorem principalHook_structureMap_val (p : Fin n → ℝ)
    {s t : ℝ} (hst : s ≤ t)
    (x : (reindex L.orderHom (HookInfinity.module (R := k) p)).obj s) :
    (structureMapLinear (reindex L.orderHom (HookInfinity.module (R := k) p)) hst x).val () =
      x.val () := rfl

/-- The natural principal comparison reads the unchanged original generator
coefficient at every real parameter, including the zero fibres. -/
theorem principalHook_reindexIso_hom_val (p : Fin n → ℝ) (t : ℝ)
    (x : (reindex L.orderHom (HookInfinity.module (R := k) p)).obj t) :
    (((L.principalHook_reindexIso (k := k) p).hom.app t).hom x :
      RealBarcode.fiber (k := k) (L.entrance p, (⊤ : WithTop ℝ)) t).val = x.val () := by
  change (((principalHook_intervalIso (k := k)
    (CoordinateRealBridge.diagonal (L.entrance p))).hom.app
      (CoordinateRealBridge.diagonal t)).hom _ :
        RealBarcode.fiber (k := k) (L.entrance p, (⊤ : WithTop ℝ)) t).val = x.val ()
  rw [principalHook_intervalIso_hom_val]
  rfl

/-- The principal comparison commutes with every restricted structure map. -/
theorem principalHook_reindexIso_naturality (p : Fin n → ℝ)
    {s t : ℝ} (hst : s ≤ t) :
    structureMap (reindex L.orderHom (HookInfinity.module (R := k) p)) hst ≫
        (L.principalHook_reindexIso (k := k) p).hom.app t =
      (L.principalHook_reindexIso (k := k) p).hom.app s ≫
        structureMap (RealBarcode.intervalModule (k := k)
          (L.entrance p, (⊤ : WithTop ℝ))) hst :=
  (L.principalHook_reindexIso (k := k) p).hom.naturality (homOfLE hst)

private theorem finiteInterval_isZero_iff (b d : ℝ) :
    IsZero (RealBarcode.intervalModule (k := k) (b, (d : WithTop ℝ))) ↔ d ≤ b := by
  constructor
  · intro hz
    by_contra h
    have hbd : b < d := lt_of_not_ge h
    have hf := (Functor.isZero_iff _).mp hz b
    have : Subsingleton (RealBarcode.fiber (k := k) (b, (d : WithTop ℝ)) b) :=
      ModuleCat.subsingleton_of_isZero hf
    let x : RealBarcode.fiber (k := k) (b, (d : WithTop ℝ)) b :=
      ⟨1, by simp [RealBarcode.fiber, RealBarcode.alive, hbd]⟩
    have he := congrArg Subtype.val (Subsingleton.elim x 0)
    exact one_ne_zero he
  · exact RectangleBarcodeBridge.empty_interval_isZero (k := k) (b, d)

/-- Raw finite hooks restrict to zero exactly when their slice death is no
later than their slice birth. No ordering of the original endpoints is needed. -/
theorem finiteHook_reindex_isZero_iff (p q : Fin n → ℝ) :
    IsZero (reindex L.orderHom (Hook.module (k := k) p q)) ↔
      L.entrance q ≤ L.entrance p := by
  rw [L.finiteHook_reindex_eq]
  exact finiteInterval_isZero_iff _ _

/-- Equal entrance times give a zero restricted hook, even if the original
hook has strictly ordered endpoints. -/
theorem finiteHook_reindex_isZero_of_entrance_eq (p q : Fin n → ℝ)
    (he : L.entrance p = L.entrance q) :
    IsZero (reindex L.orderHom (Hook.module (k := k) p q)) :=
  (L.finiteHook_reindex_isZero_iff p q).mpr he.ge

/-- Ordered original endpoints give ordered entrance times; strictness can
be lost under restriction. -/
theorem finiteHook_reindex_isZero_iff_entrance_eq (p q : Fin n → ℝ) (hpq : p ≤ q) :
    IsZero (reindex L.orderHom (Hook.module (k := k) p q)) ↔
      L.entrance p = L.entrance q := by
  rw [L.finiteHook_reindex_isZero_iff]
  exact ⟨fun h => le_antisymm (L.entrance_monotone hpq) h, fun h => h.ge⟩

/-- The retained endpoint pair of one actual hook tag. Collapsed finite hooks
are omitted; principal hooks always retain their infinite death. -/
noncomputable def hookEndpoints (tag : RealHookTag (n := n)) :
    Option (ℝ × WithTop ℝ) := by
  classical
  exact match tag with
  | .inl pq => if L.entrance pq.val.1 < L.entrance pq.val.2 then
      some (L.entrance pq.val.1, (L.entrance pq.val.2 : WithTop ℝ)) else none
  | .inr p => some (L.entrance p, ⊤)

@[simp] theorem hookEndpoints_finite
    (pq : {pq : (Fin n → ℝ) × (Fin n → ℝ) // pq.1 < pq.2}) :
    L.hookEndpoints (.inl pq) =
      if L.entrance pq.val.1 < L.entrance pq.val.2 then
        some (L.entrance pq.val.1, (L.entrance pq.val.2 : WithTop ℝ)) else none := rfl

@[simp] theorem hookEndpoints_principal (p : Fin n → ℝ) :
    L.hookEndpoints (.inr p) = some (L.entrance p, (⊤ : WithTop ℝ)) := rfl

/-- A valid finite hook tag is omitted exactly when its entrance times coincide. -/
theorem hookEndpoints_finite_eq_none_iff
    (pq : {pq : (Fin n → ℝ) × (Fin n → ℝ) // pq.1 < pq.2}) :
    L.hookEndpoints (.inl pq) = none ↔
      L.entrance pq.val.1 = L.entrance pq.val.2 := by
  rw [L.hookEndpoints_finite]
  split_ifs with h
  · simp only [false_iff]
    exact ne_of_lt h
  · simp only [true_iff]
    exact le_antisymm (L.entrance_monotone pq.property.le) (not_lt.mp h)

/-- Every extracted endpoint pair is positive, with an included birth and
excluded finite death. -/
theorem hookEndpoints_positive (tag : RealHookTag (n := n))
    (p : ℝ × WithTop ℝ) (hp : L.hookEndpoints tag = some p) :
    (p.1 : WithTop ℝ) < p.2 := by
  cases tag with
  | inl pq =>
    rw [L.hookEndpoints_finite] at hp
    split_ifs at hp with h
    cases Option.some.inj hp
    exact WithTop.coe_lt_coe.mpr h
  | inr b =>
    simp only [L.hookEndpoints_principal, Option.some.injEq] at hp
    cases hp
    exact WithTop.coe_lt_top _

/-- Each retained tag restricts naturally to its extracted ordinary interval. -/
noncomputable def hookTag_reindexIso_of_some (tag : RealHookTag (n := n))
    (p : ℝ × WithTop ℝ) (hp : L.hookEndpoints tag = some p) :
    reindex L.orderHom
        (FiniteRankProjectiveClassification.rankProjectiveHookModule (k := k) tag) ≅
      RealBarcode.intervalModule (k := k) p := by
  cases tag with
  | inl pq =>
    rw [L.hookEndpoints_finite] at hp
    split_ifs at hp with h
    cases Option.some.inj hp
    exact eqToIso (L.finiteHook_reindex_eq pq.val.1 pq.val.2)
  | inr b =>
    simp only [L.hookEndpoints_principal, Option.some.injEq] at hp
    cases hp
    exact L.principalHook_reindexIso b

/-- An omitted valid tag has an actual zero restricted module. -/
theorem hookTag_reindex_isZero_of_none (tag : RealHookTag (n := n))
    (hnone : L.hookEndpoints tag = none) :
    IsZero (reindex L.orderHom
      (FiniteRankProjectiveClassification.rankProjectiveHookModule (k := k) tag)) := by
  cases tag with
  | inl pq =>
    exact L.finiteHook_reindex_isZero_of_entrance_eq pq.val.1 pq.val.2
      ((L.hookEndpoints_finite_eq_none_iff pq).mp hnone)
  | inr b => simp at hnone

/-- Restrict every occurrence, dropping only collapsed finite intervals. -/
noncomputable def sliceHookMultiset (B : Multiset (RealHookTag (n := n))) :
    Multiset (ℝ × WithTop ℝ) := B.filterMap L.hookEndpoints

@[simp] theorem sliceHookMultiset_zero : L.sliceHookMultiset 0 = 0 := rfl

@[simp] theorem sliceHookMultiset_add (B C : Multiset (RealHookTag (n := n))) :
    L.sliceHookMultiset (B + C) = L.sliceHookMultiset B + L.sliceHookMultiset C := by
  simp [sliceHookMultiset]

@[simp] theorem sliceHookMultiset_singleton (tag : RealHookTag (n := n)) :
    L.sliceHookMultiset {tag} = (L.hookEndpoints tag).toList := by
  change (tag ::ₘ 0).filterMap L.hookEndpoints = _
  rw [Multiset.filterMap_cons]
  cases L.hookEndpoints tag <;> simp

/-- Membership remembers a retained source occurrence. -/
theorem mem_sliceHookMultiset (B : Multiset (RealHookTag (n := n)))
    (p : ℝ × WithTop ℝ) :
    p ∈ L.sliceHookMultiset B ↔ ∃ tag ∈ B, L.hookEndpoints tag = some p := by
  simp [sliceHookMultiset]

/-- Endpoint collisions preserve their full multiplicity. -/
theorem count_sliceHookMultiset (B : Multiset (RealHookTag (n := n)))
    (p : ℝ × WithTop ℝ) :
    (L.sliceHookMultiset B).count p = B.countP (fun tag => L.hookEndpoints tag = some p) := by
  classical
  induction B using Multiset.induction_on with
  | empty => simp
  | @cons tag B ih =>
    change (B.filterMap L.hookEndpoints).count p = _ at ih
    change ((tag ::ₘ B).filterMap L.hookEndpoints).count p = _
    cases he : L.hookEndpoints tag with
    | none =>
      rw [Multiset.filterMap_cons_none tag B he, Multiset.countP_cons]
      simpa only [he, reduceCtorEq, ↓reduceIte, add_zero] using ih
    | some q =>
      rw [Multiset.filterMap_cons_some L.hookEndpoints tag B he,
        Multiset.count_cons, Multiset.countP_cons, ih]
      simp [he, eq_comm]

/-- The retained intervals as a positive ordinary endpoint diagram. -/
noncomputable def sliceHookDiagram (B : Multiset (RealHookTag (n := n))) : Diagram ℝ where
  points := L.sliceHookMultiset B
  offDiagonal := by
    intro p hp
    obtain ⟨tag, _, he⟩ := (L.mem_sliceHookMultiset B p).mp hp
    exact ne_of_lt (L.hookEndpoints_positive tag p he)

@[simp] theorem sliceHookDiagram_points (B : Multiset (RealHookTag (n := n))) :
    (L.sliceHookDiagram B).points = L.sliceHookMultiset B := rfl

theorem sliceHookDiagram_isPositive (B : Multiset (RealHookTag (n := n))) :
    (L.sliceHookDiagram B).IsPositive := by
  intro p hp
  obtain ⟨tag, _, he⟩ := (L.mem_sliceHookMultiset B p).mp hp
  exact L.hookEndpoints_positive tag p he

end TDA.Persistence.PositiveAffineLine
