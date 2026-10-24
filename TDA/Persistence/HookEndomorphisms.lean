import TDA.Persistence.HookProjective
import TDA.Persistence.HookInfinity
import Mathlib.CategoryTheory.Linear.FunctorCategory
import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts

/-!
# Scalar endomorphisms and indecomposability of hooks

Evaluation at birth identifies the actual endomorphism ring of every
nonzero finite-death hook, and of every principal upset, with the coefficient
field. Hence their only idempotents are zero and identity, so they are
indecomposable in the existing categorical sense. No finiteness of the
grade poset or boundedness of the support is needed.

These are the individual-hook ingredients for BOOS, arXiv:2208.00300v3,
§2.6 and Theorem 2.7. They do not assert uniqueness of finite hook
decompositions or minimal rank-projective resolutions.
-/

set_option autoImplicit false

universe u v

namespace TDA.Persistence

open CategoryTheory CategoryTheory.Limits

/- The projection argument below adapts the criterion
`TauCeti.indecomposable_of_idempotent_eq_zero_or_id` at
5283b03c90ba08f975b65098ee412a890b567a6e (Apache 2.0,
copyright 2026 The Tau Ceti contributors). We use Mathlib's existing
`Indecomposable`; no alternative categorical structure is introduced. -/
private theorem indecomposable_of_scalar_end
    {C : Type*} [Category C] [Preadditive C] [HasBinaryBiproducts C]
    {k : Type*} [Field k] {X : C} (e : End X ≃+* k) : Indecomposable X := by
  have hX : ¬ IsZero X := by
    intro h
    have hz := congrArg e ((IsZero.iff_id_eq_zero X).mp h)
    change e (1 : End X) = e 0 at hz
    rw [map_one, map_zero] at hz
    exact one_ne_zero hz
  have hid : ∀ q : X ⟶ X, q ≫ q = q → q = 0 ∨ q = 𝟙 X := by
    intro q hq
    have h : IsIdempotentElem (e q) := by
      change e q * e q = e q
      simpa only [← map_mul, End.mul_def] using congrArg e hq
    rcases IsIdempotentElem.iff_eq_zero_or_one.mp h with h0 | h1
    · exact Or.inl (e.injective (h0.trans (map_zero e).symm))
    · exact Or.inr (e.injective (h1.trans (map_one e).symm))
  refine ⟨hX, fun Y Z i => ?_⟩
  rcases hid (i.hom ≫ biprod.fst ≫ biprod.inl ≫ i.inv) (by simp) with h0 | h1
  · refine Or.inl ((IsZero.iff_id_eq_zero Y).mpr ?_)
    simpa using congrArg (fun f : X ⟶ X =>
      biprod.inl ≫ i.inv ≫ f ≫ i.hom ≫ biprod.fst) h0
  · refine Or.inr ((IsZero.iff_id_eq_zero Z).mpr ?_)
    simpa using (congrArg (fun f : X ⟶ X =>
      biprod.inr ≫ i.inv ≫ f ≫ i.hom ≫ biprod.snd) h1).symm

variable {k : Type u} [Field k] {P : Type v} [PartialOrder P]

private instance : HasBinaryBiproducts (PModule.{u,v,u} k P) :=
  HasBinaryBiproducts.of_hasBinaryProducts

namespace Hook

/-- A death at or before birth gives the zero module, excluded from nonzero hooks. -/
theorem isZero_of_le {i j : P} (hji : j ≤ i) : IsZero (module (k := k) i j) := by
  apply (IsZero.iff_id_eq_zero _).mpr
  ext p x
  exact SupportInterval.val_eq_zero (support i j)
    (fun hp => hp.2 (hji.trans hp.1)) x

/-- A hook endomorphism is multiplication by its birth coefficient. -/
theorem end_eq_smul_id {i j : P} (hij : i < j)
    (α : End (module (k := k) i j)) :
    α = (((α.app i).hom (SupportInterval.one (support i j) (birth_mem hij)) : k)) •
      𝟙 (module (k := k) i j) := by
  apply hom_ext hij
  apply Subtype.ext
  simp [SupportInterval.one]

private theorem algebraMap_bijective {i j : P} (hij : i < j) :
    Function.Bijective (algebraMap k (End (module (k := k) i j))) := by
  constructor
  · intro a b hab
    have h := congrArg (fun f : End (module (k := k) i j) =>
      (((f.app i).hom (SupportInterval.one (support i j) (birth_mem hij))) : k)) hab
    simp only [Algebra.algebraMap_eq_smul_one] at h
    change a * (1 : k) = b * 1 at h
    simpa only [mul_one] using h
  · intro α
    refine ⟨(((α.app i).hom (SupportInterval.one (support i j) (birth_mem hij))) : k), ?_⟩
    simpa only [Algebra.algebraMap_eq_smul_one, End.one_def] using (end_eq_smul_id hij α).symm

/-- Evaluation at birth is an isomorphism of the actual hook endomorphism ring. -/
noncomputable def endRingEquiv {i j : P} (hij : i < j) :
    End (module (k := k) i j) ≃+* k :=
  (RingEquiv.ofBijective (algebraMap k (End (module (k := k) i j)))
    (algebraMap_bijective hij)).symm

/-- The inverse endomorphism-ring comparison is the actual scalar identity map. -/
@[simp] theorem endRingEquiv_symm_apply {i j : P} (hij : i < j) (c : k) :
    (endRingEquiv (k := k) hij).symm c = c • 𝟙 (module (k := k) i j) := by
  simp only [endRingEquiv, RingEquiv.symm_symm, RingEquiv.ofBijective_apply,
    Algebra.algebraMap_eq_smul_one, End.one_def]

/-- The endomorphism-ring comparison reads the birth coefficient. -/
theorem endRingEquiv_apply {i j : P} (hij : i < j) (α : End (module (k := k) i j)) :
    endRingEquiv hij α =
      (((α.app i).hom (SupportInterval.one (support i j) (birth_mem hij))) : k) := by
  apply (endRingEquiv hij).symm.injective
  rw [RingEquiv.symm_apply_apply, endRingEquiv_symm_apply]
  exact end_eq_smul_id hij α

/-- A nonzero finite-death hook has no decomposition into two nonzero summands. -/
theorem indecomposable {i j : P} (hij : i < j) :
    Indecomposable (module (k := k) i j) :=
  indecomposable_of_scalar_end (endRingEquiv hij)

end Hook

namespace HookInfinity

/-- The principal-upset generator has coefficient one at birth. -/
@[simp] theorem fiberEquiv_birth (i : P) :
    fiberEquivOfLe (R := k) (le_refl i) (birth i) = 1 := by
  change (Finsupp.single () (1 : k)) () = 1
  simp

/-- The principal-upset birth generator is nonzero. -/
theorem birth_ne_zero (i : P) : birth (R := k) i ≠ 0 := by
  intro h
  have he := congrArg (fiberEquivOfLe (R := k) (le_refl i)) h
  rw [fiberEquiv_birth, map_zero] at he
  exact one_ne_zero he

/-- An infinite-death hook endomorphism is multiplication by its birth coefficient. -/
theorem end_eq_smul_id (i : P) (α : End (module (R := k) i)) :
    α = fiberEquivOfLe (le_refl i) ((α.app i).hom (birth i)) •
      𝟙 (module (R := k) i) := by
  apply hom_ext
  apply (fiberEquivOfLe (R := k) (le_refl i)).injective
  change _ = _ * ((birth (R := k) i).val ())
  rw [show (birth (R := k) i).val () = 1 from fiberEquiv_birth i, mul_one]
  simp

private theorem algebraMap_bijective (i : P) :
    Function.Bijective (algebraMap k (End (module (R := k) i))) := by
  constructor
  · intro a b hab
    have h := congrArg (fun f : End (module (R := k) i) =>
      fiberEquivOfLe (le_refl i) ((f.app i).hom (birth i))) hab
    simp only [Algebra.algebraMap_eq_smul_one] at h
    change a * ((birth i).val ()) = b * ((birth i).val ()) at h
    rw [show (birth (R := k) i).val () = 1 from fiberEquiv_birth i, mul_one, mul_one] at h
    exact h
  · intro α
    refine ⟨fiberEquivOfLe (le_refl i) ((α.app i).hom (birth i)), ?_⟩
    simpa only [Algebra.algebraMap_eq_smul_one, End.one_def] using (end_eq_smul_id i α).symm

/-- Evaluation at birth identifies the principal-upset endomorphism ring with the field. -/
noncomputable def endRingEquiv (i : P) : End (module (R := k) i) ≃+* k :=
  (RingEquiv.ofBijective (algebraMap k (End (module (R := k) i)))
    (algebraMap_bijective i)).symm

/-- The inverse principal-upset comparison is scalar multiplication by the identity. -/
@[simp] theorem endRingEquiv_symm_apply (i : P) (c : k) :
    (endRingEquiv (k := k) i).symm c = c • 𝟙 (module (R := k) i) := by
  simp only [endRingEquiv, RingEquiv.symm_symm, RingEquiv.ofBijective_apply,
    Algebra.algebraMap_eq_smul_one, End.one_def]

/-- The principal-upset comparison reads the unique coefficient at birth. -/
theorem endRingEquiv_apply (i : P) (α : End (module (R := k) i)) :
    endRingEquiv i α = fiberEquivOfLe (le_refl i) ((α.app i).hom (birth i)) := by
  apply (endRingEquiv i).symm.injective
  rw [RingEquiv.symm_apply_apply, endRingEquiv_symm_apply]
  exact end_eq_smul_id i α

/-- Infinite-death hooks are indecomposable, including unbounded principal upsets. -/
theorem indecomposable (i : P) : Indecomposable (module (R := k) i) :=
  indecomposable_of_scalar_end (endRingEquiv i)

end HookInfinity

namespace SupportInterval

private theorem support_subset_of_iso (S T : Set P) (hS : S.OrdConnected)
    (hT : T.OrdConnected) (e : module (k := k) S hS ≅ module T hT) : S ⊆ T := by
  intro p hp
  by_contra ht
  have hz : (e.hom.app p).hom (one S hp) = 0 :=
    Subtype.ext (val_eq_zero T ht _)
  have h := congrArg (fun f => f.hom (one S hp)) (e.hom_inv_id_app p)
  change (e.inv.app p).hom ((e.hom.app p).hom (one S hp)) = one S hp at h
  rw [hz, map_zero] at h
  exact (zero_ne_one : (0 : k) ≠ 1) (congrArg Subtype.val h)

/-- Natural isomorphism of interval modules recovers their actual supports,
including the empty support. Convexity alone need not imply indecomposability. -/
theorem support_eq_of_iso (S T : Set P) (hS : S.OrdConnected)
    (hT : T.OrdConnected) (e : module (k := k) S hS ≅ module T hT) : S = T :=
  Set.Subset.antisymm (support_subset_of_iso S T hS hT e)
    (support_subset_of_iso T S hT hS e.symm)

end SupportInterval

namespace Hook

/-- The least support point recovers the birth of an individual nonzero hook. -/
theorem birth_eq_of_iso {i j i' j' : P} (hij : i < j) (hij' : i' < j')
    (e : module (k := k) i j ≅ module i' j') : i = i' := by
  have h := SupportInterval.support_eq_of_iso (support i j) (support i' j')
    (support_ordConnected i j) (support_ordConnected i' j') e
  have hi : i ∈ support i' j' := h ▸ birth_mem hij
  have hi' : i' ∈ support i j := h.symm ▸ birth_mem hij'
  exact le_antisymm hi'.1 hi.1

/-- Actual isomorphism recovers both finite birth and finite death. -/
theorem endpoints_eq_of_iso {i j i' j' : P} (hij : i < j) (hij' : i' < j')
    (e : module (k := k) i j ≅ module i' j') : i = i' ∧ j = j' := by
  have hi := birth_eq_of_iso hij hij' e
  subst i'
  have h := SupportInterval.support_eq_of_iso (support i j) (support i j')
    (support_ordConnected i j) (support_ordConnected i j') e
  constructor
  · rfl
  · apply le_antisymm
    · by_contra hj
      have hm : j' ∈ support i j := ⟨hij'.le, hj⟩
      exact death_not_mem i j' (h ▸ hm)
    · by_contra hj
      have hm : j ∈ support i j' := ⟨hij.le, hj⟩
      exact death_not_mem i j (h.symm ▸ hm)

/-- The isomorphism classes of individual nonzero finite hooks retain both endpoints. -/
theorem nonempty_iso_iff {i j i' j' : P} (hij : i < j) (hij' : i' < j') :
    Nonempty (module (k := k) i j ≅ module i' j') ↔ i = i' ∧ j = j' := by
  constructor
  · rintro ⟨e⟩
    exact endpoints_eq_of_iso hij hij' e
  · rintro ⟨rfl, rfl⟩
    exact ⟨Iso.refl _⟩

/-- Finite and infinite death are distinguished by actual module isomorphism. -/
theorem not_nonempty_iso_infinity {i j i' : P} (hij : i < j) :
    ¬ Nonempty (module (k := k) i j ≅ HookInfinity.module (R := k) i') := by
  rintro ⟨e⟩
  let x := SupportInterval.one (support i j) (birth_mem hij) (k := k)
  have hx : x ≠ 0 := fun h => (one_ne_zero : (1 : k) ≠ 0) (congrArg Subtype.val h)
  have hbirth : i' ≤ i := by
    by_contra h
    have hz := HookInfinity.fiber_eq_zero_of_not_le h ((e.hom.app i).hom x)
    exact hx ((e.app i).toLinearEquiv.injective (hz.trans (map_zero _).symm))
  let E := HookInfinity.fiberEquivOfLe (R := k) (hbirth.trans hij.le)
  let y := E.symm 1
  have hz : (e.inv.app j).hom y = 0 :=
    Subtype.ext (SupportInterval.val_eq_zero (support i j) (death_not_mem i j) _)
  have hy : y = 0 :=
    (e.app j).symm.toLinearEquiv.injective (hz.trans (map_zero _).symm)
  have h := congrArg E hy
  rw [LinearEquiv.apply_symm_apply, map_zero] at h
  exact one_ne_zero h

end Hook

namespace HookInfinity

private theorem birth_le_of_iso {i i' : P}
    (e : module (R := k) i ≅ module i') : i' ≤ i := by
  by_contra h
  have hz := fiber_eq_zero_of_not_le h ((e.hom.app i).hom (birth (R := k) i))
  exact birth_ne_zero i ((e.app i).toLinearEquiv.injective (hz.trans (map_zero _).symm))

/-- The birth of a principal upset is determined by its actual module. -/
theorem birth_eq_of_iso {i i' : P} (e : module (R := k) i ≅ module i') : i = i' :=
  le_antisymm (birth_le_of_iso e.symm) (birth_le_of_iso e)

/-- Individual infinite-death hooks are isomorphic exactly at equal births. -/
theorem nonempty_iso_iff {i i' : P} :
    Nonempty (module (R := k) i ≅ module i') ↔ i = i' := by
  constructor
  · rintro ⟨e⟩
    exact birth_eq_of_iso e
  · rintro rfl
    exact ⟨Iso.refl _⟩

end HookInfinity

end TDA.Persistence
