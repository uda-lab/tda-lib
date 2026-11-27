import TDA.Persistence.HookEndomorphisms
import TDA.Persistence.SupportInterval

/-!
# Endomorphisms of interval modules over a linear order

Every endomorphism of `SupportInterval.module S hS` over a linearly ordered index type is
multiplication by one scalar of the coefficient field (`exists_smul_id`), because two points of
the support are comparable and naturality carries the coefficient from one to the other. For a
nonempty support this is a ring isomorphism `End (module S hS) ≃+* k` (`endRingEquiv`).

A composite `module S ⟶ module T ⟶ module S` vanishes when `S ≠ T` (`comp_eq_zero_of_ne`):
the scalar of the composite is zero at a point of `S` outside `T`, and when `S ⊂ T` the
reverse composite `module T ⟶ module S ⟶ module T` is a scalar vanishing at a point of
`T ∖ S`, so its square, which contains the square of the first scalar, is zero.

These are Lemma 2.1 and Lemma 3.1 of Gan and Upegui Keagy, arXiv:2507.01303v1,
for a linearly ordered index type. Isomorphic interval modules have equal supports
(`SupportInterval.support_eq_of_iso`).
-/

set_option autoImplicit false

universe u v

namespace TDA.Persistence.SupportInterval

open CategoryTheory

variable {k : Type u} [Field k] {P : Type v} [LinearOrder P]

/-- The coefficient at a point of the support of an endomorphism of an interval module. -/
private noncomputable def coeff (S : Set P) (hS : S.OrdConnected)
    (f : module (k := k) S hS ⟶ module S hS) {x : P} (hx : x ∈ S) : k :=
  (((f.app x).hom (one (k := k) S hx)) : k)

private theorem coeff_eq (S : Set P) (hS : S.OrdConnected)
    (f : module (k := k) S hS ⟶ module S hS) {x y : P} (hx : x ∈ S) (hy : y ∈ S) :
    coeff S hS f hx = coeff S hS f hy := by
  rcases le_total x y with h | h
  · exact coefficient_eq_of_le S S hS hS f h hx hy hy
  · exact (coefficient_eq_of_le S S hS hS f h hy hx hx).symm

/-- Every endomorphism of an interval module over a linear order is a scalar multiple of the
identity. -/
theorem exists_smul_id (S : Set P) (hS : S.OrdConnected)
    (f : module (k := k) S hS ⟶ module S hS) :
    ∃ c : k, f = c • 𝟙 (module (k := k) S hS) := by
  classical
  by_cases hne : S.Nonempty
  · obtain ⟨x, hx⟩ := hne
    refine ⟨coeff S hS f hx, ?_⟩
    ext p z
    by_cases hp : p ∈ S
    · rw [app_val_eq_mul S S hS hS f hp z]
      show (z : k) * coeff S hS f hp = coeff S hS f hx * (z : k)
      rw [coeff_eq S hS f hp hx, mul_comm]
    · have hz : z = 0 := Subtype.ext (val_eq_zero S hp z)
      subst hz
      simp
  · refine ⟨0, ?_⟩
    ext p z
    have hp : p ∉ S := fun h => hne ⟨p, h⟩
    have hz : z = 0 := Subtype.ext (val_eq_zero S hp z)
    subst hz
    simp

private theorem coeff_smul_id (S : Set P) (hS : S.OrdConnected) (c : k) {x : P} (hx : x ∈ S) :
    coeff S hS (c • 𝟙 (module (k := k) S hS)) hx = c := by
  simp [coeff, one]

/-- The scalar endomorphism is determined by its coefficient. -/
theorem smul_id_injective (S : Set P) (hS : S.OrdConnected) (hne : S.Nonempty) :
    Function.Injective fun c : k => c • 𝟙 (module (k := k) S hS) := by
  intro a b hab
  obtain ⟨x, hx⟩ := hne
  have h := congrArg (fun f => coeff S hS f hx) hab
  simpa only [coeff_smul_id] using h

/-- Evaluation of the scalar identifies the endomorphism ring of a nonempty interval module
over a linear order with the coefficient field. -/
noncomputable def endRingEquiv (S : Set P) (hS : S.OrdConnected) (hne : S.Nonempty) :
    End (module (k := k) S hS) ≃+* k :=
  (RingEquiv.ofBijective (algebraMap k (End (module (k := k) S hS)))
    (by
      constructor
      · intro a b hab
        apply smul_id_injective S hS hne
        simpa only [Algebra.algebraMap_eq_smul_one, End.smul_asHom, End.one_asHom] using
          congrArg End.asHom hab
      · intro α
        obtain ⟨c, hc⟩ := exists_smul_id S hS α.asHom
        refine ⟨c, ?_⟩
        apply End.ext
        simpa only [Algebra.algebraMap_eq_smul_one, End.smul_asHom, End.one_asHom] using
          hc.symm)).symm

/-- The inverse of the ring equivalence is the scalar identity. -/
@[simp] theorem endRingEquiv_symm_apply (S : Set P) (hS : S.OrdConnected) (hne : S.Nonempty)
    (c : k) :
    (endRingEquiv S hS hne).symm c = .of (c • 𝟙 (module (k := k) S hS)) := by
  apply End.ext
  simp only [endRingEquiv, RingEquiv.symm_symm]
  change (algebraMap k (End (module (k := k) S hS)) c).asHom = _
  simp only [Algebra.algebraMap_eq_smul_one, End.smul_asHom, End.one_asHom]

/-- The ring equivalence reads the coefficient at any point of the support. -/
theorem endRingEquiv_apply (S : Set P) (hS : S.OrdConnected) (hne : S.Nonempty)
    (α : End (module (k := k) S hS)) {x : P} (hx : x ∈ S) :
    endRingEquiv S hS hne α = (((α.asHom.app x).hom (one (k := k) S hx)) : k) := by
  obtain ⟨c, hc⟩ := exists_smul_id S hS α.asHom
  have hα : α = (endRingEquiv S hS hne).symm c := by
    rw [endRingEquiv_symm_apply]
    exact End.ext hc
  rw [hα, RingEquiv.apply_symm_apply, endRingEquiv_symm_apply]
  exact (coeff_smul_id S hS c hx).symm

private theorem comp_eq_smul_zero_of_not_mem (S T : Set P) (hS : S.OrdConnected)
    (hT : T.OrdConnected) (g : module (k := k) S hS ⟶ module T hT)
    (h : module (k := k) T hT ⟶ module S hS) (c : k) (hc : g ≫ h = c • 𝟙 _)
    {x : P} (hx : x ∈ S) (hxT : x ∉ T) : c = 0 := by
  have h1 := congrArg (fun f => (((f.app x).hom (one (k := k) S hx)) : k)) hc
  have hz : (g.app x).hom (one (k := k) S hx) = 0 :=
    Subtype.ext (val_eq_zero T hxT _)
  have h2 : (((g ≫ h).app x).hom (one (k := k) S hx) : k) = 0 := by
    change (((h.app x).hom ((g.app x).hom (one (k := k) S hx))) : k) = 0
    rw [hz, map_zero]
    rfl
  have h3 := coeff_smul_id S hS c hx
  simp only at h1
  rw [h2] at h1
  exact (h1.trans h3).symm

/-- A composite `module S ⟶ module T ⟶ module S` of interval modules over a linear order
vanishes when `S ≠ T`. The two outer supports are given as equal sets. -/
theorem comp_eq_zero_of_ne {S T S' : Set P} (hS : S.OrdConnected) (hT : T.OrdConnected)
    (hS' : S'.OrdConnected) (hSS' : S' = S) (hST : S ≠ T)
    (g : module (k := k) S hS ⟶ module T hT) (h : module (k := k) T hT ⟶ module S' hS') :
    g ≫ h = 0 := by
  subst hSS'
  obtain ⟨c, hc⟩ := exists_smul_id S' hS (g ≫ h)
  by_cases hne : S'.Nonempty
  · obtain ⟨x, hx⟩ := hne
    by_cases hsub : ∀ z ∈ S', z ∈ T
    · have hss : S' ⊂ T := lt_of_le_of_ne hsub (fun e => hST e)
      obtain ⟨y, hyT, hyS⟩ := Set.exists_of_ssubset hss
      obtain ⟨d, hd⟩ := exists_smul_id T hT (h ≫ g)
      have hd0 : d = 0 := by
        have h1 := congrArg (fun f => (((f.app y).hom (one (k := k) T hyT)) : k)) hd
        have hz : (h.app y).hom (one (k := k) T hyT) = 0 :=
          Subtype.ext (val_eq_zero S' hyS _)
        have h2 : (((h ≫ g).app y).hom (one (k := k) T hyT) : k) = 0 := by
          change (((g.app y).hom ((h.app y).hom (one (k := k) T hyT))) : k) = 0
          rw [hz, map_zero]
          rfl
        simp only at h1
        rw [h2] at h1
        exact (h1.trans (coeff_smul_id T hT d hyT)).symm
      have hhg : h ≫ g = 0 := by rw [hd, hd0, zero_smul]
      have hsq : (g ≫ h) ≫ (g ≫ h) = 0 := by
        calc (g ≫ h) ≫ (g ≫ h) = g ≫ (h ≫ g) ≫ h := by simp
          _ = 0 := by rw [hhg]; simp
      have hc2 : (c * c) • 𝟙 (module (k := k) S' hS) = 0 := by
        rw [hc] at hsq
        simpa [mul_smul] using hsq
      have hcc : c * c = 0 := by
        have h1 : coeff S' hS ((c * c) • 𝟙 (module (k := k) S' hS)) hx =
            coeff S' hS 0 hx := by rw [hc2]
        rw [coeff_smul_id S' hS _ hx] at h1
        rw [h1]
        simp [coeff]
      rw [hc, mul_self_eq_zero.mp hcc, zero_smul]
    · push Not at hsub
      obtain ⟨z, hzS, hzT⟩ := hsub
      rw [hc, comp_eq_smul_zero_of_not_mem S' T hS hT g h c hc hzS hzT, zero_smul]
  · ext p z
    have hp : p ∉ S' := fun hh => hne ⟨p, hh⟩
    have hz : z = 0 := Subtype.ext (val_eq_zero S' hp z)
    subst hz
    simp

end TDA.Persistence.SupportInterval
