import TDA.Persistence.FiniteRankProjectiveHomQuotientDimension

/-!
# Nonprojective hook-generator Hom on the Boolean square

For every field, the module supported only at the bottom of `Bool × Bool` is not rank
projective. Its actual hook-generator Hom module has ordinary projective dimension one, and
its minimal finite rank-projective resolutions have a nonzero degree-one term and vanish above
degree one. Such a certified resolution is constructed from the field alone by the finite-poset
existence theorem.

The square uses the preorder category selected by the scoped instance below. Consumers can
select it with `open scoped TDA.Persistence.FiniteRankProjectiveHomNonprojectiveExamples`.
-/

set_option autoImplicit false
universe u

namespace TDA.Persistence.FiniteRankProjectiveHomNonprojectiveExamples

open CategoryTheory CategoryTheory.Limits
open TDA.Persistence
open TDA.Persistence.PrincipalDownsetRankResolution
open TDA.Persistence.FiniteRankProjectiveHomExact
open scoped ZeroObject

/-- The four-element finite lattice used by this example. -/
abbrev Square := Bool × Bool
/-- Select the preorder category on `Square` when this fixture's scope is open. -/
scoped instance (priority := 10000) squarePreorderCategory : CategoryTheory.SmallCategory Square :=
  Preorder.smallCategory Square

open scoped TDA.Persistence.FiniteRankProjectiveHomNonprojectiveExamples
private def atom : Bool → Square | false => (true, false) | true => (false, true)

variable {k : Type u} [Field k]

/-- The principal-downset module supported at the bottom of the Boolean square. -/
noncomputable abbrev bottomSimple : PModule.{u,0,u} k Square :=
  PrincipalDownsetInjective.module (k := k) (⊥ : Square)

/-- Every fiber of `bottomSimple` is finite-dimensional over its coefficient field. -/
theorem bottomSimple_finiteDimensional (p : Square) :
    FiniteDimensional k ((bottomSimple (k := k)).obj p) := by infer_instance

private instance : HasFiniteBiproducts (PModule k Square) :=
  HasFiniteBiproducts.of_hasFiniteProducts

private theorem atom_pos (b : Bool) : (⊥ : Square) < atom b := by
  classical
  cases b <;> exact lt_of_le_of_ne bot_le (by decide)

private theorem atom_ne_bot (b : Bool) : atom b ≠ (⊥ : Square) := by cases b <;> decide

private theorem atom_in_opposite_hook (b : Bool) :
    atom (!b) ∈ Hook.support (⊥ : Square) (atom b) := by cases b <;> decide

private noncomputable abbrev unit : (bottomSimple (k := k)).obj (⊥ : Square) :=
  SupportInterval.one (k := k) (Set.Iic (⊥ : Square)) (p := (⊥ : Square))
    (show (⊥ : Square) ≤ ⊥ from le_rfl)

private theorem unit_ne_zero : unit (k := k) ≠ 0 := by
  intro h
  exact (one_ne_zero : (1 : k) ≠ 0) (congrArg Subtype.val h)

private theorem off_bottom_zero (p : Square) (hp : p ≠ ⊥)
    (x : (bottomSimple (k := k)).obj p) : x = 0 := by
  apply Subtype.ext
  exact SupportInterval.val_eq_zero (Set.Iic (⊥ : Square))
    (fun h => hp (le_bot_iff.mp h)) x

private noncomputable abbrev branches (b : Bool) : PModule k Square :=
  Hook.module ⊥ (atom b)

private instance (b : Bool) (p : Square) :
    FiniteDimensional k ((branches (k := k) b).obj p) := by
  change FiniteDimensional k (SupportInterval.fiber (k := k) _ _)
  infer_instance

private noncomputable abbrev branchSum : PModule k Square := ⨁ (branches (k := k))

private instance (p : Square) : FiniteDimensional k ((branchSum (k := k)).obj p) :=
  FiniteBiproduct.finiteDimensional (branches (k := k)) p

private theorem unit_dies (b : Bool) :
    structureMapLinear (bottomSimple (k := k)) (atom_pos b).le unit = 0 :=
  off_bottom_zero _ (atom_ne_bot b) _

private noncomputable def branchMap (b : Bool) :
    branches (k := k) b ⟶ bottomSimple :=
  Hook.fromGenerator (atom_pos b) bottomSimple unit (unit_dies b)

private noncomputable def quotient : branchSum (k := k) ⟶ bottomSimple :=
  biproduct.desc (branchMap (k := k))

private noncomputable def branchGenerator (b : Bool) :
    (branchSum (k := k)).obj (⊥ : Square) :=
  ((biproduct.ι (branches (k := k)) b).app ⊥).hom
    (SupportInterval.one (Hook.support (⊥ : Square) (atom b)) (Hook.birth_mem (atom_pos b)))

private theorem quotient_generator (b : Bool) :
    ((quotient (k := k)).app ⊥).hom (branchGenerator b) = unit := by
  have h := congrArg (fun f : branches (k := k) b ⟶ bottomSimple =>
    (f.app ⊥).hom (SupportInterval.one (Hook.support (⊥ : Square) (atom b))
      (Hook.birth_mem (atom_pos b)))) (biproduct.ι_desc (branchMap (k := k)) b)
  exact h.trans (Hook.fromGenerator_birth (atom_pos b) bottomSimple unit (unit_dies b))

private theorem quotient_surjective (p : Square) :
    Function.Surjective (((quotient (k := k)).app p).hom) := by
  intro x
  by_cases hp : p = ⊥
  · subst p
    refine ⟨(x : k) • branchGenerator false, ?_⟩
    rw [map_smul, quotient_generator]
    apply Subtype.ext
    change (x : k) * 1 = (x : k)
    exact mul_one _
  · refine ⟨0, ?_⟩
    rw [map_zero, off_bottom_zero p hp x]

private theorem branchGenerator_dies (b : Bool) {p : Square} (hp : atom b ≤ p) :
    structureMapLinear (branchSum (k := k)) (bot_le : (⊥ : Square) ≤ p)
      (branchGenerator b) = 0 := by
  have hn := congrArg (fun f => f.hom
    (SupportInterval.one (Hook.support (⊥ : Square) (atom b)) (Hook.birth_mem (atom_pos b))))
      ((biproduct.ι (branches (k := k)) b).naturality
        (homOfLE (bot_le : (⊥ : Square) ≤ p)))
  change ((biproduct.ι (branches (k := k)) b).app p).hom
      (structureMapLinear (branches b) bot_le _) = _ at hn
  have hz : structureMapLinear (branches (k := k) b)
      (bot_le : (⊥ : Square) ≤ p) = 0 :=
    (SupportInterval.structureMap_eq_zero_iff
      (Hook.support (⊥ : Square) (atom b)) (Hook.support_ordConnected _ _)
      (bot_le : (⊥ : Square) ≤ p)).mpr (fun h => h.2.2 hp)
  rw [hz, LinearMap.zero_apply, map_zero] at hn
  exact hn.symm

private theorem above_atom (p : Square) (hp : p ≠ ⊥) : ∃ b, atom b ≤ p := by
  rcases p with ⟨a, b⟩
  cases a <;> cases b
  · exact (hp rfl).elim
  · exact ⟨true, le_rfl⟩
  · exact ⟨false, le_rfl⟩
  · exact ⟨false, by decide⟩

private theorem quotient_rankExact :
    IsRankExact (kernel.ι (quotient (k := k))) quotient := by
  apply RankKernel.rankExact quotient quotient_surjective
  intro a b hab x hx
  by_cases ha : a = ⊥
  · subst a
    by_cases hb : b = ⊥
    · subst b
      have hx0 : x = 0 := by simpa using hx
      subst x
      exact ⟨0, by simp, by simp⟩
    · obtain ⟨i, hi⟩ := above_atom b hb
      refine ⟨(x : k) • branchGenerator i, ?_, ?_⟩
      · rw [map_smul, quotient_generator]
        apply Subtype.ext
        exact mul_one _
      · rw [map_smul, branchGenerator_dies i hi, smul_zero]
  · rw [off_bottom_zero a ha x]
    exact ⟨0, by simp, by simp⟩

private theorem section_coordinate_zero
    (s : bottomSimple (k := k) ⟶ branchSum) (b : Bool) :
    ((biproduct.π (branches (k := k)) b).app ⊥).hom ((s.app ⊥).hom unit) = 0 := by
  let α := s ≫ biproduct.π (branches (k := k)) b
  have hn := congrArg (fun f => f.hom (unit (k := k)))
    (α.naturality (homOfLE (bot_le : (⊥ : Square) ≤ atom (!b))))
  change (α.app (atom (!b))).hom (structureMapLinear bottomSimple bot_le unit) =
    structureMapLinear (branches b) bot_le ((α.app ⊥).hom unit) at hn
  have hz : structureMapLinear (bottomSimple (k := k))
      (bot_le : (⊥ : Square) ≤ atom (!b)) unit = 0 :=
    off_bottom_zero _ (atom_ne_bot (!b)) _
  rw [hz, map_zero] at hn
  apply Subtype.ext
  have hc := congrArg Subtype.val hn
  change (0 : k) =
    (structureMapLinear (SupportInterval.module (Hook.support (⊥ : Square) (atom b))
      (Hook.support_ordConnected _ _)) bot_le ((α.app ⊥).hom unit) : k) at hc
  rw [SupportInterval.structureMap_val, if_pos (atom_in_opposite_hook b)] at hc
  exact hc.symm

private theorem quotient_not_split :
    ¬ ∃ s : bottomSimple (k := k) ⟶ branchSum, s ≫ quotient = 𝟙 bottomSimple := by
  rintro ⟨s, hs⟩
  have hv : (s.app ⊥).hom unit = 0 := by
    apply FiniteBiproduct.element_ext (branches (k := k)) ⊥
    intro b
    rw [section_coordinate_zero s b, map_zero]
  have h := congrArg (fun f : bottomSimple (k := k) ⟶ bottomSimple =>
    (f.app ⊥).hom unit) hs
  change (quotient.app ⊥).hom ((s.app ⊥).hom unit) = unit at h
  rw [hv, map_zero] at h
  exact unit_ne_zero h.symm

/-- The bottom-supported module fails the relative rank-projective lifting property. -/
theorem bottomSimple_not_rankProjective : ¬ IsRankProjective (bottomSimple (k := k)) := by
  intro h
  exact quotient_not_split (h _ _ _ _ _ quotient_rankExact (𝟙 bottomSimple))

/-- The actual hook-generator Hom module is not categorically projective. -/
theorem bottomSimple_hom_not_projective :
    ¬ Projective ((homFunctor (k := k) (S := Square)).obj bottomSimple) := by
  intro h
  have := h
  apply bottomSimple_not_rankProjective (k := k)
  have : Module.Projective (HomScalars (k := k) (S := Square))
      ((homFunctor (k := k) (S := Square)).obj (bottomSimple (k := k))) :=
    ModuleCat.projective_of_module_projective _
  exact (FiniteRankProjectiveHomFullyFaithful.rankProjective_iff_homProjective
    bottomSimple bottomSimple_finiteDimensional).mpr inferInstance

private theorem bottomSimple_has_minimal_resolution :
    Nonempty (MinimalFiniteRankProjectiveResolution (k := k) (M := bottomSimple)) :=
  FiniteRankProjectiveResolution.exists_minimalFiniteRankProjectiveResolution_of_pfd_finitePoset
    bottomSimple bottomSimple_finiteDimensional

private theorem minimalComplement_bottom :
    minimalComplement (⊥ : Square) = {atom false, atom true} := by
  ext p
  change Minimal (fun x : Square => ¬ x ≤ ⊥) p ↔ p = atom false ∨ p = atom true
  rcases p with ⟨a, b⟩
  simp only [Minimal, Prod.forall, Bool.forall_bool]
  cases a <;> cases b <;> decide

private theorem complementCard_bottom : complementCard (⊥ : Square) = 2 := by
  classical
  unfold complementCard
  rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, minimalComplement_bottom]
  have hn : atom false ≠ atom true := by decide
  simp [hn]

private theorem bottomSimple_hom_projectiveDimension_le_one :
    HasProjectiveDimensionLE
      ((homFunctor (k := k) (S := Square)).obj bottomSimple) 1 := by
  have h := PrincipalDownsetRankDimension.hasProjectiveDimensionLE (k := k) (⊥ : Square)
  simpa only [complementCard_bottom, Nat.reduceSub] using h

/-- The ordinary projective dimension of the actual Hom module is exactly one. -/
theorem bottomSimple_hom_projectiveDimension_eq_one :
    projectiveDimension ((homFunctor (k := k) (S := Square)).obj bottomSimple) = 1 := by
  apply le_antisymm
  · exact (projectiveDimension_le_iff _ 1).mpr bottomSimple_hom_projectiveDimension_le_one
  · apply (projectiveDimension_ge_iff _ 1).mpr
    intro h
    exact bottomSimple_hom_not_projective
      (projective_iff_hasProjectiveDimensionLT_one.mpr h)

/-- Every certified minimal resolution vanishes in degrees above one. -/
theorem bottomSimple_terms_vanish_above_one
    (R : MinimalFiniteRankProjectiveResolution (k := k) (M := bottomSimple)) :
    ∀ j, 1 < j → IsZero (R.termAt j) :=
  (FiniteRankProjectiveHomDimension.hasProjectiveDimensionLE_iff R 1).mp
    bottomSimple_hom_projectiveDimension_le_one

/-- Every certified minimal resolution has a nonzero degree-one term. -/
theorem bottomSimple_first_term_nonzero
    (R : MinimalFiniteRankProjectiveResolution (k := k) (M := bottomSimple)) :
    ¬ IsZero (R.termAt 1) := by
  intro hz
  have hdim : HasProjectiveDimensionLE
      ((homFunctor (k := k) (S := Square)).obj bottomSimple) 0 := by
    apply (FiniteRankProjectiveHomDimension.hasProjectiveDimensionLE_iff R 0).mpr
    intro j hj
    by_cases he : j = 1
    · simpa only [he] using hz
    · exact bottomSimple_terms_vanish_above_one R j (by omega)
  exact bottomSimple_hom_not_projective
    ((projective_iff_hasProjectiveDimensionLE_zero _).mpr hdim)

/-- The field alone yields an actual minimal resolution with nonzero degree one and
zero terms in higher degrees. -/
theorem bottomSimple_exists_minimal_resolution_nonzero_first_term :
    ∃ R : MinimalFiniteRankProjectiveResolution (k := k) (M := bottomSimple),
      ¬ IsZero (R.termAt 1) ∧ (∀ j, 1 < j → IsZero (R.termAt j)) := by
  obtain ⟨R⟩ := bottomSimple_has_minimal_resolution (k := k)
  exact ⟨R, bottomSimple_first_term_nonzero R, bottomSimple_terms_vanish_above_one R⟩

/-- The bottom fiber contains the nonzero supported unit. -/
theorem bottomSimple_nonzero :
    ∃ x : (bottomSimple (k := k)).obj (⊥ : Square), x ≠ 0 :=
  ⟨unit, unit_ne_zero⟩

private theorem bottomSimple_hom_nonzero :
    ¬ IsZero ((homFunctor (k := k) (S := Square)).obj bottomSimple) := by
  intro hzero
  have hz := (FiniteRankProjectiveHomDimension.isZero_hom_obj_iff _).mp hzero
  obtain ⟨x, hx⟩ := bottomSimple_nonzero (k := k)
  have hid := hz.eq_of_src (𝟙 (bottomSimple (k := k))) 0
  have he := congrArg (fun f : bottomSimple (k := k) ⟶ bottomSimple => (f.app ⊥).hom x) hid
  exact hx (by simpa using he)


example :
    ∃ R : MinimalFiniteRankProjectiveResolution (k := ℚ)
        (M := bottomSimple (k := ℚ)),
      ¬ IsZero (R.termAt 1) ∧ (∀ j, 1 < j → IsZero (R.termAt j)) :=
  bottomSimple_exists_minimal_resolution_nonzero_first_term (k := ℚ)

example :
    ∃ R : MinimalFiniteRankProjectiveResolution (k := ZMod 2)
        (M := bottomSimple (k := ZMod 2)),
      ¬ IsZero (R.termAt 1) ∧ (∀ j, 1 < j → IsZero (R.termAt j)) :=
  bottomSimple_exists_minimal_resolution_nonzero_first_term (k := ZMod 2)

end TDA.Persistence.FiniteRankProjectiveHomNonprojectiveExamples
