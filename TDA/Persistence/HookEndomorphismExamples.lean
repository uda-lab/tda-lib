import TDA.Persistence.HookEndomorphisms

/-!
# Consumers of hook endomorphisms

The two-coordinate hook has genuinely unbounded support. Its scalar
endomorphisms and binary indecomposability coexist with a decomposable
sum of two equal occurrences. Further consumers distinguish finite and
infinite death, recover individual endpoints, and check characteristic two
and excluded zero hooks.
-/

set_option autoImplicit false

namespace TDA.Persistence.HookEndomorphismExamples

open CategoryTheory CategoryTheory.Limits

private instance {k : Type*} [Field k] {P : Type*} [PartialOrder P] :
    HasBinaryBiproducts (PModule.{_,_,_} k P) :=
  HasBinaryBiproducts.of_hasBinaryProducts

/-- Birth at the origin in the two-coordinate order. -/
def origin : Fin 2 → ℝ := fun _ => 0

/-- A finite death one unit later in each coordinate. -/
def death : Fin 2 → ℝ := fun _ => 1

private theorem origin_lt_death : origin < death := by
  apply lt_of_le_of_ne
  · intro i; norm_num [origin, death]
  · intro h
    have h0 := congrFun h 0
    norm_num [origin, death] at h0

/-- A genuine two-coordinate hook is indecomposable and contains an unbounded ray. -/
theorem unbounded_hook :
    Indecomposable (Hook.module (k := ℚ) origin death) ∧
      ∀ t : ℝ, 0 ≤ t → (fun i : Fin 2 => if i = 0 then t else 0) ∈
        Hook.support origin death := by
  refine ⟨Hook.indecomposable origin_lt_death, ?_⟩
  intro t ht
  constructor
  · intro i
    simp only [origin]
    split_ifs
    · exact ht
    · exact le_rfl
  · intro h
    have h1 := h 1
    norm_num [death] at h1

/-- Multiplication in the actual endomorphism ring has the expected nontrivial value. -/
theorem scalar_composition :
    (Hook.endRingEquiv (k := ℚ) origin_lt_death).symm 2 ≫
      (Hook.endRingEquiv (k := ℚ) origin_lt_death).symm 3 =
        (6 : ℚ) • 𝟙 (Hook.module (k := ℚ) origin death) := by
  rw [← Hook.endRingEquiv_symm_apply origin_lt_death (6 : ℚ)]
  let e := Hook.endRingEquiv (k := ℚ) origin_lt_death
  apply e.injective
  change e (e.symm 3 * e.symm 2) = e (e.symm 6)
  rw [map_mul, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply,
    RingEquiv.apply_symm_apply]
  norm_num

/-- Two identical hook occurrences really form a decomposable object. -/
theorem repeated_hook_not_indecomposable :
    ¬ Indecomposable (Hook.module (k := ℚ) origin death ⊞ Hook.module origin death) := by
  intro h
  rcases h.2 _ _ (Iso.refl _) with h0 | h0 <;>
    exact (Hook.indecomposable (k := ℚ) origin_lt_death).1 h0

/-- Principal upsets remain indecomposable on the real plane. -/
theorem infinite_death : Indecomposable (HookInfinity.module (R := ℚ) origin) :=
  HookInfinity.indecomposable origin

/-- The same birth cannot identify finite and infinite death. -/
theorem finite_ne_infinite :
    ¬ Nonempty (Hook.module (k := ℚ) origin death ≅ HookInfinity.module (R := ℚ) origin) :=
  Hook.not_nonempty_iso_infinity origin_lt_death

/-- An isomorphism must retain the individual finite hook endpoints. -/
theorem recover_finite_endpoints {i j : Fin 2 → ℝ} (hij : i < j)
    (e : Hook.module (k := ℚ) origin death ≅ Hook.module i j) :
    i = origin ∧ j = death := by
  obtain ⟨hi, hj⟩ := Hook.endpoints_eq_of_iso origin_lt_death hij e
  exact ⟨hi.symm, hj.symm⟩

/-- The infinite-death isomorphism law recovers its birth. -/
theorem recover_infinite_birth {i : Fin 2 → ℝ}
    (e : HookInfinity.module (R := ℚ) origin ≅ HookInfinity.module i) : i = origin :=
  (HookInfinity.birth_eq_of_iso e).symm

/-- Characteristic two preserves both the ring comparison and indecomposability. -/
theorem characteristic_two :
    Indecomposable (Hook.module (k := ZMod 2) (0 : Fin 2) 1) ∧
      (Hook.endRingEquiv (k := ZMod 2) (by decide : (0 : Fin 2) < 1))
        ((1 : ZMod 2) • 𝟙 (Hook.module (k := ZMod 2) (0 : Fin 2) 1) +
          (1 : ZMod 2) • 𝟙 (Hook.module (k := ZMod 2) (0 : Fin 2) 1)) = 0 := by
  constructor
  · exact Hook.indecomposable (by decide)
  · simp only [one_smul]
    change (Hook.endRingEquiv (k := ZMod 2) (by decide : (0 : Fin 2) < 1))
      ((1 : End (Hook.module (k := ZMod 2) (0 : Fin 2) 1)) + 1) = 0
    rw [map_add, map_one]
    decide

/-- Equal birth and death give a zero object, hence no indecomposable nonzero hook. -/
theorem degenerate_hook :
    IsZero (Hook.module (k := ℚ) origin origin) ∧
      ¬ Indecomposable (Hook.module (k := ℚ) origin origin) :=
  ⟨Hook.isZero_of_le le_rfl, fun h => h.1 (Hook.isZero_of_le le_rfl)⟩

end TDA.Persistence.HookEndomorphismExamples
