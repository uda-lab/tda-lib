import TDA.Persistence.RankDeflation
import TDA.Persistence.FiniteHookDeflation
import TDA.Persistence.HookEndomorphisms
import Mathlib.Tactic.FinCases

/-!
# Consumers and a non-admissible epimorphism

Composing and pulling back the constructed finite hook deflations retains
actual dying nonzero lifts. Zero base change and characteristic two are
included. In contrast, the quotient from a principal upset onto its
finite-death truncation is pointwise surjective but fails rank admissibility:
its dying generator cannot have a dying lift in the principal upset.
-/

set_option autoImplicit false

namespace TDA.Persistence.RankDeflationExamples

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

/-- A nonzero vector that dies along a two-grade chain. -/
noncomputable abbrev dyingModule : PModule ℚ (Fin 2) := Hook.module 0 1

private noncomputable def birthVector : dyingModule.obj 0 :=
  SupportInterval.one (Hook.support (0 : Fin 2) 1) (Hook.birth_mem (by decide))

private theorem birthVector_ne_zero : birthVector ≠ 0 :=
  fun h => (one_ne_zero : (1 : ℚ) ≠ 0) (congrArg Subtype.val h)

private theorem birthVector_dies :
    structureMapLinear dyingModule (show (0 : Fin 2) ≤ 1 by decide) birthVector = 0 :=
  Hook.generator_dies (by decide : (0 : Fin 2) < 1) (𝟙 dyingModule)

/-- Composing two actual finite hook deflations has its actual rank-exact kernel. -/
theorem composed_actual_kernel :
    IsRankExact (kernel.ι (FiniteHookDeflation.π (FiniteHookDeflation.module dyingModule) ≫
      FiniteHookDeflation.π dyingModule))
      (FiniteHookDeflation.π (FiniteHookDeflation.module dyingModule) ≫
        FiniteHookDeflation.π dyingModule) :=
  ((FiniteHookDeflation.rankExact (FiniteHookDeflation.module dyingModule)).isRankDeflation.comp
    (FiniteHookDeflation.rankExact dyingModule).isRankDeflation).rankExact_kernel

/-- A nonzero dying vector lifts through both constructed quotient maps. -/
theorem composed_dying_nonzero :
    ∃ x : (FiniteHookDeflation.module (FiniteHookDeflation.module dyingModule)).obj 0,
      (((FiniteHookDeflation.π (FiniteHookDeflation.module dyingModule) ≫
        FiniteHookDeflation.π dyingModule).app 0).hom x) ≠ 0 ∧
      structureMapLinear (FiniteHookDeflation.module (FiniteHookDeflation.module dyingModule))
        (show (0 : Fin 2) ≤ 1 by decide) x = 0 := by
  obtain ⟨x, hx, hdie⟩ := composed_actual_kernel.lift_kernel
    (show (0 : Fin 2) ≤ 1 by decide) birthVector birthVector_dies
  exact ⟨x, by rw [hx]; exact birthVector_ne_zero, hdie⟩

/-- A nonidentity base-change map on the dying module. -/
noncomputable def twice : dyingModule ⟶ dyingModule := (2 : ℚ) • 𝟙 dyingModule

/-- The actual pullback projection along the nonidentity map is rank exact. -/
theorem pulled_actual_kernel :
    IsRankExact (kernel.ι (pullback.snd (FiniteHookDeflation.π dyingModule) twice))
      (pullback.snd (FiniteHookDeflation.π dyingModule) twice) :=
  ((FiniteHookDeflation.rankExact dyingModule).isRankDeflation.pullback_snd twice).rankExact_kernel

/-- A genuinely dying nonzero vector survives the actual pullback lift. -/
theorem pulled_dying_nonzero :
    ∃ x : (pullback (FiniteHookDeflation.π dyingModule) twice).obj 0,
      (((pullback.snd (FiniteHookDeflation.π dyingModule) twice).app 0).hom x) ≠ 0 ∧
      structureMapLinear (pullback (FiniteHookDeflation.π dyingModule) twice)
        (show (0 : Fin 2) ≤ 1 by decide) x = 0 := by
  obtain ⟨x, hx, hdie⟩ := pulled_actual_kernel.lift_kernel
    (show (0 : Fin 2) ≤ 1 by decide) birthVector birthVector_dies
  exact ⟨x, by rw [hx]; exact birthVector_ne_zero, hdie⟩

/-- At zero base change the second coordinate can be nonzero while the first is zero. -/
theorem zero_pair_vector :
    ∃ x : (pullback (FiniteHookDeflation.π dyingModule) (0 : dyingModule ⟶ dyingModule)).obj 0,
      (((pullback.fst (FiniteHookDeflation.π dyingModule) (0 : dyingModule ⟶ dyingModule)).app 0).hom x)
        = 0 ∧
      (((pullback.snd (FiniteHookDeflation.π dyingModule) (0 : dyingModule ⟶ dyingModule)).app 0).hom x)
        ≠ 0 := by
  refine ⟨PullbackFiber.mk (FiniteHookDeflation.π dyingModule)
    (0 : dyingModule ⟶ dyingModule) 0 0 birthVector (by simp), ?_, ?_⟩
  · exact PullbackFiber.fst_mk _ _ _ _ _ _
  · rw [PullbackFiber.snd_mk]
    exact birthVector_ne_zero

/-- Even zero base change produces an actual rank-exact kernel sequence. -/
theorem zero_basechange_rankExact :
    IsRankExact (kernel.ι (pullback.snd (FiniteHookDeflation.π dyingModule)
      (0 : dyingModule ⟶ dyingModule)))
      (pullback.snd (FiniteHookDeflation.π dyingModule) (0 : dyingModule ⟶ dyingModule)) :=
  ((FiniteHookDeflation.rankExact dyingModule).isRankDeflation.pullback_snd
    (0 : dyingModule ⟶ dyingModule)).rankExact_kernel

/-- A principal upset maps onto its finite-death truncation. -/
noncomputable def ordinaryQuotient : HookInfinity.module (R := ℚ) (0 : Fin 2) ⟶ dyingModule :=
  HookInfinity.fromBirth 0 dyingModule birthVector

private theorem ordinaryQuotient_surjective (p : Fin 2) :
    Function.Surjective (ordinaryQuotient.app p).hom := by
  fin_cases p
  · intro x
    refine ⟨(x : ℚ) • HookInfinity.birth (R := ℚ) (0 : Fin 2), ?_⟩
    change ((HookInfinity.fromBirth 0 dyingModule birthVector).app 0).hom
      ((x : ℚ) • HookInfinity.birth (R := ℚ) (0 : Fin 2)) = x
    rw [map_smul, HookInfinity.fromBirth_birth]
    apply Subtype.ext
    simp [birthVector, SupportInterval.one]
  · intro x
    refine ⟨0, ?_⟩
    rw [map_zero]
    exact (Subtype.ext (SupportInterval.val_eq_zero (Hook.support (0 : Fin 2) 1)
      (Hook.death_not_mem 0 1) x)).symm

private theorem ordinaryQuotient_not_admissible : ¬ IsRankDeflation ordinaryQuotient := by
  intro h
  obtain ⟨m, hm, hdie⟩ := h.rankExact_kernel.lift_kernel
    (show (0 : Fin 2) ≤ 1 by decide) birthVector birthVector_dies
  have hm0 : m = 0 := by
    apply (HookInfinity.fiberEquivOfLe (R := ℚ) (le_refl (0 : Fin 2))).injective
    rw [map_zero]
    have he := HookInfinity.fiberEquivOfLe_structureMap (R := ℚ)
      (le_refl (0 : Fin 2)) (show (0 : Fin 2) ≤ 1 by decide) m
    rw [hdie, map_zero] at he
    exact he.symm
  rw [hm0, map_zero] at hm
  exact birthVector_ne_zero hm.symm

/-- Pointwise surjectivity is strictly weaker than rank-exact admissibility. -/
theorem epi_not_rankDeflation :
    (∀ p, Function.Surjective (ordinaryQuotient.app p).hom) ∧
      ¬ IsRankDeflation ordinaryQuotient :=
  ⟨ordinaryQuotient_surjective, ordinaryQuotient_not_admissible⟩

private instance (p : Fin 1) : Subsingleton ((0 : PModule ℚ (Fin 1)).obj p) :=
  ModuleCat.subsingleton_of_isZero (Functor.zero_obj p)

private instance (p : Fin 1) : FiniteDimensional ℚ ((0 : PModule ℚ (Fin 1)).obj p) := by
  infer_instance

/-- The zero module on a nonempty grade set is included. -/
theorem zero_module : IsRankDeflation (𝟙 (0 : PModule ℚ (Fin 1))) :=
  IsRankDeflation.id _

/-- The empty grade set is included without inventing a supported generator. -/
theorem empty_poset : IsRankDeflation (𝟙 (0 : PModule ℚ (Fin 0))) := by
  let : ∀ p : Fin 0, FiniteDimensional ℚ ((0 : PModule ℚ (Fin 0)).obj p) :=
    fun p => Fin.elim0 p
  exact IsRankDeflation.id _

/-- The base change equal to twice the identity is zero in characteristic two. -/
theorem characteristic_two :
    let N := Hook.module (k := ZMod 2) (0 : Fin 2) 1
    let f : N ⟶ N := (2 : ZMod 2) • 𝟙 N
    f = 0 ∧ IsRankDeflation (pullback.snd (FiniteHookDeflation.π N) f) := by
  dsimp only
  constructor
  · have h : (2 : ZMod 2) = 0 := by decide
    rw [h, zero_smul]
  · exact (FiniteHookDeflation.rankExact _).isRankDeflation.pullback_snd _

end TDA.Persistence.RankDeflationExamples
