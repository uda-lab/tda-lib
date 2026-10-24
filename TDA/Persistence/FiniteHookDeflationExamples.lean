import TDA.Persistence.FiniteHookDeflation

/-!
# Consumers of finite hook deflations

A module on a branching poset has an actual non-split rank-exact deflation
from two principal upsets. It is therefore not rank projective, and the
general finite hook-sum deflation onto it cannot split either. Further
consumers retain finite-death hooks, infinite-death hooks and multiplicity.
-/

set_option autoImplicit false

namespace TDA.Persistence.FiniteHookDeflation.Examples

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

/-- Two incomparable births with a common later grade. -/
inductive ForkGrade where
  | left | right | top
  deriving DecidableEq

instance forkFintype : Fintype ForkGrade :=
  ⟨{.left, .right, .top}, by intro p; cases p <;> simp⟩

instance forkPartialOrder : PartialOrder ForkGrade where
  le a b := a = b ∨ b = .top
  le_refl _ := Or.inl rfl
  le_trans := by
    intro a b c hab hbc
    cases a <;> cases b <;> cases c <;> simp_all
  le_antisymm := by
    intro a b hab hba
    cases a <;> cases b <;> simp_all

instance forkDecidableLE : DecidableRel (fun a b : ForkGrade => a ≤ b) := by
  intro a b
  change Decidable (a = b ∨ b = .top)
  infer_instance


private instance : HasFiniteBiproducts (PModule ℚ ForkGrade) :=
  HasFiniteBiproducts.of_hasFiniteProducts

private def birth : Bool → ForkGrade | false => .left | true => .right

/-- One coefficient at all three grades; both incoming maps at the merge are identity. -/
abbrev forkModule : PModule ℚ ForkGrade :=
  (Functor.const ForkGrade).obj (ModuleCat.of ℚ ℚ)

instance forkModule_finiteDimensional (p : ForkGrade) : FiniteDimensional ℚ (forkModule.obj p) :=
  inferInstanceAs (FiniteDimensional ℚ ℚ)

private noncomputable def branches (b : Bool) : PModule ℚ ForkGrade :=
  HookInfinity.module (birth b)

private instance (b : Bool) (p : ForkGrade) : FiniteDimensional ℚ ((branches b).obj p) := by
  change FiniteDimensional ℚ (GradedFree.fiber (R := ℚ) (HookInfinity.generators (birth b)) p)
  infer_instance

private noncomputable def branchSum : PModule ℚ ForkGrade := ⨁ branches

private instance (p : ForkGrade) : FiniteDimensional ℚ (branchSum.obj p) :=
  FiniteBiproduct.finiteDimensional branches p

private noncomputable def branchMap (b : Bool) : branches b ⟶ forkModule :=
  HookInfinity.fromBirth (birth b) forkModule (1 : ℚ)

private noncomputable def mergeMap : branchSum ⟶ forkModule := biproduct.desc branchMap

private noncomputable def branchGenerator (b : Bool) : branchSum.obj (birth b) :=
  ((biproduct.ι branches b).app (birth b)).hom (HookInfinity.birth (birth b))

private theorem mergeMap_generator (b : Bool) :
    (mergeMap.app (birth b)).hom (branchGenerator b) = (1 : ℚ) := by
  have h := congrArg (fun f : branches b ⟶ forkModule =>
    (f.app (birth b)).hom (HookInfinity.birth (birth b)))
    (biproduct.ι_desc branchMap b)
  exact h.trans (HookInfinity.fromBirth_birth (birth b) forkModule (1 : ℚ))

private theorem mergeMap_surjective (p : ForkGrade) :
    Function.Surjective (mergeMap.app p).hom := by
  obtain ⟨b, hb⟩ : ∃ b, birth b ≤ p := by
    cases p
    · exact ⟨false, le_rfl⟩
    · exact ⟨true, le_rfl⟩
    · exact ⟨false, Or.inr rfl⟩
  intro n
  change ℚ at n
  let v := structureMapLinear branchSum hb (branchGenerator b)
  have hv : (mergeMap.app p).hom v = (1 : ℚ) := by
    have h := congrArg (fun f => f.hom (branchGenerator b))
      (mergeMap.naturality (homOfLE hb))
    change (mergeMap.app p).hom v =
      structureMapLinear forkModule hb ((mergeMap.app (birth b)).hom (branchGenerator b)) at h
    exact h.trans (congrArg (structureMapLinear forkModule hb) (mergeMap_generator b))
  refine ⟨n • v, ?_⟩
  exact (map_smul (mergeMap.app p).hom n v).trans
    ((congrArg (fun x => n • x) hv).trans (mul_one n))

/-- A concrete rank-exact kernel sequence whose quotient map does not split. -/
private theorem merge_rankExact : IsRankExact (kernel.ι mergeMap) mergeMap := by
  apply RankKernel.rankExact mergeMap mergeMap_surjective
  intro a b hab n hn
  have hn0 : n = 0 := hn
  subst n
  exact ⟨0, by simp, by simp⟩

private theorem projection_top_eq_zero (s : forkModule ⟶ branchSum) (b : Bool) :
    ((biproduct.π branches b).app .top).hom ((s.app .top).hom (1 : ℚ)) = 0 := by
  have hb : birth (!b) ≤ (.top : ForkGrade) := Or.inr rfl
  have hnot : ¬ birth b ≤ birth (!b) := by cases b <;> decide
  let α := s ≫ biproduct.π branches b
  have hz : (α.app (birth (!b))).hom (1 : ℚ) = 0 :=
    HookInfinity.fiber_eq_zero_of_not_le hnot _
  have h := congrArg (fun f => f.hom (1 : ℚ)) (α.naturality (homOfLE hb))
  change (α.app .top).hom (1 : ℚ) = structureMapLinear (branches b) hb
    ((α.app (birth (!b))).hom (1 : ℚ)) at h
  exact h.trans (by rw [hz, map_zero])

/-- Naturality at the two incomparable births rules out every section. -/
private theorem merge_not_split : ¬ ∃ s : forkModule ⟶ branchSum, s ≫ mergeMap = 𝟙 forkModule := by
  rintro ⟨s, hs⟩
  have hv : (s.app .top).hom (1 : ℚ) = 0 := by
    apply FiniteBiproduct.element_ext branches .top
    intro b
    exact (projection_top_eq_zero s b).trans (map_zero _).symm
  have h := congrArg (fun f : forkModule ⟶ forkModule => (f.app .top).hom (1 : ℚ)) hs
  change (mergeMap.app .top).hom ((s.app .top).hom (1 : ℚ)) = (1 : ℚ) at h
  rw [hv, map_zero] at h
  exact (zero_ne_one : (0 : ℚ) ≠ (1 : ℚ)) h

/-- Pointwise finite dimension alone does not imply rank projectivity. -/
theorem fork_not_rankProjective : ¬ IsRankProjective forkModule := by
  intro h
  exact merge_not_split (h _ _ _ _ _ merge_rankExact (𝟙 forkModule))

/-- The constructed hook deflation is genuinely rank exact even on this
non-projective branching module, and has no section. -/
theorem fork_deflation_non_split :
    IsRankExact (kernel.ι (π forkModule)) (π forkModule) ∧
      ¬ ∃ s : forkModule ⟶ module forkModule, s ≫ π forkModule = 𝟙 forkModule :=
  ⟨rankExact forkModule, fun h => fork_not_rankProjective
    ((isRankProjective_iff_retract forkModule).mpr h)⟩

private instance zeroFiberSubsingleton {P : Type} [PartialOrder P] (p : P) :
    Subsingleton ((0 : PModule ℚ P).obj p) :=
  ModuleCat.subsingleton_of_isZero (Functor.zero_obj p)

private instance zeroFiberFiniteDimensional {P : Type} [PartialOrder P] (p : P) :
    FiniteDimensional ℚ ((0 : PModule ℚ P).obj p) := by infer_instance

/-- The zero module contributes no hook occurrences. -/
theorem zero_occurrences : Fintype.card (Index (0 : PModule ℚ ForkGrade)) = 0 := by
  rw [card_index]
  simp only [Module.finrank_zero_of_subsingleton, Finset.sum_const_zero, add_zero]

/-- The empty indexing poset is included in the actual rank-exact construction. -/
theorem empty_poset :
    Fintype.card (Index (0 : PModule ℚ (Fin 0))) = 0 ∧
      IsRankExact (kernel.ι (π (0 : PModule ℚ (Fin 0)))) (π (0 : PModule ℚ (Fin 0))) :=
  ⟨by simp, rankExact _⟩

/-- Two coefficients at one grade are retained as two principal-upset occurrences. -/
abbrev doubleModule : PModule ℚ (Fin 1) :=
  (Functor.const (Fin 1)).obj (ModuleCat.of ℚ (ℚ × ℚ))

/-- The concrete multiplicity-two fiber is finite-dimensional. -/
instance doubleModule_finiteDimensional (p : Fin 1) : FiniteDimensional ℚ (doubleModule.obj p) :=
  inferInstanceAs (FiniteDimensional ℚ (ℚ × ℚ))

/-- Repeated birth grades are counted with multiplicity. -/
theorem repeated_occurrences : Fintype.card (Index doubleModule) = 2 := by
  classical
  rw [card_index]
  conv_lhs =>
    lhs
    equals 0 =>
      apply Finset.sum_eq_zero
      intro ab _
      exact False.elim ((not_lt_of_ge (le_of_eq (Subsingleton.elim ab.val.2 ab.val.1))) ab.property)
  simp [doubleModule, Module.finrank_prod]

/-- A single finite-death hook on a two-grade chain. -/
noncomputable abbrev finiteHook : PModule ℚ (Fin 2) := Hook.module 0 1

/-- A nonzero element dying at grade one has a genuinely dying lift. -/
theorem finite_death_nonzero_lift :
    ∃ m : (module finiteHook).obj 0, ((π finiteHook).app 0).hom m ≠ 0 ∧
      structureMapLinear (module finiteHook) (show (0 : Fin 2) ≤ 1 by decide) m = 0 := by
  let n : finiteHook.obj 0 :=
    SupportInterval.one (Hook.support (0 : Fin 2) 1) (Hook.birth_mem (by decide))
  have hn : structureMapLinear finiteHook (show (0 : Fin 2) ≤ 1 by decide) n = 0 :=
    Hook.generator_dies (by decide : (0 : Fin 2) < 1) (𝟙 finiteHook)
  obtain ⟨m, hm, hdie⟩ := lift_kernel finiteHook (show (0 : Fin 2) ≤ 1 by decide) n hn
  refine ⟨m, ?_, hdie⟩
  rw [hm]
  intro h
  have hz := congrArg Subtype.val h
  exact (one_ne_zero : (1 : ℚ) ≠ 0) hz

/-- Infinite-death hooks split their actual finite hook deflation. -/
theorem infinite_death_retract :
    ∃ s : HookInfinity.module (R := ℚ) (0 : Fin 2) ⟶
        module (HookInfinity.module (R := ℚ) (0 : Fin 2)),
      s ≫ π (HookInfinity.module (R := ℚ) (0 : Fin 2)) =
        𝟙 (HookInfinity.module (R := ℚ) (0 : Fin 2)) :=
  exists_retract _ (HookInfinity.isRankProjective _)

/-- The same deflation theorem applies in characteristic two. -/
abbrev binaryModule : PModule (ZMod 2) ForkGrade :=
  (Functor.const ForkGrade).obj (ModuleCat.of (ZMod 2) (ZMod 2))

instance binaryModule_finiteDimensional (p : ForkGrade) : FiniteDimensional (ZMod 2) (binaryModule.obj p) :=
  inferInstanceAs (FiniteDimensional (ZMod 2) (ZMod 2))

/-- Characteristic two preserves rank exactness and relative projectivity of the sum. -/
theorem characteristic_two :
    IsRankExact (kernel.ι (π binaryModule)) (π binaryModule) ∧
      IsRankProjective (module binaryModule) :=
  ⟨rankExact _, isRankProjective _⟩

end TDA.Persistence.FiniteHookDeflation.Examples
