import TDA.Persistence.RankExactPushout
import TDA.Persistence.HookEndomorphisms

/-!
# A nonzero pushout of a split rank-exact sequence

The first example starts with the identity quotient of a one-dimensional
persistence module and pushes its zero submodule out to another copy of that
module. The resulting middle module is nonzero and has the rank-exact canonical
row.

The second example has a nonzero left term and a nonzero pushout map. The split
row `0 → U → U ⊞ H → H → 0` has the principal upset `U` born at `0` and the
finite-death hook `H` on `0 < 1`. Its left term is pushed out along the
truncation `U ⟶ H`. The pushed row is rank exact. Its middle fiber at `0`
contains a nonzero vector from the new left term, and a vector that dies at `1`
while its quotient image is nonzero.
-/

set_option autoImplicit false

namespace TDA.Persistence.RankExactPushoutExamples

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

private def constantLine : PModule.{0,0,0} ℚ (Fin 2) where
  obj _ := ModuleCat.of ℚ ℚ
  map _ := 𝟙 _
  map_id _ := by simp
  map_comp _ _ := by simp

private instance constantLine_finiteDimensional (p : Fin 2) :
    FiniteDimensional ℚ (constantLine.obj p) := by
  change FiniteDimensional ℚ ℚ
  infer_instance

private theorem identityQuotient :
    IsRankExact (0 : (0 : PModule.{0,0,0} ℚ (Fin 2)) ⟶ constantLine)
      (𝟙 constantLine) := by
  have hs : IsPointwiseShortExact
      (0 : (0 : PModule.{0,0,0} ℚ (Fin 2)) ⟶ constantLine) (𝟙 constantLine) := by
    constructor
    · intro p x y _
      exact (ModuleCat.subsingleton_of_isZero (Functor.zero_obj p)).elim _ _
    · intro p n
      exact ⟨n, rfl⟩
    · intro p
      simp
  exact hs.rankExact_of_section (𝟙 constantLine) (by simp)

private noncomputable abbrev zeroModule : PModule.{0,0,0} ℚ (Fin 2) := 0

private noncomputable abbrev zeroToLine : zeroModule ⟶ constantLine := 0

/-- The canonical row from the actual pushout is rank exact. -/
theorem pushed_row_rankExact :
    IsRankExact (Limits.pushout.inr zeroToLine zeroToLine)
      (identityQuotient.toIsPointwiseShortExact.pushoutQuotient zeroToLine) := by
  letI : ∀ p : Fin 2, FiniteDimensional ℚ (constantLine.obj p) := fun _ => inferInstance
  exact identityQuotient.pushout zeroToLine

/-- The pushout middle fiber contains the image of a nonzero vector. -/
theorem pushed_middle_nontrivial :
    ∃ x : (Limits.pushout zeroToLine zeroToLine).obj 0, x ≠ 0 := by
  have hnontrivial : Nontrivial (constantLine.obj (0 : Fin 2)) := by
    change Nontrivial ℚ
    infer_instance
  letI := hnontrivial
  obtain ⟨v, hv⟩ := exists_ne (0 : constantLine.obj (0 : Fin 2))
  refine ⟨((Limits.pushout.inr zeroToLine zeroToLine).app 0).hom v, ?_⟩
  intro hx
  have hx' : ((Limits.pushout.inr zeroToLine zeroToLine).app 0).hom v =
      ((Limits.pushout.inr zeroToLine zeroToLine).app 0).hom 0 := by
    rw [map_zero]
    exact hx
  exact hv ((pushed_row_rankExact.toIsPointwiseShortExact.injective 0 hx'))

private instance : HasBinaryBiproducts (PModule.{0,0,0} ℚ (Fin 2)) :=
  HasBinaryBiproducts.of_hasBinaryProducts

/-- The canonical split row of a binary biproduct is pointwise short exact. -/
private theorem split_shortExact (A B : PModule.{0,0,0} ℚ (Fin 2)) :
    IsPointwiseShortExact (biprod.inl : A ⟶ A ⊞ B) (biprod.snd : A ⊞ B ⟶ B) := by
  have h : ∀ p : Fin 2,
      ((ShortComplex.mk (biprod.inl : A ⟶ A ⊞ B) (biprod.snd : A ⊞ B ⟶ B) (by simp)).map
        ((evaluation (Fin 2) (ModuleCat.{0} ℚ)).obj p)).ShortExact := fun p =>
    ((ShortComplex.Splitting.ofHasBinaryBiproduct A B).map
      ((evaluation (Fin 2) (ModuleCat.{0} ℚ)).obj p)).shortExact
  exact ⟨fun p => (h p).moduleCat_injective_f, fun p => (h p).moduleCat_surjective_g,
    fun p => (h p).exact.moduleCat_range_eq_ker⟩

/-- A pointwise short exact middle fiber is finite dimensional when the outer
fibers are. -/
private theorem middle_finiteDimensional {A B C : PModule.{0,0,0} ℚ (Fin 2)}
    {ι : A ⟶ B} {π : B ⟶ C} (hs : IsPointwiseShortExact ι π)
    [∀ p, FiniteDimensional ℚ (A.obj p)] [∀ p, FiniteDimensional ℚ (C.obj p)]
    (p : Fin 2) : FiniteDimensional ℚ (B.obj p) :=
  Module.Finite.of_exact (f := (ι.app p).hom) (g := (π.app p).hom)
    (LinearMap.exact_iff.mpr (hs.range_eq_ker p).symm) (hs.surjective p)

/-- The principal upset born at `0`. -/
private noncomputable abbrev upset : PModule.{0,0,0} ℚ (Fin 2) :=
  HookInfinity.module (R := ℚ) (0 : Fin 2)

/-- The finite-death hook on `0 < 1`. -/
private noncomputable abbrev dying : PModule.{0,0,0} ℚ (Fin 2) :=
  Hook.module (k := ℚ) (0 : Fin 2) 1

private instance upset_finiteDimensional (p : Fin 2) :
    FiniteDimensional ℚ (upset.obj p) := by
  change FiniteDimensional ℚ
    (GradedFree.fiber (R := ℚ) (HookInfinity.generators (0 : Fin 2)) p)
  infer_instance

private instance dying_finiteDimensional (p : Fin 2) :
    FiniteDimensional ℚ (dying.obj p) := by
  change FiniteDimensional ℚ
    (SupportInterval.fiber (k := ℚ) (Hook.support (0 : Fin 2) 1) p)
  infer_instance

private noncomputable def dyingVector : dying.obj 0 :=
  SupportInterval.one (Hook.support (0 : Fin 2) 1) (Hook.birth_mem (by decide))

private theorem dyingVector_ne_zero : dyingVector ≠ 0 :=
  fun h => (one_ne_zero : (1 : ℚ) ≠ 0) (congrArg Subtype.val h)

private theorem dyingVector_dies :
    structureMapLinear dying (show (0 : Fin 2) ≤ 1 by decide) dyingVector = 0 :=
  Hook.generator_dies (by decide : (0 : Fin 2) < 1) (𝟙 dying)

/-- The split row with nonzero outer terms is rank exact. -/
private theorem splitRow :
    IsRankExact (biprod.inl : upset ⟶ upset ⊞ dying) (biprod.snd : upset ⊞ dying ⟶ dying) := by
  have hs := split_shortExact upset dying
  let : ∀ p, FiniteDimensional ℚ ((upset ⊞ dying).obj p) := middle_finiteDimensional hs
  exact hs.rankExact_of_section biprod.inr (by simp)

/-- The truncation of the principal upset onto the finite-death hook. -/
private noncomputable def truncation : upset ⟶ dying :=
  HookInfinity.fromBirth 0 dying dyingVector

/-- The rank-exact pushout law on a split row with a nonzero left term, pushed
out along the nonzero truncation map. The pushed row is rank exact; its middle
fiber at `0` contains a nonzero vector from the new left term, and a vector
that dies at `1` while its quotient image is nonzero. -/
theorem truncation_pushout_rankExact_dying :
    (∃ l : upset.obj 0, l ≠ 0) ∧ truncation ≠ 0 ∧
    IsRankExact (Limits.pushout.inr (biprod.inl : upset ⟶ upset ⊞ dying) truncation)
      (splitRow.toIsPointwiseShortExact.pushoutQuotient truncation) ∧
    (∃ y : (Limits.pushout (biprod.inl : upset ⟶ upset ⊞ dying) truncation).obj 0,
      y ≠ 0 ∧
        ((splitRow.toIsPointwiseShortExact.pushoutQuotient truncation).app 0).hom y = 0) ∧
    ∃ x : (Limits.pushout (biprod.inl : upset ⟶ upset ⊞ dying) truncation).obj 0,
      ((splitRow.toIsPointwiseShortExact.pushoutQuotient truncation).app 0).hom x ≠ 0 ∧
        structureMapLinear (Limits.pushout (biprod.inl : upset ⟶ upset ⊞ dying) truncation)
          (show (0 : Fin 2) ≤ 1 by decide) x = 0 := by
  have hrow := splitRow.pushout truncation
  refine ⟨⟨HookInfinity.birth (R := ℚ) (0 : Fin 2), HookInfinity.birth_ne_zero _⟩, ?_, hrow,
    ?_, ?_⟩
  · intro h
    have he : ((truncation.app 0).hom (HookInfinity.birth (R := ℚ) (0 : Fin 2))) =
        dyingVector := HookInfinity.fromBirth_birth _ _ _
    rw [h] at he
    exact dyingVector_ne_zero (by simpa using he.symm)
  · refine ⟨((Limits.pushout.inr (biprod.inl : upset ⟶ upset ⊞ dying) truncation).app 0).hom
      dyingVector, ?_, ?_⟩
    · intro hy
      have hy' : ((Limits.pushout.inr (biprod.inl : upset ⟶ upset ⊞ dying) truncation).app 0).hom
          dyingVector =
          ((Limits.pushout.inr (biprod.inl : upset ⟶ upset ⊞ dying) truncation).app 0).hom 0 := by
        rw [map_zero]
        exact hy
      exact dyingVector_ne_zero (hrow.toIsPointwiseShortExact.injective 0 hy')
    · exact congrArg (fun g : dying ⟶ dying => (g.app 0).hom dyingVector)
        (splitRow.toIsPointwiseShortExact.pushoutQuotient_inr truncation)
  · obtain ⟨x, hx, hdie⟩ := hrow.lift_kernel (show (0 : Fin 2) ≤ 1 by decide)
      dyingVector dyingVector_dies
    exact ⟨x, by rw [hx]; exact dyingVector_ne_zero, hdie⟩

end TDA.Persistence.RankExactPushoutExamples
