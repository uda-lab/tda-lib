import TDA.Persistence.FiniteRankProjectiveClassification

/-!
# Boundary cases for the finite rank-projective hook classification

The classification applies to a nonzero finite-death hook and also to the zero
module, whose canonical occurrence family is empty.
-/

universe u

namespace TDA.Persistence.FiniteRankProjectiveClassification.Examples

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

variable {k : Type u} [Field k] {P : Type} [PartialOrder P] [Fintype P]

private instance : HasFiniteBiproducts (PModule.{u,0,u} k P) :=
  HasFiniteBiproducts.of_hasFiniteProducts

private instance zero_subsingleton (p : P) :
    Subsingleton ((0 : PModule.{u,0,u} k P).obj p) :=
  ModuleCat.subsingleton_of_isZero (Functor.zero_obj p)

private instance zero_finiteDimensional (p : P) :
    FiniteDimensional k ((0 : PModule.{u,0,u} k P).obj p) := by
  infer_instance

/-- A nonzero finite-death hook is classified by a selected subfamily of its
canonical finite-hook cover. -/
theorem nonzero_finite_hook_has_canonical_classification (i d : P) (hid : i < d) :
    ∃ S : Finset (FiniteHookDeflation.Index (Hook.module (k := k) i d)),
      Nonempty (Hook.module (k := k) i d ≅
        ⨁ fun t : S => FiniteHookDeflation.family (Hook.module (k := k) i d) t.1) := by
  apply (rankProjective_iff_exists_canonical_subfamily
    (M := Hook.module (k := k) i d) (fun _ => inferInstance)).mp
  exact Hook.isRankProjective hid

/-- The zero module has a classification with an empty canonical occurrence
selection. -/
theorem zero_has_empty_canonical_classification :
    ∃ S : Finset (FiniteHookDeflation.Index (0 : PModule.{u,0,u} k P)),
      S = ∅ ∧ Nonempty ((0 : PModule.{u,0,u} k P) ≅
        ⨁ fun t : S => FiniteHookDeflation.family (0 : PModule.{u,0,u} k P) t.1) := by
  let M : PModule.{u,0,u} k P := 0
  letI (p : P) : Subsingleton (M.obj p) :=
    ModuleCat.subsingleton_of_isZero (Functor.zero_obj p)
  letI (ab : FiniteHookDeflation.StrictPair P) :
      Subsingleton (LinearMap.ker (structureMapLinear M ab.property.le)) := by
    infer_instance
  have hcard : Fintype.card (FiniteHookDeflation.Index M) = 0 := by
    rw [FiniteHookDeflation.card_index]
    simp [FiniteHookDeflation.Index, M, Module.finrank_zero_of_subsingleton]
  have hindex : IsEmpty (FiniteHookDeflation.Index M) :=
    Fintype.card_eq_zero_iff.mp hcard
  have hRP : IsRankProjective M := by
    intro L A B ι π h α
    exact ⟨0, (isZero_zero _).eq_of_src _ _⟩
  have hfd : ∀ p, FiniteDimensional k (M.obj p) := by
    intro p
    infer_instance
  obtain ⟨S, e⟩ :=
    (rankProjective_iff_exists_canonical_subfamily M hfd).mp hRP
  have hS : S = ∅ := by
    ext t
    exact isEmptyElim (hindex.false t)
  exact ⟨S, hS, e⟩

end TDA.Persistence.FiniteRankProjectiveClassification.Examples
