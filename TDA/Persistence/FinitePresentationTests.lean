import TDA.Persistence.FinitePresentationLifting
import Mathlib.Data.Set.Finite.Basic

/-!
# Finite tests for morphisms from finitely presented modules

A finite presentation supplies finitely many grades at which a natural map
must be bijective to induce a bijection on maps from the presented module.
The test set consists of the generator and relation grades. The result applies
to the module itself through its presentation isomorphism.
-/

set_option autoImplicit false

universe u v w

namespace TDA.Persistence.GradedFree

open CategoryTheory

variable {R : Type u} [Ring R] {P : Type v} [Preorder P]

/-- Maps from a finitely presented module are controlled by bijectivity at a
finite set of parameter grades. -/
theorem finitelyPresented_exists_finite_postcomp_tests
    (M : PModule.{u,v,max u w} R P)
    (hM : FinitelyPresented (R := R) (P := P) M) :
    ∃ S : Set P, S.Finite ∧
      ∀ {X Y : PModule.{u,v,max u w} R P} (ρ : X ⟶ Y),
        (∀ a ∈ S, Function.Bijective (ρ.app a)) →
          Function.Bijective (fun f : M ⟶ X => f ≫ ρ) := by
  obtain ⟨D, hD, ⟨e⟩⟩ := hM
  let : Finite D.generators.Carrier := hD.1
  let : Finite D.relations.Carrier := hD.2
  let S : Set P := Set.range D.generators.grade ∪ Set.range D.relations.grade
  refine ⟨S, (Set.finite_range _).union (Set.finite_range _), ?_⟩
  intro X Y ρ hρ
  have hG : ∀ g, Function.Bijective (ρ.app (D.generators.grade g)) :=
    fun g => hρ _ (Or.inl ⟨g, rfl⟩)
  have hY : ∀ y, Function.Injective (ρ.app (D.relations.grade y)) :=
    fun y => (hρ _ (Or.inr ⟨y, rfl⟩)).1
  have hDρ := D.postcomp_bijective_of_birth_bijective_relation_injective ρ hG hY
  constructor
  · intro f g h
    apply (cancel_epi e.hom).mp
    apply hDρ.1
    simpa only [Category.assoc] using congrArg (fun q => e.hom ≫ q) h
  · intro f
    obtain ⟨l, hl⟩ := hDρ.2 (e.hom ≫ f)
    refine ⟨e.inv ≫ l, ?_⟩
    change (e.inv ≫ l) ≫ ρ = f
    change l ≫ ρ = e.hom ≫ f at hl
    rw [Category.assoc, hl, ← Category.assoc, e.inv_hom_id, Category.id_comp]

end TDA.Persistence.GradedFree
