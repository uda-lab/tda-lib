import TDA.Persistence.FinitePresentation

/-!
# Lifting maps from a presented module

A map from a presented module lifts through a natural transformation if its
components are surjective at generator grades and injective at relation grades.
Only the declared grades are tested. This allows transition isomorphisms on a
finite critical grid to remove a small shift from a morphism.
-/

set_option autoImplicit false

universe u v w

namespace TDA.Persistence.GradedFree

open CategoryTheory CategoryTheory.Limits

variable {R : Type u} [Ring R] {P : Type v} [Preorder P]

/-- Natural maps out of a free module agree if they agree on its birth vectors. -/
theorem hom_ext_birth (W : GradedGenerators.{v,w} P)
    {M : PModule.{u,v,max u w} R P} {f g : module (R := R) W ⟶ M}
    (h : ∀ i, f.app (W.grade i) (birth (R := R) W i) =
      g.app (W.grade i) (birth (R := R) W i)) : f = g := by
  exact (lift_unique (R := R) W M _ f h).trans
    (lift_unique (R := R) W M _ g (fun _ => rfl)).symm

/-- Maps from a presented module agree if they agree on its generator images. -/
theorem Presentation.hom_ext_birth
    (D : Presentation.{u,v,w} (R := R) (P := P))
    {M : PModule.{u,v,max u w} R P} {f g : D.presented ⟶ M}
    (h : ∀ i, (D.cover ≫ f).app (D.generators.grade i) (birth D.generators i) =
      (D.cover ≫ g).app (D.generators.grade i) (birth D.generators i)) : f = g := by
  have : Epi D.cover := by
    change Epi (cokernel.π D.relationMap)
    infer_instance
  exact (cancel_epi D.cover).mp (TDA.Persistence.GradedFree.hom_ext_birth D.generators h)

/-- Injectivity on generator grades suffices for injectivity on maps from a
presented module. -/
theorem Presentation.postcomp_injective_of_birth_injective
    (D : Presentation.{u,v,w} (R := R) (P := P))
    {M N : PModule.{u,v,max u w} R P} (ρ : M ⟶ N)
    (hG : ∀ g : D.generators.Carrier,
      Function.Injective (ρ.app (D.generators.grade g))) :
    Function.Injective (fun f : D.presented ⟶ M => f ≫ ρ) := by
  intro f g h
  apply D.hom_ext_birth
  intro i
  apply hG i
  exact congrArg (fun q => q.app (D.generators.grade i)
    (D.cover.app (D.generators.grade i) (birth D.generators i))) h

/-- A presentation only requires surjectivity at generator grades and
injectivity at relation grades to lift a morphism through a natural map. -/
theorem Presentation.exists_lift_of_birth_surjective_relation_injective
    (D : Presentation.{u,v,w} (R := R) (P := P))
    {M N : PModule.{u,v,max u w} R P} (ρ : M ⟶ N)
    (hG : ∀ g : D.generators.Carrier,
      Function.Surjective (ρ.app (D.generators.grade g)))
    (hY : ∀ y : D.relations.Carrier,
      Function.Injective (ρ.app (D.relations.grade y)))
    (f : D.presented ⟶ N) : ∃ l : D.presented ⟶ M, l ≫ ρ = f := by
  classical
  let s : ∀ g : D.generators.Carrier, M.obj (D.generators.grade g) :=
    fun g => Classical.choose
      (hG g ((D.cover ≫ f).app (D.generators.grade g) (birth D.generators g)))
  let lG := lift (R := R) D.generators M s
  have hl : lG ≫ ρ = D.cover ≫ f := by
    apply TDA.Persistence.GradedFree.hom_ext_birth D.generators
    intro g
    change ρ.app (D.generators.grade g)
      ((lift (R := R) D.generators M s).app (D.generators.grade g)
        (birth D.generators g)) = _
    rw [lift_birth]
    exact Classical.choose_spec
      (hG g ((D.cover ≫ f).app (D.generators.grade g) (birth D.generators g)))
  have hrel : D.relationMap ≫ lG = 0 := by
    apply TDA.Persistence.GradedFree.hom_ext_birth D.relations
    intro y
    apply hY y
    have hz : D.relationMap ≫ (lG ≫ ρ) = 0 := by
      rw [hl, ← Category.assoc, D.relations_vanish, zero_comp]
    have he := congrArg (fun q => q.app (D.relations.grade y)
      (birth (R := R) D.relations y)) hz
    simpa using he
  refine ⟨D.desc lG hrel, ?_⟩
  have : Epi D.cover := by
    change Epi (cokernel.π D.relationMap)
    infer_instance
  apply (cancel_epi D.cover).mp
  rw [← Category.assoc, D.cover_desc]
  exact hl

/-- A natural map that is bijective on generator grades and injective on
relation grades induces a bijection on maps from the presented module. -/
theorem Presentation.postcomp_bijective_of_birth_bijective_relation_injective
    (D : Presentation.{u,v,w} (R := R) (P := P))
    {M N : PModule.{u,v,max u w} R P} (ρ : M ⟶ N)
    (hG : ∀ g : D.generators.Carrier,
      Function.Bijective (ρ.app (D.generators.grade g)))
    (hY : ∀ y : D.relations.Carrier,
      Function.Injective (ρ.app (D.relations.grade y))) :
    Function.Bijective (fun f : D.presented ⟶ M => f ≫ ρ) :=
  ⟨D.postcomp_injective_of_birth_injective ρ (fun g => (hG g).1),
    D.exists_lift_of_birth_surjective_relation_injective ρ (fun g => (hG g).2) hY⟩

end TDA.Persistence.GradedFree
