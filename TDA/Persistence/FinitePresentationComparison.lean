import TDA.Persistence.FinitePresentationLifting
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# Comparing presentations

A morphism between presented modules lifts to a map on their free generators.
Exactness of the target cokernel then lifts the images of the source relations
to a map on free relations. Neither free family needs to be finite.

This is the two-term presentation form of the free-cover lift in Lesnick,
*The Theory of the Interleaving Distance on Multidimensional Persistence Modules*,
§4.1.4. Here the index is an arbitrary preorder and coefficients form a ring.
-/

set_option autoImplicit false

universe u v w

namespace TDA.Persistence.GradedFree

open CategoryTheory CategoryTheory.Limits

variable {R : Type u} [Ring R] {P : Type v} [Preorder P]

variable (E : Presentation.{u,v,w} (R := R) (P := P))

/-- Evaluation identifies the presented fiber with the quotient by the image
of the relation map at that grade. -/
noncomputable def Presentation.fiberIsoRangeQuotient (a : P) :
    E.presented.obj a ≅ ModuleCat.of R
      ((module (R := R) E.generators).obj a ⧸
        LinearMap.range (E.relationMap.app a).hom) :=
  PreservesCokernel.iso ((evaluation P (ModuleCat.{max u w} R)).obj a)
    E.relationMap ≪≫ ModuleCat.cokernelIsoRangeQuotient (E.relationMap.app a)

/-- Under the fiber quotient identification, the free cover is the quotient map. -/
theorem Presentation.cover_fiberIsoRangeQuotient (a : P) :
    E.cover.app a ≫ (E.fiberIsoRangeQuotient a).hom =
      ModuleCat.ofHom (LinearMap.range (E.relationMap.app a).hom).mkQ := by
  change (cokernel.π E.relationMap).app a ≫
    ((PreservesCokernel.iso ((evaluation P (ModuleCat.{max u w} R)).obj a)
      E.relationMap).hom ≫
      (ModuleCat.cokernelIsoRangeQuotient (E.relationMap.app a)).hom) = _
  have hp := PreservesCokernel.π_iso_hom
    ((evaluation P (ModuleCat.{max u w} R)).obj a) E.relationMap
  change (cokernel.π E.relationMap).app a ≫
    (PreservesCokernel.iso ((evaluation P (ModuleCat.{max u w} R)).obj a)
      E.relationMap).hom = cokernel.π (E.relationMap.app a) at hp
  rw [← Category.assoc, hp, ModuleCat.cokernel_π_cokernelIsoRangeQuotient_hom]

/-- The kernel of the canonical cover at each grade is exactly the image of
the relation map at that grade. -/
theorem Presentation.cover_eq_zero_iff_mem_relation_range (a : P)
    (y : (module (R := R) E.generators).obj a) :
    (E.cover.app a).hom y = 0 ↔
      y ∈ LinearMap.range (E.relationMap.app a).hom := by
  have he := congrArg (fun g : (module (R := R) E.generators).obj a ⟶
    ModuleCat.of R ((module (R := R) E.generators).obj a ⧸
      LinearMap.range (E.relationMap.app a).hom) => g.hom y)
    (E.cover_fiberIsoRangeQuotient a)
  change (E.fiberIsoRangeQuotient a).hom.hom ((E.cover.app a).hom y) =
    (LinearMap.range (E.relationMap.app a).hom).mkQ y at he
  rw [← Submodule.Quotient.mk_eq_zero]
  change _ ↔ (LinearMap.range (E.relationMap.app a).hom).mkQ y = 0
  rw [← he]
  exact ((E.fiberIsoRangeQuotient a).toLinearEquiv.map_eq_zero_iff).symm

/-- Every morphism of presented modules is induced by a commuting pair of
maps on their graded free generators and relations. -/
theorem Presentation.exists_chainMap_lift
    (D : Presentation.{u,v,w} (R := R) (P := P))
    (f : D.presented ⟶ E.presented) :
    ∃ (α : module (R := R) D.generators ⟶ module E.generators)
      (β : module (R := R) D.relations ⟶ module E.relations),
      α ≫ E.cover = D.cover ≫ f ∧
        D.relationMap ≫ α = β ≫ E.relationMap := by
  classical
  obtain ⟨α, hα⟩ := E.exists_lift D.generators (D.cover ≫ f)
  have hrelzero : D.relationMap ≫ (α ≫ E.cover) = 0 := by
    rw [hα, ← Category.assoc, D.relations_vanish, zero_comp]
  have hrange (y : D.relations.Carrier) :
      (D.relationMap ≫ α).app (D.relations.grade y)
        (birth (R := R) D.relations y) ∈
        LinearMap.range (E.relationMap.app (D.relations.grade y)).hom := by
    apply (E.cover_eq_zero_iff_mem_relation_range _ _).mp
    have hz := congrArg (fun q => q.app (D.relations.grade y)
      (birth (R := R) D.relations y)) hrelzero
    simpa [Category.assoc] using hz
  let s : ∀ y : D.relations.Carrier,
      (module (R := R) E.relations).obj (D.relations.grade y) :=
    fun y => Classical.choose (hrange y)
  have hs (y : D.relations.Carrier) :
      (E.relationMap.app (D.relations.grade y)).hom (s y) =
        (D.relationMap ≫ α).app (D.relations.grade y)
          (birth (R := R) D.relations y) :=
    Classical.choose_spec (hrange y)
  let β := lift (R := R) D.relations (module E.relations) s
  refine ⟨α, β, hα, ?_⟩
  symm
  apply TDA.Persistence.GradedFree.hom_ext_birth D.relations
  intro y
  change (E.relationMap.app (D.relations.grade y)).hom
      ((β.app (D.relations.grade y)).hom (birth D.relations y)) = _
  rw [lift_birth]
  exact hs y

end TDA.Persistence.GradedFree
