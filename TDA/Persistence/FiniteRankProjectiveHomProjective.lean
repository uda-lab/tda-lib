import TDA.Persistence.FiniteRankProjectiveEndAlgebra
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.CategoryTheory.Preadditive.Opposite
import Mathlib.Algebra.Module.Equiv.Opposite

/-!
# Hook summands give projective modules over the hook endomorphism algebra

For the finite direct sum of rank-projective hooks, precomposition equips
`Hom(HookSum, -)` with a left module structure over the opposite endomorphism
algebra. Each hook summand yields a projective module by an explicit split
embedding into the regular module.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence.FiniteRankProjectiveHomProjective

open CategoryTheory CategoryTheory.Limits
open TDA.Persistence.FiniteRankProjectiveEndAlgebra

variable {k : Type u} [Field k] {S : Type} [Lattice S] [Finite S]

noncomputable section

local instance : Fintype S := Fintype.ofFinite S
local instance : Fintype (HookTag (S := S)) := Fintype.ofFinite _

private instance : HasFiniteBiproducts (PModule.{u,0,u} k S) :=
  HasFiniteBiproducts.of_hasFiniteProducts

private abbrev EndRing := End (HookSum (k := k) (S := S))
/-- The opposite endomorphism algebra acting on maps from the finite hook
generator. This is the same scalar type used by the Hom functor. -/
abbrev HomScalars := (EndRing (k := k) (S := S))ᵐᵒᵖ

/-- Postcomposition with the hook inclusion embeds maps from the hook generator
into its endomorphism ring. -/
private def hookHomToEnd (t : HookTag (S := S)) :
    (HookSum (k := k) (S := S) ⟶ hookFamily (k := k) (S := S) t) →ₗ[HomScalars (k := k) (S := S)]
      (EndRing (k := k) (S := S)) where
  toFun f := f ≫ biproduct.ι (hookFamily (k := k) (S := S)) t
  map_add' f g := by
    exact Preadditive.add_comp _ _ _ f g
      (biproduct.ι (hookFamily (k := k) (S := S)) t)
  map_smul' r f := by
    change (r.unop ≫ f) ≫ biproduct.ι (hookFamily (k := k) (S := S)) t =
      r.unop ≫ (f ≫ biproduct.ι (hookFamily (k := k) (S := S)) t)
    exact Category.assoc _ _ _

/-- Projection from the endomorphism ring back to maps into a hook summand. -/
private def endToHookHom (t : HookTag (S := S)) :
    (EndRing (k := k) (S := S)) →ₗ[HomScalars (k := k) (S := S)]
      (HookSum (k := k) (S := S) ⟶ hookFamily (k := k) (S := S) t) where
  toFun f := f ≫ biproduct.π (hookFamily (k := k) (S := S)) t
  map_add' f g := by
    exact Preadditive.add_comp _ _ _ f g
      (biproduct.π (hookFamily (k := k) (S := S)) t)
  map_smul' r f := by
    change (r.unop ≫ f) ≫ biproduct.π (hookFamily (k := k) (S := S)) t =
      r.unop ≫ (f ≫ biproduct.π (hookFamily (k := k) (S := S)) t)
    exact Category.assoc _ _ _

/-- A map from the hook generator into any one hook is a split summand of its
regular endomorphism module. -/
private theorem hookHom_split (t : HookTag (S := S)) :
    (endToHookHom (k := k) (S := S) t).comp
      (hookHomToEnd (k := k) (S := S) t) = LinearMap.id := by
  apply LinearMap.ext
  intro f
  simp [hookHomToEnd, endToHookHom, Category.assoc]

/-- The regular endomorphism module is free over the opposite endomorphism
algebra. -/
private theorem endRing_projective :
    Module.Projective (HomScalars (k := k) (S := S))
      (EndRing (k := k) (S := S)) := by
  let e : (EndRing (k := k) (S := S)) ≃ₗ[HomScalars (k := k) (S := S)]
      HomScalars (k := k) (S := S) :=
    MulOpposite.opLinearEquiv (R := HomScalars (k := k) (S := S))
      (M := EndRing (k := k) (S := S))
  exact Module.Projective.of_equiv' e.symm

/-- The Hom module from the finite hook generator into any one of its hook
summands is projective over the opposite endomorphism algebra. The field `k`
is arbitrary. -/
theorem hookHom_isProjective (t : HookTag (S := S)) :
    Module.Projective (HomScalars (k := k) (S := S))
      (HookSum (k := k) (S := S) ⟶ hookFamily (k := k) (S := S) t) := by
  letI : Module.Projective (HomScalars (k := k) (S := S))
      (EndRing (k := k) (S := S)) := endRing_projective (k := k) (S := S)
  exact Module.Projective.of_split
    (hookHomToEnd (k := k) (S := S) t)
    (endToHookHom (k := k) (S := S) t)
    (hookHom_split (k := k) (S := S) t)


/-- Postcomposition with an isomorphism transports the hook-generator Hom
module linearly over the opposite endomorphism algebra. -/
private def homPostcomposeLinearEquiv {M N : PModule.{u,0,u} k S}
    (e : M ≅ N) :
    (HookSum (k := k) (S := S) ⟶ M) ≃ₗ[HomScalars (k := k) (S := S)]
      (HookSum (k := k) (S := S) ⟶ N) where
  toFun f := f ≫ e.hom
  invFun f := f ≫ e.inv
  left_inv f := by simp [Category.assoc]
  right_inv f := by simp [Category.assoc]
  map_add' f g := Preadditive.add_comp _ _ _ f g e.hom
  map_smul' r f := by
    change (r.unop ≫ f) ≫ e.hom = r.unop ≫ (f ≫ e.hom)
    exact Category.assoc _ _ _

/-- Maps from the hook generator into a finite biproduct are the finite product
of the corresponding Hom modules, compatibly with precomposition. -/
def homBiproductEquivPi {I : Type} [Fintype I]
    (F : I → PModule.{u,0,u} k S) :
    (HookSum (k := k) (S := S) ⟶ ⨁ F) ≃ₗ[HomScalars (k := k) (S := S)]
      (∀ i, HookSum (k := k) (S := S) ⟶ F i) where
  toFun f i := f ≫ biproduct.π F i
  invFun f := biproduct.lift f
  left_inv f := by
    apply biproduct.hom_ext _ _
    intro i
    simp
  right_inv f := by
    funext i
    simp [biproduct.lift_π]
  map_add' f g := by
    funext i
    exact Preadditive.add_comp _ _ _ f g (biproduct.π F i)
  map_smul' r f := by
    funext i
    change (r.unop ≫ f) ≫ biproduct.π F i =
      r.unop ≫ (f ≫ biproduct.π F i)
    exact Category.assoc _ _ _

/-- The finite-biproduct comparison reads each coordinate by composing with the
corresponding categorical projection. -/
@[simp] theorem homBiproductEquivPi_apply {I : Type} [Fintype I]
    (F : I → PModule.{u,0,u} k S) (f : HookSum (k := k) (S := S) ⟶ ⨁ F) (i : I) :
    homBiproductEquivPi (k := k) (S := S) F f i = f ≫ biproduct.π F i := rfl

private def indexTag {M : PModule.{u,0,u} k S} :
    FiniteHookDeflation.Index M → HookTag (S := S)
  | .inl t => .inl t.1
  | .inr t => .inr t.1

private theorem family_eq_hookFamily {M : PModule.{u,0,u} k S}
    (i : FiniteHookDeflation.Index M) :
    FiniteHookDeflation.family M i =
      hookFamily (k := k) (S := S) (indexTag (S := S) i) := by
  cases i <;> rfl

/-- For any pointwise finite-dimensional rank-projective over a finite lattice,
precomposition from the finite hook generator produces a projective module over
its opposite endomorphism algebra. The field `k` is arbitrary. -/
theorem hom_from_hookSum_isProjective (M : PModule.{u,0,u} k S)
    (hfd : ∀ p, FiniteDimensional k (M.obj p)) (hRP : IsRankProjective M) :
    Module.Projective (HomScalars (k := k) (S := S))
      (HookSum (k := k) (S := S) ⟶ M) := by
  classical
  obtain ⟨I, hI⟩ :=
    (FiniteRankProjectiveClassification.rankProjective_iff_exists_canonical_subfamily
      M hfd).mp hRP
  let F : I → PModule.{u,0,u} k S := fun i => FiniteHookDeflation.family M i.1
  let e : M ≅ ⨁ F := Classical.choice hI
  have hSummand (i : I) : Module.Projective (HomScalars (k := k) (S := S))
      (HookSum (k := k) (S := S) ⟶ F i) := by
    let tag := indexTag (S := S) i.1
    letI : Module.Projective (HomScalars (k := k) (S := S))
        (HookSum (k := k) (S := S) ⟶ hookFamily (k := k) (S := S) tag) :=
      hookHom_isProjective (k := k) (S := S) tag
    let eHook : F i ≅ hookFamily (k := k) (S := S) tag :=
      eqToIso (family_eq_hookFamily (M := M) i.1)
    exact Module.Projective.of_equiv'
      (homPostcomposeLinearEquiv (k := k) (S := S) eHook).symm
  have hPi : Module.Projective (HomScalars (k := k) (S := S))
      (∀ i, HookSum (k := k) (S := S) ⟶ F i) := by
    letI : ∀ i, Module.Projective (HomScalars (k := k) (S := S))
        (HookSum (k := k) (S := S) ⟶ F i) := hSummand
    exact Module.Projective.of_equiv'
      (DirectSum.linearEquivFunOnFintype (HomScalars (k := k) (S := S)) I
        (fun i => HookSum (k := k) (S := S) ⟶ F i))
  have hBiproduct : Module.Projective (HomScalars (k := k) (S := S))
      (HookSum (k := k) (S := S) ⟶ ⨁ F) :=
    Module.Projective.of_equiv'
      (homBiproductEquivPi (k := k) (S := S) F).symm
  exact Module.Projective.of_equiv'
    (homPostcomposeLinearEquiv (k := k) (S := S) e).symm

end

end TDA.Persistence.FiniteRankProjectiveHomProjective
