import TDA.Persistence.FinitePresentationColimits
import TDA.Persistence.FinitePresentationFiniteDimensional
import TDA.Persistence.RankExactPushout
import Mathlib.CategoryTheory.Abelian.Basic

/-!
# Finite presentations of categorical pushouts

In the category of persistence modules, a pushout is the cokernel of the map
from the common source into the binary biproduct induced by the two input maps
with opposite signs.
This comparison transfers the explicit cokernel and biproduct presentations
to the actual categorical pushout.
-/

set_option autoImplicit false

universe u v w

namespace TDA.Persistence.GradedFree

open CategoryTheory CategoryTheory.Limits

variable {R : Type u} [Ring R] {P : Type v} [Preorder P]

private instance : HasBinaryBiproducts (PModule.{u,v,max u w} R P) :=
  HasBinaryBiproducts.of_hasBinaryProducts

/-- The cokernel of the biproduct map `(f,-g)` is the actual categorical
pushout of `f` and `g`. -/
noncomputable def pushoutCokernelComparison
    {X Y Z : PModule.{u,v,max u w} R P} (f : X ⟶ Y) (g : X ⟶ Z) :
    Limits.cokernel (biprod.lift f (-g)) ≅ Limits.pushout f g := by
  exact (cokernelIsCokernel (biprod.lift f (-g))).coconePointUniqueUpToIso
    (CategoryTheory.Abelian.BiproductToPushoutIsCokernel.isColimitBiproductToPushout f g)

@[reassoc (attr := simp)]
theorem pushoutCokernelComparison_π
    {X Y Z : PModule.{u,v,max u w} R P} (f : X ⟶ Y) (g : X ⟶ Z) :
    Limits.cokernel.π (biprod.lift f (-g)) ≫ (pushoutCokernelComparison f g).hom =
      biprod.desc (Limits.pushout.inl f g) (Limits.pushout.inr f g) := by
  let hc := cokernelIsCokernel (biprod.lift f (-g))
  let hp := CategoryTheory.Abelian.BiproductToPushoutIsCokernel.isColimitBiproductToPushout f g
  simpa [pushoutCokernelComparison, hc, hp,
    CategoryTheory.Abelian.BiproductToPushoutIsCokernel.biproductToPushout] using
      (IsColimit.comp_coconePointUniqueUpToIso_hom hc hp WalkingParallelPair.one)

@[reassoc (attr := simp)]
theorem pushoutCokernelComparison_inl
    {X Y Z : PModule.{u,v,max u w} R P} (f : X ⟶ Y) (g : X ⟶ Z) :
    biprod.inl ≫ Limits.cokernel.π (biprod.lift f (-g)) ≫
        (pushoutCokernelComparison f g).hom = Limits.pushout.inl f g := by
  simp

@[reassoc (attr := simp)]
theorem pushoutCokernelComparison_inr
    {X Y Z : PModule.{u,v,max u w} R P} (f : X ⟶ Y) (g : X ⟶ Z) :
    biprod.inr ≫ Limits.cokernel.π (biprod.lift f (-g)) ≫
        (pushoutCokernelComparison f g).hom = Limits.pushout.inr f g := by
  simp

/-- Finite presentation is closed under the actual categorical pushout of two
maps between finitely presented persistence modules. -/
theorem finitelyPresented_pushout
    {X Y Z : PModule.{u,v,max u w} R P} (f : X ⟶ Y) (g : X ⟶ Z)
    (hX : FinitelyPresented.{u,v,w} (R := R) (P := P) X)
    (hY : FinitelyPresented.{u,v,w} (R := R) (P := P) Y)
    (hZ : FinitelyPresented.{u,v,w} (R := R) (P := P) Z) :
    FinitelyPresented.{u,v,w} (R := R) (P := P) (Limits.pushout f g) := by
  have hYZ : FinitelyPresented.{u,v,w} (R := R) (P := P) (Y ⊞ Z) :=
    finitelyPresented_biprod hY hZ
  have hCoker : FinitelyPresented.{u,v,w} (R := R) (P := P)
      (Limits.cokernel (biprod.lift f (-g))) :=
    finitelyPresented_cokernel (biprod.lift f (-g)) hX hYZ
  exact finitelyPresented_of_iso hCoker (pushoutCokernelComparison f g)

end TDA.Persistence.GradedFree

namespace TDA.Persistence

open CategoryTheory CategoryTheory.Limits
open GradedFree

variable {k : Type u} [Field k] {P : Type} [PartialOrder P]
variable {L M N L' : PModule.{u,0,u} k P}
variable {ι : L ⟶ M} {π : M ⟶ N}

/-- An actual rank-exact pushout row has finitely presented middle object when
its original left and middle objects and its new left object are finitely
presented. Pointwise finite-dimensionality of the new left object is derived
from finite presentation before applying the existing rank-exact pushout law.
-/
theorem IsRankExact.pushout_finitelyPresented
    (hs : IsRankExact ι π) (f : L ⟶ L')
    (hL : FinitelyPresented.{u,0,0} (R := k) (P := P) L)
    (hM : FinitelyPresented.{u,0,0} (R := k) (P := P) M)
    (hL' : FinitelyPresented.{u,0,0} (R := k) (P := P) L') :
    FinitelyPresented.{u,0,0} (R := k) (P := P) (Limits.pushout ι f) ∧
      IsRankExact (Limits.pushout.inr ι f)
        (hs.toIsPointwiseShortExact.pushoutQuotient f) := by
  letI : ∀ p : P, FiniteDimensional k (L'.obj p) :=
    fun p => GradedFree.finitelyPresented_finiteDimensional L' hL' p
  exact ⟨GradedFree.finitelyPresented_pushout ι f hL hM hL', hs.pushout f⟩

end TDA.Persistence
