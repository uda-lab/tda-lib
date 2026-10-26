import TDA.Persistence.FiniteRankProjectiveHomExact

/-!
# Full faithfulness of the hook-generator Hom functor

The principal-upset summands of the hook sum recover each fiber of a
persistence module from maps out of the hook sum.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence.FiniteRankProjectiveHomFullyFaithful

open CategoryTheory CategoryTheory.Limits
open TDA.Persistence.FiniteRankProjectiveEndAlgebra
open TDA.Persistence.FiniteRankProjectiveHomExact

variable {k : Type u} [Field k] {S : Type} [Lattice S] [Finite S]

noncomputable section

local instance : Fintype S := Fintype.ofFinite S
local instance : Fintype (HookTag (S := S)) := Fintype.ofFinite _

private instance : HasFiniteBiproducts (PModule.{u,0,u} k S) :=
  HasFiniteBiproducts.of_hasFiniteProducts

private abbrev L := HookSum (k := k) (S := S)
private abbrev E := HomScalars (k := k) (S := S)

/-- Projection onto the principal-upset summand at a grade. -/
noncomputable def projection (a : S) :
    L (k := k) (S := S) ⟶ HookInfinity.module (R := k) a :=
  biproduct.π (hookFamily (k := k) (S := S)) (.inr a)

/-- Inclusion of the principal-upset summand at a grade. -/
noncomputable def inclusion (a : S) :
    HookInfinity.module (R := k) a ⟶ L (k := k) (S := S) :=
  biproduct.ι (hookFamily (k := k) (S := S)) (.inr a)

private theorem inclusion_projection (a : S) :
    inclusion (k := k) (S := S) a ≫ projection (k := k) (S := S) a =
      𝟙 (HookInfinity.module (R := k) a) :=
  biproduct.ι_π_self _ _

/-- Encode a birth-fiber vector as a map from the full hook generator. -/
noncomputable def encode (M : PModule.{u,0,u} k S) (a : S) (x : M.obj a) :
    L (k := k) (S := S) ⟶ M :=
  projection (k := k) (S := S) a ≫ HookInfinity.fromBirth a M x

@[simp] theorem encode_birth (M : PModule.{u,0,u} k S) (a : S) (x : M.obj a) :
    (((inclusion (k := k) (S := S) a ≫ encode M a x).app a).hom
      (HookInfinity.birth a)) = x := by
  change (((inclusion (k := k) (S := S) a ≫
      (projection (k := k) (S := S) a ≫ HookInfinity.fromBirth a M x)).app a).hom
      (HookInfinity.birth a)) = x
  rw [← Category.assoc, inclusion_projection, Category.id_comp]
  exact HookInfinity.fromBirth_birth a M x

private theorem encode_add (M : PModule.{u,0,u} k S) (a : S)
    (x y : M.obj a) : encode M a (x + y) = encode M a x + encode M a y := by
  have h : HookInfinity.fromBirth a M (x + y) =
      HookInfinity.fromBirth a M x + HookInfinity.fromBirth a M y := by
    apply HookInfinity.hom_ext
    simp
  simp [encode, h, Preadditive.comp_add]

private theorem encode_smul (M : PModule.{u,0,u} k S) (a : S)
    (r : k) (x : M.obj a) : encode M a (r • x) = r • encode M a x := by
  have h : HookInfinity.fromBirth a M (r • x) =
      r • HookInfinity.fromBirth a M x := by
    apply HookInfinity.hom_ext
    simp
  simp [encode, h, Linear.comp_smul]

private theorem scalar_as_end_action (M : PModule.{u,0,u} k S)
    (r : k) (g : L (k := k) (S := S) ⟶ M) :
    (MulOpposite.op (r • (𝟙 (L (k := k) (S := S)))) : E (k := k) (S := S)) • g =
      r • g := by
  change (r • 𝟙 (L (k := k) (S := S))) ≫ g = r • g
  simp

private theorem map_scalar (M N : PModule.{u,0,u} k S)
    (T : (L (k := k) (S := S) ⟶ M) →ₗ[E (k := k) (S := S)]
      (L (k := k) (S := S) ⟶ N)) (r : k)
    (g : L (k := k) (S := S) ⟶ M) : T (r • g) = r • T g := by
  rw [← scalar_as_end_action M r g, map_smul, scalar_as_end_action N r (T g)]

private def fiberMap (M N : PModule.{u,0,u} k S)
    (T : (L (k := k) (S := S) ⟶ M) →ₗ[E (k := k) (S := S)]
      (L (k := k) (S := S) ⟶ N)) (a : S) : M.obj a →ₗ[k] N.obj a where
  toFun x := (((inclusion (k := k) (S := S) a ≫ T (encode M a x)).app a).hom
    (HookInfinity.birth a))
  map_add' x y := by
    rw [encode_add, map_add]
    simp [Preadditive.comp_add]
  map_smul' r x := by
    rw [encode_smul, map_scalar]
    change (((inclusion (k := k) (S := S) a ≫ (r • T (encode M a x))).app a).hom
      (HookInfinity.birth a)) = r •
        (((inclusion (k := k) (S := S) a ≫ T (encode M a x)).app a).hom
          (HookInfinity.birth a))
    simp [Linear.comp_smul]

private theorem evaluate (M N : PModule.{u,0,u} k S)
    (T : (L (k := k) (S := S) ⟶ M) →ₗ[E (k := k) (S := S)]
      (L (k := k) (S := S) ⟶ N))
    (g : L (k := k) (S := S) ⟶ M) (a : S) (x : (L (k := k) (S := S)).obj a) :
    ((T g).app a).hom x =
      fiberMap M N T a ((g.app a).hom x) := by
  let u : HookInfinity.module (R := k) a ⟶ L (k := k) (S := S) :=
    HookInfinity.fromBirth a (L (k := k) (S := S)) x
  let e : End (L (k := k) (S := S)) :=
    projection (k := k) (S := S) a ≫ u
  have hu : u ≫ g = HookInfinity.fromBirth a M ((g.app a).hom x) := by
    apply HookInfinity.hom_ext
    simp [u]
  have h1 : e ≫ g = encode M a ((g.app a).hom x) := by
    simpa [e, encode, Category.assoc] using
      congrArg (fun v : HookInfinity.module (R := k) a ⟶ M =>
        projection (k := k) (S := S) a ≫ v) hu
  have h2 : T (e ≫ g) = e ≫ T g := by
    exact T.map_smul (MulOpposite.op e) g
  have h3 := congrArg
    (fun f : L (k := k) (S := S) ⟶ N =>
      (((inclusion (k := k) (S := S) a ≫ f).app a).hom
        (HookInfinity.birth a))) (h1 ▸ h2)
  have heval :
      (((inclusion (k := k) (S := S) a ≫ e ≫ T g).app a).hom
        (HookInfinity.birth a)) = ((T g).app a).hom x := by
    have hie : inclusion (k := k) (S := S) a ≫ e = u := by
      change inclusion (k := k) (S := S) a ≫
        (projection (k := k) (S := S) a ≫ u) = u
      rw [← Category.assoc, inclusion_projection, Category.id_comp]
    rw [← Category.assoc, hie]
    simp [u]
  exact heval.symm.trans h3.symm

/-- Recover the unique persistence map represented by an endomorphism-linear
map between hook-generator Hom modules. -/
noncomputable def preimage (M N : PModule.{u,0,u} k S)
    (T : (L (k := k) (S := S) ⟶ M) →ₗ[E (k := k) (S := S)]
      (L (k := k) (S := S) ⟶ N)) : M ⟶ N where
  app a := ModuleCat.ofHom (fiberMap M N T a)
  naturality := by
    intro a b hab
    let hab' : a ≤ b := leOfHom hab
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    let g := encode M a x
    let z : (L (k := k) (S := S)).obj a :=
      ((inclusion (k := k) (S := S) a).app a).hom (HookInfinity.birth a)
    let y := structureMapLinear (L (k := k) (S := S)) hab' z
    have hgz : ((g.app a).hom z) = x := encode_birth M a x
    have hgy : ((g.app b).hom y) = structureMapLinear M hab' x := by
      have h := congrArg (fun f : (L (k := k) (S := S)).obj a ⟶ M.obj b =>
        f.hom z) (g.naturality hab)
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
      change ((g.app b).hom (((L (k := k) (S := S)).map hab).hom z)) =
        (M.map hab).hom x
      rw [← hgz]
      exact h
    have hTz : ((T g).app a).hom z = fiberMap M N T a x := by
      rfl
    have hTy : ((T g).app b).hom y = structureMapLinear N hab' (fiberMap M N T a x) := by
      have h := congrArg (fun f : (L (k := k) (S := S)).obj a ⟶ N.obj b =>
        f.hom z) ((T g).naturality hab)
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
      change (((T g).app b).hom (((L (k := k) (S := S)).map hab).hom z)) =
        (N.map hab).hom (fiberMap M N T a x)
      rw [← hTz]
      exact h
    change fiberMap M N T b (structureMapLinear M hab' x) =
      structureMapLinear N hab' (fiberMap M N T a x)
    rw [← hgy, ← evaluate M N T g b y, hTy]

/-- Birth-fiber formula for the reconstructed persistence morphism. -/
theorem preimage_app (M N : PModule.{u,0,u} k S)
    (T : (L (k := k) (S := S) ⟶ M) →ₗ[E (k := k) (S := S)]
      (L (k := k) (S := S) ⟶ N)) (a : S) (x : M.obj a) :
    ((preimage M N T).app a).hom x =
      (((inclusion (k := k) (S := S) a ≫ T (encode M a x)).app a).hom
        (HookInfinity.birth a)) := rfl

@[simp] theorem postcompose_preimage (M N : PModule.{u,0,u} k S)
    (T : (L (k := k) (S := S) ⟶ M) →ₗ[E (k := k) (S := S)]
      (L (k := k) (S := S) ⟶ N)) :
    postcompose (k := k) (S := S) (preimage M N T) = T := by
  apply LinearMap.ext
  intro g
  apply NatTrans.ext
  funext a
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact (evaluate M N T g a x).symm

@[simp] theorem preimage_postcompose (M N : PModule.{u,0,u} k S)
    (f : M ⟶ N) :
    preimage M N (postcompose (k := k) (S := S) f) = f := by
  apply NatTrans.ext
  funext a
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (f.app a).hom
    (((inclusion (k := k) (S := S) a ≫ encode M a x).app a).hom
      (HookInfinity.birth a)) = (f.app a).hom x
  rw [encode_birth]

/-- Every endomorphism-linear Hom-module map has a unique persistence-map
preimage, naturally supplied by the principal-upset summands. -/
noncomputable def homEquiv (M N : PModule.{u,0,u} k S) :
    (M ⟶ N) ≃
      ((L (k := k) (S := S) ⟶ M) →ₗ[E (k := k) (S := S)]
        (L (k := k) (S := S) ⟶ N)) where
  toFun := postcompose (k := k) (S := S)
  invFun := preimage M N
  left_inv := preimage_postcompose M N
  right_inv := postcompose_preimage M N

/-- The actual hook-generator Hom functor is fully faithful on all persistence
modules, with no pointwise finite-dimensionality assumption. -/
noncomputable def homFunctor_fullyFaithful :
    (homFunctor (k := k) (S := S)).FullyFaithful where
  preimage T := preimage _ _ T.hom
  map_preimage := by
    intro M N T
    apply ModuleCat.hom_ext
    exact postcompose_preimage M N T.hom

noncomputable instance homFunctor_full :
    (homFunctor (k := k) (S := S)).Full :=
  (homFunctor_fullyFaithful (k := k) (S := S)).full

instance homFunctor_faithful :
    (homFunctor (k := k) (S := S)).Faithful :=
  (homFunctor_fullyFaithful (k := k) (S := S)).faithful

/-- Rank projectivity of a pointwise finite-dimensional persistence module is
equivalent to ordinary projectivity of its hook-generator Hom module. -/
theorem rankProjective_iff_homProjective (M : PModule.{u,0,u} k S)
    (hfd : ∀ a, FiniteDimensional k (M.obj a)) :
    IsRankProjective M ↔
      Module.Projective (E (k := k) (S := S))
        (L (k := k) (S := S) ⟶ M) := by
  constructor
  · intro h
    exact FiniteRankProjectiveHomProjective.hom_from_hookSum_isProjective M hfd h
  · intro h A B C ι π hs α
    have hsurj : Function.Surjective
        (postcompose (k := k) (S := S) π) :=
      (rankExact_iff_postcompose_surjective (k := k) (S := S)
        hs.toIsPointwiseShortExact hs.finiteDimensional).mp hs
    obtain ⟨lift, hlift⟩ := Module.projective_lifting_property (h := h)
      (postcompose (k := k) (S := S) π)
      (postcompose (k := k) (S := S) α) hsurj
    let β : M ⟶ B := preimage M B lift
    refine ⟨β, ?_⟩
    have hmap : postcompose (k := k) (S := S) (β ≫ π) =
        postcompose (k := k) (S := S) α := by
      rw [postcompose_comp, show postcompose (k := k) (S := S) β = lift from
        postcompose_preimage M B lift]
      exact hlift
    calc
      β ≫ π = preimage M C (postcompose (k := k) (S := S) (β ≫ π)) :=
        (preimage_postcompose M C (β ≫ π)).symm
      _ = preimage M C (postcompose (k := k) (S := S) α) := congrArg _ hmap
      _ = α := preimage_postcompose M C α

end

end TDA.Persistence.FiniteRankProjectiveHomFullyFaithful
