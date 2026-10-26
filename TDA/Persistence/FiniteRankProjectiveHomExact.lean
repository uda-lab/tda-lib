import TDA.Persistence.FiniteRankProjectiveHomProjective
import TDA.Persistence.RankExactKernel
import Mathlib.CategoryTheory.Preadditive.Opposite
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# Rank exactness detected by the finite hook generator

For a finite lattice, postcomposition on maps out of the finite sum of all
rank-projective hooks is the actual opposite-endomorphism-linear Hom functor.
Its surjectivity detects rank exactness, and on rank-exact rows it gives a
short exact sequence of modules over the opposite hook endomorphism algebra.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence.FiniteRankProjectiveHomExact

open CategoryTheory CategoryTheory.Limits
open TDA.Persistence.FiniteRankProjectiveEndAlgebra

variable {k : Type u} [Field k] {S : Type} [Lattice S] [Finite S]

noncomputable section

local instance : Fintype S := Fintype.ofFinite S
local instance : Fintype (HookTag (S := S)) := Fintype.ofFinite _

private instance : HasFiniteBiproducts (PModule.{u,0,u} k S) :=
  HasFiniteBiproducts.of_hasFiniteProducts

/-- The opposite endomorphism algebra acting on maps from the finite hook
 generator. -/
abbrev HomScalars := FiniteRankProjectiveHomProjective.HomScalars (k := k) (S := S)

/-- The E-opposite-linear map induced by postcomposition with a persistence
morphism. -/
noncomputable def postcompose {M N : PModule.{u,0,u} k S} (f : M ⟶ N) :
    (HookSum (k := k) (S := S) ⟶ M) →ₗ[HomScalars (k := k) (S := S)]
      (HookSum (k := k) (S := S) ⟶ N) where
  toFun g := g ≫ f
  map_add' g h := Preadditive.add_comp _ _ _ g h f
  map_smul' r g := by
    change (r.unop ≫ g) ≫ f = r.unop ≫ (g ≫ f)
    exact Category.assoc _ _ _

@[simp] theorem postcompose_apply {M N : PModule.{u,0,u} k S} (f : M ⟶ N)
    (g : HookSum (k := k) (S := S) ⟶ M) :
    postcompose (k := k) (S := S) f g = g ≫ f := rfl

@[simp] theorem postcompose_id (M : PModule.{u,0,u} k S) :
    postcompose (k := k) (S := S) (𝟙 M) = LinearMap.id := by
  ext g
  rfl

@[simp] theorem postcompose_comp {M N Q : PModule.{u,0,u} k S}
    (f : M ⟶ N) (g : N ⟶ Q) :
    postcompose (k := k) (S := S) (f ≫ g) =
      (postcompose (k := k) (S := S) g).comp
        (postcompose (k := k) (S := S) f) := by
  ext h
  rfl

/-- The actual module-valued Hom functor represented by the finite hook
 generator, with the opposite endomorphism action given by precomposition. -/
noncomputable abbrev homFunctor :
    PModule.{u,0,u} k S ⥤ ModuleCat.{u} (HomScalars (k := k) (S := S)) where
  obj M := ModuleCat.of _ (HookSum (k := k) (S := S) ⟶ M)
  map f := ModuleCat.ofHom (postcompose (k := k) (S := S) f)
  map_id M := by
    apply ModuleCat.hom_ext
    ext g
    rfl
  map_comp f g := by
    apply ModuleCat.hom_ext
    ext h
    rfl

@[simp] theorem homFunctor_map_apply {M N : PModule.{u,0,u} k S}
    (f : M ⟶ N) (g : HookSum (k := k) (S := S) ⟶ M) :
    ((homFunctor (k := k) (S := S)).map f).hom g = g ≫ f := rfl

/-- The finite hook generator is rank projective. -/
theorem hookSum_isRankProjective :
    IsRankProjective (HookSum (k := k) (S := S)) :=
  IsRankProjective.biproduct (hookFamily (k := k) (S := S)) (by
    intro t
    cases t with
    | inl ab => exact Hook.isRankProjective ab.property
    | inr a => exact HookInfinity.isRankProjective a)

/-- Rank exactness of a pointwise short exact row is equivalent to surjectivity
of postcomposition on maps from the finite hook generator. -/
theorem rankExact_iff_postcompose_surjective
    {A B C : PModule.{u,0,u} k S} {ι : A ⟶ B} {π : B ⟶ C}
    (hs : IsPointwiseShortExact ι π)
    (hfd : ∀ p, FiniteDimensional k (B.obj p)) :
    IsRankExact ι π ↔ Function.Surjective (postcompose (k := k) (S := S) π) := by
  constructor
  · intro hr g
    obtain ⟨g', hg'⟩ := hookSum_isRankProjective (k := k) (S := S)
      A B C ι π hr g
    exact ⟨g', by simpa using hg'⟩
  · intro hsurj
    refine ⟨hs, hfd, ?_⟩
    intro a b hab
    letI : FiniteDimensional k (B.obj a) := hfd a
    apply (hs.rank_add_iff_lift_kernel hab).mpr
    intro c hc
    by_cases habEq : a = b
    · subst b
      have hc' : c = 0 := by simpa only [structureMapLinear_self, LinearMap.id_apply] using hc
      exact ⟨0, by simp [hc'], by simp⟩
    · have hab' : a < b := lt_of_le_of_ne hab habEq
      let t : HookTag (S := S) := .inl ⟨(a, b), hab'⟩
      let H : PModule.{u,0,u} k S := hookFamily (k := k) (S := S) t
      have hH : H = Hook.module (k := k) a b := rfl
      let gen : (Hook.module (k := k) a b).obj a :=
        SupportInterval.one (Hook.support a b) (Hook.birth_mem hab')
      let θ : Hook.module (k := k) a b ⟶ C :=
        (Hook.homEquivKernel hab' C).symm ⟨c, hc⟩
      have hθ : (θ.app a).hom gen = c := by
        exact congrArg Subtype.val
          ((Hook.homEquivKernel hab' C).apply_symm_apply ⟨c, hc⟩)
      let θ' : HookSum (k := k) (S := S) ⟶ C :=
        biproduct.π (hookFamily (k := k) (S := S)) t ≫ eqToHom hH ≫ θ
      obtain ⟨g, hg⟩ := hsurj θ'
      let incl : Hook.module (k := k) a b ⟶ HookSum (k := k) (S := S) :=
        eqToHom hH.symm ≫ biproduct.ι (hookFamily (k := k) (S := S)) t
      let lift : Hook.module (k := k) a b ⟶ B := incl ≫ g
      have hg' : g ≫ π = θ' := by
        change postcompose (k := k) (S := S) π g = θ'
        exact hg
      have hlift : lift ≫ π = θ := by
        dsimp [lift]
        calc
          (incl ≫ g) ≫ π = incl ≫ (g ≫ π) := Category.assoc _ _ _
          _ = incl ≫ θ' := congrArg (fun q => incl ≫ q) hg'
          _ = θ := by simp [incl, θ']
      refine ⟨(lift.app a).hom gen, ?_, ?_⟩
      · have h := congrArg (fun φ : Hook.module (k := k) a b ⟶ C =>
          (φ.app a).hom gen) hlift
        simpa [hθ] using h
      · exact Hook.generator_dies hab' lift

/-- The actual short complex obtained by applying the module-valued Hom functor
to a pointwise short exact row. -/
noncomputable def homShortComplex
    {A B C : PModule.{u,0,u} k S} {ι : A ⟶ B} {π : B ⟶ C}
    (hs : IsPointwiseShortExact ι π) :
    ShortComplex (ModuleCat.{u} (HomScalars (k := k) (S := S))) :=
  ShortComplex.mk
    ((homFunctor (k := k) (S := S)).map ι)
    ((homFunctor (k := k) (S := S)).map π)
    (by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro f
      change (f ≫ ι) ≫ π = 0
      calc
        (f ≫ ι) ≫ π = f ≫ (ι ≫ π) := Category.assoc _ _ _
        _ = 0 := by rw [hs.comp_eq_zero]; simp)

/-- Postcomposition sends a rank-exact row to a short exact row in the actual
module category over the opposite endomorphism algebra. In particular the
first map is injective and the middle term is the kernel of the last map. -/
theorem homFunctor_map_shortExact
    {A B C : PModule.{u,0,u} k S} {ι : A ⟶ B} {π : B ⟶ C}
    (hs : IsRankExact ι π) :
    (homShortComplex (k := k) (S := S) hs.toIsPointwiseShortExact).ShortExact := by
  let S' := homShortComplex (k := k) (S := S) hs.toIsPointwiseShortExact
  have hsurj : Function.Surjective (postcompose (k := k) (S := S) π) :=
    (rankExact_iff_postcompose_surjective (k := k) (S := S)
      hs.toIsPointwiseShortExact hs.finiteDimensional).mp hs
  have hinj : Function.Injective (postcompose (k := k) (S := S) ι) := by
    intro f g h
    ext p x
    exact hs.injective p (congrArg (fun q => (q.app p).hom x) h)
  have hExact : S'.Exact := by
    rw [ShortComplex.moduleCat_exact_iff]
    intro f hf
    change postcompose (k := k) (S := S) π f = 0 at hf
    change HookSum (k := k) (S := S) ⟶ B at f
    let e := hs.toIsPointwiseShortExact.kernelIso
    let fk : HookSum (k := k) (S := S) ⟶ kernel π :=
      kernel.lift π f hf
    refine ⟨fk ≫ e.inv, ?_⟩
    change postcompose (k := k) (S := S) ι (fk ≫ e.inv) = f
    dsimp [postcompose]
    have hfactor : fk ≫ kernel.ι π = f := by
      dsimp [fk]
      exact kernel.lift_ι π f hf
    have heι : e.hom ≫ kernel.ι π = ι :=
      hs.toIsPointwiseShortExact.kernelIso_hom_ι
    calc
      (fk ≫ e.inv) ≫ ι = (fk ≫ e.inv) ≫ (e.hom ≫ kernel.ι π) := by
        exact congrArg (fun q => (fk ≫ e.inv) ≫ q) heι.symm
      _ = ((fk ≫ e.inv) ≫ e.hom) ≫ kernel.ι π := Category.assoc _ _ _
      _ = fk ≫ kernel.ι π := by simp
      _ = f := hfactor
  haveI : Mono S'.f :=
    (ModuleCat.mono_iff_injective _).2 (by
      change Function.Injective (postcompose (k := k) (S := S) ι)
      exact hinj)
  haveI : Epi S'.g :=
    (ModuleCat.epi_iff_surjective _).2 (by
      change Function.Surjective (postcompose (k := k) (S := S) π)
      exact hsurj)
  exact ⟨hExact⟩

end

end TDA.Persistence.FiniteRankProjectiveHomExact
