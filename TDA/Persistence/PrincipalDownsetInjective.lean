import TDA.Persistence.SupportInterval
import Mathlib.Algebra.Category.ModuleCat.EpiMono
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.CategoryTheory.Linear.FunctorCategory
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Principal-downset injectives

The interval module supported on `Set.Iic p` represents the dual of evaluation
at `p`: a functional extends to every earlier grade by the structure map, and
vanishes outside the downset. Extending functionals along injective linear maps
then proves ordinary categorical injectivity, without finiteness assumptions.

For finite posets with a bottom element these are the rectangles `R_(bottom,p)`
in BOOS, arXiv:2208.00300v3, Lemma 2.4. The direct-sum classification in that
lemma requires additional arguments beyond these individual injectives.
-/

set_option autoImplicit false

universe u v

namespace TDA.Persistence.PrincipalDownsetInjective

open CategoryTheory
open scoped Classical

variable {k : Type u} [Field k] {P : Type v} [Preorder P]

/-- One scalar at every grade below `p`, with the support-interval maps. -/
noncomputable abbrev module (p : P) : PModule.{u,v,u} k P :=
  SupportInterval.module (Set.Iic p) Set.ordConnected_Iic

/-- Read the scalar coefficient of a map at its terminal support grade. -/
noncomputable def evaluation (p : P) (M : PModule.{u,v,u} k P)
    (f : M ⟶ module p) : M.obj p →ₗ[k] k :=
  (SupportInterval.fiber (k := k) (Set.Iic p) p).subtype.comp (f.app p).hom

private noncomputable def extensionLinear (p : P) (M : PModule.{u,v,u} k P)
    (l : M.obj p →ₗ[k] k) (q : P) :
    M.obj q →ₗ[k] SupportInterval.fiber (k := k) (Set.Iic p) q := by
  classical
  exact if h : q ≤ p then
    (l.comp (structureMapLinear M h)).codRestrict _ (by
      intro x
      simp [SupportInterval.fiber, h]) else 0

private theorem extensionLinear_val (p : P) (M : PModule.{u,v,u} k P)
    (l : M.obj p →ₗ[k] k) (q : P) (x : M.obj q) :
    (extensionLinear p M l q x : k) =
      if h : q ≤ p then l (structureMapLinear M h x) else 0 := by
  classical
  by_cases h : q ≤ p <;> simp [extensionLinear, h]

/-- Coextend a functional by transport to `p`, and by zero outside its downset. -/
noncomputable def extension (p : P) (M : PModule.{u,v,u} k P)
    (l : M.obj p →ₗ[k] k) : M ⟶ module p where
  app q := ModuleCat.ofHom (extensionLinear p M l q)
  naturality {q r} f := by
    classical
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change (extensionLinear p M l r (structureMapLinear M (leOfHom f) x) : k) =
      (structureMapLinear (module p) (leOfHom f) (extensionLinear p M l q x) : k)
    rw [extensionLinear_val, SupportInterval.structureMap_val, extensionLinear_val]
    by_cases hr : r ≤ p
    · have hq : q ≤ p := (leOfHom f).trans hr
      simp only [hr, hq, Set.mem_Iic, dite_true, if_true]
      rw [structureMapLinear_comp M (leOfHom f) hr]
      rfl
    · simp [hr]

/-- The coefficient of the coextension at any grade, including the zero boundary. -/
theorem extension_app_val (p : P) (M : PModule.{u,v,u} k P)
    (l : M.obj p →ₗ[k] k) (q : P) (x : M.obj q) :
    (((extension p M l).app q).hom x : k) =
      if h : q ≤ p then l (structureMapLinear M h x) else 0 :=
  extensionLinear_val p M l q x

/-- A coextension recovers its functional at the terminal support grade. -/
@[simp] theorem evaluation_extension (p : P) (M : PModule.{u,v,u} k P)
    (l : M.obj p →ₗ[k] k) : evaluation p M (extension p M l) = l := by
  ext x
  change (((extension p M l).app p).hom x : k) = l x
  rw [extension_app_val]
  simp

/-- Naturality determines every coefficient from the component at `p`. -/
theorem app_val (p : P) (M : PModule.{u,v,u} k P)
    (f : M ⟶ module p) (q : P) (x : M.obj q) :
    ((f.app q).hom x : k) =
      if h : q ≤ p then evaluation p M f (structureMapLinear M h x) else 0 := by
  classical
  by_cases h : q ≤ p
  · have hn := congrArg (fun g => (g.hom x : k)) (f.naturality (homOfLE h))
    change evaluation p M f (structureMapLinear M h x) =
      (structureMapLinear (module p) h ((f.app q).hom x) : k) at hn
    rw [SupportInterval.structureMap_val, if_pos (show p ∈ Set.Iic p from le_rfl)] at hn
    simpa [h] using hn.symm
  · simpa [h] using SupportInterval.val_eq_zero (Set.Iic p) h ((f.app q).hom x)

/-- A morphism into a principal downset is determined by its endpoint functional. -/
@[ext] theorem hom_ext (p : P) (M : PModule.{u,v,u} k P)
    {f g : M ⟶ module p} (h : evaluation p M f = evaluation p M g) : f = g := by
  ext q x
  rw [app_val, app_val, h]

/-- Coextension of the endpoint functional recovers the whole morphism. -/
@[simp] theorem extension_evaluation (p : P) (M : PModule.{u,v,u} k P)
    (f : M ⟶ module p) : extension p M (evaluation p M f) = f := by
  apply hom_ext p M
  exact evaluation_extension p M _

/-- The linear dual of evaluation represents maps into the principal downset. -/
noncomputable def homLinearEquiv (p : P) (M : PModule.{u,v,u} k P) :
    (M ⟶ module p) ≃ₗ[k] (M.obj p →ₗ[k] k) where
  toFun := evaluation p M
  invFun := extension p M
  left_inv := extension_evaluation p M
  right_inv := evaluation_extension p M
  map_add' f g := by ext x; rfl
  map_smul' c f := by ext x; rfl

/-- Evaluation commutes with precomposition by a natural transformation. -/
theorem evaluation_precomp (p : P) {M N : PModule.{u,v,u} k P}
    (a : M ⟶ N) (f : N ⟶ module p) :
    evaluation p M (a ≫ f) = (evaluation p N f).comp (a.app p).hom := rfl

/-- Coextension commutes with precomposition by a natural transformation. -/
theorem extension_precomp (p : P) {M N : PModule.{u,v,u} k P}
    (a : M ⟶ N) (l : N.obj p →ₗ[k] k) :
    a ≫ extension p N l = extension p M (l.comp (a.app p).hom) := by
  apply hom_ext p M
  simp [evaluation_precomp]

/-- The principal-downset module is injective against arbitrary ambient monos. -/
instance isInjective (p : P) : Injective (module (k := k) p) where
  factors {A B} g f _ := by
    have hinj : Function.Injective (f.app p).hom :=
      (ModuleCat.mono_iff_injective _).mp ((NatTrans.mono_iff_mono_app f).mp inferInstance p)
    obtain ⟨s, hs⟩ := (f.app p).hom.exists_leftInverse_of_injective
      (LinearMap.ker_eq_bot.mpr hinj)
    refine ⟨extension p B ((evaluation p A g).comp s), ?_⟩
    apply hom_ext p A
    rw [evaluation_precomp, evaluation_extension, LinearMap.comp_assoc, hs,
      LinearMap.comp_id]

/-- Every principal-downset fiber is finite-dimensional over the arbitrary field. -/
instance finiteDimensional (p q : P) : FiniteDimensional k ((module (k := k) p).obj q) := by
  change FiniteDimensional k (SupportInterval.fiber (k := k) (Set.Iic p) q)
  infer_instance

end TDA.Persistence.PrincipalDownsetInjective
