import TDA.Persistence.Basic
import Mathlib.LinearAlgebra.Finsupp.Supported
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.Algebra.Category.ModuleCat.Limits

/-!
# Free persistence modules on graded generators

At index `a`, the free module has the generators whose grades are at most `a`.
The fibers are supported submodules of a single finitely supported function space;
structure maps are inclusions. This construction works over a ring and an arbitrary
preordered index, and does not use a monoid algebra.
-/

set_option autoImplicit false

universe u v w

namespace TDA.Persistence

open CategoryTheory

namespace GradedFree

noncomputable section

variable {R : Type u} [Ring R] {P : Type v} [Preorder P]

/-- A family of generators with assigned birth grades. -/
structure GradedGenerators (P : Type v) where
  Carrier : Type w
  grade : Carrier → P

variable (W : GradedGenerators.{v,w} P)

/-- The free fiber consists of finite linear combinations of generators born by `a`. -/
def fiber (a : P) : Submodule R (W.Carrier →₀ R) :=
  Finsupp.supported R R {g | W.grade g ≤ a}

/-- The fiber is the ordinary free module on generators available at `a`. -/
def fiberEquiv (a : P) :
    fiber (R := R) W a ≃ₗ[R] ({g : W.Carrier // W.grade g ≤ a} →₀ R) :=
  Finsupp.supportedEquivFinsupp {g | W.grade g ≤ a}

/-- Every generator present at `a` is present at later indices. -/
theorem fiber_mono {a b : P} (h : a ≤ b) : fiber (R := R) W a ≤ fiber W b := by
  intro x hx g hg
  exact (hx hg).trans h

/-- Free fibers agree when precisely the same generators are available. -/
theorem fiber_eq_of_birth_iff {a b : P}
    (h : ∀ g : W.Carrier, W.grade g ≤ a ↔ W.grade g ≤ b) :
    fiber (R := R) W a = fiber W b := by
  unfold fiber
  congr 1
  ext g
  exact h g

/-- A generator's basis vector at every index at or after its grade. -/
def generator (g : W.Carrier) {a : P} (h : W.grade g ≤ a) : fiber (R := R) W a :=
  ⟨Finsupp.single g 1, Finsupp.single_mem_supported R 1 h⟩

/-- The free persistence module on a graded family. -/
def module : PModule.{u,v,max u w} R P where
  obj a := ModuleCat.of R (fiber (R := R) W a)
  map {a b} f := ModuleCat.ofHom (Submodule.inclusion (fiber_mono (R := R) W (leOfHom f)))
  map_id a := by
    apply ModuleCat.hom_ext
    rfl
  map_comp f g := by
    apply ModuleCat.hom_ext
    rfl

/-- Structure maps retain the underlying finite linear combination. -/
@[simp] theorem structureMap_apply {a b : P} (h : a ≤ b) (x : fiber (R := R) W a) :
    (structureMapLinear (module (R := R) W) h x : fiber (R := R) W b).val = x.val := rfl

/-- If no generator is born between two comparable grades, their free-module
structure map is an isomorphism. -/
def structureIsoOfBirthIff {a b : P} (hab : a ≤ b)
    (h : ∀ g : W.Carrier, W.grade g ≤ a ↔ W.grade g ≤ b) :
    (module (R := R) W).obj a ≅ (module W).obj b where
  hom := structureMap (module W) hab
  inv := ModuleCat.ofHom
    (Submodule.inclusion (fiber_eq_of_birth_iff (R := R) W h).ge)
  hom_inv_id := by
    apply ModuleCat.hom_ext
    rfl
  inv_hom_id := by
    apply ModuleCat.hom_ext
    rfl

/-- The generator at its birth grade. -/
def birth (g : W.Carrier) : (module (R := R) W).obj (W.grade g) :=
  generator (R := R) W g le_rfl

/-- At any later index, a generator is the structure image of its birth vector. -/
theorem generator_eq_structureMap (g : W.Carrier) {a : P} (h : W.grade g ≤ a) :
    generator (R := R) W g h =
      structureMapLinear (module (R := R) W) h (birth (R := R) W g) := rfl

/-- A coefficient assignment to the available generators extends to a linear map
from the entire free fiber. -/
def fiberLift {V : Type*} [AddCommGroup V] [Module R V] (a : P)
    (v : {g : W.Carrier // W.grade g ≤ a} → V) : fiber (R := R) W a →ₗ[R] V :=
  (Finsupp.linearCombination R v).comp (fiberEquiv (R := R) W a).toLinearMap

/-- The extension evaluates to the selected vector on each basis generator. -/
@[simp] theorem fiberLift_generator {V : Type*} [AddCommGroup V] [Module R V]
    (a : P) (v : {g : W.Carrier // W.grade g ≤ a} → V)
    (g : W.Carrier) (h : W.grade g ≤ a) :
    fiberLift (R := R) W a v (generator (R := R) W g h) = v ⟨g, h⟩ := by
  have heq :
      (fiberEquiv (R := R) W a).symm (Finsupp.single ⟨g, h⟩ (1 : R)) =
        generator (R := R) W g h := by
    apply Subtype.ext
    exact Finsupp.supportedEquivFinsupp_symm_single _ _ _
  rw [← heq]
  simp [fiberLift, Finsupp.linearCombination_single]

/-- The available generators determine every linear map from a free fiber. -/
theorem fiberLift_unique {V : Type*} [AddCommGroup V] [Module R V]
    (a : P) (v : {g : W.Carrier // W.grade g ≤ a} → V)
    (f : fiber (R := R) W a →ₗ[R] V)
    (hf : ∀ g (h : W.grade g ≤ a), f (generator (R := R) W g h) = v ⟨g, h⟩) :
    f = fiberLift (R := R) W a v := by
  let e := fiberEquiv (R := R) W a
  have hb (i : {g : W.Carrier // W.grade g ≤ a}) :
      e.symm (Finsupp.basisSingleOne i) = generator (R := R) W i.val i.property := by
    apply Subtype.ext
    change ((Finsupp.supportedEquivFinsupp (R := R) {g | W.grade g ≤ a}).symm
      (Finsupp.single i (1 : R)) : W.Carrier →₀ R) = Finsupp.single i.val 1
    exact Finsupp.supportedEquivFinsupp_symm_single (R := R)
      {g | W.grade g ≤ a} i (1 : R)
  have he : f.comp e.symm.toLinearMap =
      (fiberLift (R := R) W a v).comp e.symm.toLinearMap := by
    apply Finsupp.basisSingleOne.ext
    intro i
    change f (e.symm (Finsupp.basisSingleOne i)) =
      fiberLift (R := R) W a v (e.symm (Finsupp.basisSingleOne i))
    rw [hb]
    exact (hf i.val i.property).trans
      (fiberLift_generator (R := R) W a v i.val i.property).symm
  apply LinearMap.ext
  intro x
  have hx := LinearMap.congr_fun he (e x)
  simpa using hx

/-- A degree-respecting choice of generator images extends to a natural map
of persistence modules. -/
def lift (M : PModule.{u,v,max u w} R P)
    (s : ∀ g : W.Carrier, M.obj (W.grade g)) : module (R := R) W ⟶ M where
  app a := ModuleCat.ofHom
    (fiberLift (R := R) W a fun g => structureMapLinear M g.property (s g.val))
  naturality a b f := by
    apply ModuleCat.hom_ext
    change (fiberLift (R := R) W b
        (fun i => structureMapLinear M i.property (s i.val))).comp
          (Submodule.inclusion (fiber_mono (R := R) W (leOfHom f))) =
      (structureMapLinear M (leOfHom f)).comp
        (fiberLift (R := R) W a
          (fun i => structureMapLinear M i.property (s i.val)))
    let v : {g : W.Carrier // W.grade g ≤ a} → M.obj b :=
      fun i => structureMapLinear M (i.property.trans (leOfHom f)) (s i.val)
    calc
      _ = fiberLift (R := R) W a v := by
        apply fiberLift_unique
        intro g h
        change fiberLift (R := R) W b
          (fun i => structureMapLinear M i.property (s i.val))
            (generator (R := R) W g (h.trans (leOfHom f))) = v ⟨g, h⟩
        exact fiberLift_generator (R := R) W b
          (fun i => structureMapLinear M i.property (s i.val)) g _
      _ = _ := by
        symm
        apply fiberLift_unique
        intro g h
        change structureMapLinear M (leOfHom f)
          (fiberLift (R := R) W a
            (fun i => structureMapLinear M i.property (s i.val))
            (generator (R := R) W g h)) = v ⟨g, h⟩
        rw [fiberLift_generator]
        exact (congrArg (fun q => q (s g))
          (structureMapLinear_comp M h (leOfHom f))).symm

/-- The natural extension maps a generator to its chosen image at birth. -/
@[simp] theorem lift_birth (M : PModule.{u,v,max u w} R P)
    (s : ∀ g : W.Carrier, M.obj (W.grade g)) (g : W.Carrier) :
    (lift (R := R) W M s).app (W.grade g) (birth (R := R) W g) = s g := by
  change fiberLift (R := R) W (W.grade g)
    (fun i => structureMapLinear M i.property (s i.val))
      (generator (R := R) W g le_rfl) = s g
  simp

/-- A natural map out of the free module is fixed by its values on the
generators at their birth grades. -/
theorem lift_unique (M : PModule.{u,v,max u w} R P)
    (s : ∀ g : W.Carrier, M.obj (W.grade g))
    (f : module (R := R) W ⟶ M)
    (hf : ∀ g, f.app (W.grade g) (birth (R := R) W g) = s g) :
    f = lift (R := R) W M s := by
  apply NatTrans.ext
  funext a
  apply ModuleCat.hom_ext
  apply fiberLift_unique (R := R) W a
    (fun i => structureMapLinear M i.property (s i.val))
  intro g h
  have hn := f.naturality (homOfLE h)
  have hg : (generator (R := R) W g h) =
      structureMapLinear (module (R := R) W) h (birth (R := R) W g) :=
    generator_eq_structureMap (R := R) W g h
  change f.app a (generator (R := R) W g h) =
    structureMapLinear M h (s g)
  rw [hg]
  have := congrArg (fun q : (module (R := R) W).obj (W.grade g) ⟶ M.obj a =>
    q (birth (R := R) W g)) hn
  simpa [structureMapLinear, structureMap, hf g] using this

/-- Maps out of a graded free module lift through a natural transformation
whose every component is surjective. No finite-generator assumption is needed. -/
theorem exists_lift_of_surjective
    {M N : PModule.{u,v,max u w} R P} (ρ : N ⟶ M)
    (hρ : ∀ a, Function.Surjective (ρ.app a))
    (f : module (R := R) W ⟶ M) :
    ∃ l : module (R := R) W ⟶ N, l ≫ ρ = f := by
  classical
  let s : ∀ g : W.Carrier, N.obj (W.grade g) :=
    fun g => Classical.choose (hρ (W.grade g) (f.app (W.grade g) (birth (R := R) W g)))
  refine ⟨lift (R := R) W N s, ?_⟩
  have h : lift (R := R) W N s ≫ ρ =
      lift (R := R) W M
        (fun g => f.app (W.grade g) (birth (R := R) W g)) := by
    apply lift_unique (R := R) W M
    intro g
    change ρ.app (W.grade g)
      ((lift (R := R) W N s).app (W.grade g) (birth (R := R) W g)) =
        f.app (W.grade g) (birth (R := R) W g)
    rw [lift_birth]
    exact Classical.choose_spec
      (hρ (W.grade g) (f.app (W.grade g) (birth (R := R) W g)))
  exact h.trans (lift_unique (R := R) W M _ f (fun _ => rfl)).symm

/-- Two lifts of the same map differ by an element of the cover kernel on
each graded generator. -/
theorem sub_lifts_mem_ker
    {M N : PModule.{u,v,max u w} R P} (ρ : N ⟶ M)
    (f : module (R := R) W ⟶ M)
    (l₁ l₂ : module (R := R) W ⟶ N)
    (h₁ : l₁ ≫ ρ = f) (h₂ : l₂ ≫ ρ = f) (g : W.Carrier) :
    l₁.app (W.grade g) (birth (R := R) W g) -
      l₂.app (W.grade g) (birth (R := R) W g) ∈
        LinearMap.ker (ρ.app (W.grade g)).hom := by
  rw [LinearMap.mem_ker, map_sub]
  have e₁ := congrArg (fun q : (module (R := R) W).obj (W.grade g) ⟶ M.obj (W.grade g) =>
    q (birth (R := R) W g)) (congrArg (fun q => q.app (W.grade g)) h₁)
  have e₂ := congrArg (fun q : (module (R := R) W).obj (W.grade g) ⟶ M.obj (W.grade g) =>
    q (birth (R := R) W g)) (congrArg (fun q => q.app (W.grade g)) h₂)
  simpa using congrArg₂ (· - ·) e₁ e₂

end

end GradedFree

end TDA.Persistence
