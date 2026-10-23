import TDA.Persistence.FiniteDecomposition

/-!
# Image factorization on a finite chain

The image fibers are linear-map ranges. Naturality restricts the target structure
maps to these ranges, giving a natural componentwise epi–mono factorization.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence

open CategoryTheory

variable {s : ℕ} {k : Type u} [Field k]
variable {M N : PModule.{u,0,u} k (Fin s)}

/-- The persistence module of component images, with induced structure maps. -/
def finiteImage (f : M ⟶ N) : PModule.{u,0,u} k (Fin s) where
  obj i := ModuleCat.of k (LinearMap.range (f.app i).hom)
  map {i j} g := ModuleCat.ofHom <|
    (((N.map g).hom).comp (LinearMap.range (f.app i).hom).subtype).codRestrict
      (LinearMap.range (f.app j).hom) (by
        rintro ⟨_, x, rfl⟩
        refine ⟨(M.map g).hom x, ?_⟩
        exact congrArg (fun h : M.obj i ⟶ N.obj j => h.hom x) (f.naturality g))
  map_id i := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change (N.map (𝟙 i)).hom x.val = x.val
    simp
  map_comp {i j l} g h := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change (N.map (g ≫ h)).hom x.val = (N.map h).hom ((N.map g).hom x.val)
    rw [N.map_comp]
    rfl

/-- Image fibers inherit finite dimensionality as submodules of the target fibers. -/
instance finiteImage_finiteDimensional (f : M ⟶ N)
    [∀ i, FiniteDimensional k (N.obj i)] (i : Fin s) :
    FiniteDimensional k ((finiteImage f).obj i) := by
  change FiniteDimensional k (LinearMap.range (f.app i).hom)
  infer_instance

/-- The componentwise corestriction to the image. -/
def toFiniteImage (f : M ⟶ N) : M ⟶ finiteImage f where
  app i := ModuleCat.ofHom (f.app i).hom.rangeRestrict
  naturality {i j} g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact congrArg (fun h : M.obj i ⟶ N.obj j => h.hom x) (f.naturality g)

/-- The componentwise inclusion of the image. -/
def fromFiniteImage (f : M ⟶ N) : finiteImage f ⟶ N where
  app i := ModuleCat.ofHom (LinearMap.range (f.app i).hom).subtype
  naturality {_i _j} _g := rfl

/-- The constructed epi–mono factors compose to the original natural transformation. -/
theorem toFiniteImage_comp_fromFiniteImage (f : M ⟶ N) :
    toFiniteImage f ≫ fromFiniteImage f = f := by
  apply NatTrans.ext
  funext i
  rfl

/-- Corestriction to a range is surjective at every stage. -/
theorem toFiniteImage_surjective (f : M ⟶ N) (i : Fin s) :
    Function.Surjective ((toFiniteImage f).app i).hom :=
  LinearMap.surjective_rangeRestrict _

/-- The image inclusion is injective at every stage. -/
theorem fromFiniteImage_injective (f : M ⟶ N) (i : Fin s) :
    Function.Injective ((fromFiniteImage f).app i).hom :=
  Subtype.val_injective

/-- A component injection remains injective after corestriction to its range. -/
theorem toFiniteImage_injective (f : M ⟶ N)
    (hf : ∀ i, Function.Injective (f.app i).hom) (i : Fin s) :
    Function.Injective ((toFiniteImage f).app i).hom :=
  (LinearMap.injective_rangeRestrict_iff _).mpr (hf i)

/-- For a componentwise surjection the image inclusion is also surjective. -/
theorem fromFiniteImage_surjective (f : M ⟶ N)
    (hf : ∀ i, Function.Surjective (f.app i).hom) (i : Fin s) :
    Function.Surjective ((fromFiniteImage f).app i).hom := by
  intro y
  obtain ⟨x, hx⟩ := hf i y
  exact ⟨⟨(f.app i).hom x, x, rfl⟩, hx⟩

end TDA.Persistence
