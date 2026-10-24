import TDA.Persistence.HookProjective
import TDA.Persistence.HookInfinity
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Products
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Kernels
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

/-!
# Projectivity relative to rank exact sequences

A module is rank projective when every morphism from it lifts along every
rank-exact quotient. Finite-death hooks and principal upsets have this
property, as do their finite categorical biproducts. Evaluation preserves
these biproducts and kernels, giving pointwise finite-dimensionality and
the ordinary short exact kernel sequence used by rank-projective deflations.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence

open CategoryTheory CategoryTheory.Limits

variable {k : Type u} [Field k] {P : Type} [PartialOrder P]

private instance : HasFiniteBiproducts (PModule.{u,0,u} k P) :=
  HasFiniteBiproducts.of_hasFiniteProducts

/-- The relative lifting property against actual pointwise-finite-dimensional
rank-exact short exact sequences. -/
def IsRankProjective (Q : PModule.{u,0,u} k P) : Prop :=
  ∀ (L M N : PModule.{u,0,u} k P) (ι : L ⟶ M) (π : M ⟶ N),
    IsRankExact ι π → ∀ α : Q ⟶ N, ∃ β : Q ⟶ M, β ≫ π = α

/-- Every nonzero finite-death hook is rank projective. -/
theorem Hook.isRankProjective {i j : P} (hij : i < j) :
    IsRankProjective (module (k := k) i j) := by
  intro L M N ι π hs α
  exact exists_lift hij hs α

/-- A principal upset is rank projective, including unbounded supports. -/
theorem HookInfinity.isRankProjective (i : P) :
    IsRankProjective (module (R := k) i) := by
  intro L M N ι π hs α
  exact exists_lift_rankExact hs α

/-- A finite-death hook has at most one coefficient in each fiber. -/
@[instance] theorem Hook.finiteDimensional (i j p : P) :
    FiniteDimensional k ((module (k := k) i j).obj p) := by
  change FiniteDimensional k (SupportInterval.fiber (k := k) (support i j) p)
  infer_instance

/-- Principal-upset fibers are zero or one-dimensional over the field. -/
@[instance] theorem HookInfinity.finiteDimensional (i p : P) :
    FiniteDimensional k ((module (R := k) i).obj p) := by
  change FiniteDimensional k (GradedFree.fiber (R := k) (generators i) p)
  infer_instance

/-- Relative projectivity is preserved by natural isomorphism. -/
theorem IsRankProjective.of_iso {Q Q' : PModule.{u,0,u} k P}
    (h : IsRankProjective Q) (e : Q ≅ Q') : IsRankProjective Q' := by
  intro L M N ι π hs α
  obtain ⟨β, hβ⟩ := h L M N ι π hs (e.hom ≫ α)
  refine ⟨e.inv ≫ β, ?_⟩
  simp [Category.assoc, hβ]

/-- A finite biproduct of rank projectives is rank projective. -/
theorem IsRankProjective.biproduct {J : Type} [Fintype J]
    (F : J → PModule.{u,0,u} k P) (hF : ∀ j, IsRankProjective (F j)) :
    IsRankProjective (⨁ F) := by
  intro L M N ι π hs α
  choose β hβ using fun j => hF j L M N ι π hs (biproduct.ι F j ≫ α)
  refine ⟨biproduct.desc β, ?_⟩
  apply biproduct.hom_ext'
  intro j
  simpa only [← Category.assoc, biproduct.ι_desc] using hβ j

/-- A retract of a rank-projective module is rank projective. -/
theorem IsRankProjective.of_retract {Q Q' : PModule.{u,0,u} k P}
    (h : IsRankProjective Q) (s : Q' ⟶ Q) (r : Q ⟶ Q') (hsr : s ≫ r = 𝟙 Q') :
    IsRankProjective Q' := by
  intro L M N ι π hs α
  obtain ⟨β, hβ⟩ := h L M N ι π hs (r ≫ α)
  refine ⟨s ≫ β, ?_⟩
  calc
    (s ≫ β) ≫ π = s ≫ (β ≫ π) := Category.assoc _ _ _
    _ = s ≫ (r ≫ α) := congrArg (fun f => s ≫ f) hβ
    _ = (s ≫ r) ≫ α := (Category.assoc _ _ _).symm
    _ = α := by rw [hsr, Category.id_comp]

namespace FiniteBiproduct

/-- Evaluating a finite categorical biproduct gives the ordinary product of
its fiber vector spaces. -/
noncomputable def fiberIsoPi {J : Type} [Fintype J]
    (F : J → PModule.{u,0,u} k P) (p : P) :
    (⨁ F).obj p ≅ ModuleCat.of k (∀ j, (F j).obj p) :=
  (Functor.mapBiproduct ((evaluation P (ModuleCat.{u} k)).obj p) F) ≪≫
    ModuleCat.biproductIsoPi (fun j => (F j).obj p)

/-- The fiber comparison reads the evaluated categorical projections. -/
theorem fiberIsoPi_hom_π {J : Type} [Fintype J]
    (F : J → PModule.{u,0,u} k P) (p : P) (j : J) :
    (fiberIsoPi F p).hom ≫ ModuleCat.ofHom (LinearMap.proj j) =
      (biproduct.π F j).app p := by
  have hπ : (ModuleCat.biproductIsoPi (fun j => (F j).obj p)).hom ≫
      ModuleCat.ofHom (LinearMap.proj j) = biproduct.π (fun j => (F j).obj p) j := by
    rw [← ModuleCat.biproductIsoPi_inv_comp_π, Iso.hom_inv_id_assoc]
  calc
    _ = (Functor.mapBiproduct ((evaluation P (ModuleCat.{u} k)).obj p) F).hom ≫
        ((ModuleCat.biproductIsoPi (fun j => (F j).obj p)).hom ≫
          ModuleCat.ofHom (LinearMap.proj j)) := Category.assoc _ _ _
    _ = (Functor.mapBiproduct ((evaluation P (ModuleCat.{u} k)).obj p) F).hom ≫
        biproduct.π (fun j => (F j).obj p) j :=
      congrArg (fun f =>
        (Functor.mapBiproduct ((evaluation P (ModuleCat.{u} k)).obj p) F).hom ≫ f) hπ
    _ = (biproduct.π F j).app p := biproduct.lift_π _ j

/-- Evaluated projections distinguish vectors in a finite biproduct fiber. -/
theorem element_ext {J : Type} [Fintype J]
    (F : J → PModule.{u,0,u} k P) (p : P) {x y : (⨁ F).obj p}
    (h : ∀ j, ((biproduct.π F j).app p).hom x = ((biproduct.π F j).app p).hom y) :
    x = y := by
  apply (ModuleCat.mono_iff_injective (fiberIsoPi F p).hom).mp inferInstance
  funext j
  have hx := congrArg (fun f : (⨁ F).obj p ⟶ (F j).obj p => f.hom x)
    (fiberIsoPi_hom_π F p j)
  have hy := congrArg (fun f : (⨁ F).obj p ⟶ (F j).obj p => f.hom y)
    (fiberIsoPi_hom_π F p j)
  exact hx.trans ((h j).trans hy.symm)

/-- Finite-dimensional summand fibers give finite-dimensional sum fibers. -/
theorem finiteDimensional {J : Type} [Fintype J]
    (F : J → PModule.{u,0,u} k P) (p : P)
    [∀ j, FiniteDimensional k ((F j).obj p)] :
    FiniteDimensional k ((⨁ F).obj p) :=
  FiniteDimensional.of_injective (fiberIsoPi F p).hom.hom
    ((ModuleCat.mono_iff_injective _).mp inferInstance)

end FiniteBiproduct

namespace RankKernel

variable {M N : PModule.{u,0,u} k P} (π : M ⟶ N)

/-- The existing categorical kernel at a grade is its linear-map kernel. -/
noncomputable def fiberIso (p : P) :
    (kernel π).obj p ≅ ModuleCat.of k (LinearMap.ker (π.app p).hom) :=
  (PreservesKernel.iso ((evaluation P (ModuleCat.{u} k)).obj p) π) ≪≫
    ModuleCat.kernelIsoKer (π.app p)

/-- The inverse fiber comparison commutes with the actual kernel inclusion. -/
theorem fiberIso_inv_ι (p : P) :
    (fiberIso π p).inv ≫ (kernel.ι π).app p =
      ModuleCat.ofHom (LinearMap.ker (π.app p).hom).subtype := by
  change (ModuleCat.kernelIsoKer (π.app p)).inv ≫
    (PreservesKernel.iso ((evaluation P (ModuleCat.{u} k)).obj p) π).inv ≫
      ((evaluation P (ModuleCat.{u} k)).obj p).map (kernel.ι π) = _
  rw [PreservesKernel.iso_inv_ι]
  exact ModuleCat.kernelIsoKer_inv_kernel_ι _

/-- The actual categorical kernel inclusion is injective at every grade. -/
theorem injective (p : P) : Function.Injective ((kernel.ι π).app p).hom := by
  exact (ModuleCat.mono_iff_injective _).mp inferInstance

/-- The image of the actual kernel inclusion is the linear-map kernel. -/
theorem range_eq_ker (p : P) :
    LinearMap.range ((kernel.ι π).app p).hom = LinearMap.ker (π.app p).hom := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    have h := congrArg (fun f => (f.app p).hom y) (kernel.condition π)
    exact h
  · intro hx
    refine ⟨(fiberIso π p).inv.hom ⟨x, hx⟩, ?_⟩
    exact congrArg (fun f : ModuleCat.of k (LinearMap.ker (π.app p).hom) ⟶ M.obj p =>
      f.hom ⟨x, hx⟩) (fiberIso_inv_ι π p)

/-- Every componentwise surjection has its ordinary short exact kernel sequence. -/
theorem shortExact (hπ : ∀ p, Function.Surjective (π.app p).hom) :
    IsPointwiseShortExact (kernel.ι π) π where
  injective := injective π
  surjective := hπ
  range_eq_ker := range_eq_ker π

/-- Kernel fibers inherit finite dimensionality from the source. -/
theorem finiteDimensional (p : P) [FiniteDimensional k (M.obj p)] :
    FiniteDimensional k ((kernel π).obj p) :=
  FiniteDimensional.of_injective ((kernel.ι π).app p).hom (injective π p)

/-- Surjectivity together with actual dying-element lifts gives the rank-exact
kernel sequence; rank additivity is derived rather than a premise. -/
theorem rankExact (hπ : ∀ p, Function.Surjective (π.app p).hom)
    [∀ p, FiniteDimensional k (M.obj p)]
    (hlift : ∀ {a b : P} (hab : a ≤ b) (n : N.obj a),
      structureMapLinear N hab n = 0 →
        ∃ m : M.obj a, (π.app a).hom m = n ∧ structureMapLinear M hab m = 0) :
    IsRankExact (kernel.ι π) π where
  toIsPointwiseShortExact := shortExact π hπ
  finiteDimensional _ := inferInstance
  rank_add hab := ((shortExact π hπ).rank_add_iff_lift_kernel hab).mpr (hlift hab)

end RankKernel

end TDA.Persistence
