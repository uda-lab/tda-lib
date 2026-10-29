import TDA.Persistence.FiniteInjectivePresentation
import TDA.Persistence.RankExactKernel
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# The two-injective presentation

The coordinate embedding of a pointwise finite-dimensional persistence module
has an actual categorical cokernel. Embedding that cokernel into its own
coordinate injective gives the concrete two-step injective construction used
for the Hom dimension shift.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence.TwoInjectivePresentation

open CategoryTheory CategoryTheory.Limits
open scoped Classical

variable {k : Type u} [Field k] {S : Type} [Lattice S] [Finite S]
  [OrderBot S] [OrderTop S]

noncomputable section

local instance : Fintype S := Fintype.ofFinite S

private instance : HasFiniteBiproducts (PModule.{u,0,u} k S) :=
  HasFiniteBiproducts.of_hasFiniteProducts

open FiniteInjectivePresentation

/-- The first actual coordinate injective containing `M`. -/
abbrev firstInjective (M : PModule.{u,0,u} k S) := module M

/-- The coordinate embedding of `M` into its first injective. -/
abbrev firstEmbedding (M : PModule.{u,0,u} k S)
    [∀ p, FiniteDimensional k (M.obj p)] : M ⟶ firstInjective M := embedding M

/-- The actual categorical cokernel of the first coordinate embedding. -/
def quotient (M : PModule.{u,0,u} k S)
    [∀ p, FiniteDimensional k (M.obj p)] : PModule.{u,0,u} k S :=
  cokernel (firstEmbedding M)

/-- The actual epic projection from the first injective to its cokernel. -/
def quotientProjection (M : PModule.{u,0,u} k S)
    [∀ p, FiniteDimensional k (M.obj p)] : firstInjective M ⟶ quotient M :=
  cokernel.π (firstEmbedding M)

/-- The cokernel projection is surjective in every fiber. -/
theorem quotientProjection_surjective (M : PModule.{u,0,u} k S)
    [∀ p, FiniteDimensional k (M.obj p)] (p : S) :
    Function.Surjective ((quotientProjection M).app p).hom := by
  haveI : Epi (cokernel.π (firstEmbedding M)) := inferInstance
  have hEpi : Epi (quotientProjection M) := by
    change Epi (cokernel.π (firstEmbedding M))
    infer_instance
  have hApp : Epi ((quotientProjection M).app p) :=
    (NatTrans.epi_iff_epi_app (quotientProjection M)).mp hEpi p
  exact (ModuleCat.epi_iff_surjective _).mp hApp

/-- The actual cokernel remains pointwise finite-dimensional, by the epic
projection from the already finite-dimensional first injective. -/
theorem quotient_finiteDimensional (M : PModule.{u,0,u} k S)
    [∀ p, FiniteDimensional k (M.obj p)] (p : S) :
    FiniteDimensional k ((quotient M).obj p) := by
  letI : FiniteDimensional k ((firstInjective M).obj p) :=
    FiniteInjectivePresentation.finiteDimensional M p
  exact FiniteDimensional.of_surjective ((quotientProjection M).app p).hom
    (quotientProjection_surjective M p)

/-- The second actual coordinate injective, built from the actual cokernel. -/
abbrev secondInjective (M : PModule.{u,0,u} k S)
    [∀ p, FiniteDimensional k (M.obj p)] := module (quotient M)

/-- The coordinate embedding of the actual cokernel into the second injective. -/
def secondEmbedding (M : PModule.{u,0,u} k S)
    [∀ p, FiniteDimensional k (M.obj p)] : quotient M ⟶ secondInjective M := by
  letI : ∀ p, FiniteDimensional k ((quotient M).obj p) := quotient_finiteDimensional M
  exact embedding (quotient M)

/-- The map from the first injective to the second is the actual cokernel
projection followed by the coordinate embedding of that cokernel. -/
def differential (M : PModule.{u,0,u} k S)
    [∀ p, FiniteDimensional k (M.obj p)] :
    firstInjective M ⟶ secondInjective M := quotientProjection M ≫ secondEmbedding M

@[simp] theorem differential_eq (M : PModule.{u,0,u} k S)
    [∀ p, FiniteDimensional k (M.obj p)] :
    differential M = quotientProjection M ≫ secondEmbedding M := rfl

/-- The defining composition is zero. -/
@[reassoc (attr := simp)] theorem firstEmbedding_comp_differential
    (M : PModule.{u,0,u} k S) [∀ p, FiniteDimensional k (M.obj p)] :
    firstEmbedding M ≫ differential M = 0 := by
  have hzero : firstEmbedding M ≫ quotientProjection M = 0 := by
    change firstEmbedding M ≫ cokernel.π (firstEmbedding M) = 0
    exact cokernel.condition _
  calc
    firstEmbedding M ≫ differential M =
        (firstEmbedding M ≫ quotientProjection M) ≫ secondEmbedding M := by
          simp [differential, Category.assoc]
    _ = 0 := by rw [hzero, zero_comp]

/-- The first coordinate injective is an ordinary injective object. -/
theorem firstInjective_injective (M : PModule.{u,0,u} k S) :
    Injective (firstInjective M) := inferInstance

/-- The second coordinate injective is an ordinary injective object. -/
theorem secondInjective_injective (M : PModule.{u,0,u} k S)
    [∀ p, FiniteDimensional k (M.obj p)] :
    Injective (secondInjective M) := inferInstance

/-- The first coordinate embedding is monic. -/
theorem firstEmbedding_mono (M : PModule.{u,0,u} k S)
    [∀ p, FiniteDimensional k (M.obj p)] : Mono (firstEmbedding M) := inferInstance

/-- The second coordinate embedding is monic. -/
theorem secondEmbedding_mono (M : PModule.{u,0,u} k S)
    [∀ p, FiniteDimensional k (M.obj p)] : Mono (secondEmbedding M) := by
  letI : ∀ p, FiniteDimensional k ((quotient M).obj p) := quotient_finiteDimensional M
  exact FiniteInjectivePresentation.embedding_mono (quotient M)

/-- Projection onto a selected first-injective summand recovers its coordinate
coextension. -/
@[reassoc] theorem firstEmbedding_π (M : PModule.{u,0,u} k S)
    [∀ p, FiniteDimensional k (M.obj p)] (t : Index M) :
    firstEmbedding M ≫ biproduct.π (family M) t = summandMap M t :=
  embedding_π M t

/-- The projected coefficient of the first embedding is the transported basis
coordinate, and is zero outside the selected downset. -/
theorem firstEmbedding_π_app_val (M : PModule.{u,0,u} k S)
    [∀ p, FiniteDimensional k (M.obj p)] (t : Index M) (q : S) (x : M.obj q) :
    (((biproduct.π (family M) t).app q).hom
      (((firstEmbedding M).app q).hom x) : k) =
      if h : q ≤ t.1 then coordinate M t.1 t.2 (structureMapLinear M h x) else 0 :=
  embedding_π_app_val M t q x

/-- The pointwise cokernel row of the first embedding is short exact. -/
def cokernelRow (M : PModule.{u,0,u} k S)
    [∀ p, FiniteDimensional k (M.obj p)] :
    IsPointwiseShortExact (firstEmbedding M) (quotientProjection M) where
  injective p := by
    apply (ModuleCat.mono_iff_injective _).mp
    exact (NatTrans.mono_iff_mono_app _).mp (firstEmbedding_mono M) p
  surjective := quotientProjection_surjective M
  range_eq_ker := by
    intro p
    have h := (ShortComplex.exact_cokernel (firstEmbedding M)).map_of_epi_of_preservesCokernel
      ((evaluation S (ModuleCat.{u} k)).obj p) inferInstance inferInstance
    exact h.moduleCat_range_eq_ker

/-- The actual two-injective sequence is exact at the first injective: the
first embedding is monic and its image is exactly the kernel of the composed
map to the second injective. -/
theorem range_firstEmbedding_eq_ker_differential
    (M : PModule.{u,0,u} k S) [∀ p, FiniteDimensional k (M.obj p)] (p : S) :
    LinearMap.range ((firstEmbedding M).app p).hom =
      LinearMap.ker ((differential M).app p).hom := by
  have hrow := cokernelRow M
  have hmono : Function.Injective ((secondEmbedding M).app p).hom := by
    apply (ModuleCat.mono_iff_injective _).mp
    exact (NatTrans.mono_iff_mono_app _).mp (secondEmbedding_mono M) p
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    apply LinearMap.mem_ker.mpr
    have hzero := congrArg (fun f => (f.app p).hom y)
      (cokernel.condition (firstEmbedding M))
    change ((quotientProjection M).app p).hom
      (((firstEmbedding M).app p).hom y) = 0 at hzero
    change ((secondEmbedding M).app p).hom
      (((quotientProjection M).app p).hom (((firstEmbedding M).app p).hom y)) = 0
    rw [hzero, map_zero]
  · intro hx
    have hπzero : ((quotientProjection M).app p).hom x = 0 := by
      apply hmono
      have hx' := LinearMap.mem_ker.mp hx
      have hcomp : ((differential M).app p).hom =
          ((secondEmbedding M).app p).hom.comp ((quotientProjection M).app p).hom := rfl
      rw [hcomp, LinearMap.comp_apply] at hx'
      rw [hx', map_zero]
    rw [hrow.range_eq_ker p]
    exact LinearMap.mem_ker.mpr hπzero

/-- The actual two-injective sequence is exact at `I₀` as a short complex in
the abelian category of persistence modules. -/
def shortComplex (M : PModule.{u,0,u} k S)
    [∀ p, FiniteDimensional k (M.obj p)] :
    ShortComplex (PModule.{u,0,u} k S) :=
  ShortComplex.mk (firstEmbedding M) (differential M)
    (by
      apply firstEmbedding_comp_differential)

theorem shortComplex_exact (M : PModule.{u,0,u} k S)
    [∀ p, FiniteDimensional k (M.obj p)] : (shortComplex M).Exact := by
  let S' := shortComplex M
  apply S'.exact_iff_kernel_ι_comp_cokernel_π_zero.mpr
  ext p x
  have hzero : (S'.g.app p).hom (((kernel.ι S'.g).app p).hom x) = 0 := by
    have h := congrArg (fun f => (f.app p).hom x) (kernel.condition S'.g)
    exact h
  have heq : LinearMap.range ((firstEmbedding M).app p).hom =
      LinearMap.ker (S'.g.app p).hom := by
    change LinearMap.range ((firstEmbedding M).app p).hom =
      LinearMap.ker ((differential M).app p).hom
    exact range_firstEmbedding_eq_ker_differential M p
  have hxker : ((kernel.ι S'.g).app p).hom x ∈ LinearMap.ker (S'.g.app p).hom :=
    LinearMap.mem_ker.mpr hzero
  have hrange : ((kernel.ι S'.g).app p).hom x ∈
      LinearMap.range ((firstEmbedding M).app p).hom := by
    rw [← heq] at hxker
    exact hxker
  obtain ⟨y, hy⟩ : ∃ y : M.obj p,
      ((firstEmbedding M).app p).hom y = ((kernel.ι S'.g).app p).hom x := by
    exact (LinearMap.mem_range.mp hrange)
  change ((quotientProjection M).app p).hom (((kernel.ι S'.g).app p).hom x) = 0
  rw [← hy]
  have h := congrArg (fun f => (f.app p).hom y) (cokernel.condition (firstEmbedding M))
  exact h

end

end TDA.Persistence.TwoInjectivePresentation
