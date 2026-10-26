import TDA.Persistence.PrincipalDownsetInjective
import TDA.Persistence.RankProjective

/-!
# Finite injective presentations

Over a finite poset, the basis coordinates of a pointwise finite-dimensional
module give an embedding into a finite biproduct of principal-downset
injectives. Each basis coordinate contributes its own occurrence. An ordinary
injective module is exactly one for which this embedding admits a retraction.

This supplies finite pointwise finite-dimensional injective presentations used
in the two-injective step of BOOS, arXiv:2208.00300v3, Theorem 5.16. It makes no
minimality or direct-sum classification assertion.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence.FiniteInjectivePresentation

open CategoryTheory CategoryTheory.Limits
open scoped Classical

variable {k : Type u} [Field k] {P : Type} [PartialOrder P] [Finite P]

noncomputable section

local instance : Fintype P := Fintype.ofFinite P

private instance : HasFiniteBiproducts (PModule.{u,0,u} k P) :=
  HasFiniteBiproducts.of_hasFiniteProducts

variable (M : PModule.{u,0,u} k P)

/-- A separate occurrence for every basis coordinate at every grade. -/
abbrev Index := Σ p : P, Fin (Module.finrank k (M.obj p))

instance indexFintype : Fintype (Index M) := by unfold Index; infer_instance

/-- The principal-downset injective assigned to each occurrence. -/
abbrev family (t : Index M) : PModule.{u,0,u} k P := PrincipalDownsetInjective.module t.1

/-- The actual finite categorical biproduct of the selected injectives. -/
def module : PModule.{u,0,u} k P := ⨁ family M

/-- The finite biproduct is an ordinary injective object. -/
instance isInjective : Injective (module M) := by
  unfold module
  have : ∀ t : Index M, Injective (family M t) := fun t =>
    PrincipalDownsetInjective.isInjective t.1
  infer_instance

/-- Its fibers are finite-dimensional. -/
instance finiteDimensional (p : P) : FiniteDimensional k ((module M).obj p) := by
  exact FiniteBiproduct.finiteDimensional (family M) p

variable [∀ p, FiniteDimensional k (M.obj p)]

/-- The chosen finite-basis coordinate functional. -/
def coordinate (p : P) (j : Fin (Module.finrank k (M.obj p))) : M.obj p →ₗ[k] k :=
  (Module.finBasis k (M.obj p)).coord j

/-- Coextend the coordinate functional into its principal downset. -/
def summandMap (t : Index M) : M ⟶ family M t :=
  PrincipalDownsetInjective.extension t.1 M (coordinate M t.1 t.2)

/-- Assemble all coordinate coextensions into the finite biproduct. -/
def embedding : M ⟶ module M := biproduct.lift (summandMap M)

/-- Projection recovers the selected coordinate coextension. -/
@[reassoc] theorem embedding_π (t : Index M) :
    embedding M ≫ biproduct.π (family M) t = summandMap M t := biproduct.lift_π _ _

/-- The coefficient of every projected component, both inside and outside the downset. -/
theorem embedding_π_app_val (t : Index M) (q : P) (x : M.obj q) :
    (((biproduct.π (family M) t).app q).hom (((embedding M).app q).hom x) : k) =
      if h : q ≤ t.1 then coordinate M t.1 t.2 (structureMapLinear M h x) else 0 := by
  have h := congrArg (fun f : M ⟶ family M t => ((f.app q).hom x : k)) (embedding_π M t)
  exact h.trans (PrincipalDownsetInjective.extension_app_val t.1 M _ q x)

/-- At its own grade, a projected component is the original basis coordinate. -/
@[simp] theorem embedding_coordinate (q : P) (j : Fin (Module.finrank k (M.obj q)))
    (x : M.obj q) :
    (((biproduct.π (family M) ⟨q, j⟩).app q).hom (((embedding M).app q).hom x) : k) =
      coordinate M q j x := by
  rw [embedding_π_app_val]
  simp

/-- The coordinates at grade `q` separate vectors, even in dimension zero. -/
theorem component_injective (q : P) : Function.Injective ((embedding M).app q).hom := by
  intro x y h
  apply (Module.finBasis k (M.obj q)).repr.injective
  ext j
  have hj := congrArg (fun z => (((biproduct.π (family M) ⟨q, j⟩).app q).hom z : k)) h
  rw [embedding_coordinate, embedding_coordinate] at hj
  exact hj

/-- The coordinate embedding is a categorical monomorphism. -/
instance embedding_mono : Mono (embedding M) := by
  apply (NatTrans.mono_iff_mono_app _).mpr
  intro q
  exact (ModuleCat.mono_iff_injective _).mpr (component_injective M q)

/-- A chosen retraction of the coordinate embedding for an injective module. -/
def retraction [Injective M] : module M ⟶ M := Injective.factorThru (𝟙 M) (embedding M)

/-- The chosen retraction splits the coordinate embedding. -/
@[reassoc (attr := simp)] theorem embedding_retraction [Injective M] :
    embedding M ≫ retraction M = 𝟙 M := Injective.comp_factorThru _ _

/-- Ordinary injectivity is equivalent to splitting the constructed embedding. -/
theorem injective_iff_splits : Injective M ↔
    ∃ r : module M ⟶ M, embedding M ≫ r = 𝟙 M := by
  constructor
  · intro h
    have := h
    exact ⟨retraction M, embedding_retraction M⟩
  · rintro ⟨r, hr⟩
    exact (show Retract M (module M) from ⟨embedding M, r, hr⟩).injective

/-- The finite pointwise finite-dimensional ordinary injective presentation. -/
def presentation : InjectivePresentation M where
  J := module M
  f := embedding M

/-- The presentation's actual injective target has finite-dimensional fibers. -/
theorem presentation_finiteDimensional (p : P) :
    FiniteDimensional k ((presentation M).J.obj p) := finiteDimensional M p

end

end TDA.Persistence.FiniteInjectivePresentation
