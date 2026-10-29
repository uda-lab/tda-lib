import TDA.Persistence.AlgebraicFamily

/-!
# Natural isomorphisms of algebraic families

Coordinate isomorphisms act on algebraic sums, and dependent occurrence indices
can be regrouped into iterated sums. Both operations commute with every real
persistence transition, without a finiteness or countability assumption.
-/

set_option autoImplicit false

universe u v w x y

namespace TDA.Persistence.AlgebraicFamily

open CategoryTheory
open scoped DirectSum Classical

variable {k : Type u} [Field k] {ι : Type}

/-- Natural maps on summands induce the coordinatewise map on the algebraic sum. -/
noncomputable def familyMap (F G : ι → PModule.{u,0,u} k ℝ)
    (η : ∀ i, F i ⟶ G i) : familyModule F ⟶ familyModule G := by
  classical
  refine { app := fun t => ModuleCat.ofHom (DirectSum.lmap (fun i => ((η i).app t).hom))
           naturality := ?_ }
  intro s t f
  apply ModuleCat.hom_ext
  change (DirectSum.lmap (fun i => ((η i).app t).hom)).comp
      (DirectSum.lmap (fun i => ((F i).map f).hom)) =
    (DirectSum.lmap (fun i => ((G i).map f).hom)).comp
      (DirectSum.lmap (fun i => ((η i).app s).hom))
  apply DirectSum.linearMap_ext
  intro i
  apply LinearMap.ext
  intro z
  simp only [LinearMap.comp_apply, DirectSum.lmap_lof]
  apply congrArg (DirectSum.lof k ι (fun j => (G j).obj t) i)
  exact congrArg (fun L => L.hom z) ((η i).naturality f)

/-- Isomorphisms on the summands induce a natural isomorphism on their algebraic sums. -/
noncomputable def familyIso (F G : ι → PModule.{u,0,u} k ℝ)
    (e : ∀ i, F i ≅ G i) : familyModule F ≅ familyModule G :=
  NatIso.ofComponents
    (fun t => (DirectSum.congrLinearEquiv (fun i => ((e i).app t).toLinearEquiv)).toModuleIso)
    (fun {_ _} f => (familyMap F G (fun i => (e i).hom)).naturality f)

private theorem sigma_lmap_natural
    {R : Type u} [Semiring R]
    {ι : Type v} [DecidableEq ι]
    {α : ι → Type w} [∀ i, DecidableEq (α i)]
    (D : ∀ i, α i → Type x)
    [∀ i a, AddCommMonoid (D i a)] [∀ i a, Module R (D i a)]
    (E : ∀ i, α i → Type y)
    [∀ i a, AddCommMonoid (E i a)] [∀ i a, Module R (E i a)]
    (f : ∀ i a, D i a →ₗ[R] E i a) :
    (DirectSum.sigmaLcurryEquiv (R := R) (δ := E)).toLinearMap.comp
      (DirectSum.lmap (fun j : Σ i, α i => f j.1 j.2)) =
    (DirectSum.lmap (fun i => DirectSum.lmap (f i))).comp
      (DirectSum.sigmaLcurryEquiv (R := R) (δ := D)).toLinearMap := by
  classical
  apply DirectSum.linearMap_ext
  intro j
  apply LinearMap.ext
  intro z
  simp only [LinearMap.comp_apply, DirectSum.lmap_lof]
  change DirectSum.sigmaCurry
      (DirectSum.lof R _ (fun j : Σ i, α i => E j.1 j.2) j (f j.1 j.2 z)) =
    DirectSum.lmap (fun i => DirectSum.lmap (f i))
      (DirectSum.sigmaCurry
        (DirectSum.lof R _ (fun j : Σ i, α i => D j.1 j.2) j z))
  have hD : DirectSum.sigmaCurry
      (DirectSum.lof R _ (fun j : Σ i, α i => D j.1 j.2) j z) =
      DirectSum.lof R ι (fun i => ⨁ a, D i a) j.1
        (DirectSum.lof R (α j.1) (D j.1) j.2 z) := by
    simpa only [DirectSum.lof_eq_of] using
      (DirectSum.sigmaCurry_of (δ := D) j z)
  have hE : DirectSum.sigmaCurry
      (DirectSum.lof R _ (fun j : Σ i, α i => E j.1 j.2) j (f j.1 j.2 z)) =
      DirectSum.lof R ι (fun i => ⨁ a, E i a) j.1
        (DirectSum.lof R (α j.1) (E j.1) j.2 (f j.1 j.2 z)) := by
    simpa only [DirectSum.lof_eq_of] using
      (DirectSum.sigmaCurry_of (δ := E) j (f j.1 j.2 z))
  rw [hD, hE, DirectSum.lmap_lof, DirectSum.lmap_lof]


/-- Curry a sigma-indexed algebraic family into an iterated algebraic family. -/
noncomputable def sigmaMap {κ : ι → Type}
    (F : (Σ i, κ i) → PModule.{u,0,u} k ℝ) :
    familyModule F ⟶ familyModule (fun i => familyModule (fun j : κ i => F ⟨i,j⟩)) := by
  classical
  refine { app := ?_, naturality := ?_ }
  · intro t
    exact ModuleCat.ofHom
      (DirectSum.sigmaLcurryEquiv (R := k)
        (δ := fun i : ι => fun j : κ i => (F ⟨i,j⟩).obj t)).toLinearMap
  · intro s t f
    apply ModuleCat.hom_ext
    let D : (i : ι) → κ i → Type u := fun i j => (F ⟨i,j⟩).obj s
    let E : (i : ι) → κ i → Type u := fun i j => (F ⟨i,j⟩).obj t
    let maps : ∀ i j, D i j →ₗ[k] E i j := fun i j => ((F ⟨i,j⟩).map f).hom
    change (DirectSum.sigmaLcurryEquiv (R := k) (δ := E)).toLinearMap.comp
        (DirectSum.lmap (fun j : Σ i, κ i => maps j.1 j.2)) =
      (DirectSum.lmap (fun i => DirectSum.lmap (maps i))).comp
        (DirectSum.sigmaLcurryEquiv (R := k) (δ := D)).toLinearMap
    exact sigma_lmap_natural D E maps

/-- A dependent sum of occurrence indices can be regrouped into iterated algebraic sums,
naturally for every persistence transition. No finiteness assumptions are required. -/
noncomputable def sigmaIso {κ : ι → Type}
    (F : (Σ i, κ i) → PModule.{u,0,u} k ℝ) :
    familyModule F ≅ familyModule (fun i => familyModule (fun j : κ i => F ⟨i,j⟩)) := by
  classical
  exact NatIso.ofComponents
    (fun t => (DirectSum.sigmaLcurryEquiv (R := k)
      (δ := fun i : ι => fun j : κ i => (F ⟨i,j⟩).obj t)).toModuleIso)
    (fun {_ _} f => (sigmaMap F).naturality f)

/-- The family isomorphism acts by the given summand isomorphism on each generator. -/
@[simp] theorem familyIso_hom_lof (F G : ι → PModule.{u,0,u} k ℝ)
    (e : ∀ i, F i ≅ G i) (t : ℝ) (i : ι) (z : (F i).obj t) :
    (((familyIso F G e).hom).app t).hom
      (DirectSum.lof k ι (fun j => (F j).obj t) i z) =
      DirectSum.lof k ι (fun j => (G j).obj t) i (((e i).hom.app t).hom z) := by
  classical
  change DirectSum.lmap (fun j => ((e j).hom.app t).hom)
    (DirectSum.lof k ι (fun j => (F j).obj t) i z) = _
  exact DirectSum.lmap_lof (fun j : ι => ((e j).hom.app t).hom) i z

/-- Sigma regrouping carries a generator to the corresponding nested generator. -/
@[simp] theorem sigmaIso_hom_lof {κ : ι → Type}
    (F : (Σ i, κ i) → PModule.{u,0,u} k ℝ)
    (t : ℝ) (i : ι) (j : κ i) (z : (F ⟨i,j⟩).obj t) :
    (((sigmaIso F).hom).app t).hom
      (DirectSum.lof k (Σ i, κ i) (fun a => (F a).obj t) ⟨i,j⟩ z) =
    DirectSum.lof k ι (fun a => DirectSum (κ a) (fun b => (F ⟨a,b⟩).obj t)) i
      (DirectSum.lof k (κ i) (fun b => (F ⟨i,b⟩).obj t) j z) := by
  classical
  change DirectSum.sigmaCurry
    (δ := fun a : ι => fun b : κ a => (F ⟨a,b⟩).obj t)
    (DirectSum.lof k _ (fun a : Σ i, κ i => (F a).obj t) ⟨i,j⟩ z) = _
  simpa only [DirectSum.lof_eq_of] using
    (DirectSum.sigmaCurry_of (δ := fun a : ι => fun b : κ a => (F ⟨a,b⟩).obj t) ⟨i,j⟩ z)

end TDA.Persistence.AlgebraicFamily
