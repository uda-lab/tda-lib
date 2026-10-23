import TDA.Persistence.RealBarcode
import Mathlib.Algebra.DirectSum.Module
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Algebraic sums of real persistence modules

The fiber of `familyModule F` is the algebraic direct sum of the fibers of `F`.
Its canonical map to `RealBarcode.familyModule F` is an isomorphism when only
finitely many summands have a nontrivial fiber at each parameter. This finiteness
is a consequence of a pointwise finite-dimensional direct-sum representation.
The occurrence type can be uncountable.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence.AlgebraicFamily

open CategoryTheory

variable {k : Type u} [Field k] {ι : Type}

/-- The algebraic direct sum, with coordinatewise transition maps. -/
noncomputable def familyModule (F : ι → PModule.{u,0,u} k ℝ) :
    PModule.{u,0,u} k ℝ where
  obj t := ModuleCat.of k (DirectSum ι (fun i => (F i).obj t))
  map f := ModuleCat.ofHom (DirectSum.lmap (fun i : ι => ((F i).map f).hom))
  map_id t := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply DFinsupp.ext
    intro i
    simp
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply DFinsupp.ext
    intro i
    simp [Functor.map_comp]

/-- The summand at an occurrence maps naturally into the algebraic sum. -/
noncomputable def inclusion (F : ι → PModule.{u,0,u} k ℝ) (i : ι) :
    F i ⟶ familyModule F := by
  classical
  refine { app := fun t => ModuleCat.ofHom (DirectSum.lof k ι (fun j => (F j).obj t) i)
           naturality := ?_ }
  intro s t f
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change DirectSum.lof k ι (fun j => (F j).obj t) i (((F i).map f).hom x) =
    DirectSum.lmap (fun j => ((F j).map f).hom)
      (DirectSum.lof k ι (fun j => (F j).obj s) i x)
  simp

/-- The inclusion retains its own fiber coordinate. -/
@[simp] theorem inclusion_apply_self (F : ι → PModule.{u,0,u} k ℝ)
    (i : ι) (t : ℝ) (x : (F i).obj t) :
    DirectSum.component k ι (fun j => (F j).obj t) i
      (((inclusion F i).app t).hom x) = x := by
  classical
  change DirectSum.component k ι (fun j => (F j).obj t) i
    (DirectSum.lof k ι (fun j => (F j).obj t) i x) = x
  simp

/-- The inclusion has zero in every other fiber coordinate. -/
@[simp] theorem inclusion_apply_ne (F : ι → PModule.{u,0,u} k ℝ)
    {i j : ι} (hij : i ≠ j) (t : ℝ) (x : (F i).obj t) :
    DirectSum.component k ι (fun l => (F l).obj t) j
      (((inclusion F i).app t).hom x) = 0 := by
  classical
  change DirectSum.component k ι (fun l => (F l).obj t) j
    (DirectSum.lof k ι (fun l => (F l).obj t) i x) = 0
  rw [DirectSum.component.of]
  simp [hij]

/-- Assemble a family of natural maps by the universal property of the algebraic sum. -/
noncomputable def desc (F : ι → PModule.{u,0,u} k ℝ)
    {M : PModule.{u,0,u} k ℝ} (η : ∀ i, F i ⟶ M) : familyModule F ⟶ M := by
  classical
  refine { app := ?_, naturality := ?_ }
  · intro t
    exact ModuleCat.ofHom
      (DirectSum.toModule k ι (M.obj t) (fun i => ((η i).app t).hom))
  intro s t f
  apply ModuleCat.hom_ext
  apply DirectSum.linearMap_ext
  intro i
  apply LinearMap.ext
  intro x
  change DirectSum.toModule k ι (M.obj t) (fun j => ((η j).app t).hom)
      (DirectSum.lmap (fun j => ((F j).map f).hom)
        (DirectSum.lof k ι (fun j => (F j).obj s) i x)) =
    (M.map f).hom (DirectSum.toModule k ι (M.obj s) (fun j => ((η j).app s).hom)
      (DirectSum.lof k ι (fun j => (F j).obj s) i x))
  simp only [DirectSum.lmap_lof, DirectSum.toModule_lof]
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using
    congrArg (fun L => L.hom x) ((η i).naturality f)

/-- The assembled map agrees with the given map on each summand. -/
@[simp] theorem inclusion_desc (F : ι → PModule.{u,0,u} k ℝ)
    {M : PModule.{u,0,u} k ℝ} (η : ∀ i, F i ⟶ M) (i : ι) :
    inclusion F i ≫ desc F η = η i := by
  classical
  ext t x
  change DirectSum.toModule k ι (M.obj t) (fun j => ((η j).app t).hom)
    (DirectSum.lof k ι (fun j => (F j).obj t) i x) = ((η i).app t).hom x
  simp

/-- The structure map of an algebraic sum acts in each coordinate. -/
@[simp] theorem structureMap_apply (F : ι → PModule.{u,0,u} k ℝ)
    {s t : ℝ} (h : s ≤ t) (x : (familyModule F).obj s) (i : ι) :
    DirectSum.component k ι (fun j => (F j).obj t) i
      (structureMapLinear (familyModule F) h x) =
      structureMapLinear (F i) h
        (DirectSum.component k ι (fun j => (F j).obj s) i x) := by
  classical
  change DirectSum.component k ι (fun j => (F j).obj t) i
    (DirectSum.lmap (fun j : ι => ((F j).map (homOfLE h)).hom) x) =
    ((F i).map (homOfLE h)).hom
      (DirectSum.component k ι (fun j => (F j).obj s) i x)
  rfl

/-- The canonical injection into the existing coordinate-product realization. -/
noncomputable def toProduct (F : ι → PModule.{u,0,u} k ℝ) :
    familyModule F ⟶ RealBarcode.familyModule F where
  app t := ModuleCat.ofHom (DFinsupp.coeFnLinearMap k)
  naturality := by
    intro s t f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext i
    rfl

/-- The canonical comparison retains every coordinate. -/
@[simp] theorem toProduct_apply (F : ι → PModule.{u,0,u} k ℝ) (t : ℝ)
    (x : (familyModule F).obj t) (i : ι) :
    ((toProduct F).app t).hom x i =
      DirectSum.component k ι (fun j => (F j).obj t) i x := rfl

/-- The comparison from an algebraic sum to a product is injective at every fiber. -/
theorem toProduct_injective (F : ι → PModule.{u,0,u} k ℝ) (t : ℝ) :
    Function.Injective (((toProduct F).app t).hom) := by
  change Function.Injective (DFinsupp.coeFnLinearMap k :
    DirectSum ι (fun i => (F i).obj t) →ₗ[k] ∀ i, (F i).obj t)
  exact DFunLike.coe_injective

/-- Under finite activity, every product vector has finite support. -/
theorem toProduct_surjective (F : ι → PModule.{u,0,u} k ℝ) (t : ℝ)
    (h : Set.Finite {i | Nontrivial ((F i).obj t)}) :
    Function.Surjective (((toProduct F).app t).hom) := by
  classical
  intro x
  let y : DirectSum ι (fun i => (F i).obj t) :=
    DFinsupp.mk h.toFinset (fun i : (↑h.toFinset : Set ι) => x i)
  refine ⟨y, ?_⟩
  funext i
  change y i = x i
  by_cases hi : i ∈ h.toFinset
  · exact DFinsupp.mk_of_mem hi
  · have hn : ¬Nontrivial ((F i).obj t) := by simpa using hi
    exact @Subsingleton.elim ((F i).obj t)
      (not_nontrivial_iff_subsingleton.mp hn) _ _

/-- Finite activity identifies the algebraic sum with the preserved product API,
through the canonical coordinate map. -/
noncomputable def productIso (F : ι → PModule.{u,0,u} k ℝ)
    (h : ∀ t, Set.Finite {i | Nontrivial ((F i).obj t)}) :
    familyModule F ≅ RealBarcode.familyModule F :=
  NatIso.ofComponents (fun t =>
    (LinearEquiv.ofBijective (((toProduct F).app t).hom)
      ⟨toProduct_injective F t, toProduct_surjective F t (h t)⟩).toModuleIso)
    (fun f => (toProduct F).naturality f)

/-- The natural isomorphism uses the canonical comparison as its forward map. -/
@[simp] theorem productIso_hom (F : ι → PModule.{u,0,u} k ℝ)
    (h : ∀ t, Set.Finite {i | Nontrivial ((F i).obj t)}) :
    (productIso F h).hom = toProduct F := rfl

/-- For a finite occurrence type, the algebraic-sum realization canonically
agrees with the coordinate-product realization used by finite barcodes. -/
noncomputable def finiteProductIso [Finite ι]
    (F : ι → PModule.{u,0,u} k ℝ) :
    familyModule F ≅ RealBarcode.familyModule F :=
  productIso F (fun _ => Set.toFinite _)

set_option linter.style.haveILetI false in
/-- Finite-dimensional algebraic sums have only finitely many nonzero summands.
This imposes no finiteness or countability condition on the occurrence type. -/
theorem finite_nontrivial_of_finiteDimensional (F : ι → PModule.{u,0,u} k ℝ) (t : ℝ)
    [FiniteDimensional k ((familyModule F).obj t)] :
    Set.Finite {i | Nontrivial ((F i).obj t)} := by
  classical
  let A := {i | Nontrivial ((F i).obj t)}
  have hn (i : A) : ∃ x : (F i).obj t, x ≠ 0 := by
    exact @exists_ne ((F i).obj t) i.property 0
  choose v hv using hn
  let w (i : A) : DirectSum ι (fun j => (F j).obj t) :=
    DirectSum.lof k ι (fun j => (F j).obj t) i.val (v i)
  have hw : LinearIndependent k w := by
    rw [linearIndependent_iff']
    intro s c hc i hi
    have he := congrArg (DirectSum.component k ι (fun j => (F j).obj t) i.val) hc
    have hsum : (∑ j ∈ s, c j •
        DirectSum.component k ι (fun l => (F l).obj t) i.val (w j)) = c i • v i := by
      rw [Finset.sum_eq_single i]
      · simp [w]
      · intro j _ hji
        have hval : j.val ≠ i.val := fun h => hji (Subtype.ext h)
        simp [w, DirectSum.component.of, hval]
      · simp [hi]
    have he' : (∑ j ∈ s, c j •
        DirectSum.component k ι (fun l => (F l).obj t) i.val (w j)) = 0 := by
      have hmap := map_sum (DirectSum.component k ι (fun l => (F l).obj t) i.val)
        (fun j : A => c j • w j) s
      calc
        _ = ∑ j ∈ s,
            DirectSum.component k ι (fun l => (F l).obj t) i.val (c j • w j) := by
              simp only [map_smul]
        _ = DirectSum.component k ι (fun l => (F l).obj t) i.val
            (∑ j ∈ s, c j • w j) := hmap.symm
        _ = DirectSum.component k ι (fun l => (F l).obj t) i.val 0 := he
        _ = 0 := map_zero _
    rw [hsum] at he'
    exact (smul_eq_zero.mp he').resolve_right (hv i)
  letI : FiniteDimensional k (DirectSum ι (fun j => (F j).obj t)) := by
    change FiniteDimensional k ((familyModule F).obj t)
    infer_instance
  letI := hw.finite
  exact Set.toFinite A

set_option linter.style.haveILetI false in
/-- A pointwise finite-dimensional module represented by an algebraic sum has
finite activity at each parameter; local finiteness is an output. -/
theorem finite_nontrivial_of_iso {M : PModule.{u,0,u} k ℝ}
    (F : ι → PModule.{u,0,u} k ℝ) (e : M ≅ familyModule F)
    (hM : ∀ t, FiniteDimensional k (M.obj t)) (t : ℝ) :
    Set.Finite {i | Nontrivial ((F i).obj t)} := by
  letI := hM t
  letI : FiniteDimensional k ((familyModule F).obj t) :=
    Module.Finite.equiv ((e.app t).toLinearEquiv)
  exact finite_nontrivial_of_finiteDimensional F t

/-- A pointwise finite-dimensional algebraic-sum representation also gives a
product representation, through a natural isomorphism with the same coordinates. -/
noncomputable def productIsoOfRepresentation {M : PModule.{u,0,u} k ℝ}
    (F : ι → PModule.{u,0,u} k ℝ) (e : M ≅ familyModule F)
    (hM : ∀ t, FiniteDimensional k (M.obj t)) :
    familyModule F ≅ RealBarcode.familyModule F :=
  productIso F (finite_nontrivial_of_iso F e hM)

/-- Only finitely many occurrences of a locally finite family meet a finite
observation list. No global finiteness of the family is needed. -/
theorem finite_observed_nontrivial (F : ι → PModule.{u,0,u} k ℝ)
    (h : ∀ t, Set.Finite {i | Nontrivial ((F i).obj t)})
    {N : ℕ} (c : Fin N → ℝ) :
    Set.Finite {i | ∃ n, Nontrivial ((F i).obj (c n))} := by
  have he : {i | ∃ n, Nontrivial ((F i).obj (c n))} =
      ⋃ n : Fin N, {i | Nontrivial ((F i).obj (c n))} := by
    ext i
    simp
  rw [he]
  exact Set.finite_iUnion (fun n => h (c n))

/-- A finite observation list detects only finitely many summands in a pointwise
finite-dimensional algebraic-sum representation. The occurrence type itself can
remain infinite or uncountable. -/
theorem finite_observed_nontrivial_of_iso {M : PModule.{u,0,u} k ℝ}
    (F : ι → PModule.{u,0,u} k ℝ) (e : M ≅ familyModule F)
    (hM : ∀ t, FiniteDimensional k (M.obj t))
    {N : ℕ} (c : Fin N → ℝ) :
    Set.Finite {i | ∃ n, Nontrivial ((F i).obj (c n))} :=
  finite_observed_nontrivial F (finite_nontrivial_of_iso F e hM) c

end TDA.Persistence.AlgebraicFamily
