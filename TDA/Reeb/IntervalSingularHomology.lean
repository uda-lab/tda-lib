import TDA.Reeb.IntervalComponents
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.AlgebraicTopology.SingularHomology.HomologyZero

/-!
# Degree-zero singular homology of interval preimages

For `f : C(X, ℝ)`, `intervalPreimageTopCat f : OpenInterval ⥤ TopCat` sends an open interval
`I` to the subspace `f ⁻¹ I` and an inclusion `I ≤ J` to the actual inclusion
`preimageInclusion f` of inverse images. `intervalSingularHomology k n f` is its composite with
`n`-th singular homology with coefficients `k₀ = ModuleCat.of k k`, and
`linearizedIntervalComponents k f = intervalComponents f ⋙ sigmaConst.obj k₀` is the free
`k`-module on the path-component precosheaf. In degree zero,
`intervalSingularHomologyIso₀ k f` is a natural isomorphism between them, with components
`TopCat.singularHomology₀Iso` at the preimage.

* `singularHomology₀Class X R x : R ⟶ H₀(X; R)` is the class of the point `x`, the image of the
  `0`-simplex `x` in homology. `singularHomology₀Class_comp_singularHomology₀Iso_hom` sends it to
  the coproduct injection indexed by `ZerothHomotopy.mk x`.
* `singularHomology₀Class_comp_map` states that a continuous map sends the class of `x` to the
  class of its image, and `singularHomology₀Iso_hom_naturality` that
  `TopCat.singularHomology₀Iso` is natural in `X` for the map `componentMap` of path components.
  The second is proved on point representatives: cancel the isomorphism at the source and test
  on the coproduct injections of path components, each of which is the image of a point class.
  `singularHomology₀ε_naturality` is the augmentation form.
* `intervalClass_comp_map_comp_intervalSingularHomologyIso₀_hom_app` and
  `intervalClass_comp_intervalSingularHomologyIso₀_hom_app_comp_map` are the public map rule: for
  `I ≤ J` and a point `x` of `f ⁻¹ I`, the class of `x` goes to the coproduct injection indexed by
  `ZerothHomotopy.mk` of the included point, along the homology square and along the linearized
  component square alike (`intervalComponents_map_mk`).
* `isZero_intervalSingularHomology₀_obj_bot` and `isZero_linearizedIntervalComponents_obj_bot`:
  the empty interval has zero value.

No compactness, tameness, local-connectedness or finiteness assumption is made, and the
coefficient ring `k` is arbitrary. This is the degree-zero comparison only: the isomorphism
forgets all higher homology and is not a derived equivalence. Two components of `f ⁻¹ I` that
meet in a larger `f ⁻¹ J` induce a fold `k ⊕ k ⟶ k`; see
`TDA.Reeb.Examples.IntervalSingularHomology` and
`docs/math/reeb-interval-singular-homology.md`.
-/

open CategoryTheory Limits AlgebraicTopology TypeCat
open scoped Simplicial

universe w u

namespace TDA.Reeb

/-! ### Degree zero of an arbitrary space -/

section DegreeZero

variable {C : Type*} [Category C] [HasCoproducts.{w} C] [Preadditive C] [CategoryWithHomology C]

/-- The class of a point `x` of `X` in `H₀(X; R)`: the image of the `0`-simplex `x`. -/
noncomputable def singularHomology₀Class (X : TopCat.{w}) (R : C) (x : X) :
    R ⟶ ((singularHomologyFunctor C 0).obj R).obj X :=
  (((TopCat.toSSet.obj X).chainComplex R).liftCycles
      (k := (TopCat.toSSet.obj X).ιChainComplex (TopCat.toSSetObj₀Equiv.symm x)) 0
      (by simp) (by simp)) ≫
    ((TopCat.toSSet.obj X).chainComplex R).homologyπ 0

-- The degree-zero singular homology API of Mathlib needs `respectTransparency` off at its own
-- declarations (`SingularHomology/HomologyZero.lean`); the same per-declaration setting is used here.
set_option backward.isDefEq.respectTransparency false in
/-- The class of `x` is sent by `TopCat.singularHomology₀Iso` to the coproduct injection indexed
by the path component of `x`. -/
@[reassoc (attr := simp)]
theorem singularHomology₀Class_comp_singularHomology₀Iso_hom (X : TopCat.{w}) (R : C) (x : X) :
    singularHomology₀Class X R x ≫ (TopCat.singularHomology₀Iso X R).hom =
      Sigma.ι (fun _ : ZerothHomotopy X => R) (ZerothHomotopy.mk x) := by
  have h := SSet.liftCycles_ιChainComplex_homologyπ_homology₀Iso_hom (R := R)
    (TopCat.toSSet.obj X) (TopCat.toSSetObj₀Equiv.symm x)
  unfold singularHomology₀Class TopCat.singularHomology₀Iso
  simp only [Iso.trans_hom, Category.assoc]
  rw [reassoc_of% h]
  simp [sigmaConst]

set_option backward.isDefEq.respectTransparency false in
/-- The coproduct injection of the component of `x` is sent back to the class of `x` by the
inverse of `TopCat.singularHomology₀Iso`. -/
@[reassoc (attr := simp)]
theorem sigma_ι_comp_singularHomology₀Iso_inv (X : TopCat.{w}) (R : C) (x : X) :
    Sigma.ι (fun _ : ZerothHomotopy X => R) (ZerothHomotopy.mk x) ≫
        (TopCat.singularHomology₀Iso X R).inv = singularHomology₀Class X R x := by
  rw [← singularHomology₀Class_comp_singularHomology₀Iso_hom, Category.assoc, Iso.hom_inv_id,
    Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
/-- A continuous map sends the class of `x` to the class of its image. -/
@[reassoc (attr := simp)]
theorem singularHomology₀Class_comp_map {X Y : TopCat.{w}} (g : X ⟶ Y) (R : C) (x : X) :
    singularHomology₀Class X R x ≫ ((singularHomologyFunctor C 0).obj R).map g =
      singularHomology₀Class Y R (g x) := by
  have e : (TopCat.toSSet.map g).app (Opposite.op ⦋0⦌) (TopCat.toSSetObj₀Equiv.symm x) =
      TopCat.toSSetObj₀Equiv.symm (g x) := by
    apply TopCat.toSSetObj₀Equiv.injective
    simp [TopCat.toSSetObj₀Equiv]
    rfl
  unfold singularHomology₀Class
  have hm : ((singularHomologyFunctor C 0).obj R).map g =
      HomologicalComplex.homologyMap
        (SSet.chainComplexMap (TopCat.toSSet.map g) R) 0 := rfl
  rw [Category.assoc, hm, HomologicalComplex.homologyπ_naturality,
    HomologicalComplex.liftCycles_comp_cyclesMap_assoc]
  simp only [SSet.ι_chainComplexMap_f, e]

set_option backward.isDefEq.respectTransparency false in
/-- `TopCat.singularHomology₀Iso` is natural in the space, for the map induced by `g` on path
components. -/
theorem singularHomology₀Iso_hom_naturality {X Y : TopCat.{w}} (g : X ⟶ Y) (R : C) :
    ((singularHomologyFunctor C 0).obj R).map g ≫ (TopCat.singularHomology₀Iso Y R).hom =
      (TopCat.singularHomology₀Iso X R).hom ≫
        (sigmaConst.obj R).map (TypeCat.ofHom (TDA.Topology.componentMap g.hom)) := by
  rw [← cancel_epi (TopCat.singularHomology₀Iso X R).inv, Iso.inv_hom_id_assoc]
  refine Sigma.hom_ext _ _ fun c => ?_
  induction c using ZerothHomotopy.rec with
  | mk x => simp [sigmaConst]

/-- The augmentation `H₀(X; R) ⟶ R` is natural in the space. -/
theorem singularHomology₀ε_naturality {X Y : TopCat.{w}} (g : X ⟶ Y) (R : C) :
    ((singularHomologyFunctor C 0).obj R).map g ≫ TopCat.singularHomology₀ε Y R =
      TopCat.singularHomology₀ε X R := by
  rw [← TopCat.singularHomology₀Iso_sigma_desc_id, ← TopCat.singularHomology₀Iso_sigma_desc_id,
    ← Category.assoc, singularHomology₀Iso_hom_naturality, Category.assoc]
  congr 1
  refine Sigma.hom_ext _ _ fun c => ?_
  simp [sigmaConst]

omit [CategoryWithHomology C] in
/-- A coproduct over an empty index type is zero. -/
theorem isZero_sigma_of_isEmpty {ι : Type w} [IsEmpty ι] (R : C) :
    IsZero (∐ fun _ : ι => R) :=
  (IsZero.iff_id_eq_zero _).2 (Sigma.hom_ext _ _ fun i => isEmptyElim i)

end DegreeZero

/-! ### Interval preimages -/

section Interval

open OpenInterval

variable {X : Type u} [TopologicalSpace X]

/-- The interval preimage functor `I ↦ f ⁻¹ I` into `TopCat`, sending an inclusion of intervals
to the actual inclusion `preimageInclusion` of inverse images along the interval-to-opens
functor. -/
def intervalPreimageTopCat (f : C(X, ℝ)) : OpenInterval ⥤ TopCat.{u} where
  obj I := TopCat.of {x : X // f x ∈ I}
  map {I J} i := TopCat.ofHom (preimageInclusion f (leOfHom (toOpensFunctor.map i)))
  map_id _ := by ext; rfl
  map_comp _ _ := by ext; rfl

@[simp]
theorem intervalPreimageTopCat_obj (f : C(X, ℝ)) (I : OpenInterval) :
    ((intervalPreimageTopCat f).obj I : Type u) = {x : X // f x ∈ I} := rfl

theorem intervalPreimageTopCat_map_hom (f : C(X, ℝ)) {I J : OpenInterval} (i : I ⟶ J) :
    ((intervalPreimageTopCat f).map i).hom =
      preimageInclusion f (leOfHom (toOpensFunctor.map i)) := rfl

@[simp]
theorem intervalPreimageTopCat_map_apply_val (f : C(X, ℝ)) {I J : OpenInterval} (i : I ⟶ J)
    (x : (intervalPreimageTopCat f).obj I) : (((intervalPreimageTopCat f).map i) x).1 = x.1 :=
  rfl

/-- The preimage inclusion of an inclusion of intervals, on path components, is the map of the
interval component functor. -/
theorem componentMap_intervalPreimageTopCat_map (f : C(X, ℝ)) {I J : OpenInterval} (i : I ⟶ J) :
    TDA.Topology.componentMap ((intervalPreimageTopCat f).map i).hom =
      (intervalComponents f).map i := rfl

variable (k : Type u) [Ring k]

/-- Singular homology with coefficients `k` in degree `n` of the preimages `f ⁻¹ I`, covariant in
inclusions of open intervals. The coefficient object `ModuleCat.of k k` is the same as in
`linearizedIntervalComponents`. -/
noncomputable def intervalSingularHomology (n : ℕ) (f : C(X, ℝ)) : OpenInterval ⥤ ModuleCat.{u} k :=
  intervalPreimageTopCat f ⋙ (singularHomologyFunctor (ModuleCat.{u} k) n).obj (ModuleCat.of k k)

/-- The path-component precosheaf `intervalComponents f` linearized over `k`: the free `k`-module
`∐_{c ∈ π₀ (f ⁻¹ I)} k` at each interval `I`, with the coproduct maps induced by the inclusions
of intervals. -/
noncomputable def linearizedIntervalComponents (f : C(X, ℝ)) : OpenInterval ⥤ ModuleCat.{u} k :=
  intervalComponents f ⋙ sigmaConst.obj (ModuleCat.of k k)

/-- Degree-zero singular homology of the interval preimages is naturally isomorphic to the
linearized path-component precosheaf; the component at `I` is
`TopCat.singularHomology₀Iso (f ⁻¹ I) k`. -/
noncomputable def intervalSingularHomologyIso₀ (f : C(X, ℝ)) :
    intervalSingularHomology k 0 f ≅ linearizedIntervalComponents k f :=
  NatIso.ofComponents
    (fun I => TopCat.singularHomology₀Iso ((intervalPreimageTopCat f).obj I) (ModuleCat.of k k))
    (fun {_ _} i => singularHomology₀Iso_hom_naturality ((intervalPreimageTopCat f).map i) _)

variable {k}

theorem intervalSingularHomologyIso₀_hom_app (f : C(X, ℝ)) (I : OpenInterval) :
    (intervalSingularHomologyIso₀ k f).hom.app I =
      (TopCat.singularHomology₀Iso ((intervalPreimageTopCat f).obj I) (ModuleCat.of k k)).hom :=
  rfl

theorem intervalSingularHomologyIso₀_inv_app (f : C(X, ℝ)) (I : OpenInterval) :
    (intervalSingularHomologyIso₀ k f).inv.app I =
      (TopCat.singularHomology₀Iso ((intervalPreimageTopCat f).obj I) (ModuleCat.of k k)).inv :=
  rfl

variable (k) in
/-- The class of a point of `f ⁻¹ I` in `H₀(f ⁻¹ I; k)`. -/
noncomputable abbrev intervalClass (f : C(X, ℝ)) (I : OpenInterval)
    (x : (intervalPreimageTopCat f).obj I) :
    ModuleCat.of k k ⟶ (intervalSingularHomology k 0 f).obj I :=
  singularHomology₀Class ((intervalPreimageTopCat f).obj I) (ModuleCat.of k k) x

/-- An inclusion of intervals sends the class of `x` to the class of the included point. -/
@[reassoc]
theorem intervalClass_comp_map (f : C(X, ℝ)) {I J : OpenInterval} (i : I ⟶ J)
    (x : (intervalPreimageTopCat f).obj I) :
    intervalClass k f I x ≫ (intervalSingularHomology k 0 f).map i =
      intervalClass k f J (((intervalPreimageTopCat f).map i) x) :=
  singularHomology₀Class_comp_map _ _ _

/-- The component of `intervalSingularHomologyIso₀` at `I` sends the class of `x` to the
coproduct injection indexed by the path component of `x`. -/
@[reassoc]
theorem intervalClass_comp_intervalSingularHomologyIso₀_hom_app (f : C(X, ℝ)) (I : OpenInterval)
    (x : (intervalPreimageTopCat f).obj I) :
    intervalClass k f I x ≫ (intervalSingularHomologyIso₀ k f).hom.app I =
      Sigma.ι (fun _ : (intervalComponents f).obj I => ModuleCat.of k k) (ZerothHomotopy.mk x) :=
  singularHomology₀Class_comp_singularHomology₀Iso_hom _ _ _

/-- **Map rule, homology side.** For `I ≤ J` and `x ∈ f ⁻¹ I`, the class of `x` is sent along the
inclusion `H₀(f ⁻¹ I) ⟶ H₀(f ⁻¹ J)` and the isomorphism at `J` to the coproduct injection
indexed by `ZerothHomotopy.mk` of the included point. -/
theorem intervalClass_comp_map_comp_intervalSingularHomologyIso₀_hom_app (f : C(X, ℝ))
    {I J : OpenInterval} (i : I ⟶ J) (x : (intervalPreimageTopCat f).obj I) :
    intervalClass k f I x ≫ (intervalSingularHomology k 0 f).map i ≫
        (intervalSingularHomologyIso₀ k f).hom.app J =
      Sigma.ι (fun _ : (intervalComponents f).obj J => ModuleCat.of k k)
        (ZerothHomotopy.mk
          (⟨x.1, OpenInterval.le_iff_subset.1 (leOfHom i) x.2⟩ : {x : X // f x ∈ toOpens J})) := by
  rw [intervalClass_comp_map_assoc]
  exact intervalClass_comp_intervalSingularHomologyIso₀_hom_app f J _

set_option backward.isDefEq.respectTransparency false in
/-- **Map rule, component side.** The same injection is the image of the injection indexed by the
path component of `x` under the linearized component map of `i`. -/
theorem intervalClass_comp_intervalSingularHomologyIso₀_hom_app_comp_map (f : C(X, ℝ))
    {I J : OpenInterval} (i : I ⟶ J) (x : (intervalPreimageTopCat f).obj I) :
    intervalClass k f I x ≫ (intervalSingularHomologyIso₀ k f).hom.app I ≫
        (linearizedIntervalComponents k f).map i =
      Sigma.ι (fun _ : (intervalComponents f).obj J => ModuleCat.of k k)
        (ZerothHomotopy.mk
          (⟨x.1, OpenInterval.le_iff_subset.1 (leOfHom i) x.2⟩ : {x : X // f x ∈ toOpens J})) := by
  rw [intervalClass_comp_intervalSingularHomologyIso₀_hom_app_assoc]
  simp only [linearizedIntervalComponents, Functor.comp_map, sigmaConst_obj_map]
  rw [Sigma.ι_comp_map', Category.id_comp]
  rfl

/-- The empty interval has zero degree-zero homology. -/
theorem isZero_intervalSingularHomology₀_obj_bot (f : C(X, ℝ)) :
    IsZero ((intervalSingularHomology k 0 f).obj ⊥) :=
  IsZero.of_iso (isZero_sigma_of_isEmpty _) ((intervalSingularHomologyIso₀ k f).app ⊥)

/-- The linearized component functor vanishes on the empty interval. -/
theorem isZero_linearizedIntervalComponents_obj_bot (f : C(X, ℝ)) :
    IsZero ((linearizedIntervalComponents k f).obj ⊥) :=
  isZero_sigma_of_isEmpty _

end Interval

end TDA.Reeb
