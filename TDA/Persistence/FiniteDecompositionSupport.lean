import TDA.Persistence.RankBarcodeIso
import Mathlib.LinearAlgebra.Prod

/-! # Pointwise products and assembly for finite interval decomposition -/

universe u
namespace TDA.Persistence
open CategoryTheory
variable {k : Type u} [Field k] {N : ℕ}

/-- The ordinary product of the fibers, with componentwise structure maps. -/
noncomputable def pointwiseProd (M L : PModule.{u,0,u} k (Fin N)) :
    PModule.{u,0,u} k (Fin N) where
  obj i := ModuleCat.of k (M.obj i × L.obj i)
  map f := ModuleCat.ofHom ((M.map f).hom.prodMap (L.map f).hom)
  map_id i := by
    apply ModuleCat.hom_ext
    ext x <;> simp [LinearMap.prodMap]
  map_comp f g := by
    apply ModuleCat.hom_ext
    ext x <;> simp [LinearMap.prodMap, Functor.map_comp]

instance pointwiseProd_finiteDimensional (M L : PModule.{u,0,u} k (Fin N))
    [∀ i, FiniteDimensional k (M.obj i)] [∀ i, FiniteDimensional k (L.obj i)]
    (i : Fin N) : FiniteDimensional k ((pointwiseProd M L).obj i) := by
  change FiniteDimensional k (M.obj i × L.obj i)
  infer_instance

private theorem natTrans_apply {M L : PModule.{u,0,u} k (Fin N)}
    (a : M ⟶ L) {i j : Fin N} (f : i ⟶ j) (x : M.obj i) :
    (a.app j).hom ((M.map f).hom x) = (L.map f).hom ((a.app i).hom x) := by
  exact congrArg (fun g : M.obj i ⟶ L.obj j => g.hom x) (a.naturality f)

/-- Fiberwise products preserve natural isomorphisms. -/
noncomputable def pointwiseProdIso {M M' L L' : PModule.{u,0,u} k (Fin N)}
    (e : M ≅ M') (f : L ≅ L') : pointwiseProd M L ≅ pointwiseProd M' L' :=
  NatIso.ofComponents
    (fun i => ((e.app i).toLinearEquiv.prodCongr (f.app i).toLinearEquiv).toModuleIso)
    (by
      intro i j g
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      apply Prod.ext
      · exact natTrans_apply e.hom g x.1
      · exact natTrans_apply f.hom g x.2)

/-- The finite sum of the dimensions of all observed fibers. -/
noncomputable def totalDimension (M : PModule.{u,0,u} k (Fin N)) : ℕ :=
  ∑ i, Module.finrank k (M.obj i)

/-- Natural isomorphisms preserve the sum of stage dimensions. -/
theorem totalDimension_eq_of_iso {M L : PModule.{u,0,u} k (Fin N)} (e : M ≅ L) :
    totalDimension M = totalDimension L := by
  apply Finset.sum_congr rfl
  intro i _
  exact (e.app i).toLinearEquiv.finrank_eq

/-- The dimension sum is additive under pointwise products. -/
theorem totalDimension_pointwiseProd (M L : PModule.{u,0,u} k (Fin N))
    [∀ i, FiniteDimensional k (M.obj i)] [∀ i, FiniteDimensional k (L.obj i)] :
    totalDimension (pointwiseProd M L) = totalDimension M + totalDimension L := by
  unfold totalDimension
  change (∑ i, Module.finrank k (M.obj i × L.obj i)) = _
  simp_rw [Module.finrank_prod]
  exact Finset.sum_add_distrib

/-- The kernel fibers of a natural transformation, with the restricted structure maps. -/
noncomputable def splitComplement {A M : PModule.{u,0,u} k (Fin N)} (ret : M ⟶ A) :
    PModule.{u,0,u} k (Fin N) where
  obj i := ModuleCat.of k (LinearMap.ker (ret.app i).hom)
  map {i j} f := ModuleCat.ofHom <|
    ((M.map f).hom.comp (LinearMap.ker (ret.app i).hom).subtype).codRestrict
      (LinearMap.ker (ret.app j).hom) (by
        intro x
        change (ret.app j).hom ((M.map f).hom x.val) = 0
        rw [natTrans_apply ret f x.val, x.property, map_zero])
  map_id i := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    simp
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    simp [Functor.map_comp]

instance splitComplement_finiteDimensional {A M : PModule.{u,0,u} k (Fin N)}
    [∀ i, FiniteDimensional k (M.obj i)] (ret : M ⟶ A) (i : Fin N) :
    FiniteDimensional k ((splitComplement ret).obj i) := by
  change FiniteDimensional k (LinearMap.ker (ret.app i).hom)
  infer_instance

private theorem split_retract_apply {A M : PModule.{u,0,u} k (Fin N)}
    (inc : A ⟶ M) (ret : M ⟶ A) (h : inc ≫ ret = 𝟙 A) (i : Fin N) (a : A.obj i) :
    (ret.app i).hom ((inc.app i).hom a) = a := by
  exact congrArg (fun g : A ⟶ A => (g.app i).hom a) h

private noncomputable def splitLinearEquiv {A M : PModule.{u,0,u} k (Fin N)}
    (inc : A ⟶ M) (ret : M ⟶ A) (h : inc ≫ ret = 𝟙 A) (i : Fin N) :
    M.obj i ≃ₗ[k] (A.obj i × LinearMap.ker (ret.app i).hom) where
  toFun x := ((ret.app i).hom x, ⟨x - (inc.app i).hom ((ret.app i).hom x), by
    change (ret.app i).hom (x - (inc.app i).hom ((ret.app i).hom x)) = 0
    rw [map_sub, split_retract_apply inc ret h, sub_self]⟩)
  invFun y := (inc.app i).hom y.1 + y.2.val
  left_inv x := by simp
  right_inv y := by
    apply Prod.ext
    · simp [split_retract_apply inc ret h]
    · apply Subtype.ext
      simp [split_retract_apply inc ret h]
  map_add' x y := by
    apply Prod.ext
    · simp
    · apply Subtype.ext
      change x + y - (inc.app i).hom ((ret.app i).hom (x + y)) =
        (x - (inc.app i).hom ((ret.app i).hom x)) +
        (y - (inc.app i).hom ((ret.app i).hom y))
      simp only [map_add]
      abel
  map_smul' a x := by
    apply Prod.ext
    · simp
    · apply Subtype.ext
      simp [smul_sub]

/-- A natural inclusion and retraction split a module into the image and the kernel.
The forward map sends `x` to `(ret x, x - inc (ret x))`. -/
noncomputable def splitIso {A M : PModule.{u,0,u} k (Fin N)}
    (inc : A ⟶ M) (ret : M ⟶ A) (h : inc ≫ ret = 𝟙 A) :
    M ≅ pointwiseProd A (splitComplement ret) :=
  NatIso.ofComponents (fun i => (splitLinearEquiv inc ret h i).toModuleIso) (by
    intro i j f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Prod.ext
    · exact natTrans_apply ret f x
    · apply Subtype.ext
      change (M.map f).hom x - (inc.app j).hom ((ret.app j).hom ((M.map f).hom x)) =
        (M.map f).hom (x - (inc.app i).hom ((ret.app i).hom x))
      rw [map_sub, natTrans_apply ret f x, natTrans_apply inc f])

/-- Each fiber of a split module has the sum of the image and kernel dimensions. -/
theorem finrank_split {A M : PModule.{u,0,u} k (Fin N)}
    [∀ i, FiniteDimensional k (M.obj i)] [∀ i, FiniteDimensional k (A.obj i)]
    (inc : A ⟶ M) (ret : M ⟶ A) (h : inc ≫ ret = 𝟙 A) (i : Fin N) :
    Module.finrank k (M.obj i) = Module.finrank k (A.obj i) +
      Module.finrank k ((splitComplement ret).obj i) := by
  rw [((splitIso inc ret h).app i).toLinearEquiv.finrank_eq]
  exact Module.finrank_prod

/-- The sum of dimensions in the split image and kernel is the original sum. -/
theorem totalDimension_split {A M : PModule.{u,0,u} k (Fin N)}
    [∀ i, FiniteDimensional k (M.obj i)] [∀ i, FiniteDimensional k (A.obj i)]
    (inc : A ⟶ M) (ret : M ⟶ A) (h : inc ≫ ret = 𝟙 A) :
    totalDimension M = totalDimension A + totalDimension (splitComplement ret) := by
  rw [totalDimension_eq_of_iso (splitIso inc ret h), totalDimension_pointwiseProd]

/-- A zero dimension sum forces every stage to be a zero vector space. -/
theorem subsingleton_of_totalDimension_zero (M : PModule.{u,0,u} k (Fin N))
    [∀ i, FiniteDimensional k (M.obj i)] (h : totalDimension M = 0) (i : Fin N) :
    Subsingleton (M.obj i) := by
  apply (Module.finrank_zero_iff (R := k) (M := M.obj i)).mp
  exact (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => Nat.zero_le _)).mp h i
    (Finset.mem_univ i)

/-- The direct natural isomorphism from a zero-dimensional module to the empty barcode. -/
noncomputable def zeroDimensionIso (M : PModule.{u,0,u} k (Fin N))
    [∀ i, FiniteDimensional k (M.obj i)] (h : totalDimension M = 0) :
    M ≅ barcodeModuleOfList (k := k) [] := by
  letI : ∀ i, Subsingleton (M.obj i) := subsingleton_of_totalDimension_zero M h
  letI (i : Fin N) : Subsingleton ((barcodeModuleOfList (k := k) []).obj i) :=
    ⟨fun x y => by funext t; exact Fin.elim0 t⟩
  refine NatIso.ofComponents
    (fun i => (LinearEquiv.ofSubsingleton (R := k) (M.obj i)
      ((barcodeModuleOfList (k := k) []).obj i)).toModuleIso) ?_
  intro i j f
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact Subsingleton.elim _ _

private noncomputable def barcodeConsLinearEquiv (I : FiniteInterval N)
    (xs : List (FiniteInterval N)) (i : Fin N) :
    ((intervalModule (k := k) I).obj i × (barcodeModuleOfList (k := k) xs).obj i) ≃ₗ[k]
      (barcodeModuleOfList (k := k) (I :: xs)).obj i where
  toFun x := Fin.cases x.1 (fun t => x.2 t)
  invFun y := (y 0, fun t => y t.succ)
  left_inv x := by
    apply Prod.ext
    · rfl
    · rfl
  right_inv y := by
    funext t
    refine Fin.cases ?_ (fun t => ?_) t <;> rfl
  map_add' x y := by
    funext t
    refine Fin.cases ?_ (fun t => ?_) t <;> rfl
  map_smul' a x := by
    funext t
    refine Fin.cases ?_ (fun t => ?_) t <;> rfl

/-- Prepending an interval is the pointwise product with that interval. -/
noncomputable def barcodeModuleOfListConsIso (I : FiniteInterval N)
    (xs : List (FiniteInterval N)) :
    pointwiseProd (intervalModule (k := k) I) (barcodeModuleOfList (k := k) xs) ≅
      barcodeModuleOfList (k := k) (I :: xs) :=
  NatIso.ofComponents (fun i => (barcodeConsLinearEquiv I xs i).toModuleIso) (by
    intro i j f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext t
    refine Fin.cases ?_ (fun t => ?_) t <;> rfl)

/-- A list barcode is naturally isomorphic to its multiset realization. -/
noncomputable def barcodeModuleOfListIso (xs : List (FiniteInterval N)) :
    barcodeModuleOfList (k := k) xs ≅ barcodeModule (k := k) (↑xs : Multiset _) := by
  apply barcodeEnumerationNatIso
  apply Multiset.coe_eq_coe.mp
  simp only [Multiset.coe_toList]

end TDA.Persistence
