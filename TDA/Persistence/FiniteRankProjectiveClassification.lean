import TDA.Persistence.FiniteHookDeflation
import TDA.Persistence.HookEndomorphisms
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Limits.FunctorCategory.BinaryBiproducts
import Mathlib.Algebra.Category.ModuleCat.Images
import Mathlib.RingTheory.Artinian.Module
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Data.Fintype.EquivFin

/-!
# Finite-poset rank-projective classification

Let \(k\) be a field and \(P\) a finite poset. For a pointwise finite-dimensional
persistence module on \(P\), each endomorphism admits a uniform Fitting
decomposition across all grades. For an indecomposable module, this gives the
invertible-or-nilpotent dichotomy for endomorphisms used by the ordinary
Krull--Schmidt argument.

`RankProjectiveHookTag` records a finite hook by a strict birth-death pair and
a principal-upset hook by its birth. `rankProjectiveHookModule` assigns each
tag its module. The theorem `rankProjective_iff_exists_canonical_subfamily`
states that a pointwise finite-dimensional module is rank-projective exactly
when it is isomorphic to a finite biproduct of selected occurrences from its
canonical finite-hook cover. The selected subfamily may be empty.

When \(P\) has decidable equality, `rankProjectiveHookSum_multiplicity_unique`
shows that isomorphic finite sums of tagged hooks have the same occurrence
count at every tag, including repeated tags and empty sums. It determines tag
multiplicities, not an ordering of summands or a choice of isomorphism.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence.FiniteRankProjectiveClassification

open CategoryTheory CategoryTheory.Limits

variable {k : Type u} [Field k] {P : Type} [PartialOrder P] [Fintype P]

private instance : HasFiniteBiproducts (PModule.{u,0,u} k P) :=
  HasFiniteBiproducts.of_hasFiniteProducts


/-- On a finite poset, one Fitting exponent works at every grade. -/
theorem exists_uniform_fitting_complement (X : PModule.{u,0,u} k P)
    (hX : ∀ p, FiniteDimensional k (X.obj p)) (f : End X) :
    ∃ n : ℕ, 0 < n ∧ ∀ p,
      IsCompl (LinearMap.ker ((f.app p).hom ^ n))
        (LinearMap.range ((f.app p).hom ^ n)) := by
  classical
  letI : ∀ p, FiniteDimensional k (X.obj p) := hX
  have hEventually (p : P) :
      ∀ᶠ n : ℕ in Filter.atTop,
        IsCompl (LinearMap.ker ((f.app p).hom ^ n))
          (LinearMap.range ((f.app p).hom ^ n)) := by
    exact ((f.app p).hom).eventually_isCompl_ker_pow_range_pow
  choose b hb using fun p => (Filter.eventually_atTop.mp (hEventually p))
  refine ⟨Finset.univ.sup b + 1, Nat.succ_pos _, ?_⟩
  intro p
  exact hb p (Finset.univ.sup b + 1)
    (le_trans (Finset.le_sup (Finset.mem_univ p)) (Nat.le_succ _))

omit [Fintype P] in
private theorem natTrans_apply {A B : PModule.{u,0,u} k P} (f : A ⟶ B)
    {p q : P} (hpq : p ⟶ q) (x : A.obj p) :
    (f.app q).hom ((A.map hpq).hom x) =
      (B.map hpq).hom ((f.app p).hom x) := by
  exact congrArg (fun g : A.obj p ⟶ B.obj q => g.hom x) (f.naturality hpq)

/-- The pointwise kernels of a natural endomorphism form a submodule diagram. -/
private def kernelSubmoduleDiagram {X : PModule.{u,0,u} k P} (f : End X) :
    PModule.{u,0,u} k P where
  obj p := ModuleCat.of k (LinearMap.ker (f.app p).hom)
  map {p q} hpq := ModuleCat.ofHom <|
    (((X.map hpq).hom.comp (LinearMap.ker (f.app p).hom).subtype).codRestrict
      (LinearMap.ker (f.app q).hom) (by
        intro x
        change (f.app q).hom ((X.map hpq).hom x.val) = 0
        rw [natTrans_apply f hpq x.val, x.property, map_zero]))
  map_id p := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change (X.map (𝟙 p)).hom x.val = x.val
    simp
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change (X.map (f ≫ g)).hom x.val = (X.map g).hom ((X.map f).hom x.val)
    simp

/-- The pointwise ranges of a natural endomorphism form a submodule diagram. -/
private def rangeSubmoduleDiagram {X : PModule.{u,0,u} k P} (f : End X) :
    PModule.{u,0,u} k P where
  obj p := ModuleCat.of k (LinearMap.range (f.app p).hom)
  map {p q} hpq := ModuleCat.ofHom <|
    (((X.map hpq).hom.comp (LinearMap.range (f.app p).hom).subtype).codRestrict
      (LinearMap.range (f.app q).hom) (by
        intro x
        obtain ⟨y, hy⟩ := x.property
        refine ⟨(X.map hpq).hom y, ?_⟩
        exact (natTrans_apply f hpq y).trans (congrArg (X.map hpq).hom hy)))
  map_id p := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change (X.map (𝟙 p)).hom x.val = x.val
    simp
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change (X.map (f ≫ g)).hom x.val = (X.map g).hom ((X.map f).hom x.val)
    simp

/-- The kernel subdiagram includes naturally into the original diagram. -/
private def kernelSubmoduleInclusion {X : PModule.{u,0,u} k P} (f : End X) :
    kernelSubmoduleDiagram f ⟶ X where
  app p := by
    change ModuleCat.of k (LinearMap.ker (f.app p).hom) ⟶ X.obj p
    exact ModuleCat.ofHom (LinearMap.ker (f.app p).hom).subtype
  naturality := by
    intro p q hpq
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl

private def splitKernelDiagram {M A : PModule.{u,0,u} k P} (f : M ⟶ A) :
    PModule.{u,0,u} k P where
  obj p := ModuleCat.of k (LinearMap.ker (f.app p).hom)
  map {p q} hpq := ModuleCat.ofHom <|
    (((M.map hpq).hom.comp (LinearMap.ker (f.app p).hom).subtype).codRestrict
      (LinearMap.ker (f.app q).hom) (by
        intro x
        change (f.app q).hom ((M.map hpq).hom x.val) = 0
        rw [natTrans_apply f hpq x.val, x.property, map_zero]))
  map_id p := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change (M.map (𝟙 p)).hom x.val = x.val
    simp
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change (M.map (f ≫ g)).hom x.val = (M.map g).hom ((M.map f).hom x.val)
    simp

private def splitKernelInclusion {M A : PModule.{u,0,u} k P} (f : M ⟶ A) :
    splitKernelDiagram f ⟶ M where
  app p := by
    change ModuleCat.of k (LinearMap.ker (f.app p).hom) ⟶ M.obj p
    exact ModuleCat.ofHom (LinearMap.ker (f.app p).hom).subtype
  naturality := by
    intro p q hpq
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl

/-- The range subdiagram includes naturally into the original diagram. -/
private def rangeSubmoduleInclusion {X : PModule.{u,0,u} k P} (f : End X) :
    rangeSubmoduleDiagram f ⟶ X where
  app p := by
    change ModuleCat.of k (LinearMap.range (f.app p).hom) ⟶ X.obj p
    exact ModuleCat.ofHom (LinearMap.range (f.app p).hom).subtype
  naturality := by
    intro p q hpq
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl

private abbrev pointwiseProduct (A B : PModule.{u,0,u} k P) : PModule.{u,0,u} k P := {
  obj p := ModuleCat.of k (A.obj p × B.obj p)
  map f := ModuleCat.ofHom ((A.map f).hom.prodMap (B.map f).hom)
  map_id p := by
    apply ModuleCat.hom_ext
    ext x <;> simp [LinearMap.prodMap]
  map_comp f g := by
    apply ModuleCat.hom_ext
    ext x <;> simp [LinearMap.prodMap, Functor.map_comp]
}

/-- The manually presented pointwise product agrees with the categorical
binary biproduct used by the functor category. -/
private noncomputable def pointwiseProductIsoPointwiseBiprod
    (A B : PModule.{u,0,u} k P) :
    pointwiseProduct A B ≅ (CategoryTheory.Limits.pointwiseBinaryBicone A B).pt :=
  NatIso.ofComponents (fun p => by
    change ModuleCat.of k (A.obj p × B.obj p) ≅ A.obj p ⊞ B.obj p
    exact (ModuleCat.biprodIsoProd (A.obj p) (B.obj p)).symm) (by
    intro p q hpq
    dsimp [pointwiseProduct, CategoryTheory.Limits.pointwiseBinaryBicone]
    apply biprod.hom_ext
    · rw [Category.assoc, ModuleCat.biprodIsoProd_inv_comp_fst,
        Category.assoc, biprod.map_fst, ← Category.assoc,
        ModuleCat.biprodIsoProd_inv_comp_fst]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      rintro ⟨x, y⟩
      rfl
    · rw [Category.assoc, ModuleCat.biprodIsoProd_inv_comp_snd,
        Category.assoc, biprod.map_snd, ← Category.assoc,
        ModuleCat.biprodIsoProd_inv_comp_snd]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      rintro ⟨x, y⟩
      rfl)

private noncomputable def pointwiseProductIsoBiprod
    (A B : PModule.{u,0,u} k P) : pointwiseProduct A B ≅ A ⊞ B :=
  (pointwiseProductIsoPointwiseBiprod A B).trans
    (biprod.uniqueUpToIso A B (CategoryTheory.Limits.pointwiseBinaryBicone.isBilimit A B))

/-- The sum of the kernel and image subdiagrams maps to the original diagram. -/
private def fittingSumMap {X : PModule.{u,0,u} k P} (f : End X) :
    pointwiseProduct (kernelSubmoduleDiagram f) (rangeSubmoduleDiagram f) ⟶ X where
  app p := ModuleCat.ofHom <| ((kernelSubmoduleInclusion f).app p).hom.coprod
    ((rangeSubmoduleInclusion f).app p).hom
  naturality := by
    intro p q hpq
    dsimp [pointwiseProduct]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    rcases z with ⟨x, y⟩
    have hkerx := congrArg (fun g => g.hom x)
      ((kernelSubmoduleInclusion f).naturality hpq)
    have hrangey := congrArg (fun g => g.hom y)
      ((rangeSubmoduleInclusion f).naturality hpq)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hkerx hrangey
    change ((kernelSubmoduleInclusion f).app q).hom
        (((kernelSubmoduleDiagram f).map hpq).hom x) +
      ((rangeSubmoduleInclusion f).app q).hom
        (((rangeSubmoduleDiagram f).map hpq).hom y) =
      (X.map hpq).hom (((kernelSubmoduleInclusion f).app p).hom x +
        ((rangeSubmoduleInclusion f).app p).hom y)
    rw [hkerx, hrangey, map_add]

/-- A pointwise Fitting complement splits the persistence module into its
kernel and image subdiagrams. -/
private noncomputable def fittingDecompositionIso {X : PModule.{u,0,u} k P}
    (f : End X) (hfit : ∀ p,
      IsCompl (LinearMap.ker (f.app p).hom) (LinearMap.range (f.app p).hom)) :
    X ≅ pointwiseProduct (kernelSubmoduleDiagram f) (rangeSubmoduleDiagram f) := by
  let s := fittingSumMap f
  have hs (p : P) : IsIso (s.app p) := by
    let e := (Submodule.prodEquivOfIsCompl _ _ (hfit p)).toModuleIso
    have heq : s.app p = e.hom := by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      rintro ⟨x, y⟩
      rfl
    rw [heq]
    exact e.isIso_hom
  letI (p : P) : IsIso (s.app p) := hs p
  letI : IsIso s := NatIso.isIso_of_isIso_app s
  exact (asIso s).symm

private noncomputable def fittingBiproductIso {X : PModule.{u,0,u} k P}
    (f : End X) (hfit : ∀ p,
      IsCompl (LinearMap.ker (f.app p).hom) (LinearMap.range (f.app p).hom)) :
    X ≅ kernelSubmoduleDiagram f ⊞ rangeSubmoduleDiagram f :=
  (fittingDecompositionIso f hfit).trans
    (pointwiseProductIsoBiprod (kernelSubmoduleDiagram f) (rangeSubmoduleDiagram f))

private theorem split_apply {A M : PModule.{u,0,u} k P}
    (inc : A ⟶ M) (ret : M ⟶ A) (h : inc ≫ ret = 𝟙 A) (p : P) (a : A.obj p) :
    (ret.app p).hom ((inc.app p).hom a) = a :=
  congrArg (fun g : End A => (g.app p).hom a) h

private noncomputable def splitLinearEquiv {A M : PModule.{u,0,u} k P}
    (inc : A ⟶ M) (ret : M ⟶ A) (h : inc ≫ ret = 𝟙 A) (p : P) :
    M.obj p ≃ₗ[k] (A.obj p × LinearMap.ker (ret.app p).hom) where
  toFun x := ((ret.app p).hom x, ⟨x - (inc.app p).hom ((ret.app p).hom x), by
    change (ret.app p).hom (x - (inc.app p).hom ((ret.app p).hom x)) = 0
    rw [map_sub, split_apply inc ret h p, sub_self]⟩)
  invFun y := (inc.app p).hom y.1 + y.2.val
  left_inv x := by simp
  right_inv y := by
    apply Prod.ext
    · simp [split_apply inc ret h p]
    · apply Subtype.ext
      simp [split_apply inc ret h p]
  map_add' x y := by
    apply Prod.ext
    · simp
    · apply Subtype.ext
      change x + y - (inc.app p).hom ((ret.app p).hom (x + y)) =
        (x - (inc.app p).hom ((ret.app p).hom x)) +
        (y - (inc.app p).hom ((ret.app p).hom y))
      simp only [map_add]
      abel
  map_smul' a x := by
    apply Prod.ext
    · simp
    · apply Subtype.ext
      simp [smul_sub]

/-- A split retraction decomposes its domain into its image and the kernel. -/
private noncomputable def splitBiproductIso {A M : PModule.{u,0,u} k P}
    (inc : A ⟶ M) (ret : M ⟶ A) (h : inc ≫ ret = 𝟙 A) :
    M ≅ A ⊞ splitKernelDiagram ret :=
  (NatIso.ofComponents (fun p => (splitLinearEquiv inc ret h p).toModuleIso) (by
    intro p q hpq
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Prod.ext
    · exact natTrans_apply ret hpq x
    · apply Subtype.ext
      change (M.map hpq).hom x -
          (inc.app q).hom ((ret.app q).hom ((M.map hpq).hom x)) =
        (M.map hpq).hom (x - (inc.app p).hom ((ret.app p).hom x))
      rw [map_sub, natTrans_apply ret hpq x, natTrans_apply inc hpq])
    ).trans (pointwiseProductIsoBiprod A (splitKernelDiagram ret))

private theorem isZero_obj_of_isZero {A : PModule.{u,0,u} k P}
    (hA : IsZero A) (p : P) : IsZero (A.obj p) := by
  apply (IsZero.iff_id_eq_zero _).mpr
  simpa using congrArg (fun g : End A => g.app p)
    ((IsZero.iff_id_eq_zero A).mp hA)

private theorem indecomposable_retract_iso {A B : PModule.{u,0,u} k P}
    (hA : Indecomposable A) (hB : Indecomposable B)
    (inc : A ⟶ B) (ret : B ⟶ A) (h : inc ≫ ret = 𝟙 A) : Nonempty (A ≅ B) := by
  let K := splitKernelDiagram ret
  have hsplit : B ≅ A ⊞ K := splitBiproductIso inc ret h
  rcases hB.2 A K hsplit with hA0 | hK
  · exact (hA.1 hA0).elim
  · have hKfiber (p : P) : IsZero (K.obj p) := isZero_obj_of_isZero hK p
    have hkerbot (p : P) : LinearMap.ker (ret.app p).hom = ⊥ := by
      have hs : Subsingleton (LinearMap.ker (ret.app p).hom) := by
        simpa [K, splitKernelDiagram] using
          (ModuleCat.isZero_iff_subsingleton).mp (hKfiber p)
      exact (Submodule.eq_bot_iff _).2 (by
        intro x hx
        exact congrArg Subtype.val (hs.elim ⟨x, hx⟩ 0))
    have hInjective (p : P) : Function.Injective (ret.app p).hom :=
      (LinearMap.ker_eq_bot).mp (hkerbot p)
    have hSurjective (p : P) : Function.Surjective (ret.app p).hom := by
      intro a
      exact ⟨(inc.app p).hom a, split_apply inc ret h p a⟩
    have hIso (p : P) : IsIso (ret.app p) :=
      (ConcreteCategory.isIso_iff_bijective (ret.app p)).mpr
        ⟨hInjective p, hSurjective p⟩
    letI (p : P) : IsIso (ret.app p) := hIso p
    letI : IsIso ret := NatIso.isIso_of_isIso_app ret
    exact ⟨(asIso ret).symm⟩

private theorem natTrans_app_hom_pow {X : PModule.{u,0,u} k P}
    (f : End X) (n : ℕ) (p : P) :
    ((f ^ n).app p).hom = ((f.app p).hom ^ n) := by
  induction n with
  | zero => simp [Module.End.one_eq_id]
  | succ n ih =>
      simp [pow_succ, End.mul_def, NatTrans.comp_app, ModuleCat.hom_comp,
        Module.End.mul_eq_comp, ih]

/-- On an indecomposable pointwise finite-dimensional module, every endomorphism
is either invertible or nilpotent. This is the Fitting dichotomy needed for
finite cancellation. -/
theorem indecomposable_endomorphism_dichotomy {X : PModule.{u,0,u} k P}
    (hX : Indecomposable X) (hfd : ∀ p, FiniteDimensional k (X.obj p))
    (f : End X) : IsIso f ∨ ∃ n : ℕ, f ^ n = 0 := by
  classical
  letI : ∀ p, FiniteDimensional k (X.obj p) := hfd
  obtain ⟨n, hn, hfit⟩ := exists_uniform_fitting_complement X hfd f
  let g : End X := f ^ n
  have hfitg (p : P) : IsCompl (LinearMap.ker (g.app p).hom)
      (LinearMap.range (g.app p).hom) := by
    simpa [g, natTrans_app_hom_pow] using hfit p
  let K := kernelSubmoduleDiagram g
  let I := rangeSubmoduleDiagram g
  have hdec : X ≅ K ⊞ I := fittingBiproductIso g hfitg
  rcases hX.2 K I hdec with hK | hI
  · have hKfiber (p : P) : IsZero (K.obj p) := isZero_obj_of_isZero hK p
    have hkerbot (p : P) : LinearMap.ker (g.app p).hom = ⊥ := by
      have hs : Subsingleton (LinearMap.ker (g.app p).hom) := by
        simpa [K, kernelSubmoduleDiagram] using
          (ModuleCat.isZero_iff_subsingleton).mp (hKfiber p)
      exact (Submodule.eq_bot_iff _).2 (by
      intro x hx
      exact congrArg Subtype.val (hs.elim ⟨x, hx⟩ 0))
    have hgInjective (p : P) : Function.Injective (g.app p).hom :=
      (LinearMap.ker_eq_bot).mp (by simpa [g, natTrans_app_hom_pow] using hkerbot p)
    have hInjective (p : P) : Function.Injective (f.app p).hom := by
      rcases n with _ | n'
      · exact (Nat.not_lt_zero _ hn).elim
      · intro x y hxy
        apply hgInjective p
        simp [g, pow_succ, hxy]
    have hIso (p : P) : IsIso (f.app p) :=
      (ConcreteCategory.isIso_iff_bijective (f.app p)).mpr
        ⟨hInjective p, LinearMap.surjective_of_injective (hInjective p)⟩
    letI (p : P) : IsIso (f.app p) := hIso p
    letI : IsIso f := NatIso.isIso_of_isIso_app f
    exact Or.inl inferInstance
  · have hIfiber (p : P) : IsZero (I.obj p) := isZero_obj_of_isZero hI p
    have hrangebot (p : P) : LinearMap.range (g.app p).hom = ⊥ := by
      have hs : Subsingleton (LinearMap.range (g.app p).hom) := by
        simpa [I, rangeSubmoduleDiagram] using
          (ModuleCat.isZero_iff_subsingleton).mp (hIfiber p)
      exact (Submodule.eq_bot_iff _).2 fun x hx =>
        congrArg Subtype.val (hs.elim ⟨x, hx⟩ 0)
    have happ (p : P) : (g.app p).hom = 0 :=
      (LinearMap.range_eq_bot).mp (hrangebot p)
    have hg0 : g = 0 := by
      apply NatTrans.ext
      funext p
      exact ModuleCat.hom_ext (happ p)
    exact Or.inr ⟨n, by simpa [g] using hg0⟩

/-- A sum of two endomorphisms of an indecomposable cannot be the identity
unless at least one summand is invertible. -/
theorem indecomposable_sum_eq_one_has_isIso {X : PModule.{u,0,u} k P}
    (hX : Indecomposable X) (hfd : ∀ p, FiniteDimensional k (X.obj p))
    (a b : End X) (hab : a + b = 1) : IsIso a ∨ IsIso b := by
  rcases indecomposable_endomorphism_dichotomy hX hfd a with ha | ⟨n, hn⟩
  · exact Or.inl ha
  · have hnil : IsNilpotent a := ⟨n, hn⟩
    have hb : b = 1 - a := by
      calc
        b = a + b - a := by simp
        _ = 1 - a := by rw [hab]
    have hunit : IsUnit b := by
      rw [hb]
      exact hnil.isUnit_one_sub
    exact Or.inr (CategoryTheory.isUnit_iff_isIso b |>.mp hunit)

private theorem indecomposable_sum_isIso {X : PModule.{u,0,u} k P}
    (hX : Indecomposable X) (hfd : ∀ p, FiniteDimensional k (X.obj p))
    (a b : End X) (hab : IsIso (a + b)) : IsIso a ∨ IsIso b := by
  letI : IsIso (a + b) := hab
  let c : End X := inv (a + b)
  have hsum : c * a + c * b = 𝟙 X := by
    calc
      c * a + c * b = c * (a + b) := by rw [← mul_add]
      _ = (a + b) ≫ c := by rw [CategoryTheory.End.mul_def]
      _ = 𝟙 X := by simp [c]
  rcases indecomposable_sum_eq_one_has_isIso hX hfd (c * a) (c * b) hsum with hca | hcb
  · have hc : IsUnit c := (CategoryTheory.isUnit_iff_isIso c).mpr (by dsimp [c]; infer_instance)
    have hcaUnit : IsUnit (c * a) := (CategoryTheory.isUnit_iff_isIso (c * a)).mpr hca
    exact Or.inl <| (CategoryTheory.isUnit_iff_isIso a).mp (hc.mul_left_iff.mp hcaUnit)
  · have hc : IsUnit c := (CategoryTheory.isUnit_iff_isIso c).mpr (by dsimp [c]; infer_instance)
    have hcbUnit : IsUnit (c * b) := (CategoryTheory.isUnit_iff_isIso (c * b)).mpr hcb
    exact Or.inr <| (CategoryTheory.isUnit_iff_isIso b).mp (hc.mul_left_iff.mp hcbUnit)

private theorem indecomposable_finset_sum_isIso {X : PModule.{u,0,u} k P}
    (hX : Indecomposable X) (hfd : ∀ p, FiniteDimensional k (X.obj p))
    {ι : Type*} (s : Finset ι) (a : ι → End X)
    (hsum : IsIso (∑ i ∈ s, a i)) : ∃ i ∈ s, IsIso (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      have hzero : IsIso (0 : End X) := by simpa using hsum
      letI : IsIso (0 : End X) := hzero
      have hid : (𝟙 X : End X) = 0 := by
        calc
          𝟙 X = (0 : End X) ≫ inv (0 : End X) :=
            (IsIso.hom_inv_id (0 : End X)).symm
          _ = 0 := zero_comp
      exact (hX.1 ((IsZero.iff_id_eq_zero X).mpr hid)).elim
  | @insert i s hi ih =>
      have hsum' : IsIso (a i + ∑ j ∈ s, a j) := by
        simpa [Finset.sum_insert, hi] using hsum
      rcases indecomposable_sum_isIso hX hfd (a i) (∑ j ∈ s, a j) hsum' with hiIso | hsIso
      · exact ⟨i, Finset.mem_insert_self _ _, hiIso⟩
      · rcases ih hsIso with ⟨j, hjs, hjIso⟩
        exact ⟨j, Finset.mem_insert_of_mem hjs, hjIso⟩

/-- An indecomposable retract of a finite biproduct of indecomposables is
isomorphic to one of its summands. -/
theorem indecomposable_biproduct_summand {X : PModule.{u,0,u} k P}
    {ι : Type} [Fintype ι] (F : ι → PModule.{u,0,u} k P)
    (hX : Indecomposable X) (hfd : ∀ p, FiniteDimensional k (X.obj p))
    (hF : ∀ i, Indecomposable (F i))
    (inc : X ⟶ ⨁ F) (ret : ⨁ F ⟶ X) (hret : inc ≫ ret = 𝟙 X) :
    ∃ i, Nonempty (X ≅ F i) := by
  classical
  let a (i : ι) : End X :=
    (inc ≫ biproduct.π F i) ≫ (biproduct.ι F i ≫ ret)
  have hsum : ∑ i, a i = 𝟙 X := by
    calc
      ∑ i, a i = inc ≫ (∑ i, biproduct.π F i ≫ biproduct.ι F i) ≫ ret := by
        calc
          ∑ i, a i = ∑ i, inc ≫ biproduct.π F i ≫ biproduct.ι F i ≫ ret := by
            apply Finset.sum_congr rfl
            intro i hi
            simp [a, Category.assoc]
          _ = inc ≫ (∑ i, biproduct.π F i ≫ biproduct.ι F i) ≫ ret := by
            symm
            rw [← Category.assoc, Preadditive.comp_sum, Preadditive.sum_comp]
            simp only [Category.assoc]
      _ = inc ≫ 𝟙 (⨁ F) ≫ ret := by
        have htotal : (∑ i : ι, biproduct.π F i ≫ biproduct.ι F i) =
            𝟙 (⨁ F) := biproduct.total (f := F)
        exact congrArg (fun t : End (⨁ F) => inc ≫ t ≫ ret) htotal
      _ = 𝟙 X := by simpa using hret
  have hsumIso : IsIso (∑ i, a i) := by rw [hsum]; infer_instance
  obtain ⟨i, -, hai⟩ := indecomposable_finset_sum_isIso hX hfd Finset.univ a hsumIso
  let α : X ⟶ F i := inc ≫ biproduct.π F i
  let β : F i ⟶ X := biproduct.ι F i ≫ ret
  have hab : α ≫ β = a i := rfl
  letI : IsIso (α ≫ β) := by rw [hab]; exact hai
  let retIso : F i ⟶ X := β ≫ inv (α ≫ β)
  have hsplit : α ≫ retIso = 𝟙 X := by
    dsimp [retIso]
    rw [← Category.assoc]
    exact IsIso.hom_inv_id (α ≫ β)
  exact ⟨i, indecomposable_retract_iso hX (hF i) α retIso hsplit⟩

private theorem biproduct_inclusions_linearIndependent
    {ι J : Type} [Fintype ι] [Fintype J]
    (F : ι → PModule.{u,0,u} k P) (j : J → ι) (hj : Function.Injective j)
    (p : P) (x : ∀ t, (F (j t)).obj p) (hx : ∀ t, x t ≠ 0) :
    LinearIndependent k (fun t =>
      ((biproduct.ι F (j t)).app p).hom (x t)) := by
  classical
  rw [Fintype.linearIndependent_iffₛ]
  intro f g h
  intro t
  have hcoord := congrArg (fun z => ((biproduct.π F (j t)).app p).hom z) h
  have hdiag :
      ((biproduct.π F (j t)).app p).hom
          (((biproduct.ι F (j t)).app p).hom (x t)) = x t := by
    change ((biproduct.ι F (j t) ≫ biproduct.π F (j t)).app p).hom (x t) = x t
    rw [biproduct.ι_π_self]
    simp
  have hproject (c : J → k) :
      ((biproduct.π F (j t)).app p).hom
          (∑ s, c s • ((biproduct.ι F (j s)).app p).hom (x s)) = c t • x t := by
    rw [map_sum, Finset.sum_eq_single t]
    · simp [hdiag]
    · intro s hs hst
      have hne : j s ≠ j t := fun hEq => hst (hj hEq)
      have hz :
          ((biproduct.π F (j t)).app p).hom
            (((biproduct.ι F (j s)).app p).hom (x s)) = 0 := by
        change ((biproduct.ι F (j s) ≫ biproduct.π F (j t)).app p).hom (x s) = 0
        rw [biproduct.ι_π_ne F hne]
        simp
      simp [hz]
    · intro ht
      exact (ht (Finset.mem_univ t)).elim
  have hmul : f t • x t = g t • x t := by
    rw [← hproject f, ← hproject g]
    exact hcoord
  exact smul_left_injective k (hx t) hmul

private theorem sum_biprod_left {ι κ : Type} [Fintype ι] [Fintype κ]
    (F : ι → PModule.{u,0,u} k P) (G : κ → PModule.{u,0,u} k P) :
    (∑ i, (biprod.fst (X := ⨁ F) (Y := ⨁ G) ≫ biproduct.π F i) ≫
        (biproduct.ι F i ≫ biprod.inl (X := ⨁ F) (Y := ⨁ G))) =
      biprod.fst (X := ⨁ F) (Y := ⨁ G) ≫
        (∑ i, biproduct.π F i ≫ biproduct.ι F i) ≫
          biprod.inl (X := ⨁ F) (Y := ⨁ G) := by
  symm
  rw [← Category.assoc, Preadditive.comp_sum, Preadditive.sum_comp]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Category.assoc]

private theorem sum_biprod_right {ι κ : Type} [Fintype ι] [Fintype κ]
    (F : ι → PModule.{u,0,u} k P) (G : κ → PModule.{u,0,u} k P) :
    (∑ j, (biprod.snd (X := ⨁ F) (Y := ⨁ G) ≫ biproduct.π G j) ≫
        (biproduct.ι G j ≫ biprod.inr (X := ⨁ F) (Y := ⨁ G))) =
      biprod.snd (X := ⨁ F) (Y := ⨁ G) ≫
        (∑ j, biproduct.π G j ≫ biproduct.ι G j) ≫
          biprod.inr (X := ⨁ F) (Y := ⨁ G) := by
  symm
  rw [← Category.assoc, Preadditive.comp_sum, Preadditive.sum_comp]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Category.assoc]

private theorem sum_biprod_right_obj (X : PModule.{u,0,u} k P)
    {κ : Type} [Fintype κ] (G : κ → PModule.{u,0,u} k P) :
    (∑ j, (biprod.snd (X := X) (Y := ⨁ G) ≫ biproduct.π G j) ≫
        (biproduct.ι G j ≫ biprod.inr (X := X) (Y := ⨁ G))) =
      biprod.snd (X := X) (Y := ⨁ G) ≫
        (∑ j, biproduct.π G j ≫ biproduct.ι G j) ≫
          biprod.inr (X := X) (Y := ⨁ G) := by
  symm
  rw [← Category.assoc, Preadditive.comp_sum, Preadditive.sum_comp]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Category.assoc]

/-- The biproduct of a disjoint union of two finite families is the binary
biproduct of their categorical biproducts. -/
private noncomputable def biproduct_sum_iso {ι κ : Type} [Fintype ι] [Fintype κ]
    (F : ι → PModule.{u,0,u} k P) (G : κ → PModule.{u,0,u} k P) :
    (⨁ F) ⊞ (⨁ G) ≅ ⨁ Sum.elim F G := by
  classical
  let H : Sum ι κ → PModule.{u,0,u} k P := Sum.elim F G
  let b : CategoryTheory.Limits.Bicone H := {
    pt := (⨁ F) ⊞ (⨁ G)
    π := fun s => by
      cases s with
      | inl i => exact biprod.fst (X := ⨁ F) (Y := ⨁ G) ≫ biproduct.π F i
      | inr j => exact biprod.snd (X := ⨁ F) (Y := ⨁ G) ≫ biproduct.π G j
    ι := fun s => by
      cases s with
      | inl i => exact biproduct.ι F i ≫ biprod.inl (X := ⨁ F) (Y := ⨁ G)
      | inr j => exact biproduct.ι G j ≫ biprod.inr (X := ⨁ F) (Y := ⨁ G)
    ι_π := by
      intro s t
      cases s with
      | inl i =>
        cases t with
        | inl j =>
          by_cases h : i = j
          · subst j
            simp [H, Category.assoc, biprod.inl_fst, biprod.inl_snd,
              biprod.inr_fst, biprod.inr_snd, biproduct.ι_π]
            simpa [H] using (eqToHom_refl (H (Sum.inl i))
              (congrArg H (show Sum.inl i = Sum.inl i from rfl))).symm
          · have hs : (Sum.inl i : Sum ι κ) ≠ Sum.inl j :=
                fun hs => h (Sum.inl.inj hs)
            simp [H, Category.assoc, biprod.inl_fst, biprod.inl_snd,
              biprod.inr_fst, biprod.inr_snd, biproduct.ι_π, h, hs] <;> rfl
        | inr j =>
            simp [H, Category.assoc, biprod.inl_fst, biprod.inl_snd,
              biprod.inr_fst, biprod.inr_snd, biproduct.ι_π] <;> rfl
      | inr i =>
        cases t with
        | inl j =>
            simp [H, Category.assoc, biprod.inl_fst, biprod.inl_snd,
              biprod.inr_fst, biprod.inr_snd, biproduct.ι_π] <;> rfl
        | inr j =>
          by_cases h : i = j
          · subst j
            simp [H, Category.assoc, biprod.inl_fst, biprod.inl_snd,
              biprod.inr_fst, biprod.inr_snd, biproduct.ι_π]
            simpa [H] using (eqToHom_refl (H (Sum.inr i))
              (congrArg H (show Sum.inr i = Sum.inr i from rfl))).symm
          · have hs : (Sum.inr i : Sum ι κ) ≠ Sum.inr j :=
                fun hs => h (Sum.inr.inj hs)
            simp [H, Category.assoc, biprod.inl_fst, biprod.inl_snd,
              biprod.inr_fst, biprod.inr_snd, biproduct.ι_π, h, hs] <;> rfl
  }
  have htotal : ∑ s : Sum ι κ, b.π s ≫ b.ι s = 𝟙 b.pt := by
    rw [Fintype.sum_sum_type]
    simp only [b, H]
    change
      (∑ i, (biprod.fst (X := ⨁ F) (Y := ⨁ G) ≫ biproduct.π F i) ≫
        (biproduct.ι F i ≫ biprod.inl (X := ⨁ F) (Y := ⨁ G))) +
      (∑ j, (biprod.snd (X := ⨁ F) (Y := ⨁ G) ≫ biproduct.π G j) ≫
        (biproduct.ι G j ≫ biprod.inr (X := ⨁ F) (Y := ⨁ G))) = 𝟙 _
    rw [sum_biprod_left F G, sum_biprod_right F G,
      biproduct.total, biproduct.total]
    simp
  exact biproduct.uniqueUpToIso H (isBilimitOfTotal b htotal)

/-- Split the first term of a finite biproduct. -/
private noncomputable def biproduct_split_fin_succ {n : ℕ}
    (F : Fin (n + 1) → PModule.{u,0,u} k P) :
    F 0 ⊞ (⨁ fun i : Fin n => F i.succ) ≅ ⨁ F := by
  classical
  let tail : Fin n → PModule.{u,0,u} k P := fun i => F i.succ
  let b : CategoryTheory.Limits.Bicone F := {
    pt := F 0 ⊞ ⨁ tail
    π := Fin.cases biprod.fst (fun i => biprod.snd ≫ biproduct.π tail i)
    ι := Fin.cases biprod.inl
      (fun i => biproduct.ι tail i ≫ biprod.inr)
    ι_π := by
      intro i j
      refine Fin.cases ?_ (fun i => ?_) i
      · refine Fin.cases ?_ (fun j => ?_) j
        · simp [Category.assoc]
        · simp [Category.assoc] <;> intro h <;> cases h
      · refine Fin.cases ?_ (fun j => ?_) j
        · simp [Category.assoc]
        · by_cases h : i = j
          · subst j
            simp [tail, Category.assoc, biproduct.ι_π]
          · simp [tail, Category.assoc, h, biproduct.ι_π]
  }
  have htotal : ∑ j : Fin (n + 1), b.π j ≫ b.ι j = 𝟙 b.pt := by
    rw [Fin.sum_univ_succ]
    change biprod.fst ≫ biprod.inl +
      ∑ i : Fin n, (biprod.snd ≫ biproduct.π tail i) ≫
        (biproduct.ι tail i ≫ biprod.inr) = 𝟙 _
    rw [sum_biprod_right_obj (F 0) tail]
    rw [biproduct.total]
    exact biprod.total
  exact biproduct.uniqueUpToIso F (isBilimitOfTotal b htotal)

private theorem biproduct_split_fin_succ_inl_hom {n : ℕ}
    (F : Fin (n + 1) → PModule.{u,0,u} k P) :
    biprod.inl ≫ (biproduct_split_fin_succ F).hom = biproduct.ι F 0 := by
  apply biproduct.hom_ext
  intro j
  refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [biproduct_split_fin_succ, biproduct.uniqueUpToIso,
      Category.assoc, biproduct.lift_π,
      biproduct.ι_π_ne _ (Fin.succ_ne_zero _).symm]

private theorem biproduct_split_fin_succ_inv_fst {n : ℕ}
    (F : Fin (n + 1) → PModule.{u,0,u} k P) :
    (biproduct_split_fin_succ F).inv ≫ biprod.fst = biproduct.π F 0 := by
  apply biproduct.hom_ext'
  intro i
  refine Fin.cases ?_ (fun i => ?_) i <;>
    simp [biproduct_split_fin_succ, biproduct.uniqueUpToIso,
      Category.assoc, biproduct.ι_desc,
      biproduct.ι_π_ne _ (Fin.succ_ne_zero _).symm]

private noncomputable def totalFiberDimension (M : PModule.{u,0,u} k P) : ℕ :=
  ∑ p, Module.finrank k (M.obj p)

private theorem totalFiberDimension_eq_of_iso {M N : PModule.{u,0,u} k P}
    (e : M ≅ N) : totalFiberDimension M = totalFiberDimension N := by
  unfold totalFiberDimension
  apply Finset.sum_congr rfl
  intro p hp
  exact (e.app p).toLinearEquiv.finrank_eq

private theorem totalFiberDimension_pointwiseProduct (M N : PModule.{u,0,u} k P)
    [∀ p, FiniteDimensional k (M.obj p)] [∀ p, FiniteDimensional k (N.obj p)] :
    totalFiberDimension (pointwiseProduct M N) =
      totalFiberDimension M + totalFiberDimension N := by
  unfold totalFiberDimension
  change (∑ p, Module.finrank k (M.obj p × N.obj p)) = _
  simp_rw [Module.finrank_prod]
  exact Finset.sum_add_distrib

private theorem totalFiberDimension_biprod (M N : PModule.{u,0,u} k P)
    [∀ p, FiniteDimensional k (M.obj p)] [∀ p, FiniteDimensional k (N.obj p)] :
    totalFiberDimension (M ⊞ N) = totalFiberDimension M + totalFiberDimension N := by
  let e := pointwiseProductIsoBiprod M N
  exact (totalFiberDimension_eq_of_iso e).symm.trans
    (totalFiberDimension_pointwiseProduct M N)

private theorem totalFiberDimension_pos_of_not_isZero (M : PModule.{u,0,u} k P)
    [∀ p, FiniteDimensional k (M.obj p)] (hM : ¬ IsZero M) :
    0 < totalFiberDimension M := by
  by_contra hpos
  have hzero : totalFiberDimension M = 0 := Nat.eq_zero_of_not_pos hpos
  have hfiber (p : P) : Subsingleton (M.obj p) := by
    apply (Module.finrank_zero_iff (R := k) (M := M.obj p)).mp
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => Nat.zero_le _)).mp hzero p
      (Finset.mem_univ p)
  apply hM
  apply (IsZero.iff_id_eq_zero M).mpr
  ext p x
  exact (hfiber p).elim _ _

private theorem finiteDimensional_of_biprod_factor {A B M : PModule.{u,0,u} k P}
    (e : M ≅ A ⊞ B) (hM : ∀ p, FiniteDimensional k (M.obj p)) :
    (∀ p, FiniteDimensional k (A.obj p)) ∧ ∀ p, FiniteDimensional k (B.obj p) := by
  constructor
  · intro p
    letI : FiniteDimensional k ((A ⊞ B).obj p) := (e.app p).toLinearEquiv.finiteDimensional
    exact FiniteDimensional.of_injective ((biprod.inl (X := A) (Y := B)).app p).hom
      ((ModuleCat.mono_iff_injective _).mp inferInstance)
  · intro p
    letI : FiniteDimensional k ((A ⊞ B).obj p) := (e.app p).toLinearEquiv.finiteDimensional
    exact FiniteDimensional.of_injective ((biprod.inr (X := A) (Y := B)).app p).hom
      ((ModuleCat.mono_iff_injective _).mp inferInstance)

private theorem exists_finite_indecomposable_decomposition
    (M : PModule.{u,0,u} k P) (hM : ∀ p, FiniteDimensional k (M.obj p)) :
    ∃ n : ℕ, ∃ F : Fin n → PModule.{u,0,u} k P,
      (∀ i, Indecomposable (F i)) ∧ Nonempty (M ≅ ⨁ F) := by
  classical
  letI : ∀ p, FiniteDimensional k (M.obj p) := hM
  have aux : ∀ n (X : PModule.{u,0,u} k P), totalFiberDimension X = n →
      (∀ p, FiniteDimensional k (X.obj p)) →
        ∃ m : ℕ, ∃ F : Fin m → PModule.{u,0,u} k P,
          (∀ i, Indecomposable (F i)) ∧ Nonempty (X ≅ ⨁ F) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro X hdim hfd
      letI : ∀ p, FiniteDimensional k (X.obj p) := hfd
      by_cases hXzero : IsZero X
      · let F : Fin 0 → PModule.{u,0,u} k P := Fin.elim0
        have hsumzero : IsZero (⨁ F) := by
          apply (IsZero.iff_id_eq_zero _).mpr
          have htotal : (∑ i : Fin 0, biproduct.π F i ≫ biproduct.ι F i) =
              𝟙 (⨁ F) := biproduct.total (f := F)
          simpa using htotal.symm
        refine ⟨0, F, ?_, ⟨hXzero.iso hsumzero⟩⟩
        intro i
        exact Fin.elim0 i
      · by_cases hXindecomp : Indecomposable X
        · let F : Fin 1 → PModule.{u,0,u} k P := fun _ => X
          refine ⟨1, F, ?_, ⟨(biproductUniqueIso F).symm⟩⟩
          intro i
          exact hXindecomp
        · have hdecompose : ¬ ∀ A B, (X ≅ A ⊞ B) → IsZero A ∨ IsZero B := by
            intro h
            exact hXindecomp ⟨hXzero, h⟩
          push_neg at hdecompose
          rcases hdecompose with ⟨A, B, e, hAnz, hBnz⟩
          obtain ⟨hfdA, hfdB⟩ := finiteDimensional_of_biprod_factor e hfd
          letI : ∀ p, FiniteDimensional k (A.obj p) := hfdA
          letI : ∀ p, FiniteDimensional k (B.obj p) := hfdB
          have hAdim : totalFiberDimension A < n := by
            calc
              totalFiberDimension A < totalFiberDimension A + totalFiberDimension B :=
                Nat.lt_add_of_pos_right (totalFiberDimension_pos_of_not_isZero B hBnz)
              _ = totalFiberDimension (A ⊞ B) := (totalFiberDimension_biprod A B).symm
              _ = totalFiberDimension X := (totalFiberDimension_eq_of_iso e).symm
              _ = n := hdim
          have hBdim : totalFiberDimension B < n := by
            calc
              totalFiberDimension B < totalFiberDimension A + totalFiberDimension B :=
                Nat.lt_add_of_pos_left (totalFiberDimension_pos_of_not_isZero A hAnz)
              _ = totalFiberDimension (A ⊞ B) := (totalFiberDimension_biprod A B).symm
              _ = totalFiberDimension X := (totalFiberDimension_eq_of_iso e).symm
              _ = n := hdim
          obtain ⟨nA, FA, hFA, ⟨eA⟩⟩ := ih (totalFiberDimension A) hAdim A rfl hfdA
          obtain ⟨nB, FB, hFB, ⟨eB⟩⟩ := ih (totalFiberDimension B) hBdim B rfl hfdB
          let F : Fin (nA + nB) → PModule.{u,0,u} k P :=
            fun i => Sum.elim FA FB (finSumFinEquiv.symm i)
          have hF (i : Fin (nA + nB)) : Indecomposable (F i) := by
            cases hi : finSumFinEquiv.symm i with
            | inl j => simpa [F, hi] using hFA j
            | inr j => simpa [F, hi] using hFB j
          let ε : Fin nA ⊕ Fin nB ≃ Fin (nA + nB) := finSumFinEquiv
          have hfamily : F ∘ ε = Sum.elim FA FB := by
            funext i
            simp [F, ε, Function.comp_def]
          have eReindex : (⨁ Sum.elim FA FB) ≅ ⨁ F := by
            simpa only [hfamily] using (biproduct.reindex ε F)
          have eSum : (⨁ FA) ⊞ (⨁ FB) ≅ ⨁ F :=
            (biproduct_sum_iso FA FB).trans eReindex
          exact ⟨nA + nB, F, hF,
            ⟨e.trans ((biprod.mapIso eA eB).trans eSum)⟩⟩
  exact aux (totalFiberDimension M) M rfl hM

/-- Every indecomposable finite-dimensional rank-projective on a finite poset
is one of the actual hook occurrences in its canonical finite-hook cover. -/
theorem indecomposable_rankProjective_iso_hook
    (M : PModule.{u,0,u} k P) (hM : ∀ p, FiniteDimensional k (M.obj p))
    (hI : Indecomposable M) (hR : IsRankProjective M) :
    ∃ t : FiniteHookDeflation.Index M,
      Nonempty (M ≅ FiniteHookDeflation.family M t) := by
  classical
  obtain ⟨inc, hinc⟩ := FiniteHookDeflation.exists_retract M hR
  have hFamily : ∀ t, Indecomposable (FiniteHookDeflation.family M t) := by
    intro t
    cases t with
    | inl t => exact Hook.indecomposable t.1.property
    | inr t => exact HookInfinity.indecomposable t.1
  exact indecomposable_biproduct_summand (FiniteHookDeflation.family M)
    hI hM hFamily inc (FiniteHookDeflation.π M) hinc

/-- Tags for the two canonical hook types in the finite rank-projective cover.

A finite tag records its birth and death as a strict pair; an infinite tag
records only its birth. -/
abbrev RankProjectiveHookTag (P : Type) [PartialOrder P] :=
  Sum (FiniteHookDeflation.StrictPair P) P

/-- The persistence module represented by a finite or infinite hook tag. -/
noncomputable def rankProjectiveHookModule : RankProjectiveHookTag P →
    PModule.{u,0,u} k P
  | .inl ab => Hook.module ab.val.1 ab.val.2
  | .inr a => HookInfinity.module (R := k) a

private abbrev HookTag (P : Type) [PartialOrder P] := RankProjectiveHookTag P

private def hookTag {M : PModule.{u,0,u} k P}
    (t : FiniteHookDeflation.Index M) : HookTag P :=
  match t with
  | .inl t => .inl t.1
  | .inr t => .inr t.1

private noncomputable def hookTagModule : HookTag P → PModule.{u,0,u} k P :=
  rankProjectiveHookModule (k := k)

private noncomputable def hookTagEndRingEquiv : ∀ c : HookTag P,
    End (hookTagModule (k := k) c) ≃+* k
  | .inl ab => Hook.endRingEquiv ab.property
  | .inr a => HookInfinity.endRingEquiv a

private theorem hookTag_iso_of_nonzero_composite {c d : HookTag P}
    {α : hookTagModule (k := k) c ⟶ hookTagModule (k := k) d}
    {β : hookTagModule (k := k) d ⟶ hookTagModule (k := k) c}
    (h : α ≫ β ≠ 0) :
    IsIso α := by
  classical
  let ec : End (hookTagModule (k := k) c) ≃+* k := hookTagEndRingEquiv c
  have hc : ec (α ≫ β) ≠ 0 := by
    intro hz
    apply h
    exact ec.injective (by simpa using hz)
  have hunitScalar : IsUnit (ec (α ≫ β)) := isUnit_iff_ne_zero.mpr hc
  let ab : End (hookTagModule (k := k) c) := α ≫ β
  have hunit : IsUnit ab := by
    have hm := IsUnit.map ec.symm.toRingHom hunitScalar
    simpa [ec] using hm
  letI : IsIso ab := (CategoryTheory.isUnit_iff_isIso _).mp hunit
  let r : hookTagModule d ⟶ hookTagModule c := β ≫ inv ab
  have hsection : α ≫ r = 𝟙 (hookTagModule c) := by
    dsimp [r]
    rw [← Category.assoc]
    exact IsIso.hom_inv_id ab
  let p : End (hookTagModule d) := r ≫ α
  have hp : p ≫ p = p := by
    calc
      p ≫ p = r ≫ (α ≫ r) ≫ α := by simp [p, Category.assoc]
      _ = r ≫ 𝟙 _ ≫ α := by rw [hsection]
      _ = p := by simp [p]
  let ed : End (hookTagModule (k := k) d) ≃+* k := hookTagEndRingEquiv d
  have hpidem : IsIdempotentElem (ed p) := by
    change ed p * ed p = ed p
    simpa only [← map_mul, End.mul_def] using congrArg ed hp
  rcases IsIdempotentElem.iff_eq_zero_or_one.mp hpidem with hz | ho
  · have hp0 : p = 0 := ed.injective (by simpa using hz)
    have hα0 : α = 0 := by
      calc
        α = α ≫ p := by
          dsimp [p]
          rw [← Category.assoc, hsection]
          simp
        _ = 0 := by rw [hp0]; simp
    exact (h (by simp [hα0])).elim
  · have hp1 : p = 𝟙 (hookTagModule d) := ed.injective (by simpa using ho)
    exact ⟨⟨r, hsection, hp1⟩⟩

private theorem hookTag_indecomposable (c : HookTag P) :
    Indecomposable (hookTagModule (k := k) c) := by
  cases c with
  | inl ab => exact Hook.indecomposable ab.property
  | inr a => exact HookInfinity.indecomposable a

private theorem hookTag_eq_of_iso {c d : HookTag P}
    (h : Nonempty (hookTagModule (k := k) c ≅ hookTagModule d)) : c = d := by
  cases c with
  | inl ab =>
    cases d with
    | inl cd =>
      have h' : Nonempty (Hook.module (k := k) ab.val.1 ab.val.2 ≅
          Hook.module (k := k) cd.val.1 cd.val.2) := by
        simpa [hookTagModule, rankProjectiveHookModule] using h
      rcases (Hook.nonempty_iso_iff ab.property cd.property).mp h' with ⟨ha, hd⟩
      have hab : ab = cd := Subtype.ext (Prod.ext ha hd)
      cases hab
      rfl
    | inr a =>
      have h' : Nonempty (Hook.module (k := k) ab.val.1 ab.val.2 ≅
          HookInfinity.module (R := k) a) := by
        simpa [hookTagModule, rankProjectiveHookModule] using h
      exact (Hook.not_nonempty_iso_infinity ab.property h').elim
  | inr a =>
    cases d with
    | inl ab =>
      have h' : Nonempty (Hook.module (k := k) ab.val.1 ab.val.2 ≅
          HookInfinity.module (R := k) a) := by
        rcases h with ⟨e⟩
        exact ⟨e.symm⟩
      exact (Hook.not_nonempty_iso_infinity ab.property h').elim
    | inr b =>
      have h' : Nonempty (HookInfinity.module (R := k) a ≅
          HookInfinity.module (R := k) b) := by
        simpa [hookTagModule, rankProjectiveHookModule] using h
      have hab : a = b := (HookInfinity.nonempty_iso_iff (k := k)).mp h'
      subst b
      rfl

private theorem hookTag_component_sum {n m : ℕ}
    (F : Fin n → HookTag P) (G : Fin m → HookTag P)
    (e : (⨁ fun i => hookTagModule (k := k) (F i)) ≅
      ⨁ fun j => hookTagModule (k := k) (G j)) (i : Fin n) :
    ∑ j : Fin m,
      ((biproduct.ι (fun i => hookTagModule (k := k) (F i)) i ≫ e.hom ≫
          biproduct.π (fun j => hookTagModule (k := k) (G j)) j) ≫
        (biproduct.ι (fun j => hookTagModule (k := k) (G j)) j ≫ e.inv ≫
          biproduct.π (fun i => hookTagModule (k := k) (F i)) i)) =
      𝟙 (hookTagModule (k := k) (F i)) := by
  classical
  calc
    _ = ∑ j : Fin m,
          biproduct.ι (fun i => hookTagModule (k := k) (F i)) i ≫ e.hom ≫
            (biproduct.π (fun j => hookTagModule (k := k) (G j)) j ≫
              biproduct.ι (fun j => hookTagModule (k := k) (G j)) j) ≫ e.inv ≫
              biproduct.π (fun i => hookTagModule (k := k) (F i)) i := by
        apply Finset.sum_congr rfl
        intro j hj
        simp only [Category.assoc]
    _ = biproduct.ι (fun i => hookTagModule (k := k) (F i)) i ≫ e.hom ≫
          (∑ j : Fin m,
            biproduct.π (fun j => hookTagModule (k := k) (G j)) j ≫
              biproduct.ι (fun j => hookTagModule (k := k) (G j)) j) ≫ e.inv ≫
          biproduct.π (fun i => hookTagModule (k := k) (F i)) i := by
        symm
        calc
          _ = (biproduct.ι (fun i => hookTagModule (k := k) (F i)) i ≫ e.hom) ≫
                (∑ j : Fin m,
                  biproduct.π (fun j => hookTagModule (k := k) (G j)) j ≫
                    biproduct.ι (fun j => hookTagModule (k := k) (G j)) j) ≫
                (e.inv ≫ biproduct.π (fun i => hookTagModule (k := k) (F i)) i) := by
              simp only [Category.assoc]
          _ = (∑ j : Fin m,
                (biproduct.ι (fun i => hookTagModule (k := k) (F i)) i ≫ e.hom) ≫
                  (biproduct.π (fun j => hookTagModule (k := k) (G j)) j ≫
                    biproduct.ι (fun j => hookTagModule (k := k) (G j)) j)) ≫
                (e.inv ≫ biproduct.π (fun i => hookTagModule (k := k) (F i)) i) := by
              exact congrArg (fun f => f ≫
                (e.inv ≫ biproduct.π (fun i => hookTagModule (k := k) (F i)) i))
                (Preadditive.comp_sum Finset.univ
                  (biproduct.ι (fun i => hookTagModule (k := k) (F i)) i ≫ e.hom)
                  (fun j => biproduct.π (fun j => hookTagModule (k := k) (G j)) j ≫
                    biproduct.ι (fun j => hookTagModule (k := k) (G j)) j))
          _ = ∑ j : Fin m,
                ((biproduct.ι (fun i => hookTagModule (k := k) (F i)) i ≫ e.hom) ≫
                  (biproduct.π (fun j => hookTagModule (k := k) (G j)) j ≫
                    biproduct.ι (fun j => hookTagModule (k := k) (G j)) j)) ≫
                  (e.inv ≫ biproduct.π (fun i => hookTagModule (k := k) (F i)) i) := by
              exact Preadditive.sum_comp Finset.univ
                (fun j => (biproduct.ι (fun i => hookTagModule (k := k) (F i)) i ≫ e.hom) ≫
                  (biproduct.π (fun j => hookTagModule (k := k) (G j)) j ≫
                    biproduct.ι (fun j => hookTagModule (k := k) (G j)) j))
                (e.inv ≫ biproduct.π (fun i => hookTagModule (k := k) (F i)) i)
          _ = _ := by
              apply Finset.sum_congr rfl
              intro j hj
              simp only [Category.assoc]
    _ = biproduct.ι (fun i => hookTagModule (k := k) (F i)) i ≫
          e.hom ≫ e.inv ≫
            biproduct.π (fun i => hookTagModule (k := k) (F i)) i := by
        rw [biproduct.total]
        simp [Category.assoc]
    _ = 𝟙 (hookTagModule (k := k) (F i)) := by
        calc
          _ = biproduct.ι (fun i => hookTagModule (k := k) (F i)) i ≫
                𝟙 _ ≫ biproduct.π (fun i => hookTagModule (k := k) (F i)) i :=
              congrArg (fun f => biproduct.ι (fun i => hookTagModule (k := k) (F i)) i ≫
                f ≫ biproduct.π (fun i => hookTagModule (k := k) (F i)) i) e.hom_inv_id
          _ = 𝟙 _ := by simp

private theorem exists_hookTag_iso_component {n m : ℕ}
    (F : Fin n → HookTag P) (G : Fin m → HookTag P)
    (e : (⨁ fun i => hookTagModule (k := k) (F i)) ≅
      ⨁ fun j => hookTagModule (k := k) (G j)) (i : Fin n) :
    ∃ j : Fin m, IsIso
      (biproduct.ι (fun i => hookTagModule (k := k) (F i)) i ≫ e.hom ≫
        biproduct.π (fun j => hookTagModule (k := k) (G j)) j) := by
  classical
  let a (j : Fin m) : End (hookTagModule (k := k) (F i)) :=
    (biproduct.ι (fun i => hookTagModule (k := k) (F i)) i ≫ e.hom ≫
      biproduct.π (fun j => hookTagModule (k := k) (G j)) j) ≫
    (biproduct.ι (fun j => hookTagModule (k := k) (G j)) j ≫ e.inv ≫
      biproduct.π (fun i => hookTagModule (k := k) (F i)) i)
  have hsum : ∑ j : Fin m, a j = 𝟙 (hookTagModule (k := k) (F i)) :=
    hookTag_component_sum F G e i
  let ec : End (hookTagModule (k := k) (F i)) ≃+* k :=
    hookTagEndRingEquiv (F i)
  have hscalar : (∑ j : Fin m, ec (a j)) = 1 := by
    rw [← map_sum, hsum]
    simp
  obtain ⟨j, hj⟩ : ∃ j : Fin m, ec (a j) ≠ 0 := by
    by_contra h
    have hz : ∀ j : Fin m, ec (a j) = 0 := by
      intro j
      by_contra hj
      exact h ⟨j, hj⟩
    have hzero : (∑ j : Fin m, ec (a j)) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      exact hz j
    rw [hzero] at hscalar
    exact zero_ne_one hscalar
  have hunitScalar : IsUnit (ec (a j)) := isUnit_iff_ne_zero.mpr hj
  have hunit : IsUnit (a j) := by
    have hm := IsUnit.map ec.symm.toRingHom hunitScalar
    simpa [ec] using hm
  letI : IsIso (a j) := (CategoryTheory.isUnit_iff_isIso _).mp hunit
  have hnonzero : a j ≠ 0 := by
    intro hz
    have hid : 𝟙 (hookTagModule (k := k) (F i)) = 0 := by
      calc
        𝟙 (hookTagModule (k := k) (F i)) = a j ≫ inv (a j) :=
          (IsIso.hom_inv_id (a j)).symm
        _ = 0 := by
          have hcomp := congrArg (fun f : End (hookTagModule (k := k) (F i)) =>
            f ≫ inv (a j)) hz
          exact hcomp.trans zero_comp
    exact (hookTag_indecomposable (k := k) (F i)).1
      ((IsZero.iff_id_eq_zero _).mpr hid)
  let α := biproduct.ι (fun i => hookTagModule (k := k) (F i)) i ≫ e.hom ≫
      biproduct.π (fun j => hookTagModule (k := k) (G j)) j
  let β := biproduct.ι (fun j => hookTagModule (k := k) (G j)) j ≫ e.inv ≫
      biproduct.π (fun i => hookTagModule (k := k) (F i)) i
  have hcomp : α ≫ β = a j := rfl
  have hαβ : α ≫ β ≠ 0 := by rw [hcomp]; exact hnonzero
  exact ⟨j, by simpa [α] using hookTag_iso_of_nonzero_composite hαβ⟩

private theorem fin_succ_hookTag_card {n : ℕ}
    [DecidableEq P]
    (F : Fin (n + 1) → HookTag P) (c : HookTag P) :
    Fintype.card {i : Fin (n + 1) // F i = c} =
      (if F 0 = c then 1 else 0) +
        Fintype.card {i : Fin n // F i.succ = c} := by
  classical
  calc
    Fintype.card {i : Fin (n + 1) // F i = c} =
        ∑ i : Fin (n + 1), (if F i = c then 1 else 0 : ℕ) := by
      rw [Fintype.card_subtype]
      symm
      exact Finset.sum_boole (fun i : Fin (n + 1) => F i = c) Finset.univ
    _ = (if F 0 = c then 1 else 0 : ℕ) +
        ∑ i : Fin n, (if F i.succ = c then 1 else 0 : ℕ) := by
      rw [Fin.sum_univ_succ]
    _ = (if F 0 = c then 1 else 0 : ℕ) +
        Fintype.card {i : Fin n // F i.succ = c} := by
      congr 1
      rw [Fintype.card_subtype]
      exact Finset.sum_boole (R := ℕ) (fun i : Fin n => F i.succ = c) Finset.univ

private theorem hookTag_sum_multiplicity_unique [DecidableEq P] :
    ∀ n m (F : Fin n → HookTag P) (G : Fin m → HookTag P),
      Nonempty ((⨁ fun i => hookTagModule (k := k) (F i)) ≅
        ⨁ fun j => hookTagModule (k := k) (G j)) →
      ∀ c : HookTag P,
        Fintype.card {i : Fin n // F i = c} =
          Fintype.card {j : Fin m // G j = c} := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro m F G he c
    classical
    rcases he with ⟨e⟩
    cases n with
    | zero =>
      let F0 : Fin 0 → PModule.{u,0,u} k P := fun i => hookTagModule (F i)
      let G0 : Fin m → PModule.{u,0,u} k P := fun j => hookTagModule (G j)
      have hzeroSource : IsZero (⨁ F0) := by
        apply (IsZero.iff_id_eq_zero _).mpr
        have htotal : (∑ i : Fin 0, biproduct.π F0 i ≫ biproduct.ι F0 i) =
            𝟙 (⨁ F0) := biproduct.total (f := F0)
        simpa using htotal.symm
      have hidSource : 𝟙 (⨁ F0) = 0 := (IsZero.iff_id_eq_zero _).mp hzeroSource
      have hzeroTarget : IsZero (⨁ G0) := by
        apply (IsZero.iff_id_eq_zero _).mpr
        calc
          𝟙 (⨁ G0) = e.inv ≫ e.hom := e.inv_hom_id.symm
          _ = e.inv ≫ 𝟙 (⨁ F0) ≫ e.hom := by rw [Category.id_comp]
          _ = 0 := by rw [hidSource]; simp
      have hfactor (j : Fin m) : IsZero (G0 j) := by
        apply (IsZero.iff_id_eq_zero _).mpr
        have hcoord := congrArg
          (fun f : End (⨁ G0) => biproduct.ι G0 j ≫ f ≫ biproduct.π G0 j)
          ((IsZero.iff_id_eq_zero _).mp hzeroTarget)
        simpa [Category.assoc] using hcoord
      have hm : m = 0 := by
        by_contra hm
        have hp : 0 < m := Nat.pos_of_ne_zero hm
        exact (hookTag_indecomposable (k := k) (G ⟨0, hp⟩)).1 (hfactor ⟨0, hp⟩)
      subst m
      simp
    | succ n =>
      obtain ⟨j, hAlpha⟩ := exists_hookTag_iso_component F G e 0
      let α : hookTagModule (k := k) (F 0) ⟶ hookTagModule (k := k) (G j) :=
        biproduct.ι (fun i : Fin (n + 1) => hookTagModule (k := k) (F i)) 0 ≫
          e.hom ≫ biproduct.π (fun q : Fin m => hookTagModule (k := k) (G q)) j
      have hα : IsIso α := by simpa [α] using hAlpha
      letI : IsIso α := hα
      have hIso : Nonempty (hookTagModule (k := k) (F 0) ≅ hookTagModule (k := k) (G j)) :=
        ⟨asIso α⟩
      have htag : F 0 = G j := hookTag_eq_of_iso hIso
      cases m with
      | zero => exact Fin.elim0 j
      | succ m =>
        let σ : Fin (m + 1) ≃ Fin (m + 1) := Equiv.swap 0 j
        have hσ0 : σ 0 = j := by simp [σ]
        let G' : Fin (m + 1) → HookTag P := fun q => G (σ q)
        let reindex : (⨁ fun q => hookTagModule (k := k) (G' q)) ≅
            ⨁ fun q : Fin (m + 1) => hookTagModule (k := k) (G q) :=
          biproduct.reindex σ (fun q : Fin (m + 1) => hookTagModule (k := k) (G q))
        let e' : (⨁ fun i => hookTagModule (k := k) (F i)) ≅
            ⨁ fun q => hookTagModule (k := k) (G' q) := e.trans reindex.symm
        let splitF := biproduct_split_fin_succ
          (fun i : Fin (n + 1) => hookTagModule (k := k) (F i))
        let splitG := biproduct_split_fin_succ
          (fun i : Fin (m + 1) => hookTagModule (k := k) (G' i))
        let E := splitF.trans (e'.trans splitG.symm)
        have hsplitF : biprod.inl ≫ splitF.hom =
            biproduct.ι (fun i : Fin (n + 1) => hookTagModule (k := k) (F i)) 0 :=
          biproduct_split_fin_succ_inl_hom _
        have hsplitG : splitG.inv ≫ biprod.fst =
            biproduct.π (fun i : Fin (m + 1) => hookTagModule (k := k) (G' i)) 0 :=
          biproduct_split_fin_succ_inv_fst _
        let targetIso : hookTagModule (k := k) (G' 0) ≅
            hookTagModule (k := k) (G j) :=
          eqToIso (congrArg (fun i => hookTagModule (k := k) (G i)) hσ0)
        letI : IsIso targetIso.hom := targetIso.isIso_hom
        have htargetComponent : reindex.inv ≫
            biproduct.π (fun q : Fin (m + 1) => hookTagModule (k := k) (G' q)) 0 ≫
              targetIso.hom =
            biproduct.π (fun q : Fin (m + 1) => hookTagModule (k := k) (G q)) j := by
          change (biproduct.lift fun q : Fin (m + 1) =>
            biproduct.π (fun q : Fin (m + 1) => hookTagModule (k := k) (G q)) (σ q)) ≫
              biproduct.π (fun q : Fin (m + 1) =>
                hookTagModule (k := k) (G (σ q))) 0 ≫ targetIso.hom = _
          have hLift := biproduct.lift_π
            (fun q : Fin (m + 1) =>
              biproduct.π (fun q : Fin (m + 1) => hookTagModule (k := k) (G q)) (σ q)) 0
          calc
            _ = biproduct.π (fun q : Fin (m + 1) => hookTagModule (k := k) (G q))
                  (σ 0) ≫ targetIso.hom := congrArg (fun f => f ≫ targetIso.hom) hLift
            _ = _ := by
              dsimp [targetIso]
              exact biproduct.π_comp_eqToHom
                (fun q : Fin (m + 1) => hookTagModule (k := k) (G q)) hσ0
        have hfirstBare : biprod.inl ≫ E.hom ≫ biprod.fst =
            biproduct.ι (fun i : Fin (n + 1) => hookTagModule (k := k) (F i)) 0 ≫
              e'.hom ≫ biproduct.π (fun q : Fin (m + 1) =>
                hookTagModule (k := k) (G' q)) 0 := by
          change ((biprod.inl ≫ splitF.hom) ≫ e'.hom ≫ splitG.inv ≫ biprod.fst) = _
          rw [hsplitF]
          calc
            _ = (biproduct.ι (fun i : Fin (n + 1) =>
                    hookTagModule (k := k) (F i)) 0 ≫ e'.hom) ≫
                  (splitG.inv ≫ biprod.fst) := by simp [Category.assoc]
            _ = (biproduct.ι (fun i : Fin (n + 1) =>
                    hookTagModule (k := k) (F i)) 0 ≫ e'.hom) ≫
                  biproduct.π (fun q : Fin (m + 1) =>
                    hookTagModule (k := k) (G' q)) 0 := congrArg _ hsplitG
            _ = _ := by simp [Category.assoc]
        have hfirstTransport :
            (biprod.inl ≫ E.hom ≫ biprod.fst) ≫ targetIso.hom = α := by
          calc
            _ = (biproduct.ι (fun i : Fin (n + 1) =>
                  hookTagModule (k := k) (F i)) 0 ≫ e'.hom ≫
                  biproduct.π (fun q : Fin (m + 1) =>
                    hookTagModule (k := k) (G' q)) 0) ≫ targetIso.hom :=
              congrArg (fun f => f ≫ targetIso.hom) hfirstBare
            _ = (biproduct.ι (fun i : Fin (n + 1) =>
                    hookTagModule (k := k) (F i)) 0 ≫ e.hom) ≫
                  (reindex.inv ≫ biproduct.π (fun q : Fin (m + 1) =>
                    hookTagModule (k := k) (G' q)) 0 ≫ targetIso.hom) := by
              simp [e', Category.assoc]
            _ = α := by
              rw [htargetComponent]
              rfl
        have hfirstEq : biprod.inl ≫ E.hom ≫ biprod.fst = α ≫ targetIso.inv := by
          apply (cancel_mono targetIso.hom).1
          calc
            (biprod.inl ≫ E.hom ≫ biprod.fst) ≫ targetIso.hom = α := hfirstTransport
            _ = (α ≫ targetIso.inv) ≫ targetIso.hom := by simp [Category.assoc]
        have hfirst : IsIso (biprod.inl ≫ E.hom ≫ biprod.fst) := by
          rw [hfirstEq]
          infer_instance
        letI : IsIso (biprod.inl ≫ E.hom ≫ biprod.fst) := hfirst
        let tailF : Fin n → HookTag P := fun i => F i.succ
        let tailG : Fin m → HookTag P := fun i => G' i.succ
        let tailIso : (⨁ fun i => hookTagModule (k := k) (tailF i)) ≅
            ⨁ fun i => hookTagModule (k := k) (tailG i) := Biprod.isoElim E
        have htail : Fintype.card {i : Fin n // tailF i = c} =
            Fintype.card {i : Fin m // tailG i = c} :=
          ih n (Nat.lt_succ_self n) m tailF tailG ⟨tailIso⟩ c
        have htop : F 0 = G' 0 := by simpa [G', hσ0] using htag
        have hswap : Fintype.card {i : Fin (m + 1) // G' i = c} =
            Fintype.card {i : Fin (m + 1) // G i = c} :=
          Fintype.card_congr (σ.subtypeEquiv (by intro i; rfl))
        calc
          Fintype.card {i : Fin (n + 1) // F i = c} =
              (if F 0 = c then 1 else 0) +
                Fintype.card {i : Fin n // F i.succ = c} :=
            fin_succ_hookTag_card F c
          _ = (if G' 0 = c then 1 else 0) +
                Fintype.card {i : Fin m // G' i.succ = c} := by
            rw [htop, htail]
          _ = Fintype.card {i : Fin (m + 1) // G' i = c} :=
            (fin_succ_hookTag_card G' c).symm
          _ = Fintype.card {i : Fin (m + 1) // G i = c} := hswap

/-- Isomorphic finite sums of nonzero finite or infinite hooks have the same
multiplicity for each birth/death tag. The statement retains repeated hooks
through the subtype cardinalities. -/
theorem rankProjectiveHookSum_multiplicity_unique [DecidableEq P]
    {n m : ℕ} (F : Fin n → RankProjectiveHookTag P)
    (G : Fin m → RankProjectiveHookTag P)
    (h : Nonempty
      ((⨁ fun i => rankProjectiveHookModule (k := k) (F i)) ≅
        ⨁ fun j => rankProjectiveHookModule (k := k) (G j)))
    (c : RankProjectiveHookTag P) :
    Fintype.card {i : Fin n // F i = c} =
      Fintype.card {j : Fin m // G j = c} := by
  exact hookTag_sum_multiplicity_unique n m F G h c

private theorem family_eq_hookTagModule {M : PModule.{u,0,u} k P}
    (t : FiniteHookDeflation.Index M) :
    FiniteHookDeflation.family M t = hookTagModule (hookTag t) := by
  cases t <;> rfl

private theorem family_eq_of_hookTag_eq {M : PModule.{u,0,u} k P}
    {s t : FiniteHookDeflation.Index M} (h : hookTag s = hookTag t) :
    FiniteHookDeflation.family M s = FiniteHookDeflation.family M t := by
  rw [family_eq_hookTagModule, family_eq_hookTagModule, h]

private theorem hookTag_card_finite [DecidableEq P] (M : PModule.{u,0,u} k P)
    (ab : FiniteHookDeflation.StrictPair P) :
    Fintype.card {t : FiniteHookDeflation.Index M // hookTag t = Sum.inl ab} =
      Module.finrank k (LinearMap.ker (structureMapLinear M ab.property.le)) := by
  classical
  letI : Fintype (FiniteHookDeflation.Index M) :=
    FiniteHookDeflation.indexFintype M
  let e : Fin (Module.finrank k (LinearMap.ker (structureMapLinear M ab.property.le))) ≃
      {t : FiniteHookDeflation.Index M // hookTag t = Sum.inl ab} := by
    refine Equiv.ofBijective (fun i => ⟨Sum.inl ⟨ab, i⟩, rfl⟩) ?_
    constructor
    · intro i j h
      have hv := congrArg Subtype.val h
      cases hv
      rfl
    · rintro ⟨t, ht⟩
      cases t with
      | inl q =>
        have hq : q.1 = ab := Sum.inl.inj ht
        cases hq
        exact ⟨q.2, by apply Subtype.ext; rfl⟩
      | inr q => cases ht
  simpa using Fintype.card_congr e.symm

private theorem hookTag_card_infinite [DecidableEq P] (M : PModule.{u,0,u} k P) (a : P) :
    Fintype.card {t : FiniteHookDeflation.Index M // hookTag t = Sum.inr a} =
      Module.finrank k (M.obj a) := by
  classical
  letI : Fintype (FiniteHookDeflation.Index M) :=
    FiniteHookDeflation.indexFintype M
  let e : Fin (Module.finrank k (M.obj a)) ≃
      {t : FiniteHookDeflation.Index M // hookTag t = Sum.inr a} := by
    refine Equiv.ofBijective (fun i => ⟨Sum.inr ⟨a, i⟩, rfl⟩) ?_
    constructor
    · intro i j h
      have hv := congrArg Subtype.val h
      cases hv
      rfl
    · rintro ⟨t, ht⟩
      cases t with
      | inl q => cases ht
      | inr q =>
        have hq : q.1 = a := Sum.inr.inj ht
        cases hq
        exact ⟨q.2, by apply Subtype.ext; rfl⟩
  simpa using Fintype.card_congr e.symm

private theorem finiteHookTag_source_card_le [DecidableEq P]
    (M : PModule.{u,0,u} k P) (hM : ∀ p, FiniteDimensional k (M.obj p))
    {n : ℕ} (F : Fin n → PModule.{u,0,u} k P) (e : M ≅ ⨁ F)
    (tag : Fin n → HookTag P)
    (hIso : ∀ i, Nonempty (F i ≅ hookTagModule (tag i)))
    (ab : FiniteHookDeflation.StrictPair P) :
    Fintype.card {i : Fin n // tag i = Sum.inl ab} ≤
      Module.finrank k (LinearMap.ker (structureMapLinear M ab.property.le)) := by
  classical
  let I := {i : Fin n // tag i = Sum.inl ab}
  letI : Fintype (FiniteHookDeflation.Index M) := FiniteHookDeflation.indexFintype M
  letI : Fintype I := Subtype.fintype _
  letI : ∀ p, FiniteDimensional k (M.obj p) := hM
  let eHook (i : I) : F i.val ≅ Hook.module (k := k) ab.val.1 ab.val.2 := by
    exact (Classical.choice (hIso i.val)).trans
      (eqToIso (by simpa [hookTagModule, rankProjectiveHookModule] using congrArg hookTagModule i.property))
  let x (i : I) : (F i.val).obj ab.val.1 :=
    ((eHook i).inv.app ab.val.1).hom
      (SupportInterval.one (Hook.support ab.val.1 ab.val.2)
        (Hook.birth_mem ab.property))
  have hx (i : I) : x i ≠ 0 := by
    intro hz
    have hgen := congrArg ((eHook i).hom.app ab.val.1).hom hz
    have hgen' : (SupportInterval.one (Hook.support ab.val.1 ab.val.2)
        (Hook.birth_mem ab.property) : (Hook.module (k := k) ab.val.1 ab.val.2).obj ab.val.1) = 0 := by
      simpa [x, NatTrans.comp_app, ModuleCat.hom_comp, LinearMap.comp_apply] using hgen
    exact (one_ne_zero : (1 : k) ≠ 0) (congrArg Subtype.val hgen')
  have hliSum : LinearIndependent k (fun i : I =>
      ((biproduct.ι F i.val).app ab.val.1).hom (x i)) :=
    biproduct_inclusions_linearIndependent F (fun i : I => i.val)
      Subtype.val_injective ab.val.1 x hx
  have hkerIso : LinearMap.ker ((e.inv.app ab.val.1).hom) = ⊥ :=
    LinearMap.ker_eq_bot.mpr ((e.app ab.val.1).toLinearEquiv.symm.injective)
  have hliM : LinearIndependent k (fun i : I =>
      (e.inv.app ab.val.1).hom (((biproduct.ι F i.val).app ab.val.1).hom (x i))) :=
    hliSum.map' (e.inv.app ab.val.1).hom hkerIso
  let v (i : I) : M.obj ab.val.1 :=
    (e.inv.app ab.val.1).hom (((biproduct.ι F i.val).app ab.val.1).hom (x i))
  have hdie (i : I) : structureMapLinear M ab.property.le (v i) = 0 := by
    let α : Hook.module (k := k) ab.val.1 ab.val.2 ⟶ M :=
      (eHook i).inv ≫ (biproduct.ι F i.val ≫ e.inv)
    simpa [v, x, α, NatTrans.comp_app, ModuleCat.hom_comp, LinearMap.comp_apply] using
      Hook.generator_dies ab.property α
  let w (i : I) : LinearMap.ker (structureMapLinear M ab.property.le) := ⟨v i, hdie i⟩
  have hliKer : LinearIndependent k w := by
    rw [Fintype.linearIndependent_iffₛ]
    intro f g heq i
    have hval : ∑ j, f j • v j = ∑ j, g j • v j := by
      simpa [Submodule.coe_sum, Submodule.coe_smul, w, v] using
        congrArg (fun z : LinearMap.ker (structureMapLinear M ab.property.le) =>
          (z : M.obj ab.val.1)) heq
    exact hliM.eq_coords_of_eq hval i
  simpa [I] using hliKer.fintype_card_le_finrank

private theorem infiniteHookTag_source_card_le [DecidableEq P]
    (M : PModule.{u,0,u} k P) (hM : ∀ p, FiniteDimensional k (M.obj p))
    {n : ℕ} (F : Fin n → PModule.{u,0,u} k P) (e : M ≅ ⨁ F)
    (tag : Fin n → HookTag P)
    (hIso : ∀ i, Nonempty (F i ≅ hookTagModule (tag i)))
    (a : P) :
    Fintype.card {i : Fin n // tag i = Sum.inr a} ≤
      Module.finrank k (M.obj a) := by
  classical
  let I := {i : Fin n // tag i = Sum.inr a}
  letI : Fintype (FiniteHookDeflation.Index M) := FiniteHookDeflation.indexFintype M
  letI : Fintype I := Subtype.fintype _
  letI : ∀ p, FiniteDimensional k (M.obj p) := hM
  let eHook (i : I) : F i.val ≅ HookInfinity.module (R := k) a := by
    exact (Classical.choice (hIso i.val)).trans
      (eqToIso (by simpa [hookTagModule, rankProjectiveHookModule] using congrArg hookTagModule i.property))
  let x (i : I) : (F i.val).obj a :=
    ((eHook i).inv.app a).hom (HookInfinity.birth (R := k) a)
  have hx (i : I) : x i ≠ 0 := by
    intro hz
    have hgen := congrArg ((eHook i).hom.app a).hom hz
    have hgen' : (HookInfinity.birth (R := k) a : (HookInfinity.module (R := k) a).obj a) = 0 := by
      simpa [x, NatTrans.comp_app, ModuleCat.hom_comp, LinearMap.comp_apply] using hgen
    exact HookInfinity.birth_ne_zero a hgen'
  have hliSum : LinearIndependent k (fun i : I =>
      ((biproduct.ι F i.val).app a).hom (x i)) :=
    biproduct_inclusions_linearIndependent F (fun i : I => i.val)
      Subtype.val_injective a x hx
  have hkerIso : LinearMap.ker ((e.inv.app a).hom) = ⊥ :=
    LinearMap.ker_eq_bot.mpr ((e.app a).toLinearEquiv.symm.injective)
  have hliM : LinearIndependent k (fun i : I =>
      (e.inv.app a).hom (((biproduct.ι F i.val).app a).hom (x i))) :=
    hliSum.map' (e.inv.app a).hom hkerIso
  simpa [I] using hliM.fintype_card_le_finrank

private theorem exists_hookTag_preserving_embedding [DecidableEq P]
    (M : PModule.{u,0,u} k P) (hM : ∀ p, FiniteDimensional k (M.obj p))
    {n : ℕ} (F : Fin n → PModule.{u,0,u} k P) (e : M ≅ ⨁ F)
    (tag : Fin n → HookTag P)
    (hIso : ∀ i, Nonempty (F i ≅ hookTagModule (tag i))) :
    ∃ f : Fin n → FiniteHookDeflation.Index M,
      Function.Injective f ∧ ∀ i, hookTag (f i) = tag i := by
  classical
  letI : Fintype (FiniteHookDeflation.Index M) := FiniteHookDeflation.indexFintype M
  have hcard (c : HookTag P) :
      Fintype.card {i : Fin n // tag i = c} ≤
        Fintype.card {t : FiniteHookDeflation.Index M // hookTag t = c} := by
    cases c with
    | inl ab =>
      calc
        Fintype.card {i : Fin n // tag i = Sum.inl ab} ≤
            Module.finrank k (LinearMap.ker (structureMapLinear M ab.property.le)) :=
          finiteHookTag_source_card_le M hM F e tag hIso ab
        _ = Fintype.card {t : FiniteHookDeflation.Index M // hookTag t = Sum.inl ab} :=
          (hookTag_card_finite M ab).symm
    | inr a =>
      calc
        Fintype.card {i : Fin n // tag i = Sum.inr a} ≤
            Module.finrank k (M.obj a) :=
          infiniteHookTag_source_card_le M hM F e tag hIso a
        _ = Fintype.card {t : FiniteHookDeflation.Index M // hookTag t = Sum.inr a} :=
          (hookTag_card_infinite M a).symm
  let emb (c : HookTag P) :
      {i : Fin n // tag i = c} ↪
        {t : FiniteHookDeflation.Index M // hookTag t = c} :=
    Classical.choice (Function.Embedding.nonempty_of_card_le (hcard c))
  let Source : Type := Σ c : HookTag P, {i : Fin n // tag i = c}
  let Target : Type := Σ c : HookTag P,
    {t : FiniteHookDeflation.Index M // hookTag t = c}
  let sourceEquiv : Fin n ≃ Source :=
    (Equiv.sigmaFiberEquiv tag).symm
  let targetEquiv : Target ≃ FiniteHookDeflation.Index M :=
    Equiv.sigmaFiberEquiv hookTag
  let sigmaEmbedding : Source ↪ Target := ⟨
    fun x => (⟨x.1, emb x.1 x.2⟩ : Target), by
      intro x y h
      rcases x with ⟨c, x⟩
      rcases y with ⟨d, y⟩
      have hcd : c = d := congrArg Sigma.fst h
      cases hcd
      have hxy : emb c x = emb c y := by
        apply Subtype.ext
        exact congrArg (fun z : Target => z.2.1) h
      have hxy' : x = y := (emb c).injective hxy
      subst y
      rfl
    ⟩
  let f : Fin n → FiniteHookDeflation.Index M :=
    targetEquiv ∘ sigmaEmbedding ∘ sourceEquiv
  refine ⟨f, ?_, ?_⟩
  · exact (targetEquiv.injective.comp (sigmaEmbedding.injective.comp
      sourceEquiv.injective))
  · intro i
    change hookTag ((emb (tag i) ⟨i, rfl⟩).val) = tag i
    exact (emb (tag i) ⟨i, rfl⟩).property

/-- A pointwise finite-dimensional rank-projective on a finite poset is a
finite direct sum of selected occurrences in its canonical finite-hook cover.
The occurrence indices retain the multiplicity supplied by that cover. -/
theorem rankProjective_iff_exists_canonical_subfamily
    (M : PModule.{u,0,u} k P) (hM : ∀ p, FiniteDimensional k (M.obj p)) :
    IsRankProjective M ↔
      ∃ S : Finset (FiniteHookDeflation.Index M),
        Nonempty (M ≅ ⨁ fun i : S => FiniteHookDeflation.family M i.1) := by
  classical
  constructor
  · intro hR
    obtain ⟨n, F, hF, ⟨eM⟩⟩ := exists_finite_indecomposable_decomposition M hM
    have hfd (i : Fin n) : ∀ p, FiniteDimensional k ((F i).obj p) := by
      intro p
      letI : FiniteDimensional k ((⨁ F).obj p) :=
        (eM.app p).toLinearEquiv.finiteDimensional
      exact FiniteDimensional.of_injective
        ((biproduct.ι F i).app p).hom
        ((ModuleCat.mono_iff_injective _).mp inferInstance)
    have hRPsum : IsRankProjective (⨁ F) := hR.of_iso eM
    have hRP (i : Fin n) : IsRankProjective (F i) := by
      exact hRPsum.of_retract (biproduct.ι F i) (biproduct.π F i)
        (biproduct.ι_π_self F i)
    have hTag : ∀ i : Fin n, ∃ c : HookTag P,
        Nonempty (F i ≅ hookTagModule c) := by
      intro i
      obtain ⟨t, ⟨e⟩⟩ :=
        indecomposable_rankProjective_iso_hook (F i) (hfd i) (hF i) (hRP i)
      refine ⟨hookTag t, ⟨e.trans (eqToIso (family_eq_hookTagModule t))⟩⟩
    choose tag hIso using hTag
    obtain ⟨f, hf, htag⟩ :=
      exists_hookTag_preserving_embedding M hM F eM tag hIso
    let S : Finset (FiniteHookDeflation.Index M) := Finset.univ.image f
    let g : Fin n → S := fun i => ⟨f i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩
    have hg : Function.Bijective g := by
      constructor
      · intro i j hij
        exact hf (congrArg Subtype.val hij)
      · intro s
        rcases Finset.mem_image.mp s.property with ⟨i, -, hi⟩
        exact ⟨i, Subtype.ext hi⟩
    let eIndex : Fin n ≃ S := Equiv.ofBijective g hg
    let G : Fin n → PModule.{u,0,u} k P :=
      fun i => FiniteHookDeflation.family M (f i)
    let H : S → PModule.{u,0,u} k P :=
      fun i => FiniteHookDeflation.family M i.1
    have hFactorIso (i : Fin n) : F i ≅ G i := by
      have hEq : FiniteHookDeflation.family M (f i) = hookTagModule (tag i) :=
        (family_eq_hookTagModule (M := M) (f i)).trans
          (congrArg hookTagModule (htag i))
      exact (Classical.choice (hIso i)).trans (eqToIso hEq.symm)
    have hReindexFamily : H ∘ eIndex = G := by
      funext i
      rfl
    have eReindex : (⨁ G) ≅ ⨁ H := by
      simpa only [hReindexFamily] using (biproduct.reindex eIndex H)
    refine ⟨S, ⟨eM.trans ((biproduct.mapIso hFactorIso).trans eReindex)⟩⟩
  · rintro ⟨S, ⟨e⟩⟩
    have hS : IsRankProjective
        (⨁ fun i : S => FiniteHookDeflation.family M i.1) :=
      IsRankProjective.biproduct _ (fun i => FiniteHookDeflation.family_isRankProjective M i.1)
    exact hS.of_iso e.symm

end TDA.Persistence.FiniteRankProjectiveClassification
