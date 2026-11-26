import TDA.Topology.AffineSubdivision
import TDA.Topology.SmallChains
import Mathlib.Algebra.Category.ModuleCat.Colimits

/-!
# Singular barycentric subdivision

The standard `n`-simplex is a convex subset of itself, `modelSimplex n`, with the identity affine
simplex `idSimplex n` (vertex `i` is the `i`-th vertex). A singular `n`-simplex `σ` of a space `X`
is the continuous map `modelMap σ` on the model, and `σ_*` is the chain map
`toSingularChains (isConvexSet_modelSimplex n) X (modelMap σ) R` from affine chains of the model
to singular chains of `X`; it sends `idSimplex n` to `σ`
(`ιChainComplex_idSimplex_toSingularChains`). The singular chains of `X` with coefficients `R` in a
preadditive category with coproducts are written `(TopCat.toSSet.obj X).chainComplex R`, which is
by definition `((singularChainComplexFunctor C).obj R).obj X`.

`singularSubdivision R X` is the **singular barycentric subdivision** chain map on the singular
chains of `X`: a generator `σ` goes to `σ_*(sd_n)`, where `sd_n` is the affine subdivision
`affineSubdivision` of `idSimplex n`, built recursively by `sd_n = b_n · sd(∂ idSimplex n)` with
the cone at the barycentre (`ιChainComplex_singularSubdivision_f`). It commutes with `e_*` for
every continuous map `e` from any convex subset of a standard simplex
(`toSingularChains_comp_singularSubdivision`); this compatibility gives the chain-map property
and naturality in `X` (`singularSubdivision_naturality`, `singularSubdivisionNatTrans`).

`singularSubdivisionHomotopy R X` is a homotopy from `singularSubdivision R X` to the identity,
obtained in the same way from the affine homotopy `affineSubdivisionHomotopy` of `idSimplex n`
(`ιChainComplex_singularSubdivisionHomotopy_hom`), and natural in `X`
(`singularSubdivisionHomotopy_hom_naturality`).

Both preserve every subcomplex `A` of singular simplices that contains, with each simplex, all
singular simplices with image inside its image (`exists_singularSubdivision_f_lift`,
`exists_singularSubdivisionHomotopy_hom_lift`); the small simplices of two subsets form such a
subcomplex. For complexes of modules over a ring `k`, this gives the element-wise hypotheses of
`quasiIso_of_iterate_mem` for the inclusion of small chains
(`singularSubdivision_f_apply_mem_range_smallChainsι`,
`singularSubdivisionHomotopy_hom_apply_mem_range_smallChainsι`).
-/

namespace TDA.Topology

open CategoryTheory Limits Convexity Simplicial AlgebraicTopology Opposite
open AffineChains affineSSet

noncomputable section

universe u

/-! ### The model simplex -/

/-- The standard `n`-simplex as a convex subset of itself: the model of singular `n`-simplices. -/
abbrev modelSimplex (n : ℕ) : Set (StdSimplex ℝ (Fin (n + 1))) := Set.univ

/-- The model simplex is convex. -/
theorem isConvexSet_modelSimplex (n : ℕ) : IsConvexSet ℝ (modelSimplex n) := IsConvexSet.univ

/-- The identity affine simplex of the model: vertex `i` is the `i`-th vertex of the standard
simplex. -/
def idSimplex (n : ℕ) : Fin (n + 1) → modelSimplex n := fun i => ⟨.single i, trivial⟩

/-- A singular `n`-simplex as a continuous map on the model. -/
def modelMap {X : TopCat.{u}} {n : ℕ} (σ : (TopCat.toSSet.obj X) _⦋n⦌) : C(modelSimplex n, X) :=
  ContinuousMap.restrict (modelSimplex n) (X.toSSetObjEquiv _ σ)

/-- `modelMap σ` evaluates `σ` at the underlying point of the standard simplex. -/
@[simp]
theorem modelMap_apply {X : TopCat.{u}} {n : ℕ} (σ : (TopCat.toSSet.obj X) _⦋n⦌)
    (x : modelSimplex n) : modelMap σ x = X.toSSetObjEquiv _ σ x.1 :=
  rfl

/-- The image of `modelMap σ` lies in the image of `σ`. -/
theorem range_modelMap_subset {X : TopCat.{u}} {n : ℕ} (σ : (TopCat.toSSet.obj X) _⦋n⦌) :
    Set.range (modelMap σ) ⊆ Set.range (X.toSSetObjEquiv _ σ) := by
  rintro _ ⟨x, rfl⟩
  exact ⟨x.1, rfl⟩

/-- The identity affine simplex realizes as the identity of the standard simplex. -/
@[simp]
theorem realize_idSimplex (n : ℕ) (t : StdSimplex ℝ (Fin (n + 1))) :
    realize (isConvexSet_modelSimplex n) (idSimplex n) t = ⟨t, trivial⟩ := by
  ext1
  rw [coe_realize_apply, StdSimplex.affineMapMk_apply]
  exact StdSimplex.iConvexComb_single t

/-- `σ_*` sends the identity affine simplex to `σ`. -/
@[simp]
theorem toSingular_idSimplex {X : TopCat.{u}} {n : ℕ} (σ : (TopCat.toSSet.obj X) _⦋n⦌) :
    (toSingular (isConvexSet_modelSimplex n) X (modelMap σ)).app _ (mk (idSimplex n)) = σ := by
  rw [toSingular_app_mk, Equiv.symm_apply_eq]
  ext t
  simp

variable {C : Type*} [Category* C] [HasCoproducts.{u} C] [Preadditive C] (R : C)

/-- `σ_*` sends the generator of the identity affine simplex to the generator of `σ`. -/
@[reassoc (attr := simp)]
theorem ιChainComplex_idSimplex_toSingularChains {X : TopCat.{u}} {n : ℕ}
    (σ : (TopCat.toSSet.obj X) _⦋n⦌) :
    (affineSSet.{u} (modelSimplex n)).ιChainComplex (R := R) (mk (idSimplex n)) ≫
        (toSingularChains (isConvexSet_modelSimplex n) X (modelMap σ) R).f n =
      (TopCat.toSSet.obj X).ιChainComplex σ := by
  rw [SSet.ι_chainComplexMap_f, toSingular_idSimplex]

/-- Precomposing `toSingular` with the simplicial map of an affine map `F : K → K'` gives
`toSingular` of the composite. -/
theorem map_comp_toSingular {m m' : ℕ} {K : Set (StdSimplex ℝ (Fin (m + 1)))}
    {K' : Set (StdSimplex ℝ (Fin (m' + 1)))} (hK : IsConvexSet ℝ K) (hK' : IsConvexSet ℝ K')
    (F : ConvexSpace.AffineMap ℝ (StdSimplex ℝ (Fin (m + 1))) (StdSimplex ℝ (Fin (m' + 1))))
    (hF : Set.MapsTo F K K') (Y : TopCat.{u}) (e : C(K, Y)) (e' : C(K', Y))
    (he : ∀ x, e x = e' (hF.restrict F K K' x)) :
    affineSSet.map.{u} (hF.restrict F K K') ≫ toSingular hK' Y e' = toSingular hK Y e := by
  ext n σ
  change (Y.toSSetObjEquiv n).symm (e'.comp (realize hK' (hF.restrict F K K' ∘ ULift.down σ))) =
    (Y.toSSetObjEquiv n).symm (e.comp (realize hK (ULift.down σ)))
  congr 1
  ext t
  rw [ContinuousMap.comp_apply, ContinuousMap.comp_apply, he]
  exact congrArg e' (Subtype.ext (coe_realize_mapsTo hK hK' F hF _ t))

/-- Singular simplices obtained from `e` by affine reparametrization lie in the image of `e`. -/
theorem range_toSingular_le {m : ℕ} {K : Set (StdSimplex ℝ (Fin (m + 1)))} (hK : IsConvexSet ℝ K)
    (Y : TopCat.{u}) (e : C(K, Y)) :
    SSet.Subcomplex.range (toSingular hK Y e) ≤ simplicesIn (Set.range e) := by
  rintro n _ ⟨σ, rfl⟩
  rw [mem_simplicesIn_iff]
  rintro _ ⟨t, rfl⟩
  exact ⟨_, rfl⟩

/-! ### Extension from the model -/

private lemma chainComplexMap_f_comp {S T U : SSet.{u}} (f : S ⟶ T) (g : T ⟶ U) (n : ℕ) :
    (SSet.chainComplexMap f R).f n ≫ (SSet.chainComplexMap g R).f n =
      (SSet.chainComplexMap (f ≫ g) R).f n := by
  ext x
  simp

/-- The map out of simplicial `n`-chains with the given values on generators. -/
private def descChains {S : SSet.{u}} {n : ℕ} {T : C} (f : S _⦋n⦌ → (R ⟶ T)) :
    (S.chainComplex R).X n ⟶ T :=
  Cofan.IsColimit.desc (S.isColimitChainComplexXCofan R n) f

@[reassoc]
private lemma ι_descChains {S : SSet.{u}} {n : ℕ} {T : C} (f : S _⦋n⦌ → (R ⟶ T)) (x : S _⦋n⦌) :
    S.ιChainComplex (R := R) x ≫ descChains R f = f x :=
  Cofan.IsColimit.fac _ _ x

/-- The map of singular chains sending a generator `σ` to `σ_*(φ)`, for a model affine
chain `φ`. -/
private def extend {q p : ℕ} (φ : R ⟶ ((affineSSet.{u} (modelSimplex q)).chainComplex R).X p)
    (X : TopCat.{u}) :
    ((TopCat.toSSet.obj X).chainComplex R).X q ⟶
      ((TopCat.toSSet.obj X).chainComplex R).X p :=
  Cofan.IsColimit.desc ((TopCat.toSSet.obj X).isColimitChainComplexXCofan R q)
    fun σ => φ ≫ (toSingularChains (isConvexSet_modelSimplex q) X (modelMap σ) R).f p

private lemma ι_extend {q p : ℕ} (φ : R ⟶ ((affineSSet.{u} (modelSimplex q)).chainComplex R).X p)
    {X : TopCat.{u}} (σ : (TopCat.toSSet.obj X) _⦋q⦌) :
    (TopCat.toSSet.obj X).ιChainComplex (R := R) σ ≫ extend R φ X =
      φ ≫ (toSingularChains (isConvexSet_modelSimplex q) X (modelMap σ) R).f p :=
  Cofan.IsColimit.fac ((TopCat.toSSet.obj X).isColimitChainComplexXCofan R q) _ σ

/-- For a family `Φ` of maps of affine chains natural in affine maps, `extend` of `Φ` on the
identity simplex is compatible with `e_*` for every convex `K` and `e : C(K, X)`. -/
private lemma toSingularChains_comp_extend {q p : ℕ}
    (Φ : ∀ {m : ℕ} {K : Set (StdSimplex ℝ (Fin (m + 1)))}, IsConvexSet ℝ K →
      (((affineSSet.{u} K).chainComplex R).X q ⟶ ((affineSSet.{u} K).chainComplex R).X p))
    (hΦ : ∀ {m m' : ℕ} {K : Set (StdSimplex ℝ (Fin (m + 1)))}
      {K' : Set (StdSimplex ℝ (Fin (m' + 1)))} (hK : IsConvexSet ℝ K) (hK' : IsConvexSet ℝ K')
      (F : ConvexSpace.AffineMap ℝ (StdSimplex ℝ (Fin (m + 1))) (StdSimplex ℝ (Fin (m' + 1))))
      (hF : Set.MapsTo F K K'),
      Φ hK ≫ (SSet.chainComplexMap (affineSSet.map.{u} (hF.restrict F K K')) R).f p =
        (SSet.chainComplexMap (affineSSet.map.{u} (hF.restrict F K K')) R).f q ≫ Φ hK')
    {m : ℕ} {K : Set (StdSimplex ℝ (Fin (m + 1)))} (hK : IsConvexSet ℝ K) (X : TopCat.{u})
    (e : C(K, X)) :
    (toSingularChains hK X e R).f q ≫
        extend R ((affineSSet.{u} (modelSimplex q)).ιChainComplex (mk (idSimplex q)) ≫
          Φ (isConvexSet_modelSimplex q)) X =
      Φ hK ≫ (toSingularChains hK X e R).f p := by
  ext τ
  obtain ⟨τ, rfl⟩ : ∃ v, mk v = τ := ⟨vertices τ, rfl⟩
  have hG : Set.MapsTo (StdSimplex.affineMapMk (R := ℝ) (Subtype.val ∘ τ)) (modelSimplex q) K :=
    fun x _ => (realize hK τ x).2
  have hτ : (affineSSet.{u} K).ιChainComplex (R := R) (mk τ) =
      (affineSSet.{u} (modelSimplex q)).ιChainComplex (R := R) (mk (idSimplex q)) ≫
        (SSet.chainComplexMap (affineSSet.map.{u} (hG.restrict _ _ _)) R).f q := by
    rw [SSet.ι_chainComplexMap_f, map_app_mk]
    congr 2
    funext i
    exact Subtype.ext (StdSimplex.affineMapMk_single (R := ℝ) (Subtype.val ∘ τ) i).symm
  rw [SSet.ι_chainComplexMap_f_assoc, ι_extend, hτ]
  simp only [Category.assoc]
  rw [← reassoc_of% (hΦ (isConvexSet_modelSimplex q) hK _ hG), chainComplexMap_f_comp,
    map_comp_toSingular (isConvexSet_modelSimplex q) hK _ hG X
      (modelMap ((toSingular hK X e).app _ (mk τ))) e (fun x => by simp; rfl)]

/-! ### The subdivision chain map -/

private lemma sd_compat {q : ℕ} {m : ℕ} {K : Set (StdSimplex ℝ (Fin (m + 1)))}
    (hK : IsConvexSet ℝ K) (X : TopCat.{u}) (e : C(K, X)) :
    (toSingularChains hK X e R).f q ≫
        extend R ((affineSSet.{u} (modelSimplex q)).ιChainComplex (mk (idSimplex q)) ≫
          (affineSubdivision (isConvexSet_modelSimplex q) R).f q) X =
      (affineSubdivision hK R).f q ≫ (toSingularChains hK X e R).f q :=
  toSingularChains_comp_extend R (fun hK => (affineSubdivision hK R).f q)
    (fun hK hK' F hF => by
      simpa using HomologicalComplex.congr_hom
        (affineSubdivision_comp_chainComplexMap hK R hK' F hF) q)
    hK X e

/-- **Singular barycentric subdivision**: the chain map sending a singular simplex `σ` to
`σ_*(sd_n)`, where `sd_n = b_n · sd(∂ idSimplex n)` is the barycentric subdivision of the
identity simplex. -/
def singularSubdivision (X : TopCat.{u}) :
    (TopCat.toSSet.obj X).chainComplex R ⟶
      (TopCat.toSSet.obj X).chainComplex R where
  f n := extend R ((affineSSet.{u} (modelSimplex n)).ιChainComplex (mk (idSimplex n)) ≫
    (affineSubdivision (isConvexSet_modelSimplex n) R).f n) X
  comm' i j hij := by
    obtain rfl : i = j + 1 := hij.symm
    refine SSet.chainComplex_hom_ext (X := TopCat.toSSet.obj X) fun σ => ?_
    rw [reassoc_of% ι_extend,
      (toSingularChains (isConvexSet_modelSimplex (j + 1)) X (modelMap σ) R).comm, Category.assoc,
      (affineSubdivision (isConvexSet_modelSimplex (j + 1)) R).comm_assoc, ← sd_compat,
      ← (toSingularChains (isConvexSet_modelSimplex (j + 1)) X (modelMap σ) R).comm_assoc,
      ιChainComplex_idSimplex_toSingularChains_assoc]

/-- On a generator, singular subdivision is `σ_*` of the subdivision of the identity simplex. -/
theorem ιChainComplex_singularSubdivision_f {X : TopCat.{u}} {n : ℕ}
    (σ : (TopCat.toSSet.obj X) _⦋n⦌) :
    (TopCat.toSSet.obj X).ιChainComplex (R := R) σ ≫ (singularSubdivision R X).f n =
      (affineSSet.{u} (modelSimplex n)).ιChainComplex (mk (idSimplex n)) ≫
        (affineSubdivision (isConvexSet_modelSimplex n) R).f n ≫
          (toSingularChains (isConvexSet_modelSimplex n) X (modelMap σ) R).f n := by
  rw [← Category.assoc]
  exact ι_extend R _ σ

/-- Singular subdivision commutes with `e_*` for every continuous `e` from a convex subset of a
standard simplex: `e_* ∘ sd = sd ∘ e_*`. -/
@[reassoc]
theorem toSingularChains_comp_singularSubdivision {m : ℕ} {K : Set (StdSimplex ℝ (Fin (m + 1)))}
    (hK : IsConvexSet ℝ K) (X : TopCat.{u}) (e : C(K, X)) :
    toSingularChains hK X e R ≫ singularSubdivision R X =
      affineSubdivision hK R ≫ toSingularChains hK X e R := by
  ext q : 1
  exact sd_compat R hK X e

/-- Singular subdivision is the identity in degree `0`. -/
@[simp]
theorem singularSubdivision_f_zero (X : TopCat.{u}) :
    (singularSubdivision R X).f 0 = 𝟙 _ := by
  refine SSet.chainComplex_hom_ext (X := TopCat.toSSet.obj X) fun σ => ?_
  rw [ιChainComplex_singularSubdivision_f, affineSubdivision_f_zero, Category.id_comp,
    ιChainComplex_idSimplex_toSingularChains, Category.comp_id]

/-- **Naturality** of singular subdivision in the space. -/
@[reassoc]
theorem singularSubdivision_naturality {X Y : TopCat.{u}} (f : X ⟶ Y) :
    singularSubdivision R X ≫ SSet.chainComplexMap (TopCat.toSSet.map f) R =
      SSet.chainComplexMap (TopCat.toSSet.map f) R ≫ singularSubdivision R Y := by
  ext n : 1
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f]
  refine SSet.chainComplex_hom_ext (X := TopCat.toSSet.obj X) fun σ => ?_
  rw [reassoc_of% ιChainComplex_singularSubdivision_f, SSet.ι_chainComplexMap_f_assoc,
    ιChainComplex_singularSubdivision_f, chainComplexMap_f_comp, toSingular_comp]
  rfl

/-- Singular subdivision as a natural transformation of singular chain complex functors. -/
@[simps]
def singularSubdivisionNatTrans :
    (singularChainComplexFunctor C).obj R ⟶ (singularChainComplexFunctor C).obj R where
  app X := singularSubdivision R X
  naturality _ _ f := (singularSubdivision_naturality R f).symm

/-! ### The subdivision homotopy -/

@[reassoc]
private lemma hom_compat {q : ℕ} {m : ℕ} {K : Set (StdSimplex ℝ (Fin (m + 1)))}
    (hK : IsConvexSet ℝ K) (X : TopCat.{u}) (e : C(K, X)) :
    (toSingularChains hK X e R).f q ≫
        extend R ((affineSSet.{u} (modelSimplex q)).ιChainComplex (mk (idSimplex q)) ≫
          (affineSubdivisionHomotopy (isConvexSet_modelSimplex q) R).hom q (q + 1)) X =
      (affineSubdivisionHomotopy hK R).hom q (q + 1) ≫ (toSingularChains hK X e R).f (q + 1) :=
  toSingularChains_comp_extend R (fun hK => (affineSubdivisionHomotopy hK R).hom q (q + 1))
    (fun hK hK' F hF => affineSubdivisionHomotopy_hom_comp_chainComplexMap hK R hK' F hF q)
    hK X e

/-- The homotopy identities of the affine subdivision homotopy in positive degree. -/
private lemma affine_comm_succ {m : ℕ} {K : Set (StdSimplex ℝ (Fin (m + 1)))}
    (hK : IsConvexSet ℝ K) (n : ℕ) :
    (affineSubdivision hK R).f (n + 1) =
      ((affineSSet.{u} K).chainComplex R).d (n + 1) n ≫
          (affineSubdivisionHomotopy hK R).hom n (n + 1) +
        (affineSubdivisionHomotopy hK R).hom (n + 1) (n + 2) ≫
          ((affineSSet.{u} K).chainComplex R).d (n + 2) (n + 1) + 𝟙 _ := by
  have h := (affineSubdivisionHomotopy hK R).comm (n + 1)
  rwa [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex,
    HomologicalComplex.id_f] at h

/-- The **subdivision homotopy** from singular subdivision to the identity: on a generator `σ`
of degree `n` it is `σ_*(T_n)`, with `T_n` the affine subdivision homotopy of the identity
simplex. -/
def singularSubdivisionHomotopy (X : TopCat.{u}) :
    Homotopy (singularSubdivision R X) (𝟙 _) :=
  chainHomotopyOfSucc
    (fun n => extend R ((affineSSet.{u} (modelSimplex n)).ιChainComplex (mk (idSimplex n)) ≫
      (affineSubdivisionHomotopy (isConvexSet_modelSimplex n) R).hom n (n + 1)) X)
    (by
      refine SSet.chainComplex_hom_ext (X := TopCat.toSSet.obj X) fun σ => ?_
      rw [ιChainComplex_singularSubdivision_f, affineSubdivision_f_zero, Category.id_comp,
        ιChainComplex_idSimplex_toSingularChains, Preadditive.comp_add, reassoc_of% ι_extend,
        affineSubdivisionHomotopy_hom_zero]
      simp)
    (fun n => by
      refine SSet.chainComplex_hom_ext (X := TopCat.toSSet.obj X) fun σ => ?_
      have h₁ := ιChainComplex_idSimplex_toSingularChains R σ
      have hd := (toSingularChains (isConvexSet_modelSimplex (n + 1)) X (modelMap σ) R).comm
      have e₁ := (toSingularChains (isConvexSet_modelSimplex (n + 1)) X (modelMap σ) R).comm_assoc
      rw [ιChainComplex_singularSubdivision_f, affine_comm_succ, ← h₁]
      simp only [Preadditive.add_comp, Preadditive.comp_add, Category.assoc, Category.id_comp,
        HomologicalComplex.id_f, Category.comp_id]
      rw [e₁, hom_compat, hom_compat_assoc, hd])

/-- On a generator, the subdivision homotopy is `σ_*` of the affine homotopy of the identity
simplex. -/
theorem ιChainComplex_singularSubdivisionHomotopy_hom {X : TopCat.{u}} {n : ℕ}
    (σ : (TopCat.toSSet.obj X) _⦋n⦌) :
    (TopCat.toSSet.obj X).ιChainComplex (R := R) σ ≫
        (singularSubdivisionHomotopy R X).hom n (n + 1) =
      (affineSSet.{u} (modelSimplex n)).ιChainComplex (mk (idSimplex n)) ≫
        (affineSubdivisionHomotopy (isConvexSet_modelSimplex n) R).hom n (n + 1) ≫
          (toSingularChains (isConvexSet_modelSimplex n) X (modelMap σ) R).f (n + 1) := by
  rw [singularSubdivisionHomotopy, chainHomotopyOfSucc_hom_succ, ← Category.assoc]
  exact ι_extend R _ σ

/-- The subdivision homotopy commutes with `e_*` for every continuous `e` from a convex subset of
a standard simplex. -/
@[reassoc]
theorem toSingularChains_comp_singularSubdivisionHomotopy_hom {m : ℕ}
    {K : Set (StdSimplex ℝ (Fin (m + 1)))} (hK : IsConvexSet ℝ K) (X : TopCat.{u}) (e : C(K, X))
    (n : ℕ) :
    (toSingularChains hK X e R).f n ≫ (singularSubdivisionHomotopy R X).hom n (n + 1) =
      (affineSubdivisionHomotopy hK R).hom n (n + 1) ≫ (toSingularChains hK X e R).f (n + 1) := by
  rw [singularSubdivisionHomotopy, chainHomotopyOfSucc_hom_succ]
  exact hom_compat R hK X e

/-- **Naturality** of the subdivision homotopy in the space. -/
@[reassoc]
theorem singularSubdivisionHomotopy_hom_naturality {X Y : TopCat.{u}} (f : X ⟶ Y) (i j : ℕ) :
    (singularSubdivisionHomotopy R X).hom i j ≫
        (SSet.chainComplexMap (TopCat.toSSet.map f) R).f j =
      (SSet.chainComplexMap (TopCat.toSSet.map f) R).f i ≫
        (singularSubdivisionHomotopy R Y).hom i j := by
  by_cases hij : i + 1 = j
  · subst hij
    refine SSet.chainComplex_hom_ext (X := TopCat.toSSet.obj X) fun σ => ?_
    rw [reassoc_of% ιChainComplex_singularSubdivisionHomotopy_hom, SSet.ι_chainComplexMap_f_assoc,
      ιChainComplex_singularSubdivisionHomotopy_hom, chainComplexMap_f_comp, toSingular_comp]
    rfl
  · rw [(singularSubdivisionHomotopy R X).zero i j hij,
      (singularSubdivisionHomotopy R Y).zero i j hij, zero_comp, comp_zero]

/-! ### Subcomplexes preserved by subdivision -/

section Lift

variable {X : TopCat.{u}} (A : (TopCat.toSSet.obj X).Subcomplex)
  (hA : ∀ (n : ℕ) (σ : (TopCat.toSSet.obj X) _⦋n⦌), σ ∈ A.obj (op ⦋n⦌) →
    simplicesIn (Set.range (X.toSSetObjEquiv _ σ)) ≤ A)

include hA in
private lemma exists_extend_lift {q p : ℕ}
    (φ : R ⟶ ((affineSSet.{u} (modelSimplex q)).chainComplex R).X p) :
    ∃ g : ((A : SSet.{u}).chainComplex R).X q ⟶ ((A : SSet.{u}).chainComplex R).X p,
      g ≫ (SSet.chainComplexMap A.ι R).f p = (SSet.chainComplexMap A.ι R).f q ≫ extend R φ X := by
  have hσ (σ : (A : SSet.{u}) _⦋q⦌) :
      SSet.Subcomplex.range (toSingular (isConvexSet_modelSimplex q) X (modelMap σ.1)) ≤ A :=
    (range_toSingular_le _ X _).trans
      ((simplicesIn_mono (range_modelMap_subset σ.1)).trans (hA q σ.1 σ.2))
  refine ⟨descChains R fun σ : (A : SSet.{u}) _⦋q⦌ =>
    φ ≫ (SSet.chainComplexMap (SSet.Subcomplex.lift _ (hσ σ)) R).f p, ?_⟩
  refine SSet.chainComplex_hom_ext fun σ => ?_
  rw [ι_descChains_assoc, SSet.ι_chainComplexMap_f_assoc, Category.assoc, chainComplexMap_f_comp,
    SSet.Subcomplex.lift_ι]
  exact (ι_extend R φ σ.1).symm

include hA in
/-- Singular subdivision preserves every subcomplex `A` that contains, with each simplex, all
singular simplices with image in its image. -/
theorem exists_singularSubdivision_f_lift (n : ℕ) :
    ∃ g : ((A : SSet.{u}).chainComplex R).X n ⟶ ((A : SSet.{u}).chainComplex R).X n,
      g ≫ (SSet.chainComplexMap A.ι R).f n =
        (SSet.chainComplexMap A.ι R).f n ≫ (singularSubdivision R X).f n :=
  exists_extend_lift R A hA _

include hA in
/-- The subdivision homotopy preserves every subcomplex `A` that contains, with each simplex,
all singular simplices with image in its image. -/
theorem exists_singularSubdivisionHomotopy_hom_lift (n : ℕ) :
    ∃ g : ((A : SSet.{u}).chainComplex R).X n ⟶ ((A : SSet.{u}).chainComplex R).X (n + 1),
      g ≫ (SSet.chainComplexMap A.ι R).f (n + 1) =
        (SSet.chainComplexMap A.ι R).f n ≫ (singularSubdivisionHomotopy R X).hom n (n + 1) := by
  rw [singularSubdivisionHomotopy, chainHomotopyOfSucc_hom_succ]
  exact exists_extend_lift R A hA _

end Lift

/-- The small simplices of two subsets contain, with each simplex, all singular simplices with
image in its image. -/
theorem simplicesIn_range_le_smallSimplices {X : TopCat.{u}} (s t : Set X) (n : ℕ)
    (σ : (TopCat.toSSet.obj X) _⦋n⦌) (hσ : σ ∈ (smallSimplices s t).obj (op ⦋n⦌)) :
    simplicesIn (Set.range (X.toSSetObjEquiv _ σ)) ≤ smallSimplices s t := by
  rcases (mem_smallSimplices_iff s t σ).1 hσ with h | h
  · exact (simplicesIn_mono h).trans le_sup_left
  · exact (simplicesIn_mono h).trans le_sup_right

section ModuleCat

variable {k : Type u} [Ring k] {X : TopCat.{u}} (s t : Set X) (M : ModuleCat.{u} k)

/-- Singular subdivision carries small chains to small chains, element-wise (the hypothesis `hS`
of `quasiIso_of_iterate_mem`). -/
theorem singularSubdivision_f_apply_mem_range_smallChainsι (n : ℕ)
    (a : (smallChains s t M).X n) :
    ((singularSubdivision M X).f n).hom (((smallChainsι s t M).f n).hom a) ∈
      LinearMap.range ((smallChainsι s t M).f n).hom := by
  obtain ⟨g, hg⟩ := exists_singularSubdivision_f_lift M (smallSimplices s t)
    (simplicesIn_range_le_smallSimplices s t) n
  exact ⟨g.hom a, congrArg (fun φ => φ.hom a) hg⟩

/-- The subdivision homotopy carries small chains to small chains, element-wise (the hypothesis
`hT` of `quasiIso_of_iterate_mem`). -/
theorem singularSubdivisionHomotopy_hom_apply_mem_range_smallChainsι (n m : ℕ)
    (a : (smallChains s t M).X n) :
    ((singularSubdivisionHomotopy M X).hom n m).hom (((smallChainsι s t M).f n).hom a) ∈
      LinearMap.range ((smallChainsι s t M).f m).hom := by
  by_cases hnm : n + 1 = m
  · subst hnm
    obtain ⟨g, hg⟩ := exists_singularSubdivisionHomotopy_hom_lift M (smallSimplices s t)
      (simplicesIn_range_le_smallSimplices s t) n
    exact ⟨g.hom a, congrArg (fun φ => φ.hom a) hg⟩
  · rw [(singularSubdivisionHomotopy M X).zero n m hnm]
    exact Submodule.zero_mem _

end ModuleCat

end

end TDA.Topology
