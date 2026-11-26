import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
import Mathlib.Geometry.Convex.ConvexSpace.AffineMapCone
import Mathlib.Geometry.Convex.ConvexSpace.ModuleTopology
import Mathlib.Geometry.Convex.Set

/-!
# Affine chains on a convex subset of the standard simplex

An affine `n`-simplex with vertices in a type `X` is a tuple `Fin (n + 1) → X`. These tuples
form the simplicial set `affineSSet X`, on which a simplicial operator acts by precomposition
with the underlying monotone map, so its chain complex `(affineSSet X).chainComplex R` has
Mathlib's alternating face map differential (`SSet.ιChainComplex_d`) and no sign convention of
its own. The cone `b · σ` puts the apex `b` at vertex `0` in front of the vertices of `σ`, as
`Convexity.ConvexSpace.AffineMap.cone` does, and `coneMap R b n` extends it to `n`-chains.
The boundary formulas are `∂(b · c) = c - b · ∂c` in positive degree (`coneMap_d`) and
`∂(b · c) = c - ε(c) · b` in degree zero (`coneMap_zero_d`), with the augmentation `ε`.

For a convex set `K` in the standard simplex `StdSimplex ℝ (Fin (m + 1))`, an affine simplex
with vertices in `K` is realized by the continuous affine map `realize hK σ` (vertex `i` goes
to `σ i`); the realized cone is `AffineMap.cone` (`coe_realize_cons`). For a continuous map
`e : C(K, Y)` into any `Y : TopCat`, `toSingular hK Y e` sends an affine simplex to the
singular simplex `e ∘ realize hK σ`, and `toSingularChains hK Y e R` is the induced chain map
into the singular chains of `Y`. It is a monomorphism of simplicial sets when `e` is
injective; `toSingular_comp` is its naturality in `Y`.
-/

namespace TDA.Topology.AffineChains

open CategoryTheory Limits Convexity Simplicial

noncomputable section

universe u v w

/-! ### The simplicial set of affine simplices -/

/-- The simplicial set whose `n`-simplices are the vertex tuples `Fin (n + 1) → X`; a
simplicial operator acts by precomposition with its monotone map. -/
def affineSSet (X : Type v) : SSet.{max u v} where
  obj n := ULift.{u} (Fin (n.unop.len + 1) → X)
  map f := ↾fun σ ↦ ULift.up (ULift.down σ ∘ f.unop.toOrderHom)
  map_id _ := rfl
  map_comp _ _ := rfl

namespace affineSSet

variable {X : Type v}

/-- The affine `n`-simplex with the given vertices. -/
def mk {n : ℕ} (σ : Fin (n + 1) → X) : (affineSSet.{u} X) _⦋n⦌ := ULift.up σ

/-- The vertices of an affine simplex. -/
def vertices {n : ℕ} (σ : (affineSSet.{u} X) _⦋n⦌) : Fin (n + 1) → X := ULift.down σ

@[simp] lemma vertices_mk {n : ℕ} (σ : Fin (n + 1) → X) :
    vertices (mk.{u} σ) = σ := rfl

@[simp] lemma mk_vertices {n : ℕ} (σ : (affineSSet.{u} X) _⦋n⦌) :
    mk (vertices σ) = σ := rfl

/-- Affine simplices of a fixed dimension are their vertex tuples. -/
def equiv (n : ℕ) : (Fin (n + 1) → X) ≃ (affineSSet.{u} X) _⦋n⦌ where
  toFun := mk
  invFun := vertices
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] lemma map_mk {n m : ℕ} (f : ⦋n⦌ ⟶ ⦋m⦌) (σ : Fin (m + 1) → X) :
    (affineSSet.{u} X).map f.op (mk σ) = mk (σ ∘ f.toOrderHom) := rfl

/-- The `i`-th face deletes the `i`-th vertex. -/
@[simp] lemma δ_mk {n : ℕ} (i : Fin (n + 2)) (σ : Fin (n + 2) → X) :
    (affineSSet.{u} X).δ i (mk σ) = mk (σ ∘ i.succAbove) := rfl

/-- The simplicial map induced by a map of vertex types. -/
def map {Y : Type v} (f : X → Y) : affineSSet.{u} X ⟶ affineSSet.{u} Y where
  app _ := ↾fun σ ↦ ULift.up (f ∘ ULift.down σ)

@[simp] lemma map_app_mk {Y : Type v} (f : X → Y) {n : ℕ} (σ : Fin (n + 1) → X) :
    (map.{u} f).app _ (mk σ) = mk (f ∘ σ) := rfl

end affineSSet

open affineSSet

/-! ### The cone and its boundary -/

variable {X : Type v}

/-- The cone `b · σ` on vertex tuples: the apex `b` is vertex `0`, and vertex `i + 1` is
vertex `i` of `σ`. -/
abbrev cone {n : ℕ} (b : X) (σ : Fin (n + 1) → X) : Fin (n + 2) → X := Fin.cons b σ

@[simp] lemma cone_comp_succAbove_zero {n : ℕ} (b : X) (σ : Fin (n + 1) → X) :
    cone b σ ∘ (0 : Fin (n + 2)).succAbove = σ := by
  funext j
  simp

@[simp] lemma cone_comp_succAbove_succ {n : ℕ} (b : X) (σ : Fin (n + 2) → X) (i : Fin (n + 2)) :
    cone b σ ∘ i.succ.succAbove = cone b (σ ∘ i.succAbove) := by
  funext j
  refine Fin.cases ?_ (fun j => ?_) j
  · simp
  · simp [Fin.succ_succAbove_succ]

variable {C : Type*} [Category* C] [HasCoproducts.{max u v} C] [Preadditive C] (R : C)

/-- The cone `b · c` on affine `n`-chains, sending the generator of `σ` to that of `b · σ`. -/
def coneMap (b : X) (n : ℕ) :
    ((affineSSet.{u} X).chainComplex R).X n ⟶ ((affineSSet.{u} X).chainComplex R).X (n + 1) :=
  Cofan.IsColimit.desc ((affineSSet.{u} X).isColimitChainComplexXCofan R n)
    (fun σ => (affineSSet.{u} X).ιChainComplex (mk (cone b (vertices σ))))

@[reassoc (attr := simp)]
lemma ιChainComplex_coneMap (b : X) {n : ℕ} (σ : Fin (n + 1) → X) :
    (affineSSet.{u} X).ιChainComplex (R := R) (mk σ) ≫ coneMap.{u} R b n =
      (affineSSet.{u} X).ιChainComplex (mk (cone b σ)) :=
  Cofan.IsColimit.fac ((affineSSet.{u} X).isColimitChainComplexXCofan R n) _ (mk σ)

section Augmentation

variable {D : Type*} [Category* D] [HasCoproducts.{w} D] [Preadditive D] (R' : D)

/-- The augmentation `ε` of a simplicial chain complex, sending each vertex generator
to `𝟙 R`. -/
def augmentation (S : SSet.{w}) : (S.chainComplex R').X 0 ⟶ R' :=
  Cofan.IsColimit.desc (S.isColimitChainComplexXCofan R' 0) (fun _ => 𝟙 R')

@[reassoc (attr := simp)]
lemma ιChainComplex_augmentation (S : SSet.{w}) (x : S _⦋0⦌) :
    S.ιChainComplex (R := R') x ≫ augmentation R' S = 𝟙 R' :=
  Cofan.IsColimit.fac (S.isColimitChainComplexXCofan R' 0) _ x

end Augmentation

/-- The boundary of a cone on an affine simplex in positive degree:
`∂(b · σ) = σ - b · ∂σ`, with Mathlib's face signs `(-1) ^ i`. -/
lemma ιChainComplex_coneMap_d (b : X) {n : ℕ} (σ : Fin (n + 2) → X) :
    (affineSSet.{u} X).ιChainComplex (R := R) (mk σ) ≫ coneMap.{u} R b (n + 1) ≫
        ((affineSSet.{u} X).chainComplex R).d (n + 2) (n + 1) =
      (affineSSet.{u} X).ιChainComplex (mk σ) -
        ∑ i : Fin (n + 2), (-1) ^ i.val •
          (affineSSet.{u} X).ιChainComplex (mk (cone b (σ ∘ i.succAbove))) := by
  rw [ιChainComplex_coneMap_assoc, SSet.ιChainComplex_d, Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_smul, δ_mk, cone_comp_succAbove_zero,
    cone_comp_succAbove_succ, Fin.val_succ, pow_succ, mul_neg, mul_one, neg_smul,
    Finset.sum_neg_distrib, sub_eq_add_neg]

/-- **Cone boundary formula** in positive degree: `∂(b · c) = c - b · ∂c` for affine
chains `c` of degree `n + 1`. -/
theorem coneMap_d (b : X) (n : ℕ) :
    coneMap.{u} R b (n + 1) ≫ ((affineSSet.{u} X).chainComplex R).d (n + 2) (n + 1) =
      𝟙 _ - ((affineSSet.{u} X).chainComplex R).d (n + 1) n ≫ coneMap.{u} R b n := by
  ext σ
  obtain ⟨σ, rfl⟩ : ∃ τ, mk τ = σ := ⟨vertices σ, rfl⟩
  rw [ιChainComplex_coneMap_d, Preadditive.comp_sub, Category.comp_id,
    SSet.ιChainComplex_d_assoc, Preadditive.sum_comp]
  simp [δ_mk]

/-- **Cone boundary formula** in degree zero: `∂(b · c) = c - ε(c) · b`, where `ε` is the
augmentation and `b` is the vertex generator of the apex. -/
theorem coneMap_zero_d (b : X) :
    coneMap.{u} R b 0 ≫ ((affineSSet.{u} X).chainComplex R).d 1 0 =
      𝟙 _ - augmentation R (affineSSet.{u} X) ≫
        (affineSSet.{u} X).ιChainComplex (mk (fun _ : Fin 1 => b)) := by
  ext σ
  obtain ⟨σ, rfl⟩ : ∃ τ, mk τ = σ := ⟨vertices σ, rfl⟩
  rw [ιChainComplex_coneMap_assoc, SSet.ιChainComplex_d, Fin.sum_univ_two,
    Preadditive.comp_sub, Category.comp_id, ιChainComplex_augmentation_assoc]
  have h1 : cone b σ ∘ (1 : Fin 2).succAbove = fun _ => b := by
    funext j
    simp [Fin.fin_one_eq_zero j]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_smul, δ_mk,
    cone_comp_succAbove_zero, h1, sub_eq_add_neg]

/-- The cone commutes with the chain map of a map of vertex types. -/
@[reassoc]
theorem coneMap_comp_chainComplexMap {Y : Type v} (f : X → Y) (b : X) (n : ℕ) :
    coneMap.{u} R b n ≫ (SSet.chainComplexMap (map.{u} f) R).f (n + 1) =
      (SSet.chainComplexMap (map.{u} f) R).f n ≫ coneMap.{u} R (f b) n := by
  ext σ
  obtain ⟨σ, rfl⟩ : ∃ τ, mk τ = σ := ⟨vertices σ, rfl⟩
  rw [ιChainComplex_coneMap_assoc, SSet.ι_chainComplexMap_f, SSet.ι_chainComplexMap_f_assoc,
    map_app_mk, map_app_mk, ιChainComplex_coneMap]
  congr 2
  funext j
  refine Fin.cases ?_ (fun j => ?_) j <;> simp

/-! ### Realization in a convex subset of the standard simplex -/

variable {m : ℕ} {K : Set (StdSimplex ℝ (Fin (m + 1)))} (hK : IsConvexSet ℝ K)

/-- The realized affine simplex: the affine map from the standard `n`-simplex to `K` that
sends vertex `i` to `v i`. -/
def realize {n : ℕ} (σ : Fin (n + 1) → K) : C(StdSimplex ℝ (Fin (n + 1)), K) where
  toFun t := ⟨StdSimplex.affineMapMk (Subtype.val ∘ σ) t,
    hK.iConvexComb_mem (fun i _ => (σ i).2)⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    refine (StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (m + 1))).continuous_iff.mpr ?_
    have hf : IsAffineMap ℝ fun t : StdSimplex ℝ (Fin (n + 1)) =>
        (StdSimplex.affineMapMk (Subtype.val ∘ σ) t).weights :=
      (StdSimplex.isAffineMap_weights ℝ (Fin (m + 1))).comp
        (StdSimplex.affineMapMk (Subtype.val ∘ σ)).isAffineMap
    exact continuous_pi fun j => StdSimplex.continuous_of_isAffineMap _
      ((IsAffineMap.linearMap (Finsupp.lapply (R := ℝ) (M := ℝ) j)).comp hf)

@[simp] lemma coe_realize_apply {n : ℕ} (σ : Fin (n + 1) → K) (t : StdSimplex ℝ (Fin (n + 1))) :
    (realize hK σ t : StdSimplex ℝ (Fin (m + 1))) = StdSimplex.affineMapMk (Subtype.val ∘ σ) t :=
  rfl

@[simp] lemma realize_single {n : ℕ} (σ : Fin (n + 1) → K) (i : Fin (n + 1)) :
    realize hK σ (.single i) = σ i := by
  ext1
  simp

/-- Precomposing the vertices with `f` realizes as precomposition with `StdSimplex.map f`. -/
lemma realize_comp {n k : ℕ} (σ : Fin (n + 1) → K) (f : Fin (k + 1) → Fin (n + 1))
    (t : StdSimplex ℝ (Fin (k + 1))) :
    realize hK (σ ∘ f) t = realize hK σ (StdSimplex.map f t) := by
  ext1
  simp [StdSimplex.affineMapMk_apply, Function.comp_def]

/-- The realized cone is `AffineMap.cone` of the realized simplex. -/
lemma coe_realize_cons {n : ℕ} (b : K) (σ : Fin (n + 1) → K) :
    (fun t => (realize hK (cone b σ) t : StdSimplex ℝ (Fin (m + 1)))) =
      ⇑((StdSimplex.affineMapMk (R := ℝ) (Subtype.val ∘ σ)).cone b.1) := by
  funext t
  rw [coe_realize_apply, ConvexSpace.AffineMap.cone_def]
  congr 2
  funext j
  refine Fin.cases ?_ (fun j => ?_) j <;> simp

/-- An affine map of ambient simplices carrying `K` into `K'` commutes with realization. -/
lemma coe_realize_mapsTo {m' : ℕ} {K' : Set (StdSimplex ℝ (Fin (m' + 1)))}
    (hK' : IsConvexSet ℝ K')
    (F : ConvexSpace.AffineMap ℝ (StdSimplex ℝ (Fin (m + 1))) (StdSimplex ℝ (Fin (m' + 1))))
    (hF : Set.MapsTo F K K') {n : ℕ} (σ : Fin (n + 1) → K) (t : StdSimplex ℝ (Fin (n + 1))) :
    (realize hK' (hF.restrict F K K' ∘ σ) t : StdSimplex ℝ (Fin (m' + 1))) =
      F (realize hK σ t) := by
  rw [coe_realize_apply, coe_realize_apply]
  exact (congrArg (fun g => g t) (StdSimplex.comp_affineMapMk F (Subtype.val ∘ σ))).symm

lemma realize_injective {n : ℕ} : Function.Injective (realize (n := n) hK) := by
  intro σ τ h
  funext i
  simpa using congrArg (fun g : C(StdSimplex ℝ (Fin (n + 1)), K) => g (.single i)) h

/-! ### Affine chains in singular chains -/

/-- Affine simplices of `K` as singular simplices of `Y` through a continuous `e : C(K, Y)`. -/
def toSingular (Y : TopCat.{u}) (e : C(K, Y)) : affineSSet.{u} K ⟶ TopCat.toSSet.obj Y where
  app n := ↾fun σ ↦ (Y.toSSetObjEquiv n).symm (e.comp (realize hK (ULift.down σ)))
  naturality n n' f := by
    obtain ⟨f, rfl⟩ : ∃ g, f = Quiver.Hom.op g := ⟨f.unop, rfl⟩
    ext σ
    change (Y.toSSetObjEquiv _).symm _ =
      (TopCat.toSSet.obj Y).map f.op ((Y.toSSetObjEquiv _).symm _)
    rw [TopCat.toSSetObjEquiv_symm_naturality]
    congr 1
    ext t
    exact congrArg e (realize_comp hK σ.down f.toOrderHom t)

@[simp] lemma toSingular_app_mk (Y : TopCat.{u}) (e : C(K, Y)) {n : ℕ} (σ : Fin (n + 1) → K) :
    (toSingular hK Y e).app _ (mk σ) = (Y.toSSetObjEquiv _).symm (e.comp (realize hK σ)) :=
  rfl

/-- `toSingular` is natural in the target space. -/
lemma toSingular_comp (Y Y' : TopCat.{u}) (e : C(K, Y)) (g : Y ⟶ Y') :
    toSingular hK Y e ≫ TopCat.toSSet.map g = toSingular hK Y' (g.hom.comp e) := rfl

/-- For an injective `e`, distinct affine simplices give distinct singular simplices. -/
theorem mono_toSingular (Y : TopCat.{u}) (e : C(K, Y)) (he : Function.Injective e) :
    Mono (toSingular hK Y e) := by
  have (n : SimplexCategoryᵒᵖ) : Mono ((toSingular hK Y e).app n) := by
    refine (mono_iff_injective _).2 fun σ τ h => ?_
    have h₁ := (Y.toSSetObjEquiv n).symm.injective h
    have h₂ : realize hK (ULift.down σ) = realize hK (ULift.down τ) := by
      ext t : 1
      exact he (DFunLike.congr_fun h₁ t)
    exact congrArg ULift.up (realize_injective hK h₂)
  exact NatTrans.mono_of_mono_app _

/-- The chain map from affine chains of `K` to singular chains of `Y`. -/
abbrev toSingularChains (Y : TopCat.{u}) (e : C(K, Y)) {C : Type*} [Category* C]
    [HasCoproducts.{u} C] [Preadditive C] (R : C) :
    (affineSSet.{u} K).chainComplex R ⟶
      ((AlgebraicTopology.singularChainComplexFunctor C).obj R).obj Y :=
  SSet.chainComplexMap (toSingular hK Y e) R

end

end TDA.Topology.AffineChains
