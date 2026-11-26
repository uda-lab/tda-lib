import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Basic
import Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex
import Mathlib.CategoryTheory.Limits.Preserves.SigmaConst
import Mathlib.Topology.Category.TopCat.EpiMono

/-!
# Small singular chains of a pair of subsets

For a space `Y : TopCat.{u}` and a subset `s`, `simplicesIn s` is the subcomplex of the singular
simplicial set `TopCat.toSSet.obj Y` formed by the singular simplices whose image lies in `s`
(`mem_simplicesIn_iff`). It is the range of `TopCat.toSSet` applied to the subspace inclusion
`subsetIncl s`, and `toSSetSubsetIso s` identifies it with the singular simplicial set of the
subspace, so `singularChainsSubsetIso s R` identifies the singular chains of `s` with the chains of
`simplicesIn s`. More generally, `range_toSSet_map_eq_simplicesIn` computes the range of
`TopCat.toSSet.map g` for an embedding `g`.

For two subsets `s` and `t`, `smallSimplices s t = simplicesIn s ⊔ simplicesIn t` consists of the
singular simplices lying wholly in `s` or wholly in `t` (`mem_smallSimplices_iff`), and
`simplicesIn_inter` identifies `simplicesIn (s ∩ t)` with `simplicesIn s ⊓ simplicesIn t`.
`smallChains s t R` is the chain complex of `smallSimplices s t` with coefficients `R`, and
`smallChainsι s t R` its inclusion into all singular chains of `Y`, a monomorphism.

No openness or other assumption on `s` and `t` is made here. The short exact Mayer–Vietoris
sequence of small chains is in `TDA.Topology.SingularMayerVietoris`.
-/

open CategoryTheory Limits AlgebraicTopology Opposite
open scoped Simplicial

universe u

namespace TDA.Topology

/-- The inclusion of a subset `s` of a space `Y` as a morphism of `TopCat`. -/
def subsetIncl {Y : TopCat.{u}} (s : Set Y) : TopCat.of s ⟶ Y :=
  TopCat.ofHom (ContinuousMap.subtypeVal s)

@[simp]
theorem subsetIncl_apply {Y : TopCat.{u}} (s : Set Y) (x : TopCat.of s) :
    subsetIncl s x = x.1 :=
  rfl

/-- `TopCat.toSSet` acts on singular simplices by post-composition. -/
theorem toSSetObjEquiv_map {X Y : TopCat.{u}} (f : X ⟶ Y) (n : SimplexCategoryᵒᵖ)
    (σ : (TopCat.toSSet.obj X).obj n) :
    Y.toSSetObjEquiv n ((TopCat.toSSet.map f).app n σ) = f.hom.comp (X.toSSetObjEquiv n σ) :=
  rfl

/-- The singular simplices of `Y` whose image lies in `s`, as a subcomplex of `toSSet Y`. -/
noncomputable def simplicesIn {Y : TopCat.{u}} (s : Set Y) : (TopCat.toSSet.obj Y).Subcomplex :=
  SSet.Subcomplex.range (TopCat.toSSet.map (subsetIncl s))

/-- A singular simplex lies in `simplicesIn s` exactly when its image is contained in `s`. -/
theorem mem_simplicesIn_iff {Y : TopCat.{u}} (s : Set Y) {n : SimplexCategoryᵒᵖ}
    (σ : (TopCat.toSSet.obj Y).obj n) :
    σ ∈ (simplicesIn s).obj n ↔ Set.range (Y.toSSetObjEquiv n σ) ⊆ s := by
  constructor
  · rintro ⟨τ, rfl⟩ _ ⟨p, rfl⟩
    rw [toSSetObjEquiv_map]
    exact ((TopCat.toSSetObjEquiv _ n τ) p).2
  · intro h
    let τ' : C(_, TopCat.of s) :=
      ⟨fun p => ⟨Y.toSSetObjEquiv n σ p, h ⟨p, rfl⟩⟩,
        (Y.toSSetObjEquiv n σ).continuous.subtype_mk _⟩
    refine ⟨((TopCat.of s).toSSetObjEquiv n).symm τ', ?_⟩
    apply (Y.toSSetObjEquiv n).injective
    rw [toSSetObjEquiv_map, Equiv.apply_symm_apply]
    rfl

/-- `simplicesIn` is monotone in the subset. -/
theorem simplicesIn_mono {Y : TopCat.{u}} {s t : Set Y} (h : s ⊆ t) :
    simplicesIn s ≤ simplicesIn t := by
  intro n σ hσ
  rw [mem_simplicesIn_iff] at hσ ⊢
  exact hσ.trans h

/-- The simplices in an intersection are those lying in both subsets. -/
theorem simplicesIn_inter {Y : TopCat.{u}} (s t : Set Y) :
    simplicesIn (s ∩ t) = simplicesIn s ⊓ simplicesIn t := by
  ext n σ
  change σ ∈ (simplicesIn (s ∩ t)).obj n ↔ σ ∈ (simplicesIn s).obj n ∧ σ ∈ (simplicesIn t).obj n
  simp only [mem_simplicesIn_iff, Set.subset_inter_iff]

/-- The whole space carries every singular simplex. -/
theorem simplicesIn_univ (Y : TopCat.{u}) : simplicesIn (Set.univ : Set Y) = ⊤ := by
  ext n σ
  change σ ∈ (simplicesIn (Set.univ : Set Y)).obj n ↔ True
  simp only [mem_simplicesIn_iff, Set.subset_univ]

/-- The small simplices for the pair `s, t`: those lying wholly in `s` or wholly in `t`. -/
noncomputable def smallSimplices {Y : TopCat.{u}} (s t : Set Y) :
    (TopCat.toSSet.obj Y).Subcomplex :=
  simplicesIn s ⊔ simplicesIn t

/-- A singular simplex is small exactly when its image lies in `s` or in `t`. -/
theorem mem_smallSimplices_iff {Y : TopCat.{u}} (s t : Set Y) {n : SimplexCategoryᵒᵖ}
    (σ : (TopCat.toSSet.obj Y).obj n) :
    σ ∈ (smallSimplices s t).obj n ↔
      Set.range (Y.toSSetObjEquiv n σ) ⊆ s ∨ Set.range (Y.toSSetObjEquiv n σ) ⊆ t := by
  change σ ∈ (simplicesIn s).obj n ∨ σ ∈ (simplicesIn t).obj n ↔ _
  rw [mem_simplicesIn_iff, mem_simplicesIn_iff]

instance mono_toSSet_map_subsetIncl {Y : TopCat.{u}} (s : Set Y) :
    Mono (TopCat.toSSet.map (subsetIncl s)) := by
  have : Mono (subsetIncl s) := (TopCat.mono_iff_injective _).2 Subtype.val_injective
  infer_instance

/-- `toSSet` of the subspace `s` is isomorphic to the subcomplex `simplicesIn s`. -/
noncomputable def toSSetSubsetIso {Y : TopCat.{u}} (s : Set Y) :
    TopCat.toSSet.obj (TopCat.of s) ≅ (simplicesIn s : SSet.{u}) :=
  @asIso _ _ _ _ (SSet.Subcomplex.toRange (TopCat.toSSet.map (subsetIncl s)))
    (SSet.Subcomplex.instIsIsoToRangeOfMono _)

/-- The isomorphism `toSSetSubsetIso s` followed by the inclusion is `toSSet` of the inclusion. -/
@[reassoc (attr := simp)]
theorem toSSetSubsetIso_hom_ι {Y : TopCat.{u}} (s : Set Y) :
    (toSSetSubsetIso s).hom ≫ (simplicesIn s).ι = TopCat.toSSet.map (subsetIncl s) :=
  SSet.Subcomplex.toRange_ι _

/-- For an embedding `g`, the singular simplices factoring through `g` are those with image in
`Set.range g`. -/
theorem range_toSSet_map_eq_simplicesIn {A Y : TopCat.{u}} (g : A ⟶ Y)
    (hg : Topology.IsEmbedding g) :
    SSet.Subcomplex.range (TopCat.toSSet.map g) = simplicesIn (Set.range g) := by
  ext n σ
  change σ ∈ Set.range ((TopCat.toSSet.map g).app n) ↔ σ ∈ (simplicesIn (Set.range g)).obj n
  rw [mem_simplicesIn_iff]
  constructor
  · rintro ⟨τ, rfl⟩ _ ⟨p, rfl⟩
    rw [toSSetObjEquiv_map]
    exact ⟨_, rfl⟩
  · intro h
    choose τ hτ using fun p => h ⟨p, rfl⟩
    have hc : Continuous τ := by
      refine hg.isInducing.continuous_iff.2 ?_
      have e : (⇑g ∘ τ) = Y.toSSetObjEquiv n σ := funext hτ
      rw [e]
      exact (Y.toSSetObjEquiv n σ).continuous
    refine ⟨(A.toSSetObjEquiv n).symm ⟨τ, hc⟩, ?_⟩
    apply (Y.toSSetObjEquiv n).injective
    rw [toSSetObjEquiv_map, Equiv.apply_symm_apply]
    ext p
    exact hτ p

section Chains

variable {C : Type*} [Category C] [HasCoproducts.{u} C] [Preadditive C]

/-- The small chain complex `C^small(s, t; R)`: chains of simplices lying in `s` or in `t`. -/
noncomputable abbrev smallChains {Y : TopCat.{u}} (s t : Set Y) (R : C) : ChainComplex C ℕ :=
  (smallSimplices s t : SSet.{u}).chainComplex R

/-- The inclusion `C^small(s, t; R) ⟶ C(Y; R)` of small chains into all singular chains. -/
noncomputable abbrev smallChainsι {Y : TopCat.{u}} (s t : Set Y) (R : C) :
    smallChains s t R ⟶ ((singularChainComplexFunctor C).obj R).obj Y :=
  SSet.chainComplexMap (smallSimplices s t).ι R

/-- The singular chains of the subspace `s` are the chains of the subcomplex `simplicesIn s`. -/
noncomputable def singularChainsSubsetIso {Y : TopCat.{u}} (s : Set Y) (R : C) :
    ((singularChainComplexFunctor C).obj R).obj (TopCat.of s) ≅
      (simplicesIn s : SSet.{u}).chainComplex R :=
  ((SSet.chainComplexFunctor C).obj R).mapIso (toSSetSubsetIso s)

/-- Under `singularChainsSubsetIso`, the inclusion of `simplicesIn s` is the map induced by the
subspace inclusion. -/
@[reassoc (attr := simp)]
theorem singularChainsSubsetIso_hom_comp_chainComplexMap_ι {Y : TopCat.{u}} (s : Set Y) (R : C) :
    (singularChainsSubsetIso s R).hom ≫ SSet.chainComplexMap (simplicesIn s).ι R =
      ((singularChainComplexFunctor C).obj R).map (subsetIncl s) := by
  change ((SSet.chainComplexFunctor C).obj R).map (toSSetSubsetIso s).hom ≫
      ((SSet.chainComplexFunctor C).obj R).map (simplicesIn s).ι = _
  rw [← Functor.map_comp, toSSetSubsetIso_hom_ι]
  rfl

end Chains

section Mono

variable {C : Type*} [Category C] [Abelian C] [HasCoproducts.{u} C]

/-- The chain map of an inclusion of subcomplexes is a monomorphism. -/
instance mono_chainComplexMap_homOfLE {X : SSet.{u}} {A B : X.Subcomplex} (h : A ≤ B) (R : C) :
    Mono (SSet.chainComplexMap (SSet.Subcomplex.homOfLE h) R) :=
  HomologicalComplex.mono_of_mono_f _ fun n =>
    inferInstanceAs (Mono ((sigmaConst.obj R).map ((SSet.Subcomplex.homOfLE h).app (op ⦋n⦌))))

/-- The chain map of the inclusion of a subcomplex is a monomorphism. -/
instance mono_chainComplexMap_ι {X : SSet.{u}} (A : X.Subcomplex) (R : C) :
    Mono (SSet.chainComplexMap A.ι R) :=
  HomologicalComplex.mono_of_mono_f _ fun n =>
    inferInstanceAs (Mono ((sigmaConst.obj R).map (A.ι.app (op ⦋n⦌))))

/-- The inclusion of small chains into all singular chains is a monomorphism. -/
instance mono_smallChainsι {Y : TopCat.{u}} (s t : Set Y) (R : C) : Mono (smallChainsι s t R) :=
  HomologicalComplex.mono_of_mono_f _ fun n =>
    inferInstanceAs (Mono ((sigmaConst.obj R).map ((smallSimplices s t).ι.app (op ⦋n⦌))))

end Mono

end TDA.Topology
