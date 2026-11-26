import TDA.Topology.SingularSubdivision
import TDA.Topology.SingularMayerVietoris
import TDA.Topology.QuasiIsoOfIterate
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Geometry.Convex.ConvexSpace.CompactSpaceStdSimplex
import Mathlib.LinearAlgebra.Finsupp.Pi
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# Small chains of a cover compute singular homology

Let `s` and `t` be subsets of a space `X` whose interiors cover `X`. This module shows that the
inclusion `smallChainsι s t M` of the chains of simplices lying in `s` or in `t` into all
singular chains of `X` is a quasi-isomorphism, for coefficients in any module `M` over a ring
`k` (`quasiIso_smallChainsι`). The proof applies the iteration criterion
`quasiIso_of_iterate_mem` to singular subdivision and its homotopy to the identity; the remaining
hypothesis, that every chain becomes small after enough subdivisions, is proved in three steps.

* **The Lebesgue step on the model simplex.** For an open cover of the model `n`-simplex there is
  an `N` such that, for every `N' ≥ N`, each simplex of the `N'`-fold barycentric subdivision of
  the identity simplex lies in one member of the cover
  (`exists_isIteratedSubdivisionSimplex_subset`). Distances are measured on the weight vectors in
  `Fin (n + 1) → ℝ`; the cover has a Lebesgue number on the compact simplex, and the diameters of
  subdivision simplices are bounded by `(n / (n + 1)) ^ N'` times that of the simplex.
* **From the model to singular chains.** Applying this to the cover of the model by the preimages
  of the interiors of `s` and `t` under a singular simplex `σ`, every iterate `sd^{N'}` with
  `N' ≥ N` carries the generators of `σ` into small chains
  (`exists_iterate_singularSubdivision_ιChainComplex_mem_range`), since singular subdivision is
  `σ_*` of the affine subdivision of the identity simplex.
* **Finite support.** The simplicial `n`-chains with coefficients in `M` are spanned by the
  images of the summand inclusions (`iSup_range_ιChainComplex`), so every chain is a finite sum
  of generators and the maximum of their `N` works
  (`exists_iterate_singularSubdivision_mem_range_smallChainsι`).

With the short exact sequence `shortExact_smallChains` this gives the **Mayer–Vietoris long exact
sequence** in singular homology,

`⋯ ⟶ H_{n+1}(X) ⟶ H_n(s ∩ t) ⟶ H_n(s) ⊞ H_n(t) ⟶ H_n(X) ⟶ ⋯`,

where the first map is the connecting map `mayerVietorisδ`, the second map
`mayerVietorisInterMap` is `(inc, -inc)` and the third map `mayerVietorisSumMap` is the sum of the
inclusions. It is exact at `H_n(s ∩ t)` (`mayerVietoris_exact_inter`), at `H_n(s) ⊞ H_n(t)`
(`mayerVietoris_exact_sum`) and at `H_{n+1}(X)` (`mayerVietoris_exact_space`). The connecting map
is the inverse of the quasi-isomorphism on homology followed by the connecting map `bicartδ` of
small chains, whose sign is described by `bicartδ_eq`.
-/

namespace TDA.Topology

open CategoryTheory Limits Convexity Simplicial AlgebraicTopology Opposite HomologicalComplex
open AffineChains affineSSet

noncomputable section

universe u

/-! ### The Lebesgue step on the model simplex -/

/-- The weight vector of a point of a standard simplex, as a function. -/
private abbrev weightVector (n : ℕ) : (Fin (n + 1) →₀ ℝ) →ₗ[ℝ] Fin (n + 1) → ℝ :=
  Finsupp.lcoeFun

/-- The weight vector embeds the model simplex in `Fin (n + 1) → ℝ`. -/
private theorem isEmbedding_position_weightVector (n : ℕ) :
    Topology.IsEmbedding (position (K := modelSimplex n) (weightVector n)) :=
  (StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n + 1))).comp
    Topology.IsEmbedding.subtypeVal

/-- **The Lebesgue step on the model simplex.** For an open cover `c` of the model `n`-simplex
there is an `N` such that, for every `N' ≥ N`, every simplex of the `N'`-fold barycentric
subdivision of the identity simplex lies in one member of the cover. -/
theorem exists_isIteratedSubdivisionSimplex_subset {n : ℕ} {ι : Sort*}
    {c : ι → Set (modelSimplex n)} (hc : ∀ i, IsOpen (c i)) (hcov : ⋃ i, c i = Set.univ) :
    ∃ N : ℕ, ∀ N' ≥ N, ∀ τ : Fin (n + 1) → modelSimplex n,
      IsIteratedSubdivisionSimplex (isConvexSet_modelSimplex n) N' (idSimplex n) τ →
        ∃ i, Set.range (realize (isConvexSet_modelSimplex n) τ) ⊆ c i := by
  have hp := isEmbedding_position_weightVector n
  choose O hO hOc using fun i => hp.isInducing.isOpen_iff.1 (hc i)
  have : CompactSpace (modelSimplex n) := isCompact_iff_compactSpace.mp isCompact_univ
  have hsub : Set.range (position (K := modelSimplex n) (weightVector n)) ⊆ ⋃ i, O i := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (hcov.symm ▸ Set.mem_univ x : x ∈ ⋃ i, c i)
    exact Set.mem_iUnion.2 ⟨i, by rw [← hOc i] at hi; exact hi⟩
  obtain ⟨δ, hδ, hball⟩ := lebesgue_number_lemma_of_metric (isCompact_range hp.continuous) hO hsub
  set D := Metric.diam (Set.range (position (weightVector n) ∘
    realize (isConvexSet_modelSimplex n) (idSimplex n)))
  set r : ℝ := n / (n + 1)
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := by
    rw [div_lt_one (by positivity)]
    linarith
  have hlim : Filter.Tendsto (fun N : ℕ => r ^ N * D) Filter.atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).mul_const D
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (hlim.eventually (gt_mem_nhds hδ))
  refine ⟨N, fun N' hN' τ hτ => ?_⟩
  have hdiam : Metric.diam (Set.range (position (weightVector n) ∘
      realize (isConvexSet_modelSimplex n) τ)) < δ :=
    hτ.diam_range_realize_le.trans_lt
      ((mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hr0 hr1.le hN')
        Metric.diam_nonneg).trans_lt (hN N le_rfl))
  obtain ⟨i, hi⟩ := hball _ ⟨realize (isConvexSet_modelSimplex n) τ StdSimplex.barycenter, rfl⟩
  refine ⟨i, ?_⟩
  rintro _ ⟨x, rfl⟩
  rw [← hOc i]
  apply hi
  rw [Metric.mem_ball]
  exact (Metric.dist_le_diam_of_mem (isBounded_range_position_realize _ τ) ⟨x, rfl⟩
    ⟨_, rfl⟩).trans_lt hdiam

/-! ### Finite support of simplicial chains -/

section Support

variable {k : Type u} [Ring k]

/-- The simplicial `n`-chains with coefficients in a module `M` are spanned by the images of the
summand inclusions `ιChainComplex x`. -/
theorem iSup_range_ιChainComplex (S : SSet.{u}) (M : ModuleCat.{u} k) (n : ℕ) :
    ⨆ x : S _⦋n⦌, LinearMap.range (S.ιChainComplex (R := M) x).hom = ⊤ := by
  set W := ⨆ x : S _⦋n⦌, LinearMap.range (S.ιChainComplex (R := M) x).hom
  have h : (ModuleCat.ofHom W.mkQ : (S.chainComplex M).X n ⟶ ModuleCat.of k (_ ⧸ W)) = 0 := by
    refine SSet.chainComplex_hom_ext fun x => ?_
    ext r
    exact (Submodule.Quotient.mk_eq_zero W).2 (le_iSup (fun x => LinearMap.range
      (S.ιChainComplex (R := M) x).hom) x ⟨r, rfl⟩)
  rw [eq_top_iff]
  intro y _
  exact (Submodule.Quotient.mk_eq_zero W).1 (congrArg (fun f => f.hom y) h)

end Support

/-! ### From the model to singular chains -/

section ModuleCat

variable {k : Type u} [Ring k] {X : TopCat.{u}} (s t : Set X) (M : ModuleCat.{u} k)

/-- The singular simplex `σ_*(τ)` of an affine simplex `τ` of the model whose image under `σ` lies
in `s` or in `t` is small. -/
private theorem toSingularChains_ιChainComplex_mem_range {n : ℕ}
    (σ : (TopCat.toSSet.obj X) _⦋n⦌) (τ : Fin (n + 1) → modelSimplex n)
    (hτ : Set.range (realize (isConvexSet_modelSimplex n) τ) ⊆ modelMap σ ⁻¹' s ∨
      Set.range (realize (isConvexSet_modelSimplex n) τ) ⊆ modelMap σ ⁻¹' t) (r : M) :
    ((affineSSet.{u} (modelSimplex n)).ιChainComplex (R := M) (mk τ) ≫
        (toSingularChains (isConvexSet_modelSimplex n) X (modelMap σ) M).f n).hom r ∈
      LinearMap.range ((smallChainsι s t M).f n).hom := by
  have hmem : (toSingular (isConvexSet_modelSimplex n) X (modelMap σ)).app _ (mk τ) ∈
      (smallSimplices s t).obj (op ⦋n⦌) := by
    rw [mem_smallSimplices_iff, toSingular_app_mk, Equiv.apply_symm_apply, ContinuousMap.coe_comp,
      Set.range_comp, Set.image_subset_iff, Set.image_subset_iff]
    exact hτ
  rw [SSet.ι_chainComplexMap_f]
  exact ⟨((smallSimplices s t : SSet.{u}).ιChainComplex (R := M) ⟨_, hmem⟩).hom r,
    congrArg (fun φ : M ⟶ ((TopCat.toSSet.obj X).chainComplex M).X n => φ.hom r)
      (SSet.ι_chainComplexMap_f _ _ (smallSimplices s t).ι M _)⟩

/-- The iterated affine subdivision of the identity simplex, evaluated at `r`, is the value at `r`
of an integer combination of simplices of the iterated subdivision. -/
private theorem exists_iterate_affineSubdivision_eq (n N : ℕ) :
    ∃ g ∈ AddSubgroup.closure {f | ∃ τ, IsIteratedSubdivisionSimplex (isConvexSet_modelSimplex n)
        N (idSimplex n) τ ∧ f = (affineSSet.{u} (modelSimplex n)).ιChainComplex (R := M) (mk τ)},
      ∀ r : M, (⇑((affineSubdivision (isConvexSet_modelSimplex n) M).f n).hom)^[N]
        (((affineSSet.{u} (modelSimplex n)).ιChainComplex (R := M) (mk (idSimplex n))).hom r) =
          g.hom r := by
  induction N with
  | zero => exact ⟨_, AddSubgroup.subset_closure ⟨_, .zero _, rfl⟩, fun r => rfl⟩
  | succ N ih =>
    obtain ⟨g, hg, hgr⟩ := ih
    refine ⟨g ≫ (affineSubdivision (isConvexSet_modelSimplex n) M).f n,
      comp_affineSubdivision_mem_closure _ M hg, fun r => ?_⟩
    rw [Function.iterate_succ_apply', hgr]
    rfl

/-- **From the model to singular chains.** If the interiors of `s` and `t` cover `X`, then for
every singular simplex `σ` there is an `N` such that, for every `N' ≥ N`, the `N'`-fold singular
subdivision of every chain `r · σ` is small. -/
theorem exists_iterate_singularSubdivision_ιChainComplex_mem_range
    (h : interior s ∪ interior t = Set.univ) {n : ℕ} (σ : (TopCat.toSSet.obj X) _⦋n⦌) :
    ∃ N : ℕ, ∀ N' ≥ N, ∀ r : M,
      (⇑((singularSubdivision M X).f n).hom)^[N']
          (((TopCat.toSSet.obj X).ιChainComplex (R := M) σ).hom r) ∈
        LinearMap.range ((smallChainsι s t M).f n).hom := by
  obtain ⟨N, hN⟩ := exists_isIteratedSubdivisionSimplex_subset (n := n)
    (c := fun b : Bool => modelMap σ ⁻¹' cond b (interior s) (interior t))
    (fun b => by cases b <;> exact isOpen_interior.preimage (modelMap σ).continuous)
    (Set.iUnion_eq_univ_iff.2 fun x => by
      have hx : modelMap σ x ∈ interior s ∪ interior t := by rw [h]; trivial
      rcases hx with hx | hx
      · exact ⟨true, hx⟩
      · exact ⟨false, hx⟩)
  refine ⟨N, fun N' hN' r => ?_⟩
  obtain ⟨g, hg, hgr⟩ := exists_iterate_affineSubdivision_eq M n N'
  have hsemi : Function.Semiconj
      (⇑((toSingularChains (isConvexSet_modelSimplex n) X (modelMap σ) M).f n).hom)
      (⇑((affineSubdivision (isConvexSet_modelSimplex n) M).f n).hom)
      (⇑((singularSubdivision M X).f n).hom) := fun a =>
    (congrArg (fun φ => φ.hom a) (HomologicalComplex.congr_hom
      (toSingularChains_comp_singularSubdivision M (isConvexSet_modelSimplex n) X
        (modelMap σ)) n)).symm
  have hσ : ((TopCat.toSSet.obj X).ιChainComplex (R := M) σ).hom r =
      ((toSingularChains (isConvexSet_modelSimplex n) X (modelMap σ) M).f n).hom
        (((affineSSet.{u} (modelSimplex n)).ιChainComplex (R := M) (mk (idSimplex n))).hom r) :=
    (congrArg (fun φ => φ.hom r) (ιChainComplex_idSimplex_toSingularChains M σ)).symm
  rw [hσ, ← hsemi.iterate_right N' _, hgr]
  let Φ : (M ⟶ ((affineSSet.{u} (modelSimplex n)).chainComplex M).X n) →+
      ((TopCat.toSSet.obj X).chainComplex M).X n :=
    AddMonoidHom.mk'
      (fun g => (g ≫ (toSingularChains (isConvexSet_modelSimplex n) X (modelMap σ) M).f n).hom r)
      (fun a b => by simp [Preadditive.add_comp])
  have hle : AddSubgroup.closure {f | ∃ τ, IsIteratedSubdivisionSimplex
      (isConvexSet_modelSimplex n) N' (idSimplex n) τ ∧
        f = (affineSSet.{u} (modelSimplex n)).ιChainComplex (R := M) (mk τ)} ≤
      (LinearMap.range ((smallChainsι s t M).f n).hom).toAddSubgroup.comap Φ := by
    rw [AddSubgroup.closure_le]
    rintro _ ⟨τ, hτ, rfl⟩
    obtain ⟨b, hb⟩ := hN N' hN' τ hτ
    refine toSingularChains_ιChainComplex_mem_range s t M σ τ ?_ r
    cases b
    · exact Or.inr (hb.trans (Set.preimage_mono interior_subset))
    · exact Or.inl (hb.trans (Set.preimage_mono interior_subset))
  exact hle hg

/-- **Every chain becomes small.** If the interiors of `s` and `t` cover `X`, every singular chain
is carried into the small chains by some iterate of singular subdivision: the hypothesis
`hsmall` of `quasiIso_of_iterate_mem`. -/
theorem exists_iterate_singularSubdivision_mem_range_smallChainsι
    (h : interior s ∪ interior t = Set.univ) (n : ℕ)
    (b : ((TopCat.toSSet.obj X).chainComplex M).X n) :
    ∃ N : ℕ, (⇑((singularSubdivision M X).f n).hom)^[N] b ∈
      LinearMap.range ((smallChainsι s t M).f n).hom := by
  suffices ∃ N : ℕ, ∀ N' ≥ N, (⇑((singularSubdivision M X).f n).hom)^[N'] b ∈
      LinearMap.range ((smallChainsι s t M).f n).hom by
    obtain ⟨N, hN⟩ := this
    exact ⟨N, hN N le_rfl⟩
  have hb : b ∈ ⨆ x : (TopCat.toSSet.obj X) _⦋n⦌,
      LinearMap.range ((TopCat.toSSet.obj X).ιChainComplex (R := M) x).hom := by
    rw [iSup_range_ιChainComplex]
    trivial
  refine Submodule.iSup_induction _ (motive := fun b => ∃ N : ℕ, ∀ N' ≥ N,
      (⇑((singularSubdivision M X).f n).hom)^[N'] b ∈
        LinearMap.range ((smallChainsι s t M).f n).hom) hb ?_ ?_ ?_
  · rintro σ _ ⟨r, rfl⟩
    obtain ⟨N, hN⟩ := exists_iterate_singularSubdivision_ιChainComplex_mem_range s t M h σ
    exact ⟨N, fun N' hN' => hN N' hN' r⟩
  · exact ⟨0, fun N' _ => by rw [iterate_map_zero]; exact zero_mem _⟩
  · rintro b₁ b₂ ⟨N₁, h₁⟩ ⟨N₂, h₂⟩
    refine ⟨max N₁ N₂, fun N' hN' => ?_⟩
    rw [iterate_map_add]
    exact add_mem (h₁ N' (le_of_max_le_left hN')) (h₂ N' (le_of_max_le_right hN'))

/-- **Small chains compute singular homology.** If the interiors of `s` and `t` cover `X`, the
inclusion of the small chains of `s` and `t` into all singular chains of `X` is a
quasi-isomorphism, for coefficients in any module `M` over a ring `k`. -/
theorem quasiIso_smallChainsι (h : interior s ∪ interior t = Set.univ) :
    QuasiIso (smallChainsι s t M) :=
  quasiIso_of_iterate_mem _ (singularSubdivision M X) (singularSubdivisionHomotopy M X)
    (singularSubdivision_f_apply_mem_range_smallChainsι s t M)
    (singularSubdivisionHomotopy_hom_apply_mem_range_smallChainsι s t M)
    (exists_iterate_singularSubdivision_mem_range_smallChainsι s t M h)

end ModuleCat

/-! ### The Mayer–Vietoris long exact sequence -/

section MayerVietoris

variable {k : Type u} [Ring k] {X : TopCat.{u}} (s t : Set X) (M : ModuleCat.{u} k)

/-- Under `singularChainsSubsetIso`, the inclusion `simplicesIn A ≤ simplicesIn B` of
subcomplexes is the map induced by the inclusion `A ⊆ B`. -/
theorem singularChainsSubsetIso_inv_comp_map_inclusion {A B : Set X} (hAB : A ⊆ B)
    (hle : simplicesIn A ≤ simplicesIn B) :
    (singularChainsSubsetIso A M).inv ≫
        ((singularChainComplexFunctor (ModuleCat.{u} k)).obj M).map
          (TopCat.ofHom (ContinuousMap.inclusion hAB)) =
      SSet.chainComplexMap (SSet.Subcomplex.homOfLE hle) M ≫ (singularChainsSubsetIso B M).inv := by
  have e : SSet.chainComplexMap (SSet.Subcomplex.homOfLE hle) M ≫
      SSet.chainComplexMap (simplicesIn B).ι M = SSet.chainComplexMap (simplicesIn A).ι M :=
    (((SSet.chainComplexFunctor (ModuleCat.{u} k)).obj M).map_comp _ _).symm
  rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv,
    ← cancel_mono (SSet.chainComplexMap (simplicesIn B).ι M), Category.assoc, Category.assoc,
    singularChainsSubsetIso_hom_comp_chainComplexMap_ι, e,
    singularChainsSubsetIso_hom_comp_chainComplexMap_ι]
  exact (((singularChainComplexFunctor (ModuleCat.{u} k)).obj M).map_comp _ _).symm

/-- Under `singularChainsSubsetIso`, the inclusion of `simplicesIn A` into the small simplices,
followed by the inclusion of small chains, is the map induced by the inclusion of `A`. -/
theorem singularChainsSubsetIso_hom_comp_homOfLE_comp_smallChainsι {A : Set X}
    (hle : simplicesIn A ≤ smallSimplices s t) :
    (singularChainsSubsetIso A M).hom ≫ SSet.chainComplexMap (SSet.Subcomplex.homOfLE hle) M ≫
        smallChainsι s t M =
      ((singularChainComplexFunctor (ModuleCat.{u} k)).obj M).map (subsetIncl A) := by
  have e : SSet.chainComplexMap (SSet.Subcomplex.homOfLE hle) M ≫ smallChainsι s t M =
      SSet.chainComplexMap (simplicesIn A).ι M :=
    (((SSet.chainComplexFunctor (ModuleCat.{u} k)).obj M).map_comp _ _).symm
  rw [e]
  exact singularChainsSubsetIso_hom_comp_chainComplexMap_ι A M

/-- The homology of the chains of `simplicesIn A` is the singular homology of `A`. -/
def homologySubsetIso (A : Set X) (n : ℕ) :
    ((simplicesIn A : SSet.{u}).chainComplex M).homology n ≅
      ((singularHomologyFunctor (ModuleCat.{u} k) n).obj M).obj (TopCat.of A) :=
  (homologyFunctor _ _ n).mapIso (singularChainsSubsetIso A M).symm

/-- The homology of the middle term of the short exact sequence of small chains. -/
private def homologyBiprodIso (n : ℕ) :
    ((simplicesIn s : SSet.{u}).chainComplex M ⊞
        (simplicesIn t : SSet.{u}).chainComplex M).homology n ≅
      ((singularHomologyFunctor (ModuleCat.{u} k) n).obj M).obj (TopCat.of s) ⊞
        ((singularHomologyFunctor (ModuleCat.{u} k) n).obj M).obj (TopCat.of t) :=
  haveI := preservesBinaryBiproducts_of_preservesBiproducts
    (homologyFunctor (ModuleCat.{u} k) (ComplexShape.down ℕ) n)
  (homologyFunctor _ _ n).mapBiprod _ _ ≪≫
    biprod.mapIso (homologySubsetIso M s n) (homologySubsetIso M t n)

private theorem homologyBiprodIso_hom_fst (n : ℕ) :
    (homologyBiprodIso s t M n).hom ≫ biprod.fst =
      homologyMap (biprod.fst ≫ (singularChainsSubsetIso s M).inv) n := by
  have := preservesBinaryBiproducts_of_preservesBiproducts
    (homologyFunctor (ModuleCat.{u} k) (ComplexShape.down ℕ) n)
  unfold homologyBiprodIso
  -- `erw`: the target objects are `singularHomologyFunctor` objects, only defeq to the
  -- homology objects that `mapBiprod` produces.
  erw [Iso.trans_hom, Category.assoc, biprod.mapIso_hom, biprod.map_fst,
    Functor.mapBiprod_hom, biprod.lift_fst_assoc]
  exact (homologyMap_comp _ _ _).symm

private theorem homologyBiprodIso_hom_snd (n : ℕ) :
    (homologyBiprodIso s t M n).hom ≫ biprod.snd =
      homologyMap (biprod.snd ≫ (singularChainsSubsetIso t M).inv) n := by
  have := preservesBinaryBiproducts_of_preservesBiproducts
    (homologyFunctor (ModuleCat.{u} k) (ComplexShape.down ℕ) n)
  unfold homologyBiprodIso
  -- `erw`: the target objects are `singularHomologyFunctor` objects, only defeq to the
  -- homology objects that `mapBiprod` produces.
  erw [Iso.trans_hom, Category.assoc, biprod.mapIso_hom, biprod.map_snd,
    Functor.mapBiprod_hom, biprod.lift_snd_assoc]
  exact (homologyMap_comp _ _ _).symm

private theorem inl_homologyBiprodIso_inv (n : ℕ) :
    biprod.inl ≫ (homologyBiprodIso s t M n).inv =
      homologyMap ((singularChainsSubsetIso s M).hom ≫ biprod.inl) n := by
  have := preservesBinaryBiproducts_of_preservesBiproducts
    (homologyFunctor (ModuleCat.{u} k) (ComplexShape.down ℕ) n)
  unfold homologyBiprodIso
  -- `erw`: the target objects are `singularHomologyFunctor` objects, only defeq to the
  -- homology objects that `mapBiprod` produces.
  erw [Iso.trans_inv, biprod.mapIso_inv, biprod.inl_map_assoc,
    Functor.mapBiprod_inv, biprod.inl_desc]
  exact (homologyMap_comp _ _ _).symm

private theorem inr_homologyBiprodIso_inv (n : ℕ) :
    biprod.inr ≫ (homologyBiprodIso s t M n).inv =
      homologyMap ((singularChainsSubsetIso t M).hom ≫ biprod.inr) n := by
  have := preservesBinaryBiproducts_of_preservesBiproducts
    (homologyFunctor (ModuleCat.{u} k) (ComplexShape.down ℕ) n)
  unfold homologyBiprodIso
  -- `erw`: the target objects are `singularHomologyFunctor` objects, only defeq to the
  -- homology objects that `mapBiprod` produces.
  erw [Iso.trans_inv, biprod.mapIso_inv, biprod.inr_map_assoc,
    Functor.mapBiprod_inv, biprod.inr_desc]
  exact (homologyMap_comp _ _ _).symm

/-- For a cover by interiors, the inclusion of small chains induces an isomorphism on homology. -/
def smallChainsHomologyIso (h : interior s ∪ interior t = Set.univ) (n : ℕ) :
    (smallChains s t M).homology n ≅
      ((singularHomologyFunctor (ModuleCat.{u} k) n).obj M).obj X :=
  @asIso _ _ _ _ (homologyMap (smallChainsι s t M) n)
    ((quasiIsoAt_iff_isIso_homologyMap _ _).1
      ((quasiIso_iff _).1 (quasiIso_smallChainsι s t M h) n))

/-- The **Mayer–Vietoris connecting map** `H_{n+1}(X) ⟶ H_n(s ∩ t)` in singular homology, for
subsets `s` and `t` whose interiors cover `X`: the inverse of the isomorphism induced on
homology by the inclusion of small chains, followed by the connecting map `bicartδ` of the
short exact sequence of small chains. -/
def mayerVietorisδ (h : interior s ∪ interior t = Set.univ) (n : ℕ) :
    ((singularHomologyFunctor (ModuleCat.{u} k) (n + 1)).obj M).obj X ⟶
      ((singularHomologyFunctor (ModuleCat.{u} k) n).obj M).obj (TopCat.of ↥(s ∩ t)) :=
  @inv _ _ _ _ (homologyMap (smallChainsι s t M) (n + 1))
      ((quasiIsoAt_iff_isIso_homologyMap _ _).1
        ((quasiIso_iff _).1 (quasiIso_smallChainsι s t M h) (n + 1))) ≫
    bicartδ M (bicartSq_simplicesIn s t) n ≫ homologyMap (singularChainsSubsetIso (s ∩ t) M).inv n

/-- The map `H_n(s ∩ t) ⟶ H_n(s) ⊞ H_n(t)` of the Mayer–Vietoris sequence: the inclusions, with
the sign `(inc, -inc)`. -/
def mayerVietorisInterMap (n : ℕ) :
    ((singularHomologyFunctor (ModuleCat.{u} k) n).obj M).obj (TopCat.of ↥(s ∩ t)) ⟶
      ((singularHomologyFunctor (ModuleCat.{u} k) n).obj M).obj (TopCat.of s) ⊞
        ((singularHomologyFunctor (ModuleCat.{u} k) n).obj M).obj (TopCat.of t) :=
  biprod.lift
    (((singularHomologyFunctor (ModuleCat.{u} k) n).obj M).map
      (TopCat.ofHom (ContinuousMap.inclusion Set.inter_subset_left)))
    (-((singularHomologyFunctor (ModuleCat.{u} k) n).obj M).map
      (TopCat.ofHom (ContinuousMap.inclusion Set.inter_subset_right)))

/-- The map `H_n(s) ⊞ H_n(t) ⟶ H_n(X)` of the Mayer–Vietoris sequence: the sum of the
inclusions. -/
def mayerVietorisSumMap (n : ℕ) :
    ((singularHomologyFunctor (ModuleCat.{u} k) n).obj M).obj (TopCat.of s) ⊞
        ((singularHomologyFunctor (ModuleCat.{u} k) n).obj M).obj (TopCat.of t) ⟶
      ((singularHomologyFunctor (ModuleCat.{u} k) n).obj M).obj X :=
  biprod.desc (((singularHomologyFunctor (ModuleCat.{u} k) n).obj M).map (subsetIncl s))
    (((singularHomologyFunctor (ModuleCat.{u} k) n).obj M).map (subsetIncl t))

private theorem mayerVietorisδ_eq (h : interior s ∪ interior t = Set.univ) (n : ℕ) :
    mayerVietorisδ s t M h n = (smallChainsHomologyIso s t M h (n + 1)).inv ≫
      (shortExact_of_bicartSq M (bicartSq_simplicesIn s t)).δ (n + 1) n rfl ≫
        (homologySubsetIso M (s ∩ t) n).hom :=
  rfl

private theorem smallChainsHomologyIso_hom_comp_mayerVietorisδ
    (h : interior s ∪ interior t = Set.univ) (n : ℕ) :
    (smallChainsHomologyIso s t M h (n + 1)).hom ≫ mayerVietorisδ s t M h n =
      (shortExact_of_bicartSq M (bicartSq_simplicesIn s t)).δ (n + 1) n rfl ≫
        (homologySubsetIso M (s ∩ t) n).hom := by
  rw [mayerVietorisδ_eq, Iso.hom_inv_id_assoc]

private theorem homologySubsetIso_hom_comp_mayerVietorisInterMap (n : ℕ) :
    (homologySubsetIso M (s ∩ t) n).hom ≫ mayerVietorisInterMap s t M n =
      homologyMap (mvShortComplex (isPushout_chainComplex M (bicartSq_simplicesIn s t))).f n ≫
        (homologyBiprodIso s t M n).hom := by
  apply biprod.hom_ext
  · simp only [Category.assoc]
    rw [homologyBiprodIso_hom_fst, mayerVietorisInterMap, biprod.lift_fst]
    have key : (singularChainsSubsetIso (s ∩ t) M).inv ≫
        ((singularChainComplexFunctor (ModuleCat.{u} k)).obj M).map
          (TopCat.ofHom (ContinuousMap.inclusion Set.inter_subset_left)) =
        (mvShortComplex (isPushout_chainComplex M (bicartSq_simplicesIn s t))).f ≫
          biprod.fst ≫ (singularChainsSubsetIso s M).inv := by
      rw [singularChainsSubsetIso_inv_comp_map_inclusion M Set.inter_subset_left
        (bicartSq_simplicesIn s t).le₁₂]
      simp only [mvShortComplex, biprod.lift_fst_assoc]
    exact (homologyMap_comp _ _ _).symm.trans
      ((congrArg (homologyMap · n) key).trans (homologyMap_comp _ _ _))
  · simp only [Category.assoc]
    rw [homologyBiprodIso_hom_snd, mayerVietorisInterMap, biprod.lift_snd, Preadditive.comp_neg]
    have key : -((singularChainsSubsetIso (s ∩ t) M).inv ≫
        ((singularChainComplexFunctor (ModuleCat.{u} k)).obj M).map
          (TopCat.ofHom (ContinuousMap.inclusion Set.inter_subset_right))) =
        (mvShortComplex (isPushout_chainComplex M (bicartSq_simplicesIn s t))).f ≫
          biprod.snd ≫ (singularChainsSubsetIso t M).inv := by
      rw [singularChainsSubsetIso_inv_comp_map_inclusion M Set.inter_subset_right
        (bicartSq_simplicesIn s t).le₁₃]
      simp only [mvShortComplex, biprod.lift_snd_assoc, Preadditive.neg_comp]
    exact (congrArg Neg.neg (homologyMap_comp _ _ _).symm).trans ((homologyMap_neg _ _).symm.trans
      ((congrArg (homologyMap · n) key).trans (homologyMap_comp _ _ _)))

private theorem mayerVietorisSumMap_eq (h : interior s ∪ interior t = Set.univ) (n : ℕ) :
    mayerVietorisSumMap s t M n = (homologyBiprodIso s t M n).inv ≫
      homologyMap (mvShortComplex (isPushout_chainComplex M (bicartSq_simplicesIn s t))).g n ≫
        (smallChainsHomologyIso s t M h n).hom := by
  apply biprod.hom_ext'
  · rw [mayerVietorisSumMap, biprod.inl_desc, ← Category.assoc, inl_homologyBiprodIso_inv]
    have key : ((singularChainsSubsetIso s M).hom ≫ biprod.inl) ≫
        (mvShortComplex (isPushout_chainComplex M (bicartSq_simplicesIn s t))).g ≫
          smallChainsι s t M =
        ((singularChainComplexFunctor (ModuleCat.{u} k)).obj M).map (subsetIncl s) := by
      simp only [Category.assoc, mvShortComplex, biprod.inl_desc_assoc]
      exact singularChainsSubsetIso_hom_comp_homOfLE_comp_smallChainsι s t M _
    exact (congrArg (homologyMap · n) key).symm.trans
      ((homologyMap_comp _ _ _).trans (congrArg (_ ≫ ·) (homologyMap_comp _ _ _)))
  · rw [mayerVietorisSumMap, biprod.inr_desc, ← Category.assoc, inr_homologyBiprodIso_inv]
    have key : ((singularChainsSubsetIso t M).hom ≫ biprod.inr) ≫
        (mvShortComplex (isPushout_chainComplex M (bicartSq_simplicesIn s t))).g ≫
          smallChainsι s t M =
        ((singularChainComplexFunctor (ModuleCat.{u} k)).obj M).map (subsetIncl t) := by
      simp only [Category.assoc, mvShortComplex, biprod.inr_desc_assoc]
      exact singularChainsSubsetIso_hom_comp_homOfLE_comp_smallChainsι s t M _
    exact (congrArg (homologyMap · n) key).symm.trans
      ((homologyMap_comp _ _ _).trans (congrArg (_ ≫ ·) (homologyMap_comp _ _ _)))

private theorem homologyBiprodIso_hom_comp_mayerVietorisSumMap
    (h : interior s ∪ interior t = Set.univ) (n : ℕ) :
    (homologyBiprodIso s t M n).hom ≫ mayerVietorisSumMap s t M n =
      homologyMap (mvShortComplex (isPushout_chainComplex M (bicartSq_simplicesIn s t))).g n ≫
        (smallChainsHomologyIso s t M h n).hom := by
  rw [mayerVietorisSumMap_eq s t M h, Iso.hom_inv_id_assoc]

/-- The connecting map followed by `(inc, -inc)` vanishes. -/
@[reassoc (attr := simp)]
theorem mayerVietorisδ_comp_mayerVietorisInterMap (h : interior s ∪ interior t = Set.univ)
    (n : ℕ) : mayerVietorisδ s t M h n ≫ mayerVietorisInterMap s t M n = 0 := by
  rw [mayerVietorisδ_eq, Category.assoc, Category.assoc,
    homologySubsetIso_hom_comp_mayerVietorisInterMap,
    (shortExact_of_bicartSq M (bicartSq_simplicesIn s t)).δ_comp_assoc (n + 1) n rfl, zero_comp,
    comp_zero]

/-- `(inc, -inc)` followed by the sum of the inclusions vanishes. -/
@[reassoc (attr := simp)]
theorem mayerVietorisInterMap_comp_mayerVietorisSumMap (n : ℕ) :
    mayerVietorisInterMap s t M n ≫ mayerVietorisSumMap s t M n = 0 := by
  rw [mayerVietorisInterMap, mayerVietorisSumMap, biprod.lift_desc, Preadditive.neg_comp,
    ← Functor.map_comp, ← Functor.map_comp]
  exact add_neg_cancel _

/-- The sum of the inclusions followed by the connecting map vanishes. -/
@[reassoc (attr := simp)]
theorem mayerVietorisSumMap_comp_mayerVietorisδ (h : interior s ∪ interior t = Set.univ)
    (n : ℕ) : mayerVietorisSumMap s t M (n + 1) ≫ mayerVietorisδ s t M h n = 0 := by
  rw [mayerVietorisSumMap_eq s t M h, Category.assoc, Category.assoc,
    smallChainsHomologyIso_hom_comp_mayerVietorisδ,
    (shortExact_of_bicartSq M (bicartSq_simplicesIn s t)).comp_δ_assoc (n + 1) n rfl, zero_comp,
    comp_zero]

/-- **Exactness at `H_n(s ∩ t)`** of the Mayer–Vietoris sequence
`H_{n+1}(X) ⟶ H_n(s ∩ t) ⟶ H_n(s) ⊞ H_n(t)`. -/
theorem mayerVietoris_exact_inter (h : interior s ∪ interior t = Set.univ) (n : ℕ) :
    (ShortComplex.mk _ _ (mayerVietorisδ_comp_mayerVietorisInterMap s t M h n)).Exact :=
  ShortComplex.exact_of_iso
    (ShortComplex.isoMk (smallChainsHomologyIso s t M h (n + 1)) (homologySubsetIso M (s ∩ t) n)
      (homologyBiprodIso s t M n) (smallChainsHomologyIso_hom_comp_mayerVietorisδ s t M h n)
      (homologySubsetIso_hom_comp_mayerVietorisInterMap s t M n))
    ((shortExact_of_bicartSq M (bicartSq_simplicesIn s t)).homology_exact₁ (n + 1) n rfl)

/-- **Exactness at `H_n(s) ⊞ H_n(t)`** of the Mayer–Vietoris sequence
`H_n(s ∩ t) ⟶ H_n(s) ⊞ H_n(t) ⟶ H_n(X)`. -/
theorem mayerVietoris_exact_sum (h : interior s ∪ interior t = Set.univ) (n : ℕ) :
    (ShortComplex.mk _ _ (mayerVietorisInterMap_comp_mayerVietorisSumMap s t M n)).Exact :=
  ShortComplex.exact_of_iso
    (ShortComplex.isoMk (homologySubsetIso M (s ∩ t) n) (homologyBiprodIso s t M n)
      (smallChainsHomologyIso s t M h n)
      (homologySubsetIso_hom_comp_mayerVietorisInterMap s t M n)
      (homologyBiprodIso_hom_comp_mayerVietorisSumMap s t M h n))
    ((shortExact_of_bicartSq M (bicartSq_simplicesIn s t)).homology_exact₂ n)

/-- **Exactness at `H_{n+1}(X)`** of the Mayer–Vietoris sequence
`H_{n+1}(s) ⊞ H_{n+1}(t) ⟶ H_{n+1}(X) ⟶ H_n(s ∩ t)`. -/
theorem mayerVietoris_exact_space (h : interior s ∪ interior t = Set.univ) (n : ℕ) :
    (ShortComplex.mk _ _ (mayerVietorisSumMap_comp_mayerVietorisδ s t M h n)).Exact :=
  ShortComplex.exact_of_iso
    (ShortComplex.isoMk (homologyBiprodIso s t M (n + 1)) (smallChainsHomologyIso s t M h (n + 1))
      (homologySubsetIso M (s ∩ t) n)
      (homologyBiprodIso_hom_comp_mayerVietorisSumMap s t M h (n + 1))
      (smallChainsHomologyIso_hom_comp_mayerVietorisδ s t M h n))
    ((shortExact_of_bicartSq M (bicartSq_simplicesIn s t)).homology_exact₃ (n + 1) n rfl)

end MayerVietoris

end

end TDA.Topology
