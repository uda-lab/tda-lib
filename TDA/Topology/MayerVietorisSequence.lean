import TDA.Topology.SmallChainsQuasiIso

/-!
# The Mayer–Vietoris connecting map: sign and naturality

For subsets `s` and `t` of a space `X` whose interiors cover `X`, `TDA.Topology.SmallChainsQuasiIso`
builds the Mayer–Vietoris long exact sequence in singular homology with coefficients in a module
`M`, with connecting map `mayerVietorisδ s t M h n : H_{n+1}(X) ⟶ H_n(s ∩ t)`. This module
describes the connecting map and proves that the sequence is natural.

* **Singular homology as homology of chains.** `singularHomologyIso` identifies
  `((singularHomologyFunctor C n).obj R).obj X` with the homology of the singular chain complex,
  by the identity, and `singularHomologyFunctor_obj_map` writes the map induced by a continuous
  map as `homologyMap` of the induced chain map. Both hold by `rfl`.
* **Characterisation of `δ`.** `mayerVietorisδ_eq_bicartδ` (by `rfl`) writes the connecting map
  as the inverse of `smallChainsHomologyIso`, then the connecting map `bicartδ` of the short
  exact sequence of small chains, then `homologySubsetIso`.
  `homologyMap_smallChainsι_comp_mayerVietorisδ` is the same statement on the homology of small
  chains, and `isIso_homologyMap_smallChainsι` records that the inclusion of small chains is an
  isomorphism on homology.
* **The sign.** `mayerVietorisδ_liftCycles`: if an `(n + 1)`-cycle of `X` is `z = a + b`, with
  `a` a chain of `s` and `b` a chain of `t`, and `x` is an `n`-chain of `s ∩ t` whose image in
  `s` is `∂a`, then `δ[z] = [x]`. It is derived from `bicartδ_eq`.
* **Exchanging the pieces.** `mayerVietorisδ_flip`: the connecting map of `(t, s)` is minus the
  connecting map of `(s, t)`, followed by the identification `s ∩ t ⊆ t ∩ s`. It is derived from
  `bicartδ_flip`.
* **Naturality.** For a continuous `f : X ⟶ Y` with `f(s) ⊆ s'` and `f(t) ⊆ t'`, where both
  pairs have interiors covering their space, `mayerVietorisδ_naturality`,
  `mayerVietorisInterMap_naturality` and `mayerVietorisSumMap_naturality` state that the three
  maps of the Mayer–Vietoris sequence commute with the maps induced by `f` and its restrictions
  `subsetRestrict f`. The connecting map is handled by `bicartδ_naturality`, applied to the
  restrictions of `TopCat.toSSet.map f` to the subcomplexes of simplices lying in the pieces.
-/

namespace TDA.Topology

open CategoryTheory Limits AlgebraicTopology Opposite HomologicalComplex
open scoped Simplicial

noncomputable section

universe u

/-! ### Singular homology as the homology of singular chains -/

section HomologyObj

variable {C : Type*} [Category C] [HasCoproducts.{u} C] [Preadditive C] [CategoryWithHomology C]

/-- Singular homology of `X` is the homology of the singular chain complex of `X`; the
isomorphism is the identity. -/
def singularHomologyIso (R : C) (X : TopCat.{u}) (n : ℕ) :
    ((singularHomologyFunctor C n).obj R).obj X ≅
      (((singularChainComplexFunctor C).obj R).obj X).homology n :=
  Iso.refl _

/-- The map induced on singular homology by a continuous map is `homologyMap` of the induced
map of singular chains. -/
theorem singularHomologyFunctor_obj_map (R : C) {X Y : TopCat.{u}} (f : X ⟶ Y) (n : ℕ) :
    ((singularHomologyFunctor C n).obj R).map f =
      homologyMap (((singularChainComplexFunctor C).obj R).map f) n :=
  rfl

end HomologyObj

/-! ### Restrictions of continuous maps to subsets -/

section Restrict

variable {X Y : TopCat.{u}}

/-- The restriction `s ⟶ s'` of a continuous map `f : X ⟶ Y` with `f(s) ⊆ s'`. -/
def subsetRestrict (f : X ⟶ Y) {s : Set X} {s' : Set Y} (h : Set.MapsTo f s s') :
    TopCat.of s ⟶ TopCat.of s' :=
  TopCat.ofHom ⟨h.restrict f s s', f.hom.continuous.restrict h⟩

@[simp]
theorem subsetRestrict_apply_val (f : X ⟶ Y) {s : Set X} {s' : Set Y} (h : Set.MapsTo f s s')
    (x : TopCat.of s) : (subsetRestrict f h x).1 = f x.1 :=
  rfl

/-- The restriction followed by the inclusion of `s'` is the inclusion of `s` followed by `f`. -/
@[simp]
theorem subsetRestrict_comp_subsetIncl (f : X ⟶ Y) {s : Set X} {s' : Set Y}
    (h : Set.MapsTo f s s') : subsetRestrict f h ≫ subsetIncl s' = subsetIncl s ≫ f :=
  rfl

/-- Restrictions commute with inclusions of subsets. -/
theorem inclusion_comp_subsetRestrict (f : X ⟶ Y) {A B : Set X} {A' B' : Set Y} (hAB : A ⊆ B)
    (hA'B' : A' ⊆ B') (hA : Set.MapsTo f A A') (hB : Set.MapsTo f B B') :
    TopCat.ofHom (ContinuousMap.inclusion hAB) ≫ subsetRestrict f hB =
      subsetRestrict f hA ≫ TopCat.ofHom (ContinuousMap.inclusion hA'B') :=
  rfl

/-- The inclusion of a subset into a larger one is a monomorphism of `TopCat`. -/
instance mono_ofHom_inclusion {A B : Set X} (h : A ⊆ B) :
    Mono (TopCat.ofHom (ContinuousMap.inclusion h)) :=
  (TopCat.mono_iff_injective _).2 (Set.inclusion_injective h)

/-- A monomorphism of spaces induces a monomorphism of singular chain complexes. -/
instance mono_singularChainComplexFunctor_map {C : Type*} [Category C] [Abelian C]
    [HasCoproducts.{u} C] (R : C) (g : X ⟶ Y) [Mono g] :
    Mono (((singularChainComplexFunctor C).obj R).map g) :=
  HomologicalComplex.mono_of_mono_f _ fun n =>
    inferInstanceAs (Mono ((sigmaConst.obj R).map ((TopCat.toSSet.map g).app (op ⦋n⦌))))

end Restrict

/-! ### The connecting map -/

section MayerVietoris

variable {k : Type u} [Ring k] {X : TopCat.{u}} (s t : Set X) (M : ModuleCat.{u} k)

/-- For a cover by interiors, the inclusion of small chains is an isomorphism on homology. -/
theorem isIso_homologyMap_smallChainsι (h : interior s ∪ interior t = Set.univ) (n : ℕ) :
    IsIso (homologyMap (smallChainsι s t M) n) :=
  (quasiIsoAt_iff_isIso_homologyMap _ _).1
    ((quasiIso_iff _).1 (quasiIso_smallChainsι s t M h) n)

/-- **The connecting map on small chains.** On the homology of small chains, `mayerVietorisδ` is
the connecting map `bicartδ` of the short exact sequence of small chains, followed by the
identification of the chains of `simplicesIn (s ∩ t)` with the singular chains of `s ∩ t`. -/
theorem homologyMap_smallChainsι_comp_mayerVietorisδ (h : interior s ∪ interior t = Set.univ)
    (n : ℕ) :
    homologyMap (smallChainsι s t M) (n + 1) ≫ mayerVietorisδ s t M h n =
      bicartδ M (bicartSq_simplicesIn s t) n ≫
        homologyMap (singularChainsSubsetIso (s ∩ t) M).inv n := by
  unfold mayerVietorisδ
  have := isIso_homologyMap_smallChainsι s t M h (n + 1)
  exact IsIso.hom_inv_id_assoc _ _

/-- **The connecting map through `bicartδ`**, by definition: the inverse of the isomorphism
induced on homology by the inclusion of small chains, then the connecting map `bicartδ` of the
short exact sequence of small chains, then the identification of the homology of
`simplicesIn (s ∩ t)` with the singular homology of `s ∩ t`. -/
theorem mayerVietorisδ_eq_bicartδ (h : interior s ∪ interior t = Set.univ) (n : ℕ) :
    mayerVietorisδ s t M h n = (smallChainsHomologyIso s t M h (n + 1)).inv ≫
      bicartδ M (bicartSq_simplicesIn s t) n ≫ (homologySubsetIso M (s ∩ t) n).hom :=
  rfl

/-- The chain map of the inclusion `A ⊆ B`, under `singularChainsSubsetIso`, is the inclusion of
subcomplexes `simplicesIn A ≤ simplicesIn B`. -/
private theorem map_inclusion_comp_singularChainsSubsetIso_hom {A B : Set X} (hAB : A ⊆ B) :
    ((singularChainComplexFunctor (ModuleCat.{u} k)).obj M).map
        (TopCat.ofHom (ContinuousMap.inclusion hAB)) ≫ (singularChainsSubsetIso B M).hom =
      (singularChainsSubsetIso A M).hom ≫
        SSet.chainComplexMap (SSet.Subcomplex.homOfLE (simplicesIn_mono hAB)) M := by
  rw [← Iso.inv_comp_eq, ← Category.assoc, ← Iso.eq_comp_inv]
  exact singularChainsSubsetIso_inv_comp_map_inclusion M hAB _

/-- **The sign of the Mayer–Vietoris connecting map.** Let `z = a + b` be an `(n + 1)`-cycle of
`X`, with `a` a singular chain of `s` and `b` a singular chain of `t` (as generalized elements
`W ⟶ _`), and let `x` be an `n`-chain of `s ∩ t` whose image in `s` is `∂a`. Then the connecting
map sends the class of `z` to the class of `x`. -/
theorem mayerVietorisδ_liftCycles (h : interior s ∪ interior t = Set.univ) (n : ℕ)
    {W : ModuleCat.{u} k}
    (a : W ⟶ (((singularChainComplexFunctor (ModuleCat.{u} k)).obj M).obj (TopCat.of s)).X (n + 1))
    (b : W ⟶ (((singularChainComplexFunctor (ModuleCat.{u} k)).obj M).obj (TopCat.of t)).X (n + 1))
    (hz : (a ≫ (((singularChainComplexFunctor (ModuleCat.{u} k)).obj M).map (subsetIncl s)).f
          (n + 1) +
        b ≫ (((singularChainComplexFunctor (ModuleCat.{u} k)).obj M).map (subsetIncl t)).f
          (n + 1)) ≫
        (((singularChainComplexFunctor (ModuleCat.{u} k)).obj M).obj X).d (n + 1) n = 0)
    (x : W ⟶
      (((singularChainComplexFunctor (ModuleCat.{u} k)).obj M).obj (TopCat.of ↥(s ∩ t))).X n)
    (hx : x ≫ (((singularChainComplexFunctor (ModuleCat.{u} k)).obj M).map
          (TopCat.ofHom (ContinuousMap.inclusion Set.inter_subset_left))).f n =
      a ≫ (((singularChainComplexFunctor (ModuleCat.{u} k)).obj M).obj (TopCat.of s)).d (n + 1) n)
    (m : ℕ) (hm : (ComplexShape.down ℕ).next n = m) :
    (((singularChainComplexFunctor (ModuleCat.{u} k)).obj M).obj X).liftCycles
        (a ≫ (((singularChainComplexFunctor (ModuleCat.{u} k)).obj M).map (subsetIncl s)).f
            (n + 1) +
          b ≫ (((singularChainComplexFunctor (ModuleCat.{u} k)).obj M).map (subsetIncl t)).f
            (n + 1)) n (by simp) hz ≫
        (((singularChainComplexFunctor (ModuleCat.{u} k)).obj M).obj X).homologyπ (n + 1) ≫
          mayerVietorisδ s t M h n =
      (((singularChainComplexFunctor (ModuleCat.{u} k)).obj M).obj (TopCat.of ↥(s ∩ t))).liftCycles
          x m hm (by
            rw [← cancel_mono ((((singularChainComplexFunctor (ModuleCat.{u} k)).obj M).map
                (TopCat.ofHom (ContinuousMap.inclusion Set.inter_subset_left))).f m),
              Category.assoc, ← Hom.comm, reassoc_of% hx, d_comp_d, Limits.comp_zero,
              Limits.zero_comp]) ≫
        (((singularChainComplexFunctor (ModuleCat.{u} k)).obj M).obj
          (TopCat.of ↥(s ∩ t))).homologyπ n := by
  let a' := a ≫ (singularChainsSubsetIso s M).hom.f (n + 1)
  let b' := b ≫ (singularChainsSubsetIso t M).hom.f (n + 1)
  let x' := x ≫ (singularChainsSubsetIso (s ∩ t) M).hom.f n
  let w := a' ≫ (SSet.chainComplexMap (SSet.Subcomplex.homOfLE
      (bicartSq_simplicesIn s t).le₂₄) M).f (n + 1) +
    b' ≫ (SSet.chainComplexMap (SSet.Subcomplex.homOfLE
      (bicartSq_simplicesIn s t).le₃₄) M).f (n + 1)
  have hzw : w ≫ (smallChainsι s t M).f (n + 1) =
      a ≫ (((singularChainComplexFunctor (ModuleCat.{u} k)).obj M).map (subsetIncl s)).f
          (n + 1) +
        b ≫ (((singularChainComplexFunctor (ModuleCat.{u} k)).obj M).map (subsetIncl t)).f
          (n + 1) := by
    simp only [w, a', b', Preadditive.add_comp, Category.assoc, ← comp_f,
      singularChainsSubsetIso_hom_comp_homOfLE_comp_smallChainsι]
  have hmono : Mono ((smallChainsι s t M).f n) :=
    inferInstanceAs (Mono ((sigmaConst.obj M).map ((smallSimplices s t).ι.app (op ⦋n⦌))))
  have hz' : w ≫ (smallChains s t M).d (n + 1) n = 0 := by
    rw [← cancel_mono ((smallChainsι s t M).f n), Category.assoc, ← Hom.comm, ← Category.assoc,
      hzw, hz, Limits.zero_comp]
  have hx' : x' ≫ (SSet.chainComplexMap (SSet.Subcomplex.homOfLE
      (bicartSq_simplicesIn s t).le₁₂) M).f n =
      a' ≫ ((simplicesIn s : SSet.{u}).chainComplex M).d (n + 1) n := by
    have e := congrArg (fun φ => x ≫ φ.f n)
      (map_inclusion_comp_singularChainsSubsetIso_hom M (Set.inter_subset_left : s ∩ t ⊆ s))
    simp only [comp_f] at e
    simp only [x', a', Category.assoc]
    rw [← e, reassoc_of% hx, Hom.comm]
  have E := bicartδ_eq M (bicartSq_simplicesIn s t) n a' b' hz' x' hx' m hm
  have key : ∀ (z : W ⟶ (((singularChainComplexFunctor (ModuleCat.{u} k)).obj M).obj X).X (n + 1))
      (e : w ≫ (smallChainsι s t M).f (n + 1) = z) (hz'' : z ≫ _ = 0),
      (((singularChainComplexFunctor (ModuleCat.{u} k)).obj M).obj X).liftCycles z n
        (by simp) hz'' =
        (smallChains s t M).liftCycles w n (by simp) hz' ≫
          cyclesMap (smallChainsι s t M) (n + 1) := by
    rintro _ rfl _
    rw [liftCycles_comp_cyclesMap]
  have e1 : cyclesMap (smallChainsι s t M) (n + 1) ≫
      (((singularChainComplexFunctor (ModuleCat.{u} k)).obj M).obj X).homologyπ (n + 1) ≫
        mayerVietorisδ s t M h n =
      (smallChains s t M).homologyπ (n + 1) ≫ homologyMap (smallChainsι s t M) (n + 1) ≫
        mayerVietorisδ s t M h n :=
    (homologyπ_naturality_assoc _ _ _).symm
  rw [key _ hzw hz, Category.assoc, e1, homologyMap_smallChainsι_comp_mayerVietorisδ]
  refine ((reassoc_of% E) _).trans ((congrArg (_ ≫ ·) (homologyπ_naturality _ _)).trans ?_)
  rw [liftCycles_comp_cyclesMap_assoc]
  congr 2
  simp only [x', Category.assoc, ← comp_f, Iso.hom_inv_id, id_f, Category.comp_id]

/-- **Exchanging the two pieces negates the connecting map.** The connecting map of `(t, s)` is
minus the connecting map of `(s, t)` followed by the map induced by `s ∩ t ⊆ t ∩ s`. -/
theorem mayerVietorisδ_flip (h : interior s ∪ interior t = Set.univ) (n : ℕ) :
    mayerVietorisδ t s M ((Set.union_comm _ _).trans h) n =
      -(mayerVietorisδ s t M h n ≫ ((singularHomologyFunctor (ModuleCat.{u} k) n).obj M).map
        (TopCat.ofHom (ContinuousMap.inclusion (Set.inter_comm s t).subset))) := by
  have hle : smallSimplices s t ≤ smallSimplices t s := sup_le le_sup_right le_sup_left
  have hι : SSet.chainComplexMap (SSet.Subcomplex.homOfLE hle) M ≫ smallChainsι t s M =
      smallChainsι s t M :=
    (((SSet.chainComplexFunctor (ModuleCat.{u} k)).obj M).map_comp _ _).symm
  have N := bicartδ_naturality M (bicartSq_flip (bicartSq_simplicesIn s t))
    (bicartSq_simplicesIn t s)
    (SSet.Subcomplex.homOfLE (simplicesIn_mono (Set.inter_comm s t).subset)) (𝟙 _) (𝟙 _)
    (SSet.Subcomplex.homOfLE hle) rfl rfl rfl rfl n
  rw [bicartδ_flip M (bicartSq_simplicesIn s t)] at N
  have e₄ : (smallChainsHomologyIso t s M ((Set.union_comm _ _).trans h) (n + 1)).inv =
      (smallChainsHomologyIso s t M h (n + 1)).inv ≫
        homologyMap (SSet.chainComplexMap (SSet.Subcomplex.homOfLE hle) M) (n + 1) := by
    rw [Iso.eq_inv_comp, Iso.comp_inv_eq]
    exact (congrArg (homologyMap · (n + 1)) hι).symm.trans (homologyMap_comp _ _ _)
  have e₁ : homologyMap (SSet.chainComplexMap (SSet.Subcomplex.homOfLE
        (simplicesIn_mono (Set.inter_comm s t).subset)) M) n ≫
          (homologySubsetIso M (t ∩ s) n).hom =
      (homologySubsetIso M (s ∩ t) n).hom ≫
        ((singularHomologyFunctor (ModuleCat.{u} k) n).obj M).map
          (TopCat.ofHom (ContinuousMap.inclusion (Set.inter_comm s t).subset)) :=
    (homologyMap_comp _ _ _).symm.trans ((congrArg (homologyMap · n)
      (singularChainsSubsetIso_inv_comp_map_inclusion M _ _).symm).trans
        (homologyMap_comp _ _ _))
  rw [mayerVietorisδ_eq_bicartδ, mayerVietorisδ_eq_bicartδ, e₄, Category.assoc, ← reassoc_of% N,
    e₁, Preadditive.neg_comp, Preadditive.comp_neg]
  simp only [Category.assoc]

end MayerVietoris

/-! ### Naturality -/

section Naturality

variable {k : Type u} [Ring k] (M : ModuleCat.{u} k) {X Y : TopCat.{u}} (f : X ⟶ Y)

/-- `TopCat.toSSet.map f` carries the simplices lying in `A` into those lying in `A'` when
`f(A) ⊆ A'`. -/
private theorem range_le_simplicesIn {A : Set X} {A' : Set Y} (hA : Set.MapsTo f A A') :
    SSet.Subcomplex.range ((simplicesIn A).ι ≫ TopCat.toSSet.map f) ≤ simplicesIn A' := by
  rintro m _ ⟨σ, rfl⟩
  have hσ := (mem_simplicesIn_iff A σ.1).1 σ.2
  change (TopCat.toSSet.map f).app m σ.1 ∈ (simplicesIn A').obj m
  rw [mem_simplicesIn_iff, toSSetObjEquiv_map]
  rintro _ ⟨p, rfl⟩
  exact hA (hσ ⟨p, rfl⟩)

/-- `TopCat.toSSet.map f` carries small simplices for `s, t` to small simplices for `s', t'`. -/
private theorem range_le_smallSimplices {s t : Set X} {s' t' : Set Y} (hs : Set.MapsTo f s s')
    (ht : Set.MapsTo f t t') :
    SSet.Subcomplex.range ((smallSimplices s t).ι ≫ TopCat.toSSet.map f) ≤
      smallSimplices s' t' := by
  rintro m _ ⟨σ, rfl⟩
  have hσ := (mem_smallSimplices_iff s t σ.1).1 σ.2
  change (TopCat.toSSet.map f).app m σ.1 ∈ (smallSimplices s' t').obj m
  rw [mem_smallSimplices_iff, toSSetObjEquiv_map]
  rcases hσ with hσ | hσ
  · left
    rintro _ ⟨p, rfl⟩
    exact hs (hσ ⟨p, rfl⟩)
  · right
    rintro _ ⟨p, rfl⟩
    exact ht (hσ ⟨p, rfl⟩)

/-- The restriction of `TopCat.toSSet.map f` to the simplices lying in `A`. -/
private def simplicesInMap {A : Set X} {A' : Set Y} (hA : Set.MapsTo f A A') :
    (simplicesIn A : SSet.{u}) ⟶ simplicesIn A' :=
  SSet.Subcomplex.lift _ (range_le_simplicesIn f hA)

/-- The restriction of `TopCat.toSSet.map f` to the small simplices. -/
private def smallSimplicesMap {s t : Set X} {s' t' : Set Y} (hs : Set.MapsTo f s s')
    (ht : Set.MapsTo f t t') : (smallSimplices s t : SSet.{u}) ⟶ smallSimplices s' t' :=
  SSet.Subcomplex.lift _ (range_le_smallSimplices f hs ht)

/-- Under `toSSetSubsetIso`, `simplicesInMap` is `TopCat.toSSet` of the restriction. -/
private theorem toSSetSubsetIso_inv_comp_map_subsetRestrict {A : Set X} {A' : Set Y}
    (hA : Set.MapsTo f A A') :
    (toSSetSubsetIso A).inv ≫ TopCat.toSSet.map (subsetRestrict f hA) =
      simplicesInMap f hA ≫ (toSSetSubsetIso A').inv := by
  rw [← cancel_mono (toSSetSubsetIso A').hom, ← cancel_mono (simplicesIn A').ι, Category.assoc,
    Category.assoc, toSSetSubsetIso_hom_ι, ← Functor.map_comp, subsetRestrict_comp_subsetIncl,
    Functor.map_comp, ← toSSetSubsetIso_hom_ι]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rfl

/-- Under `singularChainsSubsetIso`, `simplicesInMap` is the chain map of the restriction. -/
private theorem singularChainsSubsetIso_inv_comp_map_subsetRestrict {A : Set X} {A' : Set Y}
    (hA : Set.MapsTo f A A') :
    (singularChainsSubsetIso A M).inv ≫
        ((singularChainComplexFunctor (ModuleCat.{u} k)).obj M).map (subsetRestrict f hA) =
      SSet.chainComplexMap (simplicesInMap f hA) M ≫ (singularChainsSubsetIso A' M).inv := by
  change ((SSet.chainComplexFunctor (ModuleCat.{u} k)).obj M).map (toSSetSubsetIso A).inv ≫
      ((SSet.chainComplexFunctor (ModuleCat.{u} k)).obj M).map
        (TopCat.toSSet.map (subsetRestrict f hA)) =
    ((SSet.chainComplexFunctor (ModuleCat.{u} k)).obj M).map (simplicesInMap f hA) ≫
      ((SSet.chainComplexFunctor (ModuleCat.{u} k)).obj M).map (toSSetSubsetIso A').inv
  rw [← Functor.map_comp, ← Functor.map_comp, toSSetSubsetIso_inv_comp_map_subsetRestrict]

variable {s t : Set X} {s' t' : Set Y}

/-- **Naturality of the connecting map.** Let `f : X ⟶ Y` be continuous with `f(s) ⊆ s'` and
`f(t) ⊆ t'`, where the interiors of `s, t` cover `X` and those of `s', t'` cover `Y`. Then the
Mayer–Vietoris connecting maps commute with the maps induced by `f` and by its restriction
`s ∩ t ⟶ s' ∩ t'`. -/
theorem mayerVietorisδ_naturality (hs : Set.MapsTo f s s') (ht : Set.MapsTo f t t')
    (h : interior s ∪ interior t = Set.univ) (h' : interior s' ∪ interior t' = Set.univ)
    (n : ℕ) :
    mayerVietorisδ s t M h n ≫ ((singularHomologyFunctor (ModuleCat.{u} k) n).obj M).map
        (subsetRestrict f (hs.inter_inter ht)) =
      ((singularHomologyFunctor (ModuleCat.{u} k) (n + 1)).obj M).map f ≫
        mayerVietorisδ s' t' M h' n := by
  have hst := hs.inter_inter ht
  have N := bicartδ_naturality M (bicartSq_simplicesIn s t) (bicartSq_simplicesIn s' t')
    (simplicesInMap f hst) (simplicesInMap f hs) (simplicesInMap f ht)
    (smallSimplicesMap f hs ht)
    (by rw [← cancel_mono (SSet.Subcomplex.ι _)]; rfl)
    (by rw [← cancel_mono (SSet.Subcomplex.ι _)]; rfl)
    (by rw [← cancel_mono (SSet.Subcomplex.ι _)]; rfl)
    (by rw [← cancel_mono (SSet.Subcomplex.ι _)]; rfl) n
  have e₄ : (smallChainsHomologyIso s t M h (n + 1)).inv ≫
        homologyMap (SSet.chainComplexMap (smallSimplicesMap f hs ht) M) (n + 1) =
      ((singularHomologyFunctor (ModuleCat.{u} k) (n + 1)).obj M).map f ≫
        (smallChainsHomologyIso s' t' M h' (n + 1)).inv := by
    have hc : SSet.chainComplexMap (smallSimplicesMap f hs ht) M ≫ smallChainsι s' t' M =
        smallChainsι s t M ≫ ((singularChainComplexFunctor (ModuleCat.{u} k)).obj M).map f :=
      (((SSet.chainComplexFunctor (ModuleCat.{u} k)).obj M).map_comp _ _).symm.trans
        ((congrArg ((SSet.chainComplexFunctor (ModuleCat.{u} k)).obj M).map
          (SSet.Subcomplex.lift_ι _ _)).trans
        (((SSet.chainComplexFunctor (ModuleCat.{u} k)).obj M).map_comp
          (smallSimplices s t).ι (TopCat.toSSet.map f)))
    rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
    exact (homologyMap_comp _ _ _).symm.trans ((congrArg (homologyMap · (n + 1)) hc).trans
      (homologyMap_comp _ _ _))
  have e₁ : (homologySubsetIso M (s ∩ t) n).hom ≫
        ((singularHomologyFunctor (ModuleCat.{u} k) n).obj M).map (subsetRestrict f hst) =
      homologyMap (SSet.chainComplexMap (simplicesInMap f hst) M) n ≫
        (homologySubsetIso M (s' ∩ t') n).hom :=
    (homologyMap_comp _ _ _).symm.trans ((congrArg (homologyMap · n)
      (singularChainsSubsetIso_inv_comp_map_subsetRestrict M f hst)).trans
        (homologyMap_comp _ _ _))
  rw [mayerVietorisδ_eq_bicartδ, mayerVietorisδ_eq_bicartδ, Category.assoc, Category.assoc, e₁,
    reassoc_of% N, reassoc_of% e₄]

/-- **Naturality of `(inc, -inc)`.** The map `H_n(s ∩ t) ⟶ H_n(s) ⊞ H_n(t)` of the Mayer–Vietoris
sequence commutes with the maps induced by the restrictions of `f`. -/
theorem mayerVietorisInterMap_naturality (hs : Set.MapsTo f s s') (ht : Set.MapsTo f t t')
    (n : ℕ) :
    mayerVietorisInterMap s t M n ≫
        biprod.map (((singularHomologyFunctor (ModuleCat.{u} k) n).obj M).map (subsetRestrict f hs))
          (((singularHomologyFunctor (ModuleCat.{u} k) n).obj M).map (subsetRestrict f ht)) =
      ((singularHomologyFunctor (ModuleCat.{u} k) n).obj M).map
          (subsetRestrict f (hs.inter_inter ht)) ≫
        mayerVietorisInterMap s' t' M n := by
  apply biprod.hom_ext
  · simp only [mayerVietorisInterMap, Category.assoc, biprod.map_fst, biprod.lift_fst_assoc,
      biprod.lift_fst, ← Functor.map_comp]
    rfl
  · simp only [mayerVietorisInterMap, Category.assoc, biprod.map_snd, biprod.lift_snd_assoc,
      biprod.lift_snd, Preadditive.neg_comp, Preadditive.comp_neg, ← Functor.map_comp]
    rfl

/-- **Naturality of the sum map.** The map `H_n(s) ⊞ H_n(t) ⟶ H_n(X)` of the Mayer–Vietoris
sequence commutes with the maps induced by `f` and its restrictions. -/
theorem mayerVietorisSumMap_naturality (hs : Set.MapsTo f s s') (ht : Set.MapsTo f t t')
    (n : ℕ) :
    mayerVietorisSumMap s t M n ≫ ((singularHomologyFunctor (ModuleCat.{u} k) n).obj M).map f =
      biprod.map (((singularHomologyFunctor (ModuleCat.{u} k) n).obj M).map (subsetRestrict f hs))
          (((singularHomologyFunctor (ModuleCat.{u} k) n).obj M).map (subsetRestrict f ht)) ≫
        mayerVietorisSumMap s' t' M n := by
  apply biprod.hom_ext'
  · simp only [mayerVietorisSumMap, biprod.inl_desc_assoc, biprod.inl_map_assoc,
      biprod.inl_desc, ← Functor.map_comp]
    rfl
  · simp only [mayerVietorisSumMap, biprod.inr_desc_assoc, biprod.inr_map_assoc,
      biprod.inr_desc, ← Functor.map_comp]
    rfl

end Naturality

end

end TDA.Topology
