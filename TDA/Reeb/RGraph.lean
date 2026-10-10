import TDA.Reeb.ConstructibleSpace
import TDA.Reeb.ConstructibleCylinder
import TDA.Reeb.QuotientComparison
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.CategoryTheory.Functor.FullyFaithful
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.MorphismProperty.Basic

/-!
# Finite ℝ-graphs: maps of realizations and the Reeb quotient

Let `S : CriticalValues n` have levels `a 0 < ⋯ < a n`, and let `D D' : FiniteReebData n` be
finite incidence data: finite vertex sets `V i`, finite edge sets `E e` and endpoint maps
`left e : E e → V e.castSucc` and `right e : E e → V e.succ`. The realization
`(ofFiniteData D).Realization S` gives every piece the discrete topology. This file proves that
finite data describe graph objects and their maps faithfully, and that a graph object is its own
Reeb quotient (de Silva–Munch–Patel, Propositions 2.8 and 2.13).

## Hom classification

`HeightMap S D D'` is the type of **all** continuous maps `g` between the realizations with
`height ∘ g = height`; no cellwise condition is imposed. `homEquiv S : D.Hom D' ≃ HeightMap S D D'`
has the forward map `realizeHom` and both inverse laws.

* Vertex component. `g` maps the critical fiber over `a i`, which is `V i`, into the critical
  fiber of the target (`vertexFiberMap`, `apply_ofVertex`).
* Edge component. The regular fiber map of `g` at `t ∈ K e` does not depend on `t`, because the
  target edge piece is discrete (`regularFiberMap_indep_of_discrete`). `edgeMap` reads it at the
  chosen base point `basePt S e` (`apply_ofStrip`).
* Incidence. On the closed cylinder, `g (y, t)` and `(edgeMap y, t)` are continuous in `t` and
  agree on the dense open gap. The target realization is Hausdorff, so they agree at both ends
  (`apply_ofCylinder`). The ends are vertex points and `ofVertex` is injective, so both incidence
  squares hold (`toHom`). No injectivity of `left` or `right` is used.
* Inverse laws. A height-preserving map agrees with the realization of its data on generators
  (`hom_ext`); conversely the data of a realized map are recovered by injectivity of `ofVertex`
  and by `regularFiberMap_realizeHom`.

## Graph objects

`FiniteReebData.instCategory` makes finite data a category. The realization functor
`realizationFunctor S : FiniteReebData n ⥤ Over (TopCat.of ℝ)` into the real slice is fully
faithful (`realizationFullyFaithful`), because slice morphisms between realizations are exactly
the height-preserving maps (`overHomEquiv`). An object of the real slice satisfies `IsRGraph` when
it is isomorphic to `toOver T D` for some `m`, `T : CriticalValues m` and `D`. Graph objects form
the full subcategory `RGraphCat`; presentations are not its objects. The packaging is in universe
`0`, the universe of the real slice; the classification itself holds in every universe.

## The Reeb quotient

Every fiber of a realization of finite data is homeomorphic to a vertex set or an edge set, or is
empty, hence discrete (`discreteTopology_fiber`) and finite (`finite_fiber`). A path of constant
height lies in one fiber and is therefore constant, so the Reeb relation is equality
(`reebRel_iff_eq`). The identity descends through the universal property of the quotient to an
inverse of the projection, and `ReebQuotient.proj` is a height-preserving homeomorphism
(`projHomeomorph`). The height is not assumed injective. On graph objects the point
`projNatTrans : 𝟭 ⟶ Q` of the Reeb quotient endofunctor is a natural isomorphism (`projNatIso`);
the explicit square for an arbitrary height-preserving map is `projInv_natural`.

## Fibers of arbitrary presentations

For an arbitrary presentation `P`, fibers outside `[a 0, a n]` are empty (`isEmpty_fiber`), and a
point whose height is not a level is an open-strip point (`exists_strip_rep`).

See `docs/math/reeb-rgraph.md`.
-/

open Set Topology CategoryTheory

universe u

namespace TDA.Reeb

noncomputable section

namespace RGraph

open CylinderPresentation

/-! ### Hom classification -/

section classification

variable {n : ℕ} {S : CriticalValues n} {D D' : FiniteReebData.{u} n}

variable (S) in
/-- Height-preserving continuous maps between finite realizations over a common `S`. -/
def HeightMap (D D' : FiniteReebData.{u} n) : Type u :=
  {g : C((ofFiniteData D).Realization S, (ofFiniteData D').Realization S) //
    ∀ q, (ofFiniteData D').height S (g q) = (ofFiniteData D).height S q}

variable (S) in
/-- A chosen regular height in each gap (any point works; `regularFiberMap_indep_of_discrete`). -/
def basePt (k : Fin n) : (S.K k : Set ℝ) :=
  ⟨(S.K_nonempty k).some, (S.K_nonempty k).some_mem⟩

section determination

variable (g : C((ofFiniteData D).Realization S, (ofFiniteData D').Realization S))
  (hg : ∀ q, (ofFiniteData D').height S (g q) = (ofFiniteData D).height S q)
include hg

/-- The edge component determined by a height-preserving map: the regular fiber map at the base
point (any point gives the same map). -/
def edgeMap (k : Fin n) (y : (ofFiniteData D).E k) : (ofFiniteData D').E k :=
  regularFiberMap S g hg k (basePt S k) y

/-- On an open strip, a height-preserving map acts by its edge component. -/
theorem apply_ofStrip (k : Fin n) (y : (ofFiniteData D).E k) (t : (S.K k : Set ℝ)) :
    g ((ofFiniteData D).ofStrip S k (y, t)) =
      (ofFiniteData D').ofStrip S k (edgeMap g hg k y, t) := by
  rw [map_ofStrip_eq S g hg k t y, edgeMap,
    regularFiberMap_indep_of_discrete S g hg k t (basePt S k)]

/-- On the closed cylinder, by continuity and density of the open gap (`T2Space` target). -/
theorem apply_ofCylinder (k : Fin n) (y : (ofFiniteData D).E k) (p : Seg S k) :
    g ((ofFiniteData D).ofCylinder S k (y, p)) =
      (ofFiniteData D').ofCylinder S k (edgeMap g hg k y, p) := by
  have hab := (S.value_castSucc_lt_succ k).le
  have hF : Continuous fun t : ℝ =>
      g ((ofFiniteData D).ofCylinder S k (y, projIcc _ _ hab t)) :=
    g.continuous.comp (((ofFiniteData D).continuous_ofCylinder S k).comp
      (continuous_const.prodMk continuous_projIcc))
  have hG : Continuous fun t : ℝ =>
      (ofFiniteData D').ofCylinder S k (edgeMap g hg k y, projIcc _ _ hab t) :=
    ((ofFiniteData D').continuous_ofCylinder S k).comp
      (continuous_const.prodMk continuous_projIcc)
  have hEq : EqOn (fun t : ℝ => g ((ofFiniteData D).ofCylinder S k (y, projIcc _ _ hab t)))
      (fun t : ℝ => (ofFiniteData D').ofCylinder S k (edgeMap g hg k y, projIcc _ _ hab t))
      (Ioo (S.value k.castSucc) (S.value k.succ)) := by
    intro t ht
    have hp : projIcc _ _ hab t = gapIncl S k ⟨t, ht⟩ :=
      projIcc_of_mem hab (Ioo_subset_Icc_self ht)
    show g ((ofFiniteData D).ofCylinder S k (y, projIcc _ _ hab t)) =
      (ofFiniteData D').ofCylinder S k (edgeMap g hg k y, projIcc _ _ hab t)
    rw [hp]
    exact apply_ofStrip g hg k y ⟨t, ht⟩
  have h := (hEq.closure hF hG)
    (show (p : ℝ) ∈ closure (Ioo (S.value k.castSucc) (S.value k.succ)) by
      rw [closure_Ioo (S.value_castSucc_lt_succ k).ne]; exact p.2)
  simpa only [projIcc_val] using h

/-- The vertex component is `vertexFiberMap`. -/
theorem apply_ofVertex (i : Fin (n + 1)) (x : (ofFiniteData D).V i) :
    g ((ofFiniteData D).ofVertex S i x) =
      (ofFiniteData D').ofVertex S i (vertexFiberMap S g hg i x) :=
  map_ofVertex_eq S g hg i x

/-- Backward direction: the finite map of a height-preserving map; endpoint continuity gives
both incidence squares. -/
def toHom : D.Hom D' where
  v i := vertexFiberMap S g hg i
  e := edgeMap g hg
  left_comm k y := by
    have h := apply_ofCylinder g hg k y (segBot S k)
    rw [(ofFiniteData D).ofCylinder_segBot S k y, (ofFiniteData D').ofCylinder_segBot S k,
      apply_ofVertex g hg] at h
    exact ((ofFiniteData D').ofVertex_injective S _ h).symm
  right_comm k y := by
    have h := apply_ofCylinder g hg k y (segTop S k)
    rw [(ofFiniteData D).ofCylinder_segTop S k y, (ofFiniteData D').ofCylinder_segTop S k,
      apply_ofVertex g hg] at h
    exact ((ofFiniteData D').ofVertex_injective S _ h).symm

end determination

variable (S) in
/-- **Hom classification.** For a common `S`, finite maps correspond bijectively to
height-preserving continuous maps of realizations; both inverse laws hold. -/
def homEquiv : D.Hom D' ≃ HeightMap S D D' where
  toFun φ := ⟨realizeHom S φ, height_realizeHom S φ⟩
  invFun g := toHom g.1 g.2
  left_inv φ := by
    apply FiniteReebData.Hom.ext
    · funext i x
      exact (ofFiniteData D').ofVertex_injective S i
        (apply_ofVertex (realizeHom S φ) (height_realizeHom S φ) i x).symm
    · funext k y
      exact regularFiberMap_realizeHom S φ k (basePt S k) y
  right_inv g := Subtype.ext <| CylinderPresentation.hom_ext
    (fun i x => (apply_ofVertex g.1 g.2 i x).symm)
    (fun k p => (apply_ofCylinder g.1 g.2 k p.1 p.2).symm)

/-- The forward map of the classification is the realization of finite maps. -/
theorem homEquiv_apply (φ : D.Hom D') : ((homEquiv S φ).1 : C(_, _)) = realizeHom S φ := rfl

end classification

/-! ### Category packaging -/

section category

variable {n : ℕ}

/-- Finite data over `n + 1` levels form a category, with `Hom.id` and the diagrammatic
`Hom.comp`. -/
instance _root_.TDA.Reeb.FiniteReebData.instCategory :
    Category.{u} (FiniteReebData.{u} n) where
  Hom := FiniteReebData.Hom
  id := FiniteReebData.Hom.id
  comp := FiniteReebData.Hom.comp
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-- Composition in the category of finite data is `Hom.comp`. -/
theorem _root_.TDA.Reeb.FiniteReebData.comp_def {D D' D'' : FiniteReebData.{u} n}
    (φ : D ⟶ D') (ψ : D' ⟶ D'') : φ ≫ ψ = FiniteReebData.Hom.comp φ ψ := rfl

/-- Identities in the category of finite data are `Hom.id`. -/
theorem _root_.TDA.Reeb.FiniteReebData.id_def (D : FiniteReebData.{u} n) :
    𝟙 D = FiniteReebData.Hom.id D := rfl

variable (S : CriticalValues n)

/-- A finite realization as an object of the real slice `Over (TopCat.of ℝ)`. -/
def toOver (D : FiniteReebData.{0} n) : Over (TopCat.of ℝ) :=
  Over.mk (TopCat.ofHom ((ofFiniteData D).height S))

/-- Realization as a functor into the real slice. It is `@[reducible]` so that
`(realizationFunctor S).obj D` and `toOver S D` unify at reducible transparency; without it the
rewrites in `refine_coherent` and `homEquivOfIso_*` fail on that mismatch. -/
@[reducible] def realizationFunctor : FiniteReebData.{0} n ⥤ Over (TopCat.of ℝ) where
  obj D := toOver S D
  map φ := Over.homMk (TopCat.ofHom (realizeHom S φ))
    (by ext q; exact height_realizeHom S φ q)
  map_id D := by
    ext q
    exact congrArg (fun f : C(_, _) => f q) (realizeHom_id S D)
  map_comp φ ψ := by
    ext q
    exact congrArg (fun f : C(_, _) => f q) (realizeHom_comp S φ ψ)

/-- Morphisms in the slice between realizations are exactly height-preserving maps. -/
def overHomEquiv (D D' : FiniteReebData.{0} n) :
    (toOver S D ⟶ toOver S D') ≃ HeightMap S D D' where
  toFun φ := ⟨φ.left.hom, fun q => overBaseMap_comm φ q⟩
  invFun g := Over.homMk (TopCat.ofHom g.1) (by ext q; exact g.2 q)
  left_inv φ := by ext q; rfl
  right_inv g := rfl

/-- **Main theorem, categorical form**: realization is fully faithful for a common `S`. -/
def realizationFullyFaithful : (realizationFunctor S).FullyFaithful where
  preimage {D D'} φ := (homEquiv S).symm (overHomEquiv S D D' φ)
  map_preimage {D D'} φ := (overHomEquiv S D D').injective
    ((homEquiv S).apply_symm_apply (overHomEquiv S D D' φ))
  preimage_map φ := (homEquiv S).symm_apply_apply φ

end category

/-! ### Graph objects -/

/-- An object of the real slice is a graph object when it is isomorphic to the realization of
finite data over some critical values. -/
def IsRGraph : ObjectProperty (Over (TopCat.of ℝ)) := fun A =>
  ∃ (m : ℕ) (T : CriticalValues m) (D : FiniteReebData.{0} m), Nonempty (A ≅ toOver T D)

/-- Graph objects: the full subcategory of the real slice. -/
abbrev RGraphCat := IsRGraph.FullSubcategory

/-- The realization functor lands in graph objects. -/
def toRGraph {n : ℕ} (S : CriticalValues n) : FiniteReebData.{0} n ⥤ RGraphCat :=
  IsRGraph.lift (realizationFunctor S) fun D => ⟨n, S, D, ⟨Iso.refl _⟩⟩

/-! ### The Reeb quotient of a graph object -/

section quotient

variable {n : ℕ} (S : CriticalValues n)

/-- Every fiber of a finite realization is discrete in the subspace topology (it is a vertex
set, an edge set or empty). -/
theorem discreteTopology_fiber (D : FiniteReebData.{u} n) (t : ℝ) :
    DiscreteTopology ((ofFiniteData D).height S ⁻¹' {t}) := by
  by_cases hne : ((ofFiniteData D).height S ⁻¹' {t}).Nonempty
  · obtain ⟨q, hq⟩ := hne
    rcases (ofFiniteData D).exists_rep S q with ⟨i, v, rfl⟩ | ⟨e, p, rfl⟩
    · have ht : S.value i = t := hq
      subst ht
      exact ((ofFiniteData D).criticalFiberHomeomorph S i).discreteTopology_iff.1 inferInstance
    · have ht : (p.2 : ℝ) = t := hq
      subst ht
      exact ((ofFiniteData D).regularFiberHomeomorph S e p.2).discreteTopology_iff.1
        inferInstance
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne]
    infer_instance

/-- A constant-height path in a finite realization is constant: Reeb classes are singletons. -/
theorem reebRel_iff_eq (D : FiniteReebData.{u} n) (q q' : (ofFiniteData D).Realization S) :
    ReebRel ((ofFiniteData D).height S) q q' ↔ q = q' := by
  constructor
  · rintro ⟨γ, hγ⟩
    have := discreteTopology_fiber S D ((ofFiniteData D).height S q)
    let c : Path (⟨q, rfl⟩ : (ofFiniteData D).height S ⁻¹' {(ofFiniteData D).height S q})
        ⟨q', by simpa using hγ 1⟩ :=
      ⟨⟨fun s => ⟨γ s, hγ s⟩, γ.continuous.subtype_mk _⟩, Subtype.ext γ.source,
        Subtype.ext γ.target⟩
    exact congrArg Subtype.val (joined_eq_of_discrete ⟨c⟩)
  · rintro rfl
    exact ReebRel.refl _ q

/-- The inverse of the projection, from the universal property of the quotient (no injectivity
of the height is used). -/
def projInv (D : FiniteReebData.{u} n) :
    C(ReebQuotient ((ofFiniteData D).height S), (ofFiniteData D).Realization S) :=
  ReebQuotient.lift (ContinuousMap.id _) fun x x' h => (reebRel_iff_eq S D x x').1 h

/-- **The projection is a height-preserving homeomorphism** for every finite realization. -/
def projHomeomorph (D : FiniteReebData.{u} n) :
    (ofFiniteData D).Realization S ≃ₜ ReebQuotient ((ofFiniteData D).height S) where
  toFun := ReebQuotient.mk _
  invFun := projInv S D
  left_inv _ := rfl
  right_inv q := by
    induction q using ReebQuotient.ind with
    | h x => rfl
  continuous_toFun := ReebQuotient.continuous_mk _
  continuous_invFun := (projInv S D).continuous

/-- The homeomorphism is the canonical projection. -/
theorem projHomeomorph_apply (D : FiniteReebData.{u} n) (q) :
    projHomeomorph S D q = ReebQuotient.proj ((ofFiniteData D).height S) q := rfl

/-- The homeomorphism preserves height. -/
theorem height_projHomeomorph (D : FiniteReebData.{u} n) (q) :
    ReebQuotient.height _ (projHomeomorph S D q) = (ofFiniteData D).height S q := rfl

/-- Naturality of the inverse in an arbitrary height-preserving map `g`. -/
theorem projInv_natural {D D' : FiniteReebData.{u} n}
    (g : C((ofFiniteData D).Realization S, (ofFiniteData D').Realization S))
    (hg : ∀ q, (ofFiniteData D').height S (g q) = (ofFiniteData D).height S q) :
    (projInv S D').comp (ReebQuotient.map g hg) = g.comp (projInv S D) :=
  ReebQuotient.hom_ext fun _ => rfl

/-- The component of the pointed endofunctor `projNatTrans` at a realization is an
isomorphism in the real slice. -/
instance isIso_projNatTrans_app_toOver (D : FiniteReebData.{0} n) :
    IsIso ((ReebQuotient.projNatTrans ℝ).app (toOver S D)) :=
  ⟨⟨Over.homMk (TopCat.ofHom (projInv S D)) (by
      ext q
      induction q using ReebQuotient.ind with
      | h x => rfl),
    by ext x; rfl,
    by
      ext q
      induction q using ReebQuotient.ind with
      | h x => rfl⟩⟩

/-- **Naturality in graph maps**: on graph objects, the point `ρ : 𝟭 ⟶ Q` of the Reeb
quotient endofunctor is a natural isomorphism. -/
instance isIso_projNatTrans_rgraph :
    IsIso (Functor.whiskerLeft IsRGraph.ι (ReebQuotient.projNatTrans ℝ)) := by
  refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun A => ?_
  obtain ⟨m, T, D, ⟨i⟩⟩ := A.property
  exact (NatTrans.isIso_app_iff_of_iso (ReebQuotient.projNatTrans ℝ) i).2 inferInstance

/-- The natural isomorphism `𝟭 ≅ Q` on graph objects. -/
def projNatIso : IsRGraph.ι ⋙ 𝟭 _ ≅ IsRGraph.ι ⋙ ReebQuotient.quotientFunctor ℝ :=
  asIso (Functor.whiskerLeft IsRGraph.ι (ReebQuotient.projNatTrans ℝ))

end quotient

/-! ### Isomorphisms of finite data -/

section isos

variable {n : ℕ}

/-- The edge components of an isomorphism of finite data are injective. -/
theorem e_injective_of_iso {D D' : FiniteReebData.{u} n} (i : D ≅ D') (k : Fin n) :
    Function.Injective (i.hom.e k) := fun x y h => by
  have hc := congrArg (fun φ : D ⟶ D => φ.e k) i.hom_inv_id
  have hx : i.inv.e k (i.hom.e k x) = x := congrFun hc x
  have hy : i.inv.e k (i.hom.e k y) = y := congrFun hc y
  rw [← hx, ← hy, h]

/-- The vertex components of an isomorphism of finite data are injective. -/
theorem v_injective_of_iso {D D' : FiniteReebData.{u} n} (i : D ≅ D') (k : Fin (n + 1)) :
    Function.Injective (i.hom.v k) := fun x y h => by
  have hc := congrArg (fun φ : D ⟶ D => φ.v k) i.hom_inv_id
  have hx : i.inv.v k (i.hom.v k x) = x := congrFun hc x
  have hy : i.inv.v k (i.hom.v k y) = y := congrFun hc y
  rw [← hx, ← hy, h]

end isos

/-! ### Fibers -/

section fibers

variable {n : ℕ} {S : CriticalValues n}

/-- Every fiber of a finite realization is finite. -/
theorem finite_fiber (S : CriticalValues n) (D : FiniteReebData.{u} n) (t : ℝ) :
    Finite ((ofFiniteData D).height S ⁻¹' {t}) := by
  refine Set.Finite.to_subtype (Set.Finite.subset
    ((Set.finite_range fun v : (Σ i, D.V i) => (ofFiniteData D).ofVertex S v.1 v.2).union
      (Set.finite_range fun z : (Σ e, D.E e) => (ofFiniteData D).ofCylinder S z.1
        (z.2, projIcc _ _ (S.value_castSucc_lt_succ z.1).le t))) ?_)
  intro q hq
  rcases (ofFiniteData D).exists_rep S q with ⟨i, v, rfl⟩ | ⟨e, p, rfl⟩
  · exact Or.inl ⟨⟨i, v⟩, rfl⟩
  · have ht : (p.2 : ℝ) = t := hq
    subst ht
    refine Or.inr ⟨⟨e, p.1⟩, ?_⟩
    show (ofFiniteData D).ofCylinder S e (p.1, projIcc _ _ _ (p.2 : ℝ)) =
      (ofFiniteData D).ofStrip S e p
    rw [projIcc_of_mem _ (Ioo_subset_Icc_self p.2.2)]
    rfl

/-- Fibers outside `[a 0, a n]` are empty, for an arbitrary presentation. -/
theorem isEmpty_fiber (S : CriticalValues n) (P : CylinderPresentation.{u} n) {t : ℝ}
    (ht : t ∉ Icc (S.value 0) (S.value (Fin.last n))) :
    IsEmpty (P.height S ⁻¹' {t}) :=
  ⟨fun q => ht ((show P.height S q.1 = t from q.2) ▸ P.height_mem_Icc S q.1)⟩

/-- A point at a height that is not an `S`-level is an open-strip point, for an arbitrary
presentation. -/
theorem exists_strip_rep (P : CylinderPresentation.{u} n) (q : P.Realization S) {t : ℝ}
    (hq : P.height S q = t) (ht : ∀ i, S.value i ≠ t) :
    ∃ (e : Fin n) (h : t ∈ (S.K e : Set ℝ)) (z : P.E e),
      q = P.ofStrip S e (z, ⟨t, h⟩) := by
  rcases P.exists_rep S q with ⟨i, v, rfl⟩ | ⟨e, p, rfl⟩
  · exact absurd hq (ht i)
  · have hp : (p.2 : ℝ) = t := hq
    subst hp
    exact ⟨e, p.2.2, p.1, rfl⟩

end fibers

end RGraph

end

end TDA.Reeb
