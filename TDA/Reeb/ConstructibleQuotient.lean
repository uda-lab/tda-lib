import TDA.Reeb.ConstructibleCylinder
import TDA.Reeb.QuotientComparison
import TDA.Reeb.RGraph
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Constructible Reeb quotients are finite ℝ-graphs

The Reeb quotient of a constructible ℝ-space is homeomorphic over `ℝ` to the finite realization
of the path components of its pieces, by a map sending the class of each raw point to the class of
its piece (de Silva, Munch and Patel, *Categorified Reeb Graphs*, Proposition 2.12).

## Setting

`S : CriticalValues n` has levels `a 0 < ⋯ < a n`, and `P : CylinderPresentation n` has arbitrary
topological pieces `V i`, `E e` with continuous endpoint maps. Write `X = P.Realization S`,
`h = P.height S` and `Q = ReebQuotient h`. The component data `P.componentData : FiniteReebData n`
has vertex sets `π₀ (V i)`, edge sets `π₀ (E e)` and endpoint maps `π₀ (left e)`,
`π₀ (right e)`. Write `G = (ofFiniteData P.componentData).Realization S` for its finite
realization. `P.vertexClass i v` and `P.edgeClass e y` are the classes `[v]` and `[y]`, typed as
points of the vertex and edge sets of `G`.

## Hypotheses

The results about a presentation are layered by the hypotheses they use on the pieces; the
compactness of `Q` (`compactSpace_reebQuotient`) needs only compactness of the pieces.

* Finiteness of every `π₀ (V i)` and `π₀ (E e)`: the component data, the class maps and their
  formulas, the component data map `componentDataHom` of an arbitrary height-preserving map, its
  independence of the regular height (`componentDataHom_e`), and its identity and composition
  laws (`componentDataHom_id`, `componentDataHom_comp`).
* In addition, local path-connectedness of every piece: continuity of the class maps, the
  continuous comparison `componentGraphMap : X → G`, its descent to `Q`, the fiber normal form,
  bijectivity of the descended map and the pointwise naturality squares. The vertex set of `G` at
  `i` has the carrier `π₀ (V i)` with the discrete topology, while `π₀ (V i)` itself carries the
  quotient topology of `V i`; likewise for edges. Unfolding `ofFiniteData` identifies the carriers,
  not the topologies. The two topologies agree exactly when the quotient topology is discrete,
  which holds for a locally path-connected piece because its path components are open
  (`continuous_vertexClass`, `continuous_edgeClass`).
* Compactness and local path-connectedness of every piece: the homeomorphism, the Hausdorff
  property of `Q`, the slice isomorphisms, transport, the cross-list comparison squares and
  constructible ℝ-spaces. Finiteness of the component sets then follows from mathlib's instance
  for compact locally path-connected spaces.

No result assumes Hausdorff pieces, or injectivity, surjectivity or an embedding property of the
endpoint maps. Everything outside the real slice is universe-polymorphic; the slice packaging is
in universe `0`, the universe of the real slice.

## The homeomorphism

1. Continuity. The maps `v ↦ (i, [v])` and `(y, t) ↦ (e, [y], t)` are continuous and satisfy
   both endpoint equations, because `π₀ (left e) [y] = [left e y]`. The universal property of the
   realization gives a continuous height-preserving `Φ = componentGraphMap : X → G`.
2. Fiber normal form. `Φ x = Φ x'` exactly when `x` and `x'` are Reeb-related
   (`componentGraphMap_eq_iff`). A path of constant height maps to a path of constant height in
   `G`, whose fibers are finite and discrete, so Reeb-related points have equal images
   (`RGraph.apply_eq_of_reebRel`). Conversely, every point is a vertex point or an open-strip
   point. Equal images force the same level and joined vertex-piece points, or the same gap, the
   same regular height and joined edge-piece points; the joining path, pushed into `X`, has
   constant height.
3. Descent. `Φ` descends to `quotientComponentGraphMap : C(Q, G)`. It is injective by the fiber
   normal form and surjective because every point of `G` is `(i, [v])` or `(e, [y], t)`.
4. Homeomorphism. With compact pieces `X` is compact, so `Q` is compact as a continuous image
   (`compactSpace_reebQuotient`), and `G` is Hausdorff. A continuous bijection from a compact space
   to a Hausdorff space is a homeomorphism, which gives `quotientComponentGraphHomeomorph : Q ≃ₜ G`.
   Continuity of the inverse comes from this argument, not from bijectivity alone.
   `t2Space_reebQuotient` is a theorem under these hypotheses; no `T2Space` instance on
   `ReebQuotient` is declared.
5. Formulas. On generators `Θ [ofVertex i v] = (i, [v])`, `Θ [ofCylinder e (y, t)] = (e, [y], t)`
   and `Θ [ofStrip e (y, t)] = (e, [y], t)`, with the three inverse formulas. `Θ` and its inverse
   preserve height, also as continuous maps, and `Θ ∘ ρ = Φ` for the projection `ρ`. A point over a
   level `a i` goes to the class of its critical-fiber preimage in `V i`, and a point over a regular
   height `t ∈ K e` to the class of its regular-fiber preimage in `E e`.

## Naturality

For presentations over a common `S` and an arbitrary continuous `φ : X → X'` with `h' ∘ φ = h`,
`componentDataHom S φ hφ` has vertex maps `π₀ (vertexFiberMap φ i)` and edge maps
`π₀ (regularFiberMap φ e t)`, read at `RGraph.basePt S e` and independent of the regular height
`t`. Its incidence squares come from the incidence theorems for the component bijections of the
realizations and their naturality. It preserves identities and composition. The comparison is
natural: `Θ' ∘ Q φ = realize (componentDataHom φ) ∘ Θ` (`quotientComponentGraphMap_natural`); the
same square holds in the real slice for every slice morphism between realizations
(`quotientOverIso_natural`), and the data map is the classification of the conjugated graph map by
`RGraph.realizationFullyFaithful` (`componentDataHom_eq_preimage`).

For an object `A` with `iA : A ≅ (X, h)` over `ℝ`, `quotientIsoOfIso` applies the quotient functor
to `iA` and composes with the comparison; it is natural for every slice morphism between objects
presented over a common `S` (`quotientIsoOfIso_natural`). Across critical lists `S` and `S'`, write
`ΘA = quotientIsoOfIso S P iA` and `ΘB = quotientIsoOfIso S' P' iB`. Every slice morphism
`g : A ⟶ B` induces the graph map `inducedGraphMap S S' iA iB g = ΘA⁻¹ ≫ Q g ≫ ΘB`, and
`Q g ≫ ΘB = ΘA ≫ inducedGraphMap S S' iA iB g` (`inducedGraphMap_square`). Over a common list the
induced map is the realization of the component data map (`inducedGraphMap_eq_componentDataHom`).

## Constructible ℝ-spaces

`IsConstructibleSpace` holds for the objects of the real slice that are isomorphic to the
realization of a presentation with compact locally path-connected pieces. `ConstructibleSpaceCat`
is its full subcategory, so its morphisms are all continuous height-preserving maps. The Reeb
quotient of every such object is a graph object (`RGraph.isRGraph_quotient`,
`isRGraph_quotient_of_isConstructibleSpace`), and the quotient functor restricts to
`quotientRGraphFunctor : ConstructibleSpaceCat ⥤ RGraph.RGraphCat` on all morphisms, including maps
between objects presented over different critical lists. Graph objects are constructible
(`isConstructibleSpace_of_isRGraph`).

## Graph case

For finite data `D`, the map `D.toComponentData : D ⟶ (ofFiniteData D).componentData`, `x ↦ [x]`,
has bijective components (`toComponentDataIso`), and the projection homeomorphism
`RGraph.projHomeomorph` followed by `Θ` is its realization
(`quotientComponentGraphMap_projHomeomorph`, `projNatTrans_comp_quotientOverIso`).

See `docs/math/reeb-constructible-quotient.md`.
-/

open Set Topology CategoryTheory

universe u

namespace TDA.Reeb

noncomputable section

/-! ### Height-preserving maps into finite realizations -/

namespace RGraph

open CylinderPresentation

section descent

variable {n : ℕ} (S : CriticalValues n) {X : Type*} [TopologicalSpace X] {f : C(X, ℝ)}
  {D : FiniteReebData.{u} n}

/-- A height-preserving map into a finite realization is constant on Reeb classes: it carries a
path of constant height to a path in a finite discrete fiber. -/
theorem apply_eq_of_reebRel (g : C(X, (ofFiniteData D).Realization S))
    (hg : ∀ x, (ofFiniteData D).height S (g x) = f x) {x x' : X} (h : ReebRel f x x') :
    g x = g x' :=
  (reebRel_iff_eq S D (g x) (g x')).1 (h.map g hg)

/-- Descent of a height-preserving map into a finite realization through the Reeb quotient. -/
def quotientLift (g : C(X, (ofFiniteData D).Realization S))
    (hg : ∀ x, (ofFiniteData D).height S (g x) = f x) :
    C(ReebQuotient f, (ofFiniteData D).Realization S) :=
  ReebQuotient.lift g fun _ _ h => apply_eq_of_reebRel S g hg h

@[simp] theorem quotientLift_mk (g : C(X, (ofFiniteData D).Realization S))
    (hg : ∀ x, (ofFiniteData D).height S (g x) = f x) (x : X) :
    quotientLift S g hg (ReebQuotient.mk f x) = g x := rfl

end descent

end RGraph

namespace CylinderPresentation

/-! ### Component data and component classes -/

section data

variable {n : ℕ} (P : CylinderPresentation.{u} n)
  [∀ i, Finite (ZerothHomotopy (P.V i))] [∀ e, Finite (ZerothHomotopy (P.E e))]

/-- The component data of a presentation: vertex sets `π₀ (V i)`, edge sets `π₀ (E e)` and the
maps induced by the endpoint maps (DMP, proof of Proposition 2.12). Only finiteness of the
component sets is assumed. -/
abbrev componentData : FiniteReebData.{u} n where
  V i := ZerothHomotopy (P.V i)
  E e := ZerothHomotopy (P.E e)
  finiteV _ := inferInstance
  finiteE _ := inferInstance
  left e := componentMap (P.left e)
  right e := componentMap (P.right e)

/-- The class `[v]` of a vertex-piece point, in the vertex set of the realized component data. -/
def vertexClass (i : Fin (n + 1)) (v : P.V i) : (ofFiniteData P.componentData).V i :=
  ZerothHomotopy.mk v

/-- The class `[y]` of an edge-piece point, in the edge set of the realized component data. -/
def edgeClass (e : Fin n) (y : P.E e) : (ofFiniteData P.componentData).E e :=
  ZerothHomotopy.mk y

theorem vertexClass_surjective (i : Fin (n + 1)) : Function.Surjective (P.vertexClass i) :=
  ZerothHomotopy.mk_surjective

theorem edgeClass_surjective (e : Fin n) : Function.Surjective (P.edgeClass e) :=
  ZerothHomotopy.mk_surjective

/-- Two vertex-piece points have the same class exactly when they are joined in the piece. -/
theorem vertexClass_eq_iff {i : Fin (n + 1)} {v v' : P.V i} :
    P.vertexClass i v = P.vertexClass i v' ↔ Joined v v' :=
  ⟨fun h => Quotient.exact h, fun h => ZerothHomotopy.sound h.somePath⟩

theorem edgeClass_eq_iff {e : Fin n} {y y' : P.E e} :
    P.edgeClass e y = P.edgeClass e y' ↔ Joined y y' :=
  ⟨fun h => Quotient.exact h, fun h => ZerothHomotopy.sound h.somePath⟩

/-- The left endpoint map of the component data on classes. -/
@[simp] theorem left_edgeClass (e : Fin n) (y : P.E e) :
    (ofFiniteData P.componentData).left e (P.edgeClass e y) =
      P.vertexClass e.castSucc (P.left e y) := rfl

/-- The right endpoint map of the component data on classes. -/
@[simp] theorem right_edgeClass (e : Fin n) (y : P.E e) :
    (ofFiniteData P.componentData).right e (P.edgeClass e y) =
      P.vertexClass e.succ (P.right e y) := rfl

end data

/-! ### The comparison map on the realization -/

section map

variable {n : ℕ} (S : CriticalValues n) (P : CylinderPresentation.{u} n)
  [∀ i, Finite (ZerothHomotopy (P.V i))] [∀ e, Finite (ZerothHomotopy (P.E e))]
  [∀ i, LocallyPathConnectedSpace (P.V i)] [∀ e, LocallyPathConnectedSpace (P.E e)]

omit [∀ e, LocallyPathConnectedSpace (P.E e)] in
/-- `v ↦ [v]` is continuous into the vertex set of `G`, which carries the discrete topology. The
quotient topology of `π₀ (V i)` is discrete because path components of a locally path-connected
space are open (mathlib's `DiscreteTopology (ZerothHomotopy _)`); the identification of carriers
alone does not give this. -/
theorem continuous_vertexClass (i : Fin (n + 1)) : Continuous (P.vertexClass i) := by
  refine continuous_discrete_rng.2 fun c => ?_
  have h : P.vertexClass i ⁻¹' {c} =
      (ZerothHomotopy.mk : P.V i → ZerothHomotopy (P.V i)) ⁻¹' {(c : ZerothHomotopy (P.V i))} :=
    rfl
  rw [h]
  exact ZerothHomotopy.isQuotientMap_mk.continuous.isOpen_preimage _ (isOpen_discrete _)

omit [∀ i, LocallyPathConnectedSpace (P.V i)] in
/-- `y ↦ [y]` is continuous into the edge set of `G`, which carries the discrete topology, for a
locally path-connected edge piece. -/
theorem continuous_edgeClass (e : Fin n) : Continuous (P.edgeClass e) := by
  refine continuous_discrete_rng.2 fun c => ?_
  have h : P.edgeClass e ⁻¹' {c} =
      (ZerothHomotopy.mk : P.E e → ZerothHomotopy (P.E e)) ⁻¹' {(c : ZerothHomotopy (P.E e))} :=
    rfl
  rw [h]
  exact ZerothHomotopy.isQuotientMap_mk.continuous.isOpen_preimage _ (isOpen_discrete _)

/-- The pieces of the comparison: `v ↦ (i, [v])` on vertex pieces and `(y, t) ↦ (e, [y], t)` on
closed cylinders. The endpoint equations hold because `π₀ (left e) [y] = [left e y]`. -/
def componentCompatibleMaps :
    P.CompatibleMaps S ((ofFiniteData P.componentData).Realization S) where
  vertex i := ⟨fun v => (ofFiniteData P.componentData).ofVertex S i (P.vertexClass i v),
    ((ofFiniteData P.componentData).continuous_ofVertex S i).comp (P.continuous_vertexClass i)⟩
  cylinder e := ⟨fun p => (ofFiniteData P.componentData).ofCylinder S e (P.edgeClass e p.1, p.2),
    ((ofFiniteData P.componentData).continuous_ofCylinder S e).comp
      (((P.continuous_edgeClass e).comp continuous_fst).prodMk continuous_snd)⟩
  segBot_eq e y := (ofFiniteData P.componentData).ofCylinder_segBot S e (P.edgeClass e y)
  segTop_eq e y := (ofFiniteData P.componentData).ofCylinder_segTop S e (P.edgeClass e y)

/-- `Φ : X → G`, sending each raw point to the class of its piece. -/
def componentGraphMap : C(P.Realization S, (ofFiniteData P.componentData).Realization S) :=
  lift (P.componentCompatibleMaps S)

@[simp] theorem componentGraphMap_ofVertex (i : Fin (n + 1)) (v : P.V i) :
    P.componentGraphMap S (P.ofVertex S i v) =
      (ofFiniteData P.componentData).ofVertex S i (P.vertexClass i v) := rfl

@[simp] theorem componentGraphMap_ofCylinder (e : Fin n) (p : P.Cylinder S e) :
    P.componentGraphMap S (P.ofCylinder S e p) =
      (ofFiniteData P.componentData).ofCylinder S e (P.edgeClass e p.1, p.2) := rfl

@[simp] theorem componentGraphMap_ofStrip (e : Fin n) (p : P.E e × (S.K e : Set ℝ)) :
    P.componentGraphMap S (P.ofStrip S e p) =
      (ofFiniteData P.componentData).ofStrip S e (P.edgeClass e p.1, p.2) := rfl

/-- `Φ` preserves height. -/
theorem height_componentGraphMap (x : P.Realization S) :
    (ofFiniteData P.componentData).height S (P.componentGraphMap S x) = P.height S x := by
  obtain ⟨y, rfl⟩ := P.quotMk_surjective S x
  rcases y with ⟨i, v⟩ | ⟨e, p⟩ <;> rfl

/-- `Φ` is surjective: every point of `G` is `(i, [v])` or `(e, [y], t)`. -/
theorem componentGraphMap_surjective : Function.Surjective (P.componentGraphMap S) := by
  intro q
  rcases (ofFiniteData P.componentData).exists_rep S q with ⟨i, c, rfl⟩ | ⟨e, ⟨c, t⟩, rfl⟩
  · obtain ⟨v, rfl⟩ := P.vertexClass_surjective i c
    exact ⟨P.ofVertex S i v, rfl⟩
  · obtain ⟨y, rfl⟩ := P.edgeClass_surjective e c
    exact ⟨P.ofStrip S e (y, t), rfl⟩

/-- Fiber normal form, hard direction: points with the same image are Reeb-related. -/
theorem reebRel_of_componentGraphMap_eq {x x' : P.Realization S}
    (h : P.componentGraphMap S x = P.componentGraphMap S x') : ReebRel (P.height S) x x' := by
  rcases P.exists_rep S x with ⟨i, v, rfl⟩ | ⟨e, ⟨y, t⟩, rfl⟩ <;>
    rcases P.exists_rep S x' with ⟨i', v', rfl⟩ | ⟨e', ⟨y', t'⟩, rfl⟩
  · rw [componentGraphMap_ofVertex, componentGraphMap_ofVertex, ofVertex_eq_ofVertex_iff] at h
    obtain ⟨rfl, hv⟩ := Sigma.mk.inj_iff.1 h
    obtain ⟨γ⟩ := (P.vertexClass_eq_iff).1 (eq_of_heq hv)
    exact ⟨γ.map (P.continuous_ofVertex S i), fun _ => rfl⟩
  · rw [componentGraphMap_ofVertex, componentGraphMap_ofStrip] at h
    exact absurd h ((ofFiniteData P.componentData).ofVertex_ne_ofStrip S i _ e' _)
  · rw [componentGraphMap_ofVertex, componentGraphMap_ofStrip] at h
    exact absurd h.symm ((ofFiniteData P.componentData).ofVertex_ne_ofStrip S i' _ e _)
  · have ht : (t : ℝ) = t' := by
      have := congrArg ((ofFiniteData P.componentData).height S) h
      rwa [componentGraphMap_ofStrip, componentGraphMap_ofStrip, height_ofStrip,
        height_ofStrip] at this
    obtain rfl : e = e' := S.eq_of_mem_K_of_mem_Icc t.2 (ht ▸ Ioo_subset_Icc_self t'.2)
    obtain rfl : t = t' := Subtype.ext ht
    rw [componentGraphMap_ofStrip, componentGraphMap_ofStrip] at h
    obtain ⟨γ⟩ := (P.edgeClass_eq_iff).1
      (congrArg Prod.fst ((ofFiniteData P.componentData).ofStrip_injective S e h))
    exact ⟨γ.map (f := fun z => P.ofStrip S e (z, t))
      ((P.continuous_ofStrip S e).comp (continuous_id.prodMk continuous_const)), fun _ => rfl⟩

/-- **Fiber normal form**: two points have the same image exactly when they are Reeb-related. -/
theorem componentGraphMap_eq_iff {x x' : P.Realization S} :
    P.componentGraphMap S x = P.componentGraphMap S x' ↔ ReebRel (P.height S) x x' :=
  ⟨P.reebRel_of_componentGraphMap_eq S, fun h =>
    RGraph.apply_eq_of_reebRel S (P.componentGraphMap S) (P.height_componentGraphMap S) h⟩

/-- The comparison `Q → G` as a continuous map: the descent of `Φ`. -/
def quotientComponentGraphMap :
    C(ReebQuotient (P.height S), (ofFiniteData P.componentData).Realization S) :=
  RGraph.quotientLift S (P.componentGraphMap S) (P.height_componentGraphMap S)

@[simp] theorem quotientComponentGraphMap_mk (x : P.Realization S) :
    P.quotientComponentGraphMap S (ReebQuotient.mk _ x) = P.componentGraphMap S x := rfl

theorem quotientComponentGraphMap_injective :
    Function.Injective (P.quotientComponentGraphMap S) := by
  intro q q' h
  induction q using ReebQuotient.ind with
  | h x =>
    induction q' using ReebQuotient.ind with
    | h x' => exact (ReebQuotient.mk_eq_mk_iff _).2 ((P.componentGraphMap_eq_iff S).1 h)

theorem quotientComponentGraphMap_surjective :
    Function.Surjective (P.quotientComponentGraphMap S) := fun q => by
  obtain ⟨x, hx⟩ := P.componentGraphMap_surjective S q
  exact ⟨ReebQuotient.mk _ x, hx⟩

theorem quotientComponentGraphMap_bijective :
    Function.Bijective (P.quotientComponentGraphMap S) :=
  ⟨P.quotientComponentGraphMap_injective S, P.quotientComponentGraphMap_surjective S⟩

/-- The comparison preserves height. -/
theorem height_quotientComponentGraphMap (q : ReebQuotient (P.height S)) :
    (ofFiniteData P.componentData).height S (P.quotientComponentGraphMap S q) =
      ReebQuotient.height (P.height S) q := by
  induction q using ReebQuotient.ind with
  | h x => exact P.height_componentGraphMap S x

end map

/-! ### The homeomorphism -/

section compact

variable {n : ℕ} (S : CriticalValues n) (P : CylinderPresentation.{u} n)
  [∀ i, CompactSpace (P.V i)] [∀ e, CompactSpace (P.E e)]

/-- The Reeb quotient of a realization with compact pieces is compact (a continuous image). -/
theorem compactSpace_reebQuotient : CompactSpace (ReebQuotient (P.height S)) :=
  (ReebQuotient.mk_surjective _).compactSpace (ReebQuotient.continuous_mk _)

end compact

section homeomorph

variable {n : ℕ} (S : CriticalValues n) (P : CylinderPresentation.{u} n)
  [∀ i, CompactSpace (P.V i)] [∀ i, LocallyPathConnectedSpace (P.V i)]
  [∀ e, CompactSpace (P.E e)] [∀ e, LocallyPathConnectedSpace (P.E e)]

/-- **DMP Proposition 2.12.** For compact locally path-connected pieces, the Reeb quotient is
homeomorphic over `ℝ` to the finite realization of the component data, sending the class of each
raw point to the class of its piece. Continuity of the inverse comes from compactness of `Q` and
Hausdorffness of `G`. -/
def quotientComponentGraphHomeomorph :
    ReebQuotient (P.height S) ≃ₜ (ofFiniteData P.componentData).Realization S :=
  haveI := P.compactSpace_reebQuotient S
  (P.quotientComponentGraphMap S).continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective _ (P.quotientComponentGraphMap_bijective S))

theorem quotientComponentGraphHomeomorph_apply (q : ReebQuotient (P.height S)) :
    P.quotientComponentGraphHomeomorph S q = P.quotientComponentGraphMap S q := rfl

@[simp] theorem quotientComponentGraphHomeomorph_mk (x : P.Realization S) :
    P.quotientComponentGraphHomeomorph S (ReebQuotient.mk _ x) = P.componentGraphMap S x := rfl

/-- Vertex generator formula. -/
theorem quotientComponentGraphHomeomorph_mk_ofVertex (i : Fin (n + 1)) (v : P.V i) :
    P.quotientComponentGraphHomeomorph S (ReebQuotient.mk _ (P.ofVertex S i v)) =
      (ofFiniteData P.componentData).ofVertex S i (P.vertexClass i v) := rfl

/-- Cylinder generator formula. -/
theorem quotientComponentGraphHomeomorph_mk_ofCylinder (e : Fin n) (p : P.Cylinder S e) :
    P.quotientComponentGraphHomeomorph S (ReebQuotient.mk _ (P.ofCylinder S e p)) =
      (ofFiniteData P.componentData).ofCylinder S e (P.edgeClass e p.1, p.2) := rfl

/-- Open-strip generator formula. -/
theorem quotientComponentGraphHomeomorph_mk_ofStrip (e : Fin n) (p : P.E e × (S.K e : Set ℝ)) :
    P.quotientComponentGraphHomeomorph S (ReebQuotient.mk _ (P.ofStrip S e p)) =
      (ofFiniteData P.componentData).ofStrip S e (P.edgeClass e p.1, p.2) := rfl

/-- The homeomorphism preserves height. -/
theorem height_quotientComponentGraphHomeomorph (q : ReebQuotient (P.height S)) :
    (ofFiniteData P.componentData).height S (P.quotientComponentGraphHomeomorph S q) =
      ReebQuotient.height (P.height S) q :=
  P.height_quotientComponentGraphMap S q

/-- Compatibility with the projection: `Θ ∘ ρ = Φ`. -/
theorem quotientComponentGraphHomeomorph_comp_proj :
    (P.quotientComponentGraphHomeomorph S : C(_, _)).comp (ReebQuotient.proj (P.height S)) =
      P.componentGraphMap S := rfl

/-- Compatibility with height, as continuous maps: `height ∘ Θ = h̄`. -/
theorem height_comp_quotientComponentGraphHomeomorph :
    ((ofFiniteData P.componentData).height S).comp
        (P.quotientComponentGraphHomeomorph S : C(_, _)) =
      ReebQuotient.height (P.height S) :=
  ContinuousMap.ext (P.height_quotientComponentGraphHomeomorph S)

theorem quotientComponentGraphHomeomorph_symm_ofVertex (i : Fin (n + 1)) (v : P.V i) :
    (P.quotientComponentGraphHomeomorph S).symm
        ((ofFiniteData P.componentData).ofVertex S i (P.vertexClass i v)) =
      ReebQuotient.mk _ (P.ofVertex S i v) := by
  rw [Homeomorph.symm_apply_eq]
  rfl

theorem quotientComponentGraphHomeomorph_symm_ofCylinder (e : Fin n) (p : P.Cylinder S e) :
    (P.quotientComponentGraphHomeomorph S).symm
        ((ofFiniteData P.componentData).ofCylinder S e (P.edgeClass e p.1, p.2)) =
      ReebQuotient.mk _ (P.ofCylinder S e p) := by
  rw [Homeomorph.symm_apply_eq]
  rfl

theorem quotientComponentGraphHomeomorph_symm_ofStrip (e : Fin n)
    (p : P.E e × (S.K e : Set ℝ)) :
    (P.quotientComponentGraphHomeomorph S).symm
        ((ofFiniteData P.componentData).ofStrip S e (P.edgeClass e p.1, p.2)) =
      ReebQuotient.mk _ (P.ofStrip S e p) := by
  rw [Homeomorph.symm_apply_eq]
  rfl

/-- The inverse preserves height. -/
theorem height_quotientComponentGraphHomeomorph_symm
    (g : (ofFiniteData P.componentData).Realization S) :
    ReebQuotient.height (P.height S) ((P.quotientComponentGraphHomeomorph S).symm g) =
      (ofFiniteData P.componentData).height S g := by
  rw [← P.height_quotientComponentGraphHomeomorph S, Homeomorph.apply_symm_apply]

/-- Fiber form at a level: a point over `a i` goes to the class of its preimage in `V i` under the
critical-fiber homeomorphism. -/
theorem quotientComponentGraphHomeomorph_mk_of_height_eq_value {x : P.Realization S}
    {i : Fin (n + 1)} (hx : P.height S x = S.value i) :
    P.quotientComponentGraphHomeomorph S (ReebQuotient.mk _ x) =
      (ofFiniteData P.componentData).ofVertex S i
        (P.vertexClass i ((P.criticalFiberHomeomorph S i).symm ⟨x, hx⟩)) := by
  have hv : P.ofVertex S i ((P.criticalFiberHomeomorph S i).symm ⟨x, hx⟩) = x :=
    congrArg Subtype.val ((P.criticalFiberHomeomorph S i).apply_symm_apply ⟨x, hx⟩)
  calc P.quotientComponentGraphHomeomorph S (ReebQuotient.mk _ x)
      = P.quotientComponentGraphHomeomorph S (ReebQuotient.mk _
          (P.ofVertex S i ((P.criticalFiberHomeomorph S i).symm ⟨x, hx⟩))) := by
        rw [hv]
    _ = _ := rfl

/-- Fiber form at a regular height `t ∈ K e`: a point over `t` goes to the class of its preimage
in `E e` under the regular-fiber homeomorphism. -/
theorem quotientComponentGraphHomeomorph_mk_of_height_eq_regular {x : P.Realization S}
    {e : Fin n} (t : (S.K e : Set ℝ)) (hx : P.height S x = t) :
    P.quotientComponentGraphHomeomorph S (ReebQuotient.mk _ x) =
      (ofFiniteData P.componentData).ofStrip S e
        (P.edgeClass e ((P.regularFiberHomeomorph S e t).symm ⟨x, hx⟩), t) := by
  have hy : P.ofStrip S e ((P.regularFiberHomeomorph S e t).symm ⟨x, hx⟩, t) = x :=
    congrArg Subtype.val ((P.regularFiberHomeomorph S e t).apply_symm_apply ⟨x, hx⟩)
  calc P.quotientComponentGraphHomeomorph S (ReebQuotient.mk _ x)
      = P.quotientComponentGraphHomeomorph S (ReebQuotient.mk _
          (P.ofStrip S e ((P.regularFiberHomeomorph S e t).symm ⟨x, hx⟩, t))) := by
        rw [hy]
    _ = _ := rfl

/-- Under the constructible hypotheses the Reeb quotient is Hausdorff. This is a theorem, not a
global instance on `ReebQuotient`. -/
theorem t2Space_reebQuotient : T2Space (ReebQuotient (P.height S)) :=
  (P.quotientComponentGraphHomeomorph S).isEmbedding.t2Space

end homeomorph

/-! ### Naturality in arbitrary height-preserving maps (common `S`) -/

section naturality

variable {n : ℕ} (S : CriticalValues n) {P P' : CylinderPresentation.{u} n}
  [∀ i, Finite (ZerothHomotopy (P.V i))] [∀ e, Finite (ZerothHomotopy (P.E e))]
  [∀ i, Finite (ZerothHomotopy (P'.V i))] [∀ e, Finite (ZerothHomotopy (P'.E e))]
  (φ : C(P.Realization S, P'.Realization S)) (hφ : ∀ x, P'.height S (φ x) = P.height S x)

/-- The map of component data induced by an arbitrary continuous height-preserving `φ`: `π₀` of
the fiber maps `vertexFiberMap` and `regularFiberMap`, the edge map read at `RGraph.basePt`. The
incidence squares are the incidence theorems for component bijections (DMP diagrams (2.5))
transported by their naturality (2.6). Only finiteness of the component sets is assumed; local
path-connectedness is not used. -/
def componentDataHom : P.componentData.Hom P'.componentData where
  v i := componentMap (vertexFiberMap S φ hφ i)
  e k := componentMap (regularFiberMap S φ hφ k (RGraph.basePt S k))
  left_comm k c := by
    induction c using ZerothHomotopy.rec with
    | mk y =>
      apply (P'.vertexComponentsEquiv S k.castSucc).injective
      have h1 := P'.map_K_le_J_castSucc_edgeComponentsEquiv S k (RGraph.basePt S k)
        (componentMap (regularFiberMap S φ hφ k (RGraph.basePt S k)) (ZerothHomotopy.mk y))
      have h2 := congrArg ((componentNatTrans φ hφ).app (OpenInterval.toOpens (S.J k.castSucc)))
        (P.map_K_le_J_castSucc_edgeComponentsEquiv S k (RGraph.basePt S k) (ZerothHomotopy.mk y))
      rw [componentNatTrans_vertexComponentsEquiv] at h2
      rw [← componentNatTrans_edgeComponentsEquiv] at h1
      exact h1.symm.trans h2
  right_comm k c := by
    induction c using ZerothHomotopy.rec with
    | mk y =>
      apply (P'.vertexComponentsEquiv S k.succ).injective
      have h1 := P'.map_K_le_J_succ_edgeComponentsEquiv S k (RGraph.basePt S k)
        (componentMap (regularFiberMap S φ hφ k (RGraph.basePt S k)) (ZerothHomotopy.mk y))
      have h2 := congrArg ((componentNatTrans φ hφ).app (OpenInterval.toOpens (S.J k.succ)))
        (P.map_K_le_J_succ_edgeComponentsEquiv S k (RGraph.basePt S k) (ZerothHomotopy.mk y))
      rw [componentNatTrans_vertexComponentsEquiv] at h2
      rw [← componentNatTrans_edgeComponentsEquiv] at h1
      exact h1.symm.trans h2

theorem componentDataHom_v_mk (i : Fin (n + 1)) (v : P.V i) :
    (componentDataHom S φ hφ).v i (ZerothHomotopy.mk v) =
      ZerothHomotopy.mk (vertexFiberMap S φ hφ i v) := rfl

/-- The edge map does not depend on the regular height at which it is read. -/
theorem componentDataHom_e (k : Fin n) (t : (S.K k : Set ℝ)) :
    (componentDataHom S φ hφ).e k = componentMap (regularFiberMap S φ hφ k t) :=
  componentMap_regularFiberMap_indep S φ hφ k (RGraph.basePt S k) t

end naturality

section functoriality

variable {n : ℕ} (S : CriticalValues n) {P P' P'' : CylinderPresentation.{u} n}
  [∀ i, Finite (ZerothHomotopy (P.V i))] [∀ e, Finite (ZerothHomotopy (P.E e))]

/-- The identity induces the identity of component data. -/
theorem componentDataHom_id :
    componentDataHom S (ContinuousMap.id (P.Realization S)) (fun _ => rfl) =
      FiniteReebData.Hom.id P.componentData := by
  refine FiniteReebData.Hom.ext (funext fun i => funext fun c => ?_)
    (funext fun k => funext fun c => ?_)
  · induction c using ZerothHomotopy.rec with
    | mk v =>
      exact congrArg ZerothHomotopy.mk (P.ofVertex_injective S i
        (map_ofVertex_eq S (ContinuousMap.id _) (fun _ => rfl) i v).symm)
  · induction c using ZerothHomotopy.rec with
    | mk y =>
      exact congrArg ZerothHomotopy.mk (congrArg Prod.fst (P.ofStrip_injective S k
        (a₁ := (_, RGraph.basePt S k)) (a₂ := (y, RGraph.basePt S k))
        (map_ofStrip_eq S (ContinuousMap.id _) (fun _ => rfl) k (RGraph.basePt S k) y).symm))

variable [∀ i, Finite (ZerothHomotopy (P'.V i))] [∀ e, Finite (ZerothHomotopy (P'.E e))]
  [∀ i, Finite (ZerothHomotopy (P''.V i))] [∀ e, Finite (ZerothHomotopy (P''.E e))]

/-- Composition of height-preserving maps induces composition of component data maps. -/
theorem componentDataHom_comp (φ : C(P.Realization S, P'.Realization S))
    (hφ : ∀ x, P'.height S (φ x) = P.height S x) (ψ : C(P'.Realization S, P''.Realization S))
    (hψ : ∀ x, P''.height S (ψ x) = P'.height S x) :
    componentDataHom S (ψ.comp φ) (fun x => (hψ (φ x)).trans (hφ x)) =
      (componentDataHom S φ hφ).comp (componentDataHom S ψ hψ) := by
  refine FiniteReebData.Hom.ext (funext fun i => funext fun c => ?_)
    (funext fun k => funext fun c => ?_)
  · induction c using ZerothHomotopy.rec with
    | mk v =>
      refine congrArg ZerothHomotopy.mk (P''.ofVertex_injective S i ?_)
      rw [← map_ofVertex_eq, ← map_ofVertex_eq, ← map_ofVertex_eq]
      rfl
  · induction c using ZerothHomotopy.rec with
    | mk y =>
      refine congrArg ZerothHomotopy.mk (congrArg Prod.fst (P''.ofStrip_injective S k
        (a₁ := (_, RGraph.basePt S k)) (a₂ := (_, RGraph.basePt S k)) ?_))
      rw [← map_ofStrip_eq, ← map_ofStrip_eq, ← map_ofStrip_eq]
      rfl

end functoriality

section naturalityLPC

variable {n : ℕ} (S : CriticalValues n) {P P' : CylinderPresentation.{u} n}
  [∀ i, Finite (ZerothHomotopy (P.V i))] [∀ e, Finite (ZerothHomotopy (P.E e))]
  [∀ i, Finite (ZerothHomotopy (P'.V i))] [∀ e, Finite (ZerothHomotopy (P'.E e))]
  [∀ i, LocallyPathConnectedSpace (P.V i)] [∀ e, LocallyPathConnectedSpace (P.E e)]
  [∀ i, LocallyPathConnectedSpace (P'.V i)] [∀ e, LocallyPathConnectedSpace (P'.E e)]
  (φ : C(P.Realization S, P'.Realization S)) (hφ : ∀ x, P'.height S (φ x) = P.height S x)

/-- Naturality of `Φ` in an arbitrary continuous height-preserving map. -/
theorem componentGraphMap_natural (x : P.Realization S) :
    P'.componentGraphMap S (φ x) =
      realizeHom S (componentDataHom S φ hφ) (P.componentGraphMap S x) := by
  rcases P.exists_rep S x with ⟨i, v, rfl⟩ | ⟨e, ⟨y, t⟩, rfl⟩
  · rw [map_ofVertex_eq S φ hφ i v]
    rfl
  · rw [map_ofStrip_eq S φ hφ e t y]
    exact congrArg (fun c => (ofFiniteData P'.componentData).ofStrip S e (c, t))
      (congrFun (componentDataHom_e S φ hφ e t).symm (ZerothHomotopy.mk y))

/-- **Naturality of the comparison**: `Θ' ∘ Q_φ = realize (componentDataHom φ) ∘ Θ`. -/
theorem quotientComponentGraphMap_natural (q : ReebQuotient (P.height S)) :
    P'.quotientComponentGraphMap S (ReebQuotient.map φ hφ q) =
      realizeHom S (componentDataHom S φ hφ) (P.quotientComponentGraphMap S q) := by
  induction q using ReebQuotient.ind with
  | h x => exact componentGraphMap_natural S φ hφ x

end naturalityLPC

/-! ### The real slice (universe `0`) -/

section slice

variable {n : ℕ} (S : CriticalValues n)

/-- The continuous map underlying a slice morphism between realizations. -/
def overHomMap {P P' : CylinderPresentation.{0} n}
    (g : Over.mk (TopCat.ofHom (P.height S)) ⟶ Over.mk (TopCat.ofHom (P'.height S))) :
    C(P.Realization S, P'.Realization S) :=
  g.left.hom

theorem height_overHomMap {P P' : CylinderPresentation.{0} n}
    (g : Over.mk (TopCat.ofHom (P.height S)) ⟶ Over.mk (TopCat.ofHom (P'.height S)))
    (x : P.Realization S) : P'.height S (overHomMap S g x) = P.height S x :=
  overBaseMap_comm g x

/-- The comparison as an isomorphism of the real slice. -/
def quotientOverIso (P : CylinderPresentation.{0} n) [∀ i, CompactSpace (P.V i)]
    [∀ i, LocallyPathConnectedSpace (P.V i)] [∀ e, CompactSpace (P.E e)]
    [∀ e, LocallyPathConnectedSpace (P.E e)] :
    (ReebQuotient.quotientFunctor ℝ).obj (Over.mk (TopCat.ofHom (P.height S))) ≅
      RGraph.toOver S P.componentData :=
  Over.isoMk (TopCat.isoOfHomeo (P.quotientComponentGraphHomeomorph S))
    (by ext q; exact P.height_quotientComponentGraphHomeomorph S q)

/-- Transport to any object isomorphic over `ℝ` to a realization. -/
def quotientIsoOfIso {A : Over (TopCat.of ℝ)} (P : CylinderPresentation.{0} n)
    [∀ i, CompactSpace (P.V i)] [∀ i, LocallyPathConnectedSpace (P.V i)]
    [∀ e, CompactSpace (P.E e)] [∀ e, LocallyPathConnectedSpace (P.E e)]
    (i : A ≅ Over.mk (TopCat.ofHom (P.height S))) :
    (ReebQuotient.quotientFunctor ℝ).obj A ≅ RGraph.toOver S P.componentData :=
  (ReebQuotient.quotientFunctor ℝ).mapIso i ≪≫ P.quotientOverIso S

variable {P P' : CylinderPresentation.{0} n}
  [∀ i, CompactSpace (P.V i)] [∀ i, LocallyPathConnectedSpace (P.V i)]
  [∀ e, CompactSpace (P.E e)] [∀ e, LocallyPathConnectedSpace (P.E e)]
  [∀ i, CompactSpace (P'.V i)] [∀ i, LocallyPathConnectedSpace (P'.V i)]
  [∀ e, CompactSpace (P'.E e)] [∀ e, LocallyPathConnectedSpace (P'.E e)]

/-- Naturality in the slice for **every** slice morphism between realizations over `S`. -/
theorem quotientOverIso_natural
    (g : Over.mk (TopCat.ofHom (P.height S)) ⟶ Over.mk (TopCat.ofHom (P'.height S))) :
    (ReebQuotient.quotientFunctor ℝ).map g ≫ (P'.quotientOverIso S).hom =
      (P.quotientOverIso S).hom ≫
        (RGraph.realizationFunctor S).map
          (componentDataHom S (overHomMap S g) (height_overHomMap S g)) := by
  ext q
  exact quotientComponentGraphMap_natural S (overHomMap S g) (height_overHomMap S g) q

/-- The component data map is the classification of the conjugated graph map by
`RGraph.realizationFullyFaithful`. -/
theorem componentDataHom_eq_preimage
    (g : Over.mk (TopCat.ofHom (P.height S)) ⟶ Over.mk (TopCat.ofHom (P'.height S))) :
    componentDataHom S (overHomMap S g) (height_overHomMap S g) =
      (RGraph.realizationFullyFaithful S).preimage
        ((P.quotientOverIso S).inv ≫ (ReebQuotient.quotientFunctor ℝ).map g ≫
          (P'.quotientOverIso S).hom) := by
  apply (RGraph.realizationFullyFaithful S).map_injective
  rw [Functor.FullyFaithful.map_preimage, quotientOverIso_natural, Iso.inv_hom_id_assoc]

/-- Naturality of the transported comparison for every slice morphism `A ⟶ B`. -/
theorem quotientIsoOfIso_natural {A B : Over (TopCat.of ℝ)}
    (iA : A ≅ Over.mk (TopCat.ofHom (P.height S)))
    (iB : B ≅ Over.mk (TopCat.ofHom (P'.height S))) (g : A ⟶ B) :
    (ReebQuotient.quotientFunctor ℝ).map g ≫ (P'.quotientIsoOfIso S iB).hom =
      (P.quotientIsoOfIso S iA).hom ≫
        (RGraph.realizationFunctor S).map
          (componentDataHom S (overHomMap S (iA.inv ≫ g ≫ iB.hom))
            (height_overHomMap S (iA.inv ≫ g ≫ iB.hom))) := by
  simp only [quotientIsoOfIso, Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
  rw [← quotientOverIso_natural, ← Functor.map_comp_assoc, ← Functor.map_comp_assoc,
    Iso.hom_inv_id_assoc, Functor.map_comp_assoc]

end slice

/-! ### Comparison squares across critical lists -/

section crossList

variable {n n' : ℕ} (S : CriticalValues n) (S' : CriticalValues n')
  {P : CylinderPresentation.{0} n} {P' : CylinderPresentation.{0} n'}
  [∀ i, CompactSpace (P.V i)] [∀ i, LocallyPathConnectedSpace (P.V i)]
  [∀ e, CompactSpace (P.E e)] [∀ e, LocallyPathConnectedSpace (P.E e)]
  [∀ i, CompactSpace (P'.V i)] [∀ i, LocallyPathConnectedSpace (P'.V i)]
  [∀ e, CompactSpace (P'.E e)] [∀ e, LocallyPathConnectedSpace (P'.E e)]
  {A B : Over (TopCat.of ℝ)}

/-- The graph map induced by an arbitrary slice morphism `g : A ⟶ B` between objects presented
over possibly different critical lists `S` and `S'`: `ΘA⁻¹ ≫ Q g ≫ ΘB`, for the transported
comparisons `ΘA = quotientIsoOfIso S P iA` and `ΘB = quotientIsoOfIso S' P' iB`. -/
def inducedGraphMap (iA : A ≅ Over.mk (TopCat.ofHom (P.height S)))
    (iB : B ≅ Over.mk (TopCat.ofHom (P'.height S'))) (g : A ⟶ B) :
    RGraph.toOver S P.componentData ⟶ RGraph.toOver S' P'.componentData :=
  (P.quotientIsoOfIso S iA).inv ≫ (ReebQuotient.quotientFunctor ℝ).map g ≫
    (P'.quotientIsoOfIso S' iB).hom

/-- **Comparison square across critical lists**: `Q g ≫ ΘB = ΘA ≫ inducedGraphMap` for every slice
morphism `g : A ⟶ B`. -/
theorem inducedGraphMap_square (iA : A ≅ Over.mk (TopCat.ofHom (P.height S)))
    (iB : B ≅ Over.mk (TopCat.ofHom (P'.height S'))) (g : A ⟶ B) :
    (ReebQuotient.quotientFunctor ℝ).map g ≫ (P'.quotientIsoOfIso S' iB).hom =
      (P.quotientIsoOfIso S iA).hom ≫ inducedGraphMap S S' iA iB g := by
  rw [inducedGraphMap, Iso.hom_inv_id_assoc]

end crossList

section crossListCommon

variable {n : ℕ} (S : CriticalValues n) {P P' : CylinderPresentation.{0} n}
  [∀ i, CompactSpace (P.V i)] [∀ i, LocallyPathConnectedSpace (P.V i)]
  [∀ e, CompactSpace (P.E e)] [∀ e, LocallyPathConnectedSpace (P.E e)]
  [∀ i, CompactSpace (P'.V i)] [∀ i, LocallyPathConnectedSpace (P'.V i)]
  [∀ e, CompactSpace (P'.E e)] [∀ e, LocallyPathConnectedSpace (P'.E e)]
  {A B : Over (TopCat.of ℝ)}

/-- Over a common critical list, the induced graph map is the realization of the component data
map of the conjugated height-preserving map. -/
theorem inducedGraphMap_eq_componentDataHom (iA : A ≅ Over.mk (TopCat.ofHom (P.height S)))
    (iB : B ≅ Over.mk (TopCat.ofHom (P'.height S))) (g : A ⟶ B) :
    inducedGraphMap S S iA iB g =
      (RGraph.realizationFunctor S).map
        (componentDataHom S (overHomMap S (iA.inv ≫ g ≫ iB.hom))
          (height_overHomMap S (iA.inv ≫ g ≫ iB.hom))) := by
  rw [inducedGraphMap, quotientIsoOfIso_natural S iA iB g, Iso.inv_hom_id_assoc]

end crossListCommon

end CylinderPresentation

/-! ### Graph objects and constructible ℝ-spaces -/

namespace RGraph

/-- **Transport.** The Reeb quotient of any object isomorphic over `ℝ` to a realization with
compact locally path-connected pieces is a graph object. -/
theorem isRGraph_quotient {A : Over (TopCat.of ℝ)} {n : ℕ} (S : CriticalValues n)
    (P : CylinderPresentation.{0} n) [∀ i, CompactSpace (P.V i)]
    [∀ i, LocallyPathConnectedSpace (P.V i)] [∀ e, CompactSpace (P.E e)]
    [∀ e, LocallyPathConnectedSpace (P.E e)] (i : A ≅ Over.mk (TopCat.ofHom (P.height S))) :
    IsRGraph ((ReebQuotient.quotientFunctor ℝ).obj A) :=
  ⟨n, S, P.componentData, ⟨P.quotientIsoOfIso S i⟩⟩

end RGraph

/-- Constructible ℝ-spaces (DMP §2.2): objects of the real slice isomorphic to the realization of a
presentation whose pieces are compact and locally path-connected. -/
def IsConstructibleSpace : ObjectProperty (Over (TopCat.of ℝ)) := fun A =>
  ∃ (n : ℕ) (S : CriticalValues n) (P : CylinderPresentation.{0} n),
    (∀ i, CompactSpace (P.V i)) ∧ (∀ i, LocallyPathConnectedSpace (P.V i)) ∧
      (∀ e, CompactSpace (P.E e)) ∧ (∀ e, LocallyPathConnectedSpace (P.E e)) ∧
        Nonempty (A ≅ Over.mk (TopCat.ofHom (P.height S)))

/-- Constructible ℝ-spaces with **all** slice morphisms (continuous height-preserving maps). -/
abbrev ConstructibleSpaceCat := IsConstructibleSpace.FullSubcategory

theorem isRGraph_quotient_of_isConstructibleSpace {A : Over (TopCat.of ℝ)}
    (hA : IsConstructibleSpace A) : RGraph.IsRGraph ((ReebQuotient.quotientFunctor ℝ).obj A) := by
  obtain ⟨n, S, P, h1, h2, h3, h4, ⟨i⟩⟩ := hA
  exact RGraph.isRGraph_quotient S P i

/-- **The Reeb functor restricts to `ℝ-Top_c ⥤ Reeb`** (DMP Proposition 2.12 with the remark
after Proposition 2.13): the quotient functor on constructible ℝ-spaces lands in graph objects,
on all continuous height-preserving maps. -/
def quotientRGraphFunctor : ConstructibleSpaceCat ⥤ RGraph.RGraphCat :=
  RGraph.IsRGraph.lift (IsConstructibleSpace.ι ⋙ ReebQuotient.quotientFunctor ℝ)
    fun A => isRGraph_quotient_of_isConstructibleSpace A.property

/-- Graph objects are constructible ℝ-spaces (finite discrete pieces). -/
theorem isConstructibleSpace_of_isRGraph {A : Over (TopCat.of ℝ)} (hA : RGraph.IsRGraph A) :
    IsConstructibleSpace A := by
  obtain ⟨m, T, D, ⟨i⟩⟩ := hA
  exact ⟨m, T, CylinderPresentation.ofFiniteData D, fun _ => inferInstance,
    fun _ => inferInstance, fun _ => inferInstance, fun _ => inferInstance, ⟨i⟩⟩

/-! ### The graph case -/

namespace FiniteReebData

open CylinderPresentation

variable {n : ℕ}

/-- The canonical map `D ⟶ π₀`-data of its realization, `x ↦ [x]`. -/
def toComponentData (D : FiniteReebData.{u} n) : D.Hom (ofFiniteData D).componentData where
  v i x := (ofFiniteData D).vertexClass i x
  e k y := (ofFiniteData D).edgeClass k y
  left_comm _ _ := rfl
  right_comm _ _ := rfl

theorem toComponentData_v_bijective (D : FiniteReebData.{u} n) (i : Fin (n + 1)) :
    Function.Bijective (D.toComponentData.v i) :=
  ⟨fun _ _ h => joined_eq_of_discrete (A := (ofFiniteData D).V i)
      ((ofFiniteData D).vertexClass_eq_iff.1 h),
    (ofFiniteData D).vertexClass_surjective i⟩

theorem toComponentData_e_bijective (D : FiniteReebData.{u} n) (k : Fin n) :
    Function.Bijective (D.toComponentData.e k) :=
  ⟨fun _ _ h => joined_eq_of_discrete (A := (ofFiniteData D).E k)
      ((ofFiniteData D).edgeClass_eq_iff.1 h),
    (ofFiniteData D).edgeClass_surjective k⟩

/-- `D ≅ π₀`-data of its realization, in the category of finite data. -/
def toComponentDataIso (D : FiniteReebData.{u} n) : D ≅ (ofFiniteData D).componentData where
  hom := D.toComponentData
  inv := D.toComponentData.inv (toComponentData_v_bijective D) (toComponentData_e_bijective D)
  hom_inv_id := Hom.comp_inv _ _ _
  inv_hom_id := Hom.inv_comp _ _ _

end FiniteReebData

namespace CylinderPresentation

variable {n : ℕ} (S : CriticalValues n)

/-- **Graph case.** The projection homeomorphism `RGraph.projHomeomorph` followed by the comparison
is the realization of the canonical data isomorphism. -/
theorem quotientComponentGraphMap_projHomeomorph (D : FiniteReebData.{u} n)
    (x : (ofFiniteData D).Realization S) :
    (ofFiniteData D).quotientComponentGraphMap S (RGraph.projHomeomorph S D x) =
      realizeHom S D.toComponentData x := by
  rcases (ofFiniteData D).exists_rep S x with ⟨i, v, rfl⟩ | ⟨e, p, rfl⟩ <;> rfl

/-- Graph case in the slice: `ρ ≫ Θ = realize (D ≅ π₀-data)`. -/
theorem projNatTrans_comp_quotientOverIso (D : FiniteReebData.{0} n) :
    (ReebQuotient.projNatTrans ℝ).app (Over.mk (TopCat.ofHom ((ofFiniteData D).height S))) ≫
        ((ofFiniteData D).quotientOverIso S).hom =
      (RGraph.realizationFunctor S).map D.toComponentData := by
  ext x
  exact quotientComponentGraphMap_projHomeomorph S D x

end CylinderPresentation

end

end TDA.Reeb
