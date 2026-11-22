import TDA.Persistence.SublevelDiagram
import TDA.Persistence.RealBarcodeRankUniqueness
import TDA.Simplicial.VertexChainMap

/-!
# Sublevel diagrams of filtered complexes related by vertex maps

Two filtered complexes may live over different vertex types, for example a complex on labels
`Fin N` and its copy on the natural numbers. This module compares their homology and their
diagrams through the existing signed maps of `TDA.Simplicial.VertexChainMap`.

* `simplicialHomologyMap_congr`: vertex maps that agree on the vertices of every face of the
  source induce the same map in homology. The ambient functions may differ elsewhere.
* `simplicialHomologyMap_comp_eq_id`: a vertex map followed by one that undoes it on the
  vertices of the faces induces the identity in homology.
* `dgm_eq_of_vertexMaps`: real filter functions on complexes over two vertex types have the
  same diagram, in every degree and over every field, when functions on the vertices in both
  directions preserve every sublevel complex and are mutually inverse on the vertices of the
  faces.

The two functions of `dgm_eq_of_vertexMaps` are total on the ambient vertex types and are
constrained on faces only; neither injectivity nor monotonicity is assumed. The induced maps
of sublevel homology are mutually inverse and commute with the inclusions, so all inclusions
have equal ranks; `rank_sublevelHomologyMap` and
`RealBarcode.multiset_eq_of_rankCounts_eq` recover the points. The statement is for real
grades, the generality of that uniqueness theorem, and for vertex types in the universe of the
field, as `dgm` requires.

These are elementary library results, not attributed to a source.
-/

set_option autoImplicit false

universe u

namespace TDA.Simplicial

open CategoryTheory

variable {V W : Type u} [LinearOrder V] [LinearOrder W]
variable {K : PreAbstractSimplicialComplex V} {L : PreAbstractSimplicialComplex W}

private theorem vertexChainMap_congr (R : Type*) [Ring R] (f g : VertexMap K L)
    (h : ∀ s ∈ K, ∀ v ∈ s, f v = g v) (n : ℕ) :
    vertexChainMap R f n = vertexChainMap R g n := by
  apply Finsupp.lhom_ext
  intro s a
  rw [vertexChainMap_single, vertexChainMap_single]
  have he : f ∘ s.1.orderEmbOfFin s.2.2 = g ∘ s.1.orderEmbOfFin s.2.2 := by
    funext i
    exact h s.1 s.2.1 _ (Finset.orderEmbOfFin_mem _ _ _)
  rw [he]

/-- Vertex maps that agree on the vertices of every face induce the same map in homology. -/
theorem simplicialHomologyMap_congr (R : Type*) [Ring R] (f g : VertexMap K L)
    (h : ∀ s ∈ K, ∀ v ∈ s, f v = g v) (n : ℕ) :
    simplicialHomologyMap R f n = simplicialHomologyMap R g n := by
  have hc : simplicialChainMap R f = simplicialChainMap R g := by
    apply HomologicalComplex.hom_ext
    intro i
    simp only [simplicialChainMap_f]
    rw [vertexChainMap_congr R f g h i]
  unfold simplicialHomologyMap
  rw [hc]

/-- A vertex map followed by a vertex map that undoes it on the vertices of the faces induces
the identity in homology. -/
theorem simplicialHomologyMap_comp_eq_id (R : Type*) [Ring R] (f : VertexMap K L)
    (g : VertexMap L K) (h : ∀ s ∈ K, ∀ v ∈ s, g (f v) = v) (n : ℕ) :
    simplicialHomologyMap R f n ≫ simplicialHomologyMap R g n =
      𝟙 (simplicialHomology K R n) := by
  rw [← simplicialHomologyMap_comp, ← simplicialHomologyMap_id]
  exact simplicialHomologyMap_congr R _ _ h n

end TDA.Simplicial

namespace TDA.Persistence

open TDA.Simplicial TDA.Filtration CategoryTheory

variable {V W : Type u} [LinearOrder V] [LinearOrder W]
variable {K : PreAbstractSimplicialComplex V} {L : PreAbstractSimplicialComplex W}

/-- Isomorphisms on the vertical sides of a commuting square preserve the image rank. -/
theorem finrank_range_eq_of_iso_square {k : Type*} [Field k] {A B C E : ModuleCat k}
    (F : A ⟶ B) (G : C ⟶ E) (e₁ : A ≅ C) (e₂ : B ≅ E) (h : F ≫ e₂.hom = e₁.hom ≫ G) :
    Module.finrank k (LinearMap.range F.hom) = Module.finrank k (LinearMap.range G.hom) := by
  have hG : G.hom ∘ₗ e₁.hom.hom = e₂.hom.hom ∘ₗ F.hom := by
    rw [← ModuleCat.hom_comp, ← ModuleCat.hom_comp, h]
  have hs : LinearMap.range e₁.hom.hom = ⊤ :=
    LinearMap.range_eq_top.2 e₁.toLinearEquiv.surjective
  have hi : Function.Injective e₂.hom.hom := e₂.toLinearEquiv.injective
  rw [← LinearMap.range_comp_of_range_eq_top G.hom hs, hG, LinearMap.range_comp]
  exact (Submodule.equivMapOfInjective e₂.hom.hom hi (LinearMap.range F.hom)).finrank_eq

/-- Real sublevel diagrams are invariant under vertex maps in both directions that preserve
every sublevel complex and are mutually inverse on the vertices of the faces. -/
theorem dgm_eq_of_vertexMaps (k : Type u) [Field k]
    [Fintype (TotalFace K)] [Fintype (TotalFace L)]
    (f : FilterFunction K ℝ) (g : FilterFunction L ℝ) (φ : V → W) (ψ : W → V)
    (hφ : ∀ r s, s ∈ f.sublevel r → s.image φ ∈ g.sublevel r)
    (hψ : ∀ r t, t ∈ g.sublevel r → t.image ψ ∈ f.sublevel r)
    (hψφ : ∀ s ∈ K, ∀ v ∈ s, ψ (φ v) = v) (hφψ : ∀ t ∈ L, ∀ w ∈ t, φ (ψ w) = w)
    (n : ℕ) : dgm k f n = dgm k g n := by
  let Φ : ∀ r, VertexMap (f.sublevel r) (g.sublevel r) := fun r =>
    ⟨φ, fun s hs => by convert hφ r s hs⟩
  let Ψ : ∀ r, VertexMap (g.sublevel r) (f.sublevel r) := fun r =>
    ⟨ψ, fun t ht => by convert hψ r t ht⟩
  let e : ∀ r,
      simplicialHomology (f.sublevel r) k n ≅ simplicialHomology (g.sublevel r) k n :=
    fun r =>
      ⟨simplicialHomologyMap k (Φ r) n, simplicialHomologyMap k (Ψ r) n,
        simplicialHomologyMap_comp_eq_id k (Φ r) (Ψ r)
          (fun s hs v hv => hψφ s (f.sublevel_le r hs) v hv) n,
        simplicialHomologyMap_comp_eq_id k (Ψ r) (Φ r)
          (fun t ht w hw => hφψ t (g.sublevel_le r ht) w hw) n⟩
  apply Diagram.ext
  apply RealBarcode.multiset_eq_of_rankCounts_eq _ _ (dgm_isPositive k f n)
    (dgm_isPositive k g n)
  intro s t hst
  rw [← rank_sublevelHomologyMap k f n s t hst, ← rank_sublevelHomologyMap k g n s t hst]
  apply finrank_range_eq_of_iso_square _ _ (e s) (e t)
  change simplicialHomologyIncl k (f.sublevel_mono hst) n ≫
      simplicialHomologyMap k (Φ t) n =
    simplicialHomologyMap k (Φ s) n ≫ simplicialHomologyIncl k (g.sublevel_mono hst) n
  rw [← simplicialHomologyMap_inclusion, ← simplicialHomologyMap_inclusion,
    ← simplicialHomologyMap_comp, ← simplicialHomologyMap_comp]
  rfl

end TDA.Persistence
