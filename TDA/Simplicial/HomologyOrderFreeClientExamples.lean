import TDA.Simplicial.HomologyOrderFree
import TDA.Filtration.Rips
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Field.ZMod

set_option autoImplicit false

/-!
# Client statements of order-free simplicial homology

Regression fixtures for #1300, family 16 of the downstream-use audit (#1207). Each statement is
written as a downstream client writes it. The inputs are a finite subset `S` of the Euclidean
plane as vertex type `↥S` with the instances found for a subtype of a `Finset`, two supplied
linear orders on `↥S`, and vertex types in `Type 1` with coefficient rings in `Type 2`; the
order-free statements choose the vertex order internally.

* The degree-zero homology of the full complex on a finite nonempty subset of the plane has
  dimension one over `ZMod 2`.
* The comparison isomorphism and the naturality square for vertex types that carry an order only
  in the statement of the comparison.
* Homology for two supplied orders on the vertices of a finite subset of the plane.
* Vertex types and coefficient rings in different universes.
-/

namespace TDA.Simplicial.HomologyOrderFreeClientExamples

/-- The full complex on a finite nonempty subset of the plane has order-free degree-zero homology
of dimension one over `ZMod 2`. -/
theorem plane_finrank_top_zero (S : Finset (EuclideanSpace ℝ (Fin 2))) [Nonempty S] :
    Module.finrank (ZMod 2)
        (simplicialHomologyOrderFree (⊤ : PreAbstractSimplicialComplex S) (ZMod 2) 0) = 1 :=
  finrank_simplicialHomologyOrderFree_top_zero (ZMod 2)

open CategoryTheory in
/-- The order-free homology of the Rips full complex of a finite subset of the plane is
isomorphic to the homology for every supplied order. -/
theorem plane_homologyOrderFree_nonempty_iso (S : Finset (EuclideanSpace ℝ (Fin 2)))
    [LinearOrder S] (n : ℕ) :
    Nonempty (simplicialHomologyOrderFree (TDA.Filtration.Rips.fullComplex S) (ZMod 2) n ≅
      simplicialHomology (TDA.Filtration.Rips.fullComplex S) (ZMod 2) n) :=
  ⟨simplicialHomologyOrderFreeIso _ _ n⟩

open CategoryTheory in
/-- Homology of the Rips full complex of a finite subset of the plane for two supplied orders is
isomorphic. -/
theorem plane_homology_nonempty_iso_of_orders (S : Finset (EuclideanSpace ℝ (Fin 2)))
    (o₁ o₂ : LinearOrder S) (n : ℕ) :
    Nonempty (@simplicialHomology S o₁ (TDA.Filtration.Rips.fullComplex S) (ZMod 2) _ n ≅
      @simplicialHomology S o₂ (TDA.Filtration.Rips.fullComplex S) (ZMod 2) _ n) :=
  ⟨simplicialHomologyIso_of_linearOrder o₁ o₂ _ _ n⟩

open CategoryTheory in
/-- The order-free homology map of a vertex map between Rips full complexes of finite subsets of
the plane is natural against the comparison isomorphisms. -/
theorem plane_homologyMapOrderFree_naturality (S T : Finset (EuclideanSpace ℝ (Fin 2)))
    [LinearOrder S] [LinearOrder T]
    (f : VertexMap (TDA.Filtration.Rips.fullComplex S) (TDA.Filtration.Rips.fullComplex T))
    (n : ℕ) :
    simplicialHomologyMapOrderFree (ZMod 2) n f ≫ (simplicialHomologyOrderFreeIso _ _ n).hom =
      (simplicialHomologyOrderFreeIso _ _ n).hom ≫ simplicialHomologyMap (ZMod 2) f n :=
  simplicialHomologyMapOrderFree_iso_naturality _ n f

/-- The dimension statement with vertices in `Type 1` and a field in `Type 2`. -/
theorem universes_finrank_top_zero (V : Type 1) [Finite V] [Nonempty V] (k : Type 2) [Field k] :
    Module.finrank k (simplicialHomologyOrderFree (⊤ : PreAbstractSimplicialComplex V) k 0) =
      1 :=
  finrank_simplicialHomologyOrderFree_top_zero k

open CategoryTheory in
/-- The order-free homology map for vertex types in `Type 1` and a ring in `Type 2`, followed by
the comparison isomorphisms, for supplied orders. -/
theorem universes_homologyMapOrderFree_naturality (V W : Type 1) [LinearOrder V]
    [LinearOrder W] (K : PreAbstractSimplicialComplex V) (L : PreAbstractSimplicialComplex W)
    (R : Type 2) [Ring R] (f : VertexMap K L) (n : ℕ) :
    simplicialHomologyMapOrderFree R n f ≫ (simplicialHomologyOrderFreeIso L R n).hom =
      (simplicialHomologyOrderFreeIso K R n).hom ≫ simplicialHomologyMap R f n :=
  simplicialHomologyMapOrderFree_iso_naturality R n f

end TDA.Simplicial.HomologyOrderFreeClientExamples
