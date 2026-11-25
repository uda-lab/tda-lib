# Alexandrov sheaves of persistence modules

## Setting

Let `X` be a preorder with its upper Alexandrov topology: the open sets are exactly the upper
sets. For `p : X` the principal open `↑p = {y | p ≤ y}` is the smallest open set containing
`p`, and `p ≤ q` holds exactly when `↑q ⊆ ↑p`. Mathlib's `Alexandrov.principals X` is the
functor `L : X ⥤ (Opens X)ᵒᵖ` sending `p` to `↑p`; it is fully faithful because an inclusion
`↑q ⊆ ↑p` forces `p ≤ q` (as `q ∈ ↑q`) and both categories are thin.

Let `C` be a complete category. The construction runs at Mathlib's universe level:
`X : TopCat.{v}` and `[Category.{v} C]`, so that the comma categories below are small.

## The two functors

**Sections over principal opens.** `Γ` sends a sheaf `F` to `L ⋙ F`: its value at `p` is
`F(↑p)`, and for `p ≤ q` its map is the restriction of `F` along `↑q ⊆ ↑p`. A persistence
module is covariant, and restriction goes from the larger open `↑p` to the smaller `↑q`, so
both directions agree.

**Kan extension.** `A` sends a diagram `M : X ⥤ C` to the pointwise right Kan extension of `M`
along `L`. Its sections over an open `U` are the limit of `M` over the comma category of
pairs `(p, ↑p ⊆ U)`, that is, over the points of `U` with the order of `X`. Mathlib proves that
this presheaf is a sheaf.

## The equivalence

**Counit.** At `p`, the comma category of `↑p` has the initial object `(p, 𝟙)`, so the limit
projection there is an isomorphism `Γ(A M)(p) ≅ M(p)`; equivalently, the counit of a pointwise
right Kan extension along a fully faithful functor is invertible. Under these isomorphisms the
transition map of `Γ(A M)` is `M(p ≤ q)`.

**Unit.** For a sheaf `F` and an open `U`, restriction gives a map from `F(U)` to the limit of
the `F(↑p)` with `↑p ⊆ U`. On a principal open it is inverse to the counit of `Γ F`. The
principal opens form a basis of the topology: each point `x` of an open `U` lies in
`↑x ⊆ U`. A morphism of sheaves that is invertible on a basis is invertible, so the comparison
is an isomorphism on every open. The sheaf condition of `F` is used here; no gluing data is
supplied separately. In particular `F(∅)` is terminal, matching the limit over the empty
comma category, and on a non-principal open such as the whole two-point antichain the
sections are the product of the sections over the two points.

Together these give an equivalence between sheaves on `X` with values in `C` and diagrams
`X ⥤ C`, natural in both directions, whose triangle identity holds on the nose.

## Unbundled preorders

For a preorder `P` that carries another topology, such as `ℝ`, the upper Alexandrov topology
lives on the type synonym `WithUpperSet P`, with the order isomorphism to `P`. Diagrams
`P ⥤ C`, in particular persistence modules `PModule K ℝ = ℝ ⥤ ModuleCat K`, correspond to sheaves
on `WithUpperSet P`; the topology of `P` is not changed. The open set `(-∞, 0)` of `ℝ` is not
open in `WithUpperSet ℝ`.

## Limits

This is a statement about the upper Alexandrov topology. It is not an equivalence with sheaves
on `ℝ` or `ℝⁿ` for their ordinary topology, and it involves no metric, derived category or
convolution.
