# Open-set path-component functors

## Components of inverse images

Let `X` and `Y` be topological spaces and `f : C(X, Y)`. For an open set `U` of `Y`,
`componentFunctor f` assigns

```lean
(componentFunctor f).obj U = ZerothHomotopy {x : X // f x ∈ U}
```

the path components of the inverse image with its induced topology. Paths stay inside the
inverse image. These are neither connected components nor path components of `X` intersected
with the inverse image. Path components and connected components are not identified for
arbitrary spaces: such a comparison needs local path connectedness of the inverse images and is
not part of this API.

For `U ≤ V`, the structure map sends the class of a point to the class of the same point in the
larger inverse image (`componentFunctor_map_mk`). The functor is covariant on the preorder
category of `TopologicalSpace.Opens Y`; no opposite category is used. The carrier universe of
`X` and the base universe of `Y` are independent. The value at `⊥` is empty for every `X` and
`f`, as are all values when the domain or the base is empty.

## Maps commuting with the base map

For `g : C(Z, Y)` and `h : C(X, Z)` with `g (h x) = f x` for every `x`, `h` restricts to each
inverse image and induces `componentNatTrans h comm : componentFunctor f ⟶ componentFunctor g`,
sending the class of `x` to the class of `h x`. Identities give identities, and composition is
diagrammatic: `componentNatTrans (k.comp h) _ = componentNatTrans h _ ≫ componentNatTrans k _`.
The commuting equation is a proposition, so the transformation does not depend on its proof.
The categorical API requires `X` and `Z` to share a carrier universe so that both functors land in
the same `Type u`. The raw map `componentMap : C(X, Z) → ZerothHomotopy X → ZerothHomotopy Z`
allows independent carrier universes. Induced maps on components need not be injective.

Pinned mathlib provides the path-component quotient `ZerothHomotopy` but no map induced by a
continuous map on it; `componentMap` is a thin wrapper around `ZerothHomotopy.lift` and
`Joined.map`. The preimage inclusion agrees definitionally with `ContinuousMap.inclusion`.

## Source correspondence

de Silva, Munch and Patel assign path components of inverse images to open intervals of `ℝ`
and map them by inclusions (*Categorified Reeb Graphs*, §3.1 Example 3.3). A continuous map
commuting with the height functions induces a natural transformation (§3.4, before
Proposition 3.15). The Lean API indexes by all open sets of an arbitrary base space. This is an
elementary generalization chosen by the library, not a statement printed in the paper;
restriction to open intervals recovers the source construction. The cosheaf (gluing) property of
Proposition 3.15 is not part of this API, so the functor is not called a cosheaf.

Sources: [de Silva, Munch and Patel, *Categorified Reeb Graphs*](https://arxiv.org/abs/1501.04147);
[pinned mathlib path components](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Topology/Connected/PathConnected.lean).
