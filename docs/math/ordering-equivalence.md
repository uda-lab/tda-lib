# Ordering equivalence and attained ranges

For filters `f : FilterFunction K α` and `g : FilterFunction K β`, ordering equivalence means
that for every pair of actual nonempty faces `s` and `t`,

```text
f.value s ≤ f.value t  ↔  g.value s ≤ g.value t.
```

This is a comparison of weak orders, so it preserves ties as well as strict ordering. The grade
types can differ and need only be linearly ordered. The definition and its six theorems add no
finiteness, decidable-vertex, nonempty-face, or inhabited-grade hypotheses.

The characterization theorem states that this relation holds exactly when there is an order
isomorphism
`Set.range f.value ≃o Set.range g.value` whose value at each attained `f`-grade is the
corresponding attained `g`-grade on the same face. The map is existential theory data; the API
does not choose a public representative or promise an executable construction. In the forward
proof, each range point supplies its own face witness. The tie theorem makes the chosen image
independent of the witness. The resulting order embedding is surjective because every point in
the target range is attained by a face, and mathlib's `OrderIso.ofSurjective` packages it as an
order isomorphism. The reverse direction uses the order isomorphism's comparison equivalence
and the specified face-wise value law.

The tie theorem follows by transferring both weak comparisons and applying antisymmetry, in
both directions. For the sublevel theorem, membership provides an actual-face witness; the
definition of ordering equivalence then transfers that face's comparison with the attained
grade. Thus the two subcomplexes agree, including on absent ambient vertices.

## Boundary cases

If `K = ⊥`, the actual-face type is empty. Filters into `Unit` and `Empty` are both valid, their
ordering equivalence is vacuous, and both attained ranges are empty and order-isomorphic. This
does not imply a total function `Unit → Empty`; such a function is impossible. The public
characterization therefore uses the attained ranges and makes no ambient-grade extension
claim.

Sublevel equality is only at corresponding attained grades. For a singleton complex with
constant grade `()` in `Unit` and constant grade `0` in `ℤ`, the filters are ordering-equivalent.
The `Unit` sublevel at `()` is the singleton complex, while the `ℤ` sublevel at `-1` is bottom.
Consequently, the result does not identify arbitrary ambient-threshold sublevel families.

The edge fixtures use actual vertices with tied grade `0`, an edge with grade `1`, and the
second filter `2 * f + 1`. They check the face-wise range map and all attained sublevel
equalities. A separate edge fixture breaks the vertex tie while preserving all forward strict
comparisons, demonstrating why one-way strict preservation is insufficient. Concrete
`ℕ`/`ℤ` fixtures instantiate the range theorem in both grade directions, including its
`iff.mpr` direction, and a private theorem checks uniqueness of a range isomorphism satisfying
the face-wise law.

## Source and conventions

- [`FilterFunction.lean`](../../TDA/Filtration/FilterFunction.lean), blob
  `bcf4907aaec0a1cb2ce116c661230a115fdf4a65`, assigns grades to
  `TDA.Simplicial.TotalFace K` and supplies `mem_sublevel_iff`; the proof reuses this API rather
  than defining another face domain or filtration.
- [`Bridge.lean`](../../TDA/Simplicial/Bridge.lean), blob
  `a811965673ef1d3da54efe0aef768bcbf3ae1d50`, defines `TotalFace` as the subtype of
  nonempty faces belonging to `K`. No absent vertex or empty face is introduced.
- The checked repository baseline is develop
  [`b3f8542fc361936914ab7795d5aa00e3cc4d2c0b`](https://github.com/uda-lab/tda-lib/commit/b3f8542fc361936914ab7795d5aa00e3cc4d2c0b).
  Mathlib remains pinned at
  [`0df444a360eaa60ab8c11dca51a86af692955474`](https://github.com/leanprover-community/mathlib4/tree/0df444a360eaa60ab8c11dca51a86af692955474);
  its existing
  [`OrderIso.ofSurjective`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Order/Hom/Basic.lean)
  is used to package the order embedding and surjectivity proof. No dependency or pin changes
  are needed.
- The result is an elementary characterization of the displayed definition and the existing
  filter API. It makes no claim to translate a numbered external persistence theorem, and does
  not establish compatible face orders, simplex prefixes, topology, homology, reductions,
  persistence diagrams, or barcodes. The relation is available for later independent units to
  use pointwise.
