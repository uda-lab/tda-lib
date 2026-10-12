# Diagrams of actual finite sublevel homology

For a filter function `f : FilterFunction K α` on a finite collection of actual
faces, `dgm k f n` labels the bars of `gradeHomologyBarcode k f n` by the distinct
attained values `f.criticalValue`. It is exactly
`ofIndexBars f.criticalValue f.criticalValue.strictMono (gradeHomologyBarcode k f n)`.
The vertex and field types share a universe; the ordered value type has an
independent universe. The value order needs no density, nonemptiness or
unboundedness assumption. The bottom filter also works with `Empty` as its
value type, without choosing a threshold.

`dgm_isPositive` proves strict birth-before-death for every point.
`rank_sublevelHomologyMap` gives, for every `r ≤ s`,

```text
finrank k (range (Hₙ(f.sublevel r) → Hₙ(f.sublevel s)))
  = #{(b,d) in dgm k f n | b ≤ r and s < d}.
```

The map is `simplicialHomologyIncl` for the actual sublevel inclusion. Birth is
inclusive and death is strict, including critical endpoints and self maps.
The count is a multiset count, so repeated points retain their multiplicities.
`dgm_eq_ofIndexBars_of_iso` identifies the diagram with a specified barcode
when the caller supplies a natural isomorphism from the actual critical-grade
homology module to that barcode module. The isomorphism remains an input;
the rank construction supplies no decomposition existence theorem.

The proof uses attained faces to reflect each threshold cut. Every sublevel is
bottom or an actual critical stage, and a stage equality identifies precisely
which attained values lie below the threshold. Equality-induced homology maps
form a commuting inclusion square. That square identifies the actual map's
range rank with the critical-grade map rank. The same cut facts transport the
birth/death predicate on every diagram point. Actual bottom homology vanishes
in every degree through the empty chains, cycles, boundary quotient and
`homologyKernelQuotient`.

In a gap, equality transport identifies the actual inclusion with the identity
of the stage homology. Above the final attained value, both sublevels are `K`
and the transported actual inclusion is the identity of `Hₙ(K;k)`. Thus the
tail map rank and the number of essential points both equal the actual
terminal homology dimension. Death `N` of an index bar is labelled `⊤` in
`WithTop α`. The zero algebraic rank at the index sentinel `N` is not a tail
homology fiber. The equality squares respect two-step actual inclusion
composition.

The private examples include all-degree bottom and Empty-value filters, a
nonzero singleton with diagram `{(a,⊤)}`, finite and essential integer
multiplicity consumers of `moduleMultiplicityInteger`, diagonal and reversed
grade counts of zero, and both supplied-iso and genuine empty-index iso
consumers.

For the full complex on `Fin 2`, the filter assigns values `2`, `5`, `9` to
`{0}`, `{1}`, `{0,1}`. Over `ZMod 2`, actual degree-zero homology at the three
nonbottom stages has dimensions `1`, `2`, `1`. Its coordinates are the vertex
coefficient, the pair of vertex coefficients, and the coefficient sum. The
actual edge boundary is `e₁−e₀`. For every zero chain `c`,

```text
c − (c₀+c₁)e₀ = ∂(c₁·{0,1}).
```

This identity normalizes every actual quotient class to a multiple of `e₀`.
It proves that the inverse of the descended coefficient-sum equivalence
sends each scalar `a` to the actual class of `a e₀`. Under these coordinates,
the inclusions are `a ↦ (a,0)`, `(a,b) ↦ a+b`, and `a ↦ a`. Their actual ranks
give index bars `[0,3)`, `[1,2)` and diagram `{(2,⊤),(5,9)}`.

The examples state both actual map rank and diagram slice count for each row:

| Thresholds `(r,s)` | Rank and count |
| --- | ---: |
| `(1,1)`, `(1,3)`, `(1,10)` | 0 |
| `(2,2)`, `(3,4)`, `(3,6)` | 1 |
| `(5,5)`, `(6,8)` | 2 |
| `(6,9)`, `(9,9)`, `(6,10)`, `(10,11)` | 1 |

The target at `6` has dimension `2` while the map from `3` has rank `1`.
The finite point survives at `8` and dies at `9`; birth `5` contributes at
the self threshold. Same-stage and tail identities, and the transported
`3→6→10` composition, concern the actual inclusion maps.

These results apply to finite simplicial sublevels with closed birth and
half-open lifetime conventions. They extend the finite rank construction to
all ordered thresholds; they do not identify it with the full tame real
function or singular homology theory. The source convention and finite
translation are described in [references.md](references.md). The separate
ordering/reparameterization and geometric obligations of [Issue #44](https://github.com/uda-lab/tda-lib/issues/44)
and the acceptance assessment of [Issue #43](https://github.com/uda-lab/tda-lib/issues/43)
remain outside this unit.
