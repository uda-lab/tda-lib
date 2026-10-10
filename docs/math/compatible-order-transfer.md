# Transfer of compatible face enumerations

Let `e : CompatibleOrder f` enumerate the actual faces of the same complex `K`. If the
values of another filter `g` are monotone along `e.enum`, the transfer keeps `e.enum`
unchanged. Both compatible orders use the supplied `Fintype (TotalFace K)`, so their index
type is the same `Fin (Fintype.card (TotalFace K))`. Proper-face ordering depends only on
that enumeration and `K`; the direct construction reuses `e.face_lt` and needs only the
provided monotonicity proof for `g`.

The public API consists of `CompatibleOrder.transfer`, its enumeration law
`CompatibleOrder.transfer_enum`, `OrderingEquivalent.monotone_comp`, and the convenience
pair `CompatibleOrder.transferOfOrderingEquivalent` and
`CompatibleOrder.transferOfOrderingEquivalent_enum`.

For `OrderingEquivalent f g`, each pair of actual faces has the same weak comparison under
both value functions. Given `i ≤ j`, monotonicity of `f.value ∘ e.enum` gives the comparison
between `f` at those two enumerated faces. The forward direction of ordering equivalence
transfers it to `g`, proving `Monotone (g.value ∘ e.enum)`. The convenience constructor applies
the direct transfer to this proof. In each constructor, projecting the enumeration reduces
definitionally to `e.enum`; both preservation theorems are `rfl`.

The direct constructor requires only monotonicity of `g` along this particular enumeration.
Ordering equivalence is sufficient, but not necessary: on the supplied edge enumeration
`[vertex 1, vertex 0, edge]`, a constant filter can transfer to grades `[0, 1, 2]` along
those entries even though the two vertex values split a tie. Reversing those vertex grades
to `[1, 0, 2]` makes the required monotonicity false. Neither construction sorts or chooses
a replacement enumeration, and the API does not claim generic existence of a compatible
order.

The examples also cover the empty complex over `Fin 0` and `Fin 2`, including filters into
`Unit` and `Empty`; a noncanonical enumeration of a tied edge with grades in `ℕ` and `ℤ`;
and a nonconstant tied pattern `[0, 0, 1]` transferred to `[1, 1, 3]`. Finite evaluations
confirm that the supplied order and each transfer produce the explicit face list
`[{1}, {0}, {0, 1}]`. These examples do not assert that arbitrary filters or grade orders
are executable.

## Source and API notes

- [`CompatibleOrder.lean`](../../TDA/Filtration/CompatibleOrder.lean) defines the actual-face
  enumeration, proper-face ordering, and grade monotonicity fields. The transfer preserves
  the given structure's first two fields verbatim.
- [`OrderingEquivalent.lean`](../../TDA/Filtration/OrderingEquivalent.lean) defines ordering
  equivalence as the pairwise iff of weak comparisons on actual faces. The proof uses that
  implication directly; it does not use the attained-range characterization or choose an
  order isomorphism.
- [`FilterFunction.lean`](../../TDA/Filtration/FilterFunction.lean) assigns values to
  `TotalFace K`. The contract and its exact source anchors are recorded in
  [Issue #110](https://github.com/uda-lab/tda-lib/issues/110).
- The examples live in
  [`CompatibleOrderTransferExamples.lean`](../../TDA/Filtration/CompatibleOrderTransferExamples.lean).
  This unit adds no dependency, vertex order, grade default, or additional instance.
