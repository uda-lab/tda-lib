# Closed loci for a fixed compatible face enumeration

Fix a filter `f₀` on a preabstract simplicial complex `K` and a compatible
enumeration `e` of its actual faces. Let `F : X → FilterFunction K α` be a family
over a topological space `X`. The grades `α` carry a linear order, a topology,
and `OrderClosedTopology α`. Assume each actual face coordinate
`x ↦ (F x).value s` is continuous. Then
`CompatibleOrder.isClosed_compatible_locus` proves that the parameters at which
*this exact enumeration* is compatible form a closed subset of `X`:

```lean
{x : X | ∃ d : CompatibleOrder (F x), d.enum = e.enum}
```

At a parameter `x`, this condition is equivalent to monotonicity of
`(F x).value ∘ e.enum`. A witness `d` with the same enumeration supplies
monotonicity. Conversely, monotonicity lets `e.transfer` keep the enumeration
and its proper-face order while replacing its grades. Each monotonicity
comparison is a weak inequality between two continuous coordinate functions;
`isClosed_le` makes its parameter set closed. Intersecting these sets over all
index pairs gives the locus. The argument also covers an empty parameter
space or an empty actual-face enumeration. It uses no topology on vertices,
faces, or `FilterFunction`, and does not sort or choose an enumeration.

The `OrderClosedTopology α` hypothesis is essential to this proof: a linear
order alone does not make the weak-order relation topologically closed. Ties
are permitted because every comparison uses `≤`. Continuity is required for
each actual face coordinate; no global continuity of `F` is asserted.

The private fixtures in
[`CompatibleOrderClosedExamples.lean`](../../TDA/Filtration/CompatibleOrderClosedExamples.lean)
cover an empty complex over real grades, an empty parameter space, a single
vertex with varying grade, and an edge whose three grades are tied at each
parameter. The tied edge has common grade `x`, so its grades vary with the
parameter while remaining equal across faces.

The decisive example grades two vertices by `0` and `x`, and their edge by
`max 0 x`. This is a valid filter for every real `x`; all three face grades
are continuous. For the fixed enumeration `[vertex 0, vertex 1, edge]`, the
compatibility locus is exactly `{x : ℝ | 0 ≤ x}`. It contains the tied boundary
`0` and excludes `-1`, although a different compatible enumeration exists at
`-1`. Thus the theorem concerns the fixed enumeration rather than existence
of some compatible order, which holds for every finite actual-face filter.

The theorem reuses [`CompatibleOrder.transfer`](../../TDA/Filtration/CompatibleOrderTransfer.lean)
and Mathlib's `isClosed_le` and `isClosed_iInter`. Its public type has no
`OrderTopology`, metric, separation, `Nonempty`, or `Inhabited` requirement.
Open dense order chambers, frontiers, local constancy, and a topology on the
space of all filter functions are separate questions.
