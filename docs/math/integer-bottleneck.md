# Exact bottleneck computation for integer presentations

`TDA.Persistence.IntegerBottleneck.run` computes the bottleneck distance between
two finite ordered integer presentations and returns an optimal occurrence
matching whenever the distance is finite. The result stores twice the distance
in `WithTop ℕ`, so half-integral values are exact.

## Inputs and occurrence labels

A `Presentation` contains `finite : List (ℤ × ℤ)` and `essential : List ℤ`.
Finite pairs with equal endpoints are discarded. Reversed pairs and negative
coordinates are retained. Repeated pairs and births are distinct occurrences.
Essential bars have infinite death; they are never matched to finite bars or
left unmatched.

`run D E` returns a `Result D E` with fields `twiceDistance` and `matching`.
Essential-count mismatch gives `⊤` and `none`. Equal counts always give a
finite value and `some` candidate, including empty inputs.

The candidate's `finiteMap` is a partial injection between `FiniteIndex D`
and `FiniteIndex E`. Each index contains a zero-based position in the original
finite list and a proof that its endpoints differ. The `essentialMap` is a
bijection between the original essential positions. `finitePairs` and
`essentialPairs` export these correspondences as lists of natural-number pairs.
Filtering does not renumber the positions.

For example:

```lean
import TDA.Persistence.IntegerBottleneckCorrectness

open TDA.Persistence.IntegerBottleneck

def left : Presentation := ⟨[(7, 7), (0, 4), (5, 5)], []⟩
def right : Presentation := ⟨[(1, 1), (2, 2), (0, 4)], []⟩

#eval (run left right).matching.map Candidate.finitePairs
-- some [(1, 2)]

example : (run left right).twiceDistance = 0 := by decide
```

## Costs and search

All executed arithmetic uses integer differences and their natural magnitudes.
The candidate cost is the maximum of the following doubled contributions,
with empty maximum zero:

| Contribution | Doubled cost |
| --- | --- |
| Finite pair `(b,d)` matched to `(b',d')` | `2 * max (abs (b-b')) (abs (d-d'))` |
| Unmatched finite pair `(b,d)` on either side | `abs (d-b)` |
| Essential birth `b` matched to `b'` | `2 * abs (b-b')` |

The search explicitly enumerates finite partial assignments and essential
functions with Mathlib's `List.pi`, filters for partial injectivity and essential
bijectivity, and selects the first minimum with `List.argmin`. When there are
`m,n` retained finite occurrences and `e` essential occurrences on each side,
it inspects `(n+1)^m * e^e` raw assignments (`0^0 = 1`). It enumerates essential
functions before filtering, rather than directly enumerating the `e!`
bijections. This exhaustive algorithm is intended for small diagrams.

The chosen matching can depend on input order and ties. Only the value is
invariant under permutations and diagonal insertion or removal. No efficient
matching algorithm or complexity improvement is claimed.

## Mathematical interpretation

`diagram D` casts the original integer coordinates to reals and applies the
existing `orderedQ`. The proof-side `Candidate.toMatching` interprets a valid
candidate as the existing `OccurrenceMatching`; the executed search uses no
real comparisons or noncomputable matching enumeration.

`matching_represented` proves that every mathematical occurrence matching is
represented by the explicit search. `twiceCost_eq` identifies each executed
cost with twice its existing matching cost. The unconditional theorem
`twiceDistance_correct`, also exposed on the result by `run_correct`, states

```text
embed (run D E).twiceDistance = 2 * bottleneck (diagram D) (diagram E),
```

where `embed` casts natural numbers to `ℝ≥0∞` and sends infinity to infinity.
`solve_cost_eq` and `solve_optimal` show that the returned matching attains this
bottleneck and no admissible matching costs less. `Candidate.cost_eq_half`
recovers a candidate's real cost by dividing its doubled cost by two.
`twiceDistance_eq_top_iff` characterizes infinity by essential-count mismatch;
`twiceDistance_perm` and the diagonal-insertion lemmas express value invariance.

`IntegerBottleneckExamples` kernel-checks odd doubled values, multiplicities,
both finite deletion costs, nonidentity essential matching, mixed diagrams,
infinity, empty and diagonal inputs, signed endpoints, permutations and original
position labels, and connects the computed values and returned witness to the
existing bottleneck. The input API is independent of coefficient fields and
simplicial data; no wrapper around `FiniteInput.run` is included.
