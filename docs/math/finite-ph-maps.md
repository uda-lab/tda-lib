# Computing maps on finite F₂ homology

`FiniteInput.runHomologyMap` computes the homology map induced by a vertex
function between two validated finite simplex lists. The lists may use different
vertex labels and face orders, and the function may merge vertices. The output
is a matrix in the existing [computed sublevel bases](finite-ph-representatives.md#complete-bases-and-inclusion-coordinates).
Coefficients are F₂ and grades are integers. This map API was added in v0.4.0.

## Inputs and matrix convention

Call `runHomologyMap xs ys p a b f`, where `xs` and `ys` satisfy the
[finite-input contract](finite-ph-computation.md), `p` is the homology degree,
`a` and `b` select the source and target sublevels, and `f : ℕ → ℕ` maps vertices.
Every source face with grade at most `a` must have its image listed in `ys` at
grade at most `b`. This condition is checked in every face degree. For example,
an H₀ query rejects a map whose admitted edge image is absent, even when both
vertex images exist. Source faces appearing after `a` impose no condition.

Success returns `some rows`. Rows follow `runDegreeAtGrade ys p b`; columns
follow `runDegreeAtGrade xs p a`, in their existing orders. Thus

```text
target coordinates of the image = matrix × source coordinates.
```

Different records with equal interval values retain different positions. The
entries come from mapping their cycle chains; interval values do not determine
the map. Invalid lists, missing image faces and images above the target threshold
return `none`, including when the requested homology groups are zero.

## Merging components and collapsing edges

The input `MapExamples.components` consists of two isolated vertices. Mapping
both to the single vertex of `MapExamples.point` gives one target H₀ coordinate
from two source coordinates:

```lean
import TDA.Persistence.Reduction.FiniteInputHomologyMapExamples

open TDA.Persistence.Reduction.FiniteInput

#eval runHomologyMap MapExamples.components MapExamples.point 0 0 (-1)
  (fun _ => 42) -- some [[1, 1]]
#eval runHomologyMap MapExamples.components MapExamples.components 0 0 0
  MapExamples.swap -- some [[0, 1], [1, 0]]
```

Both source component classes map to the same nonzero target class. Swapping
the two source vertices instead produces a permutation matrix. The theorem
`MapExamples.component_actual_map_not_injective` proves that the merging map on
actual simplicial homology is noninjective.

For H₁, `MapExamples.square` is a four-edge circle. `collapseEdge` sends its
consecutive vertices to `10, 11, 12, 10`, in the differently labelled
three-edge circle `MapExamples.circle`. The fourth edge collapses to a vertex,
while the other three edges form the target cycle:

```lean
#eval runHomologyMap MapExamples.square MapExamples.circle 1 1 1
  MapExamples.collapseEdge -- some [[1]]
#eval runHomologyMap MapExamples.square MapExamples.point 1 1 (-1)
  (fun _ => 42) -- some []
```

The first map has a genuinely nonzero actual H₁ image
(`MapExamples.square_actual_map_nonzero`). The constant map has zero target H₁.
A collapsed face contributes zero in its original chain degree: an edge whose
vertices merge does not become a degree-one copy of the image vertex. Distinct
source faces can also have the same image. Their coefficients are added over F₂,
so two coincident edge images cancel. `MapExamples.folded_path_chain_image`
checks this on a two-edge path, including a chain that is not itself a cycle.

## Empty dimensions and threshold checks

The source and target queries specify the matrix dimensions, including empty
ones. A nested list with no rows uses the source-query dimension as its width.
The companion `homologyMapMatrix` has both dimensions in its type.

| Source dimension | Target dimension | Returned rows |
|---:|---:|---|
| 1 | 0 | `[]` |
| 0 | 2 | `[[], []]` |
| 0 | 0 | `[]` |

An empty source sublevel has a vacuous image condition, even if `xs` contains
faces at later grades. A nonempty source sublevel cannot map into an empty target
sublevel. All faces tied at a threshold enter together; negative thresholds
use the same rules. An invalid complete input list is rejected at every threshold.

## Correctness and composition

`VertexMapCondition` is the finite face-image condition, and `VertexMapInput`
also checks both lists. `vertexMapCondition_iff` identifies the condition with
actual sublevel face preservation; `validatedVertexMap` constructs the existing
semantic simplicial map. `runHomologyMap_eq_some_iff` and
`runHomologyMap_eq_none_iff` characterize acceptance and rejection.
`runHomologyMap_row_count`, `runHomologyMap_column_count` and
`runHomologyMap_get` identify the shape and every indexed coefficient.

`homologyMapMatrix_correct` proves the coordinate equation above for **every**
actual source homology class, using the pre-existing `simplicialHomologyMap`.
`runHomologyMap_correct` obtains its hypotheses from successful execution.
`homologyMapMatrix_cycle` gives the corresponding equation for any admitted
supplied cycle and its exact computed image vector. No induced-map matrix,
decomposition or chain-map certificate is supplied to the executed procedure.

Identity maps give identity matrices. For validated maps from `xs` at `a` to
`ys` at `b`, then to `zs` at `c`, `homologyMapMatrix_comp` proves
`M(g ∘ f) = M(g) * M(f)`. For the identity vertex function on one input and
`a ≤ b`, `homologyMapMatrix_inclusion` recovers the existing `basisTransition`.
These statements include rectangular and empty matrices.

The chain computation uses a finite original-face matrix: unselected source
columns are zero; an admitted face maps to its image face with coefficient one
when cardinality is preserved, and to zero otherwise.
`sublevelChainVector_vertexChainMap` proves agreement with the actual signed
chain map over F₂, including collapsed faces and the sorting sign. Each source
basis cycle is then mapped and its target coordinates computed by the existing
finite normal-coordinate algorithm. The complete basis extends the resulting
column equations to every class.

The executed path uses finite images, searches and F₂ arithmetic. Actual chain
and homology objects are proof-side constructions. This is a library-derived
extension of existing Lean definitions and proved adapters; primary-paper
comparison is unperformed. No shortestness, order-independence or performance
bound is claimed.
