# Computing homology preimages with chain certificates

A vertex map can explain a target cycle without mapping any source chain to that
cycle exactly. The required equality is between homology classes: the difference
between the target cycle and the image of a source cycle must be a boundary.
`runHomologyLift` computes a source cycle and a chain filling that difference.

## Inputs and output

Use the finite F₂ simplex lists and integer sublevels described in
[finite induced maps](finite-ph-maps.md). Supply a source list `xs`, target list
`ys`, degree `p`, source threshold `a`, target threshold `b`, a vertex function
`f : ℕ → ℕ`, and a target vector `w : Fin ys.length → ZMod 2`. Vector entries
refer to the original target face positions.

The procedure checks both simplex lists, every admitted source face image, and
the target cycle's degree, sublevel support and signed boundary. These checks
apply even when either selected homology group is zero. Invalid inputs return
`none`.

Successful output contains three fields:

- `coefficients`: a fixed-length F₂ vector in the unchanged source basis-query order;
- `sourceCycle`: a duplicate-free list of original source face indices;
- `bounding`: a duplicate-free list of original target face indices.

The source cycle lies in degree `p` at threshold `a`. The bounding chain lies in
degree `p + 1` at threshold `b`. If `v` and `B` are their decoded vectors, then

```text
boundary(ys) · B = w − vertexVector(xs, ys, a, f, v).
```

This equality uses the actual signed simplicial boundary specialized to F₂.
`runHomologyLift_correct` also constructs the actual source cycle and target
chain with those coefficients and proves the same boundary identity in the
simplicial chain groups. The induced actual homology map sends the returned
source class to the supplied target class.

## Completeness and selection

For valid geometry and an admitted target cycle,
`runHomologyLift_exists_iff_range` states that a successful result exists exactly
when the target class belongs to the range of the actual induced homology map.
`runHomologyLift_eq_none_iff_not_mem_range` gives the corresponding rejection
criterion. Neither execution nor these criteria require a supplied preimage.

The computation enumerates all binary source-coordinate vectors and tests the
existing induced-map matrix. `cycleSynthesis` turns a solution into a cycle using
the computed basis representatives. Its coordinates round-trip exactly. The
existing selected filling procedure supplies the target chain.

A null-homologous target selects zero source coefficients and an empty source
cycle, including when source homology has a nontrivial kernel or the source list
is empty. Its target filling may be nonempty. A zero target vector returns empty
source and bounding supports. Other targets use a deterministic first solution;
no shortest, canonical or order-independent preimage is asserted.

Enumeration is exponential in source Betti dimension. This API is intended for
small computed groups; it does not supply efficient Gaussian elimination or a
running-time guarantee. The executable path uses finite lists, vectors, matrix
operations and the existing reduction trace. Noncomputable coordinate inverses
appear only in the correctness proofs.

## A class that enters the image

Take the theta graph on vertices `0,1,2,3`, with edges `01,13,02,23,03` at grade 1,
and add the triangle `013` at grade 2. Map a source circle onto the target loop
`02 + 23 + 03`. At grade 1 the outer cycle `01 + 13 + 02 + 23` is outside the
induced map's image. At grade 2 it lifts through the source circle: subtracting
the image loop leaves `01 + 13 + 03`, the boundary of `013`.

The following query returns source support `[3, 4, 5]` and target bounding
support `[9]`:

```lean
import TDA.Persistence.Reduction.FiniteInputHomologyLiftExamples

open TDA.Persistence.Reduction.FiniteInput
open TDA.Persistence.Reduction.FiniteInput.LiftExamples

#eval (runHomologyLift MapExamples.circle theta 1 1 2 intoTheta
  (fun i => if 5 ≤ i.val ∧ i.val ≤ 8 then 1 else 0)).map
  (fun out => (out.sourceCycle.map Fin.val, out.bounding.map Fin.val))
-- some ([3, 4, 5], [9])
```

The returned target filling is therefore nonempty, although the input target
cycle has edges absent from the source image. The public `LiftExamples` consumers
check this change and its actual range and chain semantics.

The contract is derived from the library's existing Lean definitions and proved
coordinate, map and filling APIs. No primary-paper comparison is claimed. The
scope remains finite F₂ complexes with integer grades; arbitrary fields, natural
choices of preimages and general persistence decomposition are separate matters.
