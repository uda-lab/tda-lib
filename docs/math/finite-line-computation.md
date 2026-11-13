# Executing chronological finite persistence

A finite line has vertices indexed by `Fin N` and one arrow from each index to
its successor. For `i ≤ j`, `FiniteLine.path` constructs the chronological path
from `i` to `j` by structural recursion on the target index. Its self path is
empty; each recursive step appends the final adjacent arrow.
`FiniteLine.path_length` gives its length as `j.val - i.val`. Path uniqueness
identifies this construction with every path having the same endpoints.

`FiniteLine.fromFin` expands inequalities into these paths. The path-category
and representation equivalences use that same expansion. Given modules and
explicit adjacent linear maps over a ring, `FiniteLine.moduleOfAdjacent` lifts
the paths to chronological composites. These data constructors and the
adjacent-square morphism and isomorphism constructors are executable when their
supplied data are executable. They require no coefficient-equality decision,
finite-dimensionality, basis selection or nonemptiness assumption.

At `N = 0` there are no vertices or endpoints: the empty functors and
equivalences are available, with no path query to evaluate. At `N = 1` the only
path is the self path and its structure map is the identity.

## Matrices and order of composition

For `A : MatrixSequence R N` over a commutative ring, `A.dim i` is the dimension
at stage `i`. An adjacent matrix has target rows and source columns:

```lean
A.step i j h : Matrix (Fin (A.dim j)) (Fin (A.dim i)) R
```

`A.toPModule` interprets each adjacent matrix as a linear map and composes along
the chronological path. The existing `A.compositeMatrix h` evaluates that map
on the coordinate vectors. It is executable with concrete coefficient
operations; no separate product certificate is needed. Its self matrix is the
identity, its adjacent matrix is the supplied transition, and the later matrix
multiplies on the left:

```lean
A.compositeMatrix (hij.trans hjl) =
  A.compositeMatrix hjl * A.compositeMatrix hij
```

The public `structureMapLinear_apply` identifies applying the structure map
with multiplying by this composite matrix. A zero-dimensional intermediate
stage is permitted: the long composite from a nonzero-dimensional source to a
nonzero-dimensional target is then zero.

## Concrete consumers

`FiniteLineComputableExamples` observes matrices as lists of rows and applies
the actual public structure maps. Its generic ring and commutative-ring
clients introduce no equality decision on the coefficients.

```lean
import TDA.Persistence.FiniteLineComputableExamples

open TDA.Persistence TDA.Persistence.FiniteLineComputableExamples

#eval pathLength (0 : Fin 5) 4 (by decide)             -- 4
#eval scalarAction integerFactors (i := 0) (j := 3) (by decide) 5 -- 120
#eval compositeEntries MatrixSequenceExamples.compositeZero
  (i := 0) (j := 2) (by decide)                       -- [[0]]
#eval compositeEntries MatrixSequenceExamples.compositeIdentity
  (i := 0) (j := 2) (by decide)                       -- [[1]]
#eval compositeEntries binaryShears (i := 0) (j := 2) (by decide)
  -- [[1, 1], [1, 0]] over F₂
```

The two rational rectangular sequences have dimensions `1,2,1` and adjacent
ranks one. Their long composites differ, so dimensions and adjacent ranks alone
do not determine the full persistence module. The F₂ shears do not commute:
reversing their product gives `[[0,1],[1,1]]`. Further consumers apply nonidentity
rational transitions, rectangular F₂ maps whose composite cancels, an explicit
zero-dimensional intermediate stage, empty input and a singleton stage.

## Computational and proof boundaries

Execution of the data and constructive justification of every proof are
separate questions. Path construction returns data directly by finite
recursion. The existing path-uniqueness proof retains classical reasoning in
the functor and equivalence law proofs. Matrix conversion uses explicit
coordinate vectors and finite sums, while its correctness record retains
classical finite-basis reasoning. Transitive proof-axiom audits and actual
execution therefore describe different properties.

Supplied-basis conversions, finite real-grid adapters and interval decomposition
retain their existing theory contracts; this interface computes chronological
maps, not ranks or a barcode extraction algorithm. No runtime basis selection,
real-number comparison procedure or performance guarantee is provided. See
[finite representations](finite-representations.md) for those theory interfaces.
The source basis is the existing Lean finite-line and matrix implementation;
primary-paper full-text comparison remains unperformed.
