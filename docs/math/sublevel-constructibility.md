# Constructibility of sublevel modules and the filter-diagram isometry

This note connects the two descriptions of the persistence of a real filter on a finite
complex. The [finite sublevel diagram](finite-sublevel-diagram.md) `dgm k f n` is the
value-labelled rank diagram of the critical-grade homology module. The
[sublevel module](cech-rips-interleaving.md) is the real-indexed homology module of the
sublevel filtration. The sublevel module is shown to be finite-constructible on the critical
values of f, with `dgm k f n` as its module diagram, so the
[finite-constructible isometry](constructible-isometry.md) applies to it.

## Conventions

A filter f on a complex K with finitely many actual faces attains finitely many values. The
critical grid is their increasing enumeration c₀ < … < c_{N−1}, with tied face values merged
and no sentinel. It is empty exactly for the empty complex. The sublevel module at t is the
homology Hₙ(f_t; R) of the sublevel complex f_t of faces with value at most t, over a ring
R, with homology inclusions as structure maps.

Finite constructibility on a strictly increasing real grid c has exactly two conditions. The
fibers below every grid value are zero. For s ≤ t in the same cell, the structure map from
s to t is an isomorphism. The cell of t counts the grid values at most t, so cells are
left-closed and right-open, and the last cell is unbounded with a possibly nonzero tail. The
predicate allows any ring and contains no finite-dimensionality condition. Finite
dimensionality of the critical fibers is a separate hypothesis of the module diagram and of
the isometry.

The module diagram of a constructible module on c is the rank barcode of the module sampled
at c, with each bar labelled by its grid values. A bar that survives to the end of the grid
is essential and has death ⊤. The filter diagram uses the same labelling of the rank barcode
of the critical-grade module. Both are diagrams over ℝ with essential classes at ⊤ and
multiplicities counted as multiset multiplicities, so no conversion between them is needed.

## Constructibility

The empty complex has zero chains in every degree, so its homology is zero over every ring.
If t lies below every critical value, then t lies below every face value, since every face
value is enumerated by the grid. Hence f_t is empty and its homology is zero, which is the
zero left tail.

Let s ≤ t lie in the same cell. Then f_s ⊆ f_t. Conversely, a face σ of f_t has value
c_i ≤ t for some grid index i. The value c_i is counted in the cell of t, which equals the
cell of s, so c_i ≤ s and σ lies in f_s. The two sublevels are equal, and the homology
inclusion between equal complexes is the identity up to rewriting, hence an isomorphism.
The sublevel module is therefore constructible on the critical grid over every ring.

## The diagram identity

Over a field k, the critical fiber at c_i is the homology of the grade-i sublevel, which is
finite-dimensional because K has finitely many faces. Sampling the sublevel module at the
critical grid gives the critical-grade module by definition. The module diagram on the
critical grid and `dgm k f n` are then the same labelled rank barcode of the same module. The
identity holds by definition, as an equality of diagrams over the same grid on both sides.
The realization isomorphism of the isometry note identifies the sublevel module with the
half-open realization of `dgm k f n`.

## The isometry for filter diagrams

For two filters f and g on the same finite complex, the isometry with grids c = crit f and
d = crit g gives

  bottleneck (dgm k f n) (dgm k g n) = interleaving distance of the sublevel modules.

The grids may have different lengths and are otherwise unrelated. No genericity and no
condition on essential multiplicities is assumed. At every finite parameter ε, an actual
ε-interleaving of the sublevel modules exists exactly when a cost-bounded occurrence matching
of the two diagrams exists.

The inclusion interleaving bounds the interleaving distance by the largest face difference of
f and g. Through the isometry this is a second proof of finite-filter stability. It is
independent of the face-order interpolation proof: its dependency closure does not contain
`bottleneck_dgm_le_faceSupDifference`. Since the bound is finite, the interleaving distance
is finite, and the two diagrams have the same number of essential classes.

## Fixtures

- **Two points and the triangle.** The Čech and Rips filters of the points 0 and 2 on the
  line, and of the acute triangle (0,0), (2,0), (1,2) in the plane, are constructible on
  their critical grids. Their module diagrams in degrees 0 and 1 are their filter diagrams,
  the Čech and Rips diagrams are at the interleaving distance of their modules, and their
  essential multiplicities agree.
- **Filled and hollow triangles.** The certified ℕ-graded triangles are cast to ℝ. The
  filled triangle has degree-0 module diagram {(0,1), (0,1), (0,⊤)} and degree-1 module
  diagram {(1,2)}. The hollow triangle has degree-1 module diagram {(1,⊤)}. The two filters
  live on different complexes and are not compared.
- **One vertex.** The critical grid has one value, the module is constructible, and the
  isometry gives the exact interleaving distance |a − b| of two vertex filters at a and b.
  The algebraic stability bound is attained there, as in the face-order proof.
- **Tied triangle.** The degree-1 module of the tied triangle is zero. It is constructible on
  its critical grid and also on the empty grid, and its module diagram is empty. The critical
  grid is sufficient, not minimal.
- **Empty complex.** The critical grid is empty, the module is constructible, and both sides
  of the diagram identity have no points.
- **Grid above the first value.** For a vertex filter at a, the one-point grid {a + 1} is not
  a constructibility grid: the zero left tail would make H₀ of a vertex zero at a, while it
  is the coefficient field.
- **Grid omitting a value.** For the filled triangle in degree 0, the one-point grid {0} is
  not a constructibility grid: 0 and 1 lie in one cell, but the fibers there have dimensions
  3 and 1.

## Scope

Log-scale modules are treated in degrees n ≥ 1 by the
[log-scale diagrams](log-scale-diagrams.md), on the logarithms of the positive critical
values; in degree 0 the log-scale modules have no zero left tail, and log-mapped diagrams are
not treated. Extended-real indexing, positive scaling of real modules, filters on
two different complexes, filters valued outside ℝ and infinite complexes are outside this
note. The definitions of `dgm`, the module diagram, constructibility and the isometry are
used unchanged.

## Sources

The isometry used is the merged finite-constructible form of the theorem of
[Bauer–Lesnick](references.md#BL15-v4). The stability statement rederived here is the
finite-filter form of [Cohen-Steiner–Edelsbrunner–Harer](references.md#CSEH07); the second
proof is a library proof, not a new source translation. That sublevel homology of a finite
filter is constant between consecutive attained values and zero below the first one is
proved directly in the library. Every result here is a library extension proved from
merged definitions.
