# Log-scale diagrams in degrees n ≥ 1

This note gives the [log-scale modules](cech-rips-interleaving.md) of real filters on a finite
complex a persistence diagram in every degree n ≥ 1. The module is shown to be
finite-constructible on the logarithms of the positive critical values, so the
[finite-constructible isometry](constructible-isometry.md) applies to it, as it does to the
radius-level [sublevel modules](sublevel-constructibility.md). The log-scale Čech–Rips
interleaving then becomes a bottleneck bound log 2 between log-scale diagrams.

## Conventions

The log-scale module of a real filter f at t is the homology Hₙ(f_{exp t}; R) of the sublevel
complex at exp t, with homology inclusions as structure maps. Vertex values are not assumed
to be 0. The filter f is *positive off vertices* when every face with at least two vertices
has positive value; by monotonicity this is the same as positivity on edges. Positivity passes
from g to every filter f with g ≤ f.

The positive-log grid of f is the increasing enumeration of the finite set
{log c | c a critical value of f with c > 0}. Nonpositive critical values, in particular the
vertex value 0 of Rips and Čech filters, are excluded, since their logarithm is undefined.
The log-scale diagram `logDgm k f n` is the module diagram of the log-scale module on this
grid, over a field k. It is defined for every filter and degree. It represents the module
only when the module is constructible on the grid, which is proved below for n ≥ 1 under
positivity off vertices.

## Vanishing of higher homology

The n-chains of a complex are finitely supported functions on its faces with n + 1 vertices.
If there is no such face, the chain module is zero, and so is the homology in degree n, over
every ring. A face with n + 1 vertices has at least two vertices when n ≥ 1, so a complex whose
faces have at most one vertex has zero homology in every degree n ≥ 1.

## Constructibility on the positive-log grid

Let s ≤ t lie in the same cell of the positive-log grid. Then f_{exp s} ⊆ f_{exp t}.
Conversely, let σ be a face of f_{exp t} with value v. If v ≤ 0, then v < exp s. If v > 0,
then log v is a grid value at most t, so it is counted in the cell of t, which equals the cell
of s; hence log v ≤ s and v ≤ exp s. The two sublevels are equal. This step needs no
positivity.

Let t lie below every grid value and assume positivity off vertices. A face of f_{exp t} with
at least two vertices has positive value v, so log v is a grid value and exp t < v, which is
impossible. The sublevel at exp t therefore contains only vertices, and its homology vanishes
in every degree n ≥ 1. This is the zero left tail. Together with the equality of sublevels
within a cell, the log-scale module is finite-constructible on the positive-log grid in every
degree n ≥ 1, over every ring.

Over a field, every fiber is finite-dimensional, since the sublevel has finitely many faces.

## Bottleneck bounds

For two filters f and g on the same finite complex, positive off vertices, the isometry gives,
in every degree n ≥ 1,

  d_B(logDgm k f n, logDgm k g n) = d_I(log-scale module of f, log-scale module of g).

The two positive-log grids are unrelated. If g ≤ f ≤ c · g with 1 ≤ c and g is positive off
vertices, then f is positive off vertices too, and the log c-interleaving of the log-scale
modules bounds the bottleneck distance by log c. For labelled points p in a pseudometric space
and a label metric d with d(v, w) = dist(p v, p w), the Rips filter of d is positive off
vertices, because distinct labels have positive distance and the diameter dominates every
pairwise distance. The Čech filter is positive off vertices because rips ≤ 2 · čech. With
čech ≤ rips ≤ 2 · čech, the log-scale Rips and Čech diagrams are within log 2 in every degree
n ≥ 1, without properness of the ambient space.

## The degree-0 obstruction

In degree 0 the argument fails at the zero left tail. Let some vertex have value at most 0.
For any finite grid, choose t below every grid value. The vertex lies in f_{exp t} because
exp t > 0, and it gives a nonzero class in H₀(f_{exp t}; k). Hence the fiber at t is not zero,
and the log-scale module in degree 0 is not constructible on any finite grid. For Rips and
Čech filters every vertex has value 0, so every vertex class is born at −∞ on the log scale.

## Fixtures

- **Positivity.** The two-point and triangle Rips and Čech filters are positive off vertices.
- **Comparison.** Over ZMod 2, in every degree n ≥ 1, the triangle log-scale Rips and Čech
  modules are constructible on their positive-log grids, and their diagrams are within log 2;
  the same bound holds on two points over ZMod 2 and ℚ.
- **Triangle at log (6/5).** No face with two vertices lies in the triangle Rips sublevel at
  6/5, so the degree-1 log-scale Rips module vanishes at log (6/5). At the same time the three
  Čech edges are present and the Čech 2-face is absent.
- **Above the dimension.** On two vertices no face has three vertices, so in every degree
  n ≥ 2 the log-scale modules vanish, both diagrams are empty and their bottleneck distance is
  0.
- **Dimension filters.** The filled and hollow triangles, with value card − 1 cast to ℝ, are
  positive off vertices and their degree-1 log-scale modules are constructible. Scaling the
  filled triangle by 2 moves its degree-1 log-scale diagram by at most log 2.
- **Degree 0.** The two-point Rips and Čech log-scale modules in degree 0 are constructible on
  no finite grid, in particular not on their positive-log grids.
- **Repeated labels.** Two distinct labels at one point give a Čech edge of value 0, so the
  Čech filter is not positive off vertices. No label metric is compatible with this
  configuration.

The triangle (0,0), (2,0), (1,2) has Rips values 0 on vertices, 2 on {0,1}, √5 on the two
other edges and √5 on the 2-face. Its Rips 1-skeleton closes at √5 together with the 2-face,
so its Rips degree-1 diagram is empty. Its Čech values are 1 on {0,1}, √5/2 on the other
edges and 5/4, the circumradius, on the 2-face. The hollow triangle lives on [√5/2, 5/4), so
the Čech degree-1 diagram is {(√5/2, 5/4)} and its log-scale diagram is
{(½ log (5/4), log (5/4))}. The log-scale bottleneck distance between the two is ¼ log (5/4),
well below log 2. These values are recorded for orientation and are not proved; the fixtures
establish only the bounds and memberships above.

## Scope

Degree 0 at log scale is not treated beyond the obstruction; it needs extended-real indexing
or a lower truncation. No relation between `logDgm k f n` and the radius-level diagram
`dgm k f n` mapped by log is stated: log is not an order embedding of ℝ, so such a relation
needs a partial map of diagrams with positive coordinates. Explicit Čech and Rips diagrams,
Jung's constant, Hausdorff and Gromov–Hausdorff statements and positive scaling of real
modules are outside this note. The log-scale module, constructibility, the module diagram and
the isometry are used unchanged.

## Sources

The isometry used is the merged finite-constructible form of the theorem of
[Bauer–Lesnick](references.md#BL15-v4). The Rips and ambient Čech definitions match
[Chazal–de Silva–Oudot §§4.2.1, 4.2.3](references.md#CDSO13-v3), which states no Rips/Čech
inclusion. The log-scale comparison of Čech and Rips diagrams, positivity of these filters off
vertices and the vanishing of higher homology of a complex of vertices are classical folklore
with no registered source. Every result here is a library extension proved from merged
definitions; no theorem of either paper is exported.
