# Inclusion interleavings and the log-scale Čech–Rips interleaving

This note continues the [closed ambient Čech complex](cech-rips-sandwich.md) and the
[real interleavings](real-interleavings.md). It lifts inclusions of simplicial
filtrations to morphisms of homology persistence modules, and inclusions shifted by ε to
actual real ε-interleavings. The Rips/Čech value sandwich then becomes an interleaving
of log-scale modules with parameter log 2.

## Conventions

A simplicial filtration F is a monotone map from an index preorder to preabstract
simplicial complexes on a linearly ordered vertex type. Its homology module has the
homology Hₙ(F p; R) at p, over an arbitrary ring R, and the homology inclusion along
F p ⊆ F q as structure map. Reindexing a filtration along a monotone u is precomposition.
The homology module of the reindexed filtration is, by definition, the reindexed module.

Real shifts follow the interleaving API: the ε-shift of N evaluates N at t + ε, and an
ε-interleaving consists of φ : M → N(· + ε) and ψ : N → M(· + ε) whose two double-shift
composites, followed by the index transport (t + ε) + ε = t + (ε + ε), are the structure
maps from t to t + (ε + ε). Parameters are finite nonnegative reals.

For a filter f on the faces of a complex K, the sublevel module at r is the homology of
the sublevel complex of faces with value at most r. For a real filter, the log-scale
module at t is the homology of the sublevel at exp t, that is, the sublevel module
reindexed along exp. For 1 ≤ c, the log parameter of c is log c as a nonnegative real,
and exp (t + log c) = c · exp t. The Čech side is always the sublevel of the Čech radius
filter on the full complex, so no properness of the ambient space is used.

## Inclusion morphisms and interleavings

If F p ⊆ G p for every p, the homology inclusions Hₙ(F p) → Hₙ(G p) form a natural
transformation. Both naturality composites are homology inclusions along F p ⊆ G q, and
homology inclusions are functorial: the inclusion along K ⊆ L ⊆ M is the composite of
the two inclusions. As inclusions between complexes are propositions, the inclusion map
depends only on its source and target. The reflexive inclusion gives the identity, the
composite inclusion gives the composite morphism, and reindexing an inclusion morphism
gives the inclusion morphism of the reindexed filtrations.

Let F and G be real filtrations with F t ⊆ G (t + ε) and G t ⊆ F (t + ε) for every t.
The two families of inclusions are morphisms into the shifted modules. In each
double-shift equation the left side is the composite of three homology inclusions,
F t ⊆ G (t + ε) ⊆ F ((t + ε) + ε) ⊆ F (t + (ε + ε)), the last one being the index
transport. The right side is the homology inclusion F t ⊆ F (t + (ε + ε)). Functoriality
equates them, so both equations are proved, not assumed.

For filters f and g on the same complex, g ≤ f + ε on every face gives
f_r ⊆ g_{r+ε}. Hence |f − g| ≤ ε on every face gives an ε-interleaving of the
sublevel modules, and their interleaving distance is at most ε. On a complex with
finitely many faces, taking ε to be the largest face difference bounds the distance by
that difference.

## The multiplicative sandwich

Let g ≤ f ≤ c · g on every face with 1 ≤ c. A face of f_{exp t} lies in g_{exp t},
which lies in g_{exp (t + log c)} since the shift is nonnegative. A face of g_{exp t}
has f ≤ c · g ≤ c · exp t = exp (t + log c). The inclusion interleaving of the two
exp-reindexed filtrations is therefore a log c-interleaving of the log-scale modules,
and their interleaving distance is at most log c.

The merged value bounds čech ≤ rips ≤ 2 · čech hold for labelled points in any
pseudometric space and any label metric agreeing with the ambient distances. With
f the Rips filter, g the Čech filter and c = 2, the log-scale Rips and Čech modules are
log 2-interleaved, in every degree and over every ring, and their interleaving distance
is at most log 2.

At radius level, Rips_r ⊆ Čech_r and Čech_r ⊆ Rips_{2r} hold for every real r, the second
because rips ≤ 2 · čech ≤ 2r. They give morphisms from the Rips sublevel module to the
Čech one, and from the Čech one to the Rips module reindexed by r ↦ 2r. Their composites
are the inclusion morphisms Rips_r ⊆ Rips_{2r} and Čech_r ⊆ Čech_{2r}, which exist for
every real r because all values are nonnegative. For 0 ≤ r these components are the
structure maps from r to 2r. For r < 0 no structure map from r to 2r exists, since
2r < r; both sublevels are then empty and the component is the inclusion of empty
complexes.

## Fixtures

- **Two points.** The points 0 and 2 on the line give the log 2-interleaving and the
  distance bound over ZMod 2 and ℚ in every degree.
- **Forced constant.** For ε < log 2, the hypothesis G t ⊆ F (t + ε) fails at t = 0: the
  edge has Čech value 1 = exp 0 and Rips value 2 > exp ε. At ε = log 2 the edge enters,
  since exp (log 2) = 2.
- **No zero left tail.** Every vertex lies in the Rips and Čech sublevels at exp t for
  every real t, whereas the radius-level Rips sublevel at −1 is empty.
- **Triangle.** The acute triangle (0,0), (2,0), (1,2) in the Euclidean plane gives the
  log 2-interleaving in every degree, in particular in degrees 0 and 1.
- **Radius level.** On two points, the composite at r = 1 is the structure map from 1 to
  2, and at r = −1 it is the inclusion component between empty complexes.
- **One vertex.** Vertex filters at a and b are |a − b|-interleaved; at a = b the zero
  witness has identity maps after the canonical zero-shift identification.
- **Face difference.** The two-point Rips filter and its scaling by 2 are within their
  largest face difference, which is 2 at the edge.

## Scope

The distance bounds are statements about real interleaving distances of homology
modules, not about persistence diagrams. At radius level, the
[constructibility bridge](sublevel-constructibility.md) shows that the sublevel module of a
finite filter is finite-constructible with the actual diagram as its module diagram, so the
[finite-constructible isometry](constructible-isometry.md) turns the radius-level
face-difference bound into a bottleneck bound. In degrees n ≥ 1 the
[log-scale diagrams](log-scale-diagrams.md) turn the log 2 bound into a bottleneck bound
between log-scale Rips and Čech diagrams. Degree 0 remains outside: at log scale every vertex
is alive at every time, as the no-zero-left-tail fixture shows, so in degree 0 the log-scale
module lies outside the zero-left domain of that isometry.
Hausdorff and Gromov–Hausdorff statements, the Nerve Lemma, open-ball variants and
Euclidean sharpening of the factor 2 are not treated.

## Sources

The shift, transition, interleaving and distance conventions are those of
[Bauer–Lesnick §3.1](references.md#BL15-v4), as fixed by the library API; this unit only
constructs witnesses. The Rips and ambient Čech definitions match
[Chazal–de Silva–Oudot §§4.2.1, 4.2.3](references.md#CDSO13-v3), which states no
Rips/Čech inclusion. That inclusions of filtrations induce interleavings, and that a
multiplicative sandwich gives an additive interleaving at log scale, are classical
folklore with no registered source. Every result here is a library extension proved from
merged definitions; no theorem of either paper is exported.
