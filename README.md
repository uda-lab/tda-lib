# tda-lib

`tda-lib` is a Lean 4 library for topological data analysis. It formalizes finite
persistent homology, a certified computation of persistence over the two-element
field, distances and stability bounds for persistence diagrams, Rips and Čech
filtrations of finite metric spaces, persistence images and kernels, signed barcodes
of finitely presented multiparameter modules, and selected Reeb and Mapper
constructions. The current release is
[v0.3.0](https://github.com/uda-lab/tda-lib/releases/tag/v0.3.0);
[v0.2.0](https://github.com/uda-lab/tda-lib/releases/tag/v0.2.0) and
[v0.1.0](https://github.com/uda-lab/tda-lib/releases/tag/v0.1.0) are the earlier
releases with mathematical results.

## Results in v0.1.0

- **Persistent homology.** The library builds signed simplicial chains and homology
  from faces, decomposes pointwise finite-dimensional persistence modules
  indexed by a finite chain into intervals, and relates a finite simplex filtration
  to its sublevel persistence diagram. The diagram retains multiplicities,
  finite half-open intervals and essential bars. For real-valued finite filters it
  proves a bottleneck stability bound, including changes in simplex pairing.
  Local regularity, derivative and Hessian results for diagram-based losses use
  explicit hypotheses on ordered representatives and lifts.
- **Certified computation.** An executable reduction computes persistence over
  F₂ from a valid finite list of graded simplices. Its correctness theorem
  identifies the output with the sublevel diagram in every degree;
  invalid lists are rejected.
- **Reeb and Mapper theory.** The library develops interval cosheaves, finite
  graph and constructible-cosheaf comparisons, and ordinary Mapper from pullback
  component covers. Graph and refinement results have explicit finiteness,
  coverage or constructibility assumptions. These are theory interfaces rather
  than an executable Mapper package or a general convergence theorem.

## Results added in v0.2.0

The v0.2.0 release adds the following results to those above; each holds under the
hypotheses stated. The [API guide](docs/api.md) and its mathematical notes give their
exact hypotheses. Two kinds of distance statement appear: distances between
persistence diagrams or modules, and stability of diagrams under perturbation of a
metric-space input.

- **Diagram and module distances.** For finite positive diagrams with unit occurrence
  masses and finite deaths, the powered p-cost is the minimal sum of p-th powers of
  ground distances over partial matchings, with unmatched points matched to the
  diagonal, for a real exponent p ≥ 1 and the maximum ground norm, and the rooted cost
  d_p is its p-th root. These partial-matching minima
  equal the optima over finite real boundary plans; powered and rooted matching and
  real-plan optima agree and are attained. Rooted costs satisfy distance laws and
  explicit cardinality-dependent perturbation bounds for filters on the same finite
  complex. If N is the total finite-occurrence count, d_p ≤ d_1 ≤ N^(1−1/p) d_p.
  Common diagonal translation preserves these costs; nonnegative coordinate scaling by
  c multiplies powered costs by c^p and rooted costs by c. Finite boundary transport
  additionally permits arbitrary nonnegative real masses that split between labels:
  powered and rooted optima are attained for p ≥ 1, and unit masses recover the
  occurrence-based costs. For natural p, total persistence over finite bars is
  translation-invariant and homogeneous under positive scaling. Finite-constructible
  real-indexed modules over a field satisfy the isometry theorem, their interleaving
  distance equals the bottleneck distance of their barcodes, under finite-dimensional
  critical fibers, a zero left tail, half-open strata and a possibly nonzero final
  tail. This also applies to finite-complex sublevel homology modules. Positive
  scaling of real-indexed modules scales their interleaving distance by the same
  positive factor, over every ring and including infinite distance. Sequences of
  adjacent linear maps define finite persistence modules over a ring; rectangular
  matrix sequences require a commutative ring. Over a field, their interval barcodes
  are independent of supplied bases; a construction with zero left tail and constant
  final cell retains supplied real critical values and their finite or essential
  endpoints. These are theory constructions, not executable extraction.
- **Persistence representations.** Gaussian persistence images at fixed positive
  bandwidth and fixed disjoint measurable pixels, and weighted Gaussian kernels, have
  stability bounds on finite diagram parts against first-order matching cost under
  explicit weight assumptions. For the arctan weight with C ≥ 0, the kernel constant
  is 2C + √2·π/(2|σ|), with no bandwidth-sign hypothesis, and the image constant
  is 2C + 3·√(π/2)/σ for σ > 0. The embedding, kernel-value and image bounds apply to Rips
  and Čech diagrams at radius scale when both diagrams carry the same simplex
  labelling; for sup-norm Čech configurations the bound uses half the pairwise
  discrepancy of the two configurations. At log scale they apply to Rips–Čech
  comparisons in degrees n ≥ 1 through the exact bottleneck or log 2 bounds, under the
  compatible-label and positivity hypotheses. At nonzero bandwidth, the Gaussian RKHS
  on the full birth–death plane separates finite signed Borel measures and is
  uniformly dense in C₀(ℝ²). Strictly positive measurable weights with finite weighted
  mass give injective embeddings of positive persistence measures, including
  infinite-mass Radon measures; finite atomic embeddings agree with the finite diagram
  embeddings. These analytic constructions are abstract, and do not make finite-pixel
  images characteristic. Second-level Gaussian feature bounds are available for
  general weights, but have no arctan instance.
- **Metric inputs and sampling stability.** Finite Rips and ambient Čech filtrations
  are constructed. For two metrics on the same labelled finite set, the Rips diagrams
  are within the pairwise discrepancy of the metrics in bottleneck distance. Finite
  Rips and Čech diagrams satisfy face-count bar bounds and corresponding
  total-persistence bounds using the carrier diameter or a stated enclosing radius.
  For finite nonempty metric spaces, full Rips diagrams satisfy d_B ≤ 2 d_GH in every
  degree, without equal-cardinality or common-label assumptions. Finite samples
  embedded in one ambient metric space have a twice-Hausdorff-error bound; two samples
  of a possibly infinite target have a bound of twice their summed errors, comparing
  their finite diagrams only. Hausdorff-convergent samples of a fixed finite target
  have bottleneck-convergent full diagrams. Exact diagrams and bottleneck values over
  `ZMod 2` are proved for two points at radius scale in degree zero and every positive
  degree, and for the acute triangle at radius scale in degrees zero and one and log
  scale in degree one. For two filters positive on edges, common positive scaling
  translates their log-scale diagrams and preserves their mutual log-scale bottleneck
  and interleaving distances in every degree n ≥ 1. For one finite sup-norm
  configuration, Rips and Čech diagrams are within half the carrier diameter in
  bottleneck distance, and log-scale Čech–Rips diagrams are within log 2 in degrees
  n ≥ 1 under the stated positivity and embedding assumptions.
- **Reeb.** In the library's finite real-graph category, geometric smoothing has
  coherent composition, and geometric and cosheaf interleavings agree, with equal
  extended distances. Geometric smoothing admits parameter enlargement, geometric
  interleavings are monotone, constructible smoothing lifts to constructible
  cosheaves, and smoothing a geometric interleaving preserves its parameter with
  two-sided distance bounds. Height-range, top-component and interval-local
  obstructions give lower bounds; exact distances for small examples include 1/2
  between the edge and its midpoint, 1/4 between the parallel-edge and single-edge
  graphs, and ⊤ under a component obstruction. Finite Reeb data have an incidence
  quiver and a simple incidence graph; the latter forgets parallel-edge multiplicity.
  The quotient of every constructible real space satisfies the smoothing absorption
  comparison, while constructibility of its product thickening is established for
  graph input.
- **Mapper.** Graph-PL inputs, piecewise-linear height functions on finite simple
  graphs, have ordinary and MultiNerve Mapper constructions, a cover-dependent cell
  classification and finite Reeb incidence data under explicit cover and height
  assumptions. A uniform cover by open intervals of length r whose consecutive starts
  are r − g apart, so that g is the overlap, with 0 < g and 2g ≤ r, and which is
  member-adapted, height-separating and vertex-height-covering, identifies its
  MultiNerve Mapper data with the graph-PL finite Reeb data; such covers exist with r
  below any prescribed positive bound. Closed levels have the stated vertex and
  crossing-edge components, and inclusion into a level window is bijective on path
  components. Finite Reeb data and member-adapted Mapper data are compatible with
  covering refinements. Under 2g ≤ r, the ordinary Mapper one-skeleton agrees with the
  incidence graph, which forgets parallel edge cells. Under the
  vertex-height-covering hypothesis, the interval-components cosheaf is constructible and agrees
  with the cosheaf of the finite Reeb data. The Reeb quotient of a finite graph-PL
  realization is identified with its finite graph realization. For a finite bounded
  interval cover of the attained height range, categorical Mapper retains components
  of every nonempty intersection; its reconstructed real graph lies within the full
  width of the retained intervals of that Reeb quotient in geometric interleaving
  distance. Vanishing full or retained resolutions give convergence, including
  families with varying finite cover index types. This is abstract categorical
  reconstruction, not an executable Mapper algorithm.

## Results added in v0.3.0

The v0.3.0 release adds the following results to those above; each holds under the
hypotheses stated in the [API guide](docs/api.md) and its mathematical notes, which also
give the declaration names.

- **Borel boundary transport.** The strict birth–death half-plane with one collapsed
  boundary point is a complete separable metric space. For atomic inputs and p ≥ 0, the
  all-Borel powered optimum is the native finite weighted optimum; for unit masses it is
  the powered finite matching minimum. For p ≥ 1 it equals the reservoir optimum for any
  finite capacity dominating the total masses. Also for p ≥ 1, a minimizing plan exists
  for arbitrary finite Borel inputs, and the rooted distance is a literal infimum of
  mathlib `eLpNorm`s over reservoir couplings, satisfies the sharp triangle inequality and
  separates measures. Under finite diagonal p-persistence, same-mass quantizations
  converge. Identification with an ordinary Wasserstein coupling API, including the
  library's own `TDA.Probability.measureWasserstein`, is not claimed.
- **Q-tame modules and decorated diagrams.** Rectangle measures of real modules over a
  field are defined by image-and-kernel quotients with the four-rank formula, finite on
  rectangles separated from the diagonal for q-tame modules; essential strips, box
  inequalities along interleavings, additive contents and decorated multiplicities with
  death at infinity follow, with countable support. Every pointwise finite-dimensional
  real-indexed module over a field is naturally isomorphic to an algebraic direct sum of
  scalar interval modules with order-convex supports (open or closed endpoints,
  singletons, tails and the whole line allowed), and the rank barcode of every strict
  finite observation list is the multiset of nonempty sampled intersections of these
  summands. The locally finite decorated diagram of a q-tame module is bottleneck-stable:
  an actual ε-interleaving of q-tame modules bounds the distance of the extracted diagrams
  by ε. Rips sublevel modules of totally bounded spaces are q-tame, their diagrams agree
  with the finite diagrams on finite spaces, and they are stable under Hausdorff and
  Gromov–Hausdorff perturbation, with convergence of finite samples to a totally bounded
  target. Birth-at-minus-infinity strata and finite-diagram compatibility for arbitrary
  q-tame modules are not claimed.
- **Multiparameter persistence.** Over any field and for `n ≥ 1`, a finitely presented
  persistence module indexed by `ℝⁿ` has a minimal finite rank-projective resolution whose
  terms vanish in degrees above `2n−2`; the hook multisets of its terms are independent of
  the chosen minimal resolution, so its signed hook barcode is well defined and finite,
  and its rank invariant is the alternating sum of the term ranks. An `ε`-interleaving of
  two such modules gives an unshifted `(2n−1)ε`-interleaving of the parity sums of their
  resolutions and a matching of the cross-sign hook multisets at radius `(2n−1)²ε`, so the
  signed bottleneck dissimilarity is at most `(2n−1)²` times the interleaving distance,
  without assuming finite distance or an attained infimum. In one coordinate the signed
  barcode has positive hooks only, their endpoints form the ordinary barcode, and the
  ordinary bottleneck distance of two such barcodes equals the interleaving distance. A
  two-coordinate example realized by finitely presented modules violates the triangle
  inequality for the signed dissimilarity, so no metric instance is attached. Finite
  presentation is closed under cokernels, biproducts and pushouts over any ring and
  preorder; over a field and a partial order, the middle term of a short exact row with
  finitely presented ends, the pullback of a short exact row's quotient map along a map
  from a finitely presented module when the row's left term is finitely presented, and the
  kernel of a composite of two rank-exact deflations whose rows have finitely presented
  left terms are finitely presented. Supporting results cover support-interval and
  rectangle modules, Hall bounds and occurrence matchings, graded free modules and
  presentations, the coordinate interleaving distance, finite-grid Kan reconstruction,
  rank exactness and hooks, and the interval-pair incidence algebra with its
  projective-dimension bounds. The countable extension of the hook matching, optimality of
  the constant and identification of the signed dissimilarity with an ordinary bottleneck
  distance are not claimed.
- **Metric inputs and sampling.** Greedy sparse Rips filtrations have a natural homology
  isomorphism with the relaxed filtration, a log-scale interleaving with the Rips
  filtration of shift `log((1−2η)⁻¹)`, and explicit skeleton-size bounds under a
  doubling hypothesis. Normalized subdivision-Rips bifiltrations have a natural homology
  isomorphism with the large-face cover nerve, and the finite-uniform Gromov–Prokhorov
  distance bounds their restricted homology interleaving distance. Ambient Čech diagrams
  of finite samples are stable under the Hausdorff distance, Rips homology of totally
  bounded subsets is interleaved within twice the Hausdorff distance, and the laws of
  iid Rips sample diagrams satisfy Wasserstein and `W_∞` bounds by the Gromov–Wasserstein
  distance in every degree. The new area `TDA.Probability` holds the couplings and
  moment bounds.
- **Simplicial and topological tools.** Prism-admissible vertex maps induce equal
  homology maps, barycentric subdivision is a homology isomorphism natural for inclusions,
  arbitrary-apex cones contract chains, and measure bifiltrations with finite-uniform
  Gromov–Prokhorov witnesses support the subdivision-Rips results.
- **Reeb.** Height-map pairs between spaces over ℝ bound the interleaving distance of
  interval-component cosheaves and of graph-PL Reeb quotients; vertex-height
  perturbations, extremal lower bounds, exact vertical translation, scaling by the
  absolute slope, exact merge- and split-tree values and cardinality obstructions are
  proved. Translation is a functor on finite real graphs compatible with quotients,
  thickening and smoothing. Realizations of finite trees are contractible and simply
  connected, and conversely; the general quotient comparison is not injective on the
  topologist's sine curve.
- **Mapper.** Refinements induce selector-independent homology maps and persistence
  modules, with finite barcodes under face finiteness; cover maps between real towers
  give interleavings; step-diagram bottleneck bounds are exact for grid translations;
  capped centred towers have bottleneck bounds, including from height-map pairs between
  different domains; essential counts and domain maps are included.
  Two vertex-height functions on one finite graph give Mapper–Reeb reconstruction bounds
  with convergence along vanishing resolutions and exact vertical translation.

## Use in a Lean project

Use the Lean toolchain pinned in this repository's `lean-toolchain` (currently
`leanprover/lean4:v4.33.1`) and add the release to your `lakefile.toml`:

```toml
[[require]]
name = "TDA"
git = "https://github.com/uda-lab/tda-lib.git"
rev = "v0.3.0"
```

Run `lake update TDA`, fetch the prebuilt mathlib dependencies with `lake exe cache get`,
and run `lake build TDA`. Then import the area you need:

```lean
import TDA.Persistence
-- Or import TDA.Library for the seven ordinary library areas.
```

The library areas are `TDA.Simplicial`, `TDA.Filtration`, `TDA.Persistence`, `TDA.Topology`,
`TDA.Reeb`, `TDA.Mapper` and `TDA.Probability`; `TDA.Library` loads all seven. The area
imports and `TDA.Library` omit the standalone example modules, except for the fixtures that
two Persistence library modules import directly; `import TDA` also loads them. The
[import guide](docs/api.md#entry-points) lists the areas and their requirements.

## Build and documentation

The repository pins Lean in `lean-toolchain` and mathlib in `lake-manifest.json`;
`elan` installs the pinned toolchain on first use. From a checkout, prepare the cached
dependencies and run the local library check:

```sh
scripts/bootstrap.sh
scripts/check.sh
```

For generated API pages, run `scripts/build-docs.sh` from a checkout with no
uncommitted changes. It documents `TDA.Library` and its transitive imports, and writes
the site to `docbuild/.lake/build/doc`; the site is not hosted by this repository.
Standalone examples are described in the [import guide](docs/api.md#entry-points).
The [mathematical notes](docs/math/README.md) explain
individual constructions, and the [source register](docs/math/references.md)
records consulted papers and the limits of source comparison.

<a id="future-directions"></a>

## Scope and limitations

The [API guide](docs/api.md) gives the precise assumptions, theorem names and
limits of these results. General geometric persistence, infinite-dimensional persistence
beyond q-tame modules and an executable arbitrary-field reduction are outside the current
scope.

Further directions include identification of boundary transport with an ordinary
Wasserstein coupling API, birth-at-minus-infinity strata and compatibility with the finite
`Diagram` API for other finite-type q-tame modules, the countable-sum extension of
signed-barcode stability and higher-dimensional Mapper–Reeb approximation. On `develop`, the
product thickening of every constructible real space is constructible, for every `ε ≥ 0` and
without a Hausdorff hypothesis (de Silva, Munch and Patel, *Categorified Reeb Graphs*,
Theorem 4.27; see the [API guide](docs/api.md)); this is not part of v0.3.0.
[Issue #227](https://github.com/uda-lab/tda-lib/issues/227) records the roadmap and its
source links.

## License

The library is licensed under [Apache-2.0](LICENSE).
