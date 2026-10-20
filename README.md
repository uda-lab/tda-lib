# tda-lib

`tda-lib` is a Lean 4 library for topological data analysis. It formalizes finite
persistent homology, a certified computation of persistence over the two-element
field, and selected Reeb and Mapper constructions.
[v0.1.0](https://github.com/uda-lab/tda-lib/releases/tag/v0.1.0) is the
first release of its mathematical results.

## Results

- **Persistent homology.** The library builds signed simplicial chains and homology
  from actual faces, decomposes pointwise finite-dimensional persistence modules
  indexed by a finite chain into intervals, and relates a finite simplex filtration
  to its actual sublevel persistence diagram. The diagram retains multiplicities,
  finite half-open intervals and essential bars. For real-valued finite filters it
  proves a bottleneck stability bound, including changes in simplex pairing.
  Local regularity, derivative and Hessian results for diagram-based losses use
  explicit hypotheses on ordered representatives and lifts.
- **Certified computation.** An executable reduction computes persistence over
  F₂ from a valid finite list of graded simplices. Its correctness theorem
  identifies the output with the actual sublevel diagram in every degree;
  invalid lists are rejected.
- **Reeb and Mapper theory.** The library develops interval cosheaves, finite
  graph and constructible-cosheaf comparisons, and ordinary Mapper from pullback
  component covers. Graph and refinement results have explicit finiteness,
  coverage or constructibility assumptions. These are theory interfaces rather
  than an executable Mapper package or a general convergence theorem.

The [API guide](docs/api.md) gives the precise assumptions, theorem names and
limits of these results. General geometric or infinite-dimensional persistence
and an executable arbitrary-field reduction are outside the current scope.

## Use in a Lean project

Add the release to your `lakefile.toml`:

```toml
[[require]]
name = "TDA"
git = "https://github.com/uda-lab/tda-lib.git"
rev = "v0.1.0"
```

Run `lake update` and `lake build TDA`, then import the area you need:

```lean
import TDA.Persistence
-- Or import TDA.Library for all six library areas.
```

The ordinary area imports and `TDA.Library` omit standalone examples. `import TDA`
also loads the example modules. The [import guide](docs/api.md#entry-points)
lists all six areas and their requirements.

## Build and documentation

The repository pins Lean in `lean-toolchain` and mathlib in `lake-manifest.json`.
From a checkout, prepare the cached dependencies and run the local library check:

```sh
scripts/bootstrap.sh
scripts/check.sh
```

For generated API pages, run `scripts/build-docs.sh` from a clean committed
checkout. It writes the site to `docbuild/.lake/build/doc`; the site is not
hosted by this repository. The [mathematical notes](docs/math/README.md) explain
individual constructions, and the [source register](docs/math/references.md)
records consulted papers and the limits of source comparison.

<a id="future-directions"></a>

## Development beyond v0.1.0

The `develop` branch includes these additional bounded results. The
[API guide](docs/api.md) and its mathematical notes give their exact hypotheses.

- **PH distances and stability.** For finite positive diagrams with unit occurrence
  masses and finite deaths, partial-matching minima equal optima over finite real
  boundary plans, with real exponents p ≥ 1 and maximum ground norm. Rooted costs
  satisfy distance laws and explicit cardinality-dependent perturbation bounds.
  Powered and rooted matching and real-plan optima agree and are attained. If N is
  the total finite-occurrence count, d_p ≤ d_1 ≤ N^(1−1/p) d_p. Common diagonal
  translation preserves these costs; nonnegative coordinate scaling by c multiplies
  powered costs by c^p and rooted costs by c. For natural p, total persistence over
  finite bars is translation-invariant and homogeneous under positive scaling.
  Finite Rips and Čech diagrams satisfy face-count bar bounds and corresponding
  total-persistence bounds using the carrier diameter or a stated enclosing radius.
  Finite-constructible real-indexed modules over a field satisfy barcode isometry
  with finite-dimensional critical fibers, a zero left tail, half-open strata and a
  possibly nonzero final tail. This also applies to actual finite-complex sublevel
  homology modules. Finite boundary transport additionally permits arbitrary
  nonnegative real masses that split between labels: powered and rooted optima
  are attained for p ≥ 1, and unit masses recover the occurrence-based costs.
- **Persistence representations.** Gaussian persistence images at fixed positive
  bandwidth and fixed disjoint measurable pixels, and weighted Gaussian kernels,
  have stability bounds on finite diagram parts against first-order matching cost under
  explicit weight assumptions. For the arctan weight with C ≥ 0, the kernel constant
  is 2C + √2·π/(2|σ|), with no bandwidth-sign hypothesis, and the image constant is
  2C + 3·√(π/2)/σ for σ > 0. Actual Rips and Čech diagrams have radius-scale embedding,
  fixed-diagram kernel-value and image consumers under their stated same-label
  hypotheses; the sup-norm Čech consumers use half the pairwise discrepancy.
  Log-scale Rips–Čech consumers use the exact bottleneck or log 2 bounds in degrees
  n ≥ 1 under the compatible-label and positivity hypotheses. At nonzero bandwidth,
  the Gaussian RKHS on the full birth–death plane separates finite signed Borel
  measures and is uniformly dense in C₀(ℝ²). Strictly positive measurable weights
  with finite weighted mass give injective embeddings of positive persistence
  measures, including infinite-mass Radon measures; finite atomic embeddings agree
  with the existing diagram embeddings. These analytic constructions are abstract,
  and do not make finite-pixel images characteristic. Second-level Gaussian feature
  bounds are available for general weights, but have no arctan instance.
- **Metric inputs.** Finite Rips and ambient Čech filtrations are constructed.
  Rips diagrams satisfy a same-label pairwise-discrepancy bound. For finite nonempty
  metric spaces, full actual Rips diagrams satisfy d_B ≤ 2 d_GH in every degree,
  without equal-cardinality or common-label assumptions. Finite samples embedded
  in one ambient metric space have a twice-Hausdorff-error bound; two samples of
  a possibly infinite target have a bound of twice their summed errors, comparing
  their finite diagrams only. Hausdorff-convergent samples of a fixed finite target
  have bottleneck-convergent full diagrams. Adjacent maps and rectangular matrix
  sequences give finite persistence modules and basis-independent interval
  barcodes; a zero-left-tail, constant-final-cell adapter retains supplied real
  critical values and their finite or essential endpoints. These are theory
  adapters, not executable extraction. Exact diagrams and bottleneck values over
  `ZMod 2` are computed for two points at radius scale in degree zero and every
  positive degree, and for the acute triangle at radius scale in degrees zero and
  one and log scale in degree one. Positive scaling of real-indexed modules scales
  their interleaving distance by the same positive factor, over every ring and
  including infinite distance. For two filters positive on edges, common positive
  scaling translates their log-scale diagrams and preserves their mutual log-scale
  bottleneck and interleaving distances in every degree n ≥ 1. For one finite
  sup-norm configuration, Rips and Čech diagrams are within half the carrier
  diameter in bottleneck distance. Log-scale Čech–Rips diagrams are within log 2
  in degrees n ≥ 1 under the stated positivity and embedding assumptions.
- **Reeb.** In the library's finite real-graph category, geometric smoothing has
  coherent composition, and geometric and cosheaf interleavings agree, with equal
  extended distances. Geometric smoothing admits parameter enlargement, geometric
  interleavings are monotone, constructible smoothing lifts to constructible cosheaves,
  and smoothing a geometric interleaving preserves its parameter with two-sided
  distance bounds. Height-range, top-component and interval-local obstructions give
  lower bounds; exact fixture distances include 1/2 between the edge and its midpoint,
  1/4 between the parallel-edge and single-edge graphs, and ⊤ under a component
  obstruction. Finite Reeb data have an incidence quiver and a simple incidence graph;
  the latter forgets parallel-edge multiplicity. The quotient of every constructible
  real space satisfies the smoothing absorption comparison, while constructibility
  of its product thickening is established here for graph input.
- **Mapper.** Graph-PL inputs have ordinary and MultiNerve Mapper constructions,
  a cover-dependent cell classification and finite Reeb incidence data under
  explicit cover and height assumptions. A member-adapted, height-separating,
  vertex-height-covering uniform cover with 0 < g and 2g ≤ r identifies its
  MultiNerve Mapper data with the graph-PL finite Reeb data; such covers exist with
  r below any prescribed positive bound. Closed levels have the stated vertex and
  crossing-edge components, and inclusion into a level window is bijective on path
  components. Finite Reeb data and member-adapted Mapper data are compatible with
  covering refinements. Under 2g ≤ r, the ordinary Mapper one-skeleton agrees with
  the incidence graph, which forgets parallel edge cells. Under the vertex-height-
  covering hypothesis, the interval-components cosheaf is constructible and agrees
  with the cosheaf of the finite Reeb data. The actual Reeb quotient of a finite
  graph-PL realization is identified with its finite graph realization. For a finite
  bounded interval cover of the attained height range, categorical Mapper retains
  components of every nonempty intersection; its reconstructed real graph lies
  within the full width of the retained intervals of that actual Reeb quotient in
  geometric interleaving distance. Vanishing full or retained resolutions give
  convergence, including families with varying finite cover index types. This is
  abstract categorical reconstruction, not an executable Mapper algorithm.

Further directions include all-Radon boundary-transport identification, general
infinite or q-tame persistence, metric stability with actual diagrams of infinite
point sets, higher-dimensional Mapper–Reeb approximation, and constructibility of
the product thickening of a general constructible real space beyond graph input as
in DMP Theorem 4.27. [Issue #227](https://github.com/uda-lab/tda-lib/issues/227)
records their scope and source links.

## License

The library is licensed under [Apache-2.0](LICENSE).
