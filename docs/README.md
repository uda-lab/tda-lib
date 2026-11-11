# Documentation guide

Use this guide to choose a subject, then follow the API guide for declaration names
and the mathematical notes for definitions, hypotheses and source comparisons.
It describes the **current checkout**. The [changelog](../CHANGELOG.md) separates
unreleased work from published results and links to versioned API guides.
[Installation and imports](../README.md#use-in-a-lean-project) use v0.3.0.
See the [software citation guide](citation.md) when referencing a release or
development commit.

## Persistent homology and computation

Pointwise finite-dimensional persistence modules over a field indexed by a finite
chain have interval decompositions and rank barcodes. Finite simplex filtrations give homology diagrams with
multiplicities, half-open finite bars and essential bars; finite real filters have
bottleneck stability bounds. Local loss derivatives and Hessians require explicit
ordered representatives and lifts. The certified executable reduction accepts valid
finite graded simplex lists over F₂ and rejects invalid lists; the general theory
APIs do not provide arbitrary-field executable extraction.

Start with the [PH contracts](api.md#persistent-homology-results-and-computational-boundary),
[finite interval decomposition](math/finite-interval-decomposition.md),
[sublevel diagrams](math/finite-sublevel-diagram.md) and
[certified computation](math/finite-ph-computation.md).
For real-indexed modules, use the [finite-constructible isometry](math/constructible-isometry.md),
[real interval decomposition](math/real-interval-decomposition.md) and
[q-tame diagram guide](api.md#q-tame-persistence-rectangle-measures).
These settings have different hypotheses and endpoint conventions; the q-tame
API does not cover birth-at-minus-infinity strata.

## Distances, transport and representations

Finite positive diagrams support real-exponent matching costs; finite nonnegative
real masses support boundary transport. Borel boundary transport uses the strict
birth–death half-plane with a collapsed boundary point. Its existence and metric
results concern finite Borel measures and the stated exponent assumptions;
quantization convergence requires finite diagonal persistence. Its relation to an
ordinary Wasserstein coupling API remains a separate boundary.

Use the API sections on [finite matching and transport](api.md#finite-real-exponent-matching-and-transport-costs)
and [collapsed-boundary geometry](api.md#collapsed-boundary-geometry), followed by
[finite weighted transport](math/finite-weighted-boundary-transport.md),
[metric laws](math/boundary-transport-metric.md) and
[approximation](math/boundary-transport-approximation.md).
Gaussian [images](api.md#gaussian-persistence-images) and
[weighted kernels](api.md#weighted-gaussian-kernel-embedding) have stability bounds
under explicit bandwidth, pixel and weight assumptions. The
[measure embedding note](math/gaussian-measure-universality.md) distinguishes
injective measure embeddings from finite-pixel images, which are not characteristic.
[Native boundary-transport feature bounds](api.md#gaussian-stability-under-native-boundary-transport)
also have their own weight and moment conditions.

## Multiparameter persistence

For finitely presented modules indexed by ℝⁿ over a field with n ≥ 1, finite minimal
rank-projective resolutions give signed hook barcodes and stability bounds.
The signed bottleneck dissimilarity need not satisfy the triangle inequality.
One-coordinate ordinary barcodes, positive affine restrictions and ordinary slice
matching distance have separate contracts; the slice matching distance is bounded
by coordinate interleaving distance, without a separation claim.

Begin with [presentations and rank-exact lifting](api.md#interval-supports-presentations-and-rank-exact-lifting),
then [signed hook stability](api.md#signed-hook-bottleneck-stability),
[positive affine slices](math/positive-affine-slices.md) and
[slice matching](math/affine-slice-matching.md).
The API guide also covers finite simplicial witnesses, incidence-algebra tools,
closure properties and examples. These are theory interfaces; countable hook
matching and optimality of the signed stability constant are not claimed.

## Metric inputs and sampling

Finite Rips and ambient Čech filtrations have diagram stability bounds under their
respective metric and embedding hypotheses. Rips modules of totally bounded spaces
are q-tame; their diagram and sampling results use the locally finite diagram API.
Sparse Rips and normalized subdivision-Rips have separate approximation and measure
stability contracts. Sampled Rips laws have Wasserstein bounds, with confidence and
finite total-variation results under the assumptions in the sampling guide.

Use [Rips inputs](api.md#metric-input-and-rips-diagrams),
[ambient Čech complexes](api.md#ambient-čech-complexes),
[sampled laws](api.md#sampled-rips-laws),
[sparse Rips](api.md#greedy-sparse-rips-geometry-and-deletion-maps) and
[subdivision-Rips](api.md#normalized-subdivision-rips-and-measure-stability).
The [sampling confidence note](math/rips-sampling-confidence.md) and
[law stability note](math/sampled-rips-laws.md) explain the probabilistic conditions.
A comparison of cover-nerve homology with the multicover space's own homology is
not claimed.

## Reeb and Mapper

Interval-component cosheaves and finite real graphs support smoothing and
interleaving theory. Graph-PL inputs have finite Reeb realizations and ordinary
and MultiNerve Mapper comparisons under explicit cover and height hypotheses.
Categorical reconstruction and refinement-induced Mapper homology are abstract
constructions, rather than an executable Mapper algorithm. The ordinary incidence
graph forgets parallel-edge multiplicity.

Start with [Reeb perturbations](math/reeb-perturbation.md),
[geometric/cosheaf interleavings](math/reeb-geometric-interleaving-equivalence.md),
[Mapper constructions](math/mapper.md) and
[categorical Mapper–Reeb approximation](api.md#categorical-mapper-and-reeb-approximation).
Current constructible-space results extend beyond graph input: see
[thickening tools and assembly](math/reeb-thickening-constructible.md),
[the thickening–cosheaf comparison](math/reeb-thickening-cosheaf-comparison.md) and
[constructible-input reconstruction](math/mapper-reeb-approximation.md).
The notes specify the constructibility and cover hypotheses; higher-dimensional
Mapper–Reeb approximation is outside this contract. Mapper step-diagram stability
and capped centred height-map pairs are described in the
[area contracts](api.md#areas-and-intended-use).

## Simplicial and topological foundations

Signed chains, homology, vertex maps and prism homotopies support the persistence
and Mapper developments. Follow [signed vertex maps](math/simplicial-vertex-maps.md),
[finite homology](math/simplicial-finite-homology.md) and
[subdivision and prisms](api.md#barycentric-subdivision-and-prism-homotopies).
The [area and import guide](api.md#entry-points) helps select a narrower dependency
footprint and locate separately imported examples.

## Boundaries and further directions

Read the [API review and extension limits](api.md#review-and-extension-boundaries)
and [source register](math/references.md) alongside each subject's notes. Source
matches, checked finite specializations and library extensions are distinct;
mechanical verification does not certify every declaration against external papers.
The software's license does not replace third-party source-specific rights analysis.

Further directions include ordinary Wasserstein identification of boundary
transport, birth-at-minus-infinity strata and broader finite-diagram compatibility
for q-tame modules, countable signed-barcode stability, and higher-dimensional
Mapper–Reeb approximation. [Issue #227](https://github.com/uda-lab/tda-lib/issues/227)
records source-linked directions; the current notes distinguish available results
from remaining boundaries.

## Generated API pages

The [lightweight local site](../docsite/README.md) renders these guides without
Lean. See [generated API availability](generated-api.md) for the distinction
between curated guides and revision-specific declaration pages.

The [API guide](api.md) is available without generating HTML. For declaration pages,
run `scripts/build-docs.sh` from a clean checkout, as described in the
[build instructions](../README.md#build-and-documentation). The output is
`docbuild/.lake/build/doc`; it is not hosted by this repository.
Generation targets `TDA.Library` and its transitive imports, excluding standalone
examples outside that import closure. Use the generated pages for the revision
that produced them and the corresponding source modules for separately imported
examples. Generation is separate from reading these Markdown guides.
