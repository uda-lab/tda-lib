# Changelog

Published entries summarize the existing GitHub Releases, which contain the full
results, assumptions and limitations. Their versioned API guides describe the
released interfaces. [Current documentation](docs/README.md) follows the checkout;
it can include work absent from the latest release. This is a 0.x API with no
cross-version compatibility promise.

## Unreleased

Changes on `develop` after v0.3.0; the next release version is undecided.

- Extend constructible-space thickenings, their interval-components cosheaf
  comparison and categorical Mapper reconstruction beyond graph-PL input, under
  the stated constructibility and cover hypotheses. See the
  [Reeb and Mapper guide](docs/README.md#reeb-and-mapper).
- Add positive affine slices and ordinary slice matching distance, rank erosion,
  finite simplicial rank-resolution witnesses and their distance calculations,
  and further finite-presentation and incidence-algebra interfaces. See the
  [multiparameter guide](docs/README.md#multiparameter-persistence).
- Add finite-sample confidence bounds and finite total-variation stability for
  sampled Rips laws, and Gaussian feature bounds under native boundary transport.
  Expose generic q-tame diagram stability, real interleaving rank obstructions and
  native finite-measure boundary-plan interfaces. See the
  [persistence](docs/README.md#persistent-homology-and-computation),
  [transport](docs/README.md#distances-transport-and-representations) and
  [metric input](docs/README.md#metric-inputs-and-sampling) guides.
- Separate remaining standalone fixtures from ordinary library imports, including
  boundary-transport far-atom fixtures. Use the current
  [entry-point guide](docs/api.md#entry-points) when selecting example imports.
- Reorganize README, release history and documentation navigation.

[Full changes since v0.3.0](https://github.com/uda-lab/tda-lib/compare/v0.3.0...develop).

## v0.3.0

Published 2026-10-29. [Release notes](https://github.com/uda-lab/tda-lib/releases/tag/v0.3.0)
· [Versioned API guide](https://github.com/uda-lab/tda-lib/blob/v0.3.0/docs/api.md).

- Add Borel boundary transport on the collapsed half-plane, including attainment
  and metric laws for finite measures and quantization under finite diagonal
  persistence. Identification with an ordinary Wasserstein coupling API is not claimed.
- Add decorated q-tame diagrams and bottleneck stability, real pointwise
  finite-dimensional interval decompositions, and totally bounded Rips consumers.
  Birth-at-minus-infinity strata and finite-diagram compatibility for arbitrary
  q-tame modules are not claimed by this release.
- Add finite rank-exact signed hook barcodes and bottleneck stability for finitely
  presented modules indexed by ℝⁿ over a field with n ≥ 1. The signed dissimilarity can fail
  the triangle inequality; it has no metric instance.
- Add sparse and subdivision-Rips results, Hausdorff and finite-uniform
  Gromov–Prokhorov stability, sampled Rips laws, and simplicial/topological tools.
- Add Reeb height-map pairs, translations, finite-tree results and Mapper homology
  along refinements and step towers, under the release's stated hypotheses.
- Add `TDA.Probability` to `TDA.Library`. The release reports no removed or renamed
  public declarations. Standalone examples remain outside ordinary library imports,
  except the fixture dependencies identified in its release notes.

Lean: `leanprover/lean4:v4.33.1`. The certified finite F₂ computation is unchanged.
See the release notes for exact bounds, source-review limits and unsupported extensions.

## v0.2.0

Published 2026-10-23. [Release notes](https://github.com/uda-lab/tda-lib/releases/tag/v0.2.0)
· [Versioned API guide](https://github.com/uda-lab/tda-lib/blob/v0.2.0/docs/api.md).

- Add real-exponent finite matching costs and finite real-weight boundary transport,
  finite-constructible isometry and finite representation interfaces.
- Add Gaussian persistence images and weighted kernels, analytic measure
  embeddings, and finite Rips/Čech stability and sampling results. Finite-pixel
  images are not characteristic; infinite-input diagram stability is not claimed
  by this release.
- Extend bounded Reeb smoothing/interleaving theory and graph-PL ordinary and
  MultiNerve Mapper comparisons and categorical reconstruction, under explicit
  constructibility, cover and height assumptions. These are abstract constructions.

Lean: `leanprover/lean4:v4.33.1`; six library areas. The certified finite F₂
computation is unchanged.

### Renames and module moves

Statements, hypotheses and proofs are unchanged by the following; only identifiers and module paths moved. No compatibility aliases are provided.

- Public names of the form `actual*` / `Actual*` are replaced by names for the represented mathematical objects, for example `ActualLossDerivative` → `SublevelLossDerivative`, `actualBoundaryMatrix` → `faceBoundaryMatrix`, `actualHomologyEquivOriginal` → `prefixHomologyEquivMatrixHomology`, `actualPivotBarcode` → `facePivotBarcode`. The complete old-to-new table is in [PR #473](https://github.com/uda-lab/tda-lib/pull/473). The digests `docs/math/actual-ph-loss-*.md` are now `docs/math/sublevel-loss-derivatives.md` and `docs/math/sublevel-loss-hessians.md`.
- `TDA.Mapper.GraphPL.exists_mem_K_of_mem_Icc` became `TDA.Reeb.CriticalValues.exists_mem_K_of_mem_Icc` (module `TDA.Reeb.CriticalValues`); the shared lemma `TDA.Reeb.GraphPL.dartHeight_injective` (module `TDA.Reeb.GraphPLHeight`) replaces private copies ([#487](https://github.com/uda-lab/tda-lib/pull/487)).
- The generic label-face lemmas `labelFace`, `labelFace_le`, `eq_labelFace_of_le`, `vertexCellsEquiv_labelFace` and `vertexCellsEquiv` moved to `TDA.Mapper.MultiNerveGraphPL` ([#486](https://github.com/uda-lab/tda-lib/pull/486)).
- New module `TDA.Mapper.GraphPLRealizationTopology` holds the barycentric-coordinate, Hausdorffness, edge/vertex equality, local path-connectedness, injectivity and compactness results for graph realizations, moved out of `GraphPLConstructible` and `GraphPLReebQuotient` ([#489](https://github.com/uda-lab/tda-lib/pull/489)).
- New module `TDA.Mapper.GraphPLDataRefinement` holds the graph-PL data refinement maps (`graphPLRefineHom`, `graphPLRefineIso`, the level-vertex and span-edge equivalences, their transitivity lemmas, `range_vertexHeightLevels_subset` and `graphPLRefineToOverIso`), moved out of `TDA.Mapper.GraphPLRefinement`, which keeps the uniform Mapper comparison declarations and still imports everything it did before ([#490](https://github.com/uda-lab/tda-lib/pull/490)).
- `TDA.Persistence.Reduction.FilteredNormalForm` is split into three stage modules: `FilteredNormalForm.NormalMatrix` (pivot pairing, `normalMatrix`, `normalDifferential` and its conjugation of the boundary), `FilteredNormalForm.NormalHomology` (alive coordinates, paired and essential intervals, normal cycles, boundaries, homology and rank formulas) and `FilteredNormalForm.OriginalHomology` (`OriginalCycle`, `OriginalBoundary`, `cycleBasisEquiv`, `originalHomologyEquivAlive` and the `originalHomologyMap` family). `FilteredNormalForm` itself is now an imports-only entry point, so existing imports and fully qualified names keep working ([#491](https://github.com/uda-lab/tda-lib/pull/491)).
- Example fixtures only: the shared rank-example fixtures live in `TDA.Persistence.RankExampleFixtures` ([#488](https://github.com/uda-lab/tda-lib/pull/488)).

## v0.1.0

Published 2026-10-15. [Release notes](https://github.com/uda-lab/tda-lib/releases/tag/v0.1.0)
· [Versioned API guide](https://github.com/uda-lab/tda-lib/blob/v0.1.0/docs/api.md).

- First mathematical release: signed simplicial chains and homology,
  finite-chain interval decomposition with pointwise finite-dimensional fibers over
  a field, sublevel diagrams retaining
  multiplicities and essential bars, finite-filter bottleneck stability, and
  local loss derivative/Hessian results under explicit lift hypotheses.
- Add certified executable persistence reduction over F₂ for valid finite graded
  simplex lists; invalid lists are rejected.
- Add bounded Reeb/cosheaf and ordinary Mapper theory interfaces. Unrestricted
  convergence, arbitrary-field executable decomposition and global smoothness
  across arbitrary pairing changes are not claimed by this release.

Lean: `leanprover/lean4:v4.33.1`; six library areas. See the release notes for
source-comparison and geometric scope limits.

## v0.0.2

Published 2026-10-07. [Release notes](https://github.com/uda-lab/tda-lib/releases/tag/v0.0.2).

Infrastructure only: shared skills, guarded Lean/Codex commands, optional harness
adapters and develop/main integration policy. Lean sources and dependency pins
are unchanged; no TDA proofs or algorithms are claimed.

## v0.0.1

Published 2026-10-07. [Release notes](https://github.com/uda-lab/tda-lib/releases/tag/v0.0.1).

Initial library scaffold and development infrastructure; no TDA proofs or algorithms.
