# Changelog

Published entries summarize the existing GitHub Releases, which contain the full
results, assumptions and limitations. Their versioned API guides describe the
released interfaces. [Current documentation](docs/README.md) follows the checkout;
it can include work absent from the latest release. This is a 0.x API with no
cross-version compatibility promise.

## Unreleased

Changes on `develop` after v0.3.0; the next release version is undecided.

- Extend certified finite F₂ computation on valid finite graded simplex lists
  with barcode cycle representatives, complete integer-sublevel homology bases,
  supplied-cycle coordinates and boundary fillings. Add validated vertex-induced
  homology matrices and homology preimages with chain certificates; preimage
  search is exponential in the source Betti dimension. See the
  [finite computation](docs/math/finite-ph-computation.md),
  [induced maps](docs/math/finite-ph-maps.md) and
  [homology lifts](docs/math/finite-ph-lifts.md) guides.
- Compute ranks and nullities of validated finite F₂ homology maps. Rank
  evaluation is exponential in source Betti dimension. See the
  [homology-map dimensions](docs/math/finite-ph-map-dimensions.md) guide.
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
- Add a repository-internal Comparator agreement check (`ComparatorChallenge`,
  `comparator.json`) to `scripts/check.sh`; it checks agreement with a frozen
  reference, not source fidelity (see `docs/adr/0003-frozen-comparator-contract.md`).
- Add software citation metadata: `CITATION.cff` and the
  [citation guide](docs/citation.md).
- Reorganize README, release history and documentation navigation.

### Breaking changes

- Move the pinned toolchain to `leanprover/lean4:v4.35.0`; mathlib is pinned to
  the matching `56a005855ea17e0b0958f73ec801ae140b0a1679`. Consumers must use
  Lean v4.35.0; the build now emits around 520 deprecation-warning lines and new
  "designed for use with the module system" import warnings. The bump also
  changed two upstream types, and the statements that use them were restated
  without changing their mathematical content. Mathlib's `CategoryTheory.End X` is now a
  one-field structure, so 30 public results on endomorphisms, including the
  `IsRankProjectiveCover.endomorphism_isIso` field, the `Hook`/`HookInfinity`
  `endRingEquiv` lemmas and the `hookMatrixUnit` lemmas, state through `End.asHom` and
  `End.of` (for example `IsIso u.asHom` and `u.asHom ≫ π = π`). `ProbabilityMeasure.map`
  now takes the function, so `MeasureCoupling` (fields `fst_map`/`snd_map`),
  `MeasureCoupling.map`, `MeasureCoupling.sampleLaw`, `Rips.sampleLawMeasure_map_isometry`,
  `map_carrierProbability_val` and `map_supportProbability_val` use `μ.map f`
  ([#942](https://github.com/uda-lab/tda-lib/pull/942)).
- `TDA.Mapper.GraphPL.geometricInterleavingDistance_mergeY_eq_half` no longer
  takes the redundant explicit `hab : a < b` argument; remove that argument at call sites
  ([#820](https://github.com/uda-lab/tda-lib/pull/820)).
- `TDA.Persistence.Rips.diagramOccurrence` is now an `abbrev` for
  `diagramDecoratedPoint`, with the same values
  ([#759](https://github.com/uda-lab/tda-lib/pull/759)).
- Standalone fixtures are no longer imported by `TDA.Persistence` or `TDA.Library`:
  the boundary-transport far-atom fixtures, the two identity Hom-cover examples, and the
  modules `TDA.Persistence.EphemeralIntervalIso`, `CutSubspacesExamples`,
  `FiniteRankProjectiveResolutionKanExamples` and `FiniteHookDeflationExamples`. Import
  the module itself, `TDA.Persistence.Examples` or `TDA`
  ([#783](https://github.com/uda-lab/tda-lib/pull/783), [#785](https://github.com/uda-lab/tda-lib/pull/785),
  [#854](https://github.com/uda-lab/tda-lib/pull/854)).

### Renames and module moves

Fully qualified names, statements and hypotheses are unchanged by the following unless
stated; only defining modules moved. No public declaration was removed or renamed.

- The collapsed half-plane `TDA.Persistence.BoundaryTransport.Space`, its instances,
  `ClosedHalfPlane`, `Interior`, `collapse`, `depth`, `rho` and their lemmas moved from
  `TDA.Persistence.BoundaryTransportGeometry` to `BoundaryTransportGeometryCore`;
  `BoundaryTransport.Reverse.boundaryPlan`, `singlePairReservoirCompetitor` and their
  lemmas moved from `BoundaryTransportReverse` to `BoundaryTransportReverseCore`. The
  far-atom fixtures (`far_points_shortcut`, `far_points_squared_shortcut_and_boundary_legs`,
  `Reverse.farSource`, `Reverse.farTarget` and the `Reverse.far_*` cost results) moved to
  `BoundaryTransportGeometryExamples` and `BoundaryTransportReverseExamples`. The old modules
  import both and are no longer part of `TDA.Persistence`
  ([#854](https://github.com/uda-lab/tda-lib/pull/854)).
- `FiniteRankProjectiveHomCover.Examples.zero_identity_homCover` and
  `principalUpset_identity_homCover` moved to `TDA.Persistence.FiniteRankProjectiveHomCoverExamples`;
  `TDA.Persistence.FiniteRankProjectiveHomCover` no longer provides them
  ([#785](https://github.com/uda-lab/tda-lib/pull/785)).
- The finite-resolution helpers `FiniteRankProjectiveResolution.identity`, `shift`, `tail`,
  `biprod`, `appendZero`, `appendZeros`, `termAt` and their lemmas moved from
  `TDA.Persistence.RankSchanuelResolution` to `FiniteRankProjectiveResolution`, and
  `MinimalFiniteRankProjectiveResolution.termAt_eq_resolution_termAt` from
  `RankSchanuelUnshifted` to `FiniteRankProjectiveResolutionUniqueness`
  ([#795](https://github.com/uda-lab/tda-lib/pull/795)).
- `IsPointwiseShortExact.comp_eq_zero` and `comp_eq_zero_of_range_eq_ker` moved from
  `RankExactKernel` and `RankExactGenerated` to `TDA.Persistence.RankExact`
  ([#841](https://github.com/uda-lab/tda-lib/pull/841)).
- `TDA.Persistence.Diagram.empty` moved from `RipsSamplingMeasure` to
  `TDA.Persistence.Diagram` and is now `noncomputable`
  ([#846](https://github.com/uda-lab/tda-lib/pull/846)).
- `TDA.Mapper.GraphPL.mergeFoldD02`, `mergeFoldD12` and `mergeFoldD23` moved from
  `GraphPLReebMergeFold` to `GraphPLReebMergeHeight`, and `TDA.Reeb.GraphPL.plHeight_smul`
  from `TDA.Mapper.GraphPLReebScaling` to `TDA.Reeb.GraphPLHeight`
  ([#820](https://github.com/uda-lab/tda-lib/pull/820)).
- Deprecated aliases: `TDA.Persistence.GeneratedUpsetResolution.HookInfinity.projective`
  (now a theorem; the instance is `TDA.Persistence.HookInfinity.projective` in
  `TDA.Persistence.HookInfinityProjective`, [#779](https://github.com/uda-lab/tda-lib/pull/779)) and
  `TDA.Mapper.RefinementHomologyDiagramTightnessExamples.nonempty_realInterleaving_of_structureMap_eq_zero`
  (use `TDA.Mapper.nonempty_realInterleaving_of_structureMap_eq_zero`,
  [#820](https://github.com/uda-lab/tda-lib/pull/820)).

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
