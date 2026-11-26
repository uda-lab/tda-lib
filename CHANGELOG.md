# Changelog

Published entries summarize the existing GitHub Releases, which contain the full
results, assumptions and limitations. Their versioned API guides describe the
released interfaces. [Current documentation](docs/README.md) follows the checkout;
it can include work absent from the latest release. This is a 0.x API with no
cross-version compatibility promise.

## Unreleased

Changes on `develop` after v0.5.0; the next release version is undecided.

- Downstream-use audit, family 5 (#1263, #1207): `MatrixSequence.Hom.isoOfInverse` (mutually
  inverse matrix morphisms give a natural isomorphism of the modules) and
  `MatrixSequence.barcode_eq_of_inverse_homs`; the downstream regression fixture
  `MatrixSequenceClientExamples`.
- Downstream-use audit, family 4 (#1259, #1207): `bottleneck_dgm_eq_realInterleavingDistance`
  and `nonempty_sublevelInterleaving_iff` now take filters on two finite complexes (statement
  generalised; calls with one complex are unaffected), and
  `bottleneck_dgm_le_of_sublevelInterleaving` bounds the bottleneck distance of the diagrams
  by the parameter of a sublevel interleaving; the downstream regression fixture
  `InterleavingIsometryClientExamples`.
- Downstream-use audit, family 3 (#1252, #1207): `RealBarcode.realization_unique` and
  `RealBarcode.diagram_eq_of_realize_iso` (two positive real barcode realizations of one
  module are the same diagram), the real-line counterpart of `barcode_decomposition_unique`;
  the downstream regression fixture `BarcodeUniquenessClientExamples`.
- Downstream-use audit, family 2 (#1249, #1207): for filter functions on a finite complex,
  `faceSupDifference_le_iff` (the maximal face-value difference is bounded exactly by a
  nonnegative pointwise bound), `faceSupDifference_comm`, the pointwise diagram bound
  `bottleneck_dgm_le_of_abs_sub_le` and its threshold form
  `exists_lt_abs_sub_of_ofReal_lt_bottleneck_dgm`; the downstream regression fixture
  `FilterStabilityClientExamples`.
- Claude cloud setup snapshot: `scripts/claude-cloud-setup.sh` also copies the companion skills
  `github-driven-workflow`, `github-loop-engineering` and `lean-formalization-discipline` from
  `t-uda/skills` at a pinned commit into `~/.claude/skills`, so that `scripts/preflight.sh` finds
  them in a hosted session. `STATUS.txt` records the commit and a per-skill result separately from
  the cache `state` (#683); `docs/claude-cloud-setup.md` adds `GIT_OPTIONAL_LOCKS=0` guidance for
  readers of the shared packages.
- Canonical squared-grade α–Čech comparison (#1138): `Alpha.filtration_le_squaredCech`,
  `Alpha.inclusion_natural_squaredCech` and `isIso_alpha_filtration_le_squaredCech` (every
  grade) target `Alpha.squaredCechFiltration`, which is empty below zero. The legacy
  `Alpha.filtration_le_cech` and `Alpha.inclusion_natural` keep their statements and their
  radius-zero Čech target below zero (not deprecated yet). Migration: replace them by the
  canonical counterparts; the targets agree at `t ≥ 0`
  (`Alpha.reindex_radius_cech_eq_squaredCech_of_nonneg`), and the module docstrings now state the
  negative-grade and nerve-form conventions.
- `RealIntervalObservation`: the scalar crossing count holds for `s ≤ t`
  (`persistenceImage_finrank_eq_scalar_crossing_of_le`,
  `scalar_crossing_card_eq_of_iso_of_le`); at `s = t` it counts the occurrences active at
  `s`. The strict theorems keep their statements and are now corollaries.
- Weaker-hypothesis and attainment variants beside existing statements (#1147):
  `eRankOfStructureMap_le_eRankOfStructureMap_iff_of_finiteDimensional` (finite-dimensional
  images instead of source fibers); `AlphaInput.injective_of_run_eq_some` and
  `AlphaInput.run_correct_of_fintype` (no separate injectivity hypothesis, any `Fintype`
  instance); `simplicialHomologyIncl_zero_isIso_of_edge_reachable_of_ring` (any ring);
  erosion at the exact distance for the scaled families
  (`scaledTranslatedHomology_rankErosion_min`, `scaledTranslatedHomology_eRankErosion_min`,
  `scaledHomology_rankErosion_zero`, `scaledHomology_eRankErosion_zero`).
- Rational α follow-ups (#1208): `rational_cover_from_signed_boundary_of_triangle_sites`
  gives the conclusions of `rational_cover_from_signed_boundary` without injectivity of the
  sites and the hull cycle and with hull membership only for triangle labels; `kernelGrade?`
  (`kernelGrade?_eq_grade?`) is a kernel-reducible form of `grade?`. New fixtures obtain the
  certificate of `supplied_realStage_iff` from `cornerHullCheck` (`trapezoid_checked_stages`,
  `inner_checked_stages`), give the exact α entry `25/4` of an interior edge that is not
  Gabriel (`inner_nonGabriel_cutoff`, `interior_nonGabriel_grade`), and show that the radius
  stability bound is attained (`square_stability_attained`).
- Documentation of behaviour on invalid input (#1149): the unguarded executable entry points of
  the Morse lane, the finite-input outputs, `imageBarcode`, `GraphPLIncidence.label`,
  `incircle` and the collapse-certificate checkers now say in their docstrings that they are
  total and meaningful only under their validity hypothesis, and name the guarded entry point.
  The matchings note records the four invalid Morse inputs and their results. New guarded
  `Option`-valued entry points in the Morse lane return `none` exactly when the input is not
  valid: `check?`, `criticalReport?`, `generate?`, `morseOccurrences?`, `morseDiagram?`, each
  with theorems characterising `none` and `some`. No existing statement changed.
- Signed fixtures for unit cancellation (#1151): an instance over `ℤ` (the filled triangle with
  the usual boundary) with negative entries of the reduced differential, projection and
  inclusion written by hand, a direct evaluation of the homotopy identity, and a negative
  control for incidence `-1`. No statement changed.
- Discrete Morse fixtures with negative controls (#1151): a disc on which the greedy matching is
  not of maximum cardinality; two tie orders with different occurrence lists and equal diagrams;
  the hollow triangle as a complex with no free pair that does not collapse to a point. Two
  `rfl` comparisons of the obtuse-triangle persistence examples are documented as definitional.
  No statement changed.
- Topology (#1148, first stage): `isIso_iteratedLastVertex`, `isIso_flagLastVertex`,
  `chainHomotopy_labeling_lastVertex`, `exists_common_chain_comparisons` and
  `exists_contiguous_apexMap` can be stated and applied from a client file with no scope and
  no local instance, at a literal depth such as `1`; `LastVertexClientExamples` checks this.
  The file-local orders on `Finset I` and the file-local classical `DecidableEq` that their
  statements mentioned are removed. `RationalAlpha.castPoint_apply_zero` and
  `castPoint_apply_one` give the coordinates of `castPoint`.
- Migration (#1148): `SubdivisionRealization.Vertex` is a plain `def`, no longer reducible,
  so instances on `Finset` no longer apply to `Vertex V (n + 1)`; ascribe `Finset (Vertex V n)`
  or `change` where a proof needs them. `vertexLinearOrder` and `vertexNonempty` are global
  instances instead of scoped ones (`open scoped TDA.Topology.SubdivisionRealization` is no
  longer needed). The new instance `flagVertexLinearOrder` orders `Vertex (Finset X) n`.
  Elaborated types: in `isIso_flagLastVertex`, `chainHomotopy_labeling_lastVertex` and
  `exists_common_chain_comparisons` the order on `Vertex (Finset I) n` is
  `flagVertexLinearOrder I n` instead of `vertexLinearOrder` over the removed file-local
  instance `instLinearOrderFinset_tDA` (the same order, `faceLinearOrder I` at depth `0`);
  `exists_contiguous_apexMap` takes `[DecidableEq I]` after `{N}` instead of using the
  removed `ConvexNerve.instDecidableEq_tDA`. Explicit arguments are unchanged.
- Interface follow-ups (#1148, second stage): the classification statements of
  `IncidenceQuotientSimple` can be stated from a client file with no scope, since
  `diagonalIdealTwoSided` is now a global instance (`IncidenceQuotientSimpleClientExamples`
  checks this). The example data of the integer bottleneck, finite constructible, incidence
  quotient, supplied rational α and finite-input matching fixtures are public, so a client can
  state those fixtures; copies duplicated across the rational α and matching fixture files are
  merged into one public definition each. One common lemma replaces repeated proofs:
  `TDA.Simplicial.exists_flag_extrema` (least and greatest member of a flag) and
  `Cancellation.sublevelSupported_iff_prefixSupported_of_iff`, from which both
  `sublevelSupported_iff_prefixSupported` now follow. `FiniteInterval.fiber_eq_classical`,
  `intervalMap_eq_classical` and `intervalModule_obj_eq_classical` relate the executable
  interval definitions to their v0.4.0 classical bodies. The file-local classical
  `DecidableEq` of `SubdivisionRealization` is removed; no statement mentioned it.
- Migration (#1148, second stage): `Alpha.singleton_mem_labelledComplex` no longer takes the
  unused `[DecidableEq V]`; only a call through `@` with that argument changes. Elaborated
  types of fixtures: the supplied rational α fixtures name `SuppliedCarrierExamples.quadSites`,
  `SuppliedCarrierExamples.squareSplit`, `SuppliedGradeEnumerationExamples.innerSites` and
  `SuppliedGradeEnumerationExamples.innerSplit` instead of file-private copies with the same
  bodies, and the generation fixtures name `FiniteInputMatchingExamples.pr`; in the other
  fixture files the private definitions became public under the same names.
- Native erosion fixture (#1063): the non-default Lake target `erosion-fixture` and
  `scripts/run-erosion-fixture.sh` run `RatGradedInput.runErosion` on `triangle` against
  `shiftedTriangle` in degree one as a compiled executable. Radius 0 reports the witness of
  `triangle_runErosion_zero`, radius 49/100 fails and radius 1/2 passes, in about 303 to 324 s on
  the measured host, with the time in `rankAt`; `docs/math/rank-erosion.md` records the host,
  the counts and the phase breakdown. No runtime bound is claimed.
- Exact erosion distance of two uniformly scaled tetrahedron-boundary PH₁ modules (#1048,
  `TDA.Persistence.FiniteSimplicialErosionTwoScales`): for `0 < c` and `0 < c'` over any field,
  erosion between `scaledHomology k (fun _ => c) _` and `scaledHomology k (fun _ => c') _` fails
  below `min (2 * |c - c'|) (max c c' / 2)` by an actual surviving map against a zero fibre, and
  both erosion distances equal `ENNReal.ofReal` of that value
  (`rankErosionDistance_scaledHomology_const`, `eRankErosionDistance_scaledHomology_const`);
  the maximal grade error is `2 * |c - c'|` exactly, and a lifetime-cap lemma holds for
  anisotropic scales. No equality with the interleaving distance is claimed. Fixtures:
  failing radius `3/4` between the scales `1` and `2` with its failure certificate, and both
  regimes (`1` and `2` over `ℚ`, `1` and `5/4` over `ZMod 2`).
- Rips Gromov–Hausdorff stability, client-facing forms (#1206):
  `half_lt_ghDist_of_ofReal_lt_qTameLocallyFiniteDiagram_bottleneck` (threshold form, no sign
  condition) and `qTameLocallyFiniteDiagram_bottleneck_le_ofReal_of_ghDist_le_half`;
  `qTameLocallyFiniteDiagram_congr_linearOrder` (the diagram does not depend on the vertex
  order); the order-free diagram `qTameLocallyFiniteDiagramOrderFree` with
  `qTameLocallyFiniteDiagramOrderFree_eq`, `qTameLocallyFiniteDiagramOrderFree_eq_of_isometryEquiv`,
  `qTameLocallyFiniteDiagramOrderFree_bottleneck_le_two_mul_ghDist` and
  `half_lt_ghDist_of_ofReal_lt_qTameLocallyFiniteDiagramOrderFree_bottleneck` (no `LinearOrder`
  instance); event inclusions `setOf_ofReal_lt_bottleneck_subset_setOf_half_lt_ghDist` and
  `setOf_ofReal_lt_bottleneck_subset_setOf_half_lt_ghDist_of_finite` for random sample metrics;
  and the downstream regression fixture `RipsGHClientExamples`. Existing statements are
  unchanged. The same-universe restriction on the two carriers remains, with its reason
  documented.
- Supplied α carrier for subdivided hull sides (#1213):
  `SuppliedCarrier.alphaCarrier_le_labelComplex_of_subdivided_boundary` and
  `carrier_eq_of_subdivided_boundary` state the carrier equality for a coarse strict hull whose
  sides carry ordered cut labels and for triangles whose chain equals the subdivided hull
  chain, without injectivity of the hull labels. The closed-cover inclusion
  `alphaCarrier_le_labelComplex_of_closed_cover` and `admitted_triangle_contact` are now public
  with their statements unchanged, as are `SubdividedBoundaryExamples.coarse_certificate`,
  `ordered_cuts` and `sites_contained`. `SuppliedCarrierExamples.split_carrier`,
  `split_side_faces` and `splitEmb` give a split-side fixture.
- Consumer fixtures for the executable finite-input fixtures (#1195 D-9, residual of #1150): the
  tetrahedral `sphere` and `ball` inputs now state their degree-two bar about the actual diagram
  and homology (`Examples.sphere_H2_dgm`, `Examples.ball_H2_dgm` through `outputDiagram_eq_dgm`;
  `Examples.sphere_H2_homology_finrank`, `Examples.ball_H2_homology_finrank` through
  `card_essentialPart_dgm_eq_finrank`), and `ImageBarcodeExamples.ComponentMerger` applies
  `runImageBarcode_correct` to its three runs (`image_actual`, `source_actual`, `target_actual`,
  `actual_barcodes_separated`). Fixtures only: no library statement changes.
- Grades and stages for supplied triangulations with subdivided hull sides (#1214): the new
  module `SubdividedStages` gives `subdivided_hull_dual` (a `HullDual` for every refined side),
  `subdivided_edge_counts`, `edge_grade_on_subdivided`,
  `suppliedGrades_eq_reference_of_subdivided_boundary`,
  `supplied_hasGradeTable_of_subdivided_boundary`,
  `supplied_realStage_iff_of_subdivided_boundary` and its `_faces` and `_neg` forms, under the
  hypotheses of `carrier_eq_of_subdivided_boundary` and without injectivity of the hull labels.
  The coarse `supplied_hull_dual`, `supplied_interior_dual`, `grade_on_supplied_face` and
  `suppliedGrades_eq_reference` keep their statements; their proofs now call the new public
  hull-free cores `hull_dual_of_supporting_side`, `interior_dual_of_opposite_occurrences`,
  `grade_on_face_of_edge_grades` and `suppliedGrades_eq_reference_of_face_grades`. The lemmas
  `subdivisionEdges_side`, `multiplicity_absent`, `multiplicity_at_most_one` and
  `multiplicity_listed` are now public with their statements unchanged.
  `SubdividedStagesExamples` gives all real stages of the split triangle, with `BC` entering at
  `5/2` and the refined piece `AM` at `1/4`.
  The executable rational test `SignedBoundary.checkOrderedEdgeCuts` with
  `orderedEdgeCuts_of_check` produces `OrderedEdgeCuts` from rational data, and
  `DirectedEdgeIncidence.chain_eq_of_directed_counts` reduces a chain equality to a finite check
  of net directed counts; the split fixture's `ordered_cuts` and `signed_boundary` use them in
  place of hand proofs (statements unchanged).
  `split_side_faces` and `splitEmb` give a split-side fixture. Grade rows and stages for a subdivided hull
  are not part of this change.
- Shared rank lookups in the erosion scan (#1218): `F2GridRep.erosionFailureCached?` reads each
  matrix rank through a lazily built two-level table of thunks (an outer list linear in the
  breakpoint grades, rows and ranks built when first read), so each distinct floored pair is
  evaluated at most once and only if reached; the enumeration of `erosionFailure?` is
  unchanged. `F2GridRep.erosionFailure?_eq_cached`, registered with `@[csimp]`, makes the
  compiled `runErosion` use it; `F2GridRep.rankAtWith_rankTable` and `lookup_getD_of_forall`
  show that the lookup is `rankAt`. No definition and no statement changed.
  On the recorded host the native fixture at radius `1/2` took about 5 s instead of 333 s
  (`docs/math/rank-erosion.md` § Measured native run); the `phases` and `split` replays of the
  fixture stay uncached and a `memo` replay was added. No runtime bound is claimed.
- New area `TDA.Sheaf` (#1167): for a preorder `X` with its upper Alexandrov topology and a
  complete category `C`, `TDA.Sheaf.Alexandrov.equivalence : X.Sheaf C ≌ (X ⥤ C)` has functor
  `principalSections` (sections over the principal opens `↑p`, with restriction along
  `↑q ⊆ ↑p` for `p ≤ q`) and inverse `kanSheaf` (the pointwise right Kan extension along
  `Alexandrov.principals X`). `counitIso` is the limit projection at `(p, 𝟙)`; `unitIso`
  compares sections over any open with the limit over the principal opens it contains, and
  `restrictionConeIsLimit` and `isPointwiseRightKanExtension` state this for every sheaf.
  `upperSetEquivalence` specializes to `P ⥤ C` for an unbundled preorder `P` through
  `Topology.WithUpperSet P`, with `upperSetSectionsIso` and its restriction and morphism
  naturality. Fixtures in `TDA.Sheaf.AlexandrovExamples` cover the chain `0 ⟶ ℚ` on `Fin 2`,
  the empty open, the non-principal whole antichain `Unit ⊕ Unit` (a binary product) and
  real-indexed `PModule`s over `ℚ` and `ZMod 2`.
- Finite alternating diagrams in `TDA.Sheaf` (#1182): diagrams of vector spaces on a path with
  arbitrary orientation `o : Fin n → Bool`, as functors `Paths (Vertex o) ⥤ ModuleCat k`.
  `TDA.Sheaf.AlternatingDiagram.exists_decomposition` makes every finite-dimensional diagram a
  biproduct of interval diagrams, `multiset_eq_of_iso` makes the multiset of intervals an
  isomorphism invariant, and `barcode`, `barcodeIso`, `nonempty_iso_iff_barcode_eq` and
  `intervalMultiplicity` package the classification. The proof uses the sink reflection
  `reflectSink` (an additive functor, computed on intervals by `reflectInterval`), the source
  reflection `reflectSource` with `reflectSourceUnitIso`, singleton splitting at a source, and
  the existing chain decomposition and uniqueness through `chainToDiagram`. Fixtures on the fork
  `0 → 1 ← 2` show equal dimensions and arrow ranks with different barcodes, a repeated summand
  and the zero diagram.
- Degree-zero singular homology of interval preimages (#1171): for `f : C(X, ℝ)` and a ring `k`,
  `TDA.Reeb.intervalPreimageTopCat f : OpenInterval ⥤ TopCat` sends `I` to `f ⁻¹ I` and an
  inclusion to the actual `preimageInclusion`; `intervalSingularHomology k n f` composes it with
  singular homology with coefficients `ModuleCat.of k k`, and `linearizedIntervalComponents k f`
  is `intervalComponents f ⋙ sigmaConst.obj (ModuleCat.of k k)`. `intervalSingularHomologyIso₀` is a
  natural isomorphism between them with components `TopCat.singularHomology₀Iso`, proved from
  `singularHomology₀Iso_hom_naturality` (any continuous map, on point representatives) with no
  compactness or tameness assumption. The map rule `intervalClass_comp_map_comp_intervalSingularHomologyIso₀_hom_app`
  and its linearized form send the class of `x` to the injection indexed by
  `ZerothHomotopy.mk` of the included point. Fixtures in `TDA.Reeb.IntervalSingularHomologyExamples`:
  the empty interval, an empty source, the identity of `ℝ`, and `f t = t²`, where the band
  `(1, 4)` into `(-1, 4)` induces the fold `k ⊕ k ⟶ k`. Degree zero only; not a derived equivalence.
- Real Alexandrov translations (#1168): on `upperSpace ℝ`, `TDA.Sheaf.AlexandrovTranslation.sheafShift C ε`
  is `TopCat.Sheaf.pushforward` along `translate ε : x ↦ x - ε` (`WithUpperSet.map`), with
  `(S ε F)(U) = F(U + ε)` (`coe_map_translate`) and `↑t ↦ ↑(t + ε)`. The order maps
  `sheafShiftLE`, the transition `sheafTransition`, and the natural isomorphisms `sheafZeroIso`,
  `sheafCompIso` and `sheafCongrIso` are restrictions along preimage opens, with the `RealShift`
  coherence laws. `shiftComparison R ε : sheafShift ε ⋙ realSections ≅ realSections ⋙ RealShift.shift ε`
  identifies them with `shiftLE`, `transition`, `zeroIso` and `compIso`. `SheafInterleaving`
  has the orientation of `RealInterleaving`; `SheafInterleaving.equivRealInterleaving` is an
  equivalence with real witnesses of the principal sections, `zeroEquivIso` identifies zero
  witnesses with sheaf isomorphisms, and `sheafInterleavingDistance_eq` equates the
  extended-infimum sheaf distance with `realInterleavingDistance`. Fixtures in
  `TDA.Sheaf.AlexandrovTranslationExamples`: the shift on `∅`, the whole line and `(t, ∞)`, and the
  upper rays `[0, ∞)`, `[r, ∞)` with `0 ≤ r`, interleaved by modules or sheaves exactly when `r ≤ ε`,
  at sheaf distance `r`.

- Closed-band functors on `D⁺(Sh(ℝ; k))` (#1174): `TDA.Sheaf.DerivedPlus` gives the derived
  inverse and direct images `pullbackPlus` and `pushforwardPlus` of sheaves of modules on
  `DerivedCategory.Plus`, with derived categories as instance arguments, their invertible
  composition comparisons and associativity, and the derived unit `derivedUnit`, invertible
  along homeomorphisms and coherent with composition; `corrRestr` restricts a correspondence
  transform along a map. `TDA.Sheaf.BandConvolution` defines the closed bands `D a`, their proper
  projections `p a` and `q a`, `T a := pullbackPlus (p a) ⋙ pushforwardPlus (q a)`, the radius
  maps `restr : T b ⟶ T a` with `restr_refl` and `restr_trans`, `T0Iso : T 0 ≅ 𝟭` and the
  augmentation `aug`. Fixtures in `TDA.Sheaf.BandConvolutionExamples`.
- Heredity of finite alternating diagrams in `TDA.Sheaf.AlternatingHeredity` (#1182):
  `pathTensor k o i` (Mathlib's `evaluationLeftAdjoint`) gives `P_i ⊗ V`, identified with
  `(vtx o i ⟶ t) →₀ V` at `t` by `pathTensorObjEquiv`; `representable k o i` is
  `P_i = k[paths i → −]` with `representableHomEquiv`. `pathTensorAdjunction` is the evaluation
  Hom adjunction and `projective_pathTensor` makes every `P_i ⊗ V` projective. `resolution M`
  is the standard resolution `⊕_(a : i → j) P_j ⊗ M_i ⟶ ⊕_i P_i ⊗ M_i ⟶ M` with the signs
  `u ↦ u - M(a) u`; it splits at every vertex (`resolutionSplitting`) and is short exact
  (`resolution_shortExact`). Hence `enoughProjectives_diagram`, `hasProjectiveDimensionLT_two`
  and `ext_eq_zero` for `Ext^m` with `2 ≤ m`. Fixtures in
  `TDA.Sheaf.AlternatingHeredityExamples` resolve `[0, 2]` on the fork and use `Ext² = 0`.
- Perturbation stability of interval singular homology (#1173):
  `TDA.Reeb.intervalSingularHomologyInterleaving` gives, for `f g : C(X, ℝ)` with
  `∀ x, |f x - g x| ≤ ε`, an `ε`-interleaving of `intervalSingularHomology k n f` and
  `intervalSingularHomology k n g` in every degree and over every ring, built with `Interleaving.ofApp`
  from singular homology applied to `perturbationInclusion` and its swapped-bound reverse, with
  `_self`, `_symm`, `_mono` and `_trans` laws. `interleavingDistance_intervalSingularHomology_le` and
  `_le_edist` give the radius and extended supremum bounds. In degree zero the witness is the existing
  path-component witness, linearized (`linearizedPerturbationInterleaving`) and conjugated by
  `intervalSingularHomologyIso₀` (`intervalSingularHomologyPerturbation_zero`). Fixtures in
  `TDA.Reeb.IntervalSingularHomologyStabilityExamples`: an empty source, parameter `0`, empty
  preimages, and constant maps from a point at heights `a` and `b`, at distance exactly `|a - b|`
  (`interleavingDistance_const`), over a nontrivial ring.
- Coordinate Alexandrov translations (#1169): on `upperSpace (Fin n → ℝ)` with the product order,
  for every `n`, `TDA.Sheaf.AlexandrovCoordinateTranslation.sheafShift C ε` is
  `TopCat.Sheaf.pushforward` along `translate ε : x ↦ x - ε · 1`, whose preimage of `U` is the
  image of `U` under `CoordinateShift.translation ε` and sends `↑a` to `↑(a + ε · 1)`, proved
  coordinatewise. `sheafShiftLE`, `sheafTransition`, `sheafZeroIso`, `sheafCompIso` and
  `sheafCongrIso` are restrictions along preimage opens; `shiftComparison R ε` identifies them
  under `coordinateSections` with `CoordinateShift.shiftLE`, `transition`, `zeroIso` and
  `compIso`. `SheafInterleaving.equivCoordinateInterleaving` is an equivalence with
  `CoordinateInterleaving` witnesses of the principal sections, `SheafInterleaving.equivUpperSet`
  with witnesses of `M` and `N` for the attached sheaves, and `sheafInterleavingDistance_eq`
  equates the sheaf distance with `coordinateInterleavingDistance`. The restriction identities
  `presheaf_map_eq`, `presheaf_map_comp_map`, `presheaf_map_comp_map_eq`,
  `presheaf_map_comp_map_eq_comp` and `restrictIso` are shared in `TDA.Sheaf.PresheafRestriction`
  by both translation modules, and `TDA.Sheaf.AlexandrovTranslation.SheafInterleaving.equivUpperSet`
  identifies line witnesses of attached sheaves with `RealInterleaving ε M N`. Fixtures in
  `TDA.Sheaf.AlexandrovCoordinateTranslationExamples`: for `n = 0` the shift is the identity and
  the distance is `0` for isomorphic sheaves or modules and `∞` otherwise; for `n = 1` pushforward
  along the homeomorphism `upperSpace (Fin 1 → ℝ) ≃ₜ upperSpace ℝ` carries witnesses bijectively,
  and the square with `CoordinateRealBridge.interleavingEquiv` commutes (`line_square`), with
  equal distances; for `n = 2` the upper set `{x | s < x₀ ∧ s ≤ x₁}` moves to `s + ε`, and
  `(ε, c)` with `0 < ε ≤ c` leaves it while the second coordinate stays at `c`.
- Release-snapshot API docs (#1203, #852): the hosted `docs` job is removed from
  `.github/workflows/ci.yml`; it never succeeded on the hosted runner. API pages are built with
  `scripts/build-docs.sh` at release snapshots in a proven local or self-hosted container, with
  recorded provenance (tag and source SHA, pins, checksum and size, storage and retention,
  navigation, search and source-link checks); this is not a mandatory release gate, and no
  hosting endpoint is chosen. The `check` job, the Pages site and the `release_check` input are
  unchanged. `CONTRIBUTING.md` and the orchestration skill add the merge-time Issue closure
  procedure (#1195 D-10), and `docs/math/references.md` registers four sheaf-roadmap arXiv
  versions as background with the source policy of #1170.
- Real Alexandrov and upper ray sheaves (#1177): `TDA.Sheaf.RaySheaf` puts the ray topology on
  `raySpace := TopCat.of (WithUpper ℝ)` (basis `ray t = (t, ∞)`, open sets the ordinary open
  upper sets by `isOpen_ofUpper_preimage_iff`). `rayQ` is the Alexandrov sheaf pushed forward
  along the continuous identity `rayId`, and `rayB` reads `F(ray t)`. `rayLimitIso` identifies
  `BQ(M)(t)` with `lim_{s > t} M(s)` with projections `rayProj`; `rayUnit` is the unit and
  `rayCounitIso : rayB ⋙ rayQ ≅ 𝟭` uses the ray cover of each open. `rayShift`, `rayTransition`
  and `rayCompIso` match `sheafShift` and `RealShift.shift` at the same radius
  (`rayShiftComparison`); `RaySheafInterleaving` witnesses transport along `B` and `Q`.
  For `ε > 0`, `unitInterleaving` is an `ε`-interleaving of `M` and `BQ(M)`, and
  `raySheafInterleavingDistance_rayQ` and `realInterleavingDistance_rayB` equate extended
  distances; `isZero_rayQ_iff` characterises `Q M = 0` by vanishing strict maps. Fixtures in
  `TDA.Sheaf.RaySheafExamples`: the empty open, a singleton module at distance zero from
  `BQ` without a radius-zero witness, and the constant module.
- Stratifications of the real line in `TDA.Sheaf.RealStratification` (#1181, foundation): for
  strictly increasing `p : Fin m → ℝ`, `orient m` points every arrow of the path on `2m + 1`
  strata from a point to an adjacent cell, and its free category is thin
  (`paths_hom_subsingleton`). `IsBasicOpen S U` (nonempty, order-connected, open, meeting `S` in
  at most one point) gives a basis (`isBasis_basicOpen`, `isBasis_range_basicOpen`) closed under
  nonempty intersections (`IsBasicOpen.inf`), with `BasicCat`, `basicIncl` and
  `basicTopology`. Stars `star p v` and strata `tau p U` (`tau_eq_iff`) satisfy the laws of
  `exists_star_tau` and give the functor
  `tauFunctor hp : (BasicCat (breakpoints p))ᵒᵖ ⥤ Paths (Vertex (orient m))`
  (`isIso_tauFunctor_map`). `isSheaf_basic_of_isIso_sameStratum`: a presheaf on basic opens, in
  any category, that inverts every inclusion with the same breakpoints is a sheaf for
  `basicTopology S`; so is `tauFunctor hp ⋙ M` (`isSheaf_tauFunctor_comp`). `basisEquiv S k` is
  Mathlib's comparison equivalence for this basis with `ModuleCat.{0} k`. Fixtures in
  `TDA.Sheaf.RealStratificationExamples`: zero breakpoints, the stars and strata of
  `0 ← 1 → 2`, the constant presheaf, and the point diagram extended to the real line with
  sections of dimension one over `(-1, 1)` and zero over `(1, 2)`.
- Algebraic core of singular Mayer–Vietoris (#1190, part S1), in `TDA.Topology`: small singular
  chains of two arbitrary subsets (`TDA.Topology.SmallChains`: `simplicesIn`,
  `mem_simplicesIn_iff`, `simplicesIn_inter`, `smallSimplices`, `mem_smallSimplices_iff`,
  `smallChains`, `smallChainsι`, `singularChainsSubsetIso` and, for embeddings,
  `range_toSSet_map_eq_simplicesIn`); in `TDA.Topology.SingularMayerVietoris`, the pushout of
  chain complexes of a bicartesian square of subcomplexes (`isPushout_chainComplex`), the reducible
  short complex `mvShortComplex` with maps `(t, -l)` and the sum, `shortExact_mvShortComplex` and
  `shortExact_smallChains` in any abelian category with coproducts, the connecting map `bicartδ`
  with its sign `bicartδ_eq` (the class of `a + b` goes to the class of the chain with image `∂a`
  in the first piece), `bicartδ_flip` (swapping the pieces negates it) and `bicartδ_naturality`;
  and in `TDA.Topology.QuasiIsoOfIterate`, `quasiIso_of_iterate_mem`, which proves that a
  monomorphism of complexes of modules over a ring is a quasi-isomorphism when a homotopic
  endomorphism `S ≃ 𝟙` and its homotopy preserve the subcomplex and every chain is carried into
  it by some iterate of `S`. Fixtures in `TDA.Topology.SingularMayerVietorisExamples` cover two
  rays covering `ℝ`, a segment that is not small, the flip sign over `ℚ` and contractible
  complexes.
- Lean thread default (#1240): an unset or empty `LEAN_NUM_THREADS` is no longer replaced by `1`;
  `scripts/lean.sh` and the other guarded entry points leave it unset, so Lean uses its own
  default (all hardware threads), as `uda-lab/reeb-ordering` already does. An explicit positive
  value is still kept exactly and an invalid one rejected. Start-up lines and session briefs report
  `all (lean-default; N detected)` or `N (explicit; N detected)`. Hosted CI's `check` job now sets `2`
  explicitly (it had been running at the fallback `1`); the cloud setup script keeps `1`.
- Flasque sheaves and section lifting on compact intervals (#1226, parts U1 and U2):
  `TDA.Sheaf.SheafFlasque` proves that injective sheaves of `k`-modules are flasque
  (`isFlasque_of_injective`), introduces `GermSurjective` with `germSurjective_of_isFlasque`,
  `germSurjective_of_injective` and `germSurjective_of_epi`, and gives local preimages along
  exact complexes (`exists_local_preimage_of_exact`). `TDA.Sheaf.IntervalSections` proves the
  extension step for order-connected `S ⊆ ℝ` (`exists_section_lift_extend`, on the opens
  `openIoo S p q`), the lifting of locally liftable global sections on `[u, v]` along an exact
  complex with germ-surjective first term (`exists_section_lift_Icc`) and exactness of global
  sections on `[u, v]` (`sections_exact_Icc`). Fixtures in `TDA.Sheaf.IntervalSectionsExamples`.
- Affine chains and the subdivision diameter bound (#1190, part S2): `TDA.Topology.AffineChains`
  makes the vertex tuples `Fin (n + 1) → X` a simplicial set `affineSSet X`, so its chain
  complex has Mathlib's alternating face differential. The cone `coneMap R b n` puts the apex
  `b` at vertex `0`; `coneMap_d` proves `∂(b · c) = c - b · ∂c` in positive degree and
  `coneMap_zero_d` proves `∂(b · c) = c - ε(c) · b` in degree zero, for coefficients `R` in any
  preadditive category with coproducts. For a convex `K` in `StdSimplex ℝ (Fin (m + 1))`,
  `realize hK σ` is the affine realization (its cone is `AffineMap.cone`, `coe_realize_cons`),
  and `toSingular hK Y e` and `toSingularChains hK Y e R` send affine simplices and chains to
  singular ones through `e : C(K, Y)` (a monomorphism for injective `e`). In
  `TDA.Topology.SubdivisionDiameter`, `IsSubdivisionSimplex hK σ τ` describes the simplices of
  `sd(σ) = b_σ · sd(∂σ)` and `IsIteratedSubdivisionSimplex` their `N`-fold iterates; measured
  through any linear map of the weights into a real normed space, a subdivision simplex lies in
  `σ` and has diameter at most `n / (n + 1)` times that of `σ`, and `(n / (n + 1)) ^ N` after
  `N` steps. Fixtures in `TDA.Topology.AffineChainsExamples`: the cone boundary on a segment
  over any ring and the factor `2 / 3` on the standard `2`-simplex.
- Downstream-use audit, family 1 (#1245, #1207): for finite Čech diagrams,
  `Cech.dgm_eq_of_linearOrder` (independence of the label order) and the threshold forms
  `Cech.exists_lt_dist_of_ofReal_lt_bottleneck_dgm` and
  `Cech.lt_hausdorffDist_of_ofReal_lt_bottleneck_dgm`; the downstream regression fixture
  `CechClientExamples`.
- Singular barycentric subdivision (#1190, part S3): `TDA.Topology.AffineSubdivision` defines the
  subdivision chain map `affineSubdivision hK R` on affine chains of a convex subset of a standard
  simplex (`sd(σ) = b_σ · sd(∂σ)`, identity in degree `0`) and its homotopy to the identity
  `affineSubdivisionHomotopy hK R` (`T(σ) = b_σ · (sd(σ) - σ - T(∂σ))`), both natural in affine
  maps, with `d_comp_augmentation` and the generic `chainHomotopyOfSucc`; the subdivision of `σ`
  is an integer combination of `IsSubdivisionSimplex` simplices
  (`ιChainComplex_affineSubdivision_mem_closure`, `comp_affineSubdivision_mem_closure`).
  `TDA.Topology.SingularSubdivision` defines `singularSubdivision R X`, sending a singular simplex
  `σ` to `σ_*` of the subdivision of the model simplex `idSimplex n`, natural in `X`
  (`singularSubdivision_naturality`, `singularSubdivisionNatTrans`) and compatible with `e_*` for
  every continuous `e` from a convex set (`toSingularChains_comp_singularSubdivision`), and the
  natural homotopy `singularSubdivisionHomotopy R X` to the identity. Both preserve the small
  chains of two subsets (`exists_singularSubdivision_f_lift`,
  `singularSubdivision_f_apply_mem_range_smallChainsι`,
  `singularSubdivisionHomotopy_hom_apply_mem_range_smallChainsι`). `toSingularChains` now targets
  `(TopCat.toSSet.obj Y).chainComplex R`. Fixtures in
  `TDA.Topology.SingularSubdivisionExamples`: the two signed half-segments of a singular segment,
  its boundary and a naturality instance.
- Cohomology of compact intervals (#1226, parts U3 and U4): `TDA.Sheaf.StalkPullback` gives the
  stalk of a sheaf inverse image (`stalkPullbackSheafIso`) and its compatibility with the
  adjunction unit (`stalkPullbackSheafIso_unit`); `TDA.Sheaf.PointSheaf` introduces `pt`, `toPt`,
  the constant sheaf `constSh` and `germSurjective_constSh`, with sheaves on the point read on
  global sections; `TDA.Sheaf.RightDerivedHomology` reads right derived homology off injective
  complexes (`homologyRightDerivedIsoOfInjective`, `homologyRightDerivedIsoOfQuasiIso`).
  `TDA.Sheaf.IntervalCohomology` proves `Hⁱ([u, v]; G) = 0` for `2 ≤ i` and every sheaf `G`
  (`isZero_H_Icc`), `Hⁱ([u, v]; constSh N) = 0` for `1 ≤ i` (`isZero_H_constSh_Icc`) and, for
  `u ≤ v`, that the underived and derived units at `N` are isomorphisms
  (`isIso_unit_constSh_Icc`, `isIso_derivedUnit_toPt_Icc`). Fixtures in
  `TDA.Sheaf.IntervalCohomologyExamples`.
- Small chains compute singular homology (#1190, part S4): in `TDA.Topology.SmallChainsQuasiIso`,
  `quasiIso_smallChainsι s t M h` proves that small chains include quasi-isomorphically into all
  singular chains when `interior s ∪ interior t = Set.univ`, for coefficients in any module over a
  ring. The steps are a Lebesgue number for an open cover of the model simplex
  (`exists_isIteratedSubdivisionSimplex_subset`), the transfer to singular simplices
  (`exists_iterate_singularSubdivision_ιChainComplex_mem_range`) and finite support of chains
  (`iSup_range_ιChainComplex`, `exists_iterate_singularSubdivision_mem_range_smallChainsι`). The
  Mayer–Vietoris long exact sequence on `singularHomologyFunctor`: the connecting map
  `mayerVietorisδ`, the maps `mayerVietorisInterMap` (`(inc, -inc)`) and `mayerVietorisSumMap`, the
  vanishing composites and exactness at the three spots (`mayerVietoris_exact_inter`,
  `mayerVietoris_exact_sum`, `mayerVietoris_exact_space`). Fixtures in
  `TDA.Topology.SmallChainsQuasiIsoExamples`: the two open rays of `ℝ`, the eventually small
  subdivisions of a non-small segment and a Lebesgue step on the `1`-simplex.
- Interval-local constancy on the real line (#1181, part L1): `TDA.Sheaf.LocalSystem` defines
  `IsLocallyConstantOn F U` for sheaves of `k`-modules on `realLine` (restriction between nested
  nonempty convex opens near each point is an isomorphism), with `IsLocallyConstantOn.mono`. Its
  intended equivalence with "locally isomorphic to a constant sheaf" is not yet proved in Lean
  (follow-up #1250). `restrict_isIso_of_isLocallyConstantOn`: on a convex open `W` where `F` is
  locally constant, `F(W) ⟶ F(V)` is an isomorphism for every nonempty convex open `V ⊆ W`.
  Corollaries: the transport isomorphism `transportIso` (`map_comp_transportIso_hom`,
  `transportIso_hom_eq_map`, `transportIso_trans`), germ isomorphisms `isIso_germ_of_isIso_map`
  and `isIso_germ_of_isLocallyConstantOn`. In `TDA.Sheaf.RealStratification`:
  `isIso_map_basisEquiv` and `isBasicOpen_empty`. Fixtures in `TDA.Sheaf.LocalSystemExamples`: the constant sheaf is locally constant on `ℝ`
  (`isLocallyConstantOn_constLineSheaf`, `isIso_constLineSheaf_map_ioo`,
  `finrank_stalk_constLineSheaf`); the point sheaf is locally constant on `(0, ∞)`
  (`isLocallyConstantOn_pointLineSheaf_Ioi`, `finrank_stalk_pointLineSheaf_right`) but not on `ℝ`
  (`finrank_pointLineSheaf_wide`, `not_isLocallyConstantOn_pointLineSheaf_univ`).
- Flasque acyclicity for sheaves of modules (#1225, part A): `TDA.Sheaf.FlasqueAcyclic` proves,
  for sheaves of `k`-modules, that a short exact sequence with flasque kernel is surjective on
  sections over every open (`epi_of_shortExact`, Mathlib's Zorn argument; with
  `sections_exact_of_left_exact`), that the quotient of a flasque sheaf by a flasque
  subsheaf is flasque (`isFlasque_of_shortExact`), that `f_*` keeps such sequences short exact
  (`pushforward_shortExact_of_isFlasque`), bounded below acyclic flasque complexes acyclic
  (`acyclic_pushforward_of_isFlasque`) and quasi-isomorphisms of bounded below flasque complexes
  quasi-isomorphisms (`quasiIso_pushforward_of_isFlasque`), and that the comparison
  `f_* K ⟶ Rf_* K` on `D⁺` is an isomorphism for every bounded below complex of flasque sheaves
  (`isIso_rightDerivedFunctorPlusUnit_app_of_isFlasque`, and
  `isIso_rightDerivedFunctorPlusUnit_app_toPt_of_isFlasque` for global sections); flasqueness is closed under isomorphisms, zero objects and biproducts. The
  section-gluing helpers of `TDA.Sheaf.IntervalSections` are now public in
  `TDA.Sheaf.SheafFlasque` (`presheaf_map_map_apply`, `sheafHom_naturality_apply`,
  `shortComplex_g_f_apply`, `exists_glue₂`), and `isIso_Q_map_comp_rightDerivedFunctorPlusUnit`
  is public in `TDA.Sheaf.RightDerivedHomology`. Fixtures in
  `TDA.Sheaf.FlasqueAcyclicExamples`.
- Constructible sheaves on the real line and finite alternating diagrams (#1181, D1):
  `TDA.Sheaf.RealConstructible` defines `IsConstructible S F` (local constancy on `(↑S)ᶜ` in the
  interval-local sense `IsLocallyConstantOn`, and finite-dimensional stalks; the intended
  equivalence with "locally isomorphic to a constant sheaf" is not yet proved in Lean, #1250)
  and proves `isIso_res_sameStratum` (same-stratum inclusions of basic opens are inverted) and
  `isConstructible_iff`. The section functor `sections` (via `starFunctor`) satisfies
  `sections_obj_obj` and `sections_map_gen`; the extension functor `extension` (via
  `basisSheaf`) has `extensionBasicIso`, `extensionStarIso` and `isConstructible_extension`,
  and `finiteDimensional_sections` holds. The counit `extensionSectionsIso`
  (`extensionSectionsIso_app_app`) and the unit `sectionsExtensionIso` give
  `equivalence : Constructible k p ≌ FinDiagram k m` through `sectionsFin` and `extensionFin`
  (`equivalence_functor_obj_obj`, `equivalence_functor_obj_map_gen`, `equivalence_inverse_obj_obj`). The binary gluing step
  `TDA.Sheaf.LocalSystem.isIso_map_of_le_sup` is now public. Fixtures in
  `TDA.Sheaf.RealConstructibleExamples`: no breakpoints (`p₀`, `p₀_strictMono`,
  `breakpoints_p₀`, `star_p₀`, `isConstructible_p₀_iff`, `sections_p₀`,
  `nonempty_iso_of_iso_top`, `constSheaf₀`, `isConstructible_constSheaf₀`,
  `finrank_constSheaf₀_top`); one breakpoint (`arrow_one_zero`, `arrow_one_two`,
  `intervalSheaf`, `isConstructible_intervalSheaf`, `sectionsIntervalSheafIso`,
  `finrank_intervalSheaf_star`, `not_isIso_intervalSheaf_map`, `segLeft`, `segRight`,
  `leftClosed`, `rightClosed`, `pointSheaf`, `finrank_leftClosed`, `finrank_rightClosed`,
  `not_isIso_leftClosed_right`, `not_isIso_rightClosed_left`, `not_isIso_pointSheaf`); Mathlib's
  skyscraper (`sky`, `skyObjIso`, `isZero_sky_obj`, `isConstructible_sky`, `sectionsSkyIso`,
  `skyIsoPointSheaf`). The derived comparison is out of scope (#1183).

## v0.5.0

Published 2026-11-25. [Release notes](https://github.com/uda-lab/tda-lib/releases/tag/v0.5.0)
· [Versioned API guide](https://github.com/uda-lab/tda-lib/blob/v0.5.0/docs/api.md).

- Add rationally graded simplicial input and its generated F₂ grid
  representation (`TDA.Persistence.F2GridHomologyInput`): decidable validation,
  sublevel slices in the reduction input format, and a generated `F2GridRep`
  proved valid for every valid input. See
  [rank erosion](docs/math/rank-erosion.md#executable-representations-over-the-two-element-field).
- Prove that the generated F₂ grid representation computes the homology
  (`TDA.Persistence.F2GridHomologyIso`): its Kan extension is canonically
  isomorphic to the actual homology, so generated dimensions, executable ranks
  and rank erosion between two generated representations are those of the actual
  modules. The private Kan-comparison helpers of `FiniteSimplicialPresentation`
  are now public as `CoordinateGrid.kanComparison`, `kanComparison_fac`,
  `kanInclusion_kanComparison`, `kanComparisonIso` and `kanComparisonIso_hom`,
  and `RankErosion` gains `rankErosion_iff_of_iso` and
  `rankErosionDistance_eq_of_iso`. See
  [rank erosion](docs/math/rank-erosion.md#executable-representations-over-the-two-element-field).
- Add the end-to-end erosion test of two rationally graded complexes
  (`TDA.Persistence.F2GridHomologyErosion`): `RatGradedInput.runErosion` reports
  an invalid first or second input or a negative radius separately, and its pass
  and failure are certified for the actual homology modules, including the
  failure's direction, grade pair and exact ranks. Worked example: a triangle
  against its translate by `(1/2, 0)` fails at radius 0 and passes at radius
  1/2, proved rather than evaluated. See
  [testing two rationally graded complexes](docs/math/rank-erosion.md#testing-two-rationally-graded-complexes).
- Add the semantic layer of acyclic matchings for discrete Morse reduction
  (`TDA.Persistence.Morse.AcyclicMatching`): matchings and the modified Hasse
  diagram on all faces, acyclicity proved equivalent to the Mischaikow–Nanda
  Def. 2.2 form, topological ranks for finitely many faces, and filtered acyclic
  matchings for sublevels proved equivalent to acyclic matchings with equal
  grades. See
  [acyclic matchings](docs/math/discrete-morse-matchings.md).
- Check supplied acyclic matchings on finite inputs
  (`TDA.Persistence.Morse.FiniteInputMatching`): `MatchingInput.check` accepts
  exactly an equal-grade list-level matching with a topological rank. For a valid input,
  some rank is accepted exactly for a duplicate-free filtered acyclic matching.
  `CertifiedMatching` reports the critical faces with their dimension and original grade. See
  [checking a supplied matching](docs/math/discrete-morse-matchings.md#checking-a-supplied-matching).
- Generate certified same-grade matchings on finite inputs greedily
  (`TDA.Persistence.Morse.FiniteInputMatchingGeneration`): `MatchingInput.generate`
  is a total `CertifiedMatching` built by one pass over the same-grade cover pairs
  in lexicographic order, so the checker accepts its output and, for a valid
  input, it is a filtered acyclic matching; reduction fixtures cover a tree, a
  filtration barrier, the hollow and the filled triangle and a multi-grade square. No
  maximality or optimality is claimed. See
  [generating a matching greedily](docs/math/discrete-morse-matchings.md#generating-a-matching-greedily).
- Cancel one equal-grade unit pair of a filtered based complex
  (`TDA.Persistence.Morse.UnitCancellation`): an executable reduced differential,
  projection, inclusion and homotopy over any commutative ring, with `d'² = 0`,
  both chain-map equations and `1 - i p = D H + H D` for a unit pair
  (`a ≠ b`, `D a b = 1`) of a square-zero `D`, `p i = 1` from `a ≠ b` alone, and all
  four maps grade-nonincreasing for equal grades. See
  [unit cancellation](docs/math/discrete-morse-cancellation.md).
- Bundle filtered contractions of based complexes
  (`TDA.Persistence.Morse.FilteredContraction`): computable projection, inclusion and homotopy
  matrices with chain-map, homotopy, side-condition, degree and grade fields, composition
  (`trans`), transport of the small complex along a carrier equivalence (`reindex`),
  restatement along equalities (`copy`) and the unit-pair instance (`ofUnitPair`);
  `D' * D' = 0` follows from `D * D = 0`, and the based and filtered differential properties
  transfer to the small complex. Fixtures compose two cancellations on the filled triangle by
  `decide +kernel`. See
  [filtered contractions](docs/math/discrete-morse-cancellation.md#filtered-contractions-and-their-composition).
- Form grade-sublevel homology of filtered based complexes as persistence modules over `ℤ`
  (`TDA.Persistence.Morse.FilteredHomology`): degree-`p` cycles in grades `≤ t` modulo the
  boundaries of degree-`p + 1` chains in grades `≤ t`, with no hypothesis on the matrix, and
  the natural isomorphism `sublevelHomologyIso` of these persistence modules induced by the
  projection of a filtered contraction, with equal `Module.finrank`, without assuming
  `D * D = 0`. Fixtures over `ZMod 2` transport the dimensions of the critical complex of the
  regraded filled triangle to the triangle. See
  [sublevel homology](docs/math/discrete-morse-cancellation.md#sublevel-homology-and-the-induced-isomorphism).
- Iterate unit cancellation along a supplied pivot schedule
  (`TDA.Persistence.Morse.IteratedCancellation`): `IsPivotSchedule` asks for distinct
  endpoints, unit equal-grade pairs and that no lower generator is a face of a later upper
  generator, and is preserved by cancelling the head pair; `criticalDifferential` is an
  executable reduced differential on the critical generators, and `FilteredContraction.ofSchedule`
  is the composed filtered contraction onto it. Fixtures evaluate the multi-grade square and
  the regraded filled triangle by `decide +kernel`. See
  [iterated cancellation](docs/math/discrete-morse-cancellation.md#iterated-cancellation-along-a-pivot-schedule).
- Derive the pivot schedule of a certified matching on a valid input
  (`TDA.Persistence.Morse.MatchingSchedule`): over `ZMod 2` the finite-input boundary is the
  cover incidence, `CertifiedMatching.schedule` sorts the certified pairs stably by the rank of
  the lower face, and `isPivotSchedule_schedule` proves that it is a pivot schedule for the
  boundary. `CertifiedMatching.morseDifferential` is the executable Morse differential on the
  critical positions, `CertifiedMatching.morseContraction` the filtered contraction of the
  boundary complex onto it, and `CertifiedMatching.morseHomologyIso` the induced isomorphism of
  grade-sublevel homology persistence modules. Fixtures evaluate three certificates on the
  multi-grade square, including a tie in the rank, by `decide +kernel`. See
  [the pivot schedule of a certified matching](docs/math/discrete-morse-cancellation.md#the-pivot-schedule-of-a-certified-matching).
- Bridge the Morse complex of a certified matching to simplicial persistence
  (`TDA.Persistence.Morse.SimplicialBridge`): for a valid finite input,
  `SimplicialBridge.boundaryHomologyIso` is a natural isomorphism from the grade-sublevel
  homology persistence module of its boundary complex to its simplicial sublevel persistence
  module `sublevelModule (ZMod 2) (gradeFilter xs h) p`, and for a certified matching
  `CertifiedMatching.morseSublevelModuleIso` is the natural isomorphism from that simplicial
  module to the persistence module of the Morse complex, with equal dimensions and
  structure-map ranks. Fixtures on the multi-grade square prove the sublevel homology
  dimensions of its Morse complex and of its simplicial sublevels, and that its degree-1
  diagram `dgm` is `{(1, 2)}`. The bridge does not construct an interval decomposition of these
  integer-indexed persistence modules. See
  [the simplicial bridge and the Morse persistence theorem](docs/math/discrete-morse-cancellation.md#the-simplicial-bridge-and-the-morse-persistence-theorem).
- Order the generators of a filtered based complex for the column reducer
  (`TDA.Persistence.Morse.ReducerOrder`): the key (grade, degree, generator) is injective and
  increases along every nonzero entry of a filtered differential, `sortedGenerators` sorts the
  carrier by it with a computable insertion sort, `reducerEquiv` is the resulting enumeration
  by `Fin`, and over a field `reducerMatrix` is strictly upper triangular and lowers the
  transported degree, so `matrixReductionTrace_normalForm_input` applies to it
  (`reducerMatrix_normalForm_input`). Fixtures R1 (the tie-order cancellation F4), R2 (a path
  with a certified matching whose inherited order fails strict triangularity) and R3 (the
  multi-grade square with the certificates `sqCert` and `genCert`) evaluate the reducer
  orders by `decide +kernel`. See
  [the reducer order of a filtered based complex](docs/math/discrete-morse-cancellation.md#the-reducer-order-of-a-filtered-based-complex).
- Read the column reducer's output as a graded diagram and prove its rank semantics
  (`TDA.Persistence.Morse.ReducerDiagram`): over a field, for a square matrix on `Fin m` with
  degrees and integer grades, the builders `pivotPairs`, `essentialIndices`, `occurrences` and
  `diagram` are computable, and on a boundary matrix `occurrences` and `diagram` agree by `rfl`
  with `FiniteInput.occurrences` and `FiniteInput.outputDiagram`. `rankOfStructureMap_eq_countP`
  states that, for a square-zero, strictly upper triangular, degree-lowering matrix with
  monotone grades, the ranks of the grade-sublevel homology persistence module are the slice
  counts of `diagram`. For a filtered
  differential, `reducerDiagram` is the output on `reducerMatrix`, and
  `eq_reducerDiagram_of_rankCounts` states that it is the positive diagram whose slice counts
  are the ranks of the original complex. The uniqueness `Diagram.eq_of_sliceCounts_eq` holds
  over any linear order (`TDA.Persistence.DiagramRankUniqueness`) and now also proves
  `RealBarcode.multiset_eq_of_rankCounts_eq`. Fixtures P1–P3 (a hollow triangle and the
  reducer matrices of the path R2 and the square R3) evaluate the output by `decide +kernel`. See
  [the graded reducer output and its rank semantics](docs/math/discrete-morse-cancellation.md#the-graded-reducer-output-and-its-rank-semantics).
- Run the reducer on the Morse complex of a certified matching
  (`TDA.Persistence.Morse.MorseDiagram`): `morseOccurrences` and `morseDiagram` are the
  computable reducer output on `morseDifferential`. On a valid input, over `ZMod 2`,
  `morseDiagram_eq_dgm` states that the diagram is the sublevel diagram `dgm` of the input,
  `morseDiagram_eq_outputDiagram` that it is the diagram of the ordinary run on the boundary
  matrix, and `morseDiagram_eq_morseDiagram` that two certificates give the same diagrams;
  `morseOccurrences_perm` and `morseOccurrences_perm_of_run_eq_some` state that the occurrence
  list is a permutation of the output of `FiniteInput.run`. For a filtered differential over a
  field, `reducerDiagram_eq_of_linearOrder` and `reducerOccurrences_perm_of_linearOrder` state
  that the reducer output does not depend on the tie order of the reducer order, the occurrence
  list up to permutation. Fixtures Q1–Q6 run the square with `sqCert` and `genCert` (degree-1
  diagram `{(1, 2)}`, degree-0 diagram `{(0, ⊤)}`, occurrences equal to `FiniteInput.run square`),
  the path, the tie-order complex F4 and a reversed tie order by `decide +kernel`. No interval
  decomposition over `ℤ` and no runtime claim. See
  [the reducer run on the Morse complex of a certificate](docs/math/discrete-morse-cancellation.md#the-reducer-run-on-the-morse-complex-of-a-certificate).
- Add elementary collapses of simplicial complexes (`TDA.Simplicial.Collapse`: `IsFreePair`,
  `deletion`, `ElementaryCollapsesTo`, `CollapsesTo`) and verify a Čech-to-α collapse on the
  exact obtuse triangle (`TDA.Filtration.AlphaCollapseExamples`): for `4 ≤ t < 5` the long edge
  is a free face of the triangle in the squared-grade Čech stage and its deletion is the α
  stage; at every other grade the stages are equal, and no fixed set of faces gives every α
  stage from the Čech stage at the same grade. See
  [elementary collapses and the obtuse triangle](docs/math/discrete-morse-matchings.md#elementary-collapses-and-the-obtuse-triangle).
- Prove that collapses induce homology isomorphisms (`TDA.Simplicial.CollapseHomology`):
  deleting a free face is a chain homotopy equivalence whose forward map is the inclusion, so the
  inclusion of the end of a finite collapse sequence is an isomorphism of ordinary homology in
  every degree over every ring. Levelwise collapses between two filtrations make the inclusion
  morphism of their homology persistence modules a natural isomorphism
  (`TDA.Persistence.CollapsePersistence`). On the obtuse triangle this gives the α-to-Čech
  persistence isomorphism in every degree (`TDA.Persistence.CollapsePersistenceExamples`). See
  [homology of collapses](docs/math/discrete-morse-matchings.md#homology-of-collapses).
- Add a checker for supplied collapse sequences on finite face tables
  (`TDA.Simplicial.CollapseCertificate`): a certificate is a list of pairs `(σ, τ)`,
  `checkSteps` accepts it exactly when each pair is free in the current table and the final table
  is the supplied target, and acceptance is equivalent to `CollapsesTo` between complexes with
  those face tables (`collapsesTo_iff_exists_checkSteps`). Accepted and rejected certificates are
  evaluated by `decide +kernel` (`TDA.Simplicial.CollapseCertificateExamples`), and the actual
  Čech stage of the obtuse triangle at grade 4 collapses to its α stage through the checker
  (`TDA.Filtration.AlphaCollapseCertificateExamples`). The checker requires a supplied
  certificate. See
  [checking supplied collapse sequences](docs/math/discrete-morse-matchings.md#checking-supplied-collapse-sequences).
- Check supplied collapse certificates across the critical grades of a filtered pair
  (`TDA.Filtration.CollapseCertificateFamily`): for real-indexed filtrations with rational grade
  tables, `checkCertificates` checks one supplied sequence at every grade of either table, with
  exact endpoints, and acceptance gives a collapse at every real grade, including below the first
  grade and on the unbounded tail; conversely levelwise collapses have an accepted family.
  Acceptance makes the inclusion morphism of homology persistence modules a natural isomorphism
  in every degree over every ring (`TDA.Persistence.CollapseCertificatePersistence`). On the
  obtuse triangle the family removing the long edge at grade 4 is accepted, keeping the removal
  at grade 5 is rejected, and the resulting isomorphism is the α-to-Čech one
  (`TDA.Filtration.AlphaCollapseFamilyExamples`,
  `TDA.Persistence.CollapseCertificatePersistenceExamples`). See
  [certificates across critical grades](docs/math/discrete-morse-matchings.md#certificates-across-critical-grades).
- Define the closed squared-grade α filtration for embedded sites
  (`Alpha.complexFiltration`, #1077). In finite-dimensional real inner-product spaces
  `Alpha.isLeast_grade` gives the attained entrance grade and `Alpha.sublevel_eq_complex`
  identifies the closed stages. See [closed α stages](docs/math/alpha-filtration-and-signed-coverage.md#closed-cells-and-squared-entrance-grades).
- Compute the exact rational squared grades of feasible nonempty labelled faces for finite
  distinct rational planar sites (`RationalAlpha.gradedFaces`, #1082). The cast grade and
  sublevel theorems identify the reference with closed α at every real squared grade.
  See [exact rational grades](docs/math/alpha-filtration-and-signed-coverage.md#exact-grades-on-rational-planar-sites).
- Prove the same-label comparison `alphaH0Iso` in ordinary degree zero over a field for
  finite linearly ordered labels in a real normed vector space (#1091). Its α and squared
  Čech stages are empty below zero. See [degree zero](docs/math/alpha-filtration-and-signed-coverage.md#degree-zero-comparison-with-čech).
- Verify the exact rational planar `orient` and `incircle` predicates (#1102).
  `orient_zero_iff_collinear` characterizes zero orientation, and
  `incircle_circumsphere_signs` identifies the orientation-adjusted signs for a
  noncollinear triple. See [signed planar geometry](docs/math/alpha-filtration-and-signed-coverage.md#signed-coverage-of-a-certified-planar-hull).
- For injective rational sites contained in a certified strict hull with an injective
  cycle, `rational_cover_from_signed_boundary` takes a finite CCW triangle family
  with the same signed edge chain as the hull (#1110). It gives closed hull coverage
  and the exact off-edge multiplicity. See [signed coverage](docs/math/alpha-filtration-and-signed-coverage.md#signed-coverage-of-a-certified-planar-hull).
- Produce the hull certificate from rational orientations and cover a hull whose sides are
  subdivided (#1157, #1162, #1164). `hull_polygonCertificate_hullOnly` gives the
  `PolygonCertificate` of a hull cycle from noncollinearity of triples of distinct hull
  positions and the real interior, frontier and left-support hypotheses. For a finite label
  type, `cornerHullCheck` decides `StrictCornerCycle` (every nonincident corner strictly left
  of each directed side) and `HullSitesLeft` (every site weakly left of each side);
  `cornerHullCheck_true_iff` identifies acceptance with a strict corner cycle whose hull
  contains every site, and `cornerHullCheck_sound` gives the certificate
  (`rational_corner_certificate`) and the equality of the corner hull with the convex hull of
  all sites (`siteHull_eq_all_sites`). The weak test accepts a site on a hull side that is not
  a corner (`HullCertificateExamples.midpoint_accepted`).
  `rational_cover_from_subdivided_signed_boundary`
  (`TDA.Filtration.RationalAlpha.SubdividedBoundaryCoverage`) takes the certificate of the
  coarse cycle, cuts on each side satisfying `OrderedEdgeCuts`, CCW triangles with vertices in
  the hull, and equality of the triangle chain with the chain of the subdivided boundary; it
  gives closed hull coverage and the off-edge multiplicity. See
  [signed coverage](docs/math/alpha-filtration-and-signed-coverage.md#signed-coverage-of-a-certified-planar-hull).
- Describe the incidences of a signed-boundary triangle family
  (`TDA.Filtration.RationalAlpha.TriangleIncidence`, `DirectedEdgeIncidence` and
  `TriangulationAssembly`; #1117, #1120, #1123). For injective rational sites, an injective
  certified hull cycle and CCW triangles with the hull's signed edge chain,
  `rational_edge_counts` gives each hull side one forward and no reverse triangle occurrence,
  and each other occurring pair one occurrence in each direction, in two different triangles.
  With every site in the hull and no three distinct sites collinear,
  `triangle_inter_eq_shared_labels_of_signed_boundary` identifies the intersection of two
  distinct closed triangles with the convex hull of their shared sites, and `certifiedComplex`
  assembles the nonempty subfaces `labelComplex` of the triangles into a mathlib
  `Geometry.SimplicialComplex` whose space is the hull (`certified_space_eq_siteHull`). See
  [signed coverage](docs/math/alpha-filtration-and-signed-coverage.md#signed-coverage-of-a-certified-planar-hull).
- Compute the exact α grades of supplied triangles and edges (`IncircleGrade`, `EdgeGrade` and
  `SuppliedEdgeGrade` under `TDA.Filtration.RationalAlpha`; #1125, #1127, #1129). For an
  embedding of rational planar sites and a CCW triangle, `checkIncircle` decides `incircle ≤ 0`
  at every site of a finite label type; `triangle_mem_actual_stage_iff` states that the
  triangle is in the closed α stage at `t` exactly when these inequalities hold and its
  squared circumradius is at most `t`, and `triangle_actual_grade` that the grade of a
  triangle of the α carrier is its squared circumradius. For two distinct sites,
  `edge_actual_grade_projection` gives the grade of a carrier edge as `D / 4 + D * z ^ 2`,
  with `D` the squared length and `z` a feasible parameter on the perpendicular bisector
  closest to the midpoint, and `edge_stage_of_parameter_min` the closed stage threshold.
  For an injective certified hull cycle and CCW triangles with the hull's signed edge chain
  and passing tests, `supplied_hull_dual` gives a `HullDual` for each hull side when every
  site is in the hull (its common cells are the closed outward ray from the circumcenter of
  the incident triangle) and `supplied_interior_dual` an `InteriorDual` for every other
  supplied edge (the segment between the two incident circumcenters), each with its exact
  stage threshold.
  `NoFourIncircleZeros` asks that the incircle determinant of every four distinct sites is
  nonzero, and `GeometricNoFourCocircular` that no point of the plane is equidistant from four
  distinct sites. See
  [signed coverage](docs/math/alpha-filtration-and-signed-coverage.md#signed-coverage-of-a-certified-planar-hull).
- Identify the α carrier, grades and stages of a certified supplied triangulation
  (`SuppliedCarrier`, `SuppliedGradeEnumeration` and `SuppliedStages` under
  `TDA.Filtration.RationalAlpha`; #1141, #1144, #1146). For sites `p : Fin n ↪ ℚ × ℚ`, the
  hypotheses are an injective hull cycle with a `PolygonCertificate`, every site in the hull,
  CCW triangles whose signed edge chain equals that of the hull cycle, a passing
  `checkIncircle` test for every triangle, and
  `GeometricNoFourCocircular p ∨ NoFourIncircleZeros p`; they do not include noncollinearity
  of distinct site triples. `carrier_eq_of_signed_boundary` states
  `Alpha.carrier (realSites p) = labelComplex tri`,
  `suppliedGrades_eq_reference` that the executable rows `suppliedGrades p tri` equal
  `gradedFaces p`, and `supplied_hasGradeTable` and `supplied_realStage_iff` that the faces of
  the rows of grade at most `t` are those of `Alpha.complex (realSites p) t` at every real `t`.
  The triangle chain is compared with the chain of the hull cycle itself, so every hull side is
  an edge of a supplied triangle. See
  [supplied carrier and stages](docs/math/alpha-filtration-and-signed-coverage.md#supplied-carrier-and-stages).
- Prove that small open thickenings keep the nerve of a finite compact family
  (`TDA.Topology.NerveThickening`). For finitely many compact sets in a metric space,
  `exists_pos_nerve_thickening_eq` gives `δ > 0` such that the open `ε`-thickenings have the
  nerve of the family for every `0 < ε ≤ δ`, and `exists_pos_common_nerve_thickening_eq` one
  such `δ` for two families. In a real normed space, `convex_thickening_of_iUnion_eq` states
  that the thickenings of two convex families with `C i ⊆ D i` and equal unions are open,
  convex and nested and have equal unions at every radius;
  `exists_pos_common_convex_thickening` combines both statements for finite compact convex
  families. See
  [realizations, subdivision mesh and convex nerves](docs/api.md#realizations-subdivision-mesh-and-nerves-of-nested-convex-families).
- Add the realization of a labelled simplicial complex and its coordinate stars
  (`TDA.Topology.Realization`): `Realization K` consists of the barycentric weights whose
  support is a face, and `coordinateStar K v` of the points with positive weight at `v`. The
  stars are open and cover the realization, and their nerve is `K` (`nerve_coordinateStar`).
  For a finite vertex type, the intersection of the stars of a face contracts to the
  barycenter of the face (`contraction`, `contractibleSpace_starIntersection`). An inclusion
  `K ≤ L` induces `Realization.incl`, which pulls stars back to stars
  (`pullback_coordinateStar`) and induces the inclusion on their nerves
  (`starNerveInclusion_naturality`). See
  [realizations, subdivision mesh and convex nerves](docs/api.md#realizations-subdivision-mesh-and-nerves-of-nested-convex-families).
- Realize iterated barycentric subdivisions and bound their mesh
  (`TDA.Topology.SubdivisionRealization`, `TDA.Topology.SubdivisionMesh`). For a finite vertex
  type, `complex K n` is the `n`-fold subdivision on labels that depend only on the vertex
  type, `realize p K n` interpolates the iterated barycenters of a placement `p` in a real
  normed space, and it factors through `barycentricProjection K n`
  (`realize_eq_comp_projection`), compatibly with inclusions of complexes
  (`projection_incl`). If every face of `K` has at most `d + 1` vertices and its placed
  vertices are pairwise within `M ≥ 0`, `diam_le` bounds the diameter of every realized face at
  depth `n` by `(d / (d + 1)) ^ n * M` and of every closed star by twice that, and
  `eventually_diam_lt` makes both smaller than a given `ε > 0` from some depth on. See
  [realizations, subdivision mesh and convex nerves](docs/api.md#realizations-subdivision-mesh-and-nerves-of-nested-convex-families).
- Prove that the nerve inclusion of nested convex families with equal unions induces a
  homology isomorphism (`TDA.Topology.ConvexNerveInclusion`). For a finite linearly ordered
  index type and families `C`, `D` of subsets of a real normed space with every `C i` open and
  convex, every `D i` convex, `C i ⊆ D i` and `⋃ i, C i = ⋃ i, D i`,
  `ConvexNerve.isIso_simplicialHomologyIncl` states that `nerve C ≤ nerve D` induces an
  isomorphism of simplicial homology in every degree over every ring.
  `ConvexNerve.isIso_simplicialHomologyIncl_of_compact` has the same conclusion when every
  `C i` and `D i` is compact and convex. The proof uses `TDA.Topology.SubdivisionLastVertex`
  (`isIso_iteratedLastVertex`), `TDA.Topology.NerveStarLabeling` (`exists_common_labeling`)
  and `TDA.Topology.ConeCarrierComparison` (`chainHomotopy_of_contiguous_after_lastVertex`).
  In `ConvexNerveInclusionExamples`, enlarging one of eight open boxes around a square hole
  gives a strict nerve inclusion that induces an isomorphism, with nonzero first homology over
  F₂; enlarging every box to the plane changes the union, and the inclusion is then not an
  isomorphism in degree one over F₂. See
  [realizations, subdivision mesh and convex nerves](docs/api.md#realizations-subdivision-mesh-and-nerves-of-nested-convex-families).
- Prove that the same-label α-to-Čech inclusion induces a natural persistence isomorphism in
  every degree over any ring (`TDA.Persistence.alphaCechIso`, module
  `TDA.Persistence.AlphaCech`), for a site function on a finite linearly ordered label type
  into a finite-dimensional real inner-product space. The five-point fixture
  `AlphaCechExamples.fivePointH1Square` tracks a nonzero F₂ cycle through a strict inclusion
  at squared grade 4 and the structure maps to grade 5. See
  [comparison with Čech](docs/math/alpha-filtration-and-signed-coverage.md#degree-zero-comparison-with-čech).
- Bound the bottleneck distance of radius-indexed α diagrams by the maximum matched-site
  displacement in every degree over a field
  (`TDA.Persistence.bottleneck_alphaRadiusDiagram_le_displacement`, module
  `TDA.Persistence.AlphaRadiusStability`), for two site functions on one finite linearly
  ordered label type into one finite-dimensional real inner-product space; the field lies in
  the universe of the label type. For squares with half-sides 7 and 8, the
  exact H₁ distance over F₂ is √2 on radii and 30 on squared grades
  (`AlphaRadiusStabilityExamples.square_bottlenecks`). See
  [radius displacement](docs/math/alpha-filtration-and-signed-coverage.md#exact-grades-on-rational-planar-sites).
- Add a task-oriented route through the rank-erosion guide and a list of what is
  not provided. See
  [choosing a result](docs/math/rank-erosion.md#choosing-a-result).
- Add erosion bounds for finite graded simplicial homology
  (`TDA.Persistence.FiniteSimplicialErosion`): a coordinatewise grade error
  `δ`, in particular `FiniteGraded.supGradeError`, is an admissible radius for
  `RankErosion` and `ERankErosion` and bounds both erosion distances; a failed
  erosion test at `ε` gives `ε < dE ≤ dI ≤ supGradeError`, with no
  caller-supplied presentation. See
  [rank erosion](docs/math/rank-erosion.md#finite-graded-simplicial-homology).
- Add the exact erosion distance of the uniformly translated tetrahedron-boundary
  family (`TDA.Persistence.FiniteSimplicialErosionTranslation`): erosion fails
  below `min |t-s| (1/2)` by actual surviving maps against zero fibers, so both
  erosion distances equal `min |t-s| (1/2)`, the interleaving distance; the
  radius `1/8` between the translates by `0` and `1/4` instantiates the
  failure certificate.
- Add the exact erosion distance of the coordinate-translated
  tetrahedron-boundary family
  (`TDA.Persistence.FiniteSimplicialErosionCoordinateTranslation`): erosion
  fails below `min (max |v 0 - u 0| |v 1 - u 1|) (1 / 2)` by actual surviving
  maps against zero fibers in one coordinate, so both erosion distances equal
  that value, which is the interleaving distance; the maximal grade error
  equals the coordinate gap, and a failing radius `1/8` with the gap attained
  in a negative coordinate instantiates the failure certificate. The rank
  helpers `one_le_rankOfStructureMap_of_ne_zero` and
  `rankOfStructureMap_eq_zero_of_isZero` are now public in
  `TDA.Persistence.FiniteSimplicialErosion`.
- Add the exact erosion distance of the scaled-translated tetrahedron-boundary
  family (`TDA.Persistence.FiniteSimplicialErosionScaledTranslation`): erosion
  fails below `min |t - u| (scaledLifetime s / 2)` by the actual surviving
  longer-arm map against a zero fiber, so both erosion distances equal that
  value, which is the interleaving distance; the maximal grade error equals
  the delay gap, and a failing radius `1/8` under an anisotropic scale, where
  the shorter arm does not witness the failure, instantiates the failure
  certificate.
- Add the exact erosion distance of the scaled tetrahedron-boundary module
  against zero (`TDA.Persistence.FiniteSimplicialErosionScaling`): erosion
  against the zero module fails below `scaledLifetime s / 2` by the actual
  surviving longer-arm map, so both erosion distances to zero equal
  `scaledLifetime s / 2`, which is the interleaving distance; a failing radius
  `1/8` under an anisotropic scale instantiates the finitely presented failure
  certificate.
- Add one-parameter consumers of the extended image rank
  (`TDA.Persistence.ERankQTame`): a real module is q-tame exactly when its
  strict structure maps, or those of its one-coordinate module, have finite
  extended rank; a real interleaving bounds the extended rank of a doubled-shift
  map by the middle fibre's extended dimension, so it is finite when that fibre
  is finite-dimensional; and a real interleaving gives extended-rank erosion of
  the one-coordinate modules, with the extended erosion distance at most the
  real interleaving distance. An example is q-tame but not pointwise
  finite-dimensional. See
  [rank erosion](docs/math/rank-erosion.md#one-parameter-q-tame-modules-and-real-interleavings).
- Add coordinatewise q-tameness (`TDA.Persistence.CoordinateQTame`), under the
  owner ruling on strictness: `PModule.CoordQTame` asks for finite-dimensional
  images of the structure maps that are strict in every coordinate, equivalently
  of every positive diagonal shift, and agrees with `PModule.QTame` for one
  coordinate; with no coordinate it is pointwise finite dimensionality. A
  coordinate interleaving bounds the extended rank of a doubled-shift map by the
  middle fibre's extended dimension, and maps with a gap above `2ε` in every coordinate have finite
  extended rank when the other module is coordinatewise q-tame. Erosion test
  domains are unchanged; an example is coordinatewise q-tame with an
  axis-parallel map of extended rank `⊤`. See
  [rank erosion](docs/math/rank-erosion.md#several-parameters-coordinatewise-q-tameness).
- Add weak-pair erosion on the extended image rank (`ERankErosion`) and its
  distance `eRankErosionDistance`. Monotonicity in the radius, reflexivity,
  symmetry, the triangle law and the bound by the coordinate interleaving
  distance hold for every module, without finite-dimensional fibers; on
  pointwise finite-dimensional modules the predicate and distance are
  `RankErosion` and `rankErosionDistance`. Examples show that without finite
  dimensionality neither predicate implies the other, and include an
  infinite-dimensional ephemeral module at extended distance `0` (not attained)
  or `⊤` (no coordinate) from zero. The statements are restricted to
  `PModule.{u,0,u}`. See
  [rank erosion](docs/math/rank-erosion.md#erosion-on-extended-ranks).
- Add the extended-natural image rank of a structure map
  (`eRankOfStructureMap`), the `Cardinal.toENat` of the cardinal rank: the
  dimension of the image when finite and `⊤` otherwise, so every infinite
  cardinal is collapsed to `⊤`. The composition and four-point inequalities,
  the zero, diagonal and isomorphism laws hold without finite-dimensional
  fibers. The `ℕ`-valued `rankOfStructureMap` is its truncation sending `⊤` to
  `0`, and the two agree on finite-dimensional images. Examples show that an
  infinite-dimensional constant module has the same `ℕ`-valued ranks as the
  zero module but extended rank `⊤`. See
  [rank erosion](docs/math/rank-erosion.md#extended-image-rank).
- Enclose Gaussian Gram sums and squared RKHS distances by rational arithmetic:
  for two lists of rational birth–death pairs, a rational bandwidth `σ`, a
  rational cap `0 ≤ c` and a rational tolerance `δ > 0`, `gramEnclosure` in
  `TDA.Persistence.Enclosure.Gram` is a rational interval containing the library
  `linearKernel` for the weight `capWeight c`, which is `min c (max 0 persistence)`
  as a `Weight 1 c`, and `sqDistEnclosure` is a rational interval containing
  `‖embedding σ w x - embedding σ w y‖ ^ 2`; both have width at most `δ` for
  all lists, including empty lists and zero total weight. `gramEnclosure?` and
  `sqDistEnclosure?` reject nonpositive `σ`, `c` and `δ`. The executed rational
  weight and exponent are identified with the library weight and kernel
  exponent, and `diagramEmbedding_eq_embedding_realPoints` transfers the
  statements to diagrams whose finite part is the list. The widths are
  absolute, an enclosure decides no equality, only the capped weight is covered
  and the cost is documented, not proved. See
  [Gram sums and the squared RKHS distance](docs/math/kernel-enclosure.md#gram-sums-and-the-squared-rkhs-distance).

- Enclose the exponential at nonpositive rational arguments by rational
  arithmetic: for rational `x ≤ 0` and `δ > 0`, `expEnclosure x δ` in
  `TDA.Persistence.Enclosure.Exp` is a rational interval containing
  `Real.exp x` (`expEnclosure_mem`) of width at most `δ` (`expEnclosure_width`).
  `expEnclosure?` rejects positive arguments and nonpositive tolerances. The
  argument is halved into `[-1, 0]`, a Taylor polynomial is bounded by mathlib's
  remainder estimate and the result is squared back with outward dyadic
  rounding. The width is absolute, not a relative error, and the lower endpoint
  can be `0`. The cost is documented, not proved. This is the scalar step
  of the Gaussian kernel enclosures in the entry above. See
  [Rational enclosures for Gaussian kernel values](docs/math/kernel-enclosure.md).

- Identify the diagram of the executed Rips simplex list with the Rips diagram:
  for a valid `DistanceTable`, `outputDiagram_ripsInput` states that
  `FiniteInput.outputDiagram` of the list, with integer grades read as real
  numbers, is `dgm (ZMod 2)` of `Rips.filter` for the table metric in every
  degree. At integer thresholds, `ripsLabelMap` induces an isomorphism from the
  homology of the Rips complexes to the sublevel homology of the list. `ripsRunInDegree`
  returns the records of one degree and `none` for an invalid table in every degree, and
  relabelled tables have equal diagrams. The new module
  `TDA.Persistence.SublevelDiagramVertexMap` proves `dgm_eq_of_vertexMaps`, the
  invariance of real sublevel diagrams under mutually inverse vertex maps
  between complexes on two vertex types. The four-cycle is a kernel-checked
  fixture with one class of degree one from `1` to `2`. This change proves
  no bound on the cost of the existing reduction. See
  [Diagram and homology of the Rips input](docs/math/finite-ph-computation.md#diagram-and-homology-of-the-rips-input).

- Execute the complete Rips simplex list of an integer distance table in the
  `FiniteInput` format: `DistanceTable`, its decidable `Valid`, `ripsInput`,
  `ripsInput?` and `ripsRun`. `Valid` asks for an integer metric with distinct
  points: nonnegative entries, symmetry, zero diagonal, positive distance
  between distinct labels and every triangle inequality. `ripsInput?` and
  `ripsRun` return `none` for every other table, including tables with
  repeated points or a failed triangle inequality. The
  list is ordered by grade, cardinality and label order, satisfies
  `FiniteInput.Valid`, and its faces and grades are identified with
  `Rips.fullComplex` and `Rips.filter` for the table metric. The list costs
  `O(N² 2 ^ N)` operations; the cost of the existing reduction is separate. See
  [Rips input from an integer distance table](docs/math/finite-ph-computation.md#rips-input-from-an-integer-distance-table).

- Identify each finite-input image structure-map rank with the range dimension
  of the induced simplicial map between sampled sublevels, for global vertex
  maps on monotone integer observations with repeated or negative thresholds
  and collapsed faces allowed. See
  [sampled image persistence](docs/api.md#persistent-homology-results-and-computational-boundary).
- Make the finite discrete interval constructors and `barcodeModuleOfList`
  executable with natural-endpoint decidability instead of classical
  decisions, including in the `List.Perm.idxBij` route that realizes
  repeated intervals at separate coordinates. See
  [executing finite interval and list-barcode modules](docs/math/constructive-finite-intervals.md).
- Compute certified sampled image-persistence barcodes for globally
  grade-preserving vertex maps on nondecreasing integer observations, with
  empty, negative and repeated observations allowed. Barcode endpoints are
  observation indices, with repeated intervals retained; death at the
  observation count records survival through the last sample, without
  inferring a lifetime between or beyond observations. Extraction is
  quadratic in the observation count, using the existing rank evaluation
  exponential in source Betti dimension. See
  [sampled image barcodes](docs/api.md#persistent-homology-results-and-computational-boundary).
- Make the finite-line chronological path construction and its explicit
  matrix-sequence consumer executable: `FiniteLine.path`, `fromFin`,
  `pathEquivalence`, `representationEquivalence` and `moduleOfAdjacent` build
  data directly by finite recursion instead of selecting a path with
  `Classical.choice`, with no new hypothesis on the existing public
  interfaces. See
  [executing chronological finite persistence](docs/math/finite-line-computation.md).
- Expose the executable rank of a rectangular F₂ matrix, `F2Matrix.rank`,
  computed by enumerating the images of all source vectors and proved equal to
  the range dimension and to Mathlib's `Matrix.rank`, for every shape including
  no rows or no columns. The cost is exponential in the number of columns. See
  the [API guide](docs/api.md#persistent-homology-results-and-computational-boundary).
- Reduce weak-pair rank erosion of the Kan extensions of modules on two finite
  coordinate grids to finitely many grades: the predicate holds if and only if
  its inequalities hold at the comparable pairs of points of any finite grid
  containing both grids' values and their shifts by the radius, with no
  finite-dimensionality assumption. This is a criterion over the real numbers,
  not an executable test. See
  [rank erosion](docs/math/rank-erosion.md#finite-test-grids-for-grid-kan-extensions).
- Represent F₂ modules on rational coordinate grids by executable data
  (`F2GridRep`): fiber dimensions and matrices, with a decidable validity
  condition, the actual grid module of a valid representation, and an
  executable rank at rational grades proved equal to the rank of the actual
  Kan extension. Costs are exponential in the fiber dimension and the number
  of coordinates. See
  [rank erosion](docs/math/rank-erosion.md#executable-representations-over-the-two-element-field).
- Test weak-pair rank erosion of two F₂ grid representations at a rational
  radius by execution (`F2GridRep.runErosion`). The test rejects an invalid
  representation or a negative radius. Otherwise it certifies weak-pair erosion
  of the actual Kan extensions at that radius or returns a failed inequality
  with its direction, grades and ranks. In the latter case the tested radius
  is strictly below their erosion distance. See
  [rank erosion](docs/math/rank-erosion.md#a-certified-finite-test).
- Add strict-pair rank erosion (`StrictRankErosion`, `strictRankErosionDistance`)
  on the strict pairs of the product order and compare it with the weak-pair
  predicate: the weak predicate implies the strict one at the same radius; with
  at least one coordinate and finite-dimensional fibers the strict predicate
  implies the weak one at every larger radius and the two distances are equal;
  and a radius at which a predicate fails is a non-strict lower bound of its
  distance. The predicates differ at a fixed radius, as a module supported on a
  closed box shows, and with no coordinates the strict distance is always zero.
  See [rank erosion](docs/math/rank-erosion.md#strict-pairs).
- Prove erosion attainment for modules with original finite presentations
  (`GradedFree.FinitelyPresented`): the rank invariant is locally constant
  under small diagonal moves to the right, a radius at which `RankErosion`
  fails is a strict lower bound of `rankErosionDistance`
  (`GradedFree.finitelyPresented_lt_rankErosionDistance_of_not_rankErosion`),
  the distance is at most a radius exactly when the predicate holds there
  (`GradedFree.finitelyPresented_rankErosionDistance_le_iff_rankErosion`), the
  admissible radii form a closed set, and distance zero is equality of all
  weak-pair ranks. The zero module and the Kan extension of a valid
  `F2GridRep` are finitely presented, so a failing executed test gives a strict
  lower bound of the erosion distance. Examples compute the distance `1/2` of
  the interval `[0, 1)` from zero and show that the module of a closed box is
  not finitely presented. `rankErosionDistance_self` and
  `strictRankErosionDistance_self` no longer assume finite-dimensional fibers.
  See
  [rank erosion](docs/math/rank-erosion.md#attainment-for-finitely-presented-modules).
- Compare the two erosion predicates at a fixed radius and certify failed
  tests for finitely presented modules: with at least one coordinate
  `StrictRankErosion ε M N ↔ RankErosion ε M N`
  (`GradedFree.finitelyPresented_strictRankErosion_iff_rankErosion`); the
  strict distance is at most a radius exactly when the strict predicate holds
  there; and a radius at which erosion fails is strictly below the erosion
  distance, which is at most the interleaving distance
  (`GradedFree.finitelyPresented_rankErosion_failure_certificate`,
  `GradedFree.finitelyPresented_lt_coordinateInterleavingDistance_of_not_rankErosion`).
  For valid `F2GridRep` input, `F2GridRep.runErosion` passes exactly when the
  erosion distance of the actual Kan extensions is at most the tested radius,
  and general statements give what a pass and a failure imply for both
  predicates and for the erosion and interleaving distances. Examples show
  that, with at least one coordinate, the closed box and zero are interleaved
  at every radius above their interleaving distance and not at it, that the
  fixed-radius equivalence fails with no coordinates, and that two finitely
  presented two-parameter modules over the
  two-element field have equal rank invariants, erosion distance zero and
  nonzero interleaving distance. `GradedFree.finitelyPresented_zero` now
  allows an index type in any universe. See
  [rank erosion](docs/math/rank-erosion.md#fixed-radius-certificates-and-nonseparation).
- Compute the incidence lists of graph-PL input by execution
  (`HeightGraph.incidence?`): from a Boolean adjacency function and rational
  vertex heights, the sorted distinct levels, one cell per level component and
  per crossing edge, and the spanning edges of each gap with their endpoint
  cells, retaining distinct edges with the same endpoint cells. Component labels
  are proved to decide reachability in the actual induced level graphs; invalid adjacency is
  rejected. The executed lists are proved isomorphic, as finite Reeb data, to
  `graphPLReebData` at the computed levels, and the Reeb quotient of the
  graph-PL height is identified over `ℝ` with their realization
  (`HeightGraph.reebDataIso`, `HeightGraph.reebQuotientIso`). See
  [executable incidence extraction](docs/math/mapper.md#executable-incidence-extraction).

- Compute certified F₂ barcodes of finite rational planar α filtrations.
  `AlphaInput.run` reuses the finite reducer, returns exact squared-radius
  endpoints, and rejects repeated sites. Its degreewise result agrees with
  actual closed α persistence. See
  [exact planar α barcodes](docs/math/finite-ph-computation.md#exact-planar-α-barcodes).
- Compute the exact bottleneck distance of two finite integer diagram presentations
  (`TDA.Persistence.IntegerBottleneck`, `TDA.Persistence.IntegerBottleneckCorrectness`). A
  `Presentation` lists integer finite pairs and essential births. `run` returns twice the
  distance in `WithTop ℕ` and, when the essential counts agree, an optimal occurrence
  matching on the original list positions; otherwise the value is `⊤`. `run_correct`
  identifies the value with twice the existing real diagram `bottleneck`, and `solve_cost_eq`
  and `solve_optimal` state that the returned matching attains it. The search is exhaustive.
  See [integer bottleneck computation](docs/math/integer-bottleneck.md).
- Add a whole-line example for the finite-birth decorated diagram of q-tame modules
  (`TDA.Persistence.WholeLineObstructionExamples`). Over a field, the constant scalar module on
  `ℝ` and the zero module are q-tame and have the same diagram
  `LocallyFiniteDecoratedDiagram.ofQModule`, so their diagram bottleneck distance is `0`,
  while their real interleaving distance is `⊤`
  (`canonical_zero_but_module_distance_top`). The constant module is nonzero below every
  threshold (`constant_no_zero_left_bound`).
- Count the occurrences of the scalar interval decomposition of a real pointwise
  finite-dimensional module by strict structure-map ranks
  (`TDA.Persistence.RealIntervalObservation`). For `s < t`,
  `persistenceImage_finrank_eq_scalar_crossing` states that the rank of the structure map
  from `s` to `t` is the number of occurrences whose support contains `s` and `t`; this set of
  occurrences is finite (`scalar_crossing_finite`), and isomorphic modules have equal counts
  (`scalar_crossing_card_eq_of_iso`). `RealIntervalObservationExamples` evaluates the count for
  interval modules, the zero module and a whole-line module.
- Migration from v0.4.0: the following released declarations changed in definition or
  computability, and their types are unchanged. `FiniteInput.listEquiv` has a new body whose
  inverse is a finite list search (`listEquiv_symm_val`), and `listEquiv_eq_ofBijective` proves
  it equal to the v0.4.0 body. `listEquiv`, `faceFintype`, `gradeFilter`, `positionEquiv`,
  `compatibleOrder` and `sublevelFaceIndex` are no longer `noncomputable`.
  `homologyMapDimensions` computes its rank with `F2Matrix.rank`, the same number as before;
  `homologyMapDimensions_eq` is unchanged. The `noncomputable` marker was also removed from
  `barcodeEnumerationNatIso` and from `FiniteLine.homMk`, `homOfAdjacent`, `isoOfAdjacent` and
  `adjacentRecovery`, in addition to the declarations named in the two entries above on
  executable interval and finite-line constructions. `FiniteInterval.fiber`, `intervalMap` and
  `intervalModule` decide `FiniteInterval.alive` with the new instance
  `FiniteInterval.decidableAlive` in place of a classical decision. Each equals its v0.4.0 body
  propositionally, so a downstream proof by `rfl` against the old body may need a rewrite.
  In `TDA.Persistence.RipsSamplingEmpiricalExamples`, `repeatedTraining_totalVariation` and
  `repeatedTraining_fullH0_bound` state their bounds with the public
  `TDA.Topology.MeasureBifiltration.uniformPMF (V := Bool)` in place of a private copy of the
  uniform law on `Bool`; the law and the bounds are unchanged (#981).

Lean: `leanprover/lean4:v4.35.0`, unchanged from v0.4.0; seven library areas. No module
of v0.4.0 was removed or renamed, and every theorem pinned at v0.4.0 is still pinned under
the same name. See the release notes for exact hypotheses, source-review limits and
unsupported extensions.

## v0.4.0

Published 2026-11-14. [Release notes](https://github.com/uda-lab/tda-lib/releases/tag/v0.4.0)
· [Versioned API guide](https://github.com/uda-lab/tda-lib/blob/v0.4.0/docs/api.md).

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
- Publish the curated documentation site at https://uda-lab.github.io/tda-lib/.
- Report the Lean build thread count and the detected CPU count in build
  output, instead of leaving the single-thread default invisible.
- Add a compatibility CI cache-restore key so a `lakefile.toml`-only change
  can still restore the build cache instead of forcing a cold rebuild.
- Share a Lake build-artifact cache across worktrees, so a new worktree
  restores cached build output instead of rebuilding it.

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

Lean: `leanprover/lean4:v4.35.0`; seven library areas. The certified finite F₂
computation is unchanged except for the extensions listed above. See the
release notes for exact bounds, source-review limits and unsupported
extensions.

### Note added after the release

Added on 2026-11-25; the tag and the GitHub Release are unchanged. Between v0.3.0 and
v0.4.0, [#820](https://github.com/uda-lab/tda-lib/pull/820),
[#840](https://github.com/uda-lab/tda-lib/pull/840) and
[#841](https://github.com/uda-lab/tda-lib/pull/841) rewrote the bodies of ten released
definitions without changing their values: `HeightMapPair.natTransSymm`,
`HeightMapPair.interleaving`, `Interleaving.scalePre`, `Interleaving.translatePre`,
`scalePreOneIso`, `scalePreScalePreIso`, `translatePreZeroIso`,
`simpleModule_leftDerivedZeroIso`, `bool_lower_simple_degree_zero_comparison` and
`IsPointwiseShortExact.pushoutQuotient`. The count and the list are those of the
pre-release review recorded in [#1115](https://github.com/uda-lab/tda-lib/issues/1115#issuecomment-7119370760),
which checked each new body against the old one by compiled equalities. These pull requests also added the public
helpers `Interleaving.reindex`, `reindex_φ_app`, `reindex_ψ_app`, `reindexIso` and
`reindexIso_hom_app` (`TDA.Reeb.IntervalTranslation`) and
`leftDerivedZeroIso_of_rightVertexIso` (`TDA.Persistence.IncidenceQuotientSimple`), which
v0.4.0 contains. In the same interval, [#787](https://github.com/uda-lab/tda-lib/pull/787)
changed `diagonalIdealTwoSided` in `TDA.Persistence.IncidenceVertexProjectiveDimension`
from a local instance to an `abbrev`. No migration is needed for these changes.

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
