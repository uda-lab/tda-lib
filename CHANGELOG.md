# Changelog

Published entries summarize the existing GitHub Releases, which contain the full
results, assumptions and limitations. Their versioned API guides describe the
released interfaces. [Current documentation](docs/README.md) follows the checkout;
it can include work absent from the latest release. This is a 0.x API with no
cross-version compatibility promise.

## Unreleased

Changes on `develop` after v0.4.0; the next release version is undecided.

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
  exactly an equal-grade list-level matching with a topological rank, some rank
  is accepted exactly for a duplicate-free filtered acyclic matching, and
  `CertifiedMatching` reports the critical faces with their dimension and
  original grade. See
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
  four maps grade-nonincreasing for equal grades; no iteration or persistence isomorphism. See
  [unit cancellation](docs/math/discrete-morse-cancellation.md).
- Bundle filtered contractions of based complexes
  (`TDA.Persistence.Morse.FilteredContraction`): computable projection, inclusion and homotopy
  matrices with chain-map, homotopy, side-condition, degree and grade fields, composition
  (`trans`), transport of the small complex along a carrier equivalence (`reindex`),
  restatement along equalities (`copy`) and the unit-pair instance (`ofUnitPair`);
  `D' * D' = 0` follows from `D * D = 0`, and the based and filtered differential properties
  transfer to the small complex. Fixtures compose two cancellations on the filled triangle by
  `decide +kernel`. No iteration or persistence isomorphism. See
  [filtered contractions](docs/math/discrete-morse-cancellation.md#filtered-contractions-and-their-composition).
- Form grade-sublevel homology of filtered based complexes as persistence modules over `ℤ`
  (`TDA.Persistence.Morse.FilteredHomology`): degree-`p` cycles in grades `≤ t` modulo the
  boundaries of degree-`p + 1` chains in grades `≤ t`, with no hypothesis on the matrix, and
  the natural isomorphism `sublevelHomologyIso` of these persistence modules induced by the
  projection of a filtered contraction, with equal `Module.finrank`, without assuming
  `D * D = 0`. Fixtures over `ZMod 2` transport the dimensions of the critical complex of the
  regraded filled triangle to the triangle. No bridge from `sublevelHomologyPModule` to
  simplicial homology. See
  [sublevel homology](docs/math/discrete-morse-cancellation.md#sublevel-homology-and-the-induced-isomorphism).
- Iterate unit cancellation along a supplied pivot schedule
  (`TDA.Persistence.Morse.IteratedCancellation`): `IsPivotSchedule` asks for distinct
  endpoints, unit equal-grade pairs and that no lower generator is a face of a later upper
  generator, and is preserved by cancelling the head pair; `criticalDifferential` is an
  executable reduced differential on the critical generators, and `FilteredContraction.ofSchedule`
  is the composed filtered contraction onto it. Fixtures evaluate the multi-grade square and
  the regraded filled triangle by `decide +kernel`. No derivation of the schedule from a
  matching. See
  [iterated cancellation](docs/math/discrete-morse-cancellation.md#iterated-cancellation-along-a-pivot-schedule).
- Derive the pivot schedule of a certified matching on a valid input
  (`TDA.Persistence.Morse.MatchingSchedule`): over `ZMod 2` the finite-input boundary is the
  cover incidence, `CertifiedMatching.schedule` sorts the certified pairs stably by the rank of
  the lower face, and `isPivotSchedule_schedule` proves that it is a pivot schedule for the
  boundary. `CertifiedMatching.morseDifferential` is the executable Morse differential on the
  critical positions, `CertifiedMatching.morseContraction` the filtered contraction of the
  boundary complex onto it, and `CertifiedMatching.morseHomologyIso` the induced isomorphism of
  grade-sublevel homology persistence modules. Fixtures evaluate three certificates on the
  multi-grade square, including a tie in the rank, by `decide +kernel`. No bridge to
  simplicial persistent homology. See
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
  diagram `dgm` is `{(1, 2)}`. No interval decomposition and no barcode agreement with the
  reducer. See
  [the simplicial bridge and the Morse persistence theorem](docs/math/discrete-morse-cancellation.md#the-simplicial-bridge-and-the-morse-persistence-theorem).
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
  finite-dimensional. No multiparameter finite-image condition is stated. See
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
  and the cost is documented, not proved. The docstrings of `roundDown` and
  `roundUp` now say "at most" and "at least". See
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
  degree. `ripsLabelMap` induces an isomorphism from the homology of the Rips
  complexes to the sublevel homology of the list, `ripsRunInDegree` returns the
  records of one degree and `none` for an invalid table in every degree, and
  relabelled tables have equal diagrams. The new module
  `TDA.Persistence.SublevelDiagramVertexMap` proves `dgm_eq_of_vertexMaps`, the
  invariance of real sublevel diagrams under mutually inverse vertex maps
  between complexes on two vertex types. The four-cycle is a kernel-checked
  fixture with one class of degree one from `1` to `2`. The cost of the
  existing reduction remains unbounded. See
  [Diagram and homology of the Rips input](docs/math/finite-ph-computation.md#diagram-and-homology-of-the-rips-input).

- Execute the complete Rips simplex list of an integer distance table in the
  `FiniteInput` format: `DistanceTable`, its decidable `Valid`, `ripsInput`,
  `ripsInput?` and `ripsRun`, which return `none` for an invalid table. The
  list is ordered by grade, cardinality and label order, satisfies
  `FiniteInput.Valid`, and its faces and grades are identified with
  `Rips.fullComplex` and `Rips.filter` for the table metric. The list costs
  `O(N² 2 ^ N)` operations; the cost of the existing reduction is separate.
  The equality of the resulting diagram with the Rips diagram is not part of
  this change. See
  [Rips input from an integer distance table](docs/math/finite-ph-computation.md#rips-input-from-an-integer-distance-table).

- Identify each finite-input image structure-map rank with the range dimension
  of the induced simplicial map between sampled sublevels, for global vertex
  maps on monotone integer observations with repeated or negative thresholds
  and collapsed faces allowed. See the
  [homology-map dimensions](docs/math/finite-ph-map-dimensions.md) guide.
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
  radius by execution (`F2GridRep.runErosion`): the result is invalid input, a
  pass, or a failed inequality with its direction, grades and ranks, and it is
  proved correct for the actual Kan extensions in all three cases. A failure
  refutes the predicate at that radius; it is not a strict distance bound. See
  [rank erosion](docs/math/rank-erosion.md#a-certified-finite-test).
- Add strict-pair rank erosion (`StrictRankErosion`, `strictRankErosionDistance`)
  on the strict pairs of the product order and compare it with the weak-pair
  predicate: the weak predicate implies the strict one at the same radius; with
  at least one coordinate and finite-dimensional fibers the strict predicate
  implies the weak one at every larger radius and the two distances are equal;
  and a radius at which a predicate fails is a non-strict lower bound of its
  distance. The predicates differ at a fixed radius, as a module supported on a
  closed box shows, and with no coordinates the strict distance is always zero.
  No erosion attainment or strict lower bound is supplied by these
  declarations. See [rank erosion](docs/math/rank-erosion.md#strict-pairs).
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
  cells, parallel entries retained. Component labels are proved to decide
  reachability in the actual induced level graphs; invalid adjacency is
  rejected. The executed lists are proved isomorphic, as finite Reeb data, to
  `graphPLReebData` at the computed levels, and the Reeb quotient of the
  graph-PL height is identified over `ℝ` with their realization
  (`HeightGraph.reebDataIso`, `HeightGraph.reebQuotientIso`). See
  [executable incidence extraction](docs/math/mapper.md#executable-incidence-extraction).

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
