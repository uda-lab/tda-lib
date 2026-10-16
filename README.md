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

## Future directions

The following are proposed work, not results of v0.1.0.
[Issue #227](https://github.com/uda-lab/tda-lib/issues/227) sets out their
hypotheses, source links and boundaries.

- Extend finite diagram distances to partial-matching p-costs and boundary
  transport, and develop finite-constructible real-index interleavings.
- Prove stability of persistence images with fixed bandwidth, weights and pixels.
- Build finite Rips and Čech inputs, starting with a bottleneck bound for two
  metrics on the same labelled set.
- Extend Reeb smoothing comparisons toward coherent geometric interleavings
  and a comparison with cosheaf distance.
- Study resolution-controlled Reeb approximation for graph-based Mapper,
  with the ordinary Mapper and enhanced constructions distinguished.

## License

The library is licensed under [Apache-2.0](LICENSE).
