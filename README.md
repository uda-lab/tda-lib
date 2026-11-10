# tda-lib

`tda-lib` is a Lean 4 library for topological data analysis: persistent homology,
certified finite F₂ persistence computation, diagram distances and representations,
metric-space filtrations, multiparameter persistence, and Reeb and Mapper theory.
The current published release is
[v0.3.0](https://github.com/uda-lab/tda-lib/releases/tag/v0.3.0).
Documentation on `develop` also describes unreleased work; use the versioned guides
in the [changelog](CHANGELOG.md) when working with a release.

## Scope and limitations

Most constructions are abstract theory. The certified executable reduction works
over F₂ on valid finite graded simplex lists; arbitrary-field executable reduction
and an executable Mapper package are outside its contract. Results have explicit
finiteness, field, topological and cover hypotheses. General geometric persistence
and infinite-dimensional persistence beyond the documented q-tame setting are
outside the current scope. Start with the [guide by subject](docs/README.md) and
consult the [API guide](docs/api.md) for exact assumptions and declaration names.

## Use in a Lean project

For the published **v0.3.0** release, use `leanprover/lean4:v4.33.1` and add
the dependency to your `lakefile.toml`:

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

`TDA.Library` loads the seven library areas; `import TDA` also loads standalone
examples. See the [import guide](docs/api.md#entry-points) for the current checkout
and the [v0.3.0 import guide](https://github.com/uda-lab/tda-lib/blob/v0.3.0/docs/api.md#entry-points)
for that release's module boundaries.

## Documentation

- [Guide by subject](docs/README.md): current capabilities, limitations and routes
  into the mathematical notes.
- [API and import guide](docs/api.md): declaration names and precise contracts.
- [Mathematical notes and source register](docs/math/README.md): constructions,
  conventions, references and source-comparison limits.
- [Changelog](CHANGELOG.md): published changes, migration information and unreleased work.
- [Contributing](CONTRIBUTING.md): development and integration policy.

## Build and documentation

From a checkout, prepare cached dependencies and run the library check:

```sh
scripts/bootstrap.sh
scripts/check.sh
```

Use the checkout's `lean-toolchain` and `lake-manifest.json` pins. For generated
API pages, run `scripts/build-docs.sh` from a checkout with no uncommitted changes.
It writes `docbuild/.lake/build/doc`; the site is not hosted by this repository.
See the [documentation guide](docs/README.md#generated-api-pages) for its scope.

## Citation

When citing the software, identify the release or commit used and link to its
[GitHub release](https://github.com/uda-lab/tda-lib/releases). Mathematical sources
and their use in the library are listed separately in the
[source register](docs/math/references.md).

<a id="results-in-v010"></a>
<a id="results-added-in-v020"></a>
<a id="results-added-in-v030"></a>

## Release results

See the changelog entries for
[v0.1.0](CHANGELOG.md#v010), [v0.2.0](CHANGELOG.md#v020) and
[v0.3.0](CHANGELOG.md#v030), which link to the full published release notes.
For current features, use the [guide by subject](docs/README.md).

<a id="future-directions"></a>

## Further directions

See the [current boundaries](docs/README.md#boundaries-and-further-directions) and
[API review limits](docs/api.md#review-and-extension-boundaries) before extending a
result. [Issue #227](https://github.com/uda-lab/tda-lib/issues/227) records the
source-linked directions; the guides distinguish published results from later work.

## License

The library is licensed under [Apache-2.0](LICENSE).
