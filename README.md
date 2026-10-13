# tda-lib

A Lean 4 library for topological data analysis, including persistent homology,
mathematical theory and verified computational algorithms. Development is continuous;
executability is required only where an individual algorithm contract calls for it.

The library includes signed simplicial chains and homology on actual faces, finite
interval decomposition and complete-rank classification, actual sublevel persistence
diagrams, finite-filter bottleneck stability, and local regularity, derivative and Hessian
results with explicit lift hypotheses. A certified finite F₂ simplex-list computation
connects its output to those actual diagrams. Reeb/cosheaf and ordinary Mapper constructions
also implement their bounded lane contracts; their pre-publication source review remains
tracked in [#215](https://github.com/uda-lab/tda-lib/issues/215).

See [the public API guide](docs/api.md) for entry points, coefficient and finiteness
requirements, computational scope and deferred extensions. `TDA.placeholder_add_zero`
remains an infrastructure smoke theorem exercising the axiom audit.

For ordinary use, import an area such as `TDA.Persistence`, or `TDA.Library` for all
library areas. `TDA` additionally imports standalone examples and acceptance fixtures,
and remains the comprehensive audit and documentation root.

## Build

```sh
scripts/bootstrap.sh
scripts/check.sh
```

Lean is pinned in `lean-toolchain`; mathlib is pinned in `lakefile.toml` and
`lake-manifest.json`. TauCeti is a candidate foundation to research, not an installed
dependency. Existing foundations are reused where appropriate; upstream acceptance is
not a prerequisite for local completion.

## API documentation

Generate the module and declaration pages for `TDA` and its imported dependencies with
the pinned Lean 4.33.1 toolchain and doc-gen4 revision:

```sh
scripts/build-docs.sh
```

The nested project lock is committed at `docbuild/lake-manifest.json`. The build uses
the existing parent package directory and does not update the lock. To inspect the generated
site, serve it over loopback HTTP:

```sh
cd docbuild/.lake/build/doc
python3 -m http.server 8000 --bind 127.0.0.1
```

Then open `http://127.0.0.1:8000/`. Stop the server with Ctrl-C. The site documents the
current imports-only `TDA.lean` root, intentionally including examples and acceptance
fixtures as well as library declarations. Add library modules to their area aggregator
and standalone examples to `TDA/<Area>/Examples.lean`; both enter that documentation
target. doc-gen4 also
generates pages for Lean, Init, Lake, Std and the imported libraries. Generated files and
package caches remain untracked and private. CI retains only the generated documentation
tree as a private artifact for seven days when the optional job is enabled; it does not
publish the site or upload caches. Hosted Actions remain disabled under the October
local-CI policy; this documentation command is a separate local workflow.
The build requires a clean committed tree so its source links point to that exact revision.
When the commit changes, the build refreshes TDA's cached declaration pages and search data
because doc-gen4 reads the source revision from Git rather than tracking it as a Lake input.

## Layout

| Path | Purpose |
|---|---|
| `TDA/`, `TDA.Library` | Library modules and ordinary imports-only area entry points |
| `TDA.Examples`, `TDA/<Area>/Examples.lean` | Standalone examples and acceptance fixtures |
| `TDA.lean` | Comprehensive library/example root for audit and generated documentation |
| `scripts/` | Bootstrap, full gate, integrity audits and GitHub setup |
| `docs/math/` | Source references, mathematical definitions and conventions |
| `docs/adr/` | Durable development decisions |
| `.agents/skills/tda-lib-orchestration/` | Canonical project entry policy for all agents |
| `scripts/agent/` | Shared resource, stop and process ownership safeguards |
| `.codex/`, `.claude/` | Optional native hook adapters; Claude skill compatibility links |
| `.github/` | CI and inherited Issue/PR templates |

## Development and releases

The private [tda-lib Project](https://github.com/orgs/uda-lab/projects/5) holds the overall
roadmap, milestones, priorities and progress, managed by the continuing agent dot. GitHub
Issues hold complete mathematical specifications and execution contracts. Project Ready
does not authorize execution; eligible Issues receive `agent:ready` after dot or an authorized
maintainer verifies their gates.
Regular reviewed PRs integrate into `develop`; sufficiently mature stable versions are
promoted through reviewed PRs to `main` and tagged. `main` is the stable branch, not the
routine integration target. See [the orchestration guide](docs/orchestration.md).

Public theorem axiom closures are audited against
`{propext, Classical.choice, Quot.sound}`. The coverage guard checks that public theorems
are pinned and every library/example module is imported by `TDA`; it also audits private
theorem roots outside pinned dependency closures against the same allowlist. Computational
`#eval` results are separate from theorem trust. Stable releases exclude staging holes
and report precisely the results and limitations reviewed for that release.

Public API documentation requires doc-gen4; Blueprint is optional. ellalpha is an
independent consumer, not a library completion condition. The first stable release need
not complete all Project milestones; dates and execution order are established only from
actual decisions and dependencies.

The repository remains private until roadmap preparation is complete, then continues
public development under dot's authority.

Agent sessions use `scripts/lean.sh` for direct Lean/Lake commands and `scripts/codex.sh`
for child Codex jobs. These entry points are mandatory independently of native hook activation.
Codex and Claude Code have optional supported command adapters under the same shared policy.
See the orchestration guide for stop handling and cleanup.

## License

Apache-2.0; see [LICENSE](LICENSE).
