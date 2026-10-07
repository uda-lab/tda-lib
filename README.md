# tda-lib

A Lean 4 library foundation for topological data analysis, including persistent homology,
mathematical theory and verified computational algorithms. Development is continuous;
executability is required only where an individual algorithm contract calls for it.

This repository currently supplies the development scaffold, integrity gates and release
workflow. It contains **no TDA proofs or algorithms yet**. `TDA.placeholder_add_zero` is
only an infrastructure smoke theorem exercising the axiom audit.

## Build

```sh
scripts/bootstrap.sh
scripts/check.sh
```

Lean is pinned in `lean-toolchain`; mathlib is pinned in `lakefile.toml` and
`lake-manifest.json`. TauCeti is a candidate foundation to research, not an installed
dependency. Existing foundations are reused where appropriate; upstream acceptance is
not a prerequisite for local completion.

## Layout

| Path | Purpose |
|---|---|
| `TDA/`, `TDA.lean` | Library modules and imports-only aggregator |
| `scripts/` | Bootstrap, full gate, integrity audits and GitHub setup |
| `docs/math/` | Source references, mathematical definitions and conventions |
| `docs/adr/` | Durable development decisions |
| `.agents/skills/tda-lib-orchestration/` | Canonical project entry policy for all agents |
| `scripts/agent/` | Shared resource, stop and process ownership safeguards |
| `.codex/`, `.claude/` | Optional native hook adapters; Claude skill compatibility links |
| `.github/` | CI and inherited Issue/PR templates |

## Development and releases

GitHub Issues hold the roadmap and work queue, managed by the continuing agent dot.
Regular reviewed PRs integrate into `develop`; sufficiently mature stable versions are
promoted through reviewed PRs to `main` and tagged. `main` is the stable branch, not the
routine integration target. See [the orchestration guide](docs/orchestration.md).

Public theorem axiom closures are audited against
`{propext, Classical.choice, Quot.sound}`. The coverage guard checks that public theorems
are pinned and every library module is imported. Stable releases exclude staging holes
and report precisely the results and limitations reviewed for that release.

The repository remains private until roadmap preparation is complete, then continues
public development under dot's authority.

Agent sessions use `scripts/lean.sh` for direct Lean/Lake commands and `scripts/codex.sh`
for child Codex jobs. These entry points are mandatory independently of native hook activation.
Codex and Claude Code have optional supported command adapters under the same shared policy.
See the orchestration guide for stop handling and cleanup.

## License

Apache-2.0; see [LICENSE](LICENSE).
