# lean-formalization-scaffold

A **template repository** for Lean 4 + mathlib formalisation programmes that existing agent
harnesses (Claude Code, Codex) can drive from one initial prompt to a finished, audited
development. It ships the integrity gates, CI, hooks, Issue/PR contracts and orchestration
skills that carried [`uda-lab/mobius-cpt`](https://github.com/uda-lab/mobius-cpt) from an
empty repository to a published formalisation — and nothing that would need a bespoke
orchestration runtime.

The orchestration guide is **`docs/orchestration.md`** (one page: roles, the two
configurations, lifecycle, entry commands). The procedure is
`.claude/skills/loop-orchestration-scaffold/SKILL.md`.

## Quick start

1. Create a repository from this template (`gh repo create <owner>/<name> --template
   uda-lab/lean-formalization-scaffold --private`) and clone it.
2. Open your harness in the clone (`claude` or `codex`). `AGENTS.md` / `CLAUDE.md` route the
   session into preflight; it will not start mathematics.
3. Paste the initial prompt — papers, target theorem, configuration, authority — following
   `.claude/skills/loop-orchestration-scaffold/references/initial-prompt.md`.

The session measures the machine, sets up GitHub, writes the charter Issue, renames the
library, digests the sources, rewrites `AGENTS.md` and generates the repo-specific
orchestration skill, then decomposes the target into Issues and runs the Issue → PR → review →
merge loop until the charter's definition of done is met.

## Layout

| Path | Role |
|---|---|
| `LeanScaffold/`, `LeanScaffold.lean` | placeholder library and root aggregator (renamed by `scripts/rename-project.sh`) |
| `scripts/` | preflight, bootstrap, the canonical gate `check.sh`, integrity guards, GitHub setup, git hooks |
| `scripts/print_axioms.lean` | append-only list of pinned public theorems for the live axiom audit |
| `.claude/skills/` | `loop-orchestration-scaffold` (init → submission, with templates), `lean-issue-decomposition`, `lean-review-routing` |
| `.claude/hooks/`, `.claude/settings.json` | SessionStart brief; PreToolUse guard that serialises Lean builds and enforces the codex kill switch |
| `.github/` | CI job `check`, Issue templates (formalization / infrastructure), PR template |
| `docs/orchestration.md` | the minimal orchestration guide |
| `docs/adr/` | founding decisions: harness-driven, no state machine (0001); autonomous merge authority (0002, owner ratifies) |
| `docs/math/` | the mathematical source of truth, written during Init |
| `docs/note/` | optional exposition note (opt-in lane; `scripts/check-note.sh` builds it once `note.conf` exists) |

## Build

```sh
scripts/bootstrap.sh   # once per clone: mathlib oleans via `lake exe cache get`, git hooks path
scripts/check.sh       # guards → lake build → live #print axioms audit → coverage guard
```

The toolchain is `lean-toolchain`; mathlib is pinned by tag in `lakefile.toml` and by commit
in `lake-manifest.json`. CI runs the textual guards on every pull request and the full gate
whenever Lean sources, build configuration, scripts or workflows change.

## Trust footprint

Accepted theorems are `sorry`-free and their axiom closure is contained in
`{propext, Classical.choice, Quot.sound}`; `scripts/check-axioms.sh` verifies this live for
every declaration listed in `scripts/print_axioms.lean`, and
`scripts/check_axiom_coverage.lean` fails the gate if a public theorem is not listed.

## Workflow

GitHub Issues and pull requests are the only work queue and evidence record:
Issue → branch → PR → independent review → CI → squash merge. No status, roadmap or progress
files are tracked; agent scratch lives in `.claude/scratch/` (gitignored).

## License

Apache-2.0, see `LICENSE`. Replace the copyright line when instantiating the template.
