#!/usr/bin/env bash
# Fail if the repository TRACKS transient or prohibited artefacts.
#
# GitHub Issues and PRs are the only status, planning and evidence surface of this
# repository. Build output, logs, scratch material and status/handoff/ledger-style
# documents must never be committed. This guard inspects tracked content only:
#   - with no argument, the index (`git ls-files`), i.e. what a commit would carry;
#   - with a revision argument, that commit's tree (`git ls-tree`), which is how the
#     pre-push hook audits every pushed commit.
# Untracked files are deliberately out of scope: proof experiments, local logs and
# local-only notes are exactly what policy permits to exist on disk, and a CI
# checkout has no untracked files. `.gitignore` protects against accidental `git add`.
#
# FAIL-CLOSED: the file listing is written to a temp file whose exit status is
# checked before it is consumed; one awk pass with no error suppression.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

rev="${1:-}"
list="$(mktemp)"
trap 'rm -f "$list"' EXIT
if [ -n "$rev" ]; then
  git ls-tree -r -z --name-only "$rev" > "$list"
  what="commit $rev"
else
  git ls-files -z --cached --full-name > "$list"
  what="index"
fi

# One NUL-separated pass. Each rule prints `path: reason`.
violations="$(tr '\0' '\n' < "$list" | awk '
  {
    path = $0
    lower = tolower(path)
    n = split(lower, parts, "/")
    base = parts[n]
    stem = base; sub(/\.[^.]*$/, "", stem)
    ext = ""; if (base ~ /\./) { ext = base; sub(/^.*\./, "", ext) }

    # 1. build output
    if (lower ~ /(^|\/)\.lake\// || lower ~ /(^|\/)build\//) { print path ": build output directory"; next }
    if (ext == "olean" || ext == "ilean" || ext == "trace" || ext == "hash") { print path ": compiled Lean artefact"; next }

    # 2. logs and LaTeX by-products
    if (lower ~ /\.(log|aux|synctex\.gz|fdb_latexmk|fls)$/) { print path ": log or build by-product"; next }

    # 3. status / handoff / ledger documents (Issues and PRs are the only status surface)
    if ((ext == "md" || ext == "txt" || ext == "rst") &&
        stem ~ /(^|[-_.])(handoff|status|roadmap|todo|progress|checklist|worklog|ledger|activity[-_]?log|agent[-_]?log|completion)([-_.]|$)/) {
      print path ": status/handoff/ledger-style document"; next
    }
    if (base ~ /^(handoff|status|todo|roadmap)$/) { print path ": status/handoff-style document"; next }

    # 4. prohibited directories
    if (lower ~ /(^|\/)\.agent_orchestra\//) { print path ": .agent_orchestra/ is prohibited"; next }
    if (lower ~ /(^|\/)docs\/scratch\//)     { print path ": docs/scratch/ is prohibited"; next }
    if (lower ~ /(^|\/)scratch\//)           { print path ": scratch/ directories are prohibited"; next }
    if (lower ~ /(^|\/)\.claude\/worktrees\//) { print path ": agent worktree content"; next }

    # 5. editor / OS noise
    if (base == ".ds_store" || ext == "swp") { print path ": editor/OS noise"; next }
  }
')"

count="$(tr '\0' '\n' < "$list" | grep -c . || true)"

if [ -n "$violations" ]; then
  printf '%s\n' "$violations" >&2
  echo "ERROR: transient or prohibited artefacts are tracked in the $what (Issues/PRs are the only status surface; see AGENTS.md)." >&2
  exit 1
fi
echo "OK: no transient artefacts tracked in the $what ($count files scanned)."
