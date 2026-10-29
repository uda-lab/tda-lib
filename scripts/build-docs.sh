#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

check_stop() {
  local stop_file="${CODEX_STOP_FILE:-/tmp/codex-stop}"
  if [ -e "$stop_file" ]; then
    echo "ERROR: stopped by $stop_file" >&2
    exit 2
  fi
}

# Refuse work before waiting, then recheck after the wait before touching generated output.
check_stop
# Keep invalidation, generation, lock verification, and the revision marker in one
# transaction. The Lean wrapper re-enters the same resource locks through inherited descriptors.
. "$ROOT/scripts/lib/build-lock.sh"
check_stop

# doc-gen4 embeds the checked-out Git revision in source links. Require a clean source tree
# so generated links describe the same code that was actually documented.
if [ -n "$(git status --porcelain --untracked-files=all)" ]; then
  echo 'ERROR: commit or remove source changes before generating revision-specific API docs.' >&2
  exit 2
fi

current_rev="$(git rev-parse HEAD)"
source_rev_file="$ROOT/docbuild/.lake/docs-source-rev"
echo "API documentation: +TDA.Library:docs at $current_rev (Lean threads: ${LEAN_NUM_THREADS:-1})."
python3 "$ROOT/scripts/lib/docs-cache.py" prepare "$current_rev"

cd "$ROOT/docbuild"
generation_start=$SECONDS
../scripts/lean.sh lake build +TDA.Library:docs
echo "API documentation generation: $((SECONDS - generation_start))s."
check_stop
../scripts/check-doc-lock.sh
check_stop
printf '%s\n' "$current_rev" > "$source_rev_file"
