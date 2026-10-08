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
# transaction. The Lean wrapper re-enters this same lock through inherited fd 9.
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
previous_rev="$(cat "$source_rev_file" 2>/dev/null || true)"
if [ "$previous_rev" != "$current_rev" ]; then
  check_stop
  echo "Refreshing TDA documentation source links for $current_rev."
  doc_data="$ROOT/docbuild/.lake/build/doc-data"
  doc_root="$ROOT/docbuild/.lake/build/doc"
  rm -f "$doc_data"/TDA*.doc* "$doc_data"/TDA--library.docs_built* \
    "$doc_data"/TDA--library.docsHeader_built* \
    "$doc_data"/declaration-data-TDA*.bmp "$doc_data"/backrefs-TDA*.json
  rm -rf "$doc_root/TDA"
  rm -f "$doc_root/TDA.html" "$doc_root/declarations/declaration-data.bmp"
fi

cd "$ROOT/docbuild"
../scripts/lean.sh lake build TDA:docs
check_stop
../scripts/check-doc-lock.sh
check_stop
printf '%s\n' "$current_rev" > "$source_rev_file"
