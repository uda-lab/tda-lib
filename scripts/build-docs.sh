#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

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
../scripts/check-doc-lock.sh
printf '%s\n' "$current_rev" > "$source_rev_file"
