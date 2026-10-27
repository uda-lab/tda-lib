#!/usr/bin/env bash
# Fail if a TRACKED text file contains a merge-conflict marker line: `<<<<<<<`, `=======` or
# `>>>>>>>` at the start of a line, followed by a space or the end of the line.
#
# The Lean build never reads Markdown, scripts or pin files, so a half-resolved merge in
# docs/api.md or lakefile.toml passes every other guard (PR #539). This guard inspects tracked
# content only, with the same interface as check-transient-artifacts.sh:
#   - with no argument, the index (`git grep --cached`), i.e. what a commit would carry;
#   - with a revision argument, that commit's tree, which is how the pre-push hook audits
#     every pushed commit.
# Binary files are skipped (`-I`). Untracked files are out of scope: the working tree may hold
# an unfinished merge, but nothing with markers may be committed.
#
# FAIL-CLOSED: `git grep` exits 1 for "no match" and 2 or more for an error; only exit 1 passes.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

rev="${1:-}"
pattern='^(<{7}|={7}|>{7})( |$)'
status=0
if [ -n "$rev" ]; then
  hits="$(git grep -n -I -E "$pattern" "$rev" -- . 2>&1)" || status=$?
  what="commit $rev"
else
  hits="$(git grep --cached -n -I -E "$pattern" -- . 2>&1)" || status=$?
  what="index"
fi

case "$status" in
  0)
    # `rev:path:line:text` or `path:line:text`; keep the path, line and text.
    if [ -n "$rev" ]; then hits="${hits//"$rev:"/}"; fi
    printf '%s\n' "$hits" >&2
    echo "ERROR: merge-conflict markers are tracked in the $what (resolve the merge before committing)." >&2
    exit 1 ;;
  1)
    echo "OK: no merge-conflict markers tracked in the $what." ;;
  *)
    printf '%s\n' "$hits" >&2
    echo "ERROR: git grep failed (exit $status) while scanning the $what." >&2
    exit 2 ;;
esac
