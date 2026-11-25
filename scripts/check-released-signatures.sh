#!/usr/bin/env bash
# Advisory (#1154 check 3), never part of scripts/check.sh: compares the elaborated types of
# the pinned declarations at a release ref (default: the latest v* tag) with the current
# checkout and lists each pin whose type changed or that no longer exists, saying whether the
# CHANGELOG.md "Unreleased" section names it. The output is a list of candidates for the
# working agent to inspect; a difference is often intended, nothing is rejected, and the exit
# status is 0 whatever is reported (only a usage or tooling error exits nonzero).
#
#   scripts/check-released-signatures.sh [<ref>]       dump <ref> in a temporary worktree and compare
#   scripts/check-released-signatures.sh --compare BASE.tsv HEAD.tsv [<label>]
#                                                      compare two dumps of
#                                                      scripts/dump_pin_signatures.lean
#
# The first form builds <ref> in a temporary detached worktree (warm it from the shared Lake
# artifact cache with scripts/bootstrap.sh; never a cold mathlib build) and dumps the current
# checkout, which must already be built: it is a pre-release step, not a per-PR one.
# TDA_SIG_BASE_DUMP=<file> reuses an existing dump of <ref> instead of building it.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
export PATH="$HOME/.elan/bin:$PATH"

# compare <base.tsv> <head.tsv> <label>: dump files are `name<TAB>hash<TAB>type` lines.
compare_dumps() {
  local base="$1" head="$2" label="$3" changelog="${TDA_SIG_CHANGELOG:-$ROOT/CHANGELOG.md}" work
  # Three distinct copies, selected by file name below: an empty input (for instance a missing
  # "Unreleased" section) then cannot shift the roles of the others, and BASE may equal HEAD.
  work="$(mktemp -d)"
  awk '/^## /{on = ($0 ~ /^## Unreleased/)} on' "$changelog" > "$work/sect" 2>/dev/null || : > "$work/sect"
  cp "$base" "$work/base"
  cp "$head" "$work/head"
  LC_ALL=C awk -F'\t' -v label="$label" -v sectf="$work/sect" -v basef="$work/base" '
    function lastcomp(n,   k, parts) { k = split(n, parts, "."); return parts[k] }
    FILENAME == sectf {  # words of the Unreleased section: last component of each identifier-like run
      s = $0
      gsub(/[^A-Za-z0-9_\047!?.\200-\377]/, " ", s)
      nt = split(s, tok, " ")
      for (i = 1; i <= nt; i++) { t = tok[i]; sub(/\.+$/, "", t); if (t != "") named[lastcomp(t)] = 1 }
      next
    }
    FILENAME == basef { bh[$1] = $2; bt[$1] = $3; next }
    { hh[$1] = $2; ht[$1] = $3 }
    END {
      m = 0
      for (n in bh) {
        if (!(n in hh)) { kind[n] = "no longer pinned (removed or renamed)"; order[++m] = n }
        else if (bh[n] != hh[n]) { kind[n] = "type changed"; order[++m] = n }
      }
      # insertion sort keeps the output deterministic without gawk extensions
      for (i = 2; i <= m; i++) { v = order[i]; j = i - 1; while (j >= 1 && order[j] > v) { order[j+1] = order[j]; j-- } order[j+1] = v }
      for (i = 1; i <= m; i++) {
        n = order[i]
        where = (lastcomp(n) in named) ? "named in" : "not named in"
        printf "SIGNATURE ADVISORY: %s since %s: %s; %s the CHANGELOG.md \"Unreleased\" section.\n", n, label, kind[n], where
        if (kind[n] == "type changed") { printf "  was: %s\n  now: %s\n", bt[n], ht[n] }
      }
      printf "SIGNATURE ADVISORY: %d pin(s) differ from %s; candidates to inspect, not a failure.\n", m, label
    }' "$work/sect" "$work/base" "$work/head"
  rm -rf "$work"
}

if [ "${1:-}" = --compare ]; then
  if [ "$#" -lt 3 ] || [ "$#" -gt 4 ]; then
    echo "usage: scripts/check-released-signatures.sh --compare BASE.tsv HEAD.tsv [<label>]" >&2; exit 64
  fi
  compare_dumps "$2" "$3" "${4:-the base}"
  exit 0
fi
if [ "$#" -gt 1 ]; then
  echo "usage: scripts/check-released-signatures.sh [<ref>]" >&2; exit 64
fi

ref="${1:-}"
if [ -z "$ref" ]; then
  ref="$(git describe --tags --abbrev=0 --match 'v[0-9]*' HEAD 2>/dev/null || true)"
  [ -n "$ref" ] || { echo "ERROR: no v* tag reachable from HEAD; pass a ref." >&2; exit 64; }
fi
git rev-parse --verify --quiet "$ref^{commit}" >/dev/null || { echo "ERROR: unknown ref $ref." >&2; exit 64; }

mkdir -p "$ROOT/.agents/scratch"
tmp="$(mktemp -d "$ROOT/.agents/scratch/released-signatures.XXXXXX")"
wt=""
cleanup() {
  if [ -n "$wt" ]; then git worktree remove --force "$wt" >/dev/null 2>&1 || true; fi
  rm -rf -- "$tmp"
}
trap cleanup EXIT

echo "==> dump of the current checkout"
"$ROOT/scripts/lean.sh" lake env lean scripts/dump_pin_signatures.lean > "$tmp/head.tsv"
if [ -n "${TDA_SIG_BASE_DUMP:-}" ]; then
  cp "$TDA_SIG_BASE_DUMP" "$tmp/base.tsv"
else
  echo "==> dump of $ref (temporary worktree)"
  wt="$tmp/base"
  git worktree add --detach "$wt" "$ref" >/dev/null
  (
    cd "$wt"
    # The worktree's own git-local variables must not redirect lake's package clones.
    # shellcheck disable=SC2046
    unset $(git rev-parse --local-env-vars)
    bash scripts/bootstrap.sh >/dev/null
    ./scripts/lean.sh lake build >/dev/null
    ./scripts/lean.sh lake env lean "$ROOT/scripts/dump_pin_signatures.lean"
  ) > "$tmp/base.tsv"
fi
compare_dumps "$tmp/base.tsv" "$tmp/head.tsv" "$ref"
