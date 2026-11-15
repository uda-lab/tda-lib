#!/usr/bin/env bash
# Live trust-footprint audit: run `#print axioms` for every declaration listed in
# scripts/print_axioms/*.lean and fail unless each axiom set is a subset of the
# allowlist (the Lean/mathlib kernel trio). Catches `sorryAx`, project axioms and
# other trust escapes (e.g. `Lean.ofReduceBool` from `native_decide`) — including
# transitive ones that the textual guards cannot see.
#
# All pins are checked in a single `lake env lean` process: a generated file with
# `import TDA` followed by every area file's `#print axioms` lines (the same
# extraction rule used below to build the expected-name list) runs once, so the
# whole audit costs one environment load instead of one per area file (#949). The
# record parser and its decoy/duplicate/missing/malformed diagnostics and the
# allowlist below are unchanged; only how the Lean input is assembled, and how many
# processes produce records, changed.
#
# Requires a completed `lake build` (scripts/check.sh orders this correctly).
# Changing ALLOW is a `needs-decision` change.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
export PATH="$HOME/.elan/bin:$PATH"

ALLOW="propext Classical.choice Quot.sound"
# Library (namespace) name, read from lakefile.toml so scripts/rename-project.sh has one
# less site to patch.
NS="$(sed -n 's/^name = "\(.*\)"$/\1/p' lakefile.toml | head -1)"
PIN_DIR="scripts/print_axioms"

if ! command -v lake >/dev/null 2>&1; then
  echo "ERROR: 'lake' not found (install elan; see scripts/bootstrap.sh)." >&2
  exit 1
fi

# Declarations the audit must cover, taken from every area file.
if [ ! -d "$PIN_DIR" ]; then
  echo "ERROR: missing axiom pin directory $PIN_DIR." >&2
  exit 1
fi
# Bash 3.2 (the system Bash on macOS) has no `mapfile`. Check the producer's
# status before reading its NUL-delimited, sorted stream: process substitution
# would silently accept a partial list if `find` or `sort` failed after output.
pin_paths_file="$(mktemp)"
trap 'rm -f "$pin_paths_file"' EXIT
if ! find "$PIN_DIR" -maxdepth 1 -type f -name '*.lean' -print0 | sort -z >"$pin_paths_file"; then
  echo "ERROR: failed to enumerate $PIN_DIR; axiom audit incomplete." >&2
  exit 1
fi
# Preserve spaces, newlines and a final record without a terminating NUL byte.
SCRIPTS=()
while IFS= read -r -d '' script_path || [ -n "$script_path" ]; do
  SCRIPTS+=("$script_path")
done <"$pin_paths_file"
if [ "${#SCRIPTS[@]}" -eq 0 ]; then
  echo "ERROR: $PIN_DIR has no Lean audit files." >&2
  exit 1
fi
expected_file="$(mktemp)"
records_file="$(mktemp)"
mkdir -p "$ROOT/.agents/scratch"
# A trailing suffix after XXXXXX (e.g. ".lean") needs mkstemps; the system mktemp on
# macOS only calls mkstemp and silently fails on it. Make a trailing-X-only directory
# instead and give the file inside it a fixed name.
combined_dir="$(mktemp -d "$ROOT/.agents/scratch/axiom-audit.XXXXXX")"
combined_file="$combined_dir/combined.lean"
stderr_file="$(mktemp)"
trap 'rm -f "$pin_paths_file" "$expected_file" "$records_file" "$stderr_file"; rm -rf "$combined_dir"' EXIT
if ! awk '/^#print axioms /{print $3}' "${SCRIPTS[@]}" >"$expected_file"; then
  echo "ERROR: failed to read axiom pins; the audit is incomplete." >&2
  exit 1
fi
if [ ! -s "$expected_file" ]; then
  echo "ERROR: $PIN_DIR lists no '#print axioms' declarations; the audit must never pass vacuously." >&2
  exit 1
fi

# Build the single combined input: one `import TDA`, then every area file's
# `#print axioms` lines in the same order used to build $expected_file above, so a
# pin appears in the environment exactly where it appeared in its own area file.
#
# A handful of area files intentionally pin an auto-generated `._proof_1` auxiliary
# (e.g. `TDA.Persistence.dgm._proof_1`), already accepted project convention. Printing
# thousands of such names together in one file surfaces Lean's `auxLemma` linter, whose
# warning text has no record terminator of its own and gets appended as a continuation
# line onto the preceding record by the parser below, corrupting it ("malformed"). The
# lint is about source-code naming stability, not about the axioms being audited here,
# so it is disabled for this generated file only; nothing it would have flagged affects
# which axioms a declaration depends on.
gen_start=$(date +%s.%N)
{
  printf 'import TDA\n'
  printf 'set_option linter.auxLemma false\n'
  awk '/^#print axioms /' "${SCRIPTS[@]}"
} >"$combined_file"
gen_end=$(date +%s.%N)

pin_count="$(wc -l <"$expected_file" | tr -d ' ')"
echo "==> lake env lean $combined_file (single environment load; $pin_count pin(s) across ${#SCRIPTS[@]} area file(s))"
# Capture with errexit disabled so a failing lean run is diagnosed loudly instead of
# aborting before its output is shown.
load_start=$(date +%s.%N)
set +e
result="$("$ROOT/scripts/lean.sh" lake env lean "$combined_file" 2>"$stderr_file")"
STATUS=$?
set -e
load_end=$(date +%s.%N)
printf '%s\n' "$result"
cat "$stderr_file" >&2
if [ "$STATUS" -ne 0 ]; then
  echo "ERROR: 'lake env lean $combined_file' failed with exit $STATUS." >&2
  echo "  Run 'lake build' first; a pinned declaration that no longer exists also fails here." >&2
  exit 1
fi
# Only Lean's stdout contains `#print axioms` records. Resource-guard notices and
# other stderr diagnostics are still shown above, but cannot corrupt a record.
printf '%s\n' "$result" >>"$records_file"

# Phase timings (#949): file generation is pure disk I/O over area files already
# read above; the environment load is the one `lake env lean` process, which both
# maps the Mathlib/TDA closure and prints every pinned declaration's axioms.
awk -v a="$gen_start" -v b="$gen_end" -v c="$load_start" -v d="$load_end" \
  'BEGIN { printf "AXIOM AUDIT TIMING — generate combined file: %.3fs, environment load + print: %.3fs\n", (b - a), (d - c) }' >&2

# `#print axioms` output is one record per declaration, possibly wrapped over
# several lines:  'X' depends on axioms: [a, b, c]   or   'X' does not depend on any axioms
# Join wrapped records and index them by their literal declaration names in one pass.
# Quoted Lean names can themselves end in apostrophes, so the terminator is "' ",
# not the first apostrophe after the opening one. Unpinned decoys are ignored.
if ! LC_ALL=C awk -v allow="$ALLOW" -v ns="$NS" -v pin_dir="$PIN_DIR" '
  function error(message) { print "ERROR: " message > "/dev/stderr"; failed = 1 }
  function finish_record(   tail, end, name) {
    if (record == "") return
    tail = substr(record, 2)
    end = index(tail, "\047 ")
    if (end == 0) return
    name = substr(tail, 1, end - 1)
    if (name in pins) {
      counts[name]++
      if (counts[name] == 1) records[name] = record
    }
  }
  FNR == NR { pins[$0]++; order[++n] = $0; next }
  /^\047/ { finish_record(); record = $0; next }
  { if (record != "") record = record " " $0 }
  END {
    finish_record()
    for (i = 1; i <= n; i++) {
      decl = order[i]
      if (visited[decl]++) continue
      if (pins[decl] > 1) {
        error(decl " is pinned " pins[decl] " times in " pin_dir "; pin it once.")
        continue
      }
      if (counts[decl] == 0) {
        error("no \047#print axioms\047 output for " decl " (declaration missing or renamed?).")
        continue
      }
      if (counts[decl] != 1) {
        error(counts[decl] " \047#print axioms\047 records for " decl "; expected exactly one.")
        continue
      }
      rec = records[decl]
      prefix = "\047" decl "\047 "
      body = substr(rec, length(prefix) + 1)
      sub(/[[:space:]]*$/, "", body)
      if (body == "does not depend on any axioms") {
        print "OK: " decl " — no axioms."
        continue
      }
      start = "depends on axioms: ["
      valid = index(body, start) == 1 && substr(body, length(body), 1) == "]"
      if (valid) {
        list = substr(body, length(start) + 1, length(body) - length(start) - 1)
        sub(/[[:space:]]*$/, "", list)
        count = split(list, parts, ",")
        if (count == 0) valid = 0
        joined = ""
        for (j = 1; j <= count; j++) {
          ax = parts[j]
          sub(/^[[:space:]]*/, "", ax)
          sub(/[[:space:]]*$/, "", ax)
          if (ax == "" || index(ax, "[") || index(ax, "]") || ax ~ /[[:space:]]/) valid = 0
          if (j > 1) joined = joined " "
          joined = joined ax
          parts[j] = ax
        }
      }
      if (!valid) {
        error("malformed \047#print axioms\047 record for " decl ": " rec)
        continue
      }
      bad = 0
      for (j = 1; j <= count; j++) {
        ax = parts[j]
        if (index(" " allow " ", " " ax " ")) continue
        if (ax == "sorryAx") error(decl " is incomplete (depends on sorryAx).")
        else if (index(ax, ns ".") == 1) error(decl " depends on project axiom " ax ".")
        else error(decl " depends on unexpected trust " ax ".")
        bad = 1
      }
      if (!bad) print "OK: " decl " — axioms ⊆ {" allow "}: [" joined "]"
    }
    if (failed) { print "AXIOM AUDIT FAILED" > "/dev/stderr"; exit 1 }
    print "AXIOM AUDIT OK — " n " declaration(s) within the allowlist {" allow "}."
  }
' "$expected_file" "$records_file"; then
  exit 1
fi
