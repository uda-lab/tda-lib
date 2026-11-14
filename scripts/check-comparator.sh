#!/usr/bin/env bash
# Fail-closed standalone Comparator wrapper for the frozen bounded-pilot contract (Issue
# #855). Called standalone and, if wired per the measured runtime recorded on the PR, as the
# last step of scripts/check.sh (inside the same build lock) and from scripts/hooks/pre-push;
# not wired into CI (any `.github/workflows/` change remains an owner decision).
#
# Comparator checks agreement between the production solution and the already-reviewed
# ComparatorChallenge reference; it does not itself establish fidelity to
# docs/math/rips-sampling-confidence.md (docs/adr/0003-comparator-pilot-contract.md).
set -uo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
export PATH="$HOME/.elan/bin:$PATH"

die() {
  printf 'ERROR: %s\n' "$1" >&2
  exit 2
}

# scripts/print_axioms/*.lean pins several thousand theorems in this repository: the pinned
# inventory is passed to jq through a file (--slurpfile), never as a command-line argument
# (--argjson), to stay well under ARG_MAX.
pinned_targets_file="$(mktemp)" || die "could not create a temporary file for the pinned theorem inventory."
trap 'rm -f "$pinned_targets_file"' EXIT

[ "$#" -eq 0 ] || die "this wrapper accepts no command-line overrides; refusing sandbox bypass and externally supplied exports."

CONFIG="$ROOT/comparator.json"

# Comparator resolves dependencies inside its bubblewrap sandbox and cannot write a missing
# manifest back into the project. It also needs the repository's selected Lean toolchain.
[ -s "$ROOT/lean-toolchain" ] || die "lean-toolchain is missing or empty."
[ -s "$ROOT/lake-manifest.json" ] || die "lake-manifest.json is missing or empty; run the existing pinned build first."
[ -d "$ROOT/scripts/print_axioms" ] || die "scripts/print_axioms/ is missing or unreadable."
[ -s "$CONFIG" ] || die "comparator.json is missing or empty."
command -v jq >/dev/null 2>&1 || die "jq is required to validate the frozen Comparator config."
command -v awk >/dev/null 2>&1 || die "awk is required to verify the production/reference import boundary."
command -v find >/dev/null 2>&1 || die "find is required to enumerate project Lean modules."
command -v xargs >/dev/null 2>&1 || die "xargs is required to read pinned theorem names from scripts/print_axioms/*.lean."
command -v python3 >/dev/null 2>&1 || die "python3 (with the standard tomllib module) is required to reject a configured srcDir."

# Keep the Comparator target inventory aligned with the current pinned-theorem inventory
# rather than maintaining a second target list in this wrapper. comparator.json's
# theorem_names must be a duplicate-free, non-empty, pinned SUBSET of that inventory, not
# equal to it: this pilot freezes a reference for its own one target theorem, not for every
# public theorem the repository has ever pinned across scripts/print_axioms/*.lean.
if ! find "$ROOT/scripts/print_axioms" -maxdepth 1 -type f -name '*.lean' -print0 \
    | xargs -0 sed -nE 's/^[[:space:]]*#print[[:space:]]+axioms[[:space:]]+([^[:space:]]+).*$/\1/p' \
    | jq -R . | jq -s 'unique' > "$pinned_targets_file"; then
  die "could not read pinned theorem names from scripts/print_axioms/*.lean."
fi
[ "$(cat "$pinned_targets_file")" != "[]" ] || die "scripts/print_axioms/*.lean has no pinned theorem targets."

# These fields are part of the reviewed contract (Issue #855, "Ruled design for the bounded
# pilot"). An unexpected field, a theorem_names entry outside the pinned inventory or outside
# the one frozen target, a duplicate or empty theorem_names, an added definition hole, or an
# axiom expansion is a configuration error, not a request to proceed. The pinned inventory
# (several thousand entries) is read via --slurpfile, not --argjson: passing it as a
# command-line argument would exceed ARG_MAX.
if ! jq -e --slurpfile pinned_targets_wrapped "$pinned_targets_file" '
  ($pinned_targets_wrapped[0]) as $pinned_targets |
  type == "object" and
  (keys | sort) == ["challenge_module", "definition_names", "permitted_axioms", "solution_module", "theorem_names"] and
  .challenge_module == "ComparatorChallenge.Reference" and
  .solution_module == "TDA.Probability.SamplingCoverage" and
  (.theorem_names | type) == "array" and
  (.theorem_names | length) > 0 and
  (.theorem_names | all(type == "string")) and
  (.theorem_names | unique | length) == (.theorem_names | length) and
  (.theorem_names - $pinned_targets) == [] and
  (.theorem_names - ["TDA.Probability.measure_missedCover_le_card_mul"]) == [] and
  .definition_names == [] and
  .permitted_axioms == ["propext", "Classical.choice", "Quot.sound"]
' "$CONFIG" >/dev/null 2>&1; then
  die "comparator.json is malformed or differs from the reviewed bounded-pilot contract, pinned targets, or exact axiom allowlist."
fi

# Keep the independently authored challenge and the production library on separate import
# boundaries in both directions. The production boundary is every project Lean source outside
# ComparatorChallenge (the same scope scripts/check-no-sorry.sh and
# scripts/check-no-custom-axiom.sh already use), not just comparator.json's solution_module:
# the contract freezes one target theorem, but the import-boundary guarantee covers the whole
# production tree. Challenge sources may import other challenge modules or package
# dependencies, but not any project-local module: that rule closes transitive bridges through
# auxiliary source files as well as direct imports.
solution_module="$(jq -r '.solution_module' "$CONFIG")"
solution_path="$ROOT/${solution_module//./\/}.lean"
[ -f "$solution_path" ] || die "the solution module $solution_module has no corresponding Lean source: $solution_path"
case "$solution_path/" in
  "$ROOT/TDA/"*) ;;
  *) die "the solution module $solution_module is outside the production library TDA." ;;
esac
[ -f "$ROOT/TDA.lean" ] && [ -d "$ROOT/TDA" ] \
  || die "the production TDA library root is missing or unreadable."
[ -f "$ROOT/ComparatorChallenge.lean" ] && [ -d "$ROOT/ComparatorChallenge" ] \
  || die "the ComparatorChallenge library root is missing or unreadable."
[ ! -L "$ROOT/TDA.lean" ] && [ ! -L "$ROOT/TDA" ] \
  || die "the production TDA roots must not be symlinks."
[ ! -L "$ROOT/ComparatorChallenge.lean" ] && [ ! -L "$ROOT/ComparatorChallenge" ] \
  || die "the ComparatorChallenge roots must not be symlinks."

# Fail closed on any configured srcDir, in any spelling, for either lean_lib. Every
# project_module_name computed below is a direct repo-root-relative path -> dotted-name
# conversion (slashes to dots), which is only correct when every Lean target uses Lake's
# default srcDir (".", i.e. no override): a non-default srcDir keeps the source directory in
# the file path but not in the real Lean import name, so a bridge module placed under it
# could import production while this wrapper's name mapping never recognises the match,
# letting ComparatorChallenge import that bridge undetected. TOML's string/key grammar has no
# bound on how a key's raw text can differ from its decoded value (escapes, literal-string
# quoting, line-continuation, a basic-string key with a Unicode escape whose raw bytes contain
# no literal `srcDir`, etc.), so matching the textual pattern `srcDir` can never close this
# class for good — only decoding every key the way Lake's own TOML parser does can
# (precedent: generalized-jetedmd PR #277, where three successive codex reviews defeated
# successive text-matching attempts). Decode lakefile.toml with Python's standard `tomllib`
# and recursively check every *decoded* key, at every nesting level (top-level tables,
# `[[lean_lib]]` array entries, inline tables), for the literal decoded key name `srcDir`. A
# `lakefile.lean` could set srcDir programmatically where no TOML scan would see it; this
# wrapper supports TOML configuration only, so reject outright if one exists.
[ ! -f "$ROOT/lakefile.lean" ] \
  || die "lakefile.lean exists; this wrapper only supports lakefile.toml and cannot scan a Lean build config for a programmatic srcDir override."
# No `set -e` is active in this script, so this assignment does not abort on a nonzero exit
# and `$?` right after it still reflects python3's own exit status.
srcdir_check_output="$(python3 -c '
import sys, tomllib

def has_src_dir(node):
    if isinstance(node, dict):
        return "srcDir" in node or any(has_src_dir(v) for v in node.values())
    if isinstance(node, list):
        return any(has_src_dir(v) for v in node)
    return False

try:
    with open(sys.argv[1], "rb") as f:
        doc = tomllib.load(f)
except Exception as e:
    print(f"could not parse lakefile.toml as TOML: {e}", file=sys.stderr)
    sys.exit(2)

sys.exit(1 if has_src_dir(doc) else 0)
' "$ROOT/lakefile.toml" 2>&1)"
srcdir_check_status=$?
if [ "$srcdir_check_status" -eq 1 ]; then
  die "lakefile.toml configures a srcDir (found by decoding the TOML document, not by text matching); this wrapper's module-name mapping assumes every target uses Lake's default srcDir. Derive module names from Lake's configured source roots before adding a srcDir, or remove the srcDir override."
elif [ "$srcdir_check_status" -ne 0 ]; then
  die "could not check lakefile.toml for a configured srcDir: $srcdir_check_output"
fi

# Ignore repository metadata, local build output, agent worktrees and agent scratch space —
# the same exclusions scripts/check-no-sorry.sh and scripts/check-no-custom-axiom.sh use — plus
# .claude/skills, whose entries are this repository's own compatibility symlinks into
# .agents/skills (documentation only, never Lean sources); excluding it here does not weaken
# the check below, which only ever flags a symlinked *.lean file or symlinked directory in the
# first place. A symlinked source file or directory elsewhere could otherwise hide an import
# from the enumeration below.
if ! project_symlinks="$(find "$ROOT" \
  \( -name '.git' -o -name '.lake' -o -path "$ROOT/.agents/worktrees" -o -path "$ROOT/.agents/scratch" \
     -o -path "$ROOT/.claude/worktrees" -o -path "$ROOT/.claude/scratch" -o -path "$ROOT/.claude/skills" \) -prune \
  -o -type l -print 2>&1)"; then
  die "could not check project Lean sources for symlinks: $project_symlinks"
fi
while IFS= read -r link; do
  [ -n "$link" ] || continue
  if [[ "$link" == *.lean ]] || [ -d "$link" ]; then
    die "project Lean sources must not be hidden behind symlinks: $link"
  fi
done <<< "$project_symlinks"

if ! project_sources="$(find "$ROOT" \
  \( -name '.git' -o -name '.lake' -o -path "$ROOT/.agents/worktrees" -o -path "$ROOT/.agents/scratch" \
     -o -path "$ROOT/.claude/worktrees" -o -path "$ROOT/.claude/scratch" -o -path "$ROOT/.claude/skills" \) -prune \
  -o -type f -name '*.lean' -print 2>&1)"; then
  die "could not enumerate project Lean modules: $project_sources"
fi
[ -n "$project_sources" ] || die "the project has no Lean source files."
production_source_count=0
challenge_source_count=0
while IFS= read -r source; do
  [ -n "$source" ] || continue
  case "$source" in
    "$ROOT/ComparatorChallenge.lean"|"$ROOT/ComparatorChallenge/"*)
      forbidden_target=TDA
      challenge_source_count=$((challenge_source_count + 1))
      boundary_description="ComparatorChallenge modules must not import TDA"
      ;;
    *)
      forbidden_target=ComparatorChallenge
      production_source_count=$((production_source_count + 1))
      boundary_description="project production and auxiliary modules must not import ComparatorChallenge"
      ;;
  esac
  if ! boundary_output="$(LC_ALL=C awk -v mode=import -v import_target="$forbidden_target" \
    -f "$ROOT/scripts/lean-code-scan.awk" "$source")"; then
    die "could not inspect import boundary in $source."
  fi
  [ -z "$boundary_output" ] || die "$boundary_description: $boundary_output"
done <<< "$project_sources"
[ "$production_source_count" -gt 0 ] \
  || die "the production project has no Lean source files to boundary-check."
[ "$challenge_source_count" -gt 0 ] \
  || die "the ComparatorChallenge library has no Lean source files to boundary-check."

# A challenge could otherwise import a local helper that imports TDA, even though neither
# edge directly crosses the library boundary. Treat every project source outside
# ComparatorChallenge as a forbidden local dependency of challenge modules.
declare -a project_module_names=()
declare -a project_module_sources=()
while IFS= read -r source; do
  [ -n "$source" ] || continue
  relative_source="${source#"$ROOT"/}"
  [[ "$relative_source" != *[[:space:]]* ]] \
    || die "project Lean module paths with whitespace cannot be checked safely: $source"
  module_name="${relative_source%.lean}"
  module_name="${module_name//\//.}"
  if [ -n "$module_name" ]; then
    project_module_names+=("$module_name")
    project_module_sources+=("$source")
  fi
done <<< "$project_sources"
while IFS= read -r source; do
  [ -n "$source" ] || continue
  case "$source" in
    "$ROOT/ComparatorChallenge.lean"|"$ROOT/ComparatorChallenge/"*) ;;
    *) continue ;;
  esac
  if ! imported_modules="$(LC_ALL=C awk -v mode=imports -f "$ROOT/scripts/lean-code-scan.awk" "$source")"; then
    die "could not enumerate imports in ComparatorChallenge source $source."
  fi
  while IFS= read -r imported_module; do
    [ -n "$imported_module" ] || continue
    for index in "${!project_module_names[@]}"; do
      [ "${project_module_names[$index]}" = "$imported_module" ] || continue
      candidate_source="${project_module_sources[$index]}"
      case "$candidate_source" in
        "$ROOT/ComparatorChallenge.lean"|"$ROOT/ComparatorChallenge/"*) continue ;;
      esac
      die "ComparatorChallenge modules must not import project-local modules outside ComparatorChallenge: $source imports $imported_module from $candidate_source"
    done
  done <<< "$imported_modules"
done <<< "$project_sources"

bwrap_path="$(command -v bwrap 2>/dev/null || true)"
[ -n "$bwrap_path" ] || die "bubblewrap (bwrap) is unavailable; refusing to run Comparator without its sandbox."
if [[ ${COMPARATOR_BWRAP+x} ]]; then
  [ -n "$COMPARATOR_BWRAP" ] || die "COMPARATOR_BWRAP is set but empty; unset it or name the default bwrap executable."
  if [[ "$COMPARATOR_BWRAP" != "bwrap" && "$COMPARATOR_BWRAP" != "$bwrap_path" ]]; then
    die "COMPARATOR_BWRAP must resolve to the default bwrap executable; refusing a sandbox override."
  fi
fi

# Probe the exact mount sequence `lake comparator` always performs before anything else
# (Lake/CLI/Check.lean's buildSandboxArgs: --unshare-all, then --ro-bind / /, then --tmpfs
# over /home, /root, /run/user and /tmp). A container can satisfy plain namespace creation and
# an unmasked /proc yet still lack a real /run/user directory: bwrap mounts tmpfs only over an
# existing mountpoint, and the preceding --ro-bind makes the whole tree read-only before it gets
# there, so a missing /run/user fails with "Can't mkdir /run/user: Read-only file system" deep
# inside Comparator's first sandboxed step. Report any such startup failure as exit 2 here,
# rather than letting Comparator's own ordinary rejection/build status (also exit 1) mask it.
if ! sandbox_probe_output="$(bwrap --unshare-all --ro-bind / / \
  --tmpfs /home --tmpfs /root --tmpfs /run/user --tmpfs /tmp \
  --proc /proc --dev /dev --die-with-parent --new-session /bin/true 2>&1)"; then
  printf 'ERROR: bubblewrap sandbox startup probe failed; refusing to run Comparator without its full sandbox.\n' >&2
  [ -z "$sandbox_probe_output" ] || printf '%s\n' "$sandbox_probe_output" >&2
  exit 2
fi

command -v lake >/dev/null 2>&1 || die "lake is unavailable; install/use the repository's pinned Lean toolchain."

# Serialize Comparator builds with the same lock as the canonical gate. No sandbox bypass,
# export override, or stale-export input is accepted by this wrapper.
[ -r "$ROOT/scripts/lib/build-lock.sh" ] || die "scripts/lib/build-lock.sh is missing or unreadable."
if ! . "$ROOT/scripts/lib/build-lock.sh"; then
  die "could not acquire the shared Lean build lock."
fi

if lake comparator --config "$CONFIG"; then
  exit 0
else
  status=$?
fi

case "$status" in
  1) exit 1 ;; # Comparator rejection or build failure.
  2) exit 2 ;; # Comparator could not start (config, manifest, or sandbox prerequisite).
  *)
    printf 'ERROR: lake comparator returned unexpected exit status %s; refusing success.\n' "$status" >&2
    exit 2
    ;;
esac
