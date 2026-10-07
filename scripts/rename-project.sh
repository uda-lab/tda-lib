#!/usr/bin/env bash
# Rename the placeholder library (the current `name` in lakefile.toml; `LeanScaffold` in the
# template) to the project's library name, everywhere the name is load-bearing:
# lakefile.toml, lake-manifest.json, the root aggregator, the module directory and its
# namespace, the audit inputs, the coverage guard, the hooks and AGENTS.md. The root-aggregator
# guard reads the library name from lakefile.toml, so it follows the rename. Idempotent for the
# target name; refuses names that are not valid Lean module identifiers. Run once, during the
# Init phase, before the first commit of real work.
#
# Three files compare against the *template* sentinel `LeanScaffold` to decide whether the
# repository is still uninitialised (scripts/preflight.sh, .claude/hooks/session-brief.sh) or
# describe the placeholder (this script). They are excluded from the substitution below:
# renaming their literal would make every later session report "NOT INITIALISED".
#
#   scripts/rename-project.sh <NewName>          e.g. MobiusCPT, IshikiConj51
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

if [ "$#" -ne 1 ]; then
  echo "usage: scripts/rename-project.sh <NewName>" >&2
  exit 64
fi

NEW="${1:?usage: scripts/rename-project.sh <NewName>  (a Lean module identifier, e.g. MobiusCPT)}"
OLD="$(sed -n 's/^name = "\(.*\)"$/\1/p' lakefile.toml | head -1)"

if ! printf '%s' "$NEW" | grep -qE '^[A-Z][A-Za-z0-9_]*$'; then
  echo "ERROR: '$NEW' is not a valid library name (start with an uppercase letter; letters, digits, _ only)." >&2
  exit 64
fi
if [ "$OLD" = "$NEW" ]; then
  echo "already named $NEW — nothing to do"
  exit 0
fi
if [ ! -d "$OLD" ] || [ ! -f "$OLD.lean" ]; then
  echo "ERROR: expected $OLD/ and $OLD.lean (current library name from lakefile.toml: $OLD)." >&2
  exit 1
fi
if [ -e "$NEW" ] || [ -e "$NEW.lean" ]; then
  echo "ERROR: $NEW/ or $NEW.lean already exists." >&2
  exit 1
fi

# 1. Move the module tree and the root aggregator.
git mv "$OLD.lean" "$NEW.lean" 2>/dev/null || mv "$OLD.lean" "$NEW.lean"
git mv "$OLD" "$NEW" 2>/dev/null || mv "$OLD" "$NEW"

# 2. Rewrite the whole-word occurrences in every tracked text file that carries the name.
#    Whole-word: `LeanScaffold` but not `LeanScaffoldX`. The build directory is untracked.
#    The three sentinel files (see the header) keep the template literal.
python3 - "$OLD" "$NEW" <<'PY_RENAME'
import pathlib
import re
import subprocess
import sys

old, new = sys.argv[1:]
excluded = {"scripts/preflight.sh", ".claude/hooks/session-brief.sh", "scripts/rename-project.sh"}
pattern = re.compile(r"(?<![A-Za-z0-9_])" + re.escape(old) + r"(?![A-Za-z0-9_])")
try:
    paths = subprocess.check_output(["git", "ls-files", "-z"], stderr=subprocess.DEVNULL).split(b"\0")
except subprocess.CalledProcessError:
    # The self-test fixtures have no Git repository; never walk build/cache trees.
    paths = [str(p).encode() for p in pathlib.Path(".").rglob("*")
             if not {".git", ".lake", "sources"}.intersection(p.parts)]
for raw in paths:
    if not raw:
        continue
    path = pathlib.Path(raw.decode())
    if str(path) in excluded or path.is_symlink() or not path.is_file():
        continue
    try:
        original = path.read_text()
    except UnicodeDecodeError:
        continue
    updated = pattern.sub(new, original)
    if updated != original:
        path.write_text(updated)
PY_RENAME

rm -rf .lake/build
echo "renamed $OLD -> $NEW in: $NEW.lean $NEW/"
echo "next: review AGENTS.md and README.md prose, then bash scripts/check.sh"
