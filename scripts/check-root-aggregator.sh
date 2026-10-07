#!/usr/bin/env bash
# Fail unless each library's root module is a pure aggregator: `import` lines, one module each (and
# the optional `module` header), comments and blank lines only. Theorems, definitions, namespaces,
# options and any other command belong in the individual modules the root imports; content in
# the root cannot be imported by a sibling module without an import cycle.
#
# The roots are read at run time from lakefile.toml with a real TOML parser (python3 tomllib):
# every `[[lean_lib]]` contributes its `roots` (default: its `name`), located under the package
# and library `srcDir`. The guard therefore follows scripts/rename-project.sh without a
# hard-coded library name. A missing lakefile.toml, parser or root file fails closed. Comments and
# strings are handled by the shared lexer scripts/lean-code-scan.awk (mode=root); no marker
# exempts a line.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

# Prints one `<lib><TAB><root file>` line per library root; exits non-zero on any problem.
roots="$(python3 - <<'PY'
import os, sys
try:
    import tomllib
except ImportError:
    sys.exit("ERROR: python3 >= 3.11 (tomllib) is required to read lakefile.toml.")
try:
    with open("lakefile.toml", "rb") as f:
        cfg = tomllib.load(f)
except (OSError, tomllib.TOMLDecodeError) as e:
    sys.exit(f"ERROR: cannot read lakefile.toml: {e}")
libs = cfg.get("lean_lib", [])
if not isinstance(libs, list) or not libs:
    sys.exit("ERROR: no [[lean_lib]] found in lakefile.toml.")
pkg_src = cfg.get("srcDir", ".")
for lib in libs:
    name = lib.get("name")
    roots = lib.get("roots", [name])
    if not isinstance(name, str) or not name or not isinstance(roots, list) \
            or not roots or not all(isinstance(r, str) and r for r in roots):
        sys.exit(f"ERROR: [[lean_lib]] entry without a usable name/roots: {lib!r}")
    for r in roots:
        path = os.path.normpath(os.path.join(pkg_src, lib.get("srcDir", "."),
                                             *r.split("."))) + ".lean"
        print(f"{name}\t{path}")
PY
)"

status=0
while IFS=$'\t' read -r lib f; do
  if [ ! -f "$f" ]; then
    echo "ERROR: root module $f of lean_lib '$lib' not found." >&2
    exit 1
  fi
  violations="$(awk -v mode=root -f scripts/lean-code-scan.awk "$f")"
  if [ -n "$violations" ]; then
    printf '%s\n' "$violations" >&2
    echo "ERROR: $f is the root aggregator: one 'import <Module>' per line, comments and blank lines only. Move the lines above into a module of lean_lib '$lib' and import it here." >&2
    status=1
  else
    echo "OK: $f is imports-only."
  fi
done <<< "$roots"
exit "$status"
