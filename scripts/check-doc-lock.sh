#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

git diff --quiet HEAD -- lean-toolchain lakefile.toml lake-manifest.json || {
  echo 'ERROR: documentation build changed a parent Lean/mathlib pin.' >&2
  exit 1
}

python3 - "$ROOT" <<'PY'
import json
import pathlib
import subprocess
import sys

root = pathlib.Path(sys.argv[1]).resolve()
docbuild = root / "docbuild"
manifest = json.loads((docbuild / "lake-manifest.json").read_text())
parent = json.loads((root / "lake-manifest.json").read_text())
packages = manifest["packages"]

def normalize(url):
    return url.removesuffix(".git").rstrip("/")

expected = {normalize(pkg["url"]): pkg["rev"] for pkg in parent["packages"]}
docgen_expected = {
    "https://github.com/leanprover/doc-gen4": "e2af49a7b7e5e1a9224008c1f15e7aa4f58a4015",
    "https://github.com/leanprover/leansqlite": "6168b7549738a19bc837a1625c60c5d1e5dd8aeb",
    "https://github.com/fgdorais/lean4-unicode-basic": "37e7d8cb7316a88cd3e91208385c9ec6ae780019",
    "https://github.com/dupuisf/BibtexQuery": "852edafa268eb038a7158551fd580ee8433847b0",
    "https://github.com/acmepjz/md4lean": "31907cc18f48a95384f99cee5582c00fb39e0f67",
}
for url, rev in docgen_expected.items():
    key = normalize(url)
    if key in expected and expected[key] != rev:
        raise SystemExit(f"parent/doc-gen4 lock conflict for {url}: {expected[key]} != {rev}")
    expected[key] = rev

git_packages = [pkg for pkg in packages if pkg["type"] == "git"]
path_packages = [pkg for pkg in packages if pkg["type"] == "path"]
if len(packages) != 15 or len(git_packages) != 14 or len(path_packages) != 1:
    raise SystemExit(
        f"unexpected docbuild lock shape: {len(packages)} entries, "
        f"{len(git_packages)} git, {len(path_packages)} path"
    )
actual_lock = {normalize(pkg["url"]): pkg["rev"] for pkg in git_packages}
if actual_lock != expected:
    missing = sorted(set(expected) - set(actual_lock))
    extra = sorted(set(actual_lock) - set(expected))
    changed = sorted(url for url in set(actual_lock) & set(expected) if actual_lock[url] != expected[url])
    raise SystemExit(f"nested lock differs: missing={missing}, extra={extra}, changed={changed}")

packages_dir = (docbuild / manifest["packagesDir"]).resolve()
for pkg in sorted(git_packages, key=lambda p: (p.get("scope", ""), p["name"])):
    wanted_url = normalize(pkg["url"])
    matches = []
    for checkout in packages_dir.iterdir():
        if not checkout.is_dir():
            continue
        try:
            remote = subprocess.check_output(
                ["git", "-C", str(checkout), "remote", "get-url", "origin"],
                text=True,
                stderr=subprocess.DEVNULL,
            ).strip()
        except subprocess.CalledProcessError:
            continue
        if normalize(remote) == wanted_url:
            matches.append(checkout)
    if len(matches) != 1:
        raise SystemExit(f"expected one checkout for {wanted_url}; found {len(matches)}")
    checkout = matches[0]
    head = subprocess.check_output(
        ["git", "-C", str(checkout), "rev-parse", "HEAD"], text=True
    ).strip()
    if head != pkg["rev"]:
        raise SystemExit(f"checkout mismatch for {pkg['name']}: lock={pkg['rev']} HEAD={head}")
    print(f"{pkg['name']}: {pkg['rev']} (checkout HEAD matches)")

path_pkg = path_packages[0]
path_dir = (docbuild / path_pkg["dir"]).resolve()
if path_pkg["name"] != "TDA" or path_dir != root:
    raise SystemExit(f"unexpected local TDA package: {path_pkg['name']} at {path_dir}")
tda_head = subprocess.check_output(["git", "-C", str(root), "rev-parse", "HEAD"], text=True).strip()
print(f"TDA: local path at {tda_head}")
print("Parent Lean/mathlib pin files are unchanged; nested docbuild lock has 15 entries.")
PY
